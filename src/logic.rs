// Pure logic: config parsing + case-conforming expansion.
// No Windows / winapi dependency here, so this module (and its tests)
// compile and run on any platform with `cargo test`.

use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CaseStyle {
    Lower,       // "pls"
    Capitalized, // "Pls"
    Upper,       // "PLS"
    Mixed,       // anything else, e.g. "pLs" -> falls back to Lower output
}

/// Detects how a typed word is cased, based only on its letters.
/// A single capital letter ("Q") counts as Capitalized, not Upper: it can't
/// be told apart from "Q" the start of a word, and "Question" is the more
/// useful expansion than "QUESTION".
pub fn detect_case(word: &str) -> CaseStyle {
    let mut letters = word.chars().filter(|c| c.is_alphabetic());
    let Some(first) = letters.next() else {
        return CaseStyle::Mixed;
    };
    let (mut rest_upper, mut rest_lower, mut has_rest) = (true, true, false);
    for c in letters {
        has_rest = true;
        rest_upper &= c.is_uppercase();
        rest_lower &= c.is_lowercase();
    }
    if first.is_lowercase() && rest_lower {
        CaseStyle::Lower
    } else if first.is_uppercase() && !has_rest {
        CaseStyle::Capitalized
    } else if first.is_uppercase() && rest_upper {
        CaseStyle::Upper
    } else if first.is_uppercase() && rest_lower {
        CaseStyle::Capitalized
    } else {
        CaseStyle::Mixed
    }
}

fn capitalize_first(s: &str) -> String {
    let mut chars = s.chars();
    match chars.next() {
        Some(first) => first.to_uppercase().collect::<String>() + chars.as_str(),
        None => String::new(),
    }
}

/// Applies a detected case style to the canonical (lowercase) expansion text.
pub fn apply_case(expansion: &str, style: CaseStyle) -> String {
    match style {
        CaseStyle::Upper => expansion.to_uppercase(),
        CaseStyle::Capitalized => capitalize_first(expansion),
        CaseStyle::Lower | CaseStyle::Mixed => expansion.to_string(),
    }
}

/// Parses replacements.json into a lowercase-keyed abbreviation -> expansion map.
pub fn load_config_map(json_text: &str) -> Result<HashMap<String, String>, serde_json::Error> {
    let raw: HashMap<String, String> = serde_json::from_str(json_text)?;
    let mut map = HashMap::with_capacity(raw.len());
    for (k, v) in raw {
        map.insert(k.to_lowercase(), v);
    }
    Ok(map)
}

/// Given the map and a typed word (in whatever case the user typed it),
/// returns the correctly-cased replacement, or None if no abbreviation matches.
pub fn expand(map: &HashMap<String, String>, typed_word: &str) -> Option<String> {
    let base = map.get(&typed_word.to_lowercase())?;
    let style = detect_case(typed_word);
    Some(apply_case(base, style))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_map() -> HashMap<String, String> {
        let mut m = HashMap::new();
        m.insert("pls".to_string(), "please".to_string());
        m.insert("btw".to_string(), "by the way".to_string());
        m
    }

    #[test]
    fn lower_case() {
        let m = sample_map();
        assert_eq!(expand(&m, "pls"), Some("please".to_string()));
    }

    #[test]
    fn capitalized() {
        let m = sample_map();
        assert_eq!(expand(&m, "Pls"), Some("Please".to_string()));
    }

    #[test]
    fn all_upper() {
        let m = sample_map();
        assert_eq!(expand(&m, "PLS"), Some("PLEASE".to_string()));
    }

    #[test]
    fn no_match_returns_none() {
        let m = sample_map();
        assert_eq!(expand(&m, "xyz"), None);
    }

    #[test]
    fn mixed_case_falls_back_to_lower_output() {
        let m = sample_map();
        assert_eq!(expand(&m, "pLs"), Some("please".to_string()));
    }

    #[test]
    fn multi_word_expansion_capitalized() {
        let m = sample_map();
        assert_eq!(expand(&m, "Btw"), Some("By the way".to_string()));
    }

    #[test]
    fn multi_word_expansion_all_upper() {
        let m = sample_map();
        assert_eq!(expand(&m, "BTW"), Some("BY THE WAY".to_string()));
    }

    #[test]
    fn single_capital_letter_is_capitalized_not_upper() {
        let mut m = sample_map();
        m.insert("q".to_string(), "question".to_string());
        assert_eq!(expand(&m, "Q"), Some("Question".to_string()));
        assert_eq!(expand(&m, "q"), Some("question".to_string()));
    }

    #[test]
    fn detect_case_edge_cases() {
        assert_eq!(detect_case("123"), CaseStyle::Mixed);
        assert_eq!(detect_case("pLs"), CaseStyle::Mixed);
        assert_eq!(detect_case("p1s"), CaseStyle::Lower);
        assert_eq!(detect_case("P1S"), CaseStyle::Upper);
        assert_eq!(detect_case("É"), CaseStyle::Capitalized);
        assert_eq!(detect_case("ÉTÉ"), CaseStyle::Upper);
    }

    #[test]
    fn config_parsing_lowercases_keys() {
        let json = r#"{ "pls": "please" }"#;
        let map = load_config_map(json).unwrap();
        assert_eq!(map.get("pls"), Some(&"please".to_string()));
    }
}
