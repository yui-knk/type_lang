#[derive(Debug, PartialEq)]
pub struct NameGenerator {
    count: usize
}

impl NameGenerator {
    pub fn new() -> NameGenerator {
        NameGenerator { count: 0 }
    }

    pub fn get_name(&mut self) -> String {
        let i = self.count;
        self.count += 1;
        format!("Var{}", i)
    }
}

#[cfg(test)]
mod tests_name_generator {
    use super::*;

    #[test]
    fn test_get_name() {
        let mut gen = NameGenerator::new();
        assert_eq!(gen.get_name(), "Var0".to_string());
        assert_eq!(gen.get_name(), "Var1".to_string());
    }
}
