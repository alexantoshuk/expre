pub trait Context {
    fn lookup(&self, _name: &str, _args: &[f64]) -> Option<f64> {
        None
    }
}

impl<F> Context for F
where
    F: Fn(&str, &[f64]) -> Option<f64>,
{
    fn lookup(&self, name: &str, args: &[f64]) -> Option<f64> {
        self(name, args)
    }
}
