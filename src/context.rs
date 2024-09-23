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

pub trait Context2<F, U, V> {
    fn get_float(&self, index: usize) -> Option<F> {
        None
    }
    fn get_vec2(&self, index: usize) -> Option<U> {
        None
    }
    fn get_vec3(&self, index: usize) -> Option<V> {
        None
    }
}
