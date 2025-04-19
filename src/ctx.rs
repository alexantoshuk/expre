use indexmap::{indexmap, IndexMap};

enum Globals {
    Fvar(usize),
    F2var(usize),
    F3var(usize),
    Fconst(f64),
    F2const([f64; 2]),
    F3const([f64; 3]),
    Sconst(String),
}

#[derive(Copy, Clone, Debug)]
enum Type {
    F = 1,
    F2 = 2,
    F3 = 3,
}

struct ContextMap {
    data: IndexMap<String, (Type, usize)>,
    size: usize,
}
impl ContextMap {
    fn new() -> Self {
        Self {
            data: IndexMap::new(),
            size: 0,
        }
    }
    fn insert(&mut self, key: String, ty: Type) {
        self.data.insert(key, (ty, self.size));
        self.size += ty as usize;
    }
    fn size(&self) -> usize {
        self.size
    }
    fn get(&self, name: &str) -> Option<&(Type, usize)> {
        self.data.get(name)
    }
}

impl From<Vec<(String, Type)>> for ContextMap {
    fn from(vec: Vec<(String, Type)>) -> Self {
        let mut ctx_map = ContextMap::new();
        for (key, ty) in vec {
            ctx_map.insert(key, ty);
        }
        ctx_map
    }
}

impl From<&[(String, Type)]> for ContextMap {
    fn from(s: &[(String, Type)]) -> Self {
        let mut ctx_map = ContextMap::new();
        for (key, ty) in s {
            ctx_map.insert(key.to_owned(), *ty);
        }
        ctx_map
    }
}

impl From<IndexMap<String, Type>> for ContextMap {
    fn from(map: IndexMap<String, Type>) -> Self {
        let mut ctx_map = ContextMap::new();
        for (key, ty) in map {
            ctx_map.insert(key, ty);
        }
        ctx_map
    }
}

struct Context<'a, T> {
    ctxmap: &'a ContextMap,
    data: &'a [T],
}

impl<'a, T> Context<'a, T> {
    fn new(ctxmap: &'a ContextMap, data: &'a [T]) -> Self {
        assert!(data.len() >= ctxmap.size());
        Self { ctxmap, data }
    }
    // fn get()
}

// let inputs = indexmap!{
// "id" => F,
// "P" => F3,
// "uv" => F2,
// "F" => Fu,
// };
//
// let outputs = indexmap!{
// "out" => F,
// };

// let c = expre::Expre::new();
// let resolver = c.compile("id + PI - 124 + sin(P)", &inputs);
// let result = resolver.eval(&[&id,&P,&uv,&F], &mut out);
//  let result = resolver.eval_multi(&[&id,&P,&uv,&F], &[&mut out]);
//
