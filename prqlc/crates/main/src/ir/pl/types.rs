use std::iter::zip;

use enum_as_inner::EnumAsInner;
use serde::{Deserialize, Serialize};

use super::{Ident, Literal};

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize, EnumAsInner)]
pub enum TyKind {
    /// Type of a built-in primitive type
    Primitive(PrimitiveSet),

    /// Type that contains only a one value
    Singleton(Literal),

    /// Union of sets (sum)
    Union(Vec<(Option<String>, Ty)>),

    /// Type of tuples (product)
    Tuple(TyTuple),

    /// Type of arrays
    Array(Box<Ty>),

    /// Type of sets
    /// Used for expressions that can be converted to TypeExpr.
    Set,

    /// Type of functions with defined params and return types.
    Function(Option<TyFunc>),

    /// Type of every possible value. Super type of all other types.
    /// The breaker of chains. Mother of types.
    Any,
}

#[derive(Default, Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TyTuple {
    /// Tuple fields, optionally named.
    pub fields: Vec<TyTupleField>,

    /// True when the tuple can have additional fields that we have no knowledge of at the moment.
    pub has_other: bool,
}

pub type TyTupleField = (Option<String>, Option<Ty>);

#[derive(Clone, PartialEq, Serialize, Deserialize)]
pub struct Ty {
    pub kind: TyKind,

    /// Name inferred from the type declaration.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub name: Option<String>,

    /// Ids of the nodes that are the source for data of this type.
    /// Can point to a table reference or a column expression.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub lineage: Option<usize>,

    /// Fully-qualified name of table that was instanced to produce this type.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub instance_of: Option<Ident>,

    /// True iff this type can be restricted.
    /// The new type must be subtype of the original.
    #[serde(skip_serializing_if = "is_false", default)]
    pub infer: bool,
}

/// Built-in sets.
#[derive(
    Debug, Clone, Serialize, Deserialize, PartialEq, Eq, strum::EnumString, strum::Display,
)]
pub enum PrimitiveSet {
    #[strum(to_string = "int")]
    Int,
    #[strum(to_string = "float")]
    Float,
    #[strum(to_string = "bool")]
    Bool,
    #[strum(to_string = "text")]
    Text,
    #[strum(to_string = "date")]
    Date,
    #[strum(to_string = "time")]
    Time,
    #[strum(to_string = "timestamp")]
    Timestamp,
}

// Type of a function
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
pub struct TyFunc {
    pub args: Vec<Option<Ty>>,
    pub return_ty: Box<Option<Ty>>,
}

impl Ty {
    pub fn new<K: Into<TyKind>>(kind: K) -> Ty {
        Ty {
            kind: kind.into(),
            name: None,
            lineage: None,
            instance_of: None,
            infer: false,
        }
    }

    pub fn relation(tuple: TyTuple) -> Self {
        let tuple = Ty::new(TyKind::Tuple(tuple));
        Ty::new(TyKind::Array(Box::new(tuple)))
    }

    pub fn as_relation(&self) -> Option<&TyTuple> {
        self.kind.as_array()?.kind.as_tuple()
    }

    pub fn as_relation_mut(&mut self) -> Option<&mut TyTuple> {
        self.kind.as_array_mut()?.kind.as_tuple_mut()
    }

    pub fn into_relation(self) -> Option<TyTuple> {
        self.kind.into_array().ok()?.kind.into_tuple().ok()
    }

    pub fn is_super_type_of(&self, subset: &Ty) -> bool {
        self.kind.is_super_type_of(&subset.kind)
    }

    pub fn is_sub_type_of_array(&self) -> bool {
        match &self.kind {
            TyKind::Array(_) => true,
            TyKind::Union(elements) => elements.iter().any(|(_, e)| e.is_sub_type_of_array()),
            _ => false,
        }
    }

    pub fn is_relation(&self) -> bool {
        match &self.kind {
            TyKind::Array(elem) => {
                matches!(elem.kind, TyKind::Tuple(_))
            }
            _ => false,
        }
    }

    pub fn is_function(&self) -> bool {
        matches!(self.kind, TyKind::Function(_))
    }

    pub fn is_tuple(&self) -> bool {
        matches!(self.kind, TyKind::Tuple(_))
    }
}

impl TyKind {
    fn is_super_type_of(&self, subset: &TyKind) -> bool {
        match (self, subset) {
            (TyKind::Primitive(l0), TyKind::Primitive(r0)) => l0 == r0,

            (one, TyKind::Union(many)) => many
                .iter()
                .all(|(_, each)| one.is_super_type_of(&each.kind)),

            (TyKind::Union(many), one) => {
                many.iter().any(|(_, any)| any.kind.is_super_type_of(one))
            }

            (TyKind::Any, _) => true,
            (_, TyKind::Any) => false,

            (TyKind::Function(None), TyKind::Function(_)) => true,
            (TyKind::Function(Some(_)), TyKind::Function(None)) => true,
            (TyKind::Function(Some(sup)), TyKind::Function(Some(sub))) => {
                if is_not_super_type_of(sup.return_ty.as_ref(), sub.return_ty.as_ref()) {
                    return false;
                }
                if sup.args.len() != sub.args.len() {
                    return false;
                }
                for (sup_arg, sub_arg) in zip(&sup.args, &sub.args) {
                    if is_not_super_type_of(sup_arg, sub_arg) {
                        return false;
                    }
                }

                true
            }

            (TyKind::Array(sup), TyKind::Array(sub)) => sup.is_super_type_of(sub),

            (TyKind::Tuple(sup_tuple), TyKind::Tuple(sub_tuple)) => {
                let mut sup_fields = sup_tuple.fields.iter();
                let mut sub_fields = sub_tuple.fields.iter();

                loop {
                    let sup = sup_fields.next();
                    let sub = sub_fields.next();

                    match (sup, sub) {
                        (Some((_, sup)), Some((_, sub))) => {
                            if is_not_super_type_of(sup, sub) {
                                return false;
                            }
                        }
                        (None, Some(_)) => {
                            if !sup_tuple.has_other {
                                return false;
                            }
                        }
                        (Some(_), None) => {
                            if !sub_tuple.has_other {
                                return false;
                            }
                        }
                        (None, None) => break,
                    }
                }
                true
            }

            (l, r) => l == r,
        }
    }
}

impl Ty {
    /// Converts [{T1, x = T2, y = {T3, z = T4}}]
    /// into [{alias = {T1, x = T2, T3, z = T4}}]
    pub fn rename_relation(&mut self, alias: String) {
        if let TyKind::Array(items_ty) = &mut self.kind {
            items_ty.rename_tuples(alias);
        }
    }

    /// Converts {T1, x = T2, y = {T3, z = T4}}
    /// into {alias = {T1, x = T2, T3, z = T4}}
    fn rename_tuples(&mut self, alias: String) {
        self.flatten_tuples();

        if let TyKind::Tuple(tuple) = &mut self.kind {
            let inner_tuple = std::mem::take(tuple);

            let ty = Ty {
                lineage: self.lineage,
                instance_of: self.instance_of.clone(),
                ..Ty::new(TyKind::Tuple(inner_tuple))
            };
            tuple.fields.push((Some(alias), Some(ty)));
        }
    }

    /// Converts {y = {T3, z = T4}}
    /// into {T3, z = T4}]
    pub fn flatten_tuples(&mut self) {
        if let TyKind::Tuple(tuple) = &mut self.kind {
            let mut new_fields = Vec::new();

            for (name, ty) in tuple.fields.drain(..) {
                if let Some(ty) = ty {
                    // recurse
                    // let ty = ty.flatten_tuples();

                    if let TyKind::Tuple(inner_fields) = ty.kind {
                        new_fields.extend(inner_fields.fields);

                        if self.lineage.is_none() {
                            self.lineage = ty.lineage
                        };
                        if self.instance_of.is_none() {
                            self.instance_of = ty.instance_of
                        };
                        continue;
                    }

                    new_fields.push((name, Some(ty)));
                    continue;
                }

                new_fields.push((name, ty));
            }

            tuple.fields.extend(new_fields);
        }
    }
}

fn is_not_super_type_of(sup: &Option<Ty>, sub: &Option<Ty>) -> bool {
    if let Some(sub_ret) = sub {
        if let Some(sup_ret) = sup {
            if !sup_ret.is_super_type_of(sub_ret) {
                return true;
            }
        }
    }
    false
}

impl std::fmt::Debug for Ty {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        std::fmt::Display::fmt(&self, f)
    }
}

impl From<PrimitiveSet> for TyKind {
    fn from(value: PrimitiveSet) -> Self {
        TyKind::Primitive(value)
    }
}

impl From<TyFunc> for TyKind {
    fn from(value: TyFunc) -> Self {
        TyKind::Function(Some(value))
    }
}

fn is_false(x: &bool) -> bool {
    !*x
}
