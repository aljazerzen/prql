mod expr;
mod flatten;
mod functions;
mod name_resolution;
mod static_eval;
mod stmt;
mod transforms;
mod types;

use crate::ir::decl::RootModule;
use crate::semantic::{NS_PARAM, NS_STD};
use crate::utils::IdGenerator;

/// Can fold (walk) over AST and for each function call or variable find what they are referencing.
pub struct Resolver {
    pub root_mod: RootModule,

    pub current_module_path: Vec<String>,

    /// Sometimes ident closures must be resolved and sometimes not. See [test::test_func_call_resolve].
    pub(super) in_func_call_name: bool,

    disable_type_checking: bool,

    pub id: IdGenerator<usize>,

    pub options: ResolverOptions,
}

#[derive(Default, Clone)]
pub struct ResolverOptions {
    pub allow_module_decls: bool,
}

impl Resolver {
    pub fn new(root_mod: RootModule, options: ResolverOptions) -> Self {
        Resolver {
            root_mod,
            options,
            current_module_path: Vec::new(),
            in_func_call_name: false,
            disable_type_checking: false,
            id: IdGenerator::new(),
        }
    }
}

#[cfg(test)]
pub(super) mod test {
    use anyhow::Result;
    use insta::assert_yaml_snapshot;

    use crate::ir::pl::{Expr, PlFold, Ty};

    pub fn erase_ids(expr: Expr) -> Expr {
        IdEraser {}.fold_expr(expr).unwrap()
    }

    struct IdEraser {}

    impl PlFold for IdEraser {
        fn fold_expr(&mut self, mut expr: Expr) -> Result<Expr> {
            expr.kind = self.fold_expr_kind(expr.kind)?;
            expr.id = None;
            expr.target_id = None;
            Ok(expr)
        }
    }

    fn parse_and_resolve(query: &str) -> Result<Expr> {
        let ctx = crate::semantic::test::parse_and_resolve(query)?;
        let (main, _) = ctx.find_main_rel(&[]).unwrap();
        Ok(main.clone())
    }

    fn resolve_ty(query: &str) -> Result<Ty> {
        Ok(parse_and_resolve(query)?.ty.unwrap())
    }

    fn resolve_derive(query: &str) -> Result<Vec<Expr>> {
        let expr = parse_and_resolve(query)?;
        let derive = expr.kind.into_transform_call().unwrap();
        let exprs = derive
            .kind
            .into_derive()
            .unwrap_or_else(|e| panic!("Failed to convert `{e:?}`"))
            .kind
            .into_tuple()
            .unwrap_or_else(|e| panic!("Failed to convert `{e:?}`"));
        let exprs = IdEraser {}.fold_exprs(exprs).unwrap();
        Ok(exprs)
    }

    #[test]
    fn test_variables_1() {
        assert_yaml_snapshot!(resolve_derive(
            r#"
            from employees
            derive {
                gross_salary = salary + payroll_tax,
                gross_cost =   gross_salary + benefits_cost
            }
            "#
        )
        .unwrap());
    }

    #[test]
    fn test_non_existent_function() {
        parse_and_resolve(r#"from mytable | filter (myfunc col1)"#).unwrap_err();
    }

    #[test]
    fn test_functions_1() {
        assert_yaml_snapshot!(resolve_derive(
            r#"
            let subtract = a b -> a - b

            from employees
            derive {
                net_salary = subtract gross_salary tax
            }
            "#
        )
        .unwrap());
    }

    #[test]
    fn test_functions_nested() {
        assert_yaml_snapshot!(resolve_derive(
            r#"
            let lag_day = x -> s"lag_day_todo({x})"
            let ret = x dividend_return ->  x / (lag_day x) - 1 + dividend_return

            from a
            derive (ret b c)
            "#
        )
        .unwrap());
    }

    #[test]
    fn test_functions_pipeline() {
        assert_yaml_snapshot!(resolve_derive(
            r#"
            from a
            derive one = (foo | sum)
            "#
        )
        .unwrap());

        assert_yaml_snapshot!(resolve_derive(
            r#"
            let plus_one = x -> x + 1
            let plus = x y -> x + y

            from a
            derive {b = (sum foo | plus_one | plus 2)}
            "#
        )
        .unwrap());
    }
    #[test]
    fn test_named_args() {
        assert_yaml_snapshot!(resolve_derive(
            r#"
            let add_one = x to:1 -> x + to

            from foo_table
            derive {
                added = add_one bar to:3,
                added_default = add_one bar
            }
            "#
        )
        .unwrap());
    }

    #[test]
    fn test_frames_and_names() {
        assert_yaml_snapshot!(resolve_ty(
            r#"
            from orders
            select {customer_no, gross, tax, gross - tax}
            take 20
            "#
        )
        .unwrap());

        assert_yaml_snapshot!(resolve_ty(
            r#"
            from table_1
            join customers (==customer_no)
            "#
        )
        .unwrap());

        assert_yaml_snapshot!(resolve_ty(
            r#"
            from e = employees
            join salaries (==emp_no)
            group {e.emp_no, e.gender} (
                aggregate {
                    emp_salary = average salaries.salary
                }
            )
            "#
        )
        .unwrap());
    }

    #[test]
    fn test_tuple_field_name_inference() {
        // test that:
        // - type contains aliases,
        // - names are not duplicated, but overridden,
        // - when using plain ident without alias, the ident is used as alias (TODO)
        assert_yaml_snapshot!(resolve_ty(
            r#"
            [{a = 1, b = 2, a = 3}]
            "#
        )
        .unwrap(), @r###"
        ---
        kind:
          Array:
            kind:
              Tuple:
                - Single:
                    - ~
                    - kind:
                        Primitive: Int
                      lineage: 180
                - Single:
                    - b
                    - kind:
                        Primitive: Int
                      lineage: 181
                - Single:
                    - a
                    - kind:
                        Primitive: Int
                      lineage: 182
            lineage: 179
        lineage: 178
        "###);
    }

    #[test]
    fn test_tuple_field_exclude() {
        assert_yaml_snapshot!(resolve_ty(
            r#"
            from tracks
            select (std.tuple_exclude {track_id, milliseconds, title, price} {milliseconds, title})
            "#
        )
        .unwrap(), @r###"
        ---
        kind:
          Array:
            kind:
              Tuple:
                - Single:
                    - track_id
                    - kind: Any
                      lineage: 203
                      infer: true
                - Single:
                    - price
                    - kind: Any
                      lineage: 203
                      infer: true
            lineage: 210
        "###);

        assert_yaml_snapshot!(resolve_ty(
            r#"
            from tracks
            select !{title, composer}
            "#
        )
        .unwrap(), @r###"
        ---
        kind:
          Array:
            kind:
              Tuple:
                - All:
                    ty:
                      kind: Any
                      lineage: 203
                      instance_of:
                        - default_db
                        - tracks
                      infer: true
                    exclude:
                      - - title
                      - - composer
            lineage: 203
            instance_of:
              - default_db
              - tracks
        "###);
    }
}
