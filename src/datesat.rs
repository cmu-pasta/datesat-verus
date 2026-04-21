use vstd::prelude::*;
use vstd::map::*;
use crate::*;

verus! {


    pub struct Ast {
        pub root: BoolExpr,
    }

    pub enum BoolExpr {
        And(Box<BoolExpr>, Box<BoolExpr>),
        Or(Box<BoolExpr>, Box<BoolExpr>),
        Not(Box<BoolExpr>),
        Literal(bool),
        DateLt(Box<DateExpr>, Box<DateExpr>),
        DateEq(Box<DateExpr>, Box<DateExpr>),
    }

    pub enum IntExpr {
        Literal(int),
        Var(int),
        Year(Box<DateExpr>),
        Month(Box<DateExpr>),
        Day(Box<DateExpr>),
    }

    pub enum DateExpr {
        Literal(Box<IntExpr>, Box<IntExpr>, Box<IntExpr>),
        Var(int),
        Add(Box<DateExpr>, PeriodLiteral),
    }

    pub struct PeriodLiteral(pub int, pub int, pub int);

    impl PeriodLiteral {
        pub open spec fn to_period(self) -> Period {
            Period(self.0, self.1, self.2)
        }
    }

    pub struct Environment {
        pub int_vars: Map<int, int>,
        pub date_vars: Map<int, SimpleDate>,
    }

    impl Environment {
        pub open spec fn date_var_valid(self, id: int) -> bool {
            self.date_vars.dom().contains(id) && self.date_vars[id].is_valid()
        }
    }

    impl Ast {
        pub open spec fn eval<D: DateEncoding>(self, env: Environment) -> bool {
            self.root.eval::<D>(env)
        }
    }

    impl IntExpr {
        pub open spec fn eval<D: DateEncoding>(self, env: Environment) -> int
            decreases self,
        {
            match self {
                IntExpr::Literal(n) => n,
                IntExpr::Var(id) => env.int_vars[id],
                IntExpr::Year(d) => d.eval::<D>(env).year(),
                IntExpr::Month(d) => d.eval::<D>(env).month(),
                IntExpr::Day(d) => d.eval::<D>(env).day(),
            }
        }
    }

    impl DateExpr {
        pub open spec fn eval<D: DateEncoding>(self, env: Environment) -> D
            decreases self,
        {
            match self {
                DateExpr::Literal(y, m, d) => {
                    D::from_ymd(y.eval::<D>(env), m.eval::<D>(env), d.eval::<D>(env))
                },
                DateExpr::Var(id) => {
                    let sd = env.date_vars[id];
                    D::from_ymd(sd.year(), sd.month(), sd.day())
                },
                DateExpr::Add(base, period) => {
                    base.eval::<D>(env).add_period(period.to_period())
                },
            }
        }
    }

    impl BoolExpr {
        pub open spec fn eval<D: DateEncoding>(self, env: Environment) -> bool
            decreases self,
        {
            match self {
                BoolExpr::And(a, b) => a.eval::<D>(env) && b.eval::<D>(env),
                BoolExpr::Or(a, b) => a.eval::<D>(env) || b.eval::<D>(env),
                BoolExpr::Not(a) => !a.eval::<D>(env),
                BoolExpr::Literal(v) => v,
                BoolExpr::DateLt(a, b) => a.eval::<D>(env).lt(b.eval::<D>(env)),
                BoolExpr::DateEq(a, b) => a.eval::<D>(env).eq(b.eval::<D>(env)),
            }
        }
    }

    // ── Well-formedness ────────────────────────────────────────────────

    impl DateExpr {
        pub open spec fn is_wf(self, env: Environment) -> bool
            decreases self,
        {
            match self {
                DateExpr::Literal(y, m, d) => {
                    match (*y, *m, *d) {
                        (IntExpr::Literal(yv), IntExpr::Literal(mv), IntExpr::Literal(dv)) =>
                            SimpleDate(yv, mv, dv).is_valid(),
                        _ => false,
                    }
                },
                DateExpr::Var(id) => env.date_var_valid(id),
                DateExpr::Add(base, _) => base.is_wf(env),
            }
        }
    }

    impl IntExpr {
        pub open spec fn is_wf(self, env: Environment) -> bool
            decreases self,
        {
            match self {
                IntExpr::Literal(_) => true,
                IntExpr::Var(id) => env.int_vars.dom().contains(id),
                IntExpr::Year(d) => d.is_wf(env),
                IntExpr::Month(d) => d.is_wf(env),
                IntExpr::Day(d) => d.is_wf(env),
            }
        }
    }

    impl BoolExpr {
        pub open spec fn is_wf(self, env: Environment) -> bool
            decreases self,
        {
            match self {
                BoolExpr::And(a, b) => a.is_wf(env) && b.is_wf(env),
                BoolExpr::Or(a, b) => a.is_wf(env) && b.is_wf(env),
                BoolExpr::Not(a) => a.is_wf(env),
                BoolExpr::Literal(_) => true,
                BoolExpr::DateLt(a, b) => a.is_wf(env) && b.is_wf(env),
                BoolExpr::DateEq(a, b) => a.is_wf(env) && b.is_wf(env),
            }
        }
    }

    // ── EpochDelta equivalence proofs ───────────────────────────────────

    pub proof fn lemma_date_wf_implies_valid(e: DateExpr, env: Environment)
        requires e.is_wf(env),
        ensures e.eval::<SimpleDate>(env).is_valid(),
        decreases e,
    {
        match e {
            DateExpr::Literal(y, m, d) => {
                match (*y, *m, *d) {
                    (IntExpr::Literal(yv), IntExpr::Literal(mv), IntExpr::Literal(dv)) => {
                        assert(y.eval::<SimpleDate>(env) == yv);
                        assert(m.eval::<SimpleDate>(env) == mv);
                        assert(d.eval::<SimpleDate>(env) == dv);
                    },
                    _ => {},
                }
            },
            DateExpr::Var(id) => {},
            DateExpr::Add(base, period) => {
                lemma_date_wf_implies_valid(*base, env);
                theorem_date_add_period_preserves_validity(
                    base.eval::<SimpleDate>(env),
                    period.to_period(),
                );
            },
        }
    }


    pub proof fn lemma_date_expr_ed_congruent(e: DateExpr, env: Environment)
        requires e.is_wf(env),
        ensures ed_congruent(e.eval::<SimpleDate>(env), e.eval::<EpochDelta>(env)),
        decreases e,
    {
        match e {
            DateExpr::Literal(y, m, d) => {
                match (*y, *m, *d) {
                    (IntExpr::Literal(yv), IntExpr::Literal(mv), IntExpr::Literal(dv)) => {
                        assert(y.eval::<SimpleDate>(env) == yv);
                        assert(m.eval::<SimpleDate>(env) == mv);
                        assert(d.eval::<SimpleDate>(env) == dv);
                        assert(y.eval::<EpochDelta>(env) == yv);
                        assert(m.eval::<EpochDelta>(env) == mv);
                        assert(d.eval::<EpochDelta>(env) == dv);
                        theorem_epoch_delta_from_ymd_congruent(yv, mv, dv);
                    },
                    _ => {},
                }
            },
            DateExpr::Var(id) => {
                let sd = env.date_vars[id];
                theorem_epoch_delta_from_ymd_congruent(sd.year(), sd.month(), sd.day());
            },
            DateExpr::Add(base, period) => {
                lemma_date_expr_ed_congruent(*base, env);
                lemma_date_wf_implies_valid(*base, env);
                theorem_epoch_delta_add_period_preserves_congruence(
                    base.eval::<SimpleDate>(env),
                    base.eval::<EpochDelta>(env),
                    period.to_period(),
                );
            },
        }
    }

    pub proof fn lemma_int_expr_equiv(e: IntExpr, env: Environment)
        requires e.is_wf(env),
        ensures e.eval::<SimpleDate>(env) == e.eval::<EpochDelta>(env),
        decreases e,
    {
        match e {
            IntExpr::Literal(_) => {},
            IntExpr::Var(_) => {},
            IntExpr::Year(d) => {
                lemma_date_expr_ed_congruent(*d, env);
                lemma_date_wf_implies_valid(*d, env);
                let sd = d.eval::<SimpleDate>(env);
                theorem_epoch_delta_to_ymd_from_simple_date_inverse(sd);
            },
            IntExpr::Month(d) => {
                lemma_date_expr_ed_congruent(*d, env);
                lemma_date_wf_implies_valid(*d, env);
                let sd = d.eval::<SimpleDate>(env);
                theorem_epoch_delta_to_ymd_from_simple_date_inverse(sd);
            },
            IntExpr::Day(d) => {
                lemma_date_expr_ed_congruent(*d, env);
                lemma_date_wf_implies_valid(*d, env);
                let sd = d.eval::<SimpleDate>(env);
                theorem_epoch_delta_to_ymd_from_simple_date_inverse(sd);
            },
        }
    }


    pub proof fn lemma_bool_expr_equiv(e: BoolExpr, env: Environment)
        requires e.is_wf(env),
        ensures e.eval::<SimpleDate>(env) == e.eval::<EpochDelta>(env),
        decreases e,
    {
        match e {
            BoolExpr::And(a, b) => {
                lemma_bool_expr_equiv(*a, env);
                lemma_bool_expr_equiv(*b, env);
            },
            BoolExpr::Or(a, b) => {
                lemma_bool_expr_equiv(*a, env);
                lemma_bool_expr_equiv(*b, env);
            },
            BoolExpr::Not(a) => {
                lemma_bool_expr_equiv(*a, env);
            },
            BoolExpr::Literal(_) => {},
            BoolExpr::DateLt(a, b) => {
                lemma_date_expr_ed_congruent(*a, env);
                lemma_date_expr_ed_congruent(*b, env);
                lemma_date_wf_implies_valid(*a, env);
                lemma_date_wf_implies_valid(*b, env);
                theorem_epoch_delta_congruent_preserves_comparison(
                    a.eval::<SimpleDate>(env),
                    a.eval::<EpochDelta>(env),
                    b.eval::<SimpleDate>(env),
                    b.eval::<EpochDelta>(env),
                );
            },
            BoolExpr::DateEq(a, b) => {
                lemma_date_expr_ed_congruent(*a, env);
                lemma_date_expr_ed_congruent(*b, env);
                lemma_date_wf_implies_valid(*a, env);
                lemma_date_wf_implies_valid(*b, env);
                theorem_epoch_delta_congruent_preserves_comparison(
                    a.eval::<SimpleDate>(env),
                    a.eval::<EpochDelta>(env),
                    b.eval::<SimpleDate>(env),
                    b.eval::<EpochDelta>(env),
                );
            },
        }
    }


    pub proof fn theorem_ast_epoch_equiv(ast: Ast, env: Environment)
        requires ast.root.is_wf(env),
        ensures ast.eval::<SimpleDate>(env) == ast.eval::<EpochDelta>(env),
    {
        lemma_bool_expr_equiv(ast.root, env);
    }


} // verus!
