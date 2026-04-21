use vstd::prelude::*;
use crate::*;

verus! {

    pub struct Environment;

    pub struct PeriodLiteral(pub int, pub int, pub int);

    impl PeriodLiteral {
        pub open spec fn to_period(self) -> Period {
            Period(self.0, self.1, self.2)
        }
    }

    pub enum IntExpr {
        Literal(int),
        Year(Box<DateExpr>),
        Month(Box<DateExpr>),
        Day(Box<DateExpr>),
    }

    pub enum DateExpr {
        Literal(Box<IntExpr>, Box<IntExpr>, Box<IntExpr>),
        Add(Box<DateExpr>, PeriodLiteral),
    }

    pub enum BoolExpr {
        And(Box<BoolExpr>, Box<BoolExpr>),
        Or(Box<BoolExpr>, Box<BoolExpr>),
        Not(Box<BoolExpr>),
        Literal(bool),
        DateLt(Box<DateExpr>, Box<DateExpr>),
        DateEq(Box<DateExpr>, Box<DateExpr>),
    }

    pub struct Ast {
        pub root: BoolExpr,
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

    pub open spec fn date_lit(y: int, m: int, d: int) -> DateExpr {
        DateExpr::Literal(
            Box::new(IntExpr::Literal(y)),
            Box::new(IntExpr::Literal(m)),
            Box::new(IntExpr::Literal(d)),
        )
    }

} // verus!
