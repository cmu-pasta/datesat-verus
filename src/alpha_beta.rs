use vstd::prelude::*;
use crate::*;

verus! {

    /// A date represented as (alpha, beta) where:
    ///   - alpha = number of months elapsed since EPOCH (March 1, 2000)
    ///   - beta  = number of days elapsed in the calendar month (0-indexed)
    /// So AlphaBeta(0, 0) represents March 1, 2000.
    pub struct AlphaBeta(pub int, pub int);

    impl AlphaBeta {
        pub open spec fn alpha(&self) -> int {
            self.0
        }

        pub open spec fn beta(&self) -> int {
            self.1
        }

        pub open spec fn lt(self, other: Self) -> bool {
            self.alpha() < other.alpha()
            || (self.alpha() == other.alpha() && self.beta() < other.beta())
        }

        pub open spec fn leq(self, other: Self) -> bool {
            self.lt(other) || self == other
        }

        /// Convert a Date to AlphaBeta.
        /// alpha = years_since_epoch * 12 + months_since_march
        /// beta  = day - 1
        pub open spec fn from_ymd(date: Date) -> AlphaBeta {
            let alpha = years_since_epoch(date.year(), date.month()) * 12
                      + months_since_march(date.month());
            let beta = date.day() - 1;
            AlphaBeta(alpha, beta)
        }

        /// Convert AlphaBeta back to a Date.
        /// Uses EPOCH.add_months(alpha) to recover (year, month), then sets day = beta + 1.
        pub open spec fn to_ymd(self) -> Date {
            let Date(y, m, _) = EPOCH.add_months(self.alpha());
            Date(y, m, self.beta() + 1)
        }

        /// An AlphaBeta is valid when beta is in range for the calendar month
        /// determined by alpha.
        pub open spec fn is_valid(self) -> bool {
            let Date(y, m, _) = EPOCH.add_months(self.alpha());
            0 <= self.beta() && self.beta() < dim(y, m)
        }
    }

    // Congruence between Date and AlphaBeta: asserts they are related by from_ymd.
    pub open spec fn ab_congruent(d: Date, ab: AlphaBeta) -> bool {
        ab == AlphaBeta::from_ymd(d)
    }

    // Congruence at construction: from_ymd(d) is congruent with d.
    pub proof fn theorem_ab_congruent_at_construction(d: Date)
        ensures ab_congruent(d, AlphaBeta::from_ymd(d)),
    {}

} // verus!
