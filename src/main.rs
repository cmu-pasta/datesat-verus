use vstd::prelude::*;
use vstd::math::*;

verus! {

    struct Date(int, int, int);

    spec const EPOCH : Date = Date(2000, 3, 1);

    impl Date {
        spec fn year(&self) -> int {
            self.0
        }

        spec fn month(&self) -> int {
            self.1
        }

        spec fn day(&self) -> int {
            self.2
        }

        spec fn lt(self, other: Self) -> bool {
            self.year() < other.year() ||
            (self.year() == other.year() && self.month() < other.month()) ||
            (self.year() == other.year() && self.month() == other.month() && self.day() < other.day())
        }

        spec fn leq(self, other: Self) -> bool {
            self.lt(other) || self == other
        }

        spec fn is_valid(self) -> bool {
            1 <= self.month() <= 12 && 1 <= self.day() <= dim(self.year(), self.month())
        }

    }

    spec fn leap(year: int) -> bool {
        year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
    }

    spec fn dim(year: int, month: int) -> int {
        let calendar = [31, if leap(year) { 29 } else { 28 }, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
        calendar[month - 1]
    }

    proof fn dim_is_bounded(year: int, month: int)
        requires 1 <= month <= 12,
        ensures 28 <= dim(year, month) <= 31
    {
        // QED
    }

    proof fn epoch_is_valid() {
        EPOCH.is_valid();
    }

    proof fn date_leq_is_reflexive(d: Date)
        ensures d.leq(d) {}

    proof fn date_leq_is_transitive(d1: Date, d2: Date, d3: Date)
        requires d1.leq(d2) && d2.leq(d3),
        ensures d1.leq(d3) {}

    proof fn date_leq_is_antisymmetric(d1: Date, d2: Date)
        requires d1.leq(d2) && d2.leq(d1),
        ensures d1 == d2 {}

    proof fn date_lt_is_irreflexive(d: Date)
        ensures !d.lt(d) {}

    proof fn date_lt_is_asymmetric(d1: Date, d2: Date)
        requires d1.lt(d2),
        ensures !d2.lt(d1) {}

    proof fn date_lt_is_transitive(d1: Date, d2: Date, d3: Date)
        requires d1.lt(d2) && d2.lt(d3),
        ensures d1.lt(d3) {}

    proof fn date_lt_implies_leq(d1: Date, d2: Date)
        requires d1.lt(d2),
        ensures d1.leq(d2) {}

    proof fn date_lt_implies_neq(d1: Date, d2: Date)
        requires d1.lt(d2),
        ensures d1 != d2 {}

    proof fn date_leq_neq_implies_lt(d1: Date, d2: Date)
        requires d1.leq(d2) && d1 != d2,
        ensures d1.lt(d2) {}

    struct Period(int, int, int);

    impl Period {
        spec fn years(&self) -> int {
            self.0
        }

        spec fn months(&self) -> int {
            self.1
        }
        spec fn days(&self) -> int {
            self.2
        }

        spec fn add(self, other: Self) -> Period {
            Period(self.years() + other.years(),
                self.months() + other.months(), self.days() + other.days())
        }

        spec fn scale(self, factor: int) -> Period {
            Period(self.years() * factor, self.months() * factor, self.days() * factor)
        }
    }

    proof fn period_add_zero_identity(p: Period)
        ensures p.add(Period(0,0,0)) == p {}

    proof fn period_add_commutative(p1: Period, p2: Period)
        ensures p1.add(p2) == p2.add(p1) {}

    proof fn period_add_associative(p1: Period, p2: Period, p3: Period)
        ensures p1.add(p2).add(p3) == p1.add(p2.add(p3)) {}

    proof fn period_scale_identity(p: Period)
        ensures p.scale(1) == p {}

    // proof fn period_scale_commutative(p: Period, f1: int, f2: int) by (nonlinear_arith)
    //     ensures p.scale(f1).scale(f2) == p.scale(f2).scale(f1) {}
    //
    // proof fn period_scale_associative(p: Period, f1: int, f2: int) by (nonlinear_arith)
    //     ensures p.scale(f1).scale(f2) == p.scale(f1*f2) {}

    impl Date {
        spec fn add_months(self, n: int) -> Date {
            let Date(y, m, d) = self;
            let y_ = y + (m - 1 + n) / 12;
            let m_ = 1 + ((m - 1 + n) % 12);
            let d_ = min(d, dim(y_, m_));
            Date(y_, m_, d_)
        }

        proof fn add_months_is_valid(self, n: int)
            requires self.is_valid(),
            ensures self.add_months(n).is_valid()
        {
            // QED
        }

        spec fn add_days(self, n: int) -> Date
            recommends self.is_valid(),
            decreases (n < 0) as nat, abs(n) // see note for ADD-DAYS-UNDER-2
        {
            let Date(y, m, d) = self;

            if 1 <= d <= dim(y, m) {
                if 1 <= d + n <= dim(y, m) {
                    // ADD_DAYS rule
                    Date(y, m, d + n)
                } else if (d + n > dim(y, m)) {
                    // ADD-DAYS-OVER rule
                    Date(y, m, 1).add_months(1).add_days(n - (dim(y, m) - d) - 1)
                } else if d > 1 {
                    // ADD-DAYS-UNDER1 rule
                    //assert(d + n <= 0); // covered all positive cases above
                    Date(y, m, 1).add_days(d - 1 + n)
                } else {
                    // ADD-DAYS-UNDER2 rule
                    // assert(d == 1);
                    // assert(1 + n <= 0);
                    let Date(y_, m_, _) = self.add_months(-1);
                    Date(y_, m_, 1).add_days(n + dim(y_, m_))
                    // Note: Proving that this case actually does cause
                    // recursion to terminate is tricky. For example, if we
                    // are adding -70 days, then recursively could go down to
                    // -39 days, -9 days, and then +21 days!! But we know that
                    // once we are adding positive number of days, the
                    // ADD-DAYS/ADD-DAYS-OVER rules always reduce down to zero.
                    // So, the `decreases` clause in the spec takes into account
                    // both the sign of `n` and its absolute value.
                }
             } else {
                Date(0, 0, 0) // spec is undefined for invalid dates
            }

        }

        proof fn add_days_positive_is_valid(self, n: int)
            requires self.is_valid() && n >= 0,
            ensures self.add_days(n).is_valid(),
            decreases n
        {
            let Date(y, m, d) = self;
            if 1 <= d + n <= dim(y, m) {
                // Base case: ADD-DAYS rule; trivially valid
            } else {
                // ADD-DAYS-OVER rule
                assert(d + n > dim(y, m));
                let n_ = n - (dim(y, m) - d) - 1;
                Date(y, m, 1).add_months(1).add_days_positive_is_valid(n_);
            }
        }

        proof fn add_days_negative_is_valid(self, n: int)
            requires self.is_valid() && n < 0,
            ensures self.add_days(n).is_valid(),
            decreases abs(n)
        {
            let Date(y, m, d) = self;
            if 1 <= d + n {
                // Base case: ADD-DAYS rule
                assert(d + n <= dim(y, m)); // since self.is_valid() && n < 0
            } else if d > 1 {
                // ADD-DAYS-UNDER1 rule
                assert(d <= dim(y, m));
                assert(d + n <= 0);
                Date(y, m, 1).add_days_negative_is_valid(d - 1 + n);
            } else {
                // ADD-DAYS-UNDER2 rule
                assert(d == 1);
                assert(d <= dim(y, m));
                let Date(y_, m_, _) = self.add_months(-1);
                let n_ = n + dim(y_, m_);
                // Split into positive and negative cases when recursing
                if n_ >= 0 {
                    Date(y_, m_, 1).add_days_positive_is_valid(n_)
                } else {
                    Date(y_, m_, 1).add_days_negative_is_valid(n_)
                }
            }
        }

        proof fn add_days_is_valid(self, n: int)
            requires self.is_valid(),
            ensures self.add_days(n).is_valid()
        {
            if n < 0 {
                self.add_days_negative_is_valid(n);
            } else {
                self.add_days_positive_is_valid(n);
            }
        }

        spec fn add_period(self, period: Period) -> Date
        {
            self.add_months(period.years() * 12 + period.months()).add_days(period.days())
        }

        proof fn add_period_is_valid(self, period: Period)
            requires self.is_valid(),
            ensures self.add_period(period).is_valid()
        {
            let months_to_add = period.years() * 12 + period.months();
            self.add_months_is_valid(months_to_add);
            let d_ = self.add_months(months_to_add);
            d_.add_days_is_valid(period.days());
        }

        // Monotonicity of Date-Period Addition
        // proof fn add_period_is_monotonic(d1: Date, d2: Date, p: Period)
        //     requires d1.lt(d2),
        //     ensures d1.add_period(p).leq(d2.add_period(p))
        // {
        //
        // }
    }

    fn main() {
        // Theorem 1: Well-formedness
        assert forall|d: Date, p: Period| #![auto]
            d.is_valid() implies d.add_period(p).is_valid() by { d.add_period_is_valid(p); }


    }

} // verus!