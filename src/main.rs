use vstd::prelude::*;
use vstd::math::*;

mod monotonicity;
use monotonicity::*;

mod epoch_delta;
use epoch_delta::*;

mod hybrid;
use hybrid::*;

mod alpha_beta;
use alpha_beta::*;

verus! {

    /// A calendar date in (year, month, day) form.
    pub struct Date(pub int, pub int, pub int);

    /// The epoch: March 1, 2000. Chosen so that the leap day (Feb 29) falls
    /// at the end of the epoch-year, simplifying the from_ymd formula.
    pub spec const EPOCH : Date = Date(2000, 3, 1);

    impl Date {
        pub open spec fn year(&self) -> int {
            self.0
        }

        pub open spec fn month(&self) -> int {
            self.1
        }

        pub open spec fn day(&self) -> int {
            self.2
        }

        /// Lexicographic strict ordering on dates: year, then month, then day.
        pub open spec fn lt(self, other: Self) -> bool {
            self.year() < other.year() ||
            (self.year() == other.year() && self.month() < other.month()) ||
            (self.year() == other.year() && self.month() == other.month() && self.day() < other.day())
        }

        /// Non-strict ordering: less-than or equal.
        pub open spec fn leq(self, other: Self) -> bool {
            self.lt(other) || self == other
        }

        /// A date is valid when its month is in 1..12 and its day is in 1..dim(year, month).
        pub open spec fn is_valid(self) -> bool {
            1 <= self.month() <= 12 && 1 <= self.day() <= dim(self.year(), self.month())
        }

    }

    /// Whether a year is a leap year (Gregorian rule).
    pub open spec fn leap(year: int) -> bool {
        year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)
    }

    /// Days in month: the number of days in the given month of the given year.
    pub open spec fn dim(year: int, month: int) -> int {
        let calendar = [31, if leap(year) { 29 } else { 28 }, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
        calendar[month - 1]
    }

    // ── Date and calendar proofs ──────────────────────────────────────

    pub proof fn lemma_dim_is_bounded(year: int, month: int)
        requires 1 <= month <= 12,
        ensures 28 <= dim(year, month) <= 31
    {
        // QED
    }

    proof fn lemma_epoch_is_valid() {
        EPOCH.is_valid();
    }

    pub proof fn lemma_date_leq_is_reflexive(d: Date)
        ensures d.leq(d) {}

    pub proof fn lemma_date_leq_is_transitive(d1: Date, d2: Date, d3: Date)
        requires d1.leq(d2) && d2.leq(d3),
        ensures d1.leq(d3) {}

    proof fn lemma_date_leq_is_antisymmetric(d1: Date, d2: Date)
        requires d1.leq(d2) && d2.leq(d1),
        ensures d1 == d2 {}

    proof fn lemma_date_lt_is_irreflexive(d: Date)
        ensures !d.lt(d) {}

    proof fn lemma_date_lt_is_asymmetric(d1: Date, d2: Date)
        requires d1.lt(d2),
        ensures !d2.lt(d1) {}

    proof fn lemma_date_lt_is_transitive(d1: Date, d2: Date, d3: Date)
        requires d1.lt(d2) && d2.lt(d3),
        ensures d1.lt(d3) {}

    pub proof fn lemma_date_lt_implies_leq(d1: Date, d2: Date)
        requires d1.lt(d2),
        ensures d1.leq(d2) {}

    proof fn lemma_date_lt_implies_neq(d1: Date, d2: Date)
        requires d1.lt(d2),
        ensures d1 != d2 {}

    proof fn lemma_date_leq_neq_implies_lt(d1: Date, d2: Date)
        requires d1.leq(d2) && d1 != d2,
        ensures d1.lt(d2) {}

    pub proof fn lemma_date_lt_is_total(d1: Date, d2: Date)
        ensures d1 == d2 || d1.lt(d2) || d2.lt(d1)
    {}

    // ── Period ────────────────────────────────────────────────────────

    /// A calendar period expressed as (years, months, days).
    pub struct Period(pub int, pub int, pub int);

    impl Period {
        pub open spec fn years(&self) -> int {
            self.0
        }

        pub open spec fn months(&self) -> int {
            self.1
        }
        pub open spec fn days(&self) -> int {
            self.2
        }

        /// Component-wise addition of two periods.
        spec fn add(self, other: Self) -> Period {
            Period(self.years() + other.years(),
                self.months() + other.months(), self.days() + other.days())
        }

        /// Component-wise scaling of a period by an integer factor.
        spec fn scale(self, factor: int) -> Period {
            Period(self.years() * factor, self.months() * factor, self.days() * factor)
        }
    }

    proof fn lemma_period_add_zero_identity(p: Period)
        ensures p.add(Period(0,0,0)) == p {}

    proof fn lemma_period_add_commutative(p1: Period, p2: Period)
        ensures p1.add(p2) == p2.add(p1) {}

    proof fn lemma_period_add_associative(p1: Period, p2: Period, p3: Period)
        ensures p1.add(p2).add(p3) == p1.add(p2.add(p3)) {}

    proof fn lemma_period_scale_identity(p: Period)
        ensures p.scale(1) == p {}

    #[cfg(slow_proofs)]
    proof fn lemma_period_scale_commutative(p: Period, f1: int, f2: int) by (nonlinear_arith)
        ensures p.scale(f1).scale(f2) == p.scale(f2).scale(f1) {}

    #[cfg(slow_proofs)]
    proof fn lemma_period_scale_associative(p: Period, f1: int, f2: int) by (nonlinear_arith)
        ensures p.scale(f1).scale(f2) == p.scale(f1*f2) {}

    // ── Date-period arithmetic ────────────────────────────────────────

    impl Date {
        /// Add n months to a date, clamping the day to the new month's dim.
        pub open spec fn add_months(self, n: int) -> Date {
            let Date(y, m, d) = self;
            let y_ = y + (m - 1 + n) / 12;
            let m_ = 1 + ((m - 1 + n) % 12);
            let d_ = min(d, dim(y_, m_));
            Date(y_, m_, d_)
        }

        /// Add n days to a date (positive or negative), recursively stepping
        /// across month boundaries using the ADD-DAYS-OVER / ADD-DAYS-UNDER rules.
        pub open spec fn add_days(self, n: int) -> Date
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

        /// Add a calendar period: first add years/months (as months), then add days.
        pub open spec fn add_period(self, period: Period) -> Date
        {
            self.add_months(period.years() * 12 + period.months()).add_days(period.days())
        }
    }

    // ── Date-period arithmetic proofs ─────────────────────────────────

    pub proof fn lemma_date_add_months_preserves_validity(date: Date, n: int)
        requires date.is_valid(),
        ensures date.add_months(n).is_valid()
    {
        // QED
    }

    proof fn lemma_date_add_days_pos_preserves_validity(date: Date, n: int)
        requires date.is_valid() && n >= 0,
        ensures date.add_days(n).is_valid(),
        decreases n
    {
        let Date(y, m, d) = date;
        if 1 <= d + n <= dim(y, m) {
            // Base case: ADD-DAYS rule; trivially valid
        } else {
            // ADD-DAYS-OVER rule
            assert(d + n > dim(y, m));
            let n_ = n - (dim(y, m) - d) - 1;
            lemma_date_add_days_pos_preserves_validity(Date(y, m, 1).add_months(1), n_);
        }
    }

    proof fn lemma_date_add_days_neg_preserves_validity(date: Date, n: int)
        requires date.is_valid() && n < 0,
        ensures date.add_days(n).is_valid(),
        decreases abs(n)
    {
        let Date(y, m, d) = date;
        if 1 <= d + n {
            // Base case: ADD-DAYS rule
            assert(d + n <= dim(y, m)); // since date.is_valid() && n < 0
        } else if d > 1 {
            // ADD-DAYS-UNDER1 rule
            assert(d <= dim(y, m));
            assert(d + n <= 0);
            lemma_date_add_days_neg_preserves_validity(Date(y, m, 1), d - 1 + n);
        } else {
            // ADD-DAYS-UNDER2 rule
            assert(d == 1);
            assert(d <= dim(y, m));
            let Date(y_, m_, _) = date.add_months(-1);
            let n_ = n + dim(y_, m_);
            // Split into positive and negative cases when recursing
            if n_ >= 0 {
                lemma_date_add_days_pos_preserves_validity(Date(y_, m_, 1), n_)
            } else {
                lemma_date_add_days_neg_preserves_validity(Date(y_, m_, 1), n_)
            }
        }
    }

    pub proof fn lemma_date_add_days_preserves_validity(date: Date, n: int)
        requires date.is_valid(),
        ensures date.add_days(n).is_valid()
    {
        if n < 0 {
            lemma_date_add_days_neg_preserves_validity(date, n);
        } else {
            lemma_date_add_days_pos_preserves_validity(date, n);
        }
    }

    proof fn theorem_date_add_period_preserves_validity(date: Date, period: Period)
        requires date.is_valid(),
        ensures date.add_period(period).is_valid()
    {
        let months_to_add = period.years() * 12 + period.months();
        lemma_date_add_months_preserves_validity(date, months_to_add);
        let d_ = date.add_months(months_to_add);
        lemma_date_add_days_preserves_validity(d_, period.days());
    }


    fn main() {
        // Theorem 1: Well-formedness
        assert forall|d: Date, p: Period| #![auto]
            d.is_valid() implies d.add_period(p).is_valid() by { theorem_date_add_period_preserves_validity(d, p); }

        // Theorem 2: Monotonicity of Date-Period Addition
        assert forall|d1: Date, d2: Date, p: Period| #![auto]
            d1.is_valid() && d2.is_valid() && d1.leq(d2) implies
                d1.add_period(p).leq(d2.add_period(p)) by { theorem_date_add_period_is_monotonic(d1, d2, p); }

        // Theorem 3: Round-trip conversion of Epoch-based representation
        assert forall|ed: EpochDelta| #![auto]
            EpochDelta::from_ymd(EpochDelta::to_ymd(ed)) == ed by { theorem_epoch_delta_from_ymd_to_ymd_inverse(ed); }

        // Theorem 4: Inverse round-trip for valid dates
        assert forall|d: Date| #![auto]
            d.is_valid() implies EpochDelta::to_ymd(EpochDelta::from_ymd(d)) == d by { theorem_epoch_delta_to_ymd_from_ymd_inverse(d); }

        // Theorem 5: EpochDelta congruence at construction
        assert forall|d: Date| #![auto]
            congruent(d, EpochDelta::from_ymd(d))
            by { theorem_epoch_delta_congruent_at_construction(d); }

        // Theorem 6: Congruent pairs agree on ordering and equality
        assert forall|d1: Date, ed1: EpochDelta, d2: Date, ed2: EpochDelta| #![auto]
            d1.is_valid() && d2.is_valid() && congruent(d1, ed1) && congruent(d2, ed2) implies
                (d1.lt(d2) <==> ed1.lt(ed2)) && (d1 == d2 <==> ed1 == ed2)
            by { theorem_epoch_delta_congruent_preserves_comparison(d1, ed1, d2, ed2); }

        // Theorem 7: Congruence is preserved under period addition
        assert forall|d: Date, ed: EpochDelta, p: Period| #![auto]
            d.is_valid() && congruent(d, ed) implies
                congruent(d.add_period(p), ed.add_period(p))
            by { theorem_epoch_delta_add_period_preserves_congruence(d, ed, p); }

        // Theorem 8: Hybrid congruence at construction (from_ymd)
        assert forall|d: Date| #![auto]
            d.is_valid() implies hybrid_congruent(d, Hybrid::from_ymd(d))
            by { theorem_hybrid_from_ymd_congruent(d); }

        // Theorem 9: Hybrid congruence at construction (from_epoch_delta)
        assert forall|ed: EpochDelta| #![auto]
            hybrid_congruent(ed.to_ymd(), Hybrid::from_epoch_delta(ed))
            by { theorem_hybrid_from_epoch_delta_congruent(ed); }

        // Theorem 10: Hybrid congruent pairs preserve comparison
        assert forall|d1: Date, h1: Hybrid, d2: Date, h2: Hybrid| #![auto]
            d1.is_valid() && d2.is_valid()
            && hybrid_congruent(d1, h1) && hybrid_congruent(d2, h2)
            && (h1.ymd() || h1.epoch()) && (h2.ymd() || h2.epoch()) implies
                (h1.lt(h2) <==> d1.lt(d2)) && (h1.eq(h2) <==> d1 == d2)
            by { theorem_hybrid_congruent_preserves_comparison(d1, h1, d2, h2); }

        // Theorem 11: Hybrid congruence and validity preserved under period addition
        assert forall|d: Date, h: Hybrid, p: Period| #![auto]
            d.is_valid() && hybrid_congruent(d, h) implies
                hybrid_congruent(d.add_period(p), h.add_period(p))
            by { theorem_hybrid_add_period_preserves_congruence(d, h, p); }

    }

} // verus!