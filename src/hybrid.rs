use vstd::prelude::*;
use crate::*;

verus! {

    /// A hybrid date representation that can hold a YMD form, an epoch-delta form, or both.
    ///
    /// Fields: (year, month, day, delta, ymd, epoch)
    ///   - If `ymd`   is true, Date(year, month, day) is a valid representation of this date.
    ///   - If `epoch` is true, EpochDelta(delta) is a valid representation of this date.
    ///   - At least one flag must always be true.
    ///   - Both may be true when the two representations are consistent.
    pub struct Hybrid(pub int, pub int, pub int, pub int, pub bool, pub bool);

    impl Hybrid {
        pub open spec fn year(&self) -> int { self.0 }
        pub open spec fn month(&self) -> int { self.1 }
        pub open spec fn day(&self) -> int { self.2 }
        pub open spec fn delta(&self) -> int { self.3 }
        pub open spec fn ymd(&self) -> bool { self.4 }
        pub open spec fn epoch(&self) -> bool { self.5 }

        /// A Hybrid is valid when:
        ///   - at least one representation flag is set, and
        ///   - if the YMD flag is set, the stored (year, month, day) form a valid date.
        /// (Consistency between the two representations is a separate concern.)
        pub open spec fn is_valid(self) -> bool {
            (self.ymd() || self.epoch())
            && (self.ymd() ==> Date(self.year(), self.month(), self.day()).is_valid())
        }

        /// Construct a Hybrid from a YMD date (lazy: epoch delta is not computed).
        pub open spec fn from_ymd(date: Date) -> Hybrid {
            Hybrid(date.year(), date.month(), date.day(), 0, true, false)
        }

        /// Construct a Hybrid from an EpochDelta (lazy: YMD components are not computed).
        pub open spec fn from_epoch_delta(ed: EpochDelta) -> Hybrid {
            Hybrid(0, 0, 0, ed.delta(), false, true)
        }

        /// Recover the YMD date.
        /// Uses the stored YMD components directly when available, otherwise converts
        /// from the epoch delta.
        pub open spec fn to_ymd(self) -> Date {
            if self.ymd() {
                Date(self.year(), self.month(), self.day())
            } else {
                EpochDelta(self.delta()).to_ymd()
            }
        }

        /// Recover the EpochDelta.
        /// Uses the stored delta directly when available (preferred), otherwise converts
        /// from the YMD components.
        pub open spec fn to_epoch_delta(self) -> EpochDelta {
            if self.epoch() {
                EpochDelta(self.delta())
            } else {
                EpochDelta::from_ymd(Date(self.year(), self.month(), self.day()))
            }
        }

        /// Less-than comparison.
        /// Prefers epoch delta form (integer comparison) when both have `epoch` set;
        /// falls back to Date::lt when both have `ymd` set;
        /// converts to epoch delta when flags are inconsistent.
        pub open spec fn lt(self, other: Self) -> bool {
            if self.epoch() && other.epoch() {
                self.to_epoch_delta().lt(other.to_epoch_delta()) // fast
            } else if self.ymd() && other.ymd() {
                self.to_ymd().lt(other.to_ymd())// fast
            } else {
                self.to_epoch_delta().lt(other.to_epoch_delta()) // slow
            }
        }

        /// Equality comparison (not structural — respects lazy semantics).
        /// Same flag-priority logic as lt.
        pub open spec fn eq(self, other: Self) -> bool {
            if self.epoch() && other.epoch() {
                self.to_epoch_delta() == other.to_epoch_delta() // fast
            } else if self.ymd() && other.ymd() {
                self.to_ymd() == other.to_ymd() // fast
            } else {
                self.to_epoch_delta() == other.to_epoch_delta() // slow
            }
        }

        /// Less-than-or-equal, defined as lt or eq.
        pub open spec fn leq(self, other: Self) -> bool {
            self.lt(other) || self.eq(other)
        }

        /// Add a period to this hybrid date, choosing the most efficient representation.
        ///
        /// Case 1 — pure day addition (years == 0, months == 0):
        ///   Use epoch delta semantics (just integer addition). Result is epoch-only.
        ///
        /// Case 2 — year/month addition with no day component (days == 0):
        ///   Use YMD semantics (add_months). Result is YMD-only.
        ///
        /// Case 3 — year/month addition with a non-zero day component:
        ///   Add years/months in YMD, then convert to epoch and add days by integer
        ///   arithmetic (avoiding the recursive Date::add_days entirely). Result is epoch-only.
        pub open spec fn add_period(self, p: Period) -> Hybrid {
            if p.years() == 0 && p.months() == 0 {
                // Case 1: pure day addition — epoch arithmetic
                Hybrid(0, 0, 0, self.to_epoch_delta().delta() + p.days(), false, true)
            } else if p.days() == 0 {
                // Case 2: year/month addition only — stay in YMD form
                let d = self.to_ymd().add_months(p.years() * 12 + p.months());
                Hybrid(d.year(), d.month(), d.day(), 0, true, false)
            } else {
                // Case 3: year/month + day — add months in YMD, convert to epoch, add days
                let d = self.to_ymd().add_months(p.years() * 12 + p.months());
                let ed = EpochDelta::from_ymd(d);
                Hybrid(0, 0, 0, ed.delta() + p.days(), false, true)
            }
        }
    }

    /// Congruence between a Date and a Hybrid, respecting the lazy representation.
    /// If `ymd` is set, the stored YMD must match the date.
    /// If `epoch` is set, the stored delta must equal from_ymd(d).
    pub open spec fn hybrid_congruent(d: Date, h: Hybrid) -> bool {
        (h.ymd() ==> d == Date(h.year(), h.month(), h.day()))
        && (h.epoch() ==> EpochDelta(h.delta()) == EpochDelta::from_ymd(d))
    }

    // ── Hybrid congruence proofs ──────────────────────────────────────

    // Lemma A: from_ymd constructs a congruent Hybrid.
    pub proof fn lemma_hybrid_from_ymd_congruent(d: Date)
        requires d.is_valid(),
        ensures hybrid_congruent(d, Hybrid::from_ymd(d)),
    {}

    // Lemma B: from_epoch_delta constructs a congruent Hybrid.
    pub proof fn lemma_hybrid_from_epoch_delta_congruent(ed: EpochDelta)
        ensures hybrid_congruent(ed.to_ymd(), Hybrid::from_epoch_delta(ed)),
    {
        theorem_from_ymd_to_ymd_inverse(ed);
    }

    // Lemma C: A congruent Hybrid with a valid Date is itself valid,
    // provided at least one representation flag is set.
    pub proof fn lemma_hybrid_congruent_is_valid(d: Date, h: Hybrid)
        requires d.is_valid(), hybrid_congruent(d, h), h.ymd() || h.epoch(),
        ensures h.is_valid(),
    {}

    // Lemma D: to_ymd recovers the congruent Date.
    pub proof fn lemma_hybrid_to_ymd(d: Date, h: Hybrid)
        requires d.is_valid(), hybrid_congruent(d, h), h.ymd() || h.epoch(),
        ensures h.to_ymd() == d,
    {
        if h.ymd() {
            // Stored YMD matches d directly.
        } else {
            // epoch flag is set: EpochDelta(h.delta()) == from_ymd(d)
            // h.to_ymd() = EpochDelta(h.delta()).to_ymd() = from_ymd(d).to_ymd() = d
            theorem_to_ymd_from_ymd_inverse(d);
        }
    }

    // Lemma E: to_epoch_delta recovers the congruent EpochDelta.
    pub proof fn lemma_hybrid_to_epoch_delta(d: Date, h: Hybrid)
        requires d.is_valid(), hybrid_congruent(d, h), h.ymd() || h.epoch(),
        ensures h.to_epoch_delta() == EpochDelta::from_ymd(d),
    {
        if h.epoch() {
            // Stored delta matches from_ymd(d) directly.
        } else {
            // ymd flag is set: d == Date(h.year(), h.month(), h.day())
            // h.to_epoch_delta() = from_ymd(Date(h.year(), h.month(), h.day())) = from_ymd(d)
        }
    }

    // Theorem H5: Hybrid congruent pairs preserve comparison.
    pub proof fn theorem_hybrid_congruent_preserves_comparison(
        d1: Date, h1: Hybrid, d2: Date, h2: Hybrid,
    )
        requires
            d1.is_valid(), d2.is_valid(),
            hybrid_congruent(d1, h1), hybrid_congruent(d2, h2),
            h1.ymd() || h1.epoch(), h2.ymd() || h2.epoch(),
        ensures
            (h1.lt(h2) <==> d1.lt(d2)),
            (h1.eq(h2) <==> d1 == d2),
    {
        // Establish that accessors recover the right values.
        lemma_hybrid_to_ymd(d1, h1);
        lemma_hybrid_to_ymd(d2, h2);
        lemma_hybrid_to_epoch_delta(d1, h1);
        lemma_hybrid_to_epoch_delta(d2, h2);

        // Now h1.to_ymd() == d1, h2.to_ymd() == d2,
        //     h1.to_epoch_delta() == from_ymd(d1), h2.to_epoch_delta() == from_ymd(d2).

        // For the epoch-delta branches, we need the EpochDelta congruence theorem.
        let ed1 = EpochDelta::from_ymd(d1);
        let ed2 = EpochDelta::from_ymd(d2);
        theorem_congruent_preserves_comparison(d1, ed1, d2, ed2);

        // All three branches of Hybrid::lt and Hybrid::eq now reduce to
        // either Date or EpochDelta comparison, both of which agree with d1.lt(d2) / d1 == d2.
    }

    // Theorem H6: Hybrid congruence is preserved under period addition.
    pub proof fn theorem_hybrid_congruent_add_period(d: Date, h: Hybrid, p: Period)
        requires d.is_valid(), hybrid_congruent(d, h), h.ymd() || h.epoch(),
        ensures hybrid_congruent(d.add_period(p), h.add_period(p)),
    {
        let n = p.years() * 12 + p.months();
        let days = p.days();

        // Recover accessors.
        lemma_hybrid_to_ymd(d, h);
        lemma_hybrid_to_epoch_delta(d, h);
        // Now: h.to_ymd() == d, h.to_epoch_delta() == from_ymd(d).

        if p.years() == 0 && p.months() == 0 {
            // Case 1: pure day addition.
            // h.add_period(p) = Hybrid(0,0,0, h.to_epoch_delta().delta() + days, false, true)
            // Need: EpochDelta(from_ymd(d).delta() + days) == from_ymd(d.add_period(p))
            // d.add_period(p) = d.add_months(0).add_days(days) = d.add_days(days)
            lemma_from_ymd_add_days(d, days);
        } else if p.days() == 0 {
            // Case 2: year/month only.
            // h.add_period(p) = Hybrid(d'.year(), d'.month(), d'.day(), 0, true, false)
            //   where d' = h.to_ymd().add_months(n) = d.add_months(n)
            // d.add_period(p) = d.add_months(n).add_days(0) = d.add_months(n)
            // Need: d.add_period(p) == d.add_months(n), which holds since add_days(0) is identity.
            // The YMD flag is set and matches, so hybrid_congruent holds.
        } else {
            // Case 3: mixed year/month + days.
            // h.add_period(p) = Hybrid(0,0,0, from_ymd(d.add_months(n)).delta() + days, false, true)
            // d.add_period(p) = d.add_months(n).add_days(days)
            // Need: EpochDelta(from_ymd(d.add_months(n)).delta() + days) == from_ymd(d.add_months(n).add_days(days))
            lemma_date_add_months_preserves_validity(d, n);
            lemma_from_ymd_add_days(d.add_months(n), days);
        }
    }

    // Theorem H1: Hybrid validity is preserved under period addition (for congruent Hybrids).
    pub proof fn theorem_hybrid_congruent_add_period_preserves_validity(d: Date, h: Hybrid, p: Period)
        requires d.is_valid(), hybrid_congruent(d, h), h.ymd() || h.epoch(),
        ensures
            hybrid_congruent(d.add_period(p), h.add_period(p)),
            h.add_period(p).is_valid(),
    {
        theorem_hybrid_congruent_add_period(d, h, p);
        theorem_date_add_period_preserves_validity(d, p);
        lemma_hybrid_congruent_is_valid(d.add_period(p), h.add_period(p));
    }

} // verus!
