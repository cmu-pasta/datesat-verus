use vstd::prelude::*;
use vstd::math::*;

mod period;
use period::*;

mod simple_date;
use simple_date::*;

mod monotonicity;
use monotonicity::*;

mod epoch_delta;
use epoch_delta::*;

mod hybrid;
use hybrid::*;

mod alpha_beta;
use alpha_beta::*;

verus! {

    /// Trait for date encodings that support construction from YMD,
    /// comparison, and period addition.
    pub trait DateEncoding: Sized {
        spec fn from_ymd(y: int, m: int, d: int) -> Self;
        spec fn lt(self, other: Self) -> bool;
        spec fn eq(self, other: Self) -> bool;
        spec fn add_period(self, period: Period) -> Self;
    }

    /// The epoch: March 1, 2000. Chosen so that the leap day (Feb 29) falls
    /// at the end of the epoch-year, simplifying the from_simple_date formula.
    pub spec const EPOCH : SimpleDate = SimpleDate(2000, 3, 1);

    fn main() {
        // Theorem 1: Well-formedness
        assert forall|d: SimpleDate, p: Period| #![auto]
            d.is_valid() implies d.add_period(p).is_valid() by { theorem_date_add_period_preserves_validity(d, p); }

        // Theorem 2: Monotonicity of SimpleDate-Period Addition
        assert forall|d1: SimpleDate, d2: SimpleDate, p: Period| #![auto]
            d1.is_valid() && d2.is_valid() && d1.leq(d2) implies
                d1.add_period(p).leq(d2.add_period(p)) by { theorem_date_add_period_is_monotonic(d1, d2, p); }

        // Theorem 3: EpochDelta congruence at construction
        assert forall|y: int, m: int, d: int| #![auto]
            congruent(SimpleDate(y, m, d), EpochDelta::from_ymd(y, m, d))
            by { theorem_epoch_delta_from_ymd_congruent(y, m, d); }

        // Theorem 4: EpochDelta congruent pairs preserve comparison
        assert forall|d1: SimpleDate, ed1: EpochDelta, d2: SimpleDate, ed2: EpochDelta| #![auto]
            d1.is_valid() && d2.is_valid() && congruent(d1, ed1) && congruent(d2, ed2) implies
                (d1.lt(d2) <==> ed1.lt(ed2)) && (d1.eq(d2) <==> ed1.eq(ed2))
            by { theorem_epoch_delta_congruent_preserves_comparison(d1, ed1, d2, ed2); }

        // Theorem 5: EpochDelta congruence preserved under period addition
        assert forall|d: SimpleDate, ed: EpochDelta, p: Period| #![auto]
            d.is_valid() && congruent(d, ed) implies
                congruent(d.add_period(p), ed.add_period(p))
            by { theorem_epoch_delta_add_period_preserves_congruence(d, ed, p); }

        // Theorem 6: Hybrid congruence at construction (from_ymd)
        assert forall|y: int, m: int, d: int| #![auto]
            SimpleDate(y, m, d).is_valid() implies hybrid_congruent(SimpleDate(y, m, d), Hybrid::from_ymd(y, m, d))
            by { theorem_hybrid_from_ymd_congruent(y, m, d); }

        // Theorem 7: Hybrid congruence at construction (from_epoch_delta)
        assert forall|ed: EpochDelta| #![auto]
            hybrid_congruent(ed.to_ymd(), Hybrid::from_epoch_delta(ed))
            by { theorem_hybrid_from_epoch_delta_congruent(ed); }

        // Theorem 8: Hybrid congruent pairs preserve comparison
        assert forall|d1: SimpleDate, h1: Hybrid, d2: SimpleDate, h2: Hybrid| #![auto]
            d1.is_valid() && d2.is_valid()
            && hybrid_congruent(d1, h1) && hybrid_congruent(d2, h2) implies
                (h1.lt(h2) <==> d1.lt(d2)) && (h1.eq(h2) <==> d1.eq(d2))
            by { theorem_hybrid_congruent_preserves_comparison(d1, h1, d2, h2); }

        // Theorem 9: Hybrid congruence preserved under period addition
        assert forall|d: SimpleDate, h: Hybrid, p: Period| #![auto]
            d.is_valid() && hybrid_congruent(d, h) implies
                hybrid_congruent(d.add_period(p), h.add_period(p))
            by { theorem_hybrid_add_period_preserves_congruence(d, h, p); }

        // Theorem 10: AlphaBeta congruence at construction
        assert forall|y: int, m: int, d: int| #![auto]
            ab_congruent(SimpleDate(y, m, d), AlphaBeta::from_ymd(y, m, d))
            by { theorem_ab_from_ymd_congruent(y, m, d); }

        // Theorem 11: AlphaBeta congruent pairs preserve comparison
        assert forall|d1: SimpleDate, ab1: AlphaBeta, d2: SimpleDate, ab2: AlphaBeta| #![auto]
            d1.is_valid() && d2.is_valid() && ab_congruent(d1, ab1) && ab_congruent(d2, ab2) implies
                (d1.lt(d2) <==> ab1.lt(ab2)) && (d1.eq(d2) <==> ab1.eq(ab2))
            by { theorem_ab_congruent_preserves_comparison(d1, ab1, d2, ab2); }

        // Theorem 12: AlphaBeta congruence preserved under period addition
        assert forall|d: SimpleDate, ab: AlphaBeta, p: Period| #![auto]
            d.is_valid() && ab_congruent(d, ab) implies
                ab_congruent(d.add_period(p), ab.add_period(p))
            by { theorem_ab_congruent_add_period(d, ab, p); }

    }

} // verus!
