use vstd::prelude::*;
use crate::*;

verus! {

    /// The 0-indexed absolute month of the EPOCH (March 2000).
    /// Computed as: 2000 * 12 + (3 - 1) = 24002.
    pub spec const EPOCH_ABS_MONTH: int = 2000int * 12 + 2;

    /// Calendar year for a given alpha (months since EPOCH).
    pub open spec fn year_of_alpha(alpha: int) -> int {
        (EPOCH_ABS_MONTH + alpha) / 12
    }

    /// Calendar month (1-indexed) for a given alpha (months since EPOCH).
    pub open spec fn month_of_alpha(alpha: int) -> int {
        1 + (EPOCH_ABS_MONTH + alpha) % 12
    }

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
        /// Uses year_of_alpha/month_of_alpha to recover (year, month), then sets day = beta + 1.
        pub open spec fn to_ymd(self) -> Date {
            let y = year_of_alpha(self.alpha());
            let m = month_of_alpha(self.alpha());
            Date(y, m, self.beta() + 1)
        }

        /// An AlphaBeta is valid when beta is in range for the calendar month
        /// determined by alpha.
        pub open spec fn is_valid(self) -> bool {
            let y = year_of_alpha(self.alpha());
            let m = month_of_alpha(self.alpha());
            0 <= self.beta() && self.beta() < dim(y, m)
        }

        /// Add n months: increment alpha, clamp beta to the new month's dim.
        pub open spec fn add_months(self, n: int) -> AlphaBeta {
            let y_ = year_of_alpha(self.alpha() + n);
            let m_ = month_of_alpha(self.alpha() + n);
            AlphaBeta(self.alpha() + n, min(self.beta(), dim(y_, m_) - 1))
        }

        /// Convert AlphaBeta to EpochDelta using a closed-form formula.
        /// Since alpha = years_since_epoch * 12 + months_since_march,
        /// we derive ye = alpha / 12 and me = alpha % 12 directly.
        pub open spec fn to_epoch_delta(self) -> EpochDelta {
            let ye = self.alpha() / 12;
            let me = self.alpha() % 12;
            EpochDelta(365 * ye + leap_correction(ye) + (153 * me + 2) / 5 + self.beta())
        }

        /// Convert an EpochDelta to AlphaBeta.
        /// Uses EpochDelta::to_ymd to recover (year, month, day), then computes alpha/beta.
        pub open spec fn from_epoch_delta(ed: EpochDelta) -> AlphaBeta {
            let d = ed.to_ymd();
            let alpha = years_since_epoch(d.year(), d.month()) * 12
                      + months_since_march(d.month());
            let beta = d.day() - 1;
            AlphaBeta(alpha, beta)
        }

        /// Add n days: fast path if result stays within dim(alpha), otherwise
        /// convert to EpochDelta, add days, convert back.
        pub open spec fn add_days(self, n: int) -> AlphaBeta {
            let y = year_of_alpha(self.alpha());
            let m = month_of_alpha(self.alpha());
            if 0 <= self.beta() + n && self.beta() + n < dim(y, m) {
                AlphaBeta(self.alpha(), self.beta() + n)
            } else {
                AlphaBeta::from_epoch_delta(self.to_epoch_delta().add_days(n))
            }
        }

        /// Add a period: add months first, then days.
        pub open spec fn add_period(self, p: Period) -> AlphaBeta {
            self.add_months(p.years() * 12 + p.months()).add_days(p.days())
        }
    }

    // ── Arithmetic helpers ─────────────────────────────────────────────

    // Euclidean division: (q*k + r) / k == q and (q*k + r) % k == r
    // when 0 <= r < k.
    proof fn lemma_euclid_bounded(q: int, r: int, k: int) by (nonlinear_arith)
        requires k > 0, 0 <= r, r < k,
        ensures (q * k + r) / k == q, (q * k + r) % k == r,
    {}

    // The alpha formula simplifies: for valid months (1..12),
    // years_since_epoch(y,m)*12 + months_since_march(m) == (y - 2000)*12 + (m - 3).
    proof fn lemma_alpha_canonical(y: int, m: int)
        requires 1 <= m <= 12,
        ensures years_since_epoch(y, m) * 12 + months_since_march(m)
             == (y - 2000) * 12 + (m - 3),
    {
        if m <= 2 {
            // yse = y - 2001, msm = m + 9
            // (y-2001)*12 + m + 9 = (y-2000)*12 - 12 + m + 9 = (y-2000)*12 + m - 3
        } else {
            // yse = y - 2000, msm = m - 3
            // (y-2000)*12 + m - 3
        }
    }

    // ── EPOCH.add_months characterization ───────────────────────────

    // Unfold EPOCH.add_months(n) into a concrete Date.
    proof fn lemma_epoch_add_months(n: int)
        ensures EPOCH.add_months(n) == Date(2000 + (2 + n) / 12, 1 + (2 + n) % 12, 1),
    {
        // EPOCH = Date(2000, 3, 1), so m-1+n = 2+n.
        // d_ = min(1, dim(y_, m_)) = 1 since dim >= 28 >= 1.
        let y_ = 2000 + (2 + n) / 12;
        let m_ = 1 + (2 + n) % 12;
        lemma_dim_is_bounded(y_, m_);
    }

    // ── Round-trip theorems ─────────────────────────────────────────

    // Given alpha = n, EPOCH.add_months(n) produces a Date whose from_ymd alpha is n.
    proof fn lemma_add_months_recovers_ym(n: int)
        ensures ({
            let Date(y_, m_, _) = EPOCH.add_months(n);
            years_since_epoch(y_, m_) * 12 + months_since_march(m_) == n
        })
    {
        lemma_epoch_add_months(n);
        let y_ = 2000 + (2 + n) / 12;
        let m_ = 1 + (2 + n) % 12;
        // m_ is in 1..12
        lemma_alpha_canonical(y_, m_);
        // canonical form: (y_ - 2000)*12 + (m_ - 3) = (2+n)/12 * 12 + (2+n)%12 - 2
        // By Euclidean identity: (2+n)/12 * 12 + (2+n)%12 == 2 + n
        // So the result is (2+n) - 2 = n.
        lemma_euclid_bounded((2 + n) / 12, (2 + n) % 12, 12);
    }

    // Round-trip: from_ymd(ab.to_ymd()) == ab for all AlphaBeta values.
    pub proof fn theorem_ab_from_ymd_to_ymd_inverse(ab: AlphaBeta)
        ensures AlphaBeta::from_ymd(ab.to_ymd()) == ab,
    {
        let n = ab.alpha();
        let b = ab.beta();
        lemma_epoch_add_months(n);
        lemma_add_months_recovers_ym(n);
        // to_ymd: Date(y_, m_, b+1)
        // from_ymd: alpha = n (by lemma_add_months_recovers_ym), beta = (b+1)-1 = b
    }

    // Given valid (y, m), EPOCH.add_months of the canonical alpha recovers (y, m, 1).
    proof fn lemma_yse_msm_recovers_add_months(y: int, m: int)
        requires 1 <= m <= 12,
        ensures EPOCH.add_months((y - 2000) * 12 + (m - 3))
             == Date(y, m, 1),
    {
        let alpha = (y - 2000) * 12 + (m - 3);
        lemma_epoch_add_months(alpha);
        // EPOCH.add_months(alpha) = Date(2000 + (2+alpha)/12, 1 + (2+alpha)%12, 1)
        // 2 + alpha = (y-2000)*12 + (m-1)
        // Since 1 <= m <= 12, we have 0 <= m-1 <= 11, so m-1 < 12.
        lemma_euclid_bounded(y - 2000, m - 1, 12);
        // (y-2000)*12 + (m-1)) / 12 == y - 2000
        // (y-2000)*12 + (m-1)) % 12 == m - 1
        // So y_ = 2000 + (y-2000) = y, m_ = 1 + (m-1) = m.
    }

    // Round-trip: to_ymd(from_ymd(d)) == d for valid dates.
    pub proof fn theorem_ab_to_ymd_from_ymd_inverse(d: Date)
        requires d.is_valid(),
        ensures AlphaBeta::to_ymd(AlphaBeta::from_ymd(d)) == d,
    {
        let Date(y, m, dd) = d;
        lemma_alpha_canonical(y, m);
        // alpha = (y-2000)*12 + (m-3)
        lemma_yse_msm_recovers_add_months(y, m);
        // EPOCH.add_months(alpha) == Date(y, m, 1)
        // to_ymd: Date(y, m, beta + 1) = Date(y, m, (dd-1) + 1) = Date(y, m, dd) = d
    }

    // ── Congruence ────────────────────────────────────────────────────

    // from_ymd is strictly monotone: d1.lt(d2) implies from_ymd(d1).lt(from_ymd(d2)).
    proof fn lemma_ab_from_ymd_strict_monotone(d1: Date, d2: Date)
        requires d1.is_valid(), d2.is_valid(), d1.lt(d2),
        ensures AlphaBeta::from_ymd(d1).lt(AlphaBeta::from_ymd(d2)),
    {
        let Date(y1, m1, dd1) = d1;
        let Date(y2, m2, dd2) = d2;
        lemma_alpha_canonical(y1, m1);
        lemma_alpha_canonical(y2, m2);
        // alpha1 = (y1-2000)*12 + (m1-3), alpha2 = (y2-2000)*12 + (m2-3)
        // beta1 = dd1 - 1, beta2 = dd2 - 1
        if y1 == y2 && m1 == m2 {
            // Same alpha, beta comparison is dd1-1 < dd2-1
        } else if y1 == y2 {
            // m1 < m2, same y: alpha1 = (y-2000)*12+(m1-3) < (y-2000)*12+(m2-3) = alpha2
        } else {
            // y1 < y2: need alpha1 < alpha2
            // alpha1 <= (y1-2000)*12 + 9   (max when m1=12)
            // alpha2 >= (y2-2000)*12 + (-2) (min when m2=1)
            // alpha2 - alpha1 >= (y2-y1)*12 - 11 >= 12 - 11 = 1
        }
    }

    // ── Congruence ────────────────────────────────────────────────────

    // Congruent pairs preserve comparison and equality.
    pub proof fn theorem_ab_congruent_preserves_comparison(
        d1: Date, ab1: AlphaBeta, d2: Date, ab2: AlphaBeta,
    )
        requires d1.is_valid(), d2.is_valid(),
                 ab_congruent(d1, ab1), ab_congruent(d2, ab2),
        ensures
            (d1.lt(d2) <==> ab1.lt(ab2)),
            (d1 == d2 <==> ab1 == ab2),
    {
        lemma_date_lt_is_total(d1, d2);
        if d1.lt(d2) {
            lemma_ab_from_ymd_strict_monotone(d1, d2);
        }
        if d2.lt(d1) {
            lemma_ab_from_ymd_strict_monotone(d2, d1);
        }
    }

    // ── Congruence definition ─────────────────────────────────────────

    // Congruence between Date and AlphaBeta: asserts they are related by from_ymd.
    pub open spec fn ab_congruent(d: Date, ab: AlphaBeta) -> bool {
        ab == AlphaBeta::from_ymd(d)
    }

    // Congruence at construction: from_ymd(d) is congruent with d.
    pub proof fn theorem_ab_congruent_at_construction(d: Date)
        ensures ab_congruent(d, AlphaBeta::from_ymd(d)),
    {}

    // ── AlphaBeta ↔ EpochDelta bridge lemmas ────────────────────────

    // year_of_alpha and month_of_alpha recover the year and month of a valid date.
    proof fn lemma_ym_of_alpha_from_ymd(d: Date)
        requires d.is_valid(),
        ensures
            year_of_alpha(AlphaBeta::from_ymd(d).alpha()) == d.year(),
            month_of_alpha(AlphaBeta::from_ymd(d).alpha()) == d.month(),
    {
        let Date(y, m, dd) = d;
        lemma_alpha_canonical(y, m);
        // alpha = (y-2000)*12 + (m-3)
        // EPOCH_ABS_MONTH + alpha = 24002 + (y-2000)*12 + (m-3) = y*12 + (m-1)
        lemma_euclid_bounded(y, m - 1, 12);
    }

    // ab.to_epoch_delta() == EpochDelta::from_ymd(d) when ab is congruent to d.
    proof fn lemma_ab_to_epoch_delta_eq_from_ymd(d: Date, ab: AlphaBeta)
        requires d.is_valid(), ab_congruent(d, ab),
        ensures ab.to_epoch_delta() == EpochDelta::from_ymd(d),
    {
        let Date(y, m, dd) = d;
        lemma_alpha_canonical(y, m);
        // alpha = (y-2000)*12 + (m-3) = yse*12 + msm
        // Need: alpha/12 == yse and alpha%12 == msm
        if m <= 2 {
            // yse = y-2001, msm = m+9, alpha = (y-2001)*12 + (m+9)
            lemma_euclid_bounded(y - 2001, m + 9, 12);
        } else {
            // yse = y-2000, msm = m-3, alpha = (y-2000)*12 + (m-3)
            lemma_euclid_bounded(y - 2000, m - 3, 12);
        }
    }

    // from_epoch_delta(ed) == from_ymd(ed.to_ymd()) — definitional.
    proof fn lemma_ab_from_epoch_delta_eq_from_ymd(ed: EpochDelta)
        ensures AlphaBeta::from_epoch_delta(ed) == AlphaBeta::from_ymd(ed.to_ymd()),
    {}

    // add_days preserves congruence.
    proof fn lemma_ab_add_days_congruent(d: Date, ab: AlphaBeta, n: int)
        requires d.is_valid(), ab_congruent(d, ab),
        ensures ab_congruent(d.add_days(n), ab.add_days(n)),
    {
        let Date(y, m, dd) = d;
        lemma_ym_of_alpha_from_ymd(d);
        // year_of_alpha(ab.alpha()) == y, month_of_alpha(ab.alpha()) == m

        if 0 <= ab.beta() + n && ab.beta() + n < dim(y, m) {
            // Fast path: stays in same month.
            // ab.add_days(n) = AlphaBeta(ab.alpha(), ab.beta() + n)
            // d.add_days(n) = Date(y, m, dd + n) since 1 <= dd+n <= dim(y,m)
            // from_ymd(Date(y, m, dd+n)) has same alpha and beta = dd+n-1 = ab.beta()+n
        } else {
            // Overflow path: ab.add_days(n) = from_epoch_delta(ab.to_epoch_delta().add_days(n))
            lemma_ab_to_epoch_delta_eq_from_ymd(d, ab);
            // ab.to_epoch_delta() == EpochDelta::from_ymd(d)
            lemma_ab_from_epoch_delta_eq_from_ymd(ab.to_epoch_delta().add_days(n));
            // from_epoch_delta(...) == from_ymd(EPOCH.add_days(from_ymd(d).delta() + n))
            lemma_from_ymd_add_days(d, n);
            // from_ymd(d).delta() + n == from_ymd(d.add_days(n)).delta()
            lemma_date_add_days_preserves_validity(d, n);
            theorem_epoch_delta_to_ymd_from_ymd_inverse(d.add_days(n));
            // EPOCH.add_days(from_ymd(d.add_days(n)).delta()) == d.add_days(n)
        }
    }

    // ── Period addition congruence ────────────────────────────────────

    // Adding n months to a date shifts its alpha by exactly n.
    proof fn lemma_ab_from_ymd_add_months_alpha(d: Date, n: int)
        requires d.is_valid(),
        ensures AlphaBeta::from_ymd(d.add_months(n)).alpha()
             == AlphaBeta::from_ymd(d).alpha() + n,
    {
        let Date(y, m, dd) = d;
        let k = m - 1 + n;
        let y_ = y + k / 12;
        let m_ = 1 + k % 12;
        assert(d.add_months(n) == Date(y_, m_, min(dd as int, dim(y_, m_))));
        lemma_alpha_canonical(y, m);
        lemma_alpha_canonical(y_, m_);
        // alpha(d) = (y-2000)*12 + (m-3)
        // alpha(d.add_months(n)) = (y_-2000)*12 + (m_-3)
        //   = (y + k/12 - 2000)*12 + (k%12 - 2)
        //   = (y-2000)*12 + k/12*12 + k%12 - 2
        //   = (y-2000)*12 + k - 2          [Euclidean identity]
        //   = (y-2000)*12 + (m-3) + n
        //   = alpha(d) + n
        lemma_euclid_bounded(k / 12, k % 12, 12);
    }

    // Adding n months to a date clamps beta: min(old_beta, dim(new_y, new_m) - 1).
    proof fn lemma_ab_from_ymd_add_months_beta(d: Date, n: int)
        requires d.is_valid(),
        ensures AlphaBeta::from_ymd(d.add_months(n)).beta()
             == min(d.day() - 1, dim(d.add_months(n).year(), d.add_months(n).month()) - 1),
    {
        // d.add_months(n) = Date(y_, m_, min(d, dim(y_, m_)))
        // beta = min(d, dim(y_, m_)) - 1 = min(d-1, dim(y_, m_)-1)
    }

    // Congruence is preserved under period addition.
    pub proof fn theorem_ab_congruent_add_period(d: Date, ab: AlphaBeta, p: Period)
        requires d.is_valid(), ab_congruent(d, ab),
        ensures ab_congruent(d.add_period(p), ab.add_period(p)),
    {
        let n = p.years() * 12 + p.months();
        let days = p.days();

        // Step 1: d == ab.to_ymd()
        theorem_ab_to_ymd_from_ymd_inverse(d);

        // Step 2: d.add_months(n) is valid
        lemma_date_add_months_preserves_validity(d, n);

        // Step 3: from_ymd(d.add_months(n)) matches ab.add_months(n)
        lemma_ab_from_ymd_add_months_alpha(d, n);
        lemma_ab_from_ymd_add_months_beta(d, n);
        // Need to connect: year_of_alpha/month_of_alpha(ab.alpha() + n) gives same (y_, m_) as d.add_months(n)
        let Date(y, m, dd) = d;
        lemma_alpha_canonical(y, m);
        let alpha = (y - 2000) * 12 + (m - 3);
        let k = m - 1 + n;
        let y_ = y + k / 12;
        let m_ = 1 + k % 12;
        lemma_euclid_bounded(k / 12, k % 12, 12);
        lemma_euclid_bounded(y + k / 12 - 2000, k % 12, 12);
        assert((2 + alpha + n) == (y + k / 12 - 2000) * 12 + k % 12);
        // year_of_alpha(alpha + n) == y_, month_of_alpha(alpha + n) == m_
        // EPOCH_ABS_MONTH + alpha + n = 24002 + (y-2000)*12 + (m-3) + n = y*12 + (m-1) + n = y*12 + k
        lemma_euclid_bounded(y + k / 12, k % 12, 12);
        // So from_ymd(d.add_months(n)) == ab.add_months(n)

        // Step 4: add_days preserves congruence
        lemma_ab_add_days_congruent(d.add_months(n), ab.add_months(n), days);
    }

} // verus!
