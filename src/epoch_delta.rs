use vstd::prelude::*;
use crate::*;

verus! {

    /// A date represented as the number of days since the EPOCH (2000-03-01).
    pub struct EpochDelta(pub int);

    impl EpochDelta {
        pub open spec fn delta(&self) -> int {
            self.0
        }

        pub open spec fn lt(self, other: Self) -> bool {
            self.delta() < other.delta()
        }

        pub open spec fn leq(self, other: Self) -> bool {
            self.delta() <= other.delta()
        }

        pub open spec fn is_valid(self) -> bool {
            true
        }

        pub open spec fn to_ymd(self) -> Date {
            EPOCH.add_days(self.delta())
        }

        pub open spec fn from_ymd(date: Date) -> EpochDelta
            recommends EPOCH == Date(2000, 3, 1)
        {
            // Years elapsed since Mar 1, 2000 => (year - 2000) - (month <= 2 as nat)
            let years_elapsed  = (if date.month() <= 2 { date.year() - 1 } else { date.year() }) - 2000;

            // Months elapsed since March
            let months_elapsed =  if date.month() <= 2 { date.month() + 9 } else { date.month() - 3 };

            // Days elapsed since 1st
            let days_elapsed_in_month = date.day() - 1;

            // Given Y years since 2000, how many days is that?
            let leap_days_elapsed = years_elapsed/4 - years_elapsed/100 + years_elapsed/400;
            let days_elapsed_by_years_elapsed = 365*years_elapsed + leap_days_elapsed;

            // Given X months since March, how many days is that?
            // Note: This is some wacky logic, but it works
            // Since March, the dim array is [31, 30, 31, 30, 31, 31, 30, 31, 30, 31, 31, 28_or_29]
            // Cumulatively for months elapsed in the range 0..11 inclusive, this is
            //   [0, 31, 61, 92, 122, 153, 184, 214, 245, 275, 306, 337]
            // It turns out that this is basically (153 * X + 2) / 5, assuming floor division.
            let days_elapsed_by_months_elapsed = (153*months_elapsed + 2)/5;

            EpochDelta(days_elapsed_by_years_elapsed +
                days_elapsed_by_months_elapsed + days_elapsed_in_month)
        }
        
        pub open spec fn add_days(self, n: int) -> EpochDelta {
            EpochDelta(self.delta() + n)
        }

        pub open spec fn add_months(self, n: int) -> EpochDelta {
            EpochDelta::from_ymd(self.to_ymd().add_months(n))
        }

        pub open spec fn add_period(self, period: Period) -> EpochDelta {
            self.add_months(period.years() * 12 + period.months()).add_days(period.days())
        }
    }

    pub proof fn lemma_epoch_is_at_delta_zero() ensures
        EpochDelta::from_ymd(EPOCH).delta() == 0 {}

    pub proof fn lemma_delta_zero_is_epoch() ensures
        EpochDelta::to_ymd(EpochDelta(0)) == EPOCH {}

    // The from_ymd delta for any date = first-of-month value + (day - 1)
    proof fn lemma_from_ymd_split(y: int, m: int, d: int)
        ensures EpochDelta::from_ymd(Date(y, m, d)).delta()
        == EpochDelta::from_ymd(Date(y, m, 1)).delta() + (d - 1)
    {}

    // Leap year correction: lc(k) = k/4 - k/100 + k/400
    // lc(k) - lc(k-1) == 1 iff leap(year 2000+k), else 0.
    // This connects the from_ymd formula to dim(y, 2) for the Feb->Mar boundary.
    // Division step: floor(k/n) - floor((k-1)/n) == 1 iff n divides k, else 0
    proof fn lemma_div_step(k: int, n: int) by (nonlinear_arith)
        requires n >= 1,
        ensures k/n - (k-1)/n == if k%n == 0 { 1int } else { 0 }
    {}

    proof fn lemma_leap_correction(k: int)
        ensures (k/4 - k/100 + k/400) - ((k-1)/4 - (k-1)/100 + (k-1)/400)
             == if leap(k + 2000) { 1int } else { 0 }
    {
        lemma_div_step(k, 4);
        lemma_div_step(k, 100);
        lemma_div_step(k, 400);
        // leap(k+2000) iff 4|k && (100∤k || 400|k), since 2000 ≡ 0 mod 400
        // The three lemma_div_step results give:
        //   contribution = [4|k] - [100|k] + [400|k]
        // which equals 1 iff leap(k+2000), 0 otherwise.
    }

    // Going from the first day of (y,m) to the first day of the next month
    // advances from_ymd by exactly dim(y,m).
    proof fn lemma_from_ymd_month_step(y: int, m: int)
        requires 1 <= m <= 12,
        ensures EpochDelta::from_ymd(Date(y, m, 1).add_months(1)).delta()
              == EpochDelta::from_ymd(Date(y, m, 1)).delta() + dim(y, m)
    {
        // Unfold add_months(1): y_ = y + m/12, m_ = 1 + m%12, d_ = min(1, dim(...)) = 1
        let ny = y + m/12;
        let nm = 1 + m%12;
        assert(Date(y, m, 1).add_months(1) == Date(ny, nm, 1));
        // Case split: Feb->Mar crosses a from_ymd year boundary; all others are arithmetic
        if m == 2 {
            let k = y - 2000;
            lemma_leap_correction(k);
        } else {
            // For all other months, years_elapsed is the same for (y,m) and (ny,nm)
            // so the difference is purely from the (153*m_+2)/5 term = dim(y,m).
        }
    }

    // General lemma: adding n days (positive or negative) shifts from_ymd delta by n.
    // Induction mirrors add_days' own recursion (same decreases clause).
    proof fn lemma_from_ymd_add_days(date: Date, n: int)
        requires date.is_valid(),
        ensures EpochDelta::from_ymd(date.add_days(n)).delta()
              == EpochDelta::from_ymd(date).delta() + n,
        decreases (n < 0) as nat, abs(n)
    {
        let Date(y, m, d) = date;
        if 1 <= d + n <= dim(y, m) {
            // ADD-DAYS: result = Date(y, m, d+n)
            lemma_from_ymd_split(y, m, d);
            lemma_from_ymd_split(y, m, d + n);
        } else if d + n > dim(y, m) {
            // ADD-DAYS-OVER: recurse on first-of-next-month with smaller n
            let n_ = n - (dim(y, m) - d) - 1;
            let next = Date(y, m, 1).add_months(1);
            assert(date.add_days(n) == next.add_days(n_));
            date_add_months_preserves_validity(Date(y, m, 1), 1);
            lemma_from_ymd_add_days(next, n_);
            lemma_from_ymd_split(y, m, d);
            lemma_from_ymd_month_step(y, m);
        } else if d > 1 {
            // ADD-DAYS-UNDER1: shift to first-of-month, recurse with smaller |n|
            assert(date.add_days(n) == Date(y, m, 1).add_days(d - 1 + n));
            lemma_from_ymd_add_days(Date(y, m, 1), d - 1 + n);
            lemma_from_ymd_split(y, m, d);
            lemma_from_ymd_split(y, m, 1);
        } else {
            // ADD-DAYS-UNDER2: d == 1, step back to previous month
            let Date(y_, m_, _) = date.add_months(-1);
            let n_ = n + dim(y_, m_);
            assert(date.add_days(n) == Date(y_, m_, 1).add_days(n_));
            date_add_months_preserves_validity(date, -1);
            lemma_from_ymd_add_days(Date(y_, m_, 1), n_);
            // from_ymd_first(y, m) == from_ymd_first(y_, m_) + dim(y_, m_)
            // follows from lemma_from_ymd_month_step(y_, m_) since Date(y_, m_, 1).add_months(1) == date
            assert(Date(y_, m_, 1).add_months(1) == Date(y, m, 1));
            lemma_from_ymd_month_step(y_, m_);
            lemma_from_ymd_split(y, m, 1);
            lemma_from_ymd_split(y_, m_, 1);
        }
    }

    // The inverse: from_ymd(ed.to_ymd()) == ed for all ed
    pub proof fn theorem_from_ymd_to_ymd_inverse(ed: EpochDelta)
        ensures EpochDelta::from_ymd(ed.to_ymd()) == ed
    {
        lemma_epoch_is_at_delta_zero();
        lemma_from_ymd_add_days(EPOCH, ed.delta());
    }



} // verus!
