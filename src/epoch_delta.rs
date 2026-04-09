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

    proof fn epoch_is_at_delta_zero() ensures EpochDelta::from_ymd(EPOCH).delta() == 0 {}



} // verus!
