# Penrose R15 — reset occupation vs first passage

NODE: stochastic resetting changes the occupation measure, not just first-passage statistics.

Transfer:
- Trace: `X_sigma(t)=log(1+|zeta'(sigma+it)/zeta(sigma+it)|)`.
- Reset event: upward crossing of a robust quantile threshold in `X_sigma`.
- First-passage data: event count and inter-reset intervals.
- Occupation data: normalized reset-age/value profile between reset events.
- Controls: finite Euler log-derivative over primes up to 47 and random-phase finite Euler.

Key Step 9 result:
- True zeta, `[100,170]`, q=.9, sigma `.3/.5/.7`:
  - events: `35 / 35 / 35`
  - mean interval: `14.94 / 14.94 / 14.97`
  - occupation slope: `-1.08 / -3.66 / -1.24`
- True zeta, `[500,570]`, q=.8, sigma `.3/.5/.7`:
  - events: `49 / 51 / 48`
  - mean interval: `10.77 / 10.34 / 10.85`
  - occupation slope: `-1.40 / -4.22 / -1.54`

Key Step 11 stripped-clock result:
- Force all lanes to use the exact `sigma=.5` reset clock.
- True center-minus-neighbor slope excess:
  - `[100,170]` q=.9: `-2.54`
  - `[500,570]` q=.9: `-2.30`
- Finite Euler center-minus-neighbor slope excess:
  - `[100,170]` q=.9: `-0.39`
  - `[500,570]` q=.9: `+0.02`
- Random-phase center-minus-neighbor slope excess:
  - `[100,170]` q=.9: `+0.12`
  - `[500,570]` q=.9: `+0.01`

Right-strip sanity check:
- `sigma=1.2`, `[500,570]`, q=.8:
  - true: `10` events, mean interval `50.78`, slope `-1.528`
  - finite: `10` events, mean interval `50.89`, slope `-1.539`

Verdict:
- Counted as non-promptable experimental finding, posted to `#research` id `757`.
- Interpretation: first-passage reset clocks are mostly divisor-time shadows; the occupation profile between resets carries the critical-lane log-derivative pole geometry.
