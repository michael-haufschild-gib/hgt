# Global pole-grid completion: failure and uniform two-window survivor

- **ID:** weil-work-01-pbap-global-pole-grid
- **Stage:** 1-in-progress (no-go closure pending survivor formalization)
- **Type:** FALSIFIED (existing Lean semiprime-floor obstruction)
- **Source:** docs/reports/weil-work/results/01-pbap/JOINT-UNIFORM-PROFILE-CERTIFICATE.md
- **Statement:** lambda(n)=1+1/n, n>=2, is not a globally positive full completion.

## Goal

Retain the strongest positive restriction exposed by the failed global
quadrature completion, while continuing the original full PBAP goal.
This is not a PBAP counterexample: the negative compact test need not be
integer-null.

## Gates

- [x] Exact global candidate and source-uniform local survivor stated.
- [x] Paper failure and dependency-closed positive-survivor proof recorded.
- [ ] Formalize MC6, then its strongest MC8 many-window survivor, without source derivative premises.
- [ ] Final foreground leaf/axiom/lint audits; only then close this no-go card.

## No-go closure

- **Killing mechanism:** the existing
  `not_weilPositiveFull_of_nonneg_semiprime_floor` excludes this nonnegative
  coefficient system with p=2,c=1. No external theorem is needed. Independently,
  the actual compact-source multiplier is
  gamma(t)+4-2 Re zeta(1/2+it)-2 Re zeta(3/2+it). Unconditional positive-real
  zeta peaks beat logarithmic Gamma growth. Smooth compact Fourier
  localization produces an actual negative test.
- **Strongest positive survivor:** for a fixed smooth plateau cutoff with
  integral A and every b>0 satisfying A*b*log2<1, all sufficiently large L
  and ALL complex smooth f,g supported in [0,b L log log L exp(-L/2)] obey
  Q_lambda(f+translate_L g)>=(L/4)*(mass f+mass g). Threshold independent
  of source shape, phase, derivative norms and relative masses. The same
  fixed lambda then cancels in arbitrary nonnegative aggregate-null
  mixtures of these atoms, even at different separations.
  MC7 in the same paper extends this to arbitrarily many narrow windows
  with starts separated by 6 log D and diameter D, giving D/5 times mass.
  The paper proof bounds every shorter interaction after retaining the
  unique extreme pair. This is a bridge from MC6; both capstones remain
  Lean OPEN, and MC6 must be formalized first.
  MC8 sharpens the spacing to 4 log log log D: summing the actual geometric
  rows replaces the factor counting windows and bounds the remaining cross
  cost by O(D/log log D) times mass. This is now the strongest paper survivor;
  it retains the D/5 margin and is still Lean OPEN.
- **New insight:** the global symbol is indefinite, yet spatially narrow
  separated sources cannot arbitrarily concentrate at its bad frequencies.
  Move quadrature derivatives onto one fixed cutoff; use exact source mass
  and an integrated uncertainty bound instead of assumed profile regularity.
- **Status:** global obstruction REDISCOVERED from the corpus multiples-of-
  a-prime law. Exact scratch instantiation and axiom audit PASS60.53s,
  exit0, only propext/Classical.choice/Quot.sound. The alternative
  WP02 grid-defect/zeta explanation remains paper-only. MC6 survivor
  dependency-closed on paper, Lean OPEN. Scientific novelty unestablished.
  Eleven new WP01 supporting leaves, including the literal cutoff's uniform
  bounds, actual interval geometry, growing-order phase budgets and
  complex middle-frequency error and low/high estimates, have passed 105 public audits. Gamma gluing and MC6/MC8
  capstones remain open.
  Full PBAP remains OPEN.

## Log

- 2026-10-08 — source-independent cutoff audit exposed fixed lambdaStar.
  Rejected its global extension using the already-formalized semiprime-floor
  law, independently explained by the principal grid defect and current
  primary-source large-value theorem. Preserve
  this card in progress until the nontrivial positive survivor is formalized.
- 2026-10-08 — growing-order scratch PASS24.65s. It pays all three window
  inequalities on the actual interval, for every frequency from
  exp(L)/sqrt(L) through exp((c log log L+1)L), and proves the explicit
  prefix saving exp(-(log L)^(1-c log2)/16). Production
  `WeilWorkPBAPJointGrowingOrder` is wired; targeted80.70s/final10.48s/
  nine standard-only axiom checks30.31s passed. Next: pay the fixed cutoff's Abel variation, then join low,
  middle and high frequencies before the MC6 energy capstone. No supplied
  numerical budget survives in the new schedule theorem.
- 2026-10-08 — middle-cutoff scratch PASS66.03s, empty log. The actual
  complex grid discrepancy now has a bound for both frequency signs,
  including its continuous Fourier term. The exact multiplier
  `2 cosh(L/2)` leaves a nonnegative o(L) loss when c log2<1.
  `WeilWorkPBAPJointMiddleCutoff` is wired; targeted112.29s/final93.66s/
  eleven standard-only axiom checks41.38s passed. Next scratch: full logarithmic quadrature, low-frequency o(L)
  loss and a high-frequency bound retaining the exact plateau integral.
- 2026-10-08 — full grid-frequency scratch PASS55.66s, empty log;
  `WeilWorkPBAPJointGridFrequency` wired, targeted build PASS196.55s,
  final156.47s/twelve standard-only axiom checks156.63s passed.
  All three frequency ranges now have audited actual scalar estimates. High heights retain exact Apsi
  and leave 3L/4 against log|t|. A global finite error bound pays subsequent
  integrability. Next scratch joins the Gamma deficit and integrates
  against each arbitrary source density, targeting a uniform L/3 mass
  reserve before the remaining cross-Gamma and diagonal-pole remainders.
- 2026-10-08 — `JointSymbolFloor` pays that L/3 reserve, also for two
  unrelated sources with literal b=1/(8 log2). Targeted48.98s/final84.00s/
  nine standard-only axiom checks11.03s pass. Twelve leaves/114 public
  audits. Lint has thirteen unrelated umbrella findings, none WP01.
  Next: literal two-source correlation, mass, Gamma, pole and atom identities.
  MC6/MC8/full PBAP remain OPEN; no-go card stays in progress.
