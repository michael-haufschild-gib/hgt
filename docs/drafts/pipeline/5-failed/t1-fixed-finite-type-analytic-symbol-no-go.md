# T1 fixed finite-type analytic-symbol no-go

**Route:** T1 (Levinson--Conrey / smooth AFE coefficient landing)  
**Stage:** 5 — failed/retired route class  
**Date:** 2026-08-30

## RH proof chain under attack

`smooth AFE entire finite-type differential symbol` → `coefficient-faithful fixed critical Weil LAND on every sufficiently rough source index` → `bounded Xi-mass pairing` → `RH`.

This card attacks the first implication at its strongest scale-free fixed-symbol form. It does not claim to kill scale-dependent, singular, or explicit prime-power-subtracted symbols.

## Corpus basis

- `PrimeSourceCancellationBudget.eq_zero_of_exponentialType_of_cofinite_primeLog_zeros`: prime logarithms outside any finite set are a uniqueness set for entire functions of finite exponential type.
- `XiMassLevinsonRoughTailHorizon.prime_isApertureRough` and `prime_sq_isApertureRough`: every exterior prime and its square survive the rough tail.
- `XiMassLevinsonFiniteOrderPolynomialNoGo`: fixed finite polynomial log-jets already fail coefficient-faithful true-prime landing.

Corpus search used: `scripts/formal_tools.py research "cofinite primeLog zeros exponentialType truePrimeLogHalfDensityCoeff IsApertureRough"`.

## Conjecturing loop

### C1 — finite polynomial log-symbol

Killed previously: enough exterior prime samples force the polynomial to be `X`; an exterior prime square contradicts true-prime support.

### C2 — arbitrary entire symbol

Failed. Entire interpolation on the discrete set of prime and prime-power logarithms leaves enough freedom; analyticity alone supplies no uniqueness.

### C3 — fixed entire symbol with generic growth

Failed. Generic entire growth still allows zero sets with exponent of convergence compatible with the compressed prime-log set.

### C4 — fixed entire finite-exponential-type symbol

Conjecture: no entire `F : ℂ → ℂ` satisfying a global finite-exponential-type bound can obey

`F(log n) / sqrt n = truePrimeLogHalfDensityCoeff n`

for every sufficiently rough positive integer `n`.

Proof idea: exterior-prime correctness makes `G(z) = F(z) - z` vanish on all but finitely many prime logarithms. Finite exponential type is stable under subtracting `z`; corpus cofinite prime-log uniqueness forces `G = 0`. Hence `F(z) = z`. Any exterior prime square then receives a nonzero logarithmic coefficient, contradicting true-prime support.

## Hostile audit targets

- Prove finite-exponential-type stability under subtraction of identity with explicit constants.
- Use only exterior primes through a finite-exception uniqueness theorem.
- Cancel the `1 / sqrt n` factor without hidden positivity assumptions.
- Produce the contradicting exterior prime square unconditionally.
- Formal theorem must be closed and axiom-clean; no numerical computation.

## Literature audit

- Conrey--Farmer--Kwan--Lin--Turnage-Butterbaugh, *Short mollifiers of the Riemann zeta-function* (2025), studies optimized finite linear combinations of zeta derivatives, not exact true-prime projection or this analytic-symbol obstruction: https://arxiv.org/abs/2508.11108
- Search of current entire-function sampling literature found general exponential-type zero-set criteria, but no theorem applying the cofinite prime-log uniqueness / prime-square support contradiction to Levinson coefficient landing: https://arxiv.org/abs/2105.01712

Novelty claim is scoped to this T1 route-class theorem, not to classical uniqueness theory itself.

## Terminal criterion

Route class is retired only after Lean proves the unconditional universal nonexistence theorem. Positive survivor: any viable T1 analytic landing must have type diverging with scale, be non-entire/singular, incorporate explicit nonlinear prime-power subtraction, or not factor through one fixed log-symbol.

## Resolution

**C4 proved; route class retired.** `XiMassLevinsonFiniteTypeAnalyticNoGo.lean` proves:

- affine prime-log rigidity for arbitrary cofinite prime exceptions;
- cofinal coverage by the literal moving windows `N^49 < n ≤ N^100` beyond any prescribed scale;
- exact rough-tail collapse of arbitrary normalized scale-dependent `N^49`-supported mollifiers;
- unconditional detector-native nonexistence theorem `no_fixedEntireFiniteExponentialType_normalizedMollified_truePrime_eventually_t1AfeWindows`.

No fixed entire finite-exponential-type logarithmic symbol survives, even after arbitrary scale-dependent normalized mollification. Positive survivor is sharp: scale-diverging exponential type, a singular/non-entire symbol, explicit nonlinear prime-power subtraction, or non-factorization through a single fixed log-symbol.

**Paper proof:** dependency-closed.  
**Lean:** compiled, umbrella-wired, targeted `lake build` passed; axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Global lint remains red solely on unrelated pre-existing unwired modules; this module is reachable and produced no lint violation.  
**Frontier consequence:** fixed finite-type analytic-germ LAND is terminal; T1 open core narrows to genuinely scale-varying/singular or prime-power-aware landing.
