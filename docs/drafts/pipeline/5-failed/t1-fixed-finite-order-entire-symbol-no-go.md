# T1 fixed finite-order entire-symbol no-go

- **ID:** T1-FINITE-ORDER-ENTIRE-NOGO
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` · T1 open core
- **Statement:** No fixed entire function of finite order, even with arbitrary normalized scale-dependent rough-tail mollification, can equal the true-prime half-density coefficient on every sufficiently large T1 AFE window.

## Goal

Kill the remaining fixed entire finite-order T1 LAND class in the chain

`T1 smooth AFE detector` → `coefficient-faithful true-prime landing on all eventual moving windows` → `fixed Xi-mass pairing bound` → `RH`.

This strictly extends the proved finite-exponential-type no-go from order at most one to every finite order. A surviving fixed entire symbol must have infinite order; otherwise T1 must use a singular/non-entire, scale-varying, or explicitly prime-power-aware landing.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, frozen claim, exact RH chain
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: Lean theorem, targeted build, axiom and lint audit
- [ ] 3 → 4 publication-ready

## Corpus basis

Required search tool queries:

- `scripts/formal_tools.py research "EntireFiniteOrder add sub identity finite order growth"`
- `scripts/formal_tools.py research "Jensen zeroCount finite order rpow polynomial bound"`
- `scripts/formal_tools.py research "primeLog zeros primeCounting polynomial exponential contradiction"`
- `scripts/formal_tools.py research "tendsto exp div pow atTop polynomial exponential"`

Reused results:

- `PrimeLogExponentialTypeUniqueness.primeCounting_le_sum_divisor_of_primeLog_zeros` converts prime-log zeros into a divisor-count lower bound.
- `ExponentialTypeZeroDensity.exponentialType_zeroCount_le` supplies the Jensen template.
- `SelbergClass.EntireFiniteOrder` packages global `A exp(B |z|^rho)` growth.
- `XiMassLevinsonFiniteTypeAnalyticNoGo` supplies eventual moving-window coverage, rough-tail mollifier collapse, and the exterior prime-square contradiction.

Missing in corpus: finite-order Jensen zero density, prime-log uniqueness for arbitrary finite order, cofinite finite-order prime-log uniqueness, and additive/subtractive algebra for `EntireFiniteOrder`.

## Conjecturing loop

### C1 — Möbius exponent inversion produces the true-prime landing

`[REDISCOVERED]` and rejected. Corpus already proves prime-grade Möbius inversion (`primeBoundary_moebius_inversion`, `primeGradeSource_eq_tsum_moebius_lSeries`). More importantly, the actual T1 detector outside its aperture collapses to `log n / sqrt n` on every rough integer. Dilation Möbius inversion cannot remove rough squarefree composites, so it does not close the detector-to-prime coefficient chain.

### C2 — prime logarithms are a uniqueness set for every finite-order entire function

Frozen conjecture: if an entire `f` obeys one global bound `|f(z)| <= A exp(B |z|^rho)` with finite real `rho`, and vanishes at all prime logarithms outside a finite set, then `f = 0`.

This attacks C1's obstruction at its structural source. Prime logarithms have exponentially many samples in a radius `t`, whereas every nonzero finite-order entire function has only polynomially many zeros in that radius.

### C2-T1 consequence

Prime correctness makes `G(z) = F(z) - z` vanish at every sufficiently large prime logarithm. Finite-order closure under subtraction makes `G` finite order. C2 forces `F = id`. An exterior prime square survives the T1 rough tail but true-prime density vanishes there, contradiction.

## Dependency-closed paper proof target

1. **Finite-order Jensen bound.** If `f(c) != 0` and `|f(z)| <= A exp(B |z|^rho)`, Jensen on radii `r` and `2r` gives
   `N_f(c,r) <= (log A + B (|c|+2r)^rho - log |f(c)|) / log 2`.
2. **Polynomial envelope.** Choose a natural `d >= max(rho,1)`. For `r >= 1`, monotonicity of real powers and `|c|+2r <= (|c|+2)(1+r)` absorb the right side into `K(1+r)^d` for some `K>0`.
3. **Prime-log over-density.** Chebyshev's explicit lower bound at `n=floor(exp t)` and `exp(t)/t^(d+2) -> infinity` produce `t` for which `pi(n) > K(2+|c|+t)^d`.
4. **Uniqueness.** Prime-log zeros below `log n` lie in `closedBall(c,1+|c|+log n)`. The divisor lower bound from step 3 contradicts the Jensen envelope from step 2 unless `f(c)=0`. Since `c` was arbitrary, `f=0`.
5. **Finite exceptions.** Multiply by the finite polynomial whose roots are the omitted prime logarithms. Polynomial evaluation has finite order, products preserve finite order, and density of the complement of its finite root set cancels the polynomial after full uniqueness.
6. **Subtraction stability.** For finite-order `F,G`, outside the unit disk dominate both powers by exponent `max(rho_F,rho_G)` and both exponentials by one common exponential. Thus `F-G` remains finite order. The identity is order one.
7. **T1 capstone.** Reuse the proved moving-window/rough-tail lemmas. Eventual prime correctness invokes cofinite uniqueness on `F-id`; eventual exterior prime-square correctness contradicts `F=id`.

No RH statement or unproved analytic-number-theory premise enters these seven steps.

## Hostile falsification and boundary

- Entire analyticity alone is insufficient: arbitrary interpolation on the discrete log-integer set is possible.
- Infinite-order entire functions are not excluded; their zero counts may match the exponentially dense prime-log set.
- Scale-dependent symbols are not one fixed entire function and remain open.
- Singular/non-entire and explicit nonlinear prime-power subtraction remain open.
- Rough squarefree composites block a naive Möbius/dilation repair before uniqueness is even used.

## Literature audit

Classical Jensen/Hadamard theory proves that zeros of a nonzero finite-order entire function have finite convergence exponent; see Harvard Math 213a notes, Theorem 3.15: https://people.math.harvard.edu/~ctm/home/text/class/harvard/213a/23/html/home/course/course.pdf. Search through 2026-08-30 found no published theorem applying the exponentially dense prime-log zero set to exact Levinson true-prime coefficient landing, moving T1 AFE windows, rough-tail mollifier collapse, and the forced prime-square contradiction.

Novelty claim is scoped to the exact finite-order T1 route-class obstruction and its Lean closure, not to classical Jensen theory.

## No-go closure target

- **Exact killing theorem/mechanism:** finite-order zero density plus cofinite prime-log over-sampling forces the detector symbol to be identity; rough exterior prime squares contradict true-prime support.
- **Strongest positive survivor:** exact classification boundary: any fixed entire T1 symbol satisfying eventual coefficient faithfulness must have infinite order. Remaining viable mechanisms must leave fixed finite-order entire calculus.
- **New insight:** allowing arbitrary finite order does not enlarge the viable fixed analytic T1 class; the actual transition is finite versus infinite order, not exponential type versus higher finite type.
- **Status:** route class retired. Paper proof dependency-closed. Lean capstone compiled, umbrella-wired, and targeted-build audited.

## Resolution

**C2 proved; fixed entire finite-order T1 route class retired.** Lean now proves:

- `exponentialPower_zeroCount_polynomial`: every nonzero entire exponential-power carrier has a polynomial divisor-count envelope;
- `EntireFiniteOrder.eq_zero_of_cofinite_primeLog_zeros`: cofinite prime logarithms are a uniqueness set for every finite-order entire function;
- `EntireFiniteOrder.eq_id_of_cofinite_primeLog_eq`: cofinite agreement with the identity forces global identity;
- `no_fixedEntireFiniteOrder_normalizedMollified_truePrime_eventually_t1AfeWindows`: no fixed finite-order entire symbol survives arbitrary normalized scale-dependent rough-tail mollification on all eventual literal T1 windows.

Exact obstruction: eventual prime correctness forces `F = id`; one rough exterior prime square then contradicts true-prime support. This is a qualitative finite-versus-infinite-order boundary, not a parameter optimization.

Strongest positive survivor: any coefficient-faithful fixed entire T1 symbol must have infinite order. Viable T1 landings must therefore use infinite-order growth, a singular/non-entire symbol, genuine scale variation, explicit nonlinear prime-power subtraction, or non-factorization through one fixed log-symbol.

Lean modules:

- `RHTower/SelbergClass/EntireFiniteOrderAdditiveAlgebra.lean`
- `RHTower/PrimeLogFiniteOrderUniqueness.lean`
- `RHTower/XiMassLevinsonFiniteOrderEntireNoGo.lean`

Targeted `lake build GaloisForLFunctions.RHTower.XiMassLevinsonFiniteOrderEntireNoGo` passed. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Global lint reports unrelated pre-existing unreachable modules; all three new modules are umbrella-reachable and produced no lint error. Frontier map remained read-only.

## Log

- 2026-08-30 — C1 rediscovered and rejected on corpus evidence; C2 frozen after corpus and literature audit.
- 2026-08-30 — C2 dependency-closed on paper; Jensen, Chebyshev, cofinite, subtraction, and T1 capstone chain audited with no open premise.
- 2026-08-30 — C2 formalized; detector-native capstone passed targeted build and axiom audit; fixed entire finite-order T1 class retired.
