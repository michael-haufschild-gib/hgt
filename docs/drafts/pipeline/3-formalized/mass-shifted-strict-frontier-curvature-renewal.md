# Mass-shifted strict-frontier curvature renewal

- **ID:** `mass-shifted-strict-frontier-curvature-renewal`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / arithmetic source law
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 exact open core
- **Statement:** Every occupied strict terminal-frontier rung is a positive shifted-Xi flat face
  carrying an exact adaptive negative-energy price; if RH is false, such priced rungs occur
  arbitrarily far to the right.

## Goal

Replace arbitrary-flat-face certificate by source law on actual canonical frontier schedule. This
closes producer existence, admission, parity, and cofinal occurrence without a fixed orientation
map or linear reporter. Remaining burden must concern quantitative efficiency of prices, not
existence or compatibility of renewal events.

## Gates

- [x] 0 → 1 in-progress: source-pure statement; attack uses existing strict-face and
  parity-complete curvature theorems
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: Lean capstone, targeted build green, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper and external specialist novelty audit

## Conjecture → proof/fail loop

1. **C1 — hard-edge compactness gives uniform positive renewal quotient. `[FALSIFIED]`**
   Completed-source packet compactness preserves a nonzero Paley–Wiener limit, but does not keep
   first transverse coupling away from zero. Contact can migrate to aperture boundary while
   normalized negative energy tends to zero. Strong positive survivor: compactness controls
   carrier existence, not renewal efficiency.
2. **C2 — strict canonical rung is only qualitative and need not carry arithmetic price.
   `[FALSIFIED]`** Existing strict-step theorem identifies next frontier as singular PSD face with
   positive principal head. Its null vector has nonzero terminal coordinate. Parity-complete
   first-contact theorem therefore applies canonically and gives exact price on actual schedule.
3. **C3 — false RH may leave priced strict rungs in bounded frontier region. `[FALSIFIED]`** At
   every nonnegative mass false RH supplies some non-PSD finite block. Enlarging two indices gives
   occupied failure set whose frontier lies beyond that mass. Thus frontiers are unbounded. Any
   real sequence with two values in strict order has a strict adjacent step between them; nested
   failure sets ensure every such step above an occupied rung is admissible.
4. **C4 — cofinal priced rungs alone imply RH. `[FALSIFIED]`** Cofinality gives infinitely many
   positive prices but no lower bound on their sum. Frontier can diverge through positive-chamber
   slack between priced Lipschitz persistence lengths. Strong survivor is exact
   **curvature-renewal/free-flight decomposition**: under false RH, producer is cofinal, so only
   unpriced slack can hide parabolic recession.

## Dependency-closed paper proof `[PROVED HERE]`

Write `tau_n` for terminal frontier of failure set

```text
F_n = { y >= 0 | H_(n+2)(y) is not positive definite }.
```

### 1. Exact price on every strict rung

Assume `F_n` is nonempty and `tau_n < tau_(n+1)`. Put `y=tau_(n+1)`. Corpus strict-frontier
classification gives

```text
H_(n+2)(y) > 0,
H_(n+3)(y) >= 0 but H_(n+3)(y) is not > 0.
```

An element of `F_n` lies in `[0,tau_n]`, hence `y>0`. Singular PSD gives a nonzero null vector
`c` of `H_(n+3)(y)`. Positive definiteness of principal block `H_(n+2)(y)` forces terminal
coordinate `c_(n+2)` nonzero. Apply parity-complete first-contact curvature theorem to base index
`n+2`. It yields `k>=n+2` and `x` in block size `k+2` such that

```text
0 < -Q_y(x),
y + (-Q_y(x))/W(x) <= tau_k.
```

Thus every actual strict rung—not a chosen auxiliary crossing—has exact source-selected arithmetic
price before any reflection aggregation.

### 2. False RH forces unbounded occupied frontiers

Assume not RH and fix `A` in `R`. Set `y=|A|+1`, so `0<y` and `A<y`. All-block shifted-Hankel
criterion says some `H_N(y)` is not PSD. If `H_(N+2)(y)` were positive definite, its principal
`N` block would be positive definite and therefore PSD, contradiction. Hence `y in F_N`, so

```text
A < y <= tau_N.
```

Moreover `F_N` is occupied. Therefore occupied terminal frontiers are unbounded above under false
RH.

### 3. Strict rungs are cofinal

Choose occupied `F_a` with `A<tau_a`, then occupied `F_b` with `tau_a<tau_b`. Failure sets are
nested by degree. If `b<=a`, occupancy of `F_b` would give `tau_b<=tau_a`, contradicting choice;
therefore `a<b`. Among finite list

```text
tau_a, tau_(a+1), ..., tau_b
```

some adjacent inequality is strict: otherwise reverse weak inequalities at every step would give
`tau_b<=tau_a`. Let it be `tau_j<tau_(j+1)`. Failure-set nesting `F_a subseteq F_j` makes `F_j`
occupied. Same nesting and supremum monotonicity give `tau_a<=tau_j`, hence `A<tau_j`. Step 1
then attaches exact adaptive price to this arbitrarily far-right strict rung.

Case split on RH produces unconditional closed dichotomy:

```text
RH or, for every A, there is an occupied strict rung tau_n>A
carrying a source-adaptive certificate
  0 < -Q_(tau_(n+1))(x),
  tau_(n+1) + (-Q_(tau_(n+1))(x))/W(x) <= tau_k.
```

No compactness, numerical estimate, fixed reporter, choice of orientation, realization tower, or
effectivity hypothesis enters.

## Hostile audit and literature comparison

Generic finite-sequence adjacent-step extraction and principal-block nesting are `[BRIDGE]`.
Connes--van Suijlekom ([arXiv:2511.23257](https://arxiv.org/abs/2511.23257)) derive real-zero
localization from a simple isolated convolution ground state and finite singular Toeplitz-type
truncations, not a shifted-Xi terminal-frontier price. Suzuki
([arXiv:2606.09096](https://arxiv.org/abs/2606.09096)) rewrites Weil form through a screw function
and proposes spectral limits, but supplies no source-priced Hankel renewal. Kulikov
([arXiv:2510.01374](https://arxiv.org/abs/2510.01374)) proves bounded-symbol/weak-factorization
theorems on Paley–Wiener spaces; Zhang
([arXiv:2505.00669](https://arxiv.org/abs/2505.00669)) treats direct spectral convergence of
canonical-system approximants. None of these sources contains this strict shifted-Xi
frontier/curvature composition. Novelty remains unverified pending specialist review.

## New universal principle

False RH cannot evade route by eliminating producers, trapping them at finite mass, or hiding them
on plateaux. It can survive only by making total frontier travel asymptotically inefficient relative
to exact curvature prices. Every strict rung decomposes into priced Lipschitz persistence followed
by unpriced positive-chamber free flight. Required next theorem is lower control of priced fraction
of cofinal frontier travel, or an exact identity showing free-flight slack cannot dominate.

## Lean certificate

- module:
  `formal/GaloisForLFunctions/RHTower/XiShiftedHankelStrictFrontierCurvatureRenewal.lean`
- umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- `xiShiftedHigherBlockFailureSet_mono`
- `xiShiftedHigherBlockTerminalFrontier_mono_of_le`
- `exists_sourceAdaptive_frontierCertificate_of_strict_step`
- `exists_occupied_xiShiftedHigherBlockTerminalFrontier_gt_of_not_riemannHypothesis`
- `exists_cofinal_sourceAdaptive_frontierCertificate_of_not_riemannHypothesis`
- `riemannHypothesis_or_cofinal_sourceAdaptive_frontierCertificates`

Direct `lake env lean` and targeted module build pass after umbrella wiring. All six new theorem
axiom audits report only `propext`, `Classical.choice`, and `Quot.sound`. No computation or
unproved declaration enters.

## Log

- 2026-08-12 — created in 1-in-progress; C1–C4 hostile audit complete; dependency-closed proof
  recorded pending Lean signature verification.
- 2026-08-12 — all four paper claims formalized; moved to 3-formalized after targeted audit.
