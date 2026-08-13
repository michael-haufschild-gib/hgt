# Mass-shifted arcsine-vacuum renormalized source law

- **ID:** `mass-shifted-arcsine-vacuum-renormalized-source-law`
- **Stage:** 3-formalized
- **Type:** THEOREM + SHARP NO-GO + POSITIVE SURVIVOR · Lean 4
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** Current Christoffel completion contains two deterministic positive vacuum
  accounts: invisible next-edge tax `(n+1)/16` and visible adaptive-Gauss tax `(15n+5)/16`.
  Their sum is exact coordinate-dilated arcsine recession `n+3/8`. Therefore even canonically
  renormalized positive Gauss walls cannot form finite trace; correct arithmetic object is signed,
  source-first deviation from full arcsine vacuum, which vanishes on every coordinate-dilated
  arcsine admission, tends to zero at every fixed Xi degree, and preserves all strict-frontier
  residues.

## Gates

- [x] 0 → 1 in-progress: claim, dependencies, hostile model, and positive survivor identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean theorem, targeted build and axiom audit green
- [ ] 3 → 4 publication-ready: independent novelty/priority review

## Conjecture → proof/fail ledger

1. `[FALSIFIED]` Subtracting sole one-coordinate Gaussian observer defect `(n+1)/16` makes the
   remaining positive wall a possible finite trace diagonal. Exact arcsine model leaves
   `(15n+5)/16`, still linearly divergent.
2. `[FALSIFIED]` Divergence is caused only by finite observer loss. Most divergence is already in
   visible adaptive Gaussian bulk.
3. `[POSITIVE SURVIVOR]` Full forced vacuum counterterm is `n+3/8`, not `(n+1)/16`. It is selected
   uniquely by exact current-Christoffel completion on every nonzero coordinate dilation of the
   arcsine admission.
4. `[PAPER TARGET]` Full vacuum-centered Xi source is signed and nonlinear/admission-sensitive;
   fixed-degree recession is zero, while subtraction of the regular degree counterterm leaves
   every intrinsic strict-frontier residue unchanged.

## Dependency-closed paper proof

Let `s°_k=binom(2k,k)/4^k` be shifted-arcsine moments. For every `n>0`, corpus source recession and
Jacobi-energy identities give

```text
E_n(s°) = n + 3/8.
```

Because `beta_(n+1)(s°)=1/16`, current Christoffel completion is exactly `n+3/8`. Existing adaptive
Gauss edge split is

```text
E_n/(16 beta_(n+1))
  = (n+1)/16 + Q_n/(16 h_n beta_(n+1)),
```

where `Q_n>0` is source-selected Gaussian aggregate. Hence

```text
Q_n/(16 h_n beta_(n+1))
  = n + 3/8 - (n+1)/16
  = (15n+5)/16.
```

Thus minimal renormalization remains linearly divergent even in fully positive arcsine tower. A
positive finite trace cannot be completion mechanism.

Define full vacuum counterterm `V_n=n+3/8` and actual centered scale-completed arithmetic source

```text
D_n(w)=scaleCompletedRelativeArithmeticSource(w,n)-V_n.
```

Exact coordinate-dilated arcsine completion equals `V_n` for every nonzero dilation, so its
centered source is identically zero. Existing fixed-degree Xi recession tends to `V_n`, therefore
`D_n(w)→0` for each fixed `n>0`.

At strict frontier of first contact `d>0`, existing law gives `u^d W_n(y+u)→R_(n,d)>0`. Since
`u^d V_n→0`,

```text
u^d (W_n(y+u)-V_n) → R_(n,d)>0.
```

Full vacuum subtraction removes deterministic positive recession without erasing local arithmetic
pole. QED.

## Significance and exact residual

Correct common object cannot be positive trace of raw or minimally-renormalized walls. It must be
signed arcsine-vacuum deviation formed after adaptive source admission and Christoffel completion,
but before degree/reflection reporting. Exact remaining theorem is degree-uniform control or a
cross-degree action law for `D_n` along parabolic first-contact schedules. Fixed-degree convergence
alone does not prove RH.

## Novelty

`[NOVELTY UNVERIFIED]`. Generic Gaussian quadrature defects, arcsine Jacobi coefficients, free
Jacobi backgrounds, and sum-rule subtraction are classical. Targeted audit found:

- Killip--Simon, [Sum Rules for Jacobi Matrices and Their Applications to Spectral Theory](https://arxiv.org/abs/math-ph/0112008), classifying Hilbert--Schmidt perturbations of free Jacobi matrix through positive sum rules;
- Vanlessen, [Strong asymptotics of recurrence coefficients for generalized Jacobi weights](https://arxiv.org/abs/math/0212014), deriving complete recurrence asymptotics from Riemann--Hilbert analysis;
- Kuijlaars--McLaughlin--Van Assche--Vanlessen, [Riemann--Hilbert strong asymptotics on `[-1,1]`](https://arxiv.org/abs/math/0111252), including recurrence and Hankel asymptotics;
- Romik, [Orthogonal polynomial expansions for the Riemann xi function](https://arxiv.org/abs/1902.06330), treating fixed Hermite, Meixner--Pollaczek, and continuous-Hahn expansions of Xi.

No exact analogue was found for adaptive source-selected Gauss/newborn partition, literal
shifted-Xi rational--Gamma/von-Mangoldt `P^sharp` source, two-account `(n+1)/16+(15n+5)/16`
vacuum, or strict-frontier residue-stable full subtraction.

## Log

- 2026-08-13 — minimal observer-defect renormalization killed by exact arcsine positive tower;
  full source-vacuum counterterm and signed arithmetic deviation isolated.
- 2026-08-13 — formalized in
  `RHTower/XiShiftedArcsineVacuumRenormalizedSourceLaw.lean` and wired into `RHTower.lean`.
  Direct Lean and targeted module build passed. Seven capstone axiom audits returned only
  `propext`, `Classical.choice`, and `Quot.sound`. Global lint sees both new modules through
  umbrella; remaining failures are unrelated concurrent unreachable modules.
