# Source-horizontal Wold single-holomorphic-profile no-go

- **ID:** `source-horizontal-wold-single-holomorphic-profile-no-go`
- **Stage:** 5-failed
- **Type:** FALSIFIED + THEOREM (Lean)
- **Source:** `../1-in-progress/source-horizontal-wold-weighted-resolvent-edge-frankenstein.md`
- **Statement:** No complex-differentiable one-variable function realizes the nonconstant
  horizontal Wold polar coefficient on all centered spectral points.

## Goal

Test whether the exact mass--Xi Euler-contour identity can produce the Wold-weighted resolvent
endpoint by multiplying its holomorphic mass test by one additional holomorphic factor.

## Gates

- [x] 0 → 1 in-progress: explicit candidate and existing contour target
- [x] failure theorem: unconditional proof rules out whole one-holomorphic-variable category
- [x] positive survivor: reflection-doubled source pairing identified and formalized
- [x] Lean certificate and targeted build

## Conjecture attacked

Let

\[
 a(u)=\frac{W(u)}{1+W(u)},\qquad
 W(u)=-\frac{\log 2}{2}\,uF(u).
\]

Conjecture asked for an entire `f : ℂ → ℂ` satisfying

\[
 f(z)=a(-2\operatorname{Im}z).
\]

Such an `f` could be inserted directly into the existing one-variable Euler contour.

## Killing theorem

Any complex-differentiable function factoring through `Im z` is invariant under every real
translation. Dyadic positive real periods tend to zero and never vanish, so corpus period
rigidity forces the function to be constant. Wold polar work is zero at `u=0` and strictly positive
at every `u≠0` by its quartic lower bound. Values at `z=0` and `z=i` therefore contradict
constancy.

Lean declarations:

- `differentiable_constant_of_eq_imaginaryProfile`;
- `sourceHorizontalWoldNormalizedPolarRateWeight_pos_of_ne_zero`;
- `no_differentiable_sourceHorizontalWoldNormalizedPolarImaginaryProfile`.

Module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalWoldHolomorphicProfileNoGo.lean`.

## No-go closure

- **Exact killing theorem/mechanism:** nonconstant horizontal profiles have arbitrarily small real
  periods and hence cannot be complex differentiable in one variable.
- **Strongest positive survivor:** horizontal coefficients must be produced from at least two
  independently retained orientations: a sesquiholomorphic/reflection-doubled pairing,
  operator-valued source, or equivalent two-contour construction. Existing
  `gaussHodgeMassCurrent` supplies exactly such a coefficient: it pairs two reflection-odd
  source-horizontal components before scalarization, is positive exactly off line, and retains
  prime and Gauss-depth labels.
- **New insight:** nonlinear Wold functional calculus is not the minimal producer. The labelled
  Gauss--Hodge current is uniformly bounded on the Xi divisor by the open critical-strip window,
  so the *unnormalized* current can weight every resolvent power directly.
- **Status:** survivor formalized in
  `RHTower/GaussHodgeWeightedResolventEdge.lean`; exact capstone
  `forall_gaussHodgeSourceResolventMoment_re_nonneg_iff_riemannHypothesis`.

## Verification

- direct Lean check: PASS
- targeted module build: PASS
- axiom audit: only standard Mathlib axioms
- global formal lint: blocked by unrelated concurrently added Deninger/Maynard/etc. modules not
  wired into umbrellas; both modules on this card are wired and absent from lint errors

## Log

- 2026-08-11 — single-holomorphic-factor conjecture killed in Lean.
- 2026-08-11 — reflection-doubled Gauss--Hodge survivor strengthened to literal unnormalized
  source-current resolvent endpoint.
