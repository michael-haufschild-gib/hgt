# Cauchy control replaces absolute summability in log-shift potential limits

Status: [PAPER PROVED; LEAN VERIFIED]
Date: 2026-10-09
Source policy: our Lean corpus only; no external papers or web searches.

## Objective and plan

1. Replace absolute summability by Cauchy control of absolute normalized deviation
   in uniform truncated-potential and whole-panel convergence.
2. Discharge this control from asymptotic log-shift positivity and summable excess.
3. Obtain an exact enlarged-domain potential characterization; audit every public
   theorem in Lean, wire/index the leaf, run lint, and clean owned scratch files.

## Dependency-closed paper proof

Let `a=weilDeviation lam`, `e=deviationExcess lam`, `v=deviationDeficit lam`.
Assume `CauchyBounded |a| D`. Its scale-one profile series at every real
center is summable and has sum at most `D`; nonnegativity implies `D>=0`.

The corpus supplies `exp(-2|x|) <= cauchyProfile 1 0 x` and
`|K_L(z)-K(z)| <= A exp(-2(L-1)) exp(-2|z|)`, with `A>=0`.
Reflecting the two shifts in the Cauchy profiles therefore gives

`|a(n)| (|K_L(y+log n)-K(y+log n)| +
          |K_L(y-log n)-K(y-log n)|)
 <= A exp(-2(L-1)) |a(n)|
      (P(1,y,log n)+P(1,y,-log n))`.

The same majorant with the ordinary kernel decay establishes summability of
both potential series. Summing the defect bound proves, uniformly in real y,

`|psi_L(y)-psi(y)| <= A D exp(-2(L-1))`.

The existing exact panel identity needs only summability of the truncated
potential terms; expose that actual dependency instead of absolute summability.
The existing uniform zero-side estimate is independent of lam. Together they
give uniform approximation of every entry of the expanding log-shift panel by
`2(psi(log m)-psi(0))`, now assuming only Cauchy control of |a|.

If asymptotic log-shift positivity and summable excess hold, the previous
deficit-translation theorem supplies Cauchy control of v. Summability supplies
Cauchy control of e, and `|a| <= e+v` supplies Cauchy control of |a|. Thus the
uniform approximation has no added analytic premise on this one-sided domain.

Finally, for summable excess, asymptotic log-shift positivity is equivalent to
the conjunction of Cauchy control of |a| and all inequalities
`psi(0)<=psi(log m)` for integers m>=2. Necessity uses the previous sampled
potential inequality and the new absolute Cauchy bound. Sufficiency follows
from uniform approximation, since each limiting panel entry is nonnegative.

## Boundaries and audit

No deficit summability, full Weil positivity, new axiom, numerical experiment,
heartbeat increase, or RH claim. Mixed-sign summable-excess rigidity remains open.
The exact local lexical query found no indexed combination of CauchyBounded
and truncatedDeviationPotential. Broader local search plus source inspection
identified the kernel-defect estimate, Cauchy majorant, and existing uniform
panel theorem under absolute summability. No external novelty claim.

## Lean artifacts and validation

New leaf: `formal/GaloisForLFunctions/RHTower/WeilLogShiftCauchyPotentialCone.lean`.
Public results:

- `exists_cauchyBounded_absDeviation_of_logShiftAsymptoticPositive`
- `exists_uniform_truncatedPotential_error_of_cauchyBounded`
- `exists_uniform_logShift_potential_error_of_cauchyBounded`
- `exists_uniform_logShift_potential_error_of_summable_excess`
- `weilLogShiftAsymptoticPositive_iff_cauchyBounded_potential`

In `WeilLogShiftPotentialCone.lean`, exposed the exact summability dependency
as `logShift_panel_potential_identity` and the existing coefficient-independent
estimate as `exists_uniform_logShift_zeroSide_bound`. The original theorem
under absolute summability now invokes the generalized identity; its public
statement is unchanged.

Both changed leaves passed `lake --old env lean ... -o ...` with default
heartbeats and no diagnostics. Scratch signatures and axiom checks passed
for all five new theorems and all seven public theorems in the shared module;
all twelve use exactly `[propext, Classical.choice, Quot.sound]`.

New leaf wired into `RHTower.lean`. Index refresh passed and all seven new
public API rows were verified. Scoped whitespace checks passed.
Authoritative lint exited 1 with eight unrelated unreachable modules:
RHTower's `CCMGroundEnergyZeroSumBound`, `CanonicalProductE1RealLineBounds`,
`StretchedBoseRiemannEquivalence`; HTGeometry's `ApertureConeCalculus`,
`ApertureConeWinding`, `ApertureLogTranslation`, `ApertureOpenHistoryIdeal`,
and `BoundaryCoronaCStarAlgebra`. No reported lint error concerns these leaves.

## Exact insight and next frontier

Uniform whole-panel convergence needs a bound on local logarithmic mass,
encoded by Cauchy control, rather than a finite total absolute deviation.
The previous deficit translation theorem discharges that condition from
the same one-sided positivity and excess assumptions already under study.
The resulting equivalence explicitly includes genuine series convergence
through Cauchy control, avoiding divergent-`tsum` defaults.

Next conjecture: on the summable-excess domain, replace the Cauchy-control
side condition by convergence only at the origin and integer-log samples.
Nonnegative deficit series at those samples may reproduce the block bound
directly. This is not proved here. Mixed-sign rigidity remains open.
