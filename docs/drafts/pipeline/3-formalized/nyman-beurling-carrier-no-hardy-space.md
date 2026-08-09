# The Nyman–Beurling carrier: bounded point evaluations without a Hardy space

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The gate

`HTGeometry/HardyClosureZeroFree.lean` proved the closure obstruction abstractly and named what was
missing:

> Instantiating it with the paper's concrete half-plane Hardy space still requires the half-plane `H²`
> carrier, its bounded point evaluations, and the concrete zeta generators; those are the current
> source-realization wall.

`QuantitativeNymanBeurling.lean` then carried the quantitative form as *scalar bookkeeping* (`nbFloor`,
`halfPlaneKernel`) with the Hilbert-space content described in its docstring but not formalized.

## The gate is gone

The wall assumed the criterion needs the Hardy space of a half-plane — Paley–Wiener, boundary values,
reproducing kernels. It does not. **On the Nyman–Beurling carrier the Mellin point evaluation is an
ordinary `L²` inner product.**

Pushing Báez-Duarte's data along `t = 1/u` (a measure-preserving change of variable from `L²((0,1], dt)`)
puts everything on the tail ray with plain Lebesgue measure, `RHTower.bdMeasure = volume.restrict (Ioi 1)`:

| object | on `(0,1]` | on `(1,∞)` |
|---|---|---|
| target | `1_{(0,1]}` | `bdTargetFun u = 1/u` |
| generator | `ρ_θ(t) = {θ/t} − θ{1/t}` | `bdGenFun θ u = ({θu} − θ{u})/u` |
| evaluation | `f ↦ ∫₀¹ f(t)t^{−s}dt` | `F ↦ ∫₁^∞ F(u)u^{s−1}du` |

and the evaluation is `⟪bdDetectorFun s, ·⟫` with `bdDetectorFun s u = conj(u^{s−1})`. That vector is in
`L²` exactly when `Re s < ½` — `memLp_bdDetectorFun` — with

`‖bdDetector s‖² = ∫₁^∞ u^{2Re s−2} du = 1/(1 − 2Re s)`  (`norm_sq_bdDetector`),

so **bounded point evaluation is Cauchy–Schwarz**. That squared norm is the `1/(2σ)` diagonal kernel of
`QuantitativeNymanBeurling` in the only form the argument consumes.

## What is proved

`RHTower/BaezDuarteL2Carrier.lean`, all `#print axioms`-clean:

* the carrier and its membership criterion (`memLp_two_bdMeasure_of_sq_le`), and membership for the
  target and every generator (`memLp_bdTargetFun`, `memLp_bdGenFun`);
* `inner_bdDetector` — the detector computes the Mellin integral;
* `norm_sq_bdDetector`, `norm_bdDetector`, `bdDetector_ne_zero` — the kernel value in closed form;
* `inner_bdDetector_bdTarget` — the target goes to `1/ρ` (detector at `s = 1 − ρ`);
* `inner_bdDetector_bdGen` — the generator goes to `−(θ^ρ − θ)·ζ(ρ)/ρ`, using the corpus's
  `FractionalPartZeta.integral_Ioi_zero_fract_dilate_cpow` plus the observation that `{θu} − θ{u}`
  vanishes on `(0,1)` for `θ ≤ 1`, so the tail integral is the full-ray integral;
* `bdTarget_notMem_closedSpan_of_zero` — the concrete closure obstruction at a zero `ρ` of `ζ` with
  `½ < Re ρ < 1`: the target is not in the closed span of the generators;
* `bdTarget_dist_floor` — the quantitative floor `√(2Re ρ − 1)/|ρ| ≤ ‖target − G‖` for every `G`
  annihilated by the detector (no zeta hypothesis: only `½ < Re ρ`);
* `bdTarget_dist_floor_of_mem_closedSpan` — at a zero, every finite combination of generators and every
  `L²` limit of such obeys that floor;
* `bdTarget_dist_floor_eq_nbFloor` — the floor *is* the corpus's `nbFloor (1/|ρ|) (Re ρ − ½)`, which
  attaches the existing scalar layer to actual `L²` distances;
* `bdTarget_dist_floor_attained_of_zero` — the floor is exactly attained.

Supporting generalization: `RHTower/VanishingCostRCLike.lean` proves the vanishing-cost theorem over any
`RCLike` field (`dist_innerKer_ge`, `dist_innerKer_attained`, `innerKer_vanishing_cost`). The complex case
is *necessary* here: the detector is a complex functional, and its kernel is a complex hyperplane, strictly
smaller than the kernel of the real part of the inner product. The three real statements of
`BoundaryInteriorVanishingCost` are now one-line consequences of it, so no proof is duplicated.

## Why this matters for the route

Every no-go established in this folder for the partial-sum lane is a statement about bounds that see the
coefficients only through their moduli (`coefficient-free-cap-law`,
`primitive-ratio-decomposition-and-third-cap`). The Nyman–Beurling lane is not of that shape: its
invariant is a *distance in a Hilbert space*, extremal rather than aggregated, and the caps do not touch
it. What was blocking it was the belief that its carrier needed machinery the corpus does not have. That
is now settled: the carrier is elementary and it is built.

## What remains

The floor above is the **easy** direction (RH failure ⟹ distances bounded below). The hard direction — RH
⟹ the distances tend to zero — is not addressed here and is the real content of the criterion. Two
concrete follow-ups inside reach of this file:

1. connect "RH fails" to "there is a zero with `½ < Re ρ < 1`" (the functional equation step) so the floor
   theorems can be stated from `¬ RiemannHypothesis` directly;
2. the Gram matrix of the generators in this carrier is now a well-posed, fully unconditional object —
   `⟪bdGen θ₁, bdGen θ₂⟫` is an explicit integral of fractional parts. Computing it is the entry point to
   the quantitative upper bounds, and it is exactly the kind of object `FractionalPartZeta` already
   handles.
