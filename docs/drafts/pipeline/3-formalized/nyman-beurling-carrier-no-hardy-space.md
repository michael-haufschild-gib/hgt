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

## Addendum (same day): the criterion, and the Gram object

Both follow-ups named above are done.

**1. The criterion, sufficient direction.** `RHTower/NymanBeurlingCriterion.lean`. The corpus already had
the "where does a counterexample live" bookkeeping (`rh_iff_xi_ne_zero_right`, `xi_zero_re_mem_open_unit`,
`xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial`), so no new analysis was needed:

* `exists_zetaZero_re_gt_half_of_not_riemannHypothesis` — failure of RH yields a zero of `ζ` with
  `½ < Re ρ < 1`;
* `riemannHypothesis_of_bdTarget_mem_closedSpan` — **if the target lies in the closed span of the
  Báez-Duarte generators, the Riemann hypothesis holds**;
* `riemannHypothesis_of_bdTarget_mem_closedSpan_family` — the same for an *arbitrary* subfamily of
  dilations `θ ∈ (0,1]`, which is strictly stronger (a smaller span is harder to reach), so this is the
  form to use;
* `riemannHypothesis_of_bdTarget_mem_closedSpan_discrete` — the instance at `θ = 1/(n+1)`, the discrete
  Báez-Duarte system the literature works with;
* `exists_pos_bdDist_floor_of_not_riemannHypothesis` and its discrete counterpart — the quantitative
  contrapositive: if RH fails, one positive constant lies below *every* Báez-Duarte distance, so the
  approximation is obstructed rather than merely slow.

This is the direction an actual proof of RH would consume: it reduces RH to a concrete approximation
statement in an explicit `L²` space, with no zeta-side hypothesis anywhere in the chain.

**2. The Gram object.** `RHTower/BaezDuarteGram.lean`. Every generator is real valued
(`bdGenFun_eq_ofReal`), so the carrier inner product is the complexification of the classical real Gram
integral

`bdGram θ₁ θ₂ = ∫₁^∞ ({θ₁u} − θ₁{u})({θ₂u} − θ₂{u}) u^{-2} du`

(`inner_bdGen_eq_bdGram`), which is symmetric (`bdGram_symm`), has the squared norms on its diagonal
(`bdGram_self`), and is positive semidefinite with the quadratic form equal to the squared norm of the
corresponding combination (`bdGram_quadraticForm_eq_norm_sq`, `bdGram_quadraticForm_nonneg`). Nothing here
evaluates the integral — the point is that the least-squares object of the quantitative theory is now a
well-posed unconditional definition in the corpus.

**Still open, and this is the whole remaining content:** the converse direction, RH ⟹ the distances tend
to zero. Evaluating `bdGram` in closed form is the classical entry point (for rational ratios it is a
cotangent sum), and it is real analytic work, not bookkeeping.

## Addendum 2 (same day): the target pairing in closed form

`RHTower/BaezDuarteTargetPairing.lean`. The least-squares problem has two data; the Gram matrix is the
first (above) and this is the second, evaluated **exactly**:

* `norm_bdTarget` — `‖bdTarget‖ = 1`. The target is a unit vector, so every Báez-Duarte distance lies in
  `[0,1]` and the floor `√(2Re ρ − 1)/|ρ|` is a genuine fraction of the total.
* `inner_bdGen_bdTarget` — `⟪bdGen θ, bdTarget⟫ = −θ log θ`.
* `norm_bdGen_lower`, `sq_le_bdGram_self` — Cauchy–Schwarz against the unit target gives the
  unconditional Gram-diagonal bounds `θ|log θ| ≤ ‖bdGen θ‖` and `(θ log θ)² ≤ bdGram θ θ`.

The evaluation uses no zeta function and — worth recording — **no Euler–Mascheroni constant**. Writing
`fractInvSq v = {v}v^{−2}`, the dilation identity `∫_{u>1} fractInvSq(θu) du = θ^{−1}∫_{v>θ} fractInvSq`
(`integral_Ioi_one_fractInvSq_dilate`) reduces the pairing to

`θ·(∫_{v>θ} − ∫_{v>1}) fractInvSq = θ∫_θ^1 {v}v^{−2}dv = θ∫_θ^1 v^{−1}dv = −θ log θ`,

so the constant `∫_1^∞ {v}v^{−2}dv = 1 − γ` cancels between the two terms and never has to be evaluated.
That cancellation is exactly what Báez-Duarte's normalisation `{θ/t} − θ{1/t}` is for, and it is why this
step is elementary while the Gram entries are not.

Two further consequences, in the same file:

* `exists_norm_sq_sub_smul_bdGen` — the exact `N = 1` least-squares value: the best approximation of the
  target by multiples of a single generator leaves `1 − (θ log θ)²/‖bdGen θ‖²`.  This is the first *upper*
  bound on a Báez-Duarte distance in the corpus (everything else here is a lower bound).
* `riemannHypothesis_of_norm_bdGen_eq` — if Cauchy–Schwarz is saturated by one generator, i.e.
  `‖bdGen θ‖ = θ|log θ|`, then RH holds.  This is the weakest instance of the criterion and the equality is
  expected to fail; its content is to name what the criterion is sensitive to — the ratio
  `θ|log θ|/‖bdGen θ‖`, i.e. the Gram diagonal.  Every quantitative Báez-Duarte statement is a statement
  about how close that ratio, or its many-generator analogue, gets to `1`.

## Addendum 3 (same day): the detector Gram is the corpus's Cauchy kernel

`RHTower/BaezDuarteDetectorGram.lean`. Two Mellin detectors pair explicitly:

`⟪bdDetector s₁, bdDetector s₂⟫ = ∫₁^∞ u^{s₁ + conj s₂ − 2} du = 1/(1 − s₁ − conj s₂)`

(`inner_bdDetector_bdDetector`; the conjugation step needed `conj_ofReal_cpow`, proved here from
`Complex.conj_cpow`). Writing `s = ½ − w` this is `1/(w₁ + conj w₂)`, so:

* `inner_bdDetector_eq_cauchyGram` — **for any family `w` with `Re w > 0`, the corpus's
  `rightHalfPlaneHardyCauchyGram w` is literally the Gram matrix of the detector vectors.** So
  `rightHalfPlaneHardyCauchyGram_posSemidef`, which the corpus proves by an explicit boundary integral, is
  the statement that a Gram matrix is positive semidefinite. I did not reprove PSD — the value here is the
  identification, which explains the theorem rather than repeating it.
* `inner_bdDetector_eq_rightHalfPlaneHardyCauchyGram` / `inner_bdDetector_bdDetector_zeros` — at zeta
  zeros the relevant `w` are the *centered* zeros `ρ − ½`.

That completes the data of the least-squares floor: the Gram matrix of the detectors is the Cauchy kernel
`1/((ρᵢ − ½) + conj(ρⱼ − ½))`, and their components against the target are `1/ρᵢ`
(`inner_bdDetector_bdTarget`).

* `inner_combination_bdDetector_eq_zero` — every finite combination of detectors at zeros annihilates the
  closed span of the generators;
* `bdTarget_dist_floor_orthonormal` — hence, by Bessel's inequality inside the detector span, **the squared
  Báez-Duarte distance is at least the total squared pairing of the target with any orthonormal family
  built from those detectors.**

This is the Hilbert-space skeleton of the Burnol-type lower bound `liminf d_N² log N ≥ ∑_ρ m_ρ²/|ρ|²`: the
arithmetic input is only the location of the zeros, and everything else is the geometry of the Cauchy
kernel. What is *not* here: the `log N` normalisation and the passage to the full zero sum, which need the
finite-section distances rather than the distance to the whole closed span.

## Addendum 4 (same day): `d_N → 0 ⟹ RH`

`RHTower/BaezDuarteDistance.lean` restates the criterion through the distances the literature actually
uses, `d_N = dist(1_{(0,1]}, span of the first N generators)`. All of it is metric bookkeeping around
`Metric.infDist`; the analytic content stays in the detector floor.

* `bdDist`, `bdDistFinset`, `bdDistDiscrete` — the distance for an arbitrary family, for a finite section,
  and for the classical discrete system `θ = 1/(n+1)` sectioned by `Finset.range N`;
* `bdDist_le_one`, `bdDistDiscrete_mem_Icc` — the distances lie in `[0,1]`, because the target is a unit
  vector and `0` is in every span;
* `bdDistFinset_antitone`, `bdDistDiscrete_antitone` — larger sections are at least as good;
* `riemannHypothesis_of_bdDist_eq_zero` — a vanishing distance forces RH;
* **`riemannHypothesis_of_tendsto_bdDistDiscrete` — if `d_N → 0` then the Riemann hypothesis holds**, and
  `riemannHypothesis_of_tendsto_bdDistFinset` for an arbitrary family and an arbitrary sequence of finite
  sections;
* `bdDistDiscrete_floor_of_zero`, `bdDist_floor_of_zero`, `bdDist_dichotomy` — conversely, a zero with
  `½ < Re ρ < 1` puts `√(2Re ρ − 1)/|ρ|` below *every* `d_N`, so `d_N → 0` is impossible if RH fails.

So the chain from the classical analytic statement to RH is now complete and unconditional in Lean:
`d_N → 0` ⟹ RH, with the quantitative converse. What remains — and it is the whole difficulty — is
proving `d_N → 0`, which is equivalent to RH and needs the Gram matrix asymptotics, not more bookkeeping.

## Addendum 5 (same day): the distance is a function of the Gram matrix

`RHTower/LeastSquaresProjection.lean` — the universal law, for an arbitrary inner product space over an
arbitrary `RCLike` field. Given `v : n → H`, a target `x`, and coefficients `c` solving the **normal
equations** `∀ i, ∑ⱼ ⟪vᵢ,vⱼ⟫·cⱼ = ⟪vᵢ,x⟫`:

* `inner_residual_eq_zero`, `inner_residual_span_eq_zero` — the residual is orthogonal to the span;
* `norm_sq_residual` — `‖x − ∑cⱼvⱼ‖² = ‖x‖² − re ∑ᵢ conj(cᵢ)⟪vᵢ,x⟫`;
* `norm_residual_le`, `infDist_span_eq` — the combination is the closest point, so that value *is* the
  distance.

No linear independence or invertibility hypothesis: the statements are about *a* solution of the normal
equations, which is what a least-squares computation produces. (When the family is independent,
`Matrix.posDef_gram_iff_linearIndependent` gives invertibility and hence existence and uniqueness — but the
identities do not need it.)

`RHTower/BaezDuarteLeastSquares.lean` instantiates it, closing the loop with the two data computed earlier:

* `bdDist_eq_of_normalEquations` — the distance is the residual norm;
* `bdDist_sq_eq_of_normalEquations` and, in the classical real form,
  **`bdDist_sq_eq_of_realNormalEquations` — `d² = 1 + ∑ᵢ cᵢ·θᵢ log θᵢ` where `∑ⱼ bdGram θᵢ θⱼ · cⱼ = −θᵢ log θᵢ`.**
  The `1` is `‖bdTarget‖²`.

So the Báez-Duarte distance is now a function of the Gram matrix alone, with every other constant explicit.
Combined with Addendum 4 (`d_N → 0 ⟹ RH`) the reduction is complete: **RH follows from the statement that
the solutions of the `bdGram` linear systems satisfy `∑ᵢ cᵢθᵢ log θᵢ → −1`.** The analytic problem is now
isolated in a single object, `bdGram`, and nothing else in the chain is missing.

## Addendum 6 (same day): the criterion as a template

`RHTower/MellinVanishingCriterion.lean` extracts the mechanism from the Báez-Duarte specifics. The whole
chain needs only a family in the carrier whose Mellin transforms vanish at the detector points of a
hypothetical off-line zero, plus a target whose transform does not — packaged as one predicate,
`MellinAnnihilated G x`:

* `riemannHypothesis_of_mem_closedSpan_of_mellinAnnihilated` — closed-span membership forces RH;
* `riemannHypothesis_of_infDist_eq_zero_of_mellinAnnihilated` — the metric form;
* `dist_floor_of_mellinAnnihilated` — if RH fails, `‖transform of x at ρ‖·√(2Re ρ − 1)` sits below every
  distance;
* `mellinAnnihilated_bdGen` and `riemannHypothesis_of_bdTarget_mem_closedSpan_template` — the Báez-Duarte
  family is one instance, so nothing in the earlier chain was special to it.

So a *new* candidate family — Beurling's dilations of a single function, a Möbius-weighted system, a
Balazard–Saias variant — now needs only two computations (the transforms of its members, and of its
target) to inherit the criterion, the metric form, and the quantitative floor. That is the reusable part of
this lane, and it costs one `MellinAnnihilated` proof per family.

## Addendum 7 (same day): the bridge to mathlib's projector, and the explained mass

Two additions to `LeastSquaresProjection`, both general:

* `hasOrthogonalProjection_span` — the span of a finite family always has an orthogonal projection (it is
  finite dimensional), so no instance hypothesis is needed anywhere;
* `starProjection_eq_of_normalEquations` — **a solution of the normal equations computes mathlib's
  `Submodule.starProjection`.**  So any corpus statement about the orthogonal projection onto a finite span
  can now be evaluated from the Gram matrix and the pairing vector, and conversely mathlib's projector API
  applies to my least-squares data;
* `norm_sq_combination_of_normalEquations` — the *explained mass*
  `‖∑cⱼvⱼ‖² = re ∑ᵢ conj(cᵢ)⟪vᵢ,x⟫`, the complement of `norm_sq_residual`.

Instantiated for Báez-Duarte in `norm_sq_bdProjection_of_realNormalEquations`: the projection of the target
onto a finite section carries exactly `−∑ᵢ cᵢθᵢ log θᵢ` of the target's unit mass. With
`bdDist_sq_eq_of_realNormalEquations` (`d² = 1 + ∑ᵢcᵢθᵢlogθᵢ`) that is the Pythagorean split of the unit
target, and the two formulas cross-check each other.
