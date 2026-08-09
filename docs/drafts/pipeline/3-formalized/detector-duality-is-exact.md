# The detector method is exact: distance to a span = best annihilator pairing

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The question this settles

Every positive lower bound in the Nyman–Beurling lane has the same shape. Exhibit a carrier element `w`
orthogonal to all the generators with `⟪w, 1/u⟫ ≠ 0`; Cauchy–Schwarz then gives

`dist(1/u, span) ≥ ‖⟪w, 1/u⟫‖ / ‖w‖`.

`VanishingCostRCLike.dist_innerKer_ge` is that step, and `bdTarget_dist_floor` applies it at a zeta zero.
The obvious worry is that the method is lossy: perhaps the true distance is much larger than anything a
single annihilator can certify, in which case a proof of `d_N → 0` would need machinery of a different
kind. This card removes the worry.

## What is proved

`RHTower/DetectorDuality.lean`, for any family `S` in a complete inner product space over any `RCLike`
field and any target `x`:

* `mem_orthogonal_span_iff` — orthogonality to `span S` is orthogonality to each member (span induction);
* `norm_inner_le_norm_mul_infDist_span` — the one-annihilator lower bound, for a whole family at once;
* `inner_starProjection_orthogonal_self` — `⟪P_{Kᗮ}x, x⟫ = ‖P_{Kᗮ}x‖²`;
* **`infDist_span_eq_norm_starProjection_orthogonal` — `dist(x, span S) = ‖P_{(span S)ᗮ} x‖`**;
* **`exists_detector_norm_inner_eq_infDist_span` — some `w` with `w ⟂ S`, `‖w‖ ≤ 1` and
  `‖⟪w,x⟫‖ = dist(x, span S)` exactly.** So

  `dist(x, span S) = max { ‖⟪w,x⟫‖ : w ⟂ S, ‖w‖ ≤ 1 }`,

  and the detector method is not merely sufficient — it is sharp;
* `infDist_span_eq_zero_iff`, `mem_topologicalClosure_iff`, `mem_topologicalClosure_span_iff` —
  approximability is *exactly* the nonexistence of a separating annihilator;
* `topologicalClosure_eq_top_iff`, `topologicalClosure_span_eq_top_iff` — density is *exactly* the
  nonexistence of a nonzero annihilator;
* `infDist_span_sq_add_norm_sq_starProjection` — the exact mass split `d² + ‖P_{closed span}x‖² = ‖x‖²`;
* `forall_dual_eq_zero_iff_forall_inner_eq_zero` — the Riesz bridge: annihilation by continuous
  functionals and annihilation by vectors are the same condition;
* **`mem_topologicalClosure_span_iff_forall_dual`** — hence the Hahn–Banach criteria already in the corpus
  (`RHTower/DenseSpanDuality.lean`, `HTGeometry/DenseOfVanishingDual.lean`), which give sufficiency over an
  arbitrary normed space, are *sharp* over a complete inner product space;
* range forms, for indexed families.

Instantiated at the Báez-Duarte data:

* `bdDist_eq_norm_starProjection` — every Báez-Duarte distance is the norm of a projection;
* `bdDist_sq_add_explained_mass` — `d(θ)² + ‖P bdTarget‖² = 1`, the exact explained-mass identity (this
  replaces the inequality `explained_mass_le_one` of `BaezDuarteGramReduction`);
* `exists_bdDetector_norm_inner_eq_bdDist`, `bdDist_eq_zero_iff`;
* **`riemannHypothesis_of_forall_orthogonal_bdGen`** — if every carrier element orthogonal to all the
  generators `({θᵢu} − θᵢ{u})/u` is orthogonal to `1/u`, RH holds;
* `bdDistDiscrete_eq_sup_detector` — for the classical discrete system, `d_N` both bounds and is attained
  by unit annihilators of the first `N` generators;
* `exists_bdDetector_inner_ne_zero` — combined with `bdDistDiscrete_pos`, **every** finite section has a
  unit annihilator pairing nontrivially with `1/u`: the obstruction is present at every finite level and
  the criterion can only be met in the limit;
* **`riemannHypothesis_of_detector_bound`** — if for every `ε > 0` some finite section has all its unit
  annihilators pairing with the target below `ε`, RH holds.

## Why it matters

Two things.

**The lower-bound method is not the weak link.** `bdDist_floor_of_zero` produces a positive floor from a
single detector at a zero off the critical line. Duality says that floor is not an artefact of a crude
method: the distance *is* the best detector pairing, so if the distances are bounded away from zero there
is a detector witnessing it, and if they tend to zero no detector can obstruct. The two halves of the
criterion are the two halves of one identity.

**The remaining problem changes type.** `riemannHypothesis_of_detector_bound` states RH as a *rigidity*
statement about the orthogonal complement of the generators, not an approximation statement about their
span: no need to construct coefficients, only to show that annihilators of long initial segments cannot
pair with `1/u`. `inner_bdDetector_bdGen` gives `⟪bdDetector (1−ρ), bdGen θ⟫ = −(θ^ρ − θ)ζ(ρ)/ρ` for
`½ < Re ρ < 1`, so every zero in that strip produces a separating annihilator; duality says the criterion
holds exactly when no annihilator separates. Proving RH along this lane is therefore the task of excluding
separating annihilators — not of constructing approximants.

(The converse direction, that *all* separating annihilators come from zeros, is Báez-Duarte's theorem and
is not formalized here; nothing in this card assumes it.)

## What this opens (next target)

Duality makes the *finite-section* lower bound accessible, which is the piece the layer map records as
missing for Burnol's `liminf d_N² log N ≥ ∑ m_ρ²/|ρ|²`. An annihilator of `N` generators is far easier to
produce than an annihilator of the whole family: with `M > N` detectors `bdDetector (1−ρⱼ)` some nonzero
combination annihilates all `N` generators by rank alone, and its pairing with the target is then a lower
bound for `d_N` by `norm_inner_le_norm_mul_infDist_span`. All the ingredients are already in the corpus —
`inner_bdDetector_bdGen` (no zero assumed), `inner_bdDetector_eq_cauchyGram` for the detector Gram,
`linearIndependent_bdDetector`, `bdTarget_dist_floor_orthonormal` for the Bessel step. What is missing is
the linear-algebra selection of the annihilating combination and the resulting quotient of Gram
determinants. Any bound so obtained must decay in `N` (it is `≤ d_N` and RH would force `d_N → 0`); its
rate is the content, and `1/√(log N)` is the classical target.

## Reuse beyond this lane

The general half is field-agnostic and target-agnostic; it applies to every closed-span/density question in
the corpus. `ArithmeticLogClockBoundedCompletionSaturation.primeBoundedPostprocessedTraceClock_pair_mem_graphClosure`
opens with exactly the two rewrites `← orthogonal_orthogonal_eq_closure` and `mem_orthogonal'`, which is
`mem_topologicalClosure_iff`; `ArithmeticLogClockFiniteJetSaturation` and `ArithmeticDilationTraceClass` do
the same for `= ⊤`, which is `topologicalClosure_eq_top_iff`. Those files predate this one and are left as
they are; new work should use the named laws.
