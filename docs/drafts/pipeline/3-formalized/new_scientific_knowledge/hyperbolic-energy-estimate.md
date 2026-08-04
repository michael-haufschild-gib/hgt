# The energy estimate for the clock equation

- **ID:** hyperbolic-energy-estimate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** child of `two-species-conformal-clock-scale-law`; the "hyperbolic energy theory, which
  mathlib does not have" named in the closing note of `finite-regularity-clock-probes`
- **Statement:** For a classical solution of `∂ₜ²u = Δu + Vu` with a bounded potential and uniformly
  compact spatial support, the energy `E(t) = ∫ (∂ₜu)² + |∇u|² + u²` satisfies
  `E(t) ≤ E(0)·exp((‖V‖_∞+1)|t|)`. Consequently the Cauchy problem has at most one such solution.

## Goal

Every probe construction in the corpus is an *existence* argument by Fourier synthesis, and each one
buys its solution at the price of derivatives: the Wiener route needs the potential's Fourier density
in a weighted `L¹`, which for a `C^k` potential costs `k > 2d+4`. The route that does not pay that
price is the energy method — the estimate that controls a solution by its data with no Fourier
transform at all. mathlib has no hyperbolic energy estimate, and the corpus has only its
one-dimensional shadow (`HillOscillatorEnergy`).

This card builds the estimate itself. It is the first half of the classical local theory: the
estimate gives uniqueness and the quantitative control on which any future existence proof (Galerkin,
or a fixed point in a Sobolev scale) rests, and it is stated for exactly the class of solutions the
clock programme uses — classical, real, with spatially compact support.

## The computation

With `∂ₜ²u = Δu + Vu`,

```
E'(t) = 2∫ (∂ₜu·∂ₜ²u + ⟨∇u, ∇∂ₜu⟩ + u·∂ₜu)
      = 2∫ (∂ₜu·(Δu + Vu) + ⟨∇u, ∇∂ₜu⟩ + u·∂ₜu)
      = 2∫ ((V+1)·u·∂ₜu)                                   [integration by parts]
      ≤ (‖V‖_∞+1)·E(t),
```

the middle step being `∫⟨∇u, ∇∂ₜu⟩ = -∫ Δu·∂ₜu`, valid because the spatial support is compact. The
last step is `2|ab| ≤ a² + b²`. Grönwall closes it.

## Approach

1. **Supports.** A function vanishing off a compact `K` for every time has all its partial
   derivatives vanishing off `K`; hence every integrand below is continuous with compact support,
   so integrable.
2. **Integration by parts.** mathlib's `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` gives
   `∫ ∂ᵢf·g = -∫ f·∂ᵢg` in a fixed direction for integrable data. Summing over an orthonormal
   family gives the Green identity used above.
3. **Differentiation under the integral.** `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with
   the dominating function supplied by continuity on a compact time interval times `K`.
4. **Grönwall.** `norm_le_gronwallBound_of_norm_deriv_right_le`, and its `f a = 0` corollary for
   uniqueness.

## Gates

- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized — four modules, every theorem unconditional
      (`[propext, Classical.choice, Quot.sound]`)
- [ ] 3 → 4  publication-ready

## Numbered statements

| # | statement | Lean name | state |
|---|---|---|---|
| 1 | supports of a coordinate partial derivative | `coordPartial_eq_zero_of_eventually`, `hasCompactSupport_coordPartial` | **built** |
| 2 | integration by parts on a spatial slice | `integral_mul_coordPartial` | **built** |
| 3 | the Green identity `∫(∑∂ᵢ∂ᵢf)·g = -∑∫∂ᵢf·∂ᵢg` | `integral_laplacian_mul` | **built** |
| 4 | directional derivatives of a field of events: smoothness, supports, slice bridges | `dirDeriv`, `contDiff_dirDeriv`, `dirDeriv_eq_zero_of_notMem`, `dirDeriv_timeDir_eq`, `dirDeriv_spaceDir_eq` | **built** |
| 5 | symmetry of the mixed second derivative | `dirDeriv_comm` | **built** |
| 6 | the clock equation and the energy density | `SolvesWaveEq`, `energyDensity` | **built** |
| 7 | product/sum rules for a directional derivative | `dirDeriv_mul`, `dirDeriv_sq`, `dirDeriv_add`, `dirDeriv_sum` | **built** |
| 8 | the pointwise expansion of `∂ₜ(energy density)` | `dirDeriv_energyDensity` | **built** |
| 9 | the flux identity `∫∂ₜ(energy density) = 2∫(V+1)·u·∂ₜu` | `integral_dirDeriv_energyDensity` (with `slice`, `contDiff_slice`, `hasCompactSupport_slice`, `dirDeriv_zero_of_notMem`) | **built** |
| 10 | differentiation under the integral | `waveEnergy`, `hasDerivAt_waveEnergy` (with `hasDerivAt_timeSlice`, `contDiff_energyDensity`, `energyDensity_zero_of_notMem`, `hasCompactSupport_energyDensity_slice`) | **built** |
| 11 | the flux bound and the Grönwall estimate | `energyDensity_nonneg`, `waveEnergy_nonneg`, `integrable_energyDensity_slice`, `abs_integral_flux_le`, **`waveEnergy_le_exp`** | **built** |
| 12 | vanishing of a solution with zero initial energy | `energyDensity_eq_zero_of_waveEnergy_eq_zero`, **`eq_zero_of_waveEnergy_zero`** | **built** |
| 13 | linearity of the equation and uniqueness for the Cauchy problem | `dirDeriv_sub`, `solvesWaveEq_sub`, `waveEnergy_eq_zero_of_slice_zero`, **`eq_of_solvesWaveEq_of_data_eq`** | **built** |
| 14 | time-reflection invariance and two-sided uniqueness | `timeReflect`, `dirDeriv_comp_timeReflect`, `solvesWaveEq_comp_timeReflect`, **`eq_of_solvesWaveEq_of_data_eq_all`** | **built** |
| 15 | the estimate on both sides, and continuous dependence | `energyDensity_comp_timeReflect`, `waveEnergy_comp_timeReflect`, **`waveEnergy_le_exp_abs`**, **`waveEnergy_sub_le_exp_abs`** | **built** |
| 16 | the solutions of a fixed equation form a vector space | `dirDeriv_const_smul`, **`solvesWaveEq_add`**, **`solvesWaveEq_const_smul`**, `solvesWaveEq_zero` | **built** |
| 17 | the coordinate dictionary between time-space and event coordinates | `eventCLM`, `eventCLM_timeDir`, `eventCLM_spaceDir`, `waveDirDeriv_timeDir_two_comp_eventCLM`, `waveDirDeriv_spaceDir_two_comp_eventCLM` | **built** |
| 18 | the bridge to the corpus's clock operator | **`kgWaveOp_eq_of_contDiff`**, **`solvesWaveEq_comp_eventCLM`** | **built** |
| 19 | the converse and the equivalence of the two formulations | `eventCLM_surjective`, `solvesPotentialWaveAt_of_solvesWaveEq`, **`solvesWaveEq_comp_eventCLM_iff`** | **built** |
| 20 | uniqueness in the corpus's own language | `tail_eventCLM`, **`eq_of_solvesPotentialWave_of_data_eq`** | **built** |
| 21 | the Green identity without compact support | `integral_mul_coordPartial_of_integrable`, **`integral_laplacian_mul_of_integrable`** | **built** |
| 22 | the flux identity without compact support | **`integral_dirDeriv_energyDensity_of_integrable`** | **built** |
| 23 | differentiating the energy without compact support | **`hasDerivAt_waveEnergy_of_dominated`** | **built** |
| 24 | the estimate for a decaying solution | `DecayingSolution`, `abs_integral_flux_le_of_integrable`, **`waveEnergy_le_exp_of_decaying`** | **built** |
| 25 | vanishing for a decaying solution | `energyDensity_eq_zero_of_waveEnergy_eq_zero_of_integrable`, **`eq_zero_of_waveEnergy_zero_of_decaying`** | **built** |
| 26 | the hypothesis class is inhabited: compact support implies it | `hasCompactSupport_slice_dirDeriv`, **`decayingSolution_of_hasCompactSupport`** | **built** |
| 27 | time reflection and the two-sided estimate for decaying solutions | `coordPartial_neg_fun`, `slice_dirDeriv_comp_timeReflect`, **`DecayingSolution.comp_timeReflect`**, **`waveEnergy_le_exp_abs_of_decaying`** | **built** |
| 28 | two-sided vanishing for decaying solutions | **`eq_zero_of_waveEnergy_zero_of_decaying_all`** | **built** |
| 29 | the decaying uniqueness in the corpus's own language | **`eq_zero_of_solvesPotentialWave_of_decaying`** | **built** |
| 30 | the decay hypothesis is a genuine restriction | `solvesWaveEq_one_field`, `not_integrable_energyDensity_one_field`, **`not_decayingSolution_one_field`** | **built** |

Modules: `WaveEnergyGreenIdentity.lean` (1–3), `WaveDirectionalCalculus.lean` (4–5),
`WaveEnergyFlux.lean` (6–9), `WaveEnergyDerivative.lean` (10–12), `WaveCauchyUniqueness.lean` (13), `WaveTimeReflection.lean` (14), `WaveEnergyTwoSided.lean` (15), `WaveSolutionSpace.lean` (16), `WaveEventCoordinates.lean` (17), `WaveOperatorBridge.lean` (18–19), `WaveUniquenessEventForm.lean` (20), `WaveGreenIdentityIntegrable.lean` (21), `WaveEnergyFluxIntegrable.lean` (22), `WaveEnergyDerivativeIntegrable.lean` (23), `WaveEnergyDecaying.lean` (24–25), `WaveDecayingCompactSupport.lean` (26), `WaveDecayingReflection.lean` (27–28), `WaveDecayingEventForm.lean` (29), `WaveDecayingSharp.lean` (30). All wired into the umbrella; axioms
`[propext, Classical.choice, Quot.sound]`.

## State of the build

Statements 1–9 are complete, and 9 is the mathematical heart:

`∫ ∂ₜ(energy density) = 2 ∫ (V+1)·u·∂ₜu`

for a smooth field with spatial support in a fixed compact set solving `∂ₜ²u = Δu + Vu`. The two
derivative terms cancel exactly — the equation turns `∂ₜu·∂ₜ²u` into `∂ₜu·(Δu+Vu)`, `dirDeriv_comm`
turns `∑ᵢ∂ᵢu·∂ₜ∂ᵢu` into `∑ᵢ∂ᵢu·∂ᵢ∂ₜu`, and `integral_laplacian_mul` identifies the latter with
`-∫Δu·∂ₜu`. No derivative of `u` survives on the right, which is exactly what makes the estimate
closed.

Statement 10 is also complete: `hasDerivAt_waveEnergy` differentiates the energy under the integral
sign, the domination being `Set.indicator K (fun _ => C)` with `C` the supremum of the continuous
time derivative of the energy density on the compact `Icc (t-1) (t+1) ×ˢ K`.

Statements 11 and 12 close it. The flux is dominated by the energy,
`|2∫(V+1)·u·∂ₜu| ≤ (M+1)·E(t)` whenever `|V| ≤ M` — pointwise from `2|ab| ≤ a²+b²` and the fact that
the energy density dominates `u² + (∂ₜu)²` — so Grönwall gives

**`waveEnergy_le_exp`**: `E(t) ≤ E(0)·exp((M+1)·t)` for `t ≥ 0`,

and hence **`eq_zero_of_waveEnergy_zero`**: a solution whose energy vanishes at time `0` vanishes at
every later time. A nonnegative continuous integrand with vanishing integral is identically zero
(`Continuous.ae_eq_iff_eq` on a measure of full support), and the energy density dominates `u²`.

Statement 13 puts it in the form an inverse problem uses. The equation is linear
(`solvesWaveEq_sub`), a field vanishing on a slice together with its time derivative has zero energy
there (`waveEnergy_eq_zero_of_slice_zero`), and hence **`eq_of_solvesWaveEq_of_data_eq`**: *two
classical solutions with spatially compact support, the same bounded potential and the same Cauchy
data agree at every later time.*

Statement 14 removes the sign restriction. Only the *second* time derivative enters the equation, so
reflecting an event across the initial slice carries a solution of `V` to a solution of the
reflected potential (`solvesWaveEq_comp_timeReflect`), and uniqueness for `t ≥ 0` gives
**`eq_of_solvesWaveEq_of_data_eq_all`**: the two solutions agree at *every* time.

Statement 15 closes the layer symmetrically. The energy density is even in the time derivative, so
reflection turns the forward estimate into `E(t) ≤ E(0)·exp((M+1)|t|)`
(**`waveEnergy_le_exp_abs`**), and applying that to the difference of two solutions gives
**`waveEnergy_sub_le_exp_abs`**: *the energy of the difference at any time is controlled by the
energy of the difference of the Cauchy data.* That is continuous dependence — uniqueness in
quantitative form.

Statement 16 records what superposition arguments consume: the solutions of a fixed clock equation
are closed under sums, scalar multiples and differences, with the zero field a solution.

This is the uniqueness half of the classical local theory, in exactly the class the clock programme
uses: real classical solutions with spatially compact support. What it does *not* give is existence;
that is the Galerkin or Sobolev-scale half, and it is what would lower the regularity threshold of
`finite-regularity-clock-probes` below `C^{2d+5}`.

### The bridge, built

Statements 17 and 18 close it. `kgWaveOp_eq_of_contDiff` expands the corpus operator as
`-∂₀∂₀u + ∑ᵢ∂ᵢ₊₁∂ᵢ₊₁u` for a smooth field, and `solvesWaveEq_comp_eventCLM` turns a solution of the
corpus's `SolvesPotentialWaveAt (kgWaveOp d) V u` into a solution of `SolvesWaveEq` in time-space
coordinates. So every probe the corpus constructs by Fourier synthesis — including the
finite-regularity ones — inherits the energy estimate, the two-sided estimate, uniqueness and
continuous dependence, provided it has spatially compact support.

Statement 19 makes the bridge an equivalence. Every event is `eventCLM d (y 0, Fin.tail y)`
(`Fin.cons_self_tail`), so the converse holds too and **`solvesWaveEq_comp_eventCLM_iff`** records
that the two formulations of the clock equation are the same statement. Results proved in either
language now transfer both ways.

Statement 20 states the capstone in the corpus's own language:
**`eq_of_solvesPotentialWave_of_data_eq`** — *two smooth fields with spatially compact support, both
solving `SolvesPotentialWaveAt (kgWaveOp d) V`, with `V` continuous and bounded, and agreeing on the
initial slice together with their time derivatives there, agree at every event.* No time-space
coordinates appear in the statement; the bridge is used only inside the proof.

### The compact-support hypothesis, and how far it can go

There is an honest limitation to record. The estimate assumes the field has spatially compact
support, which is what a cut-off potential supplies but **not** what a Fourier synthesis supplies:
the corpus's constructed probes decay, they do not vanish outside a compact set. The bridge
transports the *equation* to them, but the estimate itself does not yet apply.

Compact support is used in exactly two places, and statement 21 removes the first: mathlib's
integration by parts asks only that the three relevant products be integrable, so
**`integral_laplacian_mul_of_integrable`** proves the Green identity for integrable data with the
differentiability supplied by smoothness alone. Statement 22 carries that through the whole cancellation:
**`integral_dirDeriv_energyDensity_of_integrable`** proves `∫∂ₜ(energy density) = 2∫(V+1)·u·∂ₜu`
from four families of integrability hypotheses — the three the Green identity consumes and one for
the zeroth-order term — with no support hypothesis anywhere.

Statement 23 removes the second and last use: **`hasDerivAt_waveEnergy_of_dominated`** differentiates
the energy under the integral sign given an integrable dominating function on a time interval and
integrability of the energy density on the slice — no support hypothesis. For a compactly supported
field the dominating function is manufactured from the supremum on a compact set (statement 10); for
a decaying field it is supplied.

So every step of the layer — Green identity, flux identity, differentiation of the energy — runs on
integrability and domination alone, and statement 24 assembles them. The structure
`DecayingSolution` collects exactly what replaces compact support: smoothness, the equation,
integrability of the energy density and of the three Green products and the zeroth-order term on
every slice, and a local dominating function in time. With it,

**`waveEnergy_le_exp_of_decaying`**: `E(t) ≤ E(0)·exp((M+1)t)` for `t ≥ 0`, for a **decaying**
solution — no compact support anywhere.

Statement 25 carries the uniqueness half across as well:
**`eq_zero_of_waveEnergy_zero_of_decaying`** — a decaying solution whose energy vanishes at one time
vanishes at every later time.

That is the form the corpus's Fourier-built probes can meet: they decay rather than vanish outside a
compact set, and each field of `DecayingSolution` is an integrability statement about a synthesis
integral. Discharging those fields for a concrete constructed probe is the remaining bookkeeping.

Statement 26 settles the non-vacuity question that any new hypothesis class has to answer.
**`decayingSolution_of_hasCompactSupport`**: every smooth solution with spatially compact support
satisfies all seven conditions of `DecayingSolution` — each integrand is continuous with compact
support, and the dominating function is the supremum on the compact box `Icc (t-1) (t+1) ×ˢ K`,
supported on `K`. So the decaying layer **subsumes** the compactly supported one rather than
trading it for an empty class, and everything proved in statements 1–20 is a special case of
24–25.

Statement 27 makes the decaying layer symmetric. Reversing time carries a decaying solution to a
decaying solution of the reflected potential — every integrand of the seven-field bundle changes at
most by a sign, and the energy density not at all — so **`waveEnergy_le_exp_abs_of_decaying`** gives
`E(t) ≤ E(0)·exp((M+1)|t|)` on both sides of the initial slice, and statement 28
**`eq_zero_of_waveEnergy_zero_of_decaying_all`** — a decaying solution with vanishing initial energy
vanishes at *every* time, not only later ones.

With that the decaying layer has the same four theorems as the compactly supported one — estimate,
vanishing, two-sidedness, and (statement 26) the inclusion of one class in the other — with compact
support nowhere in the hypotheses.

Statement 29 states it in the corpus's own language, which is the point of the whole arc:
**`eq_zero_of_solvesPotentialWave_of_decaying`** — *a smooth field on events whose pullback to
time-space coordinates satisfies the decay conditions, and whose value and time derivative vanish on
the initial slice, vanishes at every event.* The hypotheses and the conclusion are stated on
`Fin (d+1) → ℝ` with `coordPartial 0` and `Fin.cons 0 x`; the bridge, the reflection and the whole
energy machinery live inside the proof.

### A caveat that has to be stated plainly

Statement 30 bounds the reach of the whole layer from the other side. The constant field `1` solves
the free clock equation, and its energy density is the constant `1`, which is not integrable over a
space of positive dimension — so **`not_decayingSolution_one_field`**: solving the equation does not
imply the decay hypotheses. Finiteness of the energy is an assumption about the solution.

This matters for the corpus's own probes. A Fourier synthesis against an `L¹` density produces a
*bounded* continuous field, and boundedness is not decay: the constant field is exactly such a
synthesis. So the earlier claim that the estimate "applies to the corpus's Fourier-built probes"
should be read as conditional — it applies to those probes **once their energy and Green products
are shown integrable**, which is an extra `L²`-type statement about the density and not a corollary
of the construction. Statement 26 gives one sufficient condition (compact support); a Plancherel
argument on the synthesis would give another.

One structural note for whoever continues: `DecayingSolution` is **not** closed under differences —
each of its integrability fields is a product of a derivative of the field with a derivative of its
time derivative, so the difference of two solutions produces cross terms that the hypotheses for the
two solutions separately do not cover. The two-solution uniqueness statement therefore has to assume
`DecayingSolution` *of the difference*, exactly as statement 25 is phrased. That is not a defect of
the formalisation: it is the honest content of the estimate for non-compactly-supported data.

### Historical note on the plan

The step was originally recorded as: identifying
`SolvesWaveEq u V` on `ℝ × (Fin d → ℝ)` with the corpus's `SolvesPotentialWaveAt (kgWaveOp d) V u`
on `Fin (d+1) → ℝ`. It needs two translations — the index shift `Fin (d+1) ↔ ℝ × Fin d`
(`kgEventInvCLM`, `kgSpatial`) and the change of norm between `Fin d → ℝ` and
`EuclideanSpace ℝ (Fin d)` (the two carry the same volume, `EuclideanSpace.volume_preserving_measurableEquiv`).
With it, every probe the corpus constructs by Fourier synthesis inherits the uniqueness and
stability statements above.

The expansion of the corpus operator is already available and is the entry point:
`kgWaveOp d = (SmoothPseudoMetric.ofSignature (kgEps d) (kgEps_ne_zero d)).chart.dalembert`, and
`SmoothPseudoMetric.ofSignature_dalembert_of_differentiableAt` rewrites it as
`∑ᵢ (kgEps d i)⁻¹ · ∂ᵢ∂ᵢu` under a differentiability hypothesis. With `kgEps d 0 = -1` and
`kgEps d i.succ = 1`, splitting that sum by `Fin.sum_univ_succ` gives exactly the shape of
`SolvesWaveEq`; what is left is the coordinate dictionary `coordPartial 0 ↔ dirDeriv (timeDir d)`
and `coordPartial i.succ ↔ dirDeriv (spaceDir d i)` along the linear map
`(t, x) ↦ Fin.cons t x`.

## Log
- 2026-08-04 — statement 30 (the decay hypothesis is not implied by solving the equation); the
  claim that the estimate reaches the corpus's Fourier probes is corrected to a conditional one.
- 2026-08-04 — statement 29 (decaying uniqueness in event coordinates) formalized.
- 2026-08-04 — statement 28 (two-sided vanishing for decaying solutions) formalized; the decaying
  layer now mirrors the compactly supported one completely.
- 2026-08-04 — statement 27 (reflection of a decaying solution, two-sided estimate) formalized.
- 2026-08-04 — statement 26 (compact support implies the decaying hypotheses) formalized; the class
  is inhabited and the new layer subsumes the old.
- 2026-08-04 — statement 25 (vanishing for decaying solutions) formalized.
- 2026-08-04 — statement 24 (Grönwall estimate for decaying solutions) formalized; the layer no
  longer needs compact support at any step.
- 2026-08-04 — statement 23 (dominated differentiation of the energy) formalized; compact support is
  no longer used anywhere in the layer's analytic core.
- 2026-08-04 — statement 22 (flux identity for integrable data) formalized; only the dominating
  function for differentiation under the integral still uses compact support.
- 2026-08-04 — statement 21 (Green identity for integrable data) formalized; the first of the two
  compact-support uses is removed.
- 2026-08-04 — statement 20 (uniqueness in event coordinates) formalized.
- 2026-08-04 — statement 19 (converse bridge, equivalence of the two formulations) formalized.
- 2026-08-04 — statements 17–18 (coordinate dictionary and operator bridge) formalized.
- 2026-08-04 — statement 16 (linearity of the solution space) formalized.
- 2026-08-04 — statement 15 (two-sided estimate, continuous dependence) formalized.
- 2026-08-04 — statement 14 (time reflection, two-sided uniqueness) formalized.
- 2026-08-04 — statement 13 (linearity and Cauchy uniqueness) formalized.
- 2026-08-04 — statements 11–12 formalized; the card is complete and moves to 3-formalized.
- 2026-08-04 — statement 10 (differentiation under the integral) formalized; 11–12 remain.
- 2026-08-04 — statement 9 (the flux identity) formalized; 10–12 remain.
- 2026-08-04 — statements 1–8 formalized in three modules (Green identity, directional calculus,
  pointwise flux expansion); 9–12 remain.
- 2026-08-04 — created in 1-in-progress; mathlib inputs verified present
  (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`, `norm_le_gronwallBound_of_norm_deriv_right_le`).
