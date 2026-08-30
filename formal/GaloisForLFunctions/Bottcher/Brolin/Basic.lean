/-
# Böttcher tower — Brolin: interfaces and Green-height confinement

This module is part of the split Brolin/Riesz-measure interface. Import
`GaloisForLFunctions.Bottcher.Brolin` for the full public surface.
-/
import GaloisForLFunctions.Bottcher.Capacity
import GaloisForLFunctions.Bottcher.GreenContinuity
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.Data.Multiset.Fintype
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Measure.AEMeasurable
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance basicLocalInst1 : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

/-- Distributional Riesz-measure condition.

`IsRieszMeasureOf μ u` means `μ = (2π)⁻¹ Δu`: testing against a compactly
supported continuous function `φ`, the measure integral is the distributional
Laplacian action of `u` on `φ`.
-/
def IsRieszMeasureOf (μ : Measure ℂ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    ∫ z, φ z ∂μ = (2 * Real.pi)⁻¹ * ∫ z, u z * (Δ (φ : ℂ → ℝ)) z

/-- The positive functional whose Riesz-Markov measure is `(2π)⁻¹Δu`. -/
def IsRieszFunctional (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) (u : ℂ → ℝ) : Prop :=
  ∀ φ : C_c(ℂ, ℝ),
    Λ φ = (2 * Real.pi)⁻¹ * ∫ z, u z * (Δ (φ : ℂ → ℝ)) z

/-- The Riesz-Markov measure represented by a positive compact-support functional. -/
noncomputable def rieszMeasureOfFunctional (Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ) : Measure ℂ :=
  RealRMK.rieszMeasure Λ

/-- If a positive functional is the distributional Laplacian of `u`, its
Riesz-Markov measure is the Riesz measure of `u`. -/
theorem isRieszMeasureOf_rieszMeasureOfFunctional
    {Λ : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ} {u : ℂ → ℝ}
    (hΛ : IsRieszFunctional Λ u) :
    IsRieszMeasureOf (rieszMeasureOfFunctional Λ) u := by
  intro φ
  rw [rieszMeasureOfFunctional, RealRMK.integral_rieszMeasure, hΛ φ]

/-- A Riesz measure for `u`, constructed as a genuine Riesz-Markov measure of a
positive compact-support functional. -/
structure RieszMeasure (u : ℂ → ℝ) where
  functional : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ
  isFunctional : IsRieszFunctional functional u

namespace RieszMeasure

/-- The underlying Riesz-Markov measure. -/
noncomputable def measure (R : RieszMeasure u) : Measure ℂ :=
  rieszMeasureOfFunctional R.functional

theorem isRieszMeasure (R : RieszMeasure u) :
    IsRieszMeasureOf R.measure u :=
  isRieszMeasureOf_rieszMeasureOfFunctional R.isFunctional

end RieszMeasure

/-- The dynamical Green function is represented by the logarithmic potential of
`μ` with Robin constant zero: `G_c(z) = -U^μ(z)`.

For monic quadratic polynomials the Robin constant is zero (`cap K_c = 1`), so
this is the potential representation used in the Brolin step.
-/
def HasGreenPotentialRepresentation (c : ℂ) (μ : Measure ℂ) : Prop :=
  ∀ z : ℂ, greenFunctionDyn c z = greenFunction μ 0 z

/-- Expanded form of the zero-Robin potential representation. -/
theorem hasGreenPotentialRepresentation_iff (c : ℂ) (μ : Measure ℂ) :
    HasGreenPotentialRepresentation c μ ↔
      ∀ z : ℂ, greenFunctionDyn c z = - logPotential μ z := by
  constructor
  · intro h z
    simpa [HasGreenPotentialRepresentation, greenFunction] using h z
  · intro h z
    simpa [HasGreenPotentialRepresentation, greenFunction] using h z

/-- `μ` is the Brolin/Riesz measure of the quadratic Green function `G_c`. -/
def IsBrolinMeasure (c : ℂ) (μ : Measure ℂ) : Prop :=
  IsProbOn μ (filledJulia c) ∧
    IsRieszMeasureOf μ (greenFunctionDyn c) ∧
    HasGreenPotentialRepresentation c μ

/-- A packaged Brolin measure for `f_c(z)=z²+c`. -/
structure BrolinMeasure (c : ℂ) where
  riesz : RieszMeasure (greenFunctionDyn c)
  isProbOn : IsProbOn riesz.measure (filledJulia c)
  potential : HasGreenPotentialRepresentation c riesz.measure

namespace BrolinMeasure

/-- The underlying measure, named for downstream code as `μ_c`. -/
noncomputable def μ (M : BrolinMeasure c) : Measure ℂ := M.riesz.measure

theorem isBrolinMeasure (M : BrolinMeasure c) : IsBrolinMeasure c M.μ :=
  ⟨M.isProbOn, M.riesz.isRieszMeasure, M.potential⟩

theorem probOn (M : BrolinMeasure c) : IsProbOn M.μ (filledJulia c) :=
  M.isProbOn

theorem isRieszMeasure (M : BrolinMeasure c) :
    IsRieszMeasureOf M.μ (greenFunctionDyn c) :=
  M.riesz.isRieszMeasure

/-- **Potential representation.** The packaged Brolin measure satisfies
`G_c(z) = -U^{μ_c}(z)`. -/
theorem potentialRepresentation (M : BrolinMeasure c) (z : ℂ) :
    greenFunctionDyn c z = - logPotential M.μ z :=
  (hasGreenPotentialRepresentation_iff c M.μ).mp M.potential z

/-- Equivalent Green-function notation for the same potential representation. -/
theorem greenFunctionRepresentation (M : BrolinMeasure c) (z : ℂ) :
    greenFunctionDyn c z = greenFunction M.μ 0 z :=
  M.potential z

end BrolinMeasure

/-- Direct projection from the predicate form. -/
theorem potentialRepresentation_of_isBrolinMeasure {c : ℂ} {μ : Measure ℂ}
    (hμ : IsBrolinMeasure c μ) (z : ℂ) :
    greenFunctionDyn c z = - logPotential μ z :=
  (hasGreenPotentialRepresentation_iff c μ).mp hμ.2.2 z

/-- Direct projection of the Riesz condition from the predicate form. -/
theorem isRieszMeasureOf_greenFunctionDyn_of_isBrolinMeasure {c : ℂ} {μ : Measure ℂ}
    (hμ : IsBrolinMeasure c μ) :
    IsRieszMeasureOf μ (greenFunctionDyn c) :=
  hμ.2.1

/-! ## Green-height confinement for pullback atoms -/

/-- The dynamical Green function satisfies the global quadratic scaling law,
including points of the filled Julia set where both sides are zero. -/
theorem greenFunctionDyn_quadratic (c z : ℂ) :
    greenFunctionDyn c (quadratic c z) = 2 * greenFunctionDyn c z := by
  by_cases hz : z ∈ filledJulia c
  · have hfz : quadratic c z ∈ filledJulia c :=
      (mem_filledJulia_iff_quadratic_mem c z).mp hz
    rw [greenFunctionDyn, if_pos hfz, greenFunctionDyn, if_pos hz, mul_zero]
  · have hfz : quadratic c z ∉ filledJulia c :=
      fun hfz => hz ((mem_filledJulia_iff_quadratic_mem c z).mpr hfz)
    rw [greenFunctionDyn, if_neg hfz, greenFunctionDyn, if_neg hz,
      greenLimit_quadratic_basin hz]

/-- Iterated Green-function scaling: `G_c(f_c^[n] z)=2^n G_c(z)` on all of
`ℂ`. -/
theorem greenFunctionDyn_iterate (c z : ℂ) (n : ℕ) :
    greenFunctionDyn c ((quadratic c)^[n] z) =
      (2 ^ n : ℝ) * greenFunctionDyn c z := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', greenFunctionDyn_quadratic, ih, pow_succ]
      ring

/-- Antipodal points have the same forward-orbit norms under `z ↦ z^2 + c`. -/
theorem quadratic_iterate_norm_neg (c z : ℂ) (n : ℕ) :
    ‖(quadratic c)^[n] (-z)‖ = ‖(quadratic c)^[n] z‖ := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp [quadratic]

/-- The filled Julia set is invariant under the antipodal map. -/
theorem mem_filledJulia_neg_iff (c z : ℂ) :
    -z ∈ filledJulia c ↔ z ∈ filledJulia c := by
  constructor
  · intro hz
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz ⊢
    rcases hz with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro w ⟨n, rfl⟩
    have h := hB ((quadratic c)^[n] (-z)) ⟨n, rfl⟩
    simpa [quadratic_iterate_norm_neg c z n] using h
  · intro hz
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz ⊢
    rcases hz with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    rintro w ⟨n, rfl⟩
    have h := hB ((quadratic c)^[n] z) ⟨n, rfl⟩
    simpa [quadratic_iterate_norm_neg c z n] using h

/-- Every point of the filled Julia set has a filled-Julia preimage under
`f_c(z)=z²+c`. -/
theorem exists_mem_filledJulia_quadratic_eq
    {c y : ℂ} (hy : y ∈ filledJulia c) :
    ∃ z : ℂ, z ∈ filledJulia c ∧ quadratic c z = y := by
  obtain ⟨z, hz⟩ :=
    IsAlgClosed.exists_pow_nat_eq (k := ℂ) (y - c) (by norm_num : 0 < 2)
  have hq : quadratic c z = y := by
    rw [quadratic_apply, hz]
    ring_nf
  refine ⟨z, ?_, hq⟩
  · apply (mem_filledJulia_iff_quadratic_mem c z).mpr
    rwa [hq]

/-- The finite Green approximants are antipodally even. -/
theorem greenApprox_neg_eq (c z : ℂ) (n : ℕ) :
    greenApprox c (-z) n = greenApprox c z n := by
  unfold greenApprox
  rw [quadratic_iterate_norm_neg]

/-- Green sublevel sets, used to express that finite pullback atoms collapse
toward `K_c = {G_c=0}`. -/
def greenSublevel (c : ℂ) (t : ℝ) : Set ℂ :=
  {z | greenFunctionDyn c z ≤ t}

theorem mem_greenSublevel_iff (c z : ℂ) (t : ℝ) :
    z ∈ greenSublevel c t ↔ greenFunctionDyn c z ≤ t := Iff.rfl

/-- Green sublevels are monotone in the level. -/
theorem greenSublevel_mono (c : ℂ) {s t : ℝ} (hst : s ≤ t) :
    greenSublevel c s ⊆ greenSublevel c t := by
  intro z hz
  exact le_trans hz hst

/-- Green sublevels are closed because `G_c` is continuous. -/
theorem isClosed_greenSublevel (c : ℂ) (t : ℝ) : IsClosed (greenSublevel c t) := by
  exact isClosed_le (continuous_greenFunctionDyn c) continuous_const

/-- The Green escape rate tends to `+∞` at spatial infinity. -/
theorem tendsto_greenLimit_atTop (c : ℂ) :
    Tendsto (fun z : ℂ => greenLimit c z) (Bornology.cobounded ℂ) atTop := by
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ) atTop :=
    tendsto_norm_cobounded_atTop
  have hlog : Tendsto (fun z : ℂ => Real.log ‖z‖) (Bornology.cobounded ℂ) atTop :=
    Real.tendsto_log_atTop.comp hnorm
  have hdiff : Tendsto (fun z : ℂ => greenLimit c z - Real.log ‖z‖)
      (Bornology.cobounded ℂ) (𝓝 0) := tendsto_greenLimit_sub_log c
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hdiff.add_atTop hlog

/-- The dynamical Green function tends to `+∞` at spatial infinity. This is the boundedness
input behind compact Green sublevels. -/
theorem tendsto_greenFunctionDyn_atTop (c : ℂ) :
    Tendsto (greenFunctionDyn c) (Bornology.cobounded ℂ) atTop := by
  refine (tendsto_greenLimit_atTop c).congr' ?_
  have hnorm : Tendsto (fun z : ℂ => ‖z‖) (Bornology.cobounded ℂ) atTop :=
    tendsto_norm_cobounded_atTop
  filter_upwards [hnorm.eventually_gt_atTop (max 2 ‖c‖)] with z hz
  have h2 : 2 < ‖z‖ := lt_of_le_of_lt (le_max_left _ _) hz
  have hc : ‖c‖ ≤ ‖z‖ := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz)
  have hzK : z ∉ filledJulia c := not_mem_filledJulia hc h2
  rw [greenFunctionDyn, if_neg hzK]

/-- Green sublevels are bounded because `G_c(z) → +∞` at infinity. -/
theorem isBounded_greenSublevel (c : ℂ) (t : ℝ) :
    Bornology.IsBounded (greenSublevel c t) := by
  rw [Bornology.isBounded_def]
  have hgt : {z : ℂ | t < greenFunctionDyn c z} ∈ Bornology.cobounded ℂ :=
    (tendsto_greenFunctionDyn_atTop c).eventually_gt_atTop t
  convert hgt using 1
  ext z
  simp [greenSublevel, not_le]

/-- Green sublevels are compact: closed by continuity and bounded by the escape-rate asymptotic. -/
theorem isCompact_greenSublevel (c : ℂ) (t : ℝ) : IsCompact (greenSublevel c t) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_greenSublevel c t) (isBounded_greenSublevel c t)

/-- Closed Green bands `{z | a ≤ G_c z ≤ b}`. These are the compact sets used in the
properness step for the global Böttcher branch. -/
def greenBand (c : ℂ) (a b : ℝ) : Set ℂ :=
  {z | a ≤ greenFunctionDyn c z ∧ greenFunctionDyn c z ≤ b}

theorem mem_greenBand_iff (c z : ℂ) (a b : ℝ) :
    z ∈ greenBand c a b ↔ a ≤ greenFunctionDyn c z ∧ greenFunctionDyn c z ≤ b := Iff.rfl

theorem greenBand_subset_greenSublevel (c : ℂ) (a b : ℝ) :
    greenBand c a b ⊆ greenSublevel c b := fun _ hz => hz.2

theorem isClosed_greenBand (c : ℂ) (a b : ℝ) : IsClosed (greenBand c a b) :=
  (isClosed_le continuous_const (continuous_greenFunctionDyn c)).inter
    (isClosed_le (continuous_greenFunctionDyn c) continuous_const)

/-- Green bands are compact. This formalizes the proof's compactness claim
`{a ≤ G_c ≤ b}` in the properness argument. -/
theorem isCompact_greenBand (c : ℂ) (a b : ℝ) : IsCompact (greenBand c a b) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_greenBand c a b)
    ((isBounded_greenSublevel c b).subset (greenBand_subset_greenSublevel c a b))

theorem measurableSet_greenSublevel (c : ℂ) (t : ℝ) :
    MeasurableSet (greenSublevel c t) :=
  (isClosed_greenSublevel c t).measurableSet

/-- The zero Green sublevel is exactly the filled Julia set. -/
theorem greenSublevel_zero_eq_filledJulia (c : ℂ) :
    greenSublevel c 0 = filledJulia c := by
  ext z
  constructor
  · intro hz
    have hnonneg : 0 ≤ greenFunctionDyn c z := greenFunctionDyn_nonneg c z
    exact (greenFunctionDyn_eq_zero_iff c z).mp (le_antisymm hz hnonneg)
  · intro hz
    rw [mem_greenSublevel_iff, (greenFunctionDyn_eq_zero_iff c z).mpr hz]

end Bottcher
