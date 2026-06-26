/-
# Böttcher tower — Brolin / Riesz-measure interface

This file names the missing potential-theoretic object for the quadratic Green
function.  Mathlib has distributional Laplacians and the Riesz-Markov theorem,
but it does not yet provide the planar Riesz decomposition theorem for
subharmonic functions, so the existence theorem for `μ_c` is kept as a compact
checked interface:

* `IsRieszMeasureOf μ u` says `μ = (2π)⁻¹ Δu` in distributional form.
* `HasGreenPotentialRepresentation c μ` says `G_c = -U^μ`, equivalently
  `G_c = greenFunction μ 0`.
* `BrolinMeasure c` packages the probability/support/Riesz/potential data.
* `unitCircleMeasure` is the concrete `c = 0` harmonic/equilibrium measure model.

The remaining work for arbitrary `c` is the actual Riesz-decomposition
existence proof producing a `BrolinMeasure c`.
-/
import GaloisForLFunctions.Bottcher.Capacity
import GaloisForLFunctions.Bottcher.GreenContinuity
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Polynomial.MahlerMeasure
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

open Filter Topology MeasureTheory CompactlySupported Laplacian
open scoped Laplacian

namespace Bottcher

local instance instTwoPiPos : Fact (0 < 2 * Real.pi) := ⟨Real.two_pi_pos⟩

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

/-! ## Unit-circle model kernel

The `c = 0` model has `K_0` equal to the closed unit disk and the equilibrium
measure on the boundary circle.  The following lemma records the logarithmic
kernel computation behind that model in `circleAverage` form.  It is the local
calculus brick used by the general Brolin representation after pulling the
exterior by the Böttcher coordinate.
-/

/-- The normalized Haar measure on the unit circle, pushed to `ℂ`.

This is the concrete equilibrium/harmonic measure for the model `K_0 = closedBall 0 1`.
-/
noncomputable def unitCircleMeasure : Measure ℂ :=
  Measure.map (fun θ : AddCircle (2 * Real.pi) => (AddCircle.toCircle θ : ℂ))
    AddCircle.haarAddCircle

/-- Integrating against the pushed-forward normalized circle Haar measure is
the same as `Real.circleAverage` on the unit circle. -/
theorem integral_unitCircleMeasure_eq_circleAverage (f : ℂ → ℝ)
    (hf : AEStronglyMeasurable f unitCircleMeasure) :
    ∫ z, f z ∂unitCircleMeasure = Real.circleAverage f 0 1 := by
  rw [unitCircleMeasure, integral_map]
  · rw [AddCircle.integral_haarAddCircle]
    rw [← AddCircle.intervalIntegral_preimage (2 * Real.pi) 0]
    simp [Real.circleAverage, AddCircle.toCircle_apply_mk, circleMap]
  · exact (AddCircle.continuous_toCircle.subtype_val).aemeasurable
  · simpa [unitCircleMeasure] using hf

/-- For `c = 0`, the `n`th iterate is `z ↦ z^(2^n)`. -/
theorem quadratic_zero_iterate (z : ℂ) (n : ℕ) :
    (quadratic 0)^[n] z = z ^ (2 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih, quadratic_apply]
      norm_num
      rw [← pow_mul]
      rw [pow_succ]

/-- The model filled Julia set is the closed unit disk. -/
theorem mem_filledJulia_zero_iff_norm_le_one (z : ℂ) :
    z ∈ filledJulia 0 ↔ ‖z‖ ≤ 1 := by
  constructor
  · intro hz
    by_contra hle
    push Not at hle
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le] at hz
    rcases hz with ⟨B, hB⟩
    have hBz : ∀ n : ℕ, ‖z‖ ^ (2 ^ n) ≤ B := by
      intro n
      have hmem : z ^ (2 ^ n) ∈ Set.range fun n : ℕ => (quadratic 0)^[n] z :=
        ⟨n, quadratic_zero_iterate z n⟩
      simpa [norm_pow] using hB _ hmem
    have htend : Tendsto (fun n : ℕ => ‖z‖ ^ (2 ^ n)) atTop atTop := by
      exact (tendsto_pow_atTop_atTop_of_one_lt hle).comp
        (tendsto_pow_atTop_atTop_of_one_lt (show 1 < (2 : ℕ) by norm_num))
    rcases (eventually_atTop.1 (htend.eventually_gt_atTop B)) with ⟨N, hN⟩
    exact not_le_of_gt (hN N le_rfl) (hBz N)
  · intro hz
    rw [mem_filledJulia_iff, isBounded_iff_forall_norm_le]
    refine ⟨1, fun w hw => ?_⟩
    rcases hw with ⟨n, rfl⟩
    have hpow := quadratic_zero_iterate z n
    have hle : ‖z‖ ^ (2 ^ n) ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
    simpa [hpow, norm_pow] using hle

instance instIsProbabilityMeasure_unitCircleMeasure :
    IsProbabilityMeasure unitCircleMeasure := by
  unfold unitCircleMeasure
  exact Measure.isProbabilityMeasure_map (AddCircle.continuous_toCircle.subtype_val).aemeasurable

/-- The unit-circle model measure is carried by `K_0`. -/
theorem unitCircleMeasure_filledJulia_zero_compl :
    unitCircleMeasure (filledJulia 0)ᶜ = 0 := by
  rw [unitCircleMeasure, Measure.map_apply]
  · suffices (fun θ : AddCircle (2 * Real.pi) => (AddCircle.toCircle θ : ℂ)) ⁻¹'
        (filledJulia 0)ᶜ = ∅ by
      simp [this]
    ext θ
    simp [mem_filledJulia_zero_iff_norm_le_one]
  · exact (AddCircle.continuous_toCircle.subtype_val).measurable
  · exact (isClosed_filledJulia 0).measurableSet.compl

/-- The concrete unit-circle measure is a probability carried by the model filled Julia set. -/
theorem isProbOn_unitCircleMeasure_filledJulia_zero :
    IsProbOn unitCircleMeasure (filledJulia 0) :=
  ⟨inferInstance, unitCircleMeasure_filledJulia_zero_compl⟩

/-- The model Green approximants are constant and equal to `log ‖z‖`. -/
theorem greenApprox_zero_eq_log_norm (z : ℂ) (n : ℕ) :
    greenApprox 0 z n = Real.log ‖z‖ := by
  unfold greenApprox
  rw [quadratic_zero_iterate z n, norm_pow, Real.log_pow]
  have hpow : (2 ^ n : ℝ) ≠ 0 := by positivity
  field_simp [hpow]
  norm_num

/-- The model escape-rate limit is `log ‖z‖`. -/
theorem greenLimit_zero_eq_log_norm (z : ℂ) :
    greenLimit 0 z = Real.log ‖z‖ := by
  have ht : Tendsto (greenApprox 0 z) atTop (𝓝 (Real.log ‖z‖)) := by
    have hfun : greenApprox 0 z = fun _ : ℕ => Real.log ‖z‖ :=
      funext fun n => greenApprox_zero_eq_log_norm z n
    rw [hfun]
    exact tendsto_const_nhds
  exact ht.limUnder_eq

/-- The model dynamical Green function is `log⁺ ‖z‖`. -/
theorem greenFunctionDyn_zero_eq_posLog (z : ℂ) :
    greenFunctionDyn 0 z = Real.posLog ‖z‖ := by
  by_cases hzle : ‖z‖ ≤ 1
  · rw [greenFunctionDyn, if_pos ((mem_filledJulia_zero_iff_norm_le_one z).2 hzle),
      Real.posLog_eq_log_max_one (norm_nonneg z), max_eq_left hzle, Real.log_one]
  · push Not at hzle
    have hzK : z ∉ filledJulia 0 :=
      fun hz => not_le_of_gt hzle ((mem_filledJulia_zero_iff_norm_le_one z).1 hz)
    rw [greenFunctionDyn, if_neg hzK, greenLimit_zero_eq_log_norm z,
      Real.posLog_eq_log_max_one (norm_nonneg z), max_eq_right hzle.le]

/-- The average of the logarithmic kernel against the unit circle is
`-log⁺ |z|` (with `Real.posLog`). -/
theorem circleAverage_logKernel_unitCircle (z : ℂ) :
    Real.circleAverage (fun ζ => logKernel z ζ) 0 1 = - Real.posLog ‖z‖ := by
  have h := Polynomial.logMahlerMeasure_X_sub_C z
  rw [Polynomial.logMahlerMeasure_def] at h
  have hfun : (fun ζ : ℂ => logKernel z ζ)
      = fun ζ => - Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖ := by
    funext ζ
    unfold logKernel
    simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
    congr 1
    rw [show z - ζ = -(ζ - z) by ring, norm_neg]
  rw [hfun]
  have hneg := Real.circleAverage_fun_smul (a := (-1 : ℝ))
      (f := fun ζ : ℂ =>
        Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖)
      (c := 0) (R := 1)
  calc
    Real.circleAverage
          (fun ζ => - Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖)
          0 1
        = (-1 : ℝ) • Real.circleAverage
          (fun ζ => Real.log ‖Polynomial.eval ζ (Polynomial.X - Polynomial.C z : Polynomial ℂ)‖)
          0 1 := by
          simpa using hneg
    _ = (-1 : ℝ) • Real.posLog ‖z‖ := by rw [h]
    _ = - Real.posLog ‖z‖ := by simp

/-- The logarithmic kernel is measurable against the concrete unit-circle measure. -/
theorem logKernel_aestronglyMeasurable_unitCircleMeasure (z : ℂ) :
    AEStronglyMeasurable (fun ζ => logKernel z ζ) unitCircleMeasure := by
  unfold logKernel
  exact ((Real.measurable_log.comp ((continuous_const.sub continuous_id).norm.measurable)).neg).aestronglyMeasurable

/-- The concrete unit-circle measure has potential `-log⁺ ‖z‖`. -/
theorem logPotential_unitCircleMeasure (z : ℂ) :
    logPotential unitCircleMeasure z = - Real.posLog ‖z‖ := by
  rw [logPotential,
    integral_unitCircleMeasure_eq_circleAverage (fun ζ => logKernel z ζ)
      (logKernel_aestronglyMeasurable_unitCircleMeasure z),
    circleAverage_logKernel_unitCircle]

/-- Green-function notation for the unit-circle model potential. -/
theorem greenFunction_unitCircleMeasure_zero (z : ℂ) :
    greenFunction unitCircleMeasure 0 z = Real.posLog ‖z‖ := by
  simp [greenFunction, logPotential_unitCircleMeasure z]

/-- The concrete unit-circle measure gives the full potential representation of `G_0`. -/
theorem hasGreenPotentialRepresentation_unitCircleMeasure_zero :
    HasGreenPotentialRepresentation 0 unitCircleMeasure := by
  intro z
  rw [greenFunctionDyn_zero_eq_posLog, greenFunction_unitCircleMeasure_zero]

/-- The concrete Brolin/equilibrium measure in the model case `f_0(z)=z²`. -/
noncomputable def brolinMeasureZero : Measure ℂ :=
  unitCircleMeasure

instance instIsProbabilityMeasure_brolinMeasureZero :
    IsProbabilityMeasure brolinMeasureZero := by
  rw [brolinMeasureZero]
  infer_instance

/-- The model Brolin measure is a probability carried by `K_0`. -/
theorem isProbOn_brolinMeasureZero_filledJulia_zero :
    IsProbOn brolinMeasureZero (filledJulia 0) := by
  simpa [brolinMeasureZero] using isProbOn_unitCircleMeasure_filledJulia_zero

/-- Potential of the model Brolin measure. -/
theorem logPotential_brolinMeasureZero (z : ℂ) :
    logPotential brolinMeasureZero z = - Real.posLog ‖z‖ := by
  simpa [brolinMeasureZero] using logPotential_unitCircleMeasure z

/-- Green-function notation for the model Brolin measure potential. -/
theorem greenFunction_brolinMeasureZero_zero (z : ℂ) :
    greenFunction brolinMeasureZero 0 z = Real.posLog ‖z‖ := by
  simpa [brolinMeasureZero] using greenFunction_unitCircleMeasure_zero z

/-- The named model Brolin measure gives the potential representation of `G_0`. -/
theorem hasGreenPotentialRepresentation_brolinMeasureZero_zero :
    HasGreenPotentialRepresentation 0 brolinMeasureZero := by
  simpa [brolinMeasureZero] using hasGreenPotentialRepresentation_unitCircleMeasure_zero

/-- Direct zero-model potential identity: `G_0(z) = -U^{μ_0}(z)`. -/
theorem greenFunctionDyn_zero_eq_neg_logPotential_brolinMeasureZero (z : ℂ) :
    greenFunctionDyn 0 z = - logPotential brolinMeasureZero z :=
  (hasGreenPotentialRepresentation_iff 0 brolinMeasureZero).mp
    hasGreenPotentialRepresentation_brolinMeasureZero_zero z

/-- Existence of a no-hypothesis probability measure representing the model Green function. -/
theorem exists_probOn_hasGreenPotentialRepresentation_zero :
    ∃ μ : Measure ℂ, IsProbOn μ (filledJulia 0) ∧ HasGreenPotentialRepresentation 0 μ :=
  ⟨brolinMeasureZero, isProbOn_brolinMeasureZero_filledJulia_zero,
    hasGreenPotentialRepresentation_brolinMeasureZero_zero⟩

/-- Outside the unit disk, the unit-circle kernel average is `-log |z|`. -/
theorem circleAverage_logKernel_unitCircle_of_one_le {z : ℂ} (hz : 1 ≤ ‖z‖) :
    Real.circleAverage (fun ζ => logKernel z ζ) 0 1 = - Real.log ‖z‖ := by
  rw [circleAverage_logKernel_unitCircle, Real.posLog_eq_log_max_one (norm_nonneg z),
    max_eq_right hz]

/-- Inside the unit disk, the unit-circle kernel average is zero. -/
theorem circleAverage_logKernel_unitCircle_of_norm_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Real.circleAverage (fun ζ => logKernel z ζ) 0 1 = 0 := by
  rw [circleAverage_logKernel_unitCircle, Real.posLog_eq_log_max_one (norm_nonneg z),
    max_eq_left hz, Real.log_one, neg_zero]

end Bottcher
