import GaloisForLFunctions.HTGeometry.ReturnExcisedOptimalDesignCoareaLaw
import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.ConjSqrt

/-!
# Positive-reporter complete-incidence law

This file proves the source--target inequality underlying the Bures incidence
minimax law.  A positive-definite reporter `A` controls every target in a
complete union through opposite quadratic channels `A` and `A⁻¹`.  The
target union is removed pointwise before integration, so no target-count union
bound occurs.  Restricting the source measure to a return complement retains
every source point and pays return mass once.

The identification of the optimum over reporters with Bures root fidelity is
separate matrix-convex infrastructure.  No such identification is assumed in
this file.
-/

open MeasureTheory Matrix Set
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Source quadratic channel selected by a positive reporter. -/
def finitePositiveReporterSourceEnergy {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) : ℝ :=
  (star u ⬝ᵥ (A *ᵥ u)).re

/-- Opposite target quadratic channel selected by the inverse reporter. -/
def finitePositiveReporterTargetLeverage {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (star v ⬝ᵥ (A⁻¹ *ᵥ v)).re

/-- Squared-overlap complete capture event for an arbitrary target family. -/
def finitePositiveReporterCaptureEvent
    {X C : Type*} {n : ℕ}
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) : Set X :=
  {x | ∃ c, threshold ≤ ‖finiteComplexInner (state x) (target c)‖ ^ 2}

/-- Source energy of a positive-definite reporter is nonnegative. -/
theorem finitePositiveReporterSourceEnergy_nonneg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    (u : Fin n → ℂ) :
    0 ≤ finitePositiveReporterSourceEnergy A u := by
  exact hA.posSemidef.re_dotProduct_nonneg u

/-- Inverse target leverage of a positive-definite reporter is nonnegative. -/
theorem finitePositiveReporterTargetLeverage_nonneg
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    (v : Fin n → ℂ) :
    0 ≤ finitePositiveReporterTargetLeverage A v := by
  exact hA.inv.posSemidef.re_dotProduct_nonneg v

/-- **Positive-reporter matrix Cauchy--Schwarz.**  Every overlap factors
through the square root of `A` and the inverse square root of `A`. -/
theorem finitePositiveReporter_matrixCauchySchwarz
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (u v : Fin n → ℂ) :
    ‖finiteComplexInner u v‖ ^ 2 ≤
      finitePositiveReporterSourceEnergy A u *
        finitePositiveReporterTargetLeverage A v := by
  classical
  let P : Matrix (Fin n) (Fin n) ℂ := CFC.sqrt A
  have hA0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA.posSemidef
  have hPunit : IsUnit P := by
    exact (CFC.isUnit_sqrt_iff A hA0).2 hA.isUnit
  have hPdet : IsUnit P.det := P.isUnit_iff_isUnit_det.mp hPunit
  have hPH : Pᴴ = P := by
    simpa [P, Matrix.star_eq_conjTranspose] using
      (CFC.sqrt_nonneg A).star_eq
  have hPP : P * P = A := by
    simpa [P, pow_two] using CFC.sq_sqrt A hA0
  have hPinvH : P⁻¹ᴴ = P⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, hPH]
  have hAinv : A⁻¹ = P⁻¹ * P⁻¹ := by
    letI : Invertible A := hA.isUnit.nonempty_invertible.some
    letI : Invertible P := hPunit.nonempty_invertible.some
    apply Matrix.mul_left_injective_of_invertible (A := A)
    change A⁻¹ * A = (P⁻¹ * P⁻¹) * A
    rw [Matrix.inv_mul_of_invertible, ← hPP]
    simp [Matrix.mul_assoc, Matrix.inv_mul_of_invertible]
  have hinner :
      star (P *ᵥ u) ⬝ᵥ (P⁻¹ *ᵥ v) = star u ⬝ᵥ v := by
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hPH, Matrix.mul_nonsing_inv P hPdet]
    simp
  have hquadU :
      ‖WithLp.toLp 2 (P *ᵥ u)‖ ^ 2 =
        finitePositiveReporterSourceEnergy A u := by
    rw [@norm_sq_eq_re_inner ℂ, inner_toLp_eq_finiteComplexInner]
    change (star (P *ᵥ u) ⬝ᵥ (P *ᵥ u)).re = _
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hPH, hPP, ← Matrix.dotProduct_mulVec]
    rfl
  have hquadV :
      ‖WithLp.toLp 2 (P⁻¹ *ᵥ v)‖ ^ 2 =
        finitePositiveReporterTargetLeverage A v := by
    rw [@norm_sq_eq_re_inner ℂ, inner_toLp_eq_finiteComplexInner]
    change (star (P⁻¹ *ᵥ v) ⬝ᵥ (P⁻¹ *ᵥ v)).re = _
    unfold finitePositiveReporterTargetLeverage
    rw [hAinv]
    rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec,
      Matrix.vecMul_vecMul, hPinvH, ← Matrix.dotProduct_mulVec]
  have hcs := norm_inner_le_norm (𝕜 := ℂ)
    (WithLp.toLp 2 (P *ᵥ u)) (WithLp.toLp 2 (P⁻¹ *ᵥ v))
  rw [inner_toLp_eq_finiteComplexInner] at hcs
  change ‖star (P *ᵥ u) ⬝ᵥ (P⁻¹ *ᵥ v)‖ ≤ _ at hcs
  rw [hinner] at hcs
  have hsq := pow_le_pow_left₀ (norm_nonneg (star u ⬝ᵥ v)) hcs 2
  rw [mul_pow, hquadU, hquadV] at hsq
  exact hsq

/-- One uniform inverse-channel ceiling controls the complete target union
pointwise.  Target type may be finite, countable, continuous, or empty. -/
theorem finitePositiveReporter_completeCapture_subset
    {X C : Type*} {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold targetCeiling : ℝ)
    (hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ targetCeiling) :
    finitePositiveReporterCaptureEvent target state threshold ⊆
      {x | threshold ≤
        targetCeiling * finitePositiveReporterSourceEnergy A (state x)} := by
  intro x hx
  obtain ⟨c, hc⟩ := hx
  have hsource := finitePositiveReporterSourceEnergy_nonneg hA (state x)
  calc
    threshold ≤ ‖finiteComplexInner (state x) (target c)‖ ^ 2 := hc
    _ ≤ finitePositiveReporterSourceEnergy A (state x) *
        finitePositiveReporterTargetLeverage A (target c) :=
      finitePositiveReporter_matrixCauchySchwarz A hA (state x) (target c)
    _ ≤ finitePositiveReporterSourceEnergy A (state x) * targetCeiling :=
      mul_le_mul_of_nonneg_left (hceiling c) hsource
    _ = targetCeiling * finitePositiveReporterSourceEnergy A (state x) :=
      mul_comm _ _

/-- **Complete-union positive-reporter incidence law.**  The target union is
handled before integration.  No cardinality, selector, or union-bound factor
appears. -/
theorem finitePositiveReporter_completeIncidence_bound
    {X C : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (targetCeiling : ℝ) (hceilingNonneg : 0 ≤ targetCeiling)
    (hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ targetCeiling)
    (hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy A (state x)) mu) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      targetCeiling * ∫ x,
        finitePositiveReporterSourceEnergy A (state x) ∂mu := by
  let q : X → ℝ := fun x ↦
    targetCeiling * finitePositiveReporterSourceEnergy A (state x)
  let E : Set X := finitePositiveReporterCaptureEvent target state threshold
  have hEQ : E ⊆ {x | threshold ≤ q x} := by
    exact finitePositiveReporter_completeCapture_subset
      A hA target state threshold targetCeiling hceiling
  have hintq : Integrable q mu := hint.const_mul targetCeiling
  have hqnonneg : 0 ≤ᵐ[mu] q :=
    Filter.Eventually.of_forall fun x ↦
      mul_nonneg hceilingNonneg
        (finitePositiveReporterSourceEnergy_nonneg hA (state x))
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    hqnonneg hintq threshold
  calc
    threshold * mu.real E ≤
        threshold * mu.real {x | threshold ≤ q x} :=
      mul_le_mul_of_nonneg_left
        (measureReal_mono hEQ (by finiteness)) hthreshold.le
    _ ≤ ∫ x, q x ∂mu := hmarkov
    _ = targetCeiling * ∫ x,
        finitePositiveReporterSourceEnergy A (state x) ∂mu := by
      exact integral_const_mul targetCeiling _

/-- A set is bounded by one removed mass plus its surviving mass under the
restricted complement measure. -/
theorem measureReal_le_return_add_restrict_compl
    {X : Type*} [MeasurableSpace X]
    (mu : Measure X) [IsFiniteMeasure mu]
    (event returnSet : Set X) (hreturn : MeasurableSet returnSet) :
    mu.real event ≤
      mu.real returnSet + (mu.restrict returnSetᶜ).real event := by
  have hsub : event ⊆ returnSet ∪ (event ∩ returnSetᶜ) := by
    intro x hx
    by_cases hxReturn : x ∈ returnSet
    · exact Set.mem_union_left _ hxReturn
    · exact Set.mem_union_right _ ⟨hx, hxReturn⟩
  calc
    mu.real event ≤ mu.real (returnSet ∪ (event ∩ returnSetᶜ)) :=
      measureReal_mono hsub
    _ ≤ mu.real returnSet + mu.real (event ∩ returnSetᶜ) :=
      measureReal_union_le _ _
    _ = mu.real returnSet + (mu.restrict returnSetᶜ).real event := by
      rw [measureReal_restrict_apply' hreturn.compl]

/-- **Return-excised complete-incidence law.**  Return mass is paid once and
all surviving source points retain their original restricted-measure weight. -/
theorem finitePositiveReporter_returnExcisedIncidence_bound
    {X C : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (targetCeiling : ℝ) (hceilingNonneg : 0 ≤ targetCeiling)
    (hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ targetCeiling)
    (returnSet : Set X) (hreturn : MeasurableSet returnSet)
    (hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy A (state x))
        (mu.restrict returnSetᶜ)) :
    mu.real (finitePositiveReporterCaptureEvent target state threshold) ≤
      mu.real returnSet +
        (targetCeiling * ∫ x,
          finitePositiveReporterSourceEnergy A (state x)
            ∂(mu.restrict returnSetᶜ)) / threshold := by
  let nu : Measure X := mu.restrict returnSetᶜ
  let E : Set X := finitePositiveReporterCaptureEvent target state threshold
  have hscaled := finitePositiveReporter_completeIncidence_bound
    nu A hA target state threshold hthreshold targetCeiling
      hceilingNonneg hceiling hint
  have hresidual :
      nu.real E ≤
        (targetCeiling * ∫ x,
          finitePositiveReporterSourceEnergy A (state x) ∂nu) / threshold := by
    apply (le_div_iff₀' hthreshold).2
    simpa [mul_comm] using hscaled
  have hcut := measureReal_le_return_add_restrict_compl
    mu E returnSet hreturn
  exact hcut.trans (by
    simpa [E, nu] using add_le_add_left hresidual (mu.real returnSet))

/-! ## Exact covariance reporter identity -/

/-- Entrywise source covariance `∫ |u⟩⟨u|`. -/
def finitePositiveReporterSourceCovariance
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) (state : X → Fin n → ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  complexFeatureGram mu (fun i x ↦ state x i)

/-- Pairwise coordinate integrability implies integrability of every finite
reporter quadratic form. -/
theorem finitePositiveReporter_complexSourceEnergy_integrable
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) (state : X → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    Integrable (fun x ↦ star (state x) ⬝ᵥ (A *ᵥ state x)) mu := by
  classical
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
  apply integrable_finsetSum Finset.univ
  intro i _
  apply integrable_finsetSum Finset.univ
  intro j _
  have h := (hprod j i).mul_const (A i j)
  apply h.congr
  filter_upwards [] with x
  ring

/-- Pairwise coordinate integrability also gives integrability of the real
source-energy channel. -/
theorem finitePositiveReporterSourceEnergy_integrable
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) (state : X → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    Integrable (fun x ↦ finitePositiveReporterSourceEnergy A (state x)) mu := by
  have hcomplex := finitePositiveReporter_complexSourceEnergy_integrable
    mu state A hprod
  simpa [finitePositiveReporterSourceEnergy] using hcomplex.re

/-- The trace pairing of source covariance with a reporter is exactly the
integral of the reporter's source quadratic channel. -/
theorem finitePositiveReporter_trace_covariance_mul_eq_integral
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) (state : X → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    (finitePositiveReporterSourceCovariance mu state * A).trace =
      ∫ x, star (state x) ⬝ᵥ (A *ᵥ state x) ∂mu := by
  classical
  have hterm : ∀ i j, Integrable
      (fun x ↦ star (state x i) * A i j * state x j) mu := by
    intro i j
    have h := hprod j i
    have hc := h.mul_const (A i j)
    apply hc.congr
    filter_upwards [] with x
    change state x j * star (state x i) * A i j =
      star (state x i) * A i j * state x j
    ring
  unfold finitePositiveReporterSourceCovariance complexFeatureGram
  simp only [Matrix.trace]
  calc
    (∑ i, ∑ j, (∫ x, state x i * star (state x j) ∂mu) * A j i) =
        ∑ i, ∑ j, ∫ x,
          (state x i * star (state x j)) * A j i ∂mu := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_mul_const]
    _ = ∑ j, ∑ i, ∫ x,
          star (state x j) * A j i * state x i ∂mu := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = ∫ x, ∑ j, ∑ i,
          star (state x j) * A j i * state x i ∂mu := by
      rw [integral_finsetSum Finset.univ]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum Finset.univ]
        exact fun i _ ↦ hterm j i
      · intro j _
        exact integrable_finsetSum Finset.univ fun i _ ↦ hterm j i
    _ = ∫ x, star (state x) ⬝ᵥ (A *ᵥ state x) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Real trace form of the covariance reporter identity. -/
theorem finitePositiveReporter_re_trace_covariance_mul_eq_integral
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) (state : X → Fin n → ℂ)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    ((finitePositiveReporterSourceCovariance mu state * A).trace).re =
      ∫ x, finitePositiveReporterSourceEnergy A (state x) ∂mu := by
  have hcomplex := finitePositiveReporter_trace_covariance_mul_eq_integral
    mu state A hprod
  have hre := congrArg Complex.re hcomplex
  have hint := finitePositiveReporter_complexSourceEnergy_integrable
    mu state A hprod
  calc
    ((finitePositiveReporterSourceCovariance mu state * A).trace).re =
        (∫ x, star (state x) ⬝ᵥ (A *ᵥ state x) ∂mu).re := hre
    _ = ∫ x, (star (state x) ⬝ᵥ (A *ᵥ state x)).re ∂mu := by
      simpa only [RCLike.re_eq_complex_re] using (integral_re hint).symm
    _ = ∫ x, finitePositiveReporterSourceEnergy A (state x) ∂mu := rfl

/-- Source covariance is positive semidefinite under pairwise coordinate
integrability. -/
theorem finitePositiveReporterSourceCovariance_posSemidef
    {X : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) (state : X → Fin n → ℂ)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    (finitePositiveReporterSourceCovariance mu state).PosSemidef := by
  exact complexFeatureGram_posSemidef mu
    (fun i x ↦ state x i) hprod

/-- Covariance form of the complete-union positive-reporter law. -/
theorem finitePositiveReporter_completeIncidence_covariance_bound
    {X C : Type*} [MeasurableSpace X] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.PosDef)
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (targetCeiling : ℝ) (hceilingNonneg : 0 ≤ targetCeiling)
    (hceiling : ∀ c,
      finitePositiveReporterTargetLeverage A (target c) ≤ targetCeiling)
    (hint : Integrable
      (fun x ↦ finitePositiveReporterSourceEnergy A (state x)) mu)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      targetCeiling *
        ((finitePositiveReporterSourceCovariance mu state * A).trace).re := by
  rw [finitePositiveReporter_re_trace_covariance_mul_eq_integral
    mu state A hprod]
  exact finitePositiveReporter_completeIncidence_bound
    mu A hA target state threshold hthreshold targetCeiling
      hceilingNonneg hceiling hint

/-! ## Exact finite-target reporter infimum -/

/-- Maximum inverse-channel leverage over one nonempty finite occupied target
image.  Duplicate target labels do not introduce a sum. -/
def finitePositiveReporterTargetMaximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (target : C → Fin n → ℂ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun c ↦ finitePositiveReporterTargetLeverage A (target c))

/-- Every occupied target leverage is bounded by the finite-target maximum. -/
theorem finitePositiveReporterTargetLeverage_le_maximum
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (target : C → Fin n → ℂ)
    (c : C) :
    finitePositiveReporterTargetLeverage A (target c) ≤
      finitePositiveReporterTargetMaximum A target := by
  exact Finset.le_sup'
    (fun j ↦ finitePositiveReporterTargetLeverage A (target j))
    (Finset.mem_univ c)

/-- The finite-target maximum is nonnegative for every positive reporter. -/
theorem finitePositiveReporterTargetMaximum_nonneg
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.PosDef)
    (target : C → Fin n → ℂ) :
    0 ≤ finitePositiveReporterTargetMaximum A target := by
  let c : C := Classical.choice (inferInstance : Nonempty C)
  exact (finitePositiveReporterTargetLeverage_nonneg hA (target c)).trans
    (finitePositiveReporterTargetLeverage_le_maximum A target c)

/-- Infimum of all positive-reporter source--target products for one positive
source covariance and one nonempty finite occupied target image. -/
def finitePositiveReporterIncidenceCapacity
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (sourceCovariance : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) : ℝ :=
  sInf {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
    A.PosDef ∧
      q = finitePositiveReporterTargetMaximum A target *
        ((sourceCovariance * A).trace).re}

/-- The defining reporter-value set is nonempty: the identity is positive
definite in every finite dimension. -/
theorem finitePositiveReporterIncidenceCapacity_values_nonempty
    {C : Type*} [Fintype C] [Nonempty C] {n : ℕ}
    (sourceCovariance : Matrix (Fin n) (Fin n) ℂ)
    (target : C → Fin n → ℂ) :
    {q : ℝ | ∃ A : Matrix (Fin n) (Fin n) ℂ,
      A.PosDef ∧
        q = finitePositiveReporterTargetMaximum A target *
          ((sourceCovariance * A).trace).re}.Nonempty := by
  refine ⟨finitePositiveReporterTargetMaximum
      (1 : Matrix (Fin n) (Fin n) ℂ) target *
        ((sourceCovariance * 1).trace).re, ?_⟩
  exact ⟨1, Matrix.PosDef.one, rfl⟩

/-- **Exact finite-target reporter-infimum incidence law.**  The complete
union is bounded by the infimum over every positive-definite reporter, with
the actual covariance and maximum occupied-target inverse leverage. -/
theorem finitePositiveReporter_completeIncidence_capacity_bound
    {X C : Type*} [MeasurableSpace X]
    [Fintype C] [Nonempty C] {n : ℕ}
    (mu : Measure X) [IsFiniteMeasure mu]
    (target : C → Fin n → ℂ) (state : X → Fin n → ℂ)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hprod : ∀ i j, Integrable
      (fun x ↦ state x i * star (state x j)) mu) :
    threshold * mu.real
        (finitePositiveReporterCaptureEvent target state threshold) ≤
      finitePositiveReporterIncidenceCapacity
        (finitePositiveReporterSourceCovariance mu state) target := by
  unfold finitePositiveReporterIncidenceCapacity
  apply le_csInf
    (finitePositiveReporterIncidenceCapacity_values_nonempty
      (finitePositiveReporterSourceCovariance mu state) target)
  intro q hq
  obtain ⟨A, hA, rfl⟩ := hq
  exact finitePositiveReporter_completeIncidence_covariance_bound
    mu A hA target state threshold hthreshold
      (finitePositiveReporterTargetMaximum A target)
      (finitePositiveReporterTargetMaximum_nonneg hA target)
      (finitePositiveReporterTargetLeverage_le_maximum A target)
      (finitePositiveReporterSourceEnergy_integrable mu state A hprod)
      hprod

end

end GaloisForLFunctions.HTGeometry
