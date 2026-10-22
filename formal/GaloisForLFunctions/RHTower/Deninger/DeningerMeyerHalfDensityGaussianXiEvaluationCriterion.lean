import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianCountertransportXiCapacity

/-!
# Gaussian-weighted global Xi evaluation criterion

The source-derived reflected Gaussian horizon is used to weight all zeroth Xi
evaluations of literal Meyer cohomology.  Under RH, critical-line
contractivity and square summability of the horizon give a bounded linear map
from the half-density completion to the multiplicity-exact Xi `ell^(2 : ℕ)`
carrier.

Conversely, existence of any continuous map agreeing with those weighted
evaluations forces RH.  The uniformly capacity-bounded reflected Gaussian
countertransport supplies the witness: boundedness of the global map bounds
each countertransport evaluation after division by one nonzero horizon
coordinate, and the countertransport criterion places that divisor point on
the critical line.

This is an operator-level classification, not a conditional construction
presented as an RH proof.  It identifies the precise missing source-to-global
evaluation descent: existence of that canonical weighted extension is itself
equivalent to RH.
-/

open Complex Filter Function Set Topology MeasureTheory Asymptotics
open scoped Real
open GaloisForLFunctions

namespace RHTower

noncomputable section

namespace DeningerMeyerGaussianGreen

/-- Under RH, Gaussian-weighted Xi evaluation is a linear map from literal
Meyer cohomology into the completed divisor carrier. -/
def deningerMeyerHalfDensityGaussianXiEvaluationLM
    (hRH : RiemannHypothesis) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] XiDivisorL2 where
  toFun u :=
    ⟨fun q =>
        deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) u *
          reflectedGaussianHorizonGrade q,
      Memℓp.mono
        ((lp.memℓp reflectedGaussianHorizonGradeL2).norm.const_smul
          (deningerMeyerHalfDensityCohomologySeminorm u))
        (fun q => by
          rw [norm_mul, Pi.smul_apply, smul_eq_mul,
            reflectedGaussianHorizonGradeL2_apply]
          have hq : (q.1 : ℂ).re = 1 / 2 := by
            have hfracture :=
              (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) q.1
            exact
              (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
                (q.1 : ℂ)).mp hfracture
          exact mul_le_mul_of_nonneg_right
            (norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology
              q.1 hq u)
            (norm_nonneg _))⟩
  map_add' u v := by
    apply lp.ext
    funext q
    change
      deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) (u + v) *
          reflectedGaussianHorizonGrade q = _
    rw [map_add]
    simp only [lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c u := by
    apply lp.ext
    funext q
    change
      deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) (c • u) *
          reflectedGaussianHorizonGrade q = _
    rw [map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    ring

@[simp]
theorem deningerMeyerHalfDensityGaussianXiEvaluationLM_apply
    (hRH : RiemannHypothesis)
    (u : DeningerMeyerStrongLogCohomology) (q : XiZeroCopy) :
    deningerMeyerHalfDensityGaussianXiEvaluationLM hRH u q =
      deningerMeyerXiSupportJetEvaluationLM q.1
        (⟨0, xiSupportMultiplicity_pos q.1⟩ :
          DeningerArithmeticJetIndex q.1) u *
        reflectedGaussianHorizonGrade q := rfl

/-- The weighted literal evaluation map is bounded by horizon norm times
half-density source capacity. -/
theorem norm_deningerMeyerHalfDensityGaussianXiEvaluationLM_le
    (hRH : RiemannHypothesis)
    (u : DeningerMeyerStrongLogCohomology) :
    ‖deningerMeyerHalfDensityGaussianXiEvaluationLM hRH u‖ ≤
      ‖reflectedGaussianHorizonGradeL2‖ *
        deningerMeyerHalfDensityCohomologySeminorm u := by
  have hpoint (q : XiZeroCopy) : (q.1 : ℂ).re = 1 / 2 := by
    have hfracture :=
      (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) q.1
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (q.1 : ℂ)).mp hfracture
  have hmono :
      ‖deningerMeyerHalfDensityGaussianXiEvaluationLM hRH u‖ ≤
        ‖(deningerMeyerHalfDensityCohomologySeminorm u : ℂ) •
          reflectedGaussianHorizonGradeL2‖ :=
    lp.norm_mono (by norm_num) (fun q => by
      rw [deningerMeyerHalfDensityGaussianXiEvaluationLM_apply,
        norm_mul, lp.coeFn_smul, Pi.smul_apply, norm_smul,
        reflectedGaussianHorizonGradeL2_apply]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (apply_nonneg
          deningerMeyerHalfDensityCohomologySeminorm u)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right
        (norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology
          q.1 (hpoint q) u)
        (norm_nonneg (reflectedGaussianHorizonGrade q)))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (apply_nonneg
      deningerMeyerHalfDensityCohomologySeminorm u)] at hmono
  simpa [mul_comm] using hmono

/-- Under RH, the literal weighted map extends to the complete
half-density source. -/
def deningerMeyerHalfDensityGaussianXiEvaluationCLM
    (hRH : RiemannHypothesis) :
    DeningerMeyerHalfDensityCompletion →L[ℂ] XiDivisorL2 :=
  deningerSeminormFactorC
    (C := ‖reflectedGaussianHorizonGradeL2‖)
    (T := deningerMeyerHalfDensityGaussianXiEvaluationLM hRH)
    (norm_deningerMeyerHalfDensityGaussianXiEvaluationLM_le hRH)

@[simp]
theorem deningerMeyerHalfDensityGaussianXiEvaluationCLM_mk
    (hRH : RiemannHypothesis)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHalfDensityGaussianXiEvaluationCLM hRH
        (deningerMeyerHalfDensityCompletionMk u) =
      deningerMeyerHalfDensityGaussianXiEvaluationLM hRH u := by
  exact deningerSeminormFactorC_coe _ u

/-- Unconditional formulation of weighted global evaluation descent:
some continuous map from the source completion agrees with every literal
Gaussian-weighted Xi evaluation. -/
def DeningerMeyerHalfDensityGaussianXiEvaluationAdmissible : Prop :=
  ∃ T : DeningerMeyerHalfDensityCompletion →L[ℂ] XiDivisorL2,
    ∀ (u : DeningerMeyerStrongLogCohomology) (q : XiZeroCopy),
      T (deningerMeyerHalfDensityCompletionMk u) q =
        deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) u *
          reflectedGaussianHorizonGrade q

/-- **Weighted global evaluation criterion.**  The canonical source-to-Xi
descent exists exactly under RH. -/
theorem deningerMeyerHalfDensityGaussianXiEvaluationAdmissible_iff_rh :
    DeningerMeyerHalfDensityGaussianXiEvaluationAdmissible ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨T, hT⟩
    apply
      deningerMeyerReflectedGaussianCountertransportEvaluationsBounded_iff_rh.mp
    intro rho
    let q : XiZeroCopy :=
      ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    have hhpos : 0 < ‖reflectedGaussianHorizonGrade q‖ :=
      norm_pos_iff.mpr (reflectedGaussianHorizonGrade_ne_zero q)
    refine
      ⟨2 * ‖T‖ / ‖reflectedGaussianHorizonGrade q‖, fun c => ?_⟩
    let u := deningerMeyerReflectedGaussianCountertransportClass c
    have hprod :
        ‖deningerMeyerXiSupportJetEvaluationLM rho
            (⟨0, xiSupportMultiplicity_pos rho⟩ :
              DeningerArithmeticJetIndex rho) u *
            reflectedGaussianHorizonGrade q‖ ≤ 2 * ‖T‖ := by
      calc
        _ = ‖T (deningerMeyerHalfDensityCompletionMk u) q‖ := by
          rw [hT u q]
        _ ≤ ‖T (deningerMeyerHalfDensityCompletionMk u)‖ :=
          lp.norm_apply_le_norm
            (by norm_num : (2 : ENNReal) ≠ 0) _ q
        _ ≤ ‖T‖ * ‖deningerMeyerHalfDensityCompletionMk u‖ :=
          T.le_opNorm _
        _ = ‖T‖ * deningerMeyerHalfDensityCohomologySeminorm u := by
          rw [deningerMeyerHalfDensityCompletionMk_norm]
        _ ≤ ‖T‖ * 2 :=
          mul_le_mul_of_nonneg_left
            (deningerMeyerReflectedGaussianCountertransportClass_uniform_capacity
              c)
            (norm_nonneg T)
        _ = 2 * ‖T‖ := by ring
    rw [norm_mul] at hprod
    exact (le_div_iff₀ hhpos).2 (by simpa [mul_comm] using hprod)
  · intro hRH
    refine
      ⟨deningerMeyerHalfDensityGaussianXiEvaluationCLM hRH,
        fun u q => ?_⟩
    rw [deningerMeyerHalfDensityGaussianXiEvaluationCLM_mk,
      deningerMeyerHalfDensityGaussianXiEvaluationLM_apply]

end DeningerMeyerGaussianGreen

end

end RHTower
