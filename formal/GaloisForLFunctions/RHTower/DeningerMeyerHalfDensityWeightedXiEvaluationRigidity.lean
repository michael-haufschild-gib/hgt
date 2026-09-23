import GaloisForLFunctions.RHTower.DeningerMeyerReflectedGaussianCountertransportXiCapacity

/-!
# Rigidity of weighted global Xi evaluation

Let `w` be any `ell^(2 : ℕ)` field on the multiplicity-exact Xi divisor.  Consider
the prescription

`u ↦ (q ↦ E_q(u) w(q))`,

where `E_q` is zeroth Xi evaluation on literal Meyer cohomology.  This file
classifies exactly when that prescription extends continuously from the
canonical half-density completion to the global Xi Hilbert carrier:

`extension exists ↔ every divisor copy where w is nonzero is critical`.

Sufficiency is the weighted Bessel estimate obtained from critical-line
contractivity.  Necessity uses the uniformly capacity-bounded reflected
Gaussian countertransport at one coordinate.  If `w(q) ≠ 0`, bounded global
descent would bound that character orbit, forcing `Re rho_q = 1/2`.

Consequently every coordinatewise nonzero `ell^(2 : ℕ)` weight gives such an
extension exactly under RH.  No rapidly decaying nonzero diagonal damping can
repair off-line evaluation.  A weight can hide an off-line point only by
vanishing there, which makes the repair target-selected and nonconservative.
-/

open Complex Filter Function Set Topology MeasureTheory Asymptotics
open scoped Real
open GaloisForLFunctions

namespace RHTower

noncomputable section

/-- Weighted Xi evaluation on the literal source when every retained
coordinate is critical. -/
def deningerMeyerHalfDensityWeightedXiEvaluationLM
    (w : XiDivisorL2)
    (hwline : ∀ q : XiZeroCopy, w q ≠ 0 → (q.1 : ℂ).re = 1 / 2) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] XiDivisorL2 where
  toFun u :=
    ⟨fun q =>
        deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) u * w q,
      Memℓp.mono
        ((lp.memℓp w).norm.const_smul
          (deningerMeyerHalfDensityCohomologySeminorm u))
        (fun q => by
          rw [norm_mul, Pi.smul_apply, smul_eq_mul]
          by_cases hwq : w q = 0
          · simp [hwq]
          · exact mul_le_mul_of_nonneg_right
              (norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology
                q.1 (hwline q hwq) u)
              (norm_nonneg _))⟩
  map_add' u v := by
    apply lp.ext
    funext q
    change
      deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) (u + v) * w q = _
    rw [map_add]
    simp only [lp.coeFn_add, Pi.add_apply]
    ring
  map_smul' c u := by
    apply lp.ext
    funext q
    change
      deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) (c • u) * w q = _
    rw [map_smul]
    simp only [lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    ring

@[simp]
theorem deningerMeyerHalfDensityWeightedXiEvaluationLM_apply
    (w : XiDivisorL2)
    (hwline : ∀ q : XiZeroCopy, w q ≠ 0 → (q.1 : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) (q : XiZeroCopy) :
    deningerMeyerHalfDensityWeightedXiEvaluationLM w hwline u q =
      deningerMeyerXiSupportJetEvaluationLM q.1
        (⟨0, xiSupportMultiplicity_pos q.1⟩ :
          DeningerArithmeticJetIndex q.1) u * w q := rfl

/-- Weighted global evaluation has sharp elementary bound `‖w‖ p(u)`. -/
theorem norm_deningerMeyerHalfDensityWeightedXiEvaluationLM_le
    (w : XiDivisorL2)
    (hwline : ∀ q : XiZeroCopy, w q ≠ 0 → (q.1 : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    ‖deningerMeyerHalfDensityWeightedXiEvaluationLM w hwline u‖ ≤
      ‖w‖ * deningerMeyerHalfDensityCohomologySeminorm u := by
  have hmono :
      ‖deningerMeyerHalfDensityWeightedXiEvaluationLM w hwline u‖ ≤
        ‖(deningerMeyerHalfDensityCohomologySeminorm u : ℂ) • w‖ :=
    lp.norm_mono (by norm_num) (fun q => by
      rw [deningerMeyerHalfDensityWeightedXiEvaluationLM_apply,
        norm_mul, lp.coeFn_smul, Pi.smul_apply, norm_smul]
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (apply_nonneg
          deningerMeyerHalfDensityCohomologySeminorm u)]
      by_cases hwq : w q = 0
      · simp [hwq]
      · simpa [mul_comm] using mul_le_mul_of_nonneg_right
          (norm_deningerMeyerXiSupportEvaluation_le_halfDensityCohomology
            q.1 (hwline q hwq) u)
          (norm_nonneg (w q)))
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (apply_nonneg
      deningerMeyerHalfDensityCohomologySeminorm u)] at hmono
  simpa [mul_comm] using hmono

/-- Continuous weighted evaluation on the completed source whenever the
weight is supported on critical divisor copies. -/
def deningerMeyerHalfDensityWeightedXiEvaluationCLM
    (w : XiDivisorL2)
    (hwline : ∀ q : XiZeroCopy, w q ≠ 0 → (q.1 : ℂ).re = 1 / 2) :
    DeningerMeyerHalfDensityCompletion →L[ℂ] XiDivisorL2 :=
  deningerSeminormFactorC
    (C := ‖w‖)
    (T := deningerMeyerHalfDensityWeightedXiEvaluationLM w hwline)
    (norm_deningerMeyerHalfDensityWeightedXiEvaluationLM_le w hwline)

@[simp]
theorem deningerMeyerHalfDensityWeightedXiEvaluationCLM_mk
    (w : XiDivisorL2)
    (hwline : ∀ q : XiZeroCopy, w q ≠ 0 → (q.1 : ℂ).re = 1 / 2)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerHalfDensityWeightedXiEvaluationCLM w hwline
        (deningerMeyerHalfDensityCompletionMk u) =
      deningerMeyerHalfDensityWeightedXiEvaluationLM w hwline u := by
  exact deningerSeminormFactorC_coe _ u

/-- Existence of a continuous global map agreeing with weighted Xi
evaluation on every literal source class. -/
def DeningerMeyerHalfDensityWeightedXiEvaluationAdmissible
    (w : XiDivisorL2) : Prop :=
  ∃ T : DeningerMeyerHalfDensityCompletion →L[ℂ] XiDivisorL2,
    ∀ (u : DeningerMeyerStrongLogCohomology) (q : XiZeroCopy),
      T (deningerMeyerHalfDensityCompletionMk u) q =
        deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) u * w q

/-- Any nonzero retained weight forces its divisor coordinate onto the
critical line. -/
theorem re_eq_half_of_deningerMeyerHalfDensityWeightedXiEvaluationAdmissible_of_weight_ne_zero
    (w : XiDivisorL2)
    (hA : DeningerMeyerHalfDensityWeightedXiEvaluationAdmissible w)
    (q : XiZeroCopy) (hwq : w q ≠ 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  obtain ⟨T, hT⟩ := hA
  apply
    (deningerMeyerReflectedGaussianCountertransportEvaluationBoundedAt_iff
      q.1).mp
  have hwpos : 0 < ‖w q‖ := norm_pos_iff.mpr hwq
  refine ⟨2 * ‖T‖ / ‖w q‖, fun c => ?_⟩
  let u := deningerMeyerReflectedGaussianCountertransportClass c
  have hprod :
      ‖deningerMeyerXiSupportJetEvaluationLM q.1
          (⟨0, xiSupportMultiplicity_pos q.1⟩ :
            DeningerArithmeticJetIndex q.1) u * w q‖ ≤ 2 * ‖T‖ := by
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
  exact (le_div_iff₀ hwpos).2 (by simpa [mul_comm] using hprod)

/-- **Exact support classification.**  Weighted global evaluation descends
continuously precisely when the weight vanishes at every off-line divisor
copy. -/
theorem deningerMeyerHalfDensityWeightedXiEvaluationAdmissible_iff_support_on_line
    (w : XiDivisorL2) :
    DeningerMeyerHalfDensityWeightedXiEvaluationAdmissible w ↔
      ∀ q : XiZeroCopy, w q ≠ 0 → (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hA q hwq
    exact
      re_eq_half_of_deningerMeyerHalfDensityWeightedXiEvaluationAdmissible_of_weight_ne_zero
        w hA q hwq
  · intro hwline
    refine
      ⟨deningerMeyerHalfDensityWeightedXiEvaluationCLM w hwline,
        fun u q => ?_⟩
    rw [deningerMeyerHalfDensityWeightedXiEvaluationCLM_mk,
      deningerMeyerHalfDensityWeightedXiEvaluationLM_apply]

/-- Every coordinatewise nonzero diagonal weight admits continuous weighted
Xi descent exactly under RH. -/
theorem deningerMeyerHalfDensityWeightedXiEvaluationAdmissible_iff_rh_of_pointwise_ne_zero
    (w : XiDivisorL2) (hw : ∀ q : XiZeroCopy, w q ≠ 0) :
    DeningerMeyerHalfDensityWeightedXiEvaluationAdmissible w ↔
      RiemannHypothesis := by
  rw [deningerMeyerHalfDensityWeightedXiEvaluationAdmissible_iff_support_on_line]
  constructor
  · intro hline
    rw [← xiBoundaryCharacterNeutral_iff_riemannHypothesis]
    intro rho
    let q : XiZeroCopy :=
      ⟨rho, ⟨0, xiSupportMultiplicity_pos rho⟩⟩
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff (rho : ℂ)).2
        (hline q (hw q))
  · intro hRH q _
    have hfracture :=
      (xiBoundaryCharacterNeutral_iff_riemannHypothesis.mpr hRH) q.1
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (q.1 : ℂ)).mp hfracture

/-- The canonical reciprocal divisor vector is square-summable and nonzero at every Xi copy,
so its weighted half-density evaluation is admissible exactly under RH. -/
theorem deningerMeyerHalfDensityXiInvEvaluationAdmissible_iff_rh :
    DeningerMeyerHalfDensityWeightedXiEvaluationAdmissible xiInvVec ↔
      RiemannHypothesis := by
  exact
    deningerMeyerHalfDensityWeightedXiEvaluationAdmissible_iff_rh_of_pointwise_ne_zero
      xiInvVec (fun q => by
        rw [xiInvVec_apply]
        exact inv_ne_zero (xiSpectralPoint_ne_zero q))

end

end RHTower
