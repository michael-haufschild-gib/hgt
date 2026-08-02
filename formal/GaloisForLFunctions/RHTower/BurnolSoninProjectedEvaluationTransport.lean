import GaloisForLFunctions.RHTower.BurnolSoninDilationMellin
import GaloisForLFunctions.RHTower.ArchimedeanMellinFourier
import GaloisForLFunctions.RHTower.BurnolBilateralApertureDefectEnergy

/-!
# Burnol projected evaluation transport and bilateral defect energy

This module combines actual closed extended Sonine spaces, their orthogonal projections, concrete
completed-Mellin Riesz vectors, and normalized `L²` dilations.  It proves both cross-aperture
projected Riesz laws, both exact Pythagorean decompositions, signed hyperbolic defect energy,
critical-line balance/orientation, and the finite Fourier-odd projection holonomy realizing that
energy as one quadratic form.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- Genuine orthogonal projection onto Burnol's extended Sonine space. -/
def burnolExtendedSoninProjection (a : ℝ) (ha : 0 < a) :
    evenSubspace →L[ℂ] evenSubspace := by
  letI : Fact (0 < a) := ⟨ha⟩
  exact (soninExtendedSpace a).starProjection

theorem burnolExtendedSoninProjection_eq_self_iff
    {a : ℝ} (ha : 0 < a) {f : evenSubspace} :
    burnolExtendedSoninProjection a ha f = f ↔ f ∈ soninExtendedSpace a := by
  letI : Fact (0 < a) := ⟨ha⟩
  exact Submodule.starProjection_eq_self_iff

theorem soninCosineUnitary_burnolExtendedSoninProjection
    (a : ℝ) (ha : 0 < a) (f : evenSubspace) :
    soninCosineUnitary (burnolExtendedSoninProjection a ha f) =
      burnolExtendedSoninProjection a ha (soninCosineUnitary f) := by
  letI : Fact (0 < a) := ⟨ha⟩
  change soninCosineUnitary ((soninExtendedSpace a).starProjection f) =
    (soninExtendedSpace a).starProjection (soninCosineUnitary f)
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact soninCosineUnitary_mem_soninExtendedSpace (Submodule.coe_mem _)
  · intro g hg
    have hFg : soninCosineUnitary g ∈ soninExtendedSpace a :=
      soninCosineUnitary_mem_soninExtendedSpace hg
    calc
      ⟪soninCosineUnitary f -
          soninCosineUnitary ((soninExtendedSpace a).starProjection f), g⟫_ℂ =
          ⟪soninCosineUnitary (f - (soninExtendedSpace a).starProjection f),
            soninCosineUnitary (soninCosineUnitary g)⟫_ℂ := by
            rw [map_sub, soninCosineUnitary_involutive]
      _ = ⟪f - (soninExtendedSpace a).starProjection f, soninCosineUnitary g⟫_ℂ :=
        soninCosineUnitary.inner_map_map _ _
      _ = 0 := Submodule.starProjection_inner_eq_zero f _ hFg

/-- Adjoint-dilated evaluation vector, orthogonally projected back to the larger aperture. -/
def burnolProjectedAdjointEvaluationVector
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) : soninExtendedSpace a := by
  let hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  exact (soninExtendedSpace a).orthogonalProjectionOnto
    ((ContinuousLinearMap.adjoint (evenDilationCLM r hr0))
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace))

/-- Projected cross-aperture adjoint law for the concrete continuous Mellin evaluator. -/
theorem burnolProjectedAdjointEvaluationVector_eq
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    burnolProjectedAdjointEvaluationVector hlo hhi ha hr =
      star ((r : ℂ) ^ (w - 1 / 2)) •
        burnolExtendedSoninEvaluationVector w a hlo hhi ha := by
  let hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  apply ext_inner_right ℂ
  intro f
  let Uf : soninExtendedSpace b :=
    ⟨evenDilationCLM r hr0 (f : evenSubspace),
      evenDilation_mem_soninExtendedSpace_inv_mul ha hr f.property⟩
  calc
    ⟪burnolProjectedAdjointEvaluationVector hlo hhi ha hr, f⟫_ℂ =
        ⟪(ContinuousLinearMap.adjoint (evenDilationCLM r hr0))
            (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
          (f : evenSubspace)⟫_ℂ :=
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right f _
    _ = ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
          evenDilationCLM r hr0 (f : evenSubspace)⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_left _ _ _
    _ = ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, Uf⟫_ℂ := rfl
    _ = soninMellinEvaluation w
          ((((Uf : soninExtendedSpace b) : evenSubspace) : SoninL2) : ℝ → ℂ) :=
      inner_burnolExtendedSoninEvaluationVector w b hlo hhi hb Uf
    _ = (r : ℂ) ^ (w - 1 / 2) *
          soninMellinEvaluation w
            ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ) :=
      soninMellinEvaluation_evenDilation w r hr0 (f : evenSubspace)
    _ = (r : ℂ) ^ (w - 1 / 2) *
          ⟪burnolExtendedSoninEvaluationVector w a hlo hhi ha, f⟫_ℂ := by
      rw [inner_burnolExtendedSoninEvaluationVector]
    _ = ⟪star ((r : ℂ) ^ (w - 1 / 2)) •
          burnolExtendedSoninEvaluationVector w a hlo hhi ha, f⟫_ℂ := by
      simp [inner_smul_left]

/-- Forward-dilated evaluation vector, orthogonally projected back to the larger aperture. -/
def burnolProjectedForwardEvaluationVector
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) : soninExtendedSpace a := by
  let hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  exact (soninExtendedSpace a).orthogonalProjectionOnto
    (evenDilationCLM r hr0
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace))

/-- Second projected cross-aperture law, with the inverse normalized Mellin character. -/
theorem burnolProjectedForwardEvaluationVector_eq
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 ≤ r) :
    burnolProjectedForwardEvaluationVector hlo hhi ha hr =
      star (((r : ℂ) ^ (w - 1 / 2))⁻¹) •
        burnolExtendedSoninEvaluationVector w a hlo hhi ha := by
  let hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  apply ext_inner_right ℂ
  intro f
  let Uinvf : soninExtendedSpace b :=
    ⟨evenDilationCLM r⁻¹ (inv_pos.mpr hr0) (f : evenSubspace),
      evenInverseDilation_mem_soninExtendedSpace_inv_mul ha hr f.property⟩
  calc
    ⟪burnolProjectedForwardEvaluationVector hlo hhi ha hr, f⟫_ℂ =
        ⟪evenDilationCLM r hr0
            (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
          (f : evenSubspace)⟫_ℂ :=
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right f _
    _ = ⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
          (ContinuousLinearMap.adjoint (evenDilationCLM r hr0))
            (f : evenSubspace)⟫_ℂ :=
      (ContinuousLinearMap.adjoint_inner_right _ _ _).symm
    _ = ⟪burnolExtendedSoninEvaluationVector w b hlo hhi hb, Uinvf⟫_ℂ := by
      rw [adjoint_evenDilationCLM]
      rfl
    _ = soninMellinEvaluation w
          ((((Uinvf : soninExtendedSpace b) : evenSubspace) : SoninL2) : ℝ → ℂ) :=
      inner_burnolExtendedSoninEvaluationVector w b hlo hhi hb Uinvf
    _ = (((r : ℂ) ^ (w - 1 / 2))⁻¹) *
          soninMellinEvaluation w
            ((((f : soninExtendedSpace a) : evenSubspace) : SoninL2) : ℝ → ℂ) := by
      rw [soninMellinEvaluation_evenDilation]
      rw [ofReal_inv_cpow hr0, Complex.cpow_neg]
    _ = (((r : ℂ) ^ (w - 1 / 2))⁻¹) *
          ⟪burnolExtendedSoninEvaluationVector w a hlo hhi ha, f⟫_ℂ := by
      rw [inner_burnolExtendedSoninEvaluationVector]
    _ = ⟪star (((r : ℂ) ^ (w - 1 / 2))⁻¹) •
          burnolExtendedSoninEvaluationVector w a hlo hhi ha, f⟫_ℂ := by
      simp [inner_smul_left]

/-- Orthogonal loss of the adjoint-dilated cross-aperture evaluation vector. -/
def burnolExtendedApertureDefectPlus
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) : evenSubspace :=
  let hr0 : 0 < r := zero_lt_one.trans hr
  let b : ℝ := r⁻¹ * a
  let hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  (1 - burnolExtendedSoninProjection a ha)
    ((ContinuousLinearMap.adjoint (evenDilationCLM r hr0))
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace))

/-- Orthogonal loss of the forward-dilated cross-aperture evaluation vector. -/
def burnolExtendedApertureDefectMinus
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) : evenSubspace :=
  let hr0 : 0 < r := zero_lt_one.trans hr
  let b : ℝ := r⁻¹ * a
  let hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  (1 - burnolExtendedSoninProjection a ha)
    (evenDilationCLM r hr0
      (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace))

theorem norm_sq_burnolExtendedApertureDefectPlus
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    let b : ℝ := r⁻¹ * a
    let hb : 0 < b := mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha
    ‖burnolExtendedSoninEvaluationVector w b hlo hhi hb‖ ^ 2 =
      ‖(r : ℂ) ^ (w - 1 / 2)‖ ^ 2 *
          ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 +
        ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 := by
  dsimp only
  let hr0 : 0 < r := zero_lt_one.trans hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  let z : evenSubspace :=
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)
  let za : evenSubspace :=
    (burnolExtendedSoninEvaluationVector w a hlo hhi ha : evenSubspace)
  let x := (ContinuousLinearMap.adjoint (evenDilationCLM r hr0)) z
  have hpy := (soninExtendedSpace a).norm_sq_eq_add_norm_sq_starProjection x
  have hxnorm : ‖x‖ = ‖z‖ := by
    dsimp only [x]
    rw [adjoint_evenDilationCLM]
    exact norm_evenDilationCLM_apply _ _ _
  have hP : (soninExtendedSpace a).starProjection x =
      star ((r : ℂ) ^ (w - 1 / 2)) • za := by
    exact congrArg Subtype.val
      (burnolProjectedAdjointEvaluationVector_eq hlo hhi ha hr.le)
  have hQ : (soninExtendedSpace a)ᗮ.starProjection x =
      burnolExtendedApertureDefectPlus hlo hhi ha hr := by
    rw [Submodule.starProjection_orthogonal]
    change (1 - (soninExtendedSpace a).starProjection) x = _
    rw [← show burnolExtendedSoninProjection a ha =
      (soninExtendedSpace a).starProjection from rfl]
    rfl
  rw [hxnorm, hP, hQ, norm_smul, norm_star] at hpy
  simpa [z, za, mul_pow] using hpy

theorem norm_sq_burnolExtendedApertureDefectMinus
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    let b : ℝ := r⁻¹ * a
    let hb : 0 < b := mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha
    ‖burnolExtendedSoninEvaluationVector w b hlo hhi hb‖ ^ 2 =
      ‖((r : ℂ) ^ (w - 1 / 2))⁻¹‖ ^ 2 *
          ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 +
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 := by
  dsimp only
  let hr0 : 0 < r := zero_lt_one.trans hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  let z : evenSubspace :=
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)
  let za : evenSubspace :=
    (burnolExtendedSoninEvaluationVector w a hlo hhi ha : evenSubspace)
  let x := evenDilationCLM r hr0 z
  have hpy := (soninExtendedSpace a).norm_sq_eq_add_norm_sq_starProjection x
  have hxnorm : ‖x‖ = ‖z‖ := norm_evenDilationCLM_apply _ _ _
  have hP : (soninExtendedSpace a).starProjection x =
      star (((r : ℂ) ^ (w - 1 / 2))⁻¹) • za := by
    exact congrArg Subtype.val
      (burnolProjectedForwardEvaluationVector_eq hlo hhi ha hr.le)
  have hQ : (soninExtendedSpace a)ᗮ.starProjection x =
      burnolExtendedApertureDefectMinus hlo hhi ha hr := by
    rw [Submodule.starProjection_orthogonal]
    change (1 - (soninExtendedSpace a).starProjection) x = _
    rw [← show burnolExtendedSoninProjection a ha =
      (soninExtendedSpace a).starProjection from rfl]
    rfl
  rw [hxnorm, hP, hQ, norm_smul, norm_star] at hpy
  simpa [z, za, mul_pow] using hpy

/-- Exact signed bilateral defect energy on the concrete continuous evaluation vector. -/
theorem burnolExtended_bilateralApertureDefectEnergy
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
        ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 =
      (r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re)) *
        ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 := by
  have hp := norm_sq_burnolExtendedApertureDefectPlus hlo hhi ha hr
  have hm := norm_sq_burnolExtendedApertureDefectMinus hlo hhi ha hr
  have hs :
      ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
          ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 =
        (‖(r : ℂ) ^ (w - 1 / 2)‖ ^ 2 -
          ‖((r : ℂ) ^ (w - 1 / 2))⁻¹‖ ^ 2) *
          ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 := by
    nlinarith
  rw [hs, norm_inv,
    show (r : ℂ) ^ (w - 1 / 2) = burnolMellinDilationCharacter r w from rfl,
    norm_burnolMellinDilationCharacter_sq r (zero_lt_one.trans hr) w,
    norm_burnolMellinDilationCharacter_inv_sq r (zero_lt_one.trans hr) w]

theorem burnolExtended_bilateralApertureDefects_balanced_iff
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hza : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0) :
    ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ =
        ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ↔
      w.re = 1 / 2 := by
  have hs := burnolExtended_bilateralApertureDefectEnergy hlo hhi ha hr
  have hzanorm : 0 < ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hza)
  constructor
  · intro hnorm
    have hprod :
        (r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re)) *
          ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 = 0 := by
      rw [← hs, hnorm]
      ring
    exact (burnol_rpowOrientation_zero_iff r w.re hr).mp
      ((mul_eq_zero.mp hprod).resolve_right (ne_of_gt hzanorm))
  · intro hw
    have hcoeff := (burnol_rpowOrientation_zero_iff r w.re hr).mpr hw
    have hsq :
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 =
          ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 := by
      nlinarith [hs]
    nlinarith [norm_nonneg (burnolExtendedApertureDefectMinus hlo hhi ha hr),
      norm_nonneg (burnolExtendedApertureDefectPlus hlo hhi ha hr)]

theorem burnolExtended_bilateralApertureDefects_oriented_right_iff
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hza : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0) :
    ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ <
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ↔
      1 / 2 < w.re := by
  have hs := burnolExtended_bilateralApertureDefectEnergy hlo hhi ha hr
  have hzanorm : 0 < ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hza)
  rw [← burnol_rpowOrientation_pos_iff r w.re hr]
  constructor <;> intro h
  · have hsq : 0 <
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
          ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 := by
      nlinarith [norm_nonneg (burnolExtendedApertureDefectMinus hlo hhi ha hr),
        norm_nonneg (burnolExtendedApertureDefectPlus hlo hhi ha hr)]
    nlinarith [hs]
  · have hsq : 0 <
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
          ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 := by
      rw [hs]
      positivity
    nlinarith [norm_nonneg (burnolExtendedApertureDefectMinus hlo hhi ha hr),
      norm_nonneg (burnolExtendedApertureDefectPlus hlo hhi ha hr)]

theorem burnolExtended_bilateralApertureDefects_oriented_left_iff
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r)
    (hza : burnolExtendedSoninEvaluationVector w a hlo hhi ha ≠ 0) :
    ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ <
        ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ↔
      w.re < 1 / 2 := by
  have hs := burnolExtended_bilateralApertureDefectEnergy hlo hhi ha hr
  have hzanorm : 0 < ‖burnolExtendedSoninEvaluationVector w a hlo hhi ha‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hza)
  rw [← burnol_rpowOrientation_neg_iff r w.re hr]
  constructor <;> intro h
  · have hsq :
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
            ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 < 0 := by
      nlinarith [norm_nonneg (burnolExtendedApertureDefectMinus hlo hhi ha hr),
        norm_nonneg (burnolExtendedApertureDefectPlus hlo hhi ha hr)]
    nlinarith [hs]
  · have hsq :
        ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
            ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 < 0 := by
      rw [hs]
      exact mul_neg_of_neg_of_pos h hzanorm
    nlinarith [norm_nonneg (burnolExtendedApertureDefectMinus hlo hhi ha hr),
      norm_nonneg (burnolExtendedApertureDefectPlus hlo hhi ha hr)]

/-- Finite bilateral holonomy of Burnol's actual extended-space projection. -/
def burnolExtendedBilateralApertureHolonomy
    (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenSubspace →L[ℂ] evenSubspace :=
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let P := burnolExtendedSoninProjection a ha
  U * P * ContinuousLinearMap.adjoint U -
    ContinuousLinearMap.adjoint U * P * U

/-- Cosine reflection reverses the finite extended-Sonine holonomy. -/
theorem burnolExtendedBilateralApertureHolonomy_fourier_odd
    (a : ℝ) (ha : 0 < a) (r : ℝ) (hr : 1 < r) :
    evenFourierTransform * burnolExtendedBilateralApertureHolonomy a ha r hr *
        evenFourierTransform =
      -burnolExtendedBilateralApertureHolonomy a ha r hr := by
  let J := evenFourierTransform
  let P := burnolExtendedSoninProjection a ha
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let V := ContinuousLinearMap.adjoint U
  have hJ2 : J * J = 1 := by
    simpa only [J] using evenFourierTransform_mul_self
  have hJP : J * P = P * J := by
    apply ContinuousLinearMap.ext
    intro f
    exact soninCosineUnitary_burnolExtendedSoninProjection a ha f
  have hJU : J * U = V * J := by
    simpa only [J, U, V] using evenFourierTransform_mul_evenDilationCLM r hr
  have hJV : J * V = U * J := by
    simpa only [J, U, V] using
      evenFourierTransform_mul_adjoint_evenDilationCLM r hr
  have hJPJ : J * P * J = P := by
    calc
      J * P * J = P * (J * J) := by rw [hJP]; noncomm_ring
      _ = P := by rw [hJ2, mul_one]
  have hJUJ : J * U * J = V := by
    calc
      J * U * J = V * (J * J) := by rw [hJU]; noncomm_ring
      _ = V := by rw [hJ2, mul_one]
  have hJVJ : J * V * J = U := by
    calc
      J * V * J = U * (J * J) := by rw [hJV]; noncomm_ring
      _ = U := by rw [hJ2, mul_one]
  have hconj_mul (A B : evenSubspace →L[ℂ] evenSubspace) :
      J * (A * B) * J = (J * A * J) * (J * B * J) := by
    calc
      J * (A * B) * J = J * A * B * J := by noncomm_ring
      _ = J * A * (J * J) * B * J := by rw [hJ2]; simp
      _ = (J * A * J) * (J * B * J) := by noncomm_ring
  change J * (U * P * V - V * P * U) * J = -(U * P * V - V * P * U)
  calc
    J * (U * P * V - V * P * U) * J =
        J * (U * P * V) * J - J * (V * P * U) * J := by
      rw [mul_sub, sub_mul]
    _ = (J * U * J) * (J * P * J) * (J * V * J) -
          (J * V * J) * (J * P * J) * (J * U * J) := by
      rw [hconj_mul (U * P) V, hconj_mul U P,
        hconj_mul (V * P) U, hconj_mul V P]
    _ = V * P * U - U * P * V := by rw [hJUJ, hJPJ, hJVJ]
    _ = -(U * P * V - V * P * U) := by module

/-- The signed evaluation-defect energy is the quadratic form of one source projection
holonomy. -/
theorem burnolExtended_bilateralApertureDefectEnergy_eq_holonomy
    {w : ℂ} (hlo : 1 / 2 < w.re) (hhi : w.re < 1)
    {a r : ℝ} (ha : 0 < a) (hr : 1 < r) :
    let b : ℝ := r⁻¹ * a
    let hb : 0 < b := mul_pos (inv_pos.mpr (zero_lt_one.trans hr)) ha
    ‖burnolExtendedApertureDefectMinus hlo hhi ha hr‖ ^ 2 -
        ‖burnolExtendedApertureDefectPlus hlo hhi ha hr‖ ^ 2 =
      (⟪(burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace),
        burnolExtendedBilateralApertureHolonomy a ha r hr
          (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)⟫_ℂ).re := by
  dsimp only
  let hr0 : 0 < r := zero_lt_one.trans hr
  let b : ℝ := r⁻¹ * a
  have hb : 0 < b := mul_pos (inv_pos.mpr hr0) ha
  letI : Fact (0 < a) := ⟨ha⟩
  letI : Fact (0 < b) := ⟨hb⟩
  let z : evenSubspace :=
    (burnolExtendedSoninEvaluationVector w b hlo hhi hb : evenSubspace)
  let U := evenDilationCLM r hr0
  let P := burnolExtendedSoninProjection a ha
  let V := ContinuousLinearMap.adjoint U
  have hU : ‖U z‖ = ‖z‖ := norm_evenDilationCLM_apply _ _ _
  have hV : ‖V z‖ = ‖z‖ := by
    dsimp only [V, U]
    rw [adjoint_evenDilationCLM]
    exact norm_evenDilationCLM_apply _ _ _
  have hpU := (soninExtendedSpace a).norm_sq_eq_add_norm_sq_starProjection (U z)
  have hpV := (soninExtendedSpace a).norm_sq_eq_add_norm_sq_starProjection (V z)
  rw [Submodule.starProjection_orthogonal] at hpU hpV
  change ‖U z‖ ^ 2 = ‖P (U z)‖ ^ 2 + ‖(1 - P) (U z)‖ ^ 2 at hpU
  change ‖V z‖ ^ 2 = ‖P (V z)‖ ^ 2 + ‖(1 - P) (V z)‖ ^ 2 at hpV
  rw [hU] at hpU
  rw [hV] at hpV
  have hfirst : (⟪z, U (P (V z))⟫_ℂ).re = ‖P (V z)‖ ^ 2 := by
    rw [← ContinuousLinearMap.adjoint_inner_left U (P (V z)) z]
    change (⟪V z, P (V z)⟫_ℂ).re = _
    change (⟪V z, (soninExtendedSpace a).starProjection (V z)⟫_ℂ).re = _
    exact HTGeometry.re_inner_starProjection_eq_norm_sq (soninExtendedSpace a) (V z)
  have hsecond : (⟪z, V (P (U z))⟫_ℂ).re = ‖P (U z)‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_right U z (P (U z))]
    change (⟪U z, (soninExtendedSpace a).starProjection (U z)⟫_ℂ).re = _
    exact HTGeometry.re_inner_starProjection_eq_norm_sq (soninExtendedSpace a) (U z)
  have hrhs :
      (⟪z, burnolExtendedBilateralApertureHolonomy a ha r hr z⟫_ℂ).re =
        (⟪z, U (P (V z))⟫_ℂ).re - (⟪z, V (P (U z))⟫_ℂ).re := by
    change (⟪z, (U * P * V - V * P * U) z⟫_ℂ).re = _
    simp only [sub_apply, mul_apply_eq_comp, inner_sub_right, Complex.sub_re]
  change ‖(1 - P) (U z)‖ ^ 2 - ‖(1 - P) (V z)‖ ^ 2 = _
  rw [hrhs, hfirst, hsecond]
  nlinarith [hpU, hpV]

end RHTower
