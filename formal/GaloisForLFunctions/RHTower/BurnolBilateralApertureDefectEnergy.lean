import GaloisForLFunctions.RHTower.SoninApertureFourierParityNoGo
import GaloisForLFunctions.RHTower.SoninCouplingBranchEstimate
import GaloisForLFunctions.HTGeometry.ProjectionMeasurementSurvival
import GaloisForLFunctions.Core

/-!
# Burnol bilateral aperture-defect energy

Exact zeroth-jet value law on the concrete even Sonin carrier.  The two projected evaluator
transport identities remain explicit theorem premises: the vectors, projections, normalized
dilations, orthogonal defects, Mellin character, finite holonomy, and Fourier parity operator are
all the literal objects of the repository's Sonin model.
-/

set_option maxHeartbeats 1000000

open Complex
open scoped InnerProductSpace

namespace RHTower

noncomputable section

def burnolApertureDefectPlus (a r : ℝ) (hr : 1 < r) (z : evenSubspace) : evenSubspace :=
  (1 - evenCentralSoninProjection a)
    (ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) z)

theorem norm_sq_burnolApertureDefectPlus (a r : ℝ) (hr : 1 < r) (z za : evenSubspace) (lam : ℂ)
    (hproj : evenCentralSoninProjection a
      (ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) z) =
        star lam • za) :
    ‖z‖ ^ 2 = ‖lam‖ ^ 2 * ‖za‖ ^ 2 + ‖burnolApertureDefectPlus a r hr z‖ ^ 2 := by
  let K := evenCentralSoninCarrier a
  let x := ContinuousLinearMap.adjoint
    (evenDilationCLM r (zero_lt_one.trans hr)) z
  have hpy := K.norm_sq_eq_add_norm_sq_starProjection x
  have hxnorm : ‖x‖ = ‖z‖ := by
    dsimp only [x]
    rw [adjoint_evenDilationCLM]
    exact norm_evenDilationCLM_apply _ _ _
  have hP : K.starProjection x = star lam • za := by
    rw [← evenCentralSoninProjection_eq_starProjection]
    exact hproj
  have hQ : Kᗮ.starProjection x = burnolApertureDefectPlus a r hr z := by
    rw [Submodule.starProjection_orthogonal]
    change (1 - (evenCentralSoninCarrier a).starProjection) x = _
    rw [← evenCentralSoninProjection_eq_starProjection]
    rfl
  rw [hxnorm, hP, hQ, norm_smul, norm_star] at hpy
  nlinarith [norm_nonneg lam, norm_nonneg za]

def burnolApertureDefectMinus (a r : ℝ) (hr : 1 < r) (z : evenSubspace) : evenSubspace :=
  (1 - evenCentralSoninProjection a)
    (evenDilationCLM r (zero_lt_one.trans hr) z)

theorem norm_sq_burnolApertureDefectMinus (a r : ℝ) (hr : 1 < r) (z za : evenSubspace) (lam : ℂ)
    (hproj : evenCentralSoninProjection a
      (evenDilationCLM r (zero_lt_one.trans hr) z) = star lam⁻¹ • za) :
    ‖z‖ ^ 2 = ‖lam⁻¹‖ ^ 2 * ‖za‖ ^ 2 + ‖burnolApertureDefectMinus a r hr z‖ ^ 2 := by
  let K := evenCentralSoninCarrier a
  let x := evenDilationCLM r (zero_lt_one.trans hr) z
  have hpy := K.norm_sq_eq_add_norm_sq_starProjection x
  have hxnorm : ‖x‖ = ‖z‖ := norm_evenDilationCLM_apply _ _ _
  have hP : K.starProjection x = star lam⁻¹ • za := by
    rw [← evenCentralSoninProjection_eq_starProjection]
    exact hproj
  have hQ : Kᗮ.starProjection x = burnolApertureDefectMinus a r hr z := by
    rw [Submodule.starProjection_orthogonal]
    change (1 - (evenCentralSoninCarrier a).starProjection) x = _
    rw [← evenCentralSoninProjection_eq_starProjection]
    rfl
  rw [hxnorm, hP, hQ, norm_smul, norm_star] at hpy
  nlinarith [norm_nonneg lam⁻¹, norm_nonneg za]

theorem burnol_bilateralApertureDefectEnergy (a r : ℝ) (hr : 1 < r) (z za : evenSubspace) (lam : ℂ)
    (hplus : evenCentralSoninProjection a
      (ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) z) =
        star lam • za)
    (hminus : evenCentralSoninProjection a
      (evenDilationCLM r (zero_lt_one.trans hr) z) = star lam⁻¹ • za) :
    ‖burnolApertureDefectMinus a r hr z‖ ^ 2 - ‖burnolApertureDefectPlus a r hr z‖ ^ 2 =
      (‖lam‖ ^ 2 - ‖lam‖⁻¹ ^ 2) * ‖za‖ ^ 2 := by
  have hp := norm_sq_burnolApertureDefectPlus a r hr z za lam hplus
  have hm := norm_sq_burnolApertureDefectMinus a r hr z za lam hminus
  rw [norm_inv] at hm
  nlinarith

def burnolMellinDilationCharacter (r : ℝ) (w : ℂ) : ℂ := (r : ℂ) ^ (w - 1 / 2)

theorem norm_burnolMellinDilationCharacter_sq (r : ℝ) (hr : 0 < r) (w : ℂ) :
    ‖burnolMellinDilationCharacter r w‖ ^ 2 = r ^ (2 * w.re - 1) := by
  rw [burnolMellinDilationCharacter, Complex.norm_cpow_eq_rpow_re_of_pos hr,
    Complex.sub_re]
  norm_num
  rw [← Real.rpow_natCast (r ^ (w.re - 1 / 2)) 2,
    ← Real.rpow_mul hr.le]
  congr 1
  ring

theorem norm_burnolMellinDilationCharacter_inv_sq (r : ℝ) (hr : 0 < r) (w : ℂ) :
    ‖burnolMellinDilationCharacter r w‖⁻¹ ^ 2 = r ^ (1 - 2 * w.re) := by
  rw [inv_pow, norm_burnolMellinDilationCharacter_sq r hr w, ← Real.rpow_neg hr.le]
  congr 1
  ring

theorem burnol_bilateralApertureDefectEnergy_eq_rpow (a r : ℝ) (hr : 1 < r) (w : ℂ) (z za : evenSubspace)
    (hplus : evenCentralSoninProjection a
      (ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) z) =
        star (burnolMellinDilationCharacter r w) • za)
    (hminus : evenCentralSoninProjection a
      (evenDilationCLM r (zero_lt_one.trans hr) z) = star ((burnolMellinDilationCharacter r w)⁻¹) • za) :
    ‖burnolApertureDefectMinus a r hr z‖ ^ 2 - ‖burnolApertureDefectPlus a r hr z‖ ^ 2 =
      (r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re)) * ‖za‖ ^ 2 := by
  have hs := burnol_bilateralApertureDefectEnergy a r hr z za
    (burnolMellinDilationCharacter r w) hplus hminus
  rw [hs, norm_burnolMellinDilationCharacter_sq r (zero_lt_one.trans hr) w,
    norm_burnolMellinDilationCharacter_inv_sq r (zero_lt_one.trans hr) w]

theorem evenCentralSoninProjection_pythagorean (a : ℝ) (x : evenSubspace) :
    ‖x‖ ^ 2 = ‖evenCentralSoninProjection a x‖ ^ 2 +
      ‖(1 - evenCentralSoninProjection a) x‖ ^ 2 := by
  let K := evenCentralSoninCarrier a
  have hpy := K.norm_sq_eq_add_norm_sq_starProjection x
  rw [evenCentralSoninProjection_eq_starProjection]
  change ‖x‖ ^ 2 = ‖K.starProjection x‖ ^ 2 +
    ‖(ContinuousLinearMap.id ℂ evenSubspace - K.starProjection) x‖ ^ 2
  rw [← Submodule.starProjection_orthogonal]
  exact hpy

theorem burnol_bilateralApertureDefectEnergy_eq_holonomy (a r : ℝ) (hr : 1 < r) (z : evenSubspace) :
    ‖burnolApertureDefectMinus a r hr z‖ ^ 2 - ‖burnolApertureDefectPlus a r hr z‖ ^ 2 =
      (inner ℂ z (evenSoninBilateralApertureHolonomy a r hr z)).re := by
  let U := evenDilationCLM r (zero_lt_one.trans hr)
  let P := evenCentralSoninProjection a
  let V := ContinuousLinearMap.adjoint U
  have hU : ‖U z‖ = ‖z‖ := norm_evenDilationCLM_apply _ _ _
  have hV : ‖V z‖ = ‖z‖ := by
    dsimp only [V, U]
    rw [adjoint_evenDilationCLM]
    exact norm_evenDilationCLM_apply _ _ _
  have hpU := evenCentralSoninProjection_pythagorean a (U z)
  have hpV := evenCentralSoninProjection_pythagorean a (V z)
  change ‖U z‖ ^ 2 = ‖P (U z)‖ ^ 2 + ‖(1 - P) (U z)‖ ^ 2 at hpU
  change ‖V z‖ ^ 2 = ‖P (V z)‖ ^ 2 + ‖(1 - P) (V z)‖ ^ 2 at hpV
  rw [hU] at hpU
  rw [hV] at hpV
  have hfirst : (inner ℂ z (U (P (V z)))).re = ‖P (V z)‖ ^ 2 := by
    rw [← ContinuousLinearMap.adjoint_inner_left U (P (V z)) z]
    change (inner ℂ (V z) (P (V z))).re = _
    rw [show P = (evenCentralSoninCarrier a).starProjection by
      exact evenCentralSoninProjection_eq_starProjection a]
    exact HTGeometry.re_inner_starProjection_eq_norm_sq
      (evenCentralSoninCarrier a) (V z)
  have hsecond : (inner ℂ z (V (P (U z)))).re = ‖P (U z)‖ ^ 2 := by
    rw [ContinuousLinearMap.adjoint_inner_right U z (P (U z))]
    rw [show P = (evenCentralSoninCarrier a).starProjection by
      exact evenCentralSoninProjection_eq_starProjection a]
    exact HTGeometry.re_inner_starProjection_eq_norm_sq
      (evenCentralSoninCarrier a) (U z)
  have hrhs :
      (inner ℂ z (evenSoninBilateralApertureHolonomy a r hr z)).re =
        (inner ℂ z (U (P (V z)))).re - (inner ℂ z (V (P (U z)))).re := by
    change (inner ℂ z ((U * P * V - V * P * U) z)).re = _
    simp only [sub_apply, mul_apply_eq_comp, inner_sub_right, Complex.sub_re]
  change ‖(1 - P) (U z)‖ ^ 2 - ‖(1 - P) (V z)‖ ^ 2 = _
  rw [hrhs, hfirst, hsecond]
  nlinarith [hpU, hpV]

theorem burnol_rpowOrientation_zero_iff (r σ : ℝ) (hr : 1 < r) :
    r ^ (2 * σ - 1) - r ^ (1 - 2 * σ) = 0 ↔ σ = 1 / 2 := by
  constructor
  · intro h
    have heq : r ^ (2 * σ - 1) = r ^ (1 - 2 * σ) := sub_eq_zero.mp h
    have hexp := (Real.strictMono_rpow_of_base_gt_one hr).injective heq
    linarith
  · rintro rfl
    ring_nf

theorem burnol_rpowOrientation_pos_iff (r σ : ℝ) (hr : 1 < r) :
    0 < r ^ (2 * σ - 1) - r ^ (1 - 2 * σ) ↔ 1 / 2 < σ := by
  rw [sub_pos]
  constructor
  · intro h
    have := (Real.strictMono_rpow_of_base_gt_one hr).lt_iff_lt.mp h
    linarith
  · intro h
    apply (Real.strictMono_rpow_of_base_gt_one hr).lt_iff_lt.mpr
    linarith

theorem burnol_rpowOrientation_neg_iff (r σ : ℝ) (hr : 1 < r) :
    r ^ (2 * σ - 1) - r ^ (1 - 2 * σ) < 0 ↔ σ < 1 / 2 := by
  rw [sub_neg]
  constructor
  · intro h
    have := (Real.strictMono_rpow_of_base_gt_one hr).lt_iff_lt.mp h
    linarith
  · intro h
    apply (Real.strictMono_rpow_of_base_gt_one hr).lt_iff_lt.mpr
    linarith

theorem burnol_bilateralApertureDefects_balanced_iff (a r : ℝ) (hr : 1 < r) (w : ℂ) (z za : evenSubspace)
    (hza : za ≠ 0)
    (hplus : evenCentralSoninProjection a
      (ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) z) =
        star (burnolMellinDilationCharacter r w) • za)
    (hminus : evenCentralSoninProjection a
      (evenDilationCLM r (zero_lt_one.trans hr) z) = star ((burnolMellinDilationCharacter r w)⁻¹) • za) :
    ‖burnolApertureDefectMinus a r hr z‖ = ‖burnolApertureDefectPlus a r hr z‖ ↔ w.re = 1 / 2 := by
  have hs := burnol_bilateralApertureDefectEnergy_eq_rpow a r hr w z za hplus hminus
  have hzanorm : 0 < ‖za‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hza)
  constructor
  · intro hnorm
    have hprod :
        (r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re)) * ‖za‖ ^ 2 = 0 := by
      rw [← hs, hnorm]
      ring
    have hcoeff : r ^ (2 * w.re - 1) - r ^ (1 - 2 * w.re) = 0 := by
      exact (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hzanorm)
    exact (burnol_rpowOrientation_zero_iff r w.re hr).mp hcoeff
  · intro hw
    have hcoeff := (burnol_rpowOrientation_zero_iff r w.re hr).mpr hw
    have hsq : ‖burnolApertureDefectMinus a r hr z‖ ^ 2 = ‖burnolApertureDefectPlus a r hr z‖ ^ 2 := by
      nlinarith [hs]
    nlinarith [norm_nonneg (burnolApertureDefectMinus a r hr z), norm_nonneg (burnolApertureDefectPlus a r hr z)]

theorem burnol_bilateralApertureDefects_oriented_right_iff (a r : ℝ) (hr : 1 < r) (w : ℂ)
    (z za : evenSubspace) (hza : za ≠ 0)
    (hplus : evenCentralSoninProjection a
      (ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) z) =
        star (burnolMellinDilationCharacter r w) • za)
    (hminus : evenCentralSoninProjection a
      (evenDilationCLM r (zero_lt_one.trans hr) z) = star ((burnolMellinDilationCharacter r w)⁻¹) • za) :
    ‖burnolApertureDefectPlus a r hr z‖ < ‖burnolApertureDefectMinus a r hr z‖ ↔ 1 / 2 < w.re := by
  have hs := burnol_bilateralApertureDefectEnergy_eq_rpow a r hr w z za hplus hminus
  have hzanorm : 0 < ‖za‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hza)
  rw [← burnol_rpowOrientation_pos_iff r w.re hr]
  constructor <;> intro h
  · have hsq : 0 < ‖burnolApertureDefectMinus a r hr z‖ ^ 2 - ‖burnolApertureDefectPlus a r hr z‖ ^ 2 := by
      nlinarith [norm_nonneg (burnolApertureDefectMinus a r hr z), norm_nonneg (burnolApertureDefectPlus a r hr z)]
    nlinarith [hs]
  · have hsq : 0 < ‖burnolApertureDefectMinus a r hr z‖ ^ 2 - ‖burnolApertureDefectPlus a r hr z‖ ^ 2 := by
      rw [hs]
      positivity
    nlinarith [norm_nonneg (burnolApertureDefectMinus a r hr z), norm_nonneg (burnolApertureDefectPlus a r hr z)]

theorem burnol_bilateralApertureDefects_oriented_left_iff (a r : ℝ) (hr : 1 < r) (w : ℂ)
    (z za : evenSubspace) (hza : za ≠ 0)
    (hplus : evenCentralSoninProjection a
      (ContinuousLinearMap.adjoint (evenDilationCLM r (zero_lt_one.trans hr)) z) =
        star (burnolMellinDilationCharacter r w) • za)
    (hminus : evenCentralSoninProjection a
      (evenDilationCLM r (zero_lt_one.trans hr) z) =
        star ((burnolMellinDilationCharacter r w)⁻¹) • za) :
    ‖burnolApertureDefectMinus a r hr z‖ < ‖burnolApertureDefectPlus a r hr z‖ ↔ w.re < 1 / 2 := by
  have hs := burnol_bilateralApertureDefectEnergy_eq_rpow a r hr w z za hplus hminus
  have hzanorm : 0 < ‖za‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hza)
  rw [← burnol_rpowOrientation_neg_iff r w.re hr]
  constructor <;> intro h
  · have hsq : ‖burnolApertureDefectMinus a r hr z‖ ^ 2 -
        ‖burnolApertureDefectPlus a r hr z‖ ^ 2 < 0 := by
      nlinarith [norm_nonneg (burnolApertureDefectMinus a r hr z),
        norm_nonneg (burnolApertureDefectPlus a r hr z)]
    nlinarith [hs]
  · have hsq : ‖burnolApertureDefectMinus a r hr z‖ ^ 2 -
        ‖burnolApertureDefectPlus a r hr z‖ ^ 2 < 0 := by
      rw [hs]
      exact mul_neg_of_neg_of_pos h hzanorm
    nlinarith [norm_nonneg (burnolApertureDefectMinus a r hr z),
      norm_nonneg (burnolApertureDefectPlus a r hr z)]

end
end RHTower
