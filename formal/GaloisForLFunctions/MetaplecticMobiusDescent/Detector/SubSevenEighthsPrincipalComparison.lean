import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.CompensatedRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.SubSevenEighthsLowProbe

/-!
# Sub-`7/8` Principal Contour Transport and Signal Comparison

Extends the compensated Euler-product bounds, slot error estimates, triple Mellin contour
shifts, and normalized double-residue comparison from the `7/8` half-plane down to
`43/50 ≤ Re s` along the sub-`7/8` physical ray `(X, Y, Z) = (Z^(17/48), Z^(479/1000), Z)` with
total prime-slot exponent `∑ j, ell j = 1001/6000` and signal shift `c = -24749/36000`.
-/

noncomputable section

open MeasureTheory Set Filter Asymptotics Complex
open scoped BigOperators Classical Topology ContDiff SchwartzMap FourierTransform

namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

open Eisenstein CubicJacobi CubicKubota CubicRamified CompletedGauss
open CanonicalRowCompletion CanonicalQuadraticSieve SchwartzPlanePoisson
open HeckeFamily

section SubSevenEighthsEuler

namespace ProbeEuler

/-- Unramified local correction defect bound on `(43/50 ≤ Re x, 9/10 ≤ Re w, 4/25 ≤ Re z)`. -/
theorem sub_unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (43 / 50 : ℝ) ≤ x.re) (hw : (9 / 10 : ℝ) ≤ w.re) (hz : (4 / 25 : ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24 / 25 : ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(53 / 25 : ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9 / 10 : ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(43 / 50 : ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(19 / 25 : ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1 / 2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1 / 2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1 / 2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 :=
    hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9 / 10 : ℝ) ≤ 0)).trans_eq
      (Real.rpow_zero Q))
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17 / 10 : ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (_ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q ^ a') (hbb : b ≤ Q ^ b') (he : a' + b' ≤ -(17 / 10 : ℝ)) : a * b ≤ T := by
    calc
      a * b ≤ Q ^ a' * Q ^ b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q ^ (a' + b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖ * ‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖ * ‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖ * ‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖ * ‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖ * ‖V‖ * ‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q : ℂ)⁻¹ K (-D + W * R) 1
  have hE : ‖P + D‖ ≤ 28 * T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q : ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖ * (1 + ‖W‖) ≤ 2 * T := by
      calc
        _ ≤ ‖R‖ * 2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P - 1‖ ≤ 240 * T
  have hWE : (1 + ‖W‖) * ‖P + D‖ ≤ 56 * T := by
    calc
      _ ≤ 2 * (28 * T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith

lemma sub_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    1 - coordR Q A x z ≠ 0 ∧ 1 - coordV Q z ≠ 0 ∧ 1 - coordD Q eta v x ≠ 0 := by
  have hQ0 : 0 < Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1 / 2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    exact rpow_le_half Q _ hQ (by linarith)
  have hD : ‖coordD Q eta v x‖ ≤ 1 / 2 :=
    (coordD_norm_le Q hQ0 eta v x he hv).trans (rpow_le_half Q _ hQ (by linarith))
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem sub_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => unramifiedClosed Q A eta v x w z) {x : ℂ | 43 / 50 < x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hd := sub_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem sub_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => unramifiedClosed Q A eta v x w z) {w : ℂ | 9 / 10 < w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro w _hw
  have hd := sub_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem sub_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (he : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hx : 43 / 50 ≤ x.re) :
    AnalyticOnNhd ℂ (fun z => unramifiedClosed Q A eta v x w z) {z : ℂ | 4 / 25 < z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hd := sub_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z
    hd.1 hd.2.1 hd.2.2).differentiableWithinAt

end ProbeEuler

namespace ProbePhysical

open ProbeEuler
local notation "Id" => Ideal Eisenstein.O

lemma sub_idealClosedCorrection_bound (η : Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    ‖idealClosedCorrection η P x w z - 1‖ ≤ globalPrimeDefectBound P := by
  apply sub_unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

/-- Global Euler correction bound extended down to `43/50 ≤ Re x`. -/
theorem sub_globalClosedCorrection_bound (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z - 1‖ ≤ 1 / 2 :=
  product_defect_le _ _ hS.summable
    (fun P => sub_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

theorem sub_globalClosedCorrection_analytic_x (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z) {x : ℂ | 43 / 50 < x.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    apply sub_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact sub_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem sub_globalClosedCorrection_analytic_w (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z) {w : ℂ | 9 / 10 < w.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    apply sub_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact sub_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem sub_globalClosedCorrection_analytic_z (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z) {z : ℂ | 4 / 25 < z.re} := by
  apply normalProduct_analytic _ _ _ (isOpen_lt continuous_const Complex.continuous_re) hS.summable
  · intro P
    apply sub_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact sub_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half

end ProbePhysical

namespace PrincipalSignalComparison

open ProbePhysical

theorem sub_sourceCorrection_differentiable (η : Character) (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) :
    DifferentiableOn ℂ (sourceCorrection η E) {s : ℂ | 43 / 50 < s.re} :=
  (sub_globalClosedCorrection_analytic_x η E hE.tail 1 (1 / 6)
    (by norm_num) (by norm_num)).differentiableOn

theorem sub_sourceCorrection_bound (η : Character) (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) (s : ℂ) (hs : 43 / 50 < s.re) :
    ‖sourceCorrection η E s - 1‖ ≤ 1 / 2 :=
  sub_globalClosedCorrection_bound η E hE.tail s 1 (1 / 6) hs.le (by norm_num) (by norm_num)

end PrincipalSignalComparison

end SubSevenEighthsEuler

section SubSevenEighthsSlotEstimate

namespace PrincipalSlotEstimate

open ProbeEuler ProbeLocal

theorem sub_principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) :=
      sub_unramifiedClosed_open_region_bound Q A η 1 s 1 (1 / 6)
        (by linarith) hA hη (by simp) hs (by norm_num) (by norm_num)
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem sub_principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have h := sub_principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem sub_principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (sub_principal_correction_lower_bound hQ hA hη hs))

theorem sub_principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hl := sub_principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr (by linarith)

theorem sub_principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by norm_num)
  refine ⟨hV, ?_, ?_⟩
  · rw [principal_W, ← principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem sub_principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 43 / 50 ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(43 / 50 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(43 / 50 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by
    have h := coordW_norm_le Q hQ0 (1 : ℂ) 1 (by simp)
    norm_num at h
    exact h.trans (by simpa using hpow (-1) 0 (by norm_num))
  have hR : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖coordD Q η 1 s‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hK : ‖coordK Q η s 1‖ ≤ Q ^ (-s.re) := by
    convert coordK_norm_le Q hQ1 η s 1 hη.le using 1
    norm_num
  have hB := principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-(43 / 50 : ℝ)) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(43 / 50 : ℝ)) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-(43 / 50 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤
      Q ^ (-(43 / 50 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by norm_num)
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem sub_principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 43 / 50 ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-(43 / 50 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(43 / 50 : ℝ)) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(43 / 50 : ℝ)) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := sub_principal_marked_error_bounds hQ hA hη hs
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

/-- Compensated principal slot error on `43/50 ≤ Re s`. -/
theorem sub_principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 43 / 50 ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-(43 / 50 : ℝ)) := by
  have hn := sub_principal_correction_ne_zero hQ hA hη.le hs
  have he := sub_principal_replacement_error hQ hA hη hs
  have hi := sub_principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(43 / 50 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem sub_weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 43 / 50 ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-(43 / 50 : ℝ))) * ∑ i ∈ S, w i := by
  apply weighted_slot_error S w _ _ hw
  intro i hi
  apply (sub_principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)

theorem sub_weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 43 / 50 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-(43 / 50 : ℝ))) ^ S.card - 1 := by
  apply fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact sub_weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

theorem sub_weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 43 / 50 ≤ s.re)
    (hsmall : 1440 * P ^ (-(43 / 50 : ℝ)) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-(43 / 50 : ℝ))) :=
  (sub_weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (product_error_linear S.card (by positivity) hsmall)

theorem sub_principalSlot_differentiableAt {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re) :
    DifferentiableAt ℂ (principalSlot Q A η) s := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hQnz : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ0.ne'
  have hg := sub_principal_geometric_bounds hQ hη hs
  have hV := one_sub_ne_zero_of_norm_le_half _ hg.1
  have hD := one_sub_ne_zero_of_norm_le_half _ hg.2.2
  have hR : 1 - coordR Q A s (1 / 6) ≠ 0 := by
    apply one_sub_ne_zero_of_norm_le_half
    apply (coordR_norm_le Q hQ0 A s (1 / 6) hA).trans
    apply rpow_le_half Q _ hQ4
    norm_num
    linarith
  have hr := coordR_differentiable Q hQ0 A (1 / 6)
  have hd := coordD_differentiable Q hQ0 η 1
  have hk := coordK_differentiable Q hQ0 η 1
  have hp : DifferentiableAt ℂ (principalMarked Q A η) s := by
    unfold principalMarked markedFactor
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  have hb : Differentiable ℂ (fun s : ℂ => star η * (Q : ℂ) ^ s) :=
    (differentiable_id.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hQ0.ne'))).const_mul _
  have hrep : DifferentiableAt ℂ (principalReplacement Q A η) s := by
    unfold principalReplacement compensatedReplacement
    fun_prop (disch := first | assumption | exact Or.inl hQnz)
  exact hrep.div (unramifiedClosed_differentiableAt Q hQ0 A η 1 s 1 (1 / 6) hR hV hD)
    (sub_principal_correction_ne_zero hQ hA hη hs)

theorem sub_region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(17 / 10 : ℝ)) :=
      sub_unramifiedClosed_open_region_bound Q A η 1 s w z
        (by linarith) hA hη (by simp) hs (by linarith) (by linarith)
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem sub_region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have h := sub_region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem sub_region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (sub_region_correction_lower_bound hQ hA hη hs hw hz))

theorem sub_region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hl := sub_region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr (by linarith)

theorem sub_region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem sub_region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(43 / 50 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(43 / 50 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := principal_B_norm hQ0 η s hη
  have hg := sub_region_geometric_bounds hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-(43 / 50 : ℝ)) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-(43 / 50 : ℝ)) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-(43 / 50 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-(43 / 50 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem sub_region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-(43 / 50 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := sub_region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-(43 / 50 : ℝ)) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(43 / 50 : ℝ)) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := sub_region_marked_error_bounds hQ hA hη hs hw hz
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

/-- Compensated region slot error on `(43/50 ≤ Re s, 19/20 ≤ Re w, 33/200 ≤ Re z)`. -/
theorem sub_region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-(43 / 50 : ℝ)) := by
  have hn := sub_region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := sub_region_replacement_error hQ hA hη hs hw hz
  have hi := sub_region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(43 / 50 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem sub_region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 43 / 50 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-(43 / 50 : ℝ)) := by
  have he := sub_region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem sub_weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 43 / 50 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-(43 / 50 : ℝ))) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-(43 / 50 : ℝ))) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := sub_region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-(43 / 50 : ℝ)) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

end PrincipalSlotEstimate

end SubSevenEighthsSlotEstimate

section SubSevenEighthsMellinBoundary

namespace ProbeFiniteProductBounds

open ProbePhysical ProbeEuler ProbeLocal PrincipalMellinResidues ProbeMellinBoundary
local notation "Id" => Ideal Eisenstein.O

theorem sub_correction_lower_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    1 / 2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (sub_idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P, hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem sub_correction_ne_zero (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (sub_correction_lower_bound η S hS P hP x w z hx hw hz))

theorem sub_correction_inverse_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := sub_correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma sub_marked_differentiableAt_w (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := sub_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma sub_marked_differentiableAt_z (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := sub_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryIdealGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem sub_local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9 / 10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := sub_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := sub_unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro w hw
  have hmc := sub_marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := sub_correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem sub_local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4 / 25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := sub_unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro z hz
  have hd := sub_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := sub_marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := sub_correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma sub_marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : 43 / 50 ≤ x.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1 / 2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1 / 2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1 - x.re - w.re ≤ 0)).trans_eq
      (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12 * ‖coordR Q A x z‖ * (1 + ‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12 * (1 / 2 : ℝ) * (1 + 1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4 * ‖coordK Q η x w‖ * ‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4 * 1 * (1 / 2 : ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

theorem sub_local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (43 / 50) Bx) (hw : 19 / 20 ≤ w.re)
    (hz : z.re ∈ Icc (33 / 200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val) * (Q : ℂ) ^ x‖ ≤ Q ^ Bx := by
    rw [norm_mul, norm_star, Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0, Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW, one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1 / 2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    sub_marked_bound Q (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := replacement_bound _ _ _ _ _ _ (Q ^ Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := sub_correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ) ^ (z - 1)‖ ≤ Q ^ (Bz - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re, Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv, norm_mul, norm_mul]
  change _ ≤ Q ^ (Bz - 1) * (400 * (1 + Q ^ Bx))
  calc
    _ ≤ Q ^ (Bz - 1) * (200 * (1 + Q ^ Bx) * 2) := by gcongr
    _ = _ := by ring

theorem sub_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9 / 10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (sub_local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem sub_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4 / 25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (sub_local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem sub_slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (43 / 50) Bx) (hw : 19 / 20 ≤ w.re) (hz : z.re ∈ Icc (33 / 200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier, slotBound, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (sub_local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma sub_global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3 / 2 := by
  have hb := sub_globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith

theorem sub_combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9 / 10 < w.re} :=
  (sub_globalClosedCorrection_analytic_w η S hS x z hx hz).mul
    (sub_slot_analytic_w η S hS J T b hT x z hx hz)

theorem sub_combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 43 / 50 ≤ x.re) (hw : 9 / 10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4 / 25 < z.re} :=
  (sub_globalClosedCorrection_analytic_z η S hS x w hx hw).mul
    (sub_slot_analytic_z η S hS J T b hT x w hx hw)

theorem sub_combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (43 / 50) Bx) (hw : 19 / 20 ≤ w.re) (hz : z.re ∈ Icc (33 / 200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3 / 2) * slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (sub_global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (sub_slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem sub_slot_norm_bound_sharp {ι : Type*} (η : Character) (J : Finset ι)
    (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀ j ∈ J, ∀ P ∈ T j, 0 ≤ b j P)
    (hQ : ∀ j ∈ J, ∀ P ∈ T j, Pmin ≤ (Ideal.absNorm P.val : ℝ))
    (hη : ∀ j ∈ J, ∀ P ∈ T j, ‖idealCoeff η P.val‖ = 1) (s w z : ℂ)
    (hs : 43 / 50 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      ∏ j ∈ J, (1 + 1440 * Pmin ^ (-(43 / 50 : ℝ))) *
        ∑ P ∈ T j, b j P * (Ideal.absNorm P.val : ℝ) ^ (z.re - 1) := by
  simp only [slotMultiplier, local_eq_regionSlot, norm_prod]
  apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
  intro j hj
  simpa only [mul_assoc, Complex.ofReal_natCast] using
    PrincipalSlotEstimate.sub_weighted_region_slot_norm (T j) (b j)
      (fun P => (Ideal.absNorm P.val : ℝ))
      (fun P => actualAPhase η (primaryIdealGenerator P.val))
      (fun P => idealCoeff η P.val) s w z Pmin hPmin (hb j hj) (hQ j hj)
      (fun P _ => actualAPhase_norm_le_one η _) (hη j hj) hs hw hz

theorem sub_combined_slot_bound_sharp {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℝ) (Pmin : ℝ)
    (hPmin : 480 ≤ Pmin) (hb : ∀ j ∈ J, ∀ P ∈ T j, 0 ≤ b j P)
    (hQ : ∀ j ∈ J, ∀ P ∈ T j, Pmin ≤ (Ideal.absNorm P.val : ℝ))
    (hη : ∀ j ∈ J, ∀ P ∈ T j, ‖idealCoeff η P.val‖ = 1) (s w z : ℂ)
    (hs : 43 / 50 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖globalClosedCorrection η S s w z * slotMultiplier η J T (fun j P => (b j P : ℂ)) s w z‖ ≤
      (3 / 2) * ∏ j ∈ J, (1 + 1440 * Pmin ^ (-(43 / 50 : ℝ))) *
        ∑ P ∈ T j, b j P * (Ideal.absNorm P.val : ℝ) ^ (z.re - 1) := by
  rw [norm_mul]
  exact mul_le_mul (sub_global_norm_bound η S hS s w z hs (by linarith) (by linarith))
    (sub_slot_norm_bound_sharp η J T b Pmin hPmin hb hQ hη s w z hs hw hz)
    (norm_nonneg _) (by norm_num)

theorem sub_source_w_boundary {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0 < a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal Eisenstein.O) [NeZero M] (X Y Z : ℝ) (hY : 0 < Y)
    (s z : ℂ) (hs : 43 / 50 ≤ s.re) (hz : 33 / 200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1 < cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19 / 20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3 / 2) * slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _)) 0
  · exact (sub_combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9 / 10 : ℝ) < w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero, mul_one] using sub_combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ) + t * I) z s.re z.re ⟨hs, le_rfl⟩ (by simpa using hx.1) ⟨hz, le_rfl⟩

theorem sub_source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0 < a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0 < Y)
    (s z : ℂ) (hs : 43 / 50 ≤ s.re) (hz : 4 / 25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z)
      {w : ℂ | 9 / 10 < w.re} := by
  have hM := compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (sub_combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) * Complex.exp ((s + z - 1) ^ 2) *
      mellin (SchwartzPlanePoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y : ℂ) ^ (w - 1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem sub_source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (s w : ℂ) (hs : 43 / 50 ≤ s.re) (hw : 9 / 10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z)
      {z : ℂ | 4 / 25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (SchwartzPlanePoisson.paperRadialFourier W0))
      {z : ℂ | 4 / 25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono
      (by intro z hz; change 0 < z.re; change (4 / 25 : ℝ) < z.re at hz; linarith)
  have hH := (sub_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y : ℂ) ^ (w - 1) * mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) * Complex.exp ((s + z - 1) ^ 2) *
      mellin (SchwartzPlanePoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

end ProbeFiniteProductBounds

namespace ProbeFiniteProductX

open ProbePhysical ProbeEuler ProbeLocal PrincipalMellinResidues ProbeFiniteProductBounds
local notation "Id" => Ideal Eisenstein.O

lemma sub_marked_differentiableAt_x (η : Character) (P : PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 43 / 50 ≤ x.re) (hz : 4 / 25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := sub_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryIdealGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem sub_local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | 43 / 50 < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := sub_unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hd := sub_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryIdealGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := sub_marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := sub_correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem sub_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset PrimeIdeal) (b : ι → PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | 43 / 50 < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (sub_local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem sub_continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (43 / 50 : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (isOpen_lt continuous_const Complex.continuous_re)
  intro x hx
  have hx' : (43 / 50 : ℝ) < x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta < x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (sub_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (sub_slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem sub_continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0 < Z) (w z : ℂ)
    (hw : 9 / 10 ≤ w.re) (hz : 4 / 25 ≤ z.re) {a c : ℝ}
    (ha : 43 / 50 < a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a ≤ x.re ∧ x.re ≤ c} := by
  apply (sub_continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

end ProbeFiniteProductX

end SubSevenEighthsMellinBoundary

section SubSevenEighthsPrincipalContours

namespace ProbePrincipalContours

open ProbePhysical ProbeEuler ProbeLocal ProbeFiniteProductBounds ProbeFiniteProductX
open PrincipalMellinResidues PrincipalMellinGrowth ProbeMellinBoundary
local notation "Id" => Ideal Eisenstein.O

lemma sub_arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hσ : σ ∈ Icc a Bs) (hξ : ξ ∈ Icc (33 / 200 : ℝ) Bz)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw) (δw δz : ℝ) (hdw : 0 < δw) (hdz : 0 < δz)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C * (1 + |s.im| ^ 2))
    (p : HeightSpace)
    (hwgap : δw ≤ ‖((υ : ℂ) + p.2 * I) - 1‖)
    (hzgap : δz ≤ ‖6 * ((ξ : ℂ) + p.1.2 * I) - 1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ : ℂ) + p.1.1 * I)
      ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I)‖ ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2 ^ 8 := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1 / 2 - ((ξ : ℂ) + p.1.2 * I))
    (show (1 / 2 - ((ξ : ℂ) + p.1.2 * I) : ℂ).re ∈ Icc (1 / 2 - Bz) (1 / 2 - 33 / 200) by
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero]
      norm_num only [show (1 / 2 : ℂ).re = 1 / 2 by norm_num]
      constructor <;> linarith [hξ.1, hξ.2])
  have hz := cpow_le_scaleBound hZ (((σ : ℂ) + p.1.1 * I) + ((ξ : ℂ) + p.1.2 * I) - 1)
    (show ((((σ : ℂ) + p.1.1 * I) + ((ξ : ℂ) + p.1.2 * I) - 1) : ℂ).re ∈
        Icc (a + 33 / 200 - 1) (Bs + Bz - 1) by
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero, one_re]
      constructor <;> linarith [hσ.1, hσ.2, hξ.1, hξ.2])
  have hy := cpow_le_scaleBound hY (((υ : ℂ) + p.2 * I) - 1)
    (show (((υ : ℂ) + p.2 * I) - 1 : ℂ).re ∈ Icc (19 / 20 - 1) (cw - 1) by
      simp only [sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        mul_zero, zero_mul, sub_self, add_zero, one_re]
      constructor <;> linarith [hυ.1, hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ : ℂ) + p.1.1 * I)‖ ≤
      C * height p.1.1 ^ 2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      add_zero, zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := sub_combined_slot_bound η S hS.tail J T b hT ((σ : ℂ) + p.1.1 * I)
    ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2) (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ : ℂ) + p.2 * I ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hυ.1]
  have hw1 : (υ : ℂ) + p.2 * I ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hwgap; linarith
  have hz0 : (6 * ((ξ : ℂ) + p.1.2 * I) : ℂ) ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hξ.1]
  have hz1 : (6 * ((ξ : ℂ) + p.1.2 * I) : ℂ) ≠ 1 := by
    intro h; rw [h, sub_self, norm_zero] at hzgap; linarith
  have hlz0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏ P ∈ S, P)) _ hz0 hz1 _ _ hdz hzgap
    (fixed_principal_z_box_growth (∏ P ∈ S, P) Bz ξ p.1.2 hξ)
  have hlw0 := LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏ P ∈ S, P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏ P ∈ S, P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏ P ∈ S, P)) (6 * ((ξ : ℂ) + p.1.2 * I))‖ ≤
      (zBoxAmplitude (∏ P ∈ S, P) Bz / δz) * height p.1.2 ^ 3 := by
    convert hlz0 using 1 <;> first | rfl | ring
  have hlw : ‖LFunction (fixedPrincipal (∏ P ∈ S, P)) ((υ : ℂ) + p.2 * I)‖ ≤
      (wAmplitude (∏ P ∈ S, P) cw / δw) * height p.2 ^ 3 := by
    convert hlw0 using 1 <;> first | rfl | ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1 / 2 - Bz) (1 / 2 - 33 / 200)).le
  have hsY := (scaleBound_pos Y (19 / 20 - 1) (cw - 1)).le
  have hsZ := (scaleBound_pos Z (a + 33 / 200 - 1) (Bs + Bz - 1)).le
  have hHB := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏ P ∈ S, P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏ P ∈ S, P) hcw).le hdw.le
  calc
    _ = ‖(X : ℂ) ^ (1 / 2 - ((ξ : ℂ) + p.1.2 * I))‖ *
        ‖(Z : ℂ) ^ (((σ : ℂ) + p.1.1 * I) + ((ξ : ℂ) + p.1.2 * I) - 1)‖ *
        ‖(Y : ℂ) ^ (((υ : ℂ) + p.2 * I) - 1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ : ℂ) + p.1.1 * I)‖ *
        ‖globalClosedCorrection η S ((σ : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
          slotMultiplier η J T b ((σ : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) ((υ : ℂ) + p.2 * I)‖ := by
      simp only [arithmeticMultiplier, norm_mul]
    _ ≤ scaleBound X (1 / 2 - Bz) (1 / 2 - 33 / 200) *
        scaleBound Z (a + 33 / 200 - 1) (Bs + Bz - 1) *
        scaleBound Y (19 / 20 - 1) (cw - 1) * (C * height p.1.1 ^ 2) *
        ((3 / 2) * slotBound J T b Bs Bz) *
        ((zBoxAmplitude (∏ P ∈ S, P) Bz / δz) * height p.1.2 ^ 3) *
        ((wAmplitude (∏ P ∈ S, P) cw / δw) * height p.2 ^ 3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _ ≤ scaleBound X (1 / 2 - Bz) (1 / 2 - 33 / 200) *
        scaleBound Z (a + 33 / 200 - 1) (Bs + Bz - 1) *
        scaleBound Y (19 / 20 - 1) (cw - 1) * (C * jointHeight p.1.1 p.1.2 p.2 ^ 2) *
        ((3 / 2) * slotBound J T b Bs Bz) *
        ((zBoxAmplitude (∏ P ∈ S, P) Bz / δz) * jointHeight p.1.1 p.1.2 p.2 ^ 3) *
        ((wAmplitude (∏ P ∈ S, P) cw / δw) * jointHeight p.1.1 p.1.2 p.2 ^ 3) := by
      gcongr <;> first
        | positivity
        | exact height_le_joint_s _ _ _
        | exact height_le_joint_z _ _ _
        | exact height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma sub_arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hσ : σ ∈ Icc a Bs) (hξ : ξ ∈ Icc (33 / 200 : ℝ) Bz)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw) (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C * (1 + |s.im| ^ 2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ : ℂ) + p.1.1 * I)
      ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I)‖ ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ - 1| |6 * ξ - 1| *
        jointHeight p.1.1 p.1.2 p.2 ^ 8 := by
  apply sub_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ - 1| |6 * ξ - 1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6 * ((ξ : ℂ) + p.1.2 * I) - 1)

theorem sub_continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw) (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a : ℂ) + p.1.1 * I)
        ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ : ℂ) + p.2 * I)) heightMeasure := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I))
    (arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ - 1| |6 * ξ - 1|) 8
    (sub_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl, le_rfl⟩ ⟨hξ, le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall
    (fun p => arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

theorem sub_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw) (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a : ℂ) + p.1.1 * I)
        (globalClosedCorrection η S ((a : ℂ) + p.1.1 * I)) (slotMultiplier η J T b ((a : ℂ) + p.1.1 * I))
        ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ : ℂ) + p.2 * I)) heightMeasure := by
  apply (sub_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem sub_continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw) (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) (N : ℕ) :
    ∃ C K : ℝ, 0 ≤ C ∧ 0 < K ∧ ∀ axis : SliceAxis, ∀ R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a : ℂ) + p.1.1 * I)
          ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ : ℂ) + p.2 * I)
      Integrable (fun q : ℝ × ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫ q : ℝ × ℝ, ‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ - 1| |6 * ξ - 1| * K / height R ^ N := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K, hK, hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C, K, hC, hK, ?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I)
  have hm := arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := sub_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl, le_rfl⟩ ⟨hξ, le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl, le_rfl⟩ ξ ⟨le_rfl, le_rfl⟩ υ ⟨le_rfl, le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ - 1| |6 * ξ - 1|)
    (arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q))
    ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G, onLines, arithmetic_profile_eq_source] using hh

theorem sub_source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (he : 0 < e)
    (hs1 : (a : ℂ) + t * I ≠ 1) :
    let s : ℂ := (a : ℂ) + t * I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19 / 20) (fun w =>
      K w ((1 / 6 + e : ℝ) + v * I) * LFunction (fixedSourcePrincipal S hS.prime)
        (6 * ((1 / 6 + e : ℝ) + v * I)) * LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  obtain ⟨_C, _K, _hC, _hK, hslice⟩ := sub_continued_source_slices η S hS J T b hT W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z a (1 / 6 + e) (19 / 20) 3 hX hY hZ ha hβ
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  have hi := (hslice .s t).1
  have hs0 : (a : ℂ) + t * I ≠ 0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hpair : Integrable (fun q : ℝ × ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a : ℂ) + t * I)
        (globalClosedCorrection η S ((a : ℂ) + t * I)) (slotMultiplier η J T b ((a : ℂ) + t * I))
        ((19 / 20 : ℝ) + q.2 * I) ((1 / 6 + e : ℝ) + q.1 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((1 / 6 + e : ℝ) + q.1 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((19 / 20 : ℝ) + q.2 * I)) (volume.prod volume) := by
    simpa only [sliceMap, continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

theorem sub_source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0 < a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (X Y Z : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (s : ℂ) (hs : 43 / 50 ≤ s.re) (hη : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0 < e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z)) (33 / 200) (1 / 6 + e) := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏ P ∈ S, P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3 / 2) * slotBound J T b s.re (1 / 6 + e)) (AL := zBoxAmplitude (∏ P ∈ S, P) (1 / 6 + e))
    he (mul_nonneg (by norm_num) (slotBound_nonneg J T b _ _))
    (zBoxAmplitude_nonneg _ _) 0 3
  · exact (sub_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4 / 25 : ℝ) < z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero, mul_one] using sub_combined_slot_bound η S hS.tail J T b hT s
      1 ((x : ℂ) + t * I) s.re (1 / 6 + e) ⟨hs, le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact fixed_principal_z_box_growth (∏ P ∈ S, P) (1 / 6 + e) x t hx

theorem sub_source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hcw : 1 < cw) (he : 0 < e)
    (hs1 : (a : ℂ) + t * I ≠ 1) :
    let s : ℂ := (a : ℂ) + t * I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1 / 6 + e) (fun z => verticalIntegral cw
      (fun w => K w z * LFunction π (6 * z) * LFunction π w)) =
    verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
      (fun w => K w z * LFunction π (6 * z) * LFunction π w)) +
    HeckeReciprocal.regularizedL π 1 * verticalIntegral (33 / 200) (fun z => K 1 z * LFunction π (6 * z)) +
    (HeckeReciprocal.regularizedL π 1) ^ 2 / 6 * K 1 (1 / 6) := by
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (43 / 50 : ℝ) ≤ (((a : ℂ) + t * I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta < (((a : ℂ) + t * I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := sub_source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a : ℂ) + t * I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (sub_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a : ℂ) + t * I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9 / 10 : ℝ) < w.re
    linarith [hw.1]
  · intro z hz
    have hh := ProbeFiniteProductBounds.sub_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY ((a : ℂ) + t * I) z hs (by rw [hz]; linarith) hη hcw
    convert boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6 * z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal, fixedPrincipal]
    ring
  · apply (sub_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a : ℂ) + t * I) 1 hs (by norm_num)).mono
    intro z hz
    change (4 / 25 : ℝ) < z.re
    linarith [hz.1]
  · exact hzb
  · exact sub_source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem sub_source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hcw : 1 < cw) (he : 0 < e) :
    ∀ᵐ t : ℝ, let s : ℂ := (a : ℂ) + t * I
      let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s)
      let π := fixedSourcePrincipal S hS.prime
      verticalIntegral (1 / 6 + e) (fun z => verticalIntegral cw
        (fun w => K w z * LFunction π (6 * z) * LFunction π w)) =
      verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
        (fun w => K w z * LFunction π (6 * z) * LFunction π w)) +
      HeckeReciprocal.regularizedL π 1 * verticalIntegral (33 / 200) (fun z => K 1 z * LFunction π (6 * z)) +
      (HeckeReciprocal.regularizedL π 1) ^ 2 / 6 * K 1 (1 / 6) := by
  filter_upwards [Measure.ae_ne volume (0 : ℝ)] with t ht
  apply sub_source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

lemma sub_residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (X Z a ξ C : ℝ) (hX : 0 < X) (hZ : 0 < Z) (ha : 43 / 50 ≤ a) (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1)
    (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C * (1 + |s.im| ^ 2))
    (q : ℝ × ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a : ℂ) + q.1 * I) ((ξ : ℂ) + q.2 * I)‖ ≤
      residueAmplitude S J T b X Z a ξ C * jointHeight q.1 q.2 0 ^ 5 := by
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a : ℂ) + q.1 * I)‖ ≤
      C * height q.1 ^ 2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      add_zero, zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := sub_combined_slot_bound η S hS.tail J T b hT ((a : ℂ) + q.1 * I) 1 ((ξ : ℂ) + q.2 * I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := fixed_principal_z_bound (∏ P ∈ S, P) ξ ξ q.2 ⟨hξ, le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1 / 2 - ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a + ξ - 1)).le
  have hHB := mul_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2) (slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (zBoxAmplitude_nonneg (∏ P ∈ S, P) ξ) (abs_nonneg (6 * ξ - 1))
  have hq1 := (height_pos q.1).le
  have hq2 := (height_pos q.2).le
  have hqJ := (jointHeight_pos q.1 q.2 0).le
  calc
    _ = X ^ (1 / 2 - ξ) * Z ^ (a + ξ - 1) *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a : ℂ) + q.1 * I)‖ *
        ‖globalClosedCorrection η S ((a : ℂ) + q.1 * I) 1 ((ξ : ℂ) + q.2 * I) *
          slotMultiplier η J T b ((a : ℂ) + q.1 * I) 1 ((ξ : ℂ) + q.2 * I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + q.2 * I))‖ := by
      simp only [residueArithmetic, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      norm_num
    _ ≤ X ^ (1 / 2 - ξ) * Z ^ (a + ξ - 1) * (C * height q.1 ^ 2) *
        ((3 / 2) * slotBound J T b a ξ) *
        ((zBoxAmplitude (∏ P ∈ S, P) ξ / |6 * ξ - 1|) * height q.2 ^ 3) := by
      gcongr
      first | positivity | exact hL
    _ ≤ X ^ (1 / 2 - ξ) * Z ^ (a + ξ - 1) * (C * jointHeight q.1 q.2 0 ^ 2) *
        ((3 / 2) * slotBound J T b a ξ) *
        ((zBoxAmplitude (∏ P ∈ S, P) ξ / |6 * ξ - 1|) * jointHeight q.1 q.2 0 ^ 3) := by
      gcongr <;> first | positivity | exact height_le_joint_s _ _ _ | exact height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

theorem sub_continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) :
    Integrable (fun q : ℝ × ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a : ℂ) + q.1 * I) 1 ((ξ : ℂ) + q.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + q.2 * I))) (volume.prod volume) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨_K, _hK, hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) 5 0
  have hm := residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hb := sub_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl, le_rfl⟩ ξ ⟨le_rfl, le_rfl⟩ 1 ⟨le_rfl, le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ × ℝ => residueArithmetic η S hS.prime J T b X Z ((a : ℂ) + q.1 * I) ((ξ : ℂ) + q.2 * I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap, onLines, ofReal_one, ofReal_zero, zero_mul, add_zero] using
    residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a : ℂ) + q.1 * I) ((ξ : ℂ) + q.2 * I)

theorem sub_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) :
    Integrable (fun q : ℝ × ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a : ℂ) + q.1 * I) (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
      (slotMultiplier η J T b ((a : ℂ) + q.1 * I))
      1 ((ξ : ℂ) + q.2 * I) * LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + q.2 * I)))
      (volume.prod volume) := by
  apply (sub_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume, q.1 ≠ 0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0 : ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a : ℂ) + q.1 * I ≠ 0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a : ℂ) + q.1 * I ≠ 1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem sub_source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ)
    (hcw : 1 < cw) (hυ : υ ∈ Icc (19 / 20 : ℝ) cw) (hξ1 : 6 * ξ ≠ 1) (hυ1 : υ ≠ 1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a : ℂ) + t * I)
        (globalClosedCorrection η S ((a : ℂ) + t * I)) (slotMultiplier η J T b ((a : ℂ) + t * I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * z) * LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hi := sub_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral, integral_const_mul, mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul
      (((1 / (2 * Real.pi) : ℝ) : ℂ))).const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

theorem sub_residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξ : 33 / 200 ≤ ξ) (hξ1 : 6 * ξ ≠ 1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a : ℂ) + t * I)
        (globalClosedCorrection η S ((a : ℂ) + t * I)) (slotMultiplier η J T b ((a : ℂ) + t * I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * z))) := by
  have hi := sub_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))

theorem sub_source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hcw : 1 < cw) (he : 0 < e) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral cw
      (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
      (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) +
    R * verticalIntegral a (fun s => verticalIntegral (33 / 200) (fun z => K s 1 z * LFunction π (6 * z))) +
    R ^ 2 / 6 * verticalIntegral a (fun s => K s 1 (1 / 6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  let R := HeckeReciprocal.regularizedL π 1
  let A := fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral cw
    (fun w => K s w z * LFunction π (6 * z) * LFunction π w))
  let B := fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
    (fun w => K s w z * LFunction π (6 * z) * LFunction π w))
  let D := fun s => R * verticalIntegral (33 / 200) (fun z => K s 1 z * LFunction π (6 * z))
  let E := fun s => R ^ 2 / 6 * K s 1 (1 / 6)
  have hA : Integrable (fun t : ℝ => A ((a : ℂ) + t * I)) :=
    sub_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1 / 6 + e) cw cw hX hY hZ ha hβ (by linarith) hcw ⟨by linarith, le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a : ℂ) + t * I)) :=
    sub_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1 / 6 + e) (19 / 20) cw hX hY hZ ha hβ (by linarith) hcw ⟨le_rfl, by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a : ℂ) + t * I)) :=
    (sub_residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33 / 200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐ t : ℝ, A ((a : ℂ) + t * I) =
      B ((a : ℂ) + t * I) + D ((a : ℂ) + t * I) + E ((a : ℂ) + t * I) :=
    sub_source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e cw hX hY hZ ha hβ hcw he
  have hE : Integrable (fun t : ℝ => E ((a : ℂ) + t * I)) := by
    apply ((hA.sub hB).sub hD).congr
    filter_upwards [hp] with t ht
    change A ((a : ℂ) + t * I) - B ((a : ℂ) + t * I) - D ((a : ℂ) + t * I) = E ((a : ℂ) + t * I)
    rw [ht]
    ring
  have heq : verticalIntegral a A = verticalIntegral a (fun s => B s + D s + E s) := by
    unfold verticalIntegral
    congr 1
    exact integral_congr_ae hp
  rw [verticalIntegral_add a _ _ (hB.add hD) hE, verticalIntegral_add a _ _ hB hD] at heq
  change verticalIntegral a A = verticalIntegral a B + R * verticalIntegral a _ + R ^ 2 / 6 * verticalIntegral a _
  rw [heq]
  simp only [D, E, verticalIntegral, integral_const_mul]
  ring

end ProbePrincipalContours

namespace ProbePrincipalTransport

open ProbePhysical ProbeEuler ProbeLocal ProbeFiniteProductBounds ProbeFiniteProductX
open PrincipalMellinResidues PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

theorem sub_principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hβ : HeckeZeroSupremum.beta < a) (hξlo : 1 / 6 < ξlo) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ σ ∈ Icc a 3, ∀ ξ ∈ Icc ξlo 2, ∀ p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ : ℂ) + p.1.1 * I) ((3 : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((3 : ℂ) + p.2 * I)‖ ≤ A * jointEnvelope 8 p := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D, hD, hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith) 10
  obtain ⟨E, hE, he⟩ := compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6 * ξlo - 1)
  let B := realGaussianBound a 3 ξlo 2 * 2 ^ 8 * D * E
  have hA : 0 ≤ A := arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6 * ξlo - 1)
    (by norm_num) hC (by norm_num) (by linarith)
  have hB : 0 ≤ B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A * B, mul_nonneg hA hB, ?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ ∈ Icc (33 / 200 : ℝ) 2 := ⟨by linarith [hξ.1], hξ.2⟩
  have hw : (2 : ℝ) ≤ ‖((3 : ℂ) + p.2 * I) - 1‖ := by
    simpa only [Complex.ofReal_ofNat, Complex.ofReal_one,
      show |(3 : ℝ) - 1| = 2 by norm_num] using pole_distance_vertical 1 3 p.2
  have hz : 6 * ξlo - 1 ≤ ‖6 * ((ξ : ℂ) + p.1.2 * I) - 1‖ := by
    have h := Complex.abs_re_le_norm (6 * ((ξ : ℂ) + p.1.2 * I) - 1)
    have hh : 0 ≤ 6 * ξ - 1 := by linarith [hξ.1]
    simp only [sub_re, mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im, mul_zero,
      zero_mul, sub_zero, add_zero, one_re] at h
    norm_num only [show (6 : ℂ).re = 6 by norm_num, show (6 : ℂ).im = 0 by norm_num,
      zero_mul, sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [hξ.1]) h
  have hb := sub_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6 * ξlo - 1)
    (by norm_num) (by linarith) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl, le_rfl⟩) p
  rw [← arithmetic_profile_eq_source, norm_mul]
  calc
    _ ≤ (A * jointHeight p.1.1 p.1.2 p.2 ^ 8) * ‖profile W0 W1
        ((σ : ℂ) + p.1.1 * I) ((3 : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A * (jointHeight p.1.1 p.1.2 p.2 ^ 8 * ‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines, ofReal_ofNat]; ring
    _ ≤ A * (B * jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem sub_continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3 : ℂ) + u * I) ((ξ : ℂ) + v * I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + v * I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((3 : ℂ) + u * I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3 : ℂ) + u * I) ((ξ : ℂ) + v * I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + v * I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((3 : ℂ) + u * I)) := by
  obtain ⟨A, _hA, hb⟩ := sub_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := sub_continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3 : ℂ) + u * I) ((ξ : ℂ) + v * I) (by norm_num)
    (by simpa using (show (4 / 25 : ℝ) ≤ ξ by linarith)) ha hβ (c := 3)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A := A * cauchy v * cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl, hξ2⟩ ((t, v), u)
  simpa only [jointEnvelope, Prod.fst, Prod.snd, mul_assoc, mul_left_comm, mul_comm] using h

lemma sub_continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (s w : ℂ) (hs : 43 / 50 ≤ s.re) (hw : 9 / 10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4 / 25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (SchwartzPlanePoisson.paperRadialFourier W0))
      {z : ℂ | 4 / 25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono
      (by intro z hz; change 0 < z.re; change (4 / 25 : ℝ) < z.re at hz; linarith)
  have hH := (sub_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X : ℂ) ≠ 0 := by exact_mod_cast hX.ne'
  have hnZ : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z) =
    (fun z => ((Y : ℂ) ^ (w - 1) * mellin W1 w *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s) *
      (X : ℂ) ^ (1 / 2 - z) * (Z : ℂ) ^ (s + z - 1) * Complex.exp ((s + z - 1) ^ 2) *
      mellin (SchwartzPlanePoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma sub_continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0 < X) (hZ : 0 < Z)
    (s w : ℂ) (hs : 43 / 50 ≤ s.re) (hw : 9 / 10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
      LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1 / 6 < z.re} := by
  have hK := sub_continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4 / 25 : ℝ) < z.re; change (1 / 6 : ℝ) < z.re at hz; linarith)).mul ?_).mul_const
  intro z hz
  have h0 : (6 * z : ℂ) ≠ 0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1 / 6 : ℝ) < z.re at hz; linarith
  have h1 : (6 * z : ℂ) ≠ 1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1 / 6 : ℝ) < z.re at hz; linarith
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem sub_continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a)
    (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a : ℂ) + t * I) ((3 : ℂ) + u * I) z *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
        LFunction (fixedSourcePrincipal S hS.prime) ((3 : ℂ) + u * I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a : ℂ) + t * I) ((3 : ℂ) + u * I) z *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * z) *
        LFunction (fixedSourcePrincipal S hS.prime) ((3 : ℂ) + u * I)) := by
  obtain ⟨A, _hA, hb⟩ := sub_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := sub_continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a : ℂ) + t * I) ((3 : ℂ) + u * I) (by simpa using ha) (by norm_num)
  apply verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1 / 6 : ℝ) < z.re; exact hξ.trans_le hz.1)) (A := A * cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl, ha3⟩ ζ hζ ((t, v), u)
  calc
    _ ≤ A * (gaussianMoment 8 (t + v) * cauchy v * cauchy u) := h
    _ ≤ A * (gaussianMoment 8 (t + v) * 1 * cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t + v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

theorem sub_continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a) (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z) * LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) =
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6 * z) * LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := sub_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  have hi3 := sub_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) = _
  rw [verticalIntegral_triple_reverse F a ξ 3 hiA, verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply verticalIntegral_congr_line
  intro u
  apply verticalIntegral_congr_line
  intro v
  exact sub_continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem sub_continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a) (hξ : 1 / 6 < ξ) (hξ2 : ξ ≤ 2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * z) * LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) =
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6 * z) * LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨_Cξ, _Kξ, _hCξ, _hKξ, hξi⟩ := sub_continued_source_slices η S hS J T b hT W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z a ξ 3 3 hX hY hZ ha hβ
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  obtain ⟨_C2, _K2, _hC2, _hK2, h2i⟩ := sub_continued_source_slices η S hS J T b hT W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z a 2 3 3 hX hY hZ ha hβ
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) = _
  apply verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [verticalIntegral_swap (fun z w => F ((a : ℂ) + t * I) w z) ξ 3 hiξ,
    verticalIntegral_swap (fun z w => F ((a : ℂ) + t * I) w z) 2 3 hi2]
  apply verticalIntegral_congr_line
  intro u
  exact sub_continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

theorem sub_source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a) (he : 0 < e) (he2 : e ≤ 11 / 6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral 3
      (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) := by
  dsimp only
  rw [← continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ← continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1 / 6 + e) 3]
  have hx := sub_continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := sub_continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1 / 6 + e) hX hY hZ ha.le ha3 hβ (by linarith) (by linarith)
  exact hx.symm.trans hz.symm

theorem sub_source_initial_joint_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset PrimeIdeal)
    (b : ι → PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a) (he : 0 < e) (he2 : e ≤ 11 / 6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 3) * (∫ p : HeightSpace,
      K ((3 : ℂ) + p.1.1 * I) ((3 : ℂ) + p.2 * I) ((2 : ℂ) + p.1.2 * I) *
        LFunction π (6 * ((2 : ℂ) + p.1.2 * I)) * LFunction π ((3 : ℂ) + p.2 * I) ∂heightMeasure) =
    verticalIntegral a (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
      (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) +
    R * verticalIntegral a (fun s => verticalIntegral (33 / 200) (fun z => K s 1 z * LFunction π (6 * z))) +
    R ^ 2 / 6 * verticalIntegral a (fun s => K s 1 (1 / 6)) := by
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  have hh := (sub_source_initial_placement η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2).trans
    (sub_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e 3 hX hY hZ ha.le hβ (by norm_num) he)
  have hf := (source_joint_fubini η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 2 3 3 hX hY hZ (by norm_num) (hβ.trans_le ha3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1
  have hi : (((1 / (2 * Real.pi) : ℝ) : ℂ) ^ 3) * (∫ p : HeightSpace,
      K ((3 : ℂ) + p.1.1 * I) ((3 : ℂ) + p.2 * I) ((2 : ℂ) + p.1.2 * I) *
        LFunction π (6 * ((2 : ℂ) + p.1.2 * I)) * LFunction π ((3 : ℂ) + p.2 * I) ∂heightMeasure) =
      verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
        (fun w => K s w z * LFunction π (6 * z) * LFunction π w))) := by
    dsimp [K, π]
    simp only [ofReal_ofNat] at hf
    rw [hf]
    simp only [verticalIntegral, integral_const_mul, ofReal_ofNat]
    ring
  exact hi.trans hh

end ProbePrincipalTransport

namespace ProbePrincipalRemainderBounds

open ProbePhysical ProbeEuler ProbeLocal ProbeFiniteProductBounds ProbeFiniteProductX
open PrincipalMellinResidues PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

def subSlotConstant {ι : Type*} (J : Finset ι) (c d B ξ : ℝ) : ℝ :=
  (3 / 2) * ∏ _j ∈ J, (1 + 1440 * (480 : ℝ) ^ (-(43 / 50 : ℝ))) * (128 * d * B * c ^ (ξ - 1))

lemma subSlotConstant_nonneg {ι : Type*} (J : Finset ι) {c d B ξ : ℝ}
    (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) : 0 ≤ subSlotConstant J c d B ξ := by
  have hd0 : 0 ≤ d := hc.le.trans hd
  unfold subSlotConstant
  apply mul_nonneg (by norm_num)
  exact Finset.prod_nonneg (fun _ _ => by positivity)

theorem sub_window_sharp_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : CorrectionTail S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
    (W : ι → ℝ → ℝ) (hW : ∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B)
    (hsupp : ∀ j ∈ J, Function.support (W j) ⊆ Icc c d)
    (P : ι → ℝ) (hP : ∀ j ∈ J, 0 < P j)
    (hthreshold : ∀ j ∈ J, 480 ≤ c * P j)
    (hmod : ∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * P j)
    (T : ι → Finset PrimeIdeal) (s w z : ℂ)
    (hs : 43 / 50 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : z.re = ξ) (hzlo : 33 / 200 ≤ ξ) :
    ‖globalClosedCorrection η S s w z *
      windowMultiplier η J T (fun j x => (W j x : ℂ)) P s w z‖ ≤
      subSlotConstant J c d B ξ * ∏ j ∈ J, (P j) ^ ξ := by
  let A (j : ι) := (T j).filter (fun p => W j ((Ideal.absNorm p.val : ℝ) / P j) ≠ 0)
  have hA (j : ι) (hj : j ∈ J) (p : PrimeIdeal) (hp : p ∈ A j) : c * P j ≤ (Ideal.absNorm p.val : ℝ) :=
    (le_div_iff₀ (hP j hj)).mp ((hsupp j hj) (Finset.mem_filter.mp hp).2).1
  have he : windowMultiplier η J T (fun j x => (W j x : ℂ)) P s w z =
      slotMultiplier η J A (fun j p => (W j ((Ideal.absNorm p.val : ℝ) / P j) : ℂ)) s w z := by
    unfold windowMultiplier slotMultiplier
    apply Finset.prod_congr rfl
    intro j _hj
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hn
    have hh : W j ((Ideal.absNorm p.val : ℝ) / P j) = 0 := by
      by_contra h; exact hn (Finset.mem_filter.mpr ⟨hp, h⟩)
    simp [hh]
  rw [he]
  have h := sub_combined_slot_bound_sharp η S hS J A
    (fun j p => W j ((Ideal.absNorm p.val : ℝ) / P j)) 480 (by norm_num)
    (fun j hj p _ => (hW j hj _).1)
    (fun j hj p hp => (hthreshold j hj).trans (hA j hj p hp))
    (fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero
      (PrincipalSignalComparison.prime_coprime_of_norm_gt η p (by
        exact_mod_cast (hmod j hj).trans_le (hA j hj p hp)))) s w z hs hw (by rw [hz]; exact hzlo)
  apply h.trans
  simp only [hz]
  calc
    _ ≤ (3 / 2) * ∏ j ∈ J, (1 + 1440 * (480 : ℝ) ^ (-(43 / 50 : ℝ))) *
        ((128 * d * B * c ^ (ξ - 1)) * (P j) ^ ξ) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.prod_le_prod
      · intro j hj; apply mul_nonneg (by positivity)
        exact Finset.sum_nonneg (fun p _ =>
          mul_nonneg (hW j hj _).1 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      · intro j hj
        exact mul_le_mul_of_nonneg_left (active_prime_sum_bound (A j) (W j) c d B (P j) ξ
          hc hd hB (hP j hj) (hthreshold j hj) hξ (hW j hj) (hsupp j hj)) (by positivity)
    _ = _ := by simp only [subSlotConstant, ← mul_assoc, Finset.prod_mul_distrib]

lemma sub_continued_source_sharp_pointwise {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
    (W : ι → ℝ → ℝ) (hW : ∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B)
    (hsupp : ∀ j ∈ J, Function.support (W j) ⊆ Icc c d)
    (P : ι → ℝ) (hP : ∀ j ∈ J, 0 < P j) (hthreshold : ∀ j ∈ J, 480 ≤ c * P j)
    (hmod : ∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * P j) (T : ι → Finset PrimeIdeal)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hυ : 19 / 20 ≤ υ) (hzlo : 33 / 200 ≤ ξ) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C * (1 + |s.im| ^ 2))
    (t v u : ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p => (W j ((Ideal.absNorm p.val : ℝ) / P j) : ℂ)) W0 W1 X Y Z
      ((a : ℂ) + t * I) ((υ : ℂ) + u * I) ((ξ : ℂ) + v * I)‖ ≤
    scalePower X Y Z a ξ υ * (C * subSlotConstant J c d B ξ) * (∏ j ∈ J, (P j) ^ ξ) *
      jointHeight t v u ^ 2 * ‖onLines W0 W1 a ξ υ ((t, v), u)‖ := by
  have hslot := sub_window_sharp_bound η S hS.tail J c d B ξ hc hd hB hξ W hW hsupp
    P hP hthreshold hmod T ((a : ℂ) + t * I) ((υ : ℂ) + u * I) ((ξ : ℂ) + v * I)
    (by simpa using ha) (by simpa using hυ) (by simp) hzlo
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a : ℂ) + t * I)‖ ≤
      C * jointHeight t v u ^ 2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      add_zero, zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    have hh := height_le_joint_s t v u
    have hh0 := height_pos t
    unfold height jointHeight at *
    nlinarith [abs_nonneg t, abs_nonneg v, abs_nonneg u]
  have hx : ‖(X : ℂ) ^ (1 / 2 - ((ξ : ℂ) + v * I))‖ = X ^ (1 / 2 - ξ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]; congr 1; simp
  have hz : ‖(Z : ℂ) ^ (((a : ℂ) + t * I) + ((ξ : ℂ) + v * I) - 1)‖ = Z ^ (a + ξ - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hZ]; congr 1; simp
  have hy : ‖(Y : ℂ) ^ (((υ : ℂ) + u * I) - 1)‖ = Y ^ (υ - 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]; congr 1; simp
  have he : continuedSourceMultiplier η S hS.prime J T
      (fun j p => (W j ((Ideal.absNorm p.val : ℝ) / P j) : ℂ)) W0 W1 X Y Z
      ((a : ℂ) + t * I) ((υ : ℂ) + u * I) ((ξ : ℂ) + v * I) =
      (X : ℂ) ^ (1 / 2 - ((ξ : ℂ) + v * I)) * (Z : ℂ) ^ (((a : ℂ) + t * I) + ((ξ : ℂ) + v * I) - 1) *
      (Y : ℂ) ^ (((υ : ℂ) + u * I) - 1) *
      HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a : ℂ) + t * I) *
      (globalClosedCorrection η S ((a : ℂ) + t * I) ((υ : ℂ) + u * I) ((ξ : ℂ) + v * I) *
        windowMultiplier η J T (fun j x => (W j x : ℂ)) P
          ((a : ℂ) + t * I) ((υ : ℂ) + u * I) ((ξ : ℂ) + v * I)) *
      onLines W0 W1 a ξ υ ((t, v), u) := by
    unfold continuedSourceMultiplier windowMultiplier onLines profile; ring
  rw [he, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, hx, hz, hy]
  calc
    _ ≤ X ^ (1 / 2 - ξ) * Z ^ (a + ξ - 1) * Y ^ (υ - 1) * (C * jointHeight t v u ^ 2) *
      (subSlotConstant J c d B ξ * (∏ j ∈ J, (P j) ^ ξ)) * ‖onLines W0 W1 a ξ υ ((t, v), u)‖ := by
      gcongr
    _ = _ := by unfold scalePower; ring

lemma sub_full_sharp_pointwise {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
    (W : ι → ℝ → ℝ) (hW : ∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B)
    (hsupp : ∀ j ∈ J, Function.support (W j) ⊆ Icc c d)
    (P : ι → ℝ) (hP : ∀ j ∈ J, 0 < P j) (hthreshold : ∀ j ∈ J, 480 ≤ c * P j)
    (hmod : ∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * P j) (T : ι → Finset PrimeIdeal)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a υ C : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hυ : 19 / 20 ≤ υ) (hzlo : 33 / 200 ≤ ξ) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C * (1 + |s.im| ^ 2))
    (hυhi : υ ≤ 2) (hυ1 : υ ≠ 1) (hξ1 : 6 * ξ ≠ 1) (p : HeightSpace) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p => (W j ((Ideal.absNorm p.val : ℝ) / P j) : ℂ)) W0 W1 X Y Z
      ((a : ℂ) + p.1.1 * I) ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ : ℂ) + p.2 * I)‖ ≤
    (C * subSlotConstant J c d B ξ * (zBoxAmplitude (∏ q ∈ S, q) 1 / |6 * ξ - 1|) *
      (wAmplitude (∏ q ∈ S, q) 2 / |υ - 1|)) *
      (scalePower X Y Z a ξ υ * (∏ j ∈ J, (P j) ^ ξ)) *
      (jointHeight p.1.1 p.1.2 p.2 ^ 8 * ‖onLines W0 W1 a ξ υ p‖) := by
  let : NeZero (∏ q ∈ S, q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := sub_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a υ C hX hY hZ ha hυ hzlo hC hR p.1.1 p.1.2 p.2
  have hlz := fixed_principal_z_bound (∏ q ∈ S, q) 1 ξ p.1.2 ⟨hzlo, hξ⟩ hξ1
  have hlw := fixed_principal_w_bound (∏ q ∈ S, q) (by norm_num : (1 : ℝ) < 2) ⟨hυ, hυhi⟩ hυ1 p.2
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏ q ∈ S, q) 1) (abs_nonneg (6 * ξ - 1))
  have hAW := div_nonneg (wAmplitude_pos (∏ q ∈ S, q) (by norm_num : (1 : ℝ) < 2)).le (abs_nonneg (υ - 1))
  have hmass : 0 ≤ ∏ j ∈ J, (P j) ^ ξ := Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hP j hj).le _)
  have hslot := subSlotConstant_nonneg J (ξ := ξ) hc hd hB
  have hs := scalePower_nonneg (a := a) (ξ := ξ) (υ := υ) hX.le hY.le hZ.le
  have hv := (height_pos p.1.2).le
  have hu := (height_pos p.2).le
  have hj := (jointHeight_pos p.1.1 p.1.2 p.2).le
  rw [norm_mul, norm_mul]
  calc
    _ ≤ (scalePower X Y Z a ξ υ * (C * subSlotConstant J c d B ξ) * (∏ j ∈ J, (P j) ^ ξ) *
      jointHeight p.1.1 p.1.2 p.2 ^ 2 * ‖onLines W0 W1 a ξ υ p‖) *
      ((zBoxAmplitude (∏ q ∈ S, q) 1 / |6 * ξ - 1|) * height p.1.2 ^ 3) *
      ((wAmplitude (∏ q ∈ S, q) 2 / |υ - 1|) * height p.2 ^ 3) := by
      gcongr <;> first | positivity | exact h0 | exact hlz | exact hlw
    _ ≤ (scalePower X Y Z a ξ υ * (C * subSlotConstant J c d B ξ) * (∏ j ∈ J, (P j) ^ ξ) *
      jointHeight p.1.1 p.1.2 p.2 ^ 2 * ‖onLines W0 W1 a ξ υ p‖) *
      ((zBoxAmplitude (∏ q ∈ S, q) 1 / |6 * ξ - 1|) * jointHeight p.1.1 p.1.2 p.2 ^ 3) *
      ((wAmplitude (∏ q ∈ S, q) 2 / |υ - 1|) * jointHeight p.1.1 p.1.2 p.2 ^ 3) := by
      gcongr <;> first | positivity | exact height_le_joint_z _ _ _ | exact height_le_joint_w _ _ _
    _ = _ := by ring

lemma sub_residue_sharp_pointwise {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (c d B ξ : ℝ)
    (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) (hξ : ξ ≤ 1)
    (W : ι → ℝ → ℝ) (hW : ∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B)
    (hsupp : ∀ j ∈ J, Function.support (W j) ⊆ Icc c d)
    (P : ι → ℝ) (hP : ∀ j ∈ J, 0 < P j) (hthreshold : ∀ j ∈ J, 480 ≤ c * P j)
    (hmod : ∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * P j) (T : ι → Finset PrimeIdeal)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a C : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 ≤ a) (hzlo : 33 / 200 ≤ ξ) (hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re →
      ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖ ≤ C * (1 + |s.im| ^ 2))
    (hξ1 : 6 * ξ ≠ 1) (q : ℝ × ℝ) :
    ‖continuedSourceMultiplier η S hS.prime J T
      (fun j p => (W j ((Ideal.absNorm p.val : ℝ) / P j) : ℂ)) W0 W1 X Y Z
      ((a : ℂ) + q.1 * I) 1 ((ξ : ℂ) + q.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + q.2 * I))‖ ≤
    (C * subSlotConstant J c d B ξ * (zBoxAmplitude (∏ p ∈ S, p) 1 / |6 * ξ - 1|)) *
      (scalePower X Y Z a ξ 1 * (∏ j ∈ J, (P j) ^ ξ)) *
      (jointHeight q.1 q.2 0 ^ 5 * ‖onLines W0 W1 a ξ 1 ((q.1, q.2), 0)‖) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have h0 := sub_continued_source_sharp_pointwise η S hS J c d B ξ hc hd hB hξ W hW hsupp P hP
    hthreshold hmod T W0 W1 X Y Z a 1 C hX hY hZ ha (by norm_num) hzlo hC hR q.1 q.2 0
  simp only [ofReal_one, ofReal_zero, zero_mul, add_zero] at h0
  have hlz := fixed_principal_z_bound (∏ p ∈ S, p) 1 ξ q.2 ⟨hzlo, hξ⟩ hξ1
  have hAZ := div_nonneg (zBoxAmplitude_nonneg (∏ p ∈ S, p) 1) (abs_nonneg (6 * ξ - 1))
  have hmass : 0 ≤ ∏ j ∈ J, (P j) ^ ξ := Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hP j hj).le _)
  have hslot := subSlotConstant_nonneg J (ξ := ξ) hc hd hB
  have hs := scalePower_nonneg (a := a) (ξ := ξ) (υ := 1) hX.le hY.le hZ.le
  have hv := (height_pos q.2).le
  rw [norm_mul]
  calc
    _ ≤ (scalePower X Y Z a ξ 1 * (C * subSlotConstant J c d B ξ) * (∏ j ∈ J, (P j) ^ ξ) *
      jointHeight q.1 q.2 0 ^ 2 * ‖onLines W0 W1 a ξ 1 ((q.1, q.2), 0)‖) *
      ((zBoxAmplitude (∏ p ∈ S, p) 1 / |6 * ξ - 1|) * height q.2 ^ 3) := by
      gcongr; first | positivity | exact h0 | exact hlz
    _ ≤ (scalePower X Y Z a ξ 1 * (C * subSlotConstant J c d B ξ) * (∏ j ∈ J, (P j) ^ ξ) *
      jointHeight q.1 q.2 0 ^ 2 * ‖onLines W0 W1 a ξ 1 ((q.1, q.2), 0)‖) *
      ((zBoxAmplitude (∏ p ∈ S, p) 1 / |6 * ξ - 1|) * jointHeight q.1 q.2 0 ^ 3) := by
      gcongr; first | positivity | exact height_le_joint_z _ _ _
    _ = _ := by ring

theorem sub_full_vertical_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a ξ : ℝ) (ha : a ∈ Icc (43 / 50 : ℝ) 2) (hβ : HeckeZeroSupremum.beta < a)
    (hξ : ξ ∈ Icc (33 / 200 : ℝ) 1) (hξ1 : 6 * ξ ≠ 1)
    (υ : ℝ) (hυ : υ ∈ Icc (19 / 20 : ℝ) 2) (hυ1 : υ ≠ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ι → ℝ → ℝ),
    (∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B) →
    (∀ j ∈ J, Function.support (W j) ⊆ Icc c d) → ∀ P : ι → ℝ,
    (∀ j ∈ J, 0 < P j) → (∀ j ∈ J, 480 ≤ c * P j) →
    (∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * P j) → ∀ T : ι → Finset PrimeIdeal,
    (∀ j ∈ J, ∀ p ∈ T j, p.val ∉ S) → ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
    let K0 := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x => (W j x : ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ
      (fun w => K0 s w z * LFunction π (6 * z) * LFunction π w)))‖ ≤
      K / (|6 * ξ - 1| * |υ - 1|) * (scalePower X Y Z a ξ υ * (∏ j ∈ J, (P j) ^ ξ)) := by
  let : NeZero (∏ q ∈ S, q) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D, hD, hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (43 / 50) 2 (33 / 200) 1 (19 / 20) 2 (by norm_num) 8
  let Kraw := C * subSlotConstant J c d B ξ * zBoxAmplitude (∏ q ∈ S, q) 1 *
    wAmplitude (∏ q ∈ S, q) 2 * D + 1
  have hslot := subSlotConstant_nonneg J (ξ := ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏ q ∈ S, q) 1
  have hWA := (wAmplitude_pos (∏ q ∈ S, q) (by norm_num : (1 : ℝ) < 2)).le
  have hKraw : 0 < Kraw := by dsimp [Kraw]; positivity
  let k := ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ^ 3
  have hk : 0 < k := pow_pos normalizer_norm_pos _
  refine ⟨k * Kraw, mul_pos hk hKraw, ?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι → PrimeIdeal → ℂ := fun j p => (W j ((Ideal.absNorm p.val : ℝ) / P j) : ℂ)
  have hi := sub_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ 2 hX hY hZ ha.1 hβ hξ.1 (by norm_num) hυ hξ1 hυ1
  have hae := continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ
  have hae' := (hae.mul (EventuallyEq.rfl (f := fun p : HeightSpace =>
    LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I))))).mul
    (EventuallyEq.rfl (f := fun p : HeightSpace =>
      LFunction (fixedSourcePrincipal S hS.prime) ((υ : ℂ) + p.2 * I)))
  have hiraw := hi.congr hae'
  rw [vertical_triple_eq_joint _ a ξ υ hiraw, norm_mul, norm_pow]
  let A := C * subSlotConstant J c d B ξ * (zBoxAmplitude (∏ q ∈ S, q) 1 / |6 * ξ - 1|) *
    (wAmplitude (∏ q ∈ S, q) 2 / |υ - 1|)
  let E := scalePower X Y Z a ξ υ * (∏ j ∈ J, (P j) ^ ξ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ υ hυ
  have hint : (∫ p : HeightSpace, ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a : ℂ) + p.1.1 * I) (globalClosedCorrection η S ((a : ℂ) + p.1.1 * I))
        (windowMultiplier η J T (fun j x => (W j x : ℂ)) P ((a : ℂ) + p.1.1 * I))
        ((υ : ℂ) + p.2 * I) ((ξ : ℂ) + p.1.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + p.1.2 * I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ : ℂ) + p.2 * I)‖ ∂heightMeasure) ≤
      Kraw / (|6 * ξ - 1| * |υ - 1|) * E := by
    refine (integral_congr_ae (hae'.fun_comp norm)).symm.le.trans ?_
    calc
      _ ≤ ∫ p : HeightSpace, A * E * (jointHeight p.1.1 p.1.2 p.2 ^ 8 * ‖onLines W0 W1 a ξ υ p‖)
          ∂heightMeasure := by
        apply integral_mono hi.norm (hp.1.const_mul (A * E))
        intro p
        exact sub_full_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
          hmod T W0 W1 X Y Z a υ C hX hY hZ ha.1 hυ.1 hξ.1 hC hR hυ.2 hυ1 hξ1 p
      _ = A * E * (∫ p : HeightSpace, jointHeight p.1.1 p.1.2 p.2 ^ 8 * ‖onLines W0 W1 a ξ υ p‖
          ∂heightMeasure) := integral_const_mul _ _
      _ ≤ A * E * D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
      _ = (Kraw - 1) / (|6 * ξ - 1| * |υ - 1|) * E := by
        dsimp [A, Kraw]; simp only [add_sub_cancel_right, div_eq_mul_inv, mul_inv_rev]; ring
      _ ≤ Kraw / (|6 * ξ - 1| * |υ - 1|) * E := by gcongr; linarith
  calc
    _ ≤ k * (Kraw / (|6 * ξ - 1| * |υ - 1|) * E) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hint) hk.le
    _ = _ := by ring

theorem sub_residue_vertical_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a ξ : ℝ) (ha : a ∈ Icc (43 / 50 : ℝ) 2) (hβ : HeckeZeroSupremum.beta < a)
    (hξ : ξ ∈ Icc (33 / 200 : ℝ) 1) (hξ1 : 6 * ξ ≠ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (W : ι → ℝ → ℝ),
    (∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B) →
    (∀ j ∈ J, Function.support (W j) ⊆ Icc c d) → ∀ P : ι → ℝ,
    (∀ j ∈ J, 0 < P j) → (∀ j ∈ J, 480 ≤ c * P j) →
    (∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * P j) → ∀ T : ι → Finset PrimeIdeal,
    (∀ j ∈ J, ∀ p ∈ T j, p.val ∉ S) → ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
    let K0 := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x => (W j x : ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    ‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s => verticalIntegral ξ
      (fun z => K0 s 1 z * LFunction π (6 * z)))‖ ≤
      K / |6 * ξ - 1| * (scalePower X Y Z a ξ 1 * (∏ j ∈ J, (P j) ^ ξ)) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D, hD, hprofile⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (43 / 50) 2 (33 / 200) 1 1 1 (by norm_num) 5 0
  let Kraw := C * subSlotConstant J c d B ξ * zBoxAmplitude (∏ p ∈ S, p) 1 * D + 1
  have hslot := subSlotConstant_nonneg J (ξ := ξ) hc hd hB
  have hZA := zBoxAmplitude_nonneg (∏ p ∈ S, p) 1
  have hKraw : 0 < Kraw := by dsimp [Kraw]; positivity
  let R := HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1
  let k := ‖(((1 / (2 * Real.pi) : ℝ) : ℂ))‖ ^ 2
  have hk : 0 < k := pow_pos normalizer_norm_pos _
  refine ⟨(1 + ‖R‖) * k * Kraw, by positivity, ?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  let b : ι → PrimeIdeal → ℂ := fun j p => (W j ((Ideal.absNorm p.val : ℝ) / P j) : ℂ)
  have hi := sub_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha.1 hβ hξ.1 hξ1
  have hae : (fun q : ℝ × ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a : ℂ) + q.1 * I) 1 ((ξ : ℂ) + q.2 * I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + q.2 * I))) =ᵐ[volume.prod volume]
    (fun q : ℝ × ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a : ℂ) + q.1 * I) (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
      (windowMultiplier η J T (fun j x => (W j x : ℂ)) P ((a : ℂ) + q.1 * I)) 1 ((ξ : ℂ) + q.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + q.2 * I))) := by
    have hh : ∀ᵐ q : ℝ × ℝ ∂volume.prod volume, q.1 ≠ 0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0 : ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a : ℂ) + q.1 * I ≠ 0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a : ℂ) + q.1 * I ≠ 1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    rw [continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
    rfl
  have hiraw := hi.congr hae
  rw [vertical_pair_eq_joint _ a ξ hiraw, norm_mul, norm_mul, norm_pow]
  let A := C * subSlotConstant J c d B ξ * (zBoxAmplitude (∏ p ∈ S, p) 1 / |6 * ξ - 1|)
  let E := scalePower X Y Z a ξ 1 * (∏ j ∈ J, (P j) ^ ξ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le)
    (Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hP j hj).le _))
  have hp := hprofile a ha ξ hξ 1 ⟨le_rfl, le_rfl⟩ .w 0
  simp only [sliceMap, pow_zero, div_one] at hp
  have hint : (∫ q : ℝ × ℝ, ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((a : ℂ) + q.1 * I) (globalClosedCorrection η S ((a : ℂ) + q.1 * I))
        (windowMultiplier η J T (fun j x => (W j x : ℂ)) P ((a : ℂ) + q.1 * I))
        1 ((ξ : ℂ) + q.2 * I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6 * ((ξ : ℂ) + q.2 * I))‖ ∂volume.prod volume) ≤
      Kraw / |6 * ξ - 1| * E := by
    refine (integral_congr_ae (hae.fun_comp norm)).symm.le.trans ?_
    calc
      _ ≤ ∫ q : ℝ × ℝ, A * E * (jointHeight q.1 q.2 0 ^ 5 * ‖onLines W0 W1 a ξ 1 ((q.1, q.2), 0)‖)
          ∂volume.prod volume := by
        apply integral_mono hi.norm (hp.1.const_mul (A * E))
        intro q
        exact sub_residue_sharp_pointwise η S hS J c d B ξ hc hd hB hξ.2 W hW hsupp P hP hthreshold
          hmod T W0 W1 X Y Z a C hX hY hZ ha.1 hξ.1 hC hR hξ1 q
      _ = A * E * (∫ q : ℝ × ℝ, jointHeight q.1 q.2 0 ^ 5 * ‖onLines W0 W1 a ξ 1 ((q.1, q.2), 0)‖
          ∂volume.prod volume) := integral_const_mul _ _
      _ ≤ A * E * D := mul_le_mul_of_nonneg_left hp.2 (mul_nonneg hA hE)
      _ = (Kraw - 1) / |6 * ξ - 1| * E := by dsimp [A, Kraw]; simp only [add_sub_cancel_right]; ring
      _ ≤ Kraw / |6 * ξ - 1| * E := by gcongr; linarith
  calc
    _ ≤ (1 + ‖R‖) * (k * (Kraw / |6 * ξ - 1| * E)) := by
      apply mul_le_mul
        (by dsimp [R]; linarith [norm_nonneg (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)])
        (mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans hint) hk.le)
        (by positivity) (by positivity)
    _ = _ := by ring

theorem sub_ordered_remainders_scale_bound {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (a e : ℝ) (ha : a ∈ Icc (43 / 50 : ℝ) 2) (hβ : HeckeZeroSupremum.beta < a)
    (he : 0 < e) (hehi : e ≤ 5 / 6) :
    ∃ C : ℝ, 0 < C ∧ ∀ (W : ι → ℝ → ℝ),
    (∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B) →
    (∀ j ∈ J, Function.support (W j) ⊆ Icc c d) → ∀ P : ι → ℝ,
    (∀ j ∈ J, 0 < P j) → (∀ j ∈ J, 480 ≤ c * P j) →
    (∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * P j) → ∀ T : ι → Finset PrimeIdeal,
    (∀ j ∈ J, ∀ p ∈ T j, p.val ∉ S) → ∀ X Y Z : ℝ, 0 < X → 0 < Y → 0 < Z →
    let K0 := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (windowMultiplier η J T (fun j x => (W j x : ℂ)) P s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral a (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
      (fun w => K0 s w z * LFunction π (6 * z) * LFunction π w)))‖ ≤
      C / e * (scalePower X Y Z a (1 / 6 + e) (19 / 20) * (∏ j ∈ J, (P j) ^ (1 / 6 + e)))) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral a (fun s => verticalIntegral (33 / 200)
      (fun z => K0 s 1 z * LFunction π (6 * z)))‖ ≤
      C * (scalePower X Y Z a (33 / 200) 1 * (∏ j ∈ J, (P j) ^ (33 / 200 : ℝ)))) := by
  obtain ⟨A, hA, hfirst⟩ := sub_full_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (1 / 6 + e) ha hβ ⟨by linarith, by linarith⟩ (by linarith)
    (19 / 20) (by norm_num) (by norm_num)
  obtain ⟨D, hD, hsecond⟩ := sub_residue_vertical_scale_bound η S hS J c d B hc hd hB W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 a (33 / 200) ha hβ (by norm_num) (by norm_num)
  refine ⟨(10 / 3) * A + 100 * D, by positivity, ?_⟩
  intro W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only
  have hf := hfirst W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  have hg := hsecond W hW hsupp P hP hthreshold hmod T hT X Y Z hX hY hZ
  dsimp only at hf hg
  have hegap : |6 * ((1 / 6 : ℝ) + e) - 1| = 6 * e := by rw [abs_of_pos (by linarith)]; ring
  rw [hegap] at hf
  norm_num only [show |(19 / 20 : ℝ) - 1| = 1 / 20 by norm_num] at hf
  norm_num only [show |6 * (33 / 200 : ℝ) - 1| = 1 / 100 by norm_num] at hg
  have hm (ξ : ℝ) : 0 ≤ ∏ j ∈ J, (P j) ^ ξ :=
    Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hP j hj).le _)
  constructor
  · apply hf.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    have heq : A / (6 * e * (1 / 20)) = ((10 / 3) * A) / e := by field_simp; ring
    rw [heq]
    apply div_le_div_of_nonneg_right _ he.le
    nlinarith
  · apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (mul_nonneg (scalePower_nonneg hX.le hY.le hZ.le) (hm _))
    norm_num
    linarith

lemma sub_source_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 1001 / 6000) (Z a ξ υ : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z a ξ υ *
      (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) =
    Z ^ (a - 24749 / 36000 + (1219 / 1500) * (ξ - 1 / 6) + (479 / 1000) * (υ - 1)) := by
  have hp : (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) = Z ^ ((1001 / 6000) * ξ) := by
    simp only [← Real.rpow_mul hZ.le]
    rw [← Real.rpow_sum_of_pos hZ, ← Finset.sum_mul, hell]
  rw [hp, scalePower, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

lemma sub_source_w_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 1001 / 6000) (Z a e : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z a (1 / 6 + e) (19 / 20) *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (1 / 6 + e)) =
    Z ^ (a - 24749 / 36000 + (1219 / 1500) * e - 479 / 20000) := by
  rw [sub_source_scale_identity J ell hell Z a (1 / 6 + e) (19 / 20) hZ]
  congr 1; ring

lemma sub_source_z_scale_identity {ι : Type*} (J : Finset ι) (ell : ι → ℝ)
    (hell : ∑ j ∈ J, ell j = 1001 / 6000) (Z a : ℝ) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z a (33 / 200) 1 *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (33 / 200 : ℝ)) =
    Z ^ (a - 24749 / 36000 - 1219 / 900000) := by
  rw [sub_source_scale_identity J ell hell Z a (33 / 200) 1 hZ]
  congr 1; ring

lemma sub_source_w_strict_exponent (β e : ℝ) (he : e ≤ 1 / 2000) :
    (β + e) - 24749 / 36000 + (1219 / 1500) * e - 479 / 20000 ≤ β - 24749 / 36000 - 1 / 1200 := by
  linarith

lemma sub_source_z_strict_exponent (β e : ℝ) (he : e ≤ 1 / 2000) :
    (β + e) - 24749 / 36000 - 1219 / 900000 ≤ β - 24749 / 36000 - 1 / 1200 := by
  linarith

theorem sub_source_remainders_strict_saving {ι : Type*}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (e : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 2000)
    (ha : HeckeZeroSupremum.beta + e ∈ Icc (43 / 50 : ℝ) 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ell : ι → ℝ), (∑ j ∈ J, ell j = 1001 / 6000) → ∀ (W : ι → ℝ → ℝ),
    (∀ j ∈ J, ∀ x, 0 ≤ W j x ∧ W j x ≤ B) →
    (∀ j ∈ J, Function.support (W j) ⊆ Icc c d) → ∀ T : ι → Finset PrimeIdeal,
    (∀ j ∈ J, ∀ p ∈ T j, p.val ∉ S) → ∀ Z : ℝ, 1 ≤ Z →
    (∀ j ∈ J, 480 ≤ c * Z ^ (ell j)) → (∀ j ∈ J, (Ideal.absNorm η.modulus : ℝ) < c * Z ^ (ell j)) →
    let K0 := fun s => sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z
      (η.excludePrimes S hS.prime) s (globalClosedCorrection η S s)
      (windowMultiplier η J T (fun j x => (W j x : ℂ)) (fun j => Z ^ (ell j)) s)
    let π := fixedSourcePrincipal S hS.prime
    (‖verticalIntegral (HeckeZeroSupremum.beta + e) (fun s => verticalIntegral (1 / 6 + e)
      (fun z => verticalIntegral (19 / 20) (fun w => K0 s w z * LFunction π (6 * z) * LFunction π w)))‖ ≤
      C / e * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200)) ∧
    (‖HeckeReciprocal.regularizedL π 1 * verticalIntegral (HeckeZeroSupremum.beta + e)
      (fun s => verticalIntegral (33 / 200) (fun z => K0 s 1 z * LFunction π (6 * z)))‖ ≤
      C * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200)) := by
  obtain ⟨C, hC, hbound⟩ := sub_ordered_remainders_scale_bound η S hS J c d B hc hd hB
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 (HeckeZeroSupremum.beta + e) e ha (by linarith) he (by linarith)
  refine ⟨C, hC, ?_⟩
  intro ell hell W hW hsupp T hT Z hZ hthreshold hmod
  dsimp only
  have hZ0 : 0 < Z := by linarith
  have hh := hbound W hW hsupp (fun j => Z ^ (ell j)) (fun _ _ => Real.rpow_pos_of_pos hZ0 _)
    hthreshold hmod T hT (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  dsimp only at hh
  rw [sub_source_w_scale_identity J ell hell Z (HeckeZeroSupremum.beta + e) e hZ0,
    sub_source_z_scale_identity J ell hell Z (HeckeZeroSupremum.beta + e) hZ0] at hh
  constructor
  · exact hh.1.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (sub_source_w_strict_exponent HeckeZeroSupremum.beta e hehi))
      (div_nonneg hC.le he.le))
  · exact hh.2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ (sub_source_z_strict_exponent HeckeZeroSupremum.beta e hehi)) hC.le)

end ProbePrincipalRemainderBounds

namespace ProbePrincipalPhysical

open ProbePhysical ProbeFiniteProductBounds PrincipalMellinResidues
open PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal Eisenstein.O

theorem sub_principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K → Finset PrimeIdeal) (hT : ∀ i P, P ∈ T i → P.val ∉ S)
    (hdis : ∀ P : (∀ i, T i), Function.Injective (fun i => (P i).val))
    (b : Fin K → PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z)
    (ha : 43 / 50 < a) (ha3 : a ≤ 3) (hβ : HeckeZeroSupremum.beta < a) (he : 0 < e) (he2 : e ≤ 11 / 6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑ P : (∀ i, T i), (∏ i, b i (P i).val) *
      principalRowIntegral η S (fun i => primaryIdealGenerator (P i).val.val) W0 W1 X Y Z) =
      verticalIntegral a (fun s => verticalIntegral (1 / 6 + e) (fun z => verticalIntegral (19 / 20)
        (fun w => F s w z * LFunction π (6 * z) * LFunction π w))) +
      R * verticalIntegral a (fun s => verticalIntegral (33 / 200) (fun z => F s 1 z * LFunction π (6 * z))) +
      R ^ 2 / 6 * verticalIntegral a (fun s => F s 1 (1 / 6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact ProbePrincipalTransport.sub_source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp => hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

/-- Physical principal-pool contour remainder along `(Z^(17/48), Z^(479/1000), Z)` with
`∑ j, ell j = 1001/6000` and `43/50 < β + e ≤ 2`. -/
theorem sub_physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (e : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 2000)
    (ha : 43 / 50 < HeckeZeroSupremum.beta + e) (ha2 : HeckeZeroSupremum.beta + e ≤ 2) :
    letI : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ ell : Fin K → ℝ, (∑ j, ell j) = 1001 / 6000 → ∀ W : Fin K → ℝ → ℝ,
    (∀ j x, 0 ≤ W j x ∧ W j x ≤ B) → (∀ j, Function.support (W j) ⊆ Set.Icc c d) →
    ∀ T : Fin K → Finset PrimeIdeal, (∀ j p, p ∈ T j → p.val ∉ S) →
    (∀ P : (∀ j, T j), Function.Injective (fun j => (P j).val)) →
    ∀ Z : ℝ, 1 ≤ Z → (∀ j, 480 ≤ c * Z ^ (ell j)) →
    (∀ j, (Ideal.absNorm η.modulus : ℝ) < c * Z ^ (ell j)) →
    ‖(∑ P : (∀ j, T j), (∏ j, (W j ((Ideal.absNorm (P j).val.val : ℝ) / Z ^ (ell j)) : ℂ)) *
        principalRowIntegral η S (fun j => primaryIdealGenerator (P j).val.val)
          W0 W1 (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z) -
      sourceResidueIntegral W0 W1 (∏ p ∈ S, p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta + e) (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x => (W j x : ℂ)) (fun j => Z ^ (ell j)))‖ ≤
      C / e * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C, hC, hbound⟩ := ProbePrincipalRemainderBounds.sub_source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le, ha2⟩
  refine ⟨2 * C, by positivity, ?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0 < Z := by linarith
  have hb := hbound ell hell W (fun j _ => hW j) (fun j _ => hsupp j) T (fun j _ p hp => hT j p hp)
    Z hZ (fun j _ => hthreshold j) (fun j _ => hmod j)
  dsimp only at hb
  have heq := sub_principal_physical_pool_ordered η S hS T hT hdis
    (fun j p => (W j ((Ideal.absNorm p.val : ℝ) / Z ^ (ell j)) : ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z (HeckeZeroSupremum.beta + e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ → ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1) ^ 2 / 6 *
        verticalIntegral (HeckeZeroSupremum.beta + e) F =
      verticalIntegral (HeckeZeroSupremum.beta + e)
        (fun s => fixedPrincipalResidue (∏ p ∈ S, p) ^ 2 / 6 * F s) := by
    rw [verticalIntegral, verticalIntegral, integral_const_mul]
    dsimp only [fixedPrincipalResidue, fixedPrincipal, fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres, add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _ ≤ (2 * C) / e * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200)
  apply hn.trans
  have hCe : C ≤ C / e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0 ≤ Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200) := Real.rpow_nonneg hZ0.le _
  have htwo : (2 * C) / e = 2 * (C / e) := by ring
  rw [htwo]
  nlinarith

end ProbePrincipalPhysical

end SubSevenEighthsPrincipalContours

section SubSevenEighthsSignalComparison

namespace HeckeSignalShift

open HeckeSignal Continuation

theorem sub_quotient_holomorphic (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re}) {a : ℝ}
    (ha : (43 / 50 : ℝ) < a) (hβ : HeckeZeroSupremum.beta < a) :
    DifferentiableOn ℂ (quotient χ H) {s : ℂ | a ≤ s.re ∧ s.re ≤ 2} := by
  intro s hs
  exact ((hH.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (ha.trans_le hs.1))).mul
    (HeckeReciprocal.reciprocal_differentiableAt χ (hβ.trans_le hs.1))).differentiableWithinAt

theorem sub_quotient_polynomial_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    {a C : ℝ} (n : ℕ) (ha : (43 / 50 : ℝ) < a) (_hC : 0 ≤ C)
    (hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C * (1 + |s.im| ^ n))
    {s : ℂ} (hs : a ≤ s.re ∧ s.re ≤ 2) :
    ‖quotient χ H s‖ ≤ ((3 / 2) * C) * (1 + |s.im| ^ n) := by
  have hnorm : ‖H s‖ ≤ 3 / 2 := by
    have ht := norm_add_le (H s - 1) (1 : ℂ)
    rw [sub_add_cancel, norm_one] at ht
    linarith [hb s (ha.trans_le hs.1)]
  unfold quotient
  rw [norm_mul]
  calc
    _ ≤ (3 / 2) * (C * (1 + |s.im| ^ n)) :=
      mul_le_mul hnorm (hR s hs.1 hs.2) (norm_nonneg _) (by norm_num)
    _ = _ := by ring

/-- Shifts the Gaussian-damped reciprocal Hecke signal contour from `Re s = 2` left to any
`43/50 < a ≤ 2` above `HeckeZeroSupremum.beta`. -/
theorem sub_contour_shift_left (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re})
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    (c a : ℝ) (ha : (43 / 50 : ℝ) < a) (ha2 : a ≤ 2)
    (hβ : HeckeZeroSupremum.beta < a) {x : ℝ} (hx : 1 ≤ x) :
    signal χ H c x = (1 / (2 * Real.pi) : ℂ) *
      ∫ y : ℝ, gaussianContourIntegrand (quotient χ H) c x ((a : ℂ) + y * I) := by
  obtain ⟨C, hC, hRraw⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  have hR : ∀ s : ℂ, a ≤ s.re → s.re ≤ 2 →
      ‖HeckeReciprocal.reciprocal χ s‖ ≤ C * (1 + |s.im| ^ 2) :=
    fun s hs _ => hRraw s hs
  have hx0 : 0 < x := by linarith
  rw [signal_eq_contour χ H c hx0]
  congr 1
  apply Eq.symm
  apply vertical_integral_eq_of_polynomial_gaussian_bound _ 2 ha2
    (gaussianContourIntegrand_differentiableOn (sub_quotient_holomorphic χ H hH ha hβ) c hx0)
    (C := x ^ (2 + c) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2) * ((3 / 2) * C))
  intro b hb' y
  rw [norm_gaussianContourIntegrand _ _ _ _ hx0]
  have hxpow : x ^ (b + c) ≤ x ^ (2 + c) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith [hb'.2])
  have he : Real.exp ((b - 5 / 6) ^ 2) ≤ Real.exp ((2 - 5 / 6 : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [ha, hb'.1, hb'.2]
  have hq := sub_quotient_polynomial_bound χ H hb 2 ha hC hR
    (s := (b : ℂ) + y * I) (by simpa using hb')
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  calc
    _ ≤ (x ^ (2 + c) * Real.exp ((2 - 5 / 6 : ℝ) ^ 2)) *
        (((3 / 2) * C) * (1 + |y| ^ 2)) * Real.exp (-(y ^ 2)) := by gcongr
    _ = _ := by unfold polynomialGaussian; ring

end HeckeSignalShift

namespace PrincipalSignalComparison

open ProbePhysical PrincipalSlotEstimate ProbeEuler ProbeLocal Continuation HeckeSignal
open PrincipalMellinResidues

structure SubSlotBounds {κ ι : Type*} (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) (P : ℝ) : Prop where
  lower : 480 ≤ P
  small : 1440 * P ^ (-(43 / 50 : ℝ)) ≤ 1
  weight_nonneg : ∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p
  norm_lower : ∀ j ∈ S, ∀ p ∈ T j, P ≤ Q j p
  phase_bound : ∀ j ∈ S, ∀ p ∈ T j, ‖A j p‖ ≤ 1
  target_unit : ∀ j ∈ S, ∀ p ∈ T j, ‖η j p‖ = 1
  mass_pos : ∀ j ∈ S, 0 < slotMass T w j

theorem sub_slotRatio_error {κ ι : Type*} (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SubSlotBounds S T w Q A η P)
    {s : ℂ} (hs : 43 / 50 ≤ s.re) :
    ‖slotRatio S T w Q A η s - 1‖ ≤ slotErrorConstant S * P ^ (-(43 / 50 : ℝ)) := by
  change ‖(∏ j ∈ S, ∑ p ∈ T j, (w j p : ℂ) * principalSlot (Q j p) (A j p) (η j p) s) /
    PrincipalSlotEstimate.principalScalar S (fun j => ∑ p ∈ T j, w j p) - 1‖ ≤ _
  simpa only [slotErrorConstant, mul_assoc] using
    sub_weighted_principal_product_error_linear S T w Q A η s P h.lower hs h.small
      h.weight_nonneg h.norm_lower h.phase_bound h.target_unit h.mass_pos

theorem sub_slotRatio_bound {κ ι : Type*} (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ)
    (A η : κ → ι → ℂ) {P : ℝ} (h : SubSlotBounds S T w Q A η P)
    {s : ℂ} (hs : 43 / 50 ≤ s.re) :
    ‖slotRatio S T w Q A η s‖ ≤ 1 + slotErrorConstant S * P ^ (-(43 / 50 : ℝ)) := by
  have hn := norm_add_le (slotRatio S T w Q A η s - 1) (1 : ℂ)
  rw [sub_add_cancel, norm_one] at hn
  linarith [sub_slotRatio_error S T w Q A η h hs]

theorem sub_slotRatio_continuous_line {κ ι : Type*} (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) {P : ℝ}
    (h : SubSlotBounds S T w Q A η P) {a : ℝ} (ha : 43 / 50 ≤ a) :
    Continuous (fun t : ℝ => slotRatio S T w Q A η ((a : ℂ) + t * I)) := by
  have hc (j : κ) (hj : j ∈ S) (p : ι) (hp : p ∈ T j) :
      Continuous (fun t : ℝ => principalSlot (Q j p) (A j p) (η j p) ((a : ℂ) + t * I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (sub_principalSlot_differentiableAt (h.lower.trans (h.norm_lower j hj p hp))
      (h.phase_bound j hj p hp) (h.target_unit j hj p hp).le
      (by simpa using ha)).continuousAt.comp (by fun_prop)
  unfold slotRatio slotProduct
  apply Continuous.div_const
  apply continuous_finsetProd
  intro j hj
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (hc j hj p hp)

def subSlotResidue {κ ι : Type*} (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (Z : ℂ) ^ (((a : ℂ) + t * I) - 24749 / 36000) * Complex.exp ((((a : ℂ) + t * I) - 5 / 6) ^ 2) *
      H ((a : ℂ) + t * I) / LFunction χ ((a : ℂ) + t * I) *
        slotRatio S T w Q A η ((a : ℂ) + t * I)

theorem subSlotResidue_eq_reciprocal {κ ι : Type*} (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ) :
    subSlotResidue χ H a Z S T w Q A η = (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      gaussianContourIntegrand (quotient χ H) (-24749 / 36000) Z ((a : ℂ) + t * I) *
        slotRatio S T w Q A η ((a : ℂ) + t * I) := by
  unfold subSlotResidue
  congr 1
  apply integral_congr_ae
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  simp only [gaussianContourIntegrand, quotient, div_eq_mul_inv]
  rw [ht]
  push_cast
  ring_nf

def subKernel (χ : Character) (H : ℂ → ℂ) (a Z : ℝ) (t : ℝ) : ℂ :=
  gaussianContourIntegrand (quotient χ H) (-24749 / 36000) Z ((a : ℂ) + t * I)

def subKernelEnvelope (a C Z : ℝ) : ℝ :=
  Z ^ (a - 24749 / 36000) * Real.exp ((a - 5 / 6) ^ 2) * ((3 / 2) * C)

theorem subKernel_continuous (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re})
    {a Z : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hZ : 0 < Z) : Continuous (subKernel χ H a Z) := by
  have hh := gaussianContourIntegrand_differentiableOn
    (HeckeSignalShift.sub_quotient_holomorphic χ H hH ha hβ) (-24749 / 36000) hZ
  exact hh.continuousOn.comp_continuous (by fun_prop)
    (by intro t; simpa using And.intro (le_refl a) ha2)

theorem subKernel_norm_bound (χ : Character) (H : ℂ → ℂ)
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    {a C Z : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C * (1 + |s.im| ^ 2))
    (t : ℝ) : ‖subKernel χ H a Z t‖ ≤ subKernelEnvelope a C Z * polynomialGaussian 2 t := by
  have hq := HeckeSignalShift.sub_quotient_polynomial_bound χ H hb 2 ha hC
    (fun s hs _ => hR s hs) (s := (a : ℂ) + t * I) (by simpa using And.intro (le_refl a) ha2)
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
    Complex.ofReal_re, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] at hq
  unfold subKernel
  rw [norm_gaussianContourIntegrand _ _ _ _ hZ]
  calc
    _ ≤ (Z ^ (a + (-24749 / 36000)) * Real.exp ((a - 5 / 6) ^ 2)) *
        (((3 / 2) * C) * (1 + |t| ^ 2)) * Real.exp (-(t ^ 2)) := by gcongr
    _ = _ := by unfold subKernelEnvelope polynomialGaussian; ring_nf

theorem subKernel_integrable (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re})
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    {a C Z : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (hC : 0 ≤ C) (hZ : 0 < Z)
    (hR : ∀ s : ℂ, a ≤ s.re → ‖HeckeReciprocal.reciprocal χ s‖ ≤ C * (1 + |s.im| ^ 2)) :
    Integrable (subKernel χ H a Z) :=
  ((polynomialGaussian_integrable 2).const_mul (subKernelEnvelope a C Z)).mono'
    (subKernel_continuous χ H hH ha ha2 hβ hZ).aestronglyMeasurable
    (ae_of_all _ (subKernel_norm_bound χ H hb ha ha2 hC hZ hR))

theorem sub_exists_slotResidue_bound {κ ι : Type*} (χ : Character) (H : ℂ → ℂ)
    (hH : DifferentiableOn ℂ H {s : ℂ | 43 / 50 < s.re})
    (hb : ∀ s : ℂ, 43 / 50 < s.re → ‖H s - 1‖ ≤ 1 / 2)
    {a : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a)
    (S : Finset κ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (T : κ → Finset ι) (w Q : κ → ι → ℝ)
      (A η : κ → ι → ℂ) (P Z : ℝ), SubSlotBounds S T w Q A η P → 1 ≤ Z →
      Integrable (fun t : ℝ => subKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ) + t * I)) ∧
        ‖subSlotResidue χ H a Z S T w Q A η - signal χ H (-24749 / 36000) Z‖ ≤
          D * Z ^ (a - 24749 / 36000) * P ^ (-(43 / 50 : ℝ)) := by
  obtain ⟨C, hC, hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound χ a hβ
  refine ⟨HeckeSignalShift.infinityConstant a C 2 * slotErrorConstant S, ?_, ?_⟩
  · have hi : 0 ≤ ∫ t : ℝ, polynomialGaussian 2 t :=
      integral_nonneg (polynomialGaussian_nonneg 2)
    unfold HeckeSignalShift.infinityConstant slotErrorConstant
    positivity
  · intro T w Q A η P Z h hZ
    have hZ0 : 0 < Z := by linarith
    have hg := subKernel_integrable χ H hH hb ha ha2 hβ hC hZ0 hR
    have hc := sub_slotRatio_continuous_line S T w Q A η h ha.le
    have hbound (t : ℝ) := sub_slotRatio_bound S T w Q A η h
      (s := (a : ℂ) + t * I) (by simpa using ha.le)
    have hint := hg.mul_bdd hc.aestronglyMeasurable (ae_of_all _ hbound)
    refine ⟨hint, ?_⟩
    have herror (t : ℝ) := sub_slotRatio_error S T w Q A η h
      (s := (a : ℂ) + t * I) (by simpa using ha.le)
    have heq : subSlotResidue χ H a Z S T w Q A η - signal χ H (-24749 / 36000) Z =
        (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
          subKernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ) + t * I) - 1) := by
      rw [subSlotResidue_eq_reciprocal,
        HeckeSignalShift.sub_contour_shift_left χ H hH hb (-24749 / 36000) a ha ha2 hβ hZ,
        ← mul_sub]
      change (1 / (2 * Real.pi) : ℂ) *
        ((∫ t : ℝ, subKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ) + t * I)) -
          ∫ t : ℝ, subKernel χ H a Z t) = _
      rw [← integral_sub hint hg]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      change subKernel χ H a Z t * _ - subKernel χ H a Z t = _
      ring_nf
    rw [heq, norm_mul]
    have hbnd (t : ℝ) :
        ‖subKernel χ H a Z t * (slotRatio S T w Q A η ((a : ℂ) + t * I) - 1)‖ ≤
          (subKernelEnvelope a C Z * (slotErrorConstant S * P ^ (-(43 / 50 : ℝ)))) *
            polynomialGaussian 2 t := by
      rw [norm_mul]
      calc
        _ ≤ (subKernelEnvelope a C Z * polynomialGaussian 2 t) *
            (slotErrorConstant S * P ^ (-(43 / 50 : ℝ))) :=
          mul_le_mul (subKernel_norm_bound χ H hb ha ha2 hC hZ0 hR t) (herror t)
            (norm_nonneg _) (mul_nonneg (by unfold subKernelEnvelope; positivity)
              (polynomialGaussian_nonneg 2 t))
        _ = _ := by ring_nf
    have hn := norm_integral_le_of_norm_le
      ((polynomialGaussian_integrable 2).const_mul
        (subKernelEnvelope a C Z * (slotErrorConstant S * P ^ (-(43 / 50 : ℝ)))))
      (ae_of_all _ hbnd)
    have hm := mul_le_mul_of_nonneg_left hn (norm_nonneg (1 / (2 * Real.pi) : ℂ))
    rw [integral_const_mul] at hm
    convert hm using 1 <;> try rfl
    unfold subKernelEnvelope HeckeSignalShift.infinityConstant
    ring_nf

theorem sub_raw_slot_integrable {κ ι : Type*} (χ : Character) (H : ℂ → ℂ) (a Z : ℝ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hi : Integrable (fun t : ℝ => subKernel χ H a Z t * slotRatio S T w Q A η ((a : ℂ) + t * I))) :
    Integrable (fun t : ℝ =>
      (Z : ℂ) ^ (((a : ℂ) + t * I) - 24749 / 36000) * Complex.exp ((((a : ℂ) + t * I) - 5 / 6) ^ 2) *
        H ((a : ℂ) + t * I) / LFunction χ ((a : ℂ) + t * I) *
          slotRatio S T w Q A η ((a : ℂ) + t * I)) := by
  apply hi.congr
  filter_upwards [raw_inverse_ae_reciprocal χ a] with t ht
  unfold subKernel gaussianContourIntegrand quotient
  simp only [div_eq_mul_inv, ht]
  push_cast
  ring_nf

theorem sub_source_power_identity {Z : ℝ} (hZ : 0 < Z) (s : ℂ) :
    ((Z ^ (17 / 48 : ℝ) : ℝ) : ℂ) ^ (1 / 3 : ℂ) * (Z : ℂ) ^ (s - 5 / 6) =
      (Z : ℂ) ^ (((-(1001 / 6000 : ℝ) / 6 : ℝ) : ℂ)) * (Z : ℂ) ^ (s - 24749 / 36000) := by
  have hz : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  rw [← Complex.cpow_mul_ofReal_nonneg hZ.le (17 / 48) (1 / 3),
    ← Complex.cpow_add _ _ hz, ← Complex.cpow_add _ _ hz]
  congr 1
  push_cast
  ring_nf

theorem sub_normalized_source_double_residue {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character)
    (Y Z : ℝ) (hZ : 0 < Z) (s : ℂ) (H B : ℂ → ℂ → ℂ)
    (S : Finset κ) (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hB : B 1 (1 / 6) = slotProduct S T w Q A η s) :
    (fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z χ s H B 1 (1 / 6)) /
        (sourceResidueConstant W0 W1 M *
          (Probe.principalScalar S Z (1001 / 6000) (slotMass T w) : ℂ)) =
      (Z : ℂ) ^ (s - 24749 / 36000) * Complex.exp ((s - 5 / 6) ^ 2) * H 1 (1 / 6) /
        LFunction χ s * slotRatio S T w Q A η s := by
  rw [source_double_residue, source_normalizer_cast S T w hZ, hB]
  have hp := sub_source_power_identity hZ s
  have hz : (Z : ℂ) ^ (((-(1001 / 6000 : ℝ) / 6 : ℝ) : ℂ)) ≠ 0 :=
    (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [hZ.ne'])
  rw [hp]
  simp only [slotRatio, div_eq_mul_inv, mul_inv_rev]
  calc
    _ = (sourceResidueConstant W0 W1 M * (sourceResidueConstant W0 W1 M)⁻¹) *
        ((Z : ℂ) ^ (((-(1001 / 6000 : ℝ) / 6 : ℝ) : ℂ)) *
          ((Z : ℂ) ^ (((-(1001 / 6000 : ℝ) / 6 : ℝ) : ℂ)))⁻¹) *
        ((Z : ℂ) ^ (s - 24749 / 36000) * Complex.exp ((s - 5 / 6) ^ 2) * H 1 (1 / 6) *
          (LFunction χ s)⁻¹ * (slotProduct S T w Q A η s *
            (PrincipalSlotEstimate.principalScalar S (slotMass T w))⁻¹)) := by ring_nf
    _ = _ := by rw [mul_inv_cancel₀ hc, mul_inv_cancel₀ hz]; ring_nf

theorem sub_sourceResidueIntegral_normalized {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) =
      slotProduct S T w Q A η ((a : ℂ) + t * I)) :
    sourceResidueConstant W0 W1 M *
      (Probe.principalScalar S Z (1001 / 6000) (slotMass T w) : ℂ) ≠ 0 ∧
    sourceResidueIntegral W0 W1 M χ a (Z ^ (17 / 48 : ℝ)) Y Z H B /
      (sourceResidueConstant W0 W1 M *
        (Probe.principalScalar S Z (1001 / 6000) (slotMass T w) : ℂ)) =
        subSlotResidue χ (fun s => H s 1 (1 / 6)) a Z S T w Q A η := by
  refine ⟨mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm), ?_⟩
  unfold sourceResidueIntegral verticalIntegral subSlotResidue
  norm_num only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [mul_div_assoc, ← integral_div]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  exact sub_normalized_source_double_residue W0 W1 M χ Y Z hZ _ (H _) (B _) S T w Q A η hc (hB _)

theorem sub_source_double_residue_integrable {κ ι : Type*} (W0 W1 : SchwartzMap ℝ ℂ)
    (M : Ideal Eisenstein.O) [NeZero M] (χ : Character) (a Y Z : ℝ) (hZ : 0 < Z)
    (H B : ℂ → ℂ → ℂ → ℂ) (S : Finset κ) (T : κ → Finset ι)
    (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (hc : sourceResidueConstant W0 W1 M ≠ 0)
    (hm : ∀ j ∈ S, 0 < slotMass T w j)
    (hB : ∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) =
      slotProduct S T w Q A η ((a : ℂ) + t * I))
    (hi : Integrable (fun t : ℝ => subKernel χ (fun s => H s 1 (1 / 6)) a Z t *
      slotRatio S T w Q A η ((a : ℂ) + t * I))) :
    Integrable (fun t : ℝ => fixedPrincipalResidue M ^ 2 / 6 *
      sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z χ ((a : ℂ) + t * I)
        (H ((a : ℂ) + t * I)) (B ((a : ℂ) + t * I)) 1 (1 / 6)) := by
  have hiraw := sub_raw_slot_integrable χ (fun s => H s 1 (1 / 6)) a Z S T w Q A η hi
  have hn := mul_ne_zero hc (source_normalizer_ne_zero S T w hZ hm (ℓ := 1001 / 6000))
  apply (hiraw.mul_const
    (sourceResidueConstant W0 W1 M *
      (Probe.principalScalar S Z (1001 / 6000) (slotMass T w) : ℂ))).congr
  filter_upwards [] with t
  exact ((div_eq_iff hn).mp (sub_normalized_source_double_residue W0 W1 M χ Y Z hZ _
    (H _) (B _) S T w Q A η hc (hB _))).symm

theorem sub_exists_normalized_actual_source_bound {κ : Type*} (E : Finset (Ideal Eisenstein.O))
    (hE : SourceExclusions E) (η : Character) {a : ℝ}
    (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (T : κ → Finset PrimeIdeal)
      (w : κ → PrimeIdeal → ℝ) (P Y Z : ℝ) (B : ℂ → ℂ → ℂ → ℂ),
      480 ≤ P → 1440 * P ^ (-(43 / 50 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ w j p) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T w j) → 1 ≤ Z →
      sourceResidueConstant W0 W1 (∏ p ∈ E, p) ≠ 0 →
      (∀ t : ℝ, B ((a : ℂ) + t * I) 1 (1 / 6) = slotProduct S T w (fun _ p => Ideal.absNorm p.val)
        (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val)
          ((a : ℂ) + t * I)) →
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (1001 / 6000) (slotMass T w) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ) + t * I) (globalClosedCorrection η E ((a : ℂ) + t * I)) (B ((a : ℂ) + t * I)) 1 (1 / 6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z ^ (17 / 48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-24749 / 36000) Z‖ ≤
        D * Z ^ (a - 24749 / 36000) * P ^ (-(43 / 50 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hb⟩ := sub_exists_slotResidue_bound (ι := PrimeIdeal)
    (η.excludePrimes E hE.prime) (sourceCorrection η E)
    (sub_sourceCorrection_differentiable η E hE) (sub_sourceCorrection_bound η E hE) ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 T w P Y Z B hP hsmall hw hnorm hcop hmass hZ hc hB
  have he := sub_sourceResidueIntegral_normalized W0 W1 (∏ p ∈ E, p)
    (η.excludePrimes E hE.prime) a Y Z (by linarith) (globalClosedCorrection η E) B S T w
    (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryIdealGenerator p.val))
    (fun _ p => idealCoeff η p.val) hc hmass hB
  have hslots : SubSlotBounds S T w (fun _ p => (Ideal.absNorm p.val : ℝ))
      (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val) P :=
    ⟨hP, hsmall, hw, hnorm, fun _ _ p _ => actualAPhase_norm_le_one η _,
      fun j hj p hp => idealCoeff_norm_one_of_coprime η p.val p.property.ne_zero (hcop j hj p hp), hmass⟩
  have hbnd := hb T w (fun _ p => Ideal.absNorm p.val)
    (fun _ p => actualAPhase η (primaryIdealGenerator p.val)) (fun _ p => idealCoeff η p.val) P Z hslots hZ
  refine ⟨he.1, ?_, ?_⟩
  · exact sub_source_double_residue_integrable W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
      a Y Z (by linarith) (globalClosedCorrection η E) B S T w
      (fun _ p => Ideal.absNorm p.val) (fun _ p => actualAPhase η (primaryIdealGenerator p.val))
      (fun _ p => idealCoeff η p.val) hc hmass hB hbnd.1
  rw [he.2]
  exact hbnd.2

end PrincipalSignalComparison

namespace ProbePrincipalResidueActual

open PrincipalMellinResidues PrincipalSignalComparison ProbeFiniteProductBounds
open ProbeEuler ProbeLocal HeckeSignal ProbePhysical Continuation

theorem sub_normalized_actual_window_residue {κ : Type*}
    (E : Finset (Ideal Eisenstein.O)) (hE : SourceExclusions E) (η : Character)
    {a : ℝ} (ha : 43 / 50 < a) (ha2 : a ≤ 2) (hβ : HeckeZeroSupremum.beta < a) (S : Finset κ) :
    letI : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ),
      0 < a0 → 0 < a1 → Function.support W0 ⊆ Set.Icc a0 b0 →
      Function.support W1 ⊆ Set.Icc a1 b1 →
      (∀ y, (W0 y).im = 0) → (∀ y, (W1 y).im = 0) →
      (∀ y, 0 ≤ (W0 y).re) → (∀ y, 0 ≤ (W1 y).re) → W0 ≠ 0 → W1 ≠ 0 →
      ∀ (T : κ → Finset PrimeIdeal) (W : κ → ℝ → ℝ) (scale : κ → ℝ) (P Y Z : ℝ),
      480 ≤ P → 1440 * P ^ (-(43 / 50 : ℝ)) ≤ 1 →
      (∀ j ∈ S, ∀ p ∈ T j, 0 ≤ W j ((Ideal.absNorm p.val : ℝ) / scale j)) →
      (∀ j ∈ S, ∀ p ∈ T j, P ≤ (Ideal.absNorm p.val : ℝ)) →
      (∀ j ∈ S, ∀ p ∈ T j, IsCoprime p.val η.modulus) →
      (∀ j ∈ S, 0 < slotMass T (residueWeights W scale) j) → 1 ≤ Z →
      let B := windowMultiplier η S T (fun j t => (W j t : ℂ)) scale
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ E, p) *
        (Probe.principalScalar S Z (1001 / 6000) (slotMass T (residueWeights W scale)) : ℂ)
      normer ≠ 0 ∧
      Integrable (fun t : ℝ => fixedPrincipalResidue (∏ p ∈ E, p) ^ 2 / 6 *
        sourceMultiplier W0 W1 (Z ^ (17 / 48 : ℝ)) Y Z (η.excludePrimes E hE.prime)
          ((a : ℂ) + t * I) (globalClosedCorrection η E ((a : ℂ) + t * I))
          (B ((a : ℂ) + t * I)) 1 (1 / 6)) ∧
      ‖sourceResidueIntegral W0 W1 (∏ p ∈ E, p) (η.excludePrimes E hE.prime)
          a (Z ^ (17 / 48 : ℝ)) Y Z (globalClosedCorrection η E) B / normer -
          signal (η.excludePrimes E hE.prime) (sourceCorrection η E) (-24749 / 36000) Z‖ ≤
        D * Z ^ (a - 24749 / 36000) * P ^ (-(43 / 50 : ℝ)) := by
  dsimp only
  let : NeZero (∏ p ∈ E, p) := ⟨fixedPrimeProduct_ne_zero E hE.prime⟩
  obtain ⟨D, hD, hbound⟩ := sub_exists_normalized_actual_source_bound E hE η ha ha2 hβ S
  refine ⟨D, hD, ?_⟩
  intro W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W scale P Y Z hP hsmall hW hnorm hcop hmass hZ
  refine hbound W0 W1 T (residueWeights W scale) P Y Z
    (windowMultiplier η S T (fun j t => (W j t : ℂ)) scale)
    hP hsmall ?_ hnorm hcop hmass hZ ?_ ?_
  · intro j hj p hp
    exact mul_nonneg (hW j hj p hp) (Real.rpow_nonneg (by positivity) _)
  · exact ProbePrincipalNormalizer.sourceResidueConstant_ne_zero (∏ p ∈ E, p)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  · intro t
    exact actual_window_residue η S T W scale _

end ProbePrincipalResidueActual

namespace ProbeRaySlots

open ProbePrincipalResidueActual ProbePhysical PrincipalSignalComparison
local notation "Id" => Ideal Eisenstein.O

theorem sub_power_pool_thresholds {ι : Type*} [Fintype ι]
    (C : Set Id) (S : Finset Id) (η : Character) (c d ellMin : ℝ)
    (hc : 0 < c) (hd : c ≤ d) (hmin : 0 < ellMin)
    (ell : ι → ℝ) (hell : ∀ j, ellMin ≤ ell j) :
    ∀ᶠ Z : ℝ in atTop,
      1 ≤ Z ∧ 480 ≤ c * Z ^ ellMin ∧ 1440 * (c * Z ^ ellMin) ^ (-(43 / 50 : ℝ)) ≤ 1 ∧
      (∀ j, 480 ≤ c * Z ^ (ell j) ∧ (η.modulus.absNorm : ℝ) < c * Z ^ (ell j)) ∧
      (∀ j, ∀ P ∈ pool C S c d (Z ^ (ell j)),
        c * Z ^ ellMin ≤ (P.val.absNorm : ℝ) ∧ IsCoprime P.val η.modulus ∧ P.val ∉ S) := by
  have ht := (tendsto_rpow_atTop hmin).const_mul_atTop hc
  have hs : Tendsto (fun Z : ℝ => 1440 * (c * Z ^ ellMin) ^ (-(43 / 50 : ℝ))) atTop (nhds 0) := by
    simpa only [mul_zero, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 43 / 50)).comp ht).const_mul (1440 : ℝ)
  filter_upwards [eventually_ge_atTop (1 : ℝ), ht.eventually (eventually_ge_atTop (480 : ℝ)),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm : ℝ)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with Z hZ h480 hmod hsmall
  have hZ0 : 0 < Z := by linarith
  have hmono (j : ι) : c * Z ^ ellMin ≤ c * Z ^ (ell j) := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hZ (hell j)) hc.le
  refine ⟨hZ, h480, hsmall.le, fun j => ⟨h480.trans (hmono j), hmod.trans_le (hmono j)⟩, ?_⟩
  intro j P hP
  have hp := pool_norm_bounds C S hc.le hd (Real.rpow_pos_of_pos hZ0 _) P hP
  have hn : c * Z ^ ellMin < (P.val.absNorm : ℝ) := (hmono j).trans_lt (by simpa only [mul_comm] using hp.1)
  exact ⟨hn.le, prime_coprime_of_norm_gt η P (hmod.trans hn), (mem_pool C S c d _ P).mp hP |>.2.2.2⟩

end ProbeRaySlots

namespace ProbePrincipalNormalized

open ProbePhysical ProbeFiniteProductBounds PrincipalMellinResidues
open PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal Eisenstein.O

/-- Normalized principal-row comparison along the sub-`7/8` ray `(Z^(17/48), Z^(479/1000), Z)`
with `∑ j, ell j = 1001/6000` and `43/50 < β + e ≤ 2`: the normalized principal pool converges to
`HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-24749/36000) Z` with
strict polynomial saving below `Z^(β - 24749/36000)`. -/
theorem sub_actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (Eisenstein.O ⧸ M)]
    (H : Subgroup (Eisenstein.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M ≤ H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0 < c) (hd : c ≤ d) (hB : 0 ≤ B) (hmin : 0 < ellMin)
    (ell : Fin K → ℝ) (hell : ∀ j, ellMin ≤ ell j) (hdis : Function.Injective ell)
    (hsum : (∑ j, ell j) = 1001 / 6000)
    (W : Fin K → ℝ → ℝ) (hW : ∀ j, ContDiff ℝ ∞ (W j))
    (hcompact : ∀ j, HasCompactSupport (W j))
    (hsupp : ∀ j, Function.support (W j) ⊆ Set.Ioo c d)
    (hWbounds : ∀ j y, 0 ≤ W j y ∧ W j y ≤ B) (hne : ∀ j, W j ≠ 0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0 < a0) (ha1 : 0 < a1)
    (hW0 : Function.support W0 ⊆ Set.Icc a0 b0) (hW1 : Function.support W1 ⊆ Set.Icc a1 b1)
    (hr0 : ∀ y, (W0 y).im = 0) (hr1 : ∀ y, (W1 y).im = 0)
    (hp0 : ∀ y, 0 ≤ (W0 y).re) (hp1 : ∀ y, 0 ≤ (W1 y).re) (hn0 : W0 ≠ 0) (hn1 : W1 ≠ 0)
    (e nu : ℝ) (he : 0 < e) (hehi : e ≤ 1 / 2000) (hnu : 0 < nu)
    (ha : 43 / 50 < HeckeZeroSupremum.beta + e) (ha2 : HeckeZeroSupremum.beta + e ≤ 2) :
    letI : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ Z : ℝ in atTop,
      let T := fun j => pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
      let normer := sourceResidueConstant W0 W1 (∏ p ∈ S, p) *
        (Probe.principalScalar Finset.univ Z (1001 / 6000)
          (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : ℂ)
      normer ≠ 0 ∧
      ‖(∑ P : (∀ j, T j), (∏ j, (W j ((Ideal.absNorm (P j).val.val : ℝ) / Z ^ (ell j)) : ℂ)) *
        principalRowIntegral η S (fun j => primaryIdealGenerator (P j).val.val)
          W0 W1 (Z ^ (17 / 48 : ℝ)) (Z ^ (479 / 1000 : ℝ)) Z) / normer -
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-24749 / 36000) Z‖ ≤
      C * (Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200 + nu) +
        Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 + e - (43 / 50) * ellMin)) := by
  let : NeZero (∏ p ∈ S, p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0, hC0, hrem⟩ := ProbePrincipalPhysical.sub_physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K := K)
  obtain ⟨D, hD, hres⟩ := sub_normalized_actual_window_residue S hS η ha ha2 (by linarith)
    (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏ p ∈ S, p)
  let C := C0 / e * ‖cs⁻¹‖ + D * c ^ (-(43 / 50 : ℝ)) + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  have hpos (j : Fin K) : tsupport (W j) ⊆ Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [sub_power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y => (hWbounds j y).1) hne ell (fun j => hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ => c) (fun _ => d) ell (fun _ => hc) (fun _ => hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ, h480, hsmall, hslot, hpool⟩
  have hZ0 : 0 < Z := by linarith
  let T := fun j => pool (RayQuotient.identityClass M H) S c d (Z ^ (ell j))
  let normer := cs * (Probe.principalScalar Finset.univ Z (1001 / 6000)
    (slotMass T (residueWeights W (fun j => Z ^ (ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j => Z ^ (ell j)) (c * Z ^ ellMin) (Z ^ (479 / 1000 : ℝ)) Z h480 hsmall
    (fun j _ p _ => (hWbounds j _).1) (fun j _ p hp => (hpool j p hp).1)
    (fun j _ p hp => (hpool j p hp).2.1) (fun j _ => hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1, ?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j => Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp => (hpool j p hp).2.2) htuple Z hZ (fun j => (hslot j).1) (fun j => (hslot j).2)
  have hinv : ‖normer⁻¹‖ ≤ ‖cs⁻¹‖ * Z ^ nu := by
    dsimp only [normer]
    rw [mul_inv_rev, norm_mul, ← Complex.ofReal_inv, norm_real]
    simpa only [hsum, Real.norm_eq_abs, mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c * Z ^ ellMin) ^ (-(43 / 50 : ℝ)) = c ^ (-(43 / 50 : ℝ)) * Z ^ (-(43 / 50 : ℝ) * ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _), ← Real.rpow_mul hZ0.le]
    congr 2; ring
  have heq1 : (C0 / e * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200)) * (‖cs⁻¹‖ * Z ^ nu) =
      (C0 / e * ‖cs⁻¹‖) * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200 + nu) := by
    rw [Real.rpow_add hZ0]; ring
  have heq2 : D * Z ^ (HeckeZeroSupremum.beta + e - 24749 / 36000) * (c * Z ^ ellMin) ^ (-(43 / 50 : ℝ)) =
      (D * c ^ (-(43 / 50 : ℝ))) * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 + e - (43 / 50) * ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta - 24749 / 36000 + e - (43 / 50) * ellMin =
      (HeckeZeroSupremum.beta + e - 24749 / 36000) + (-(43 / 50 : ℝ) * ellMin) by ring, Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1, heq2]
  have h1 : C0 / e * ‖cs⁻¹‖ ≤ C := by
    dsimp [C]
    have : 0 ≤ D * c ^ (-(43 / 50 : ℝ)) := by positivity
    linarith
  have h2 : D * c ^ (-(43 / 50 : ℝ)) ≤ C := by
    dsimp [C]
    have : 0 ≤ C0 / e * ‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 - 1 / 1200 + nu) +
        C * Z ^ (HeckeZeroSupremum.beta - 24749 / 36000 + e - (43 / 50) * ellMin) := by gcongr
    _ = _ := by ring

end ProbePrincipalNormalized

end SubSevenEighthsSignalComparison

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
