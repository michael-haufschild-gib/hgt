import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinZeroPacket
import GaloisForLFunctions.RHTower.Sieve.ZetaResidueUnitRectanglePeeling
import GaloisForLFunctions.RHTower.Sieve.MaynardNormalizedReferenceTargetPerron

open Complex Filter intervalIntegral Set Topology Finset

namespace RHTower.Sieve

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The normalized adjacent Mellin kernel is analytic on the whole open right half-plane. -/
theorem analyticOnNhd_routeTNormalizedSmoothWindowMellin_re_pos
    {N H : ℝ} (hN : 0 ≤ N) (hH : 0 < H) :
    AnalyticOnNhd ℂ (routeTNormalizedSmoothWindowMellin N H)
      {s : ℂ | 0 < s.re} := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hplus := analyticOnNhd_mellin_smoothWeight_re_pos
    (N := N + H) hH
  have hbase := analyticOnNhd_mellin_smoothWeight_re_pos
    (N := N) hH
  have hscaled : AnalyticOnNhd ℂ
      (fun s => (H : ℂ)⁻¹ *
        (mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight (N + H) H x : ℝ) : ℂ)) s -
          mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s))
      {s : ℂ | 0 < s.re} :=
    analyticOnNhd_const.mul (hplus.sub hbase)
  apply AnalyticOnNhd.congr hopen hscaled
  intro s hs
  rw [routeTNormalizedSmoothWindowMellin,
    mellin_routeTSmoothWindowWeight_eq_sub hN hH hs]

/-- Four-edge regularized zeta boundary functional with normalized adjacent Mellin kernel. -/
def routeTNormalizedZetaRegularMellinBoundary
    (N H c d T : ℝ) : ℂ :=
  I • (∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((d : ℂ) + (y : ℝ) * I))
    - I • (∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((c : ℂ) + (y : ℝ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((c : ℂ) + (y : ℝ) * I))
    - ((∫ x : ℝ in c..d,
        zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((T : ℝ) : ℂ) * I))
      - ∫ x : ℝ in c..d,
        zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I) *
          routeTNormalizedSmoothWindowMellin N H
            ((x : ℂ) + ((-T : ℝ) : ℂ) * I))

/-- Exact normalized adjacent-Mellin zero residue packet on a rectangle. -/
def routeTNormalizedZetaRegularMellinZeroPacket
    (N H c d T : ℝ) : ℂ :=
  2 * Real.pi * I *
    ∑ w ∈ zetaResidueUnitClosedRectangleZeros
        ((c : ℂ) + ((-T : ℝ) : ℂ) * I)
        ((d : ℂ) + ((T : ℝ) : ℂ) * I),
      ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
        routeTNormalizedSmoothWindowMellin N H w

/-- Exact zero-crossing contour identity for the normalized adjacent physical window. -/
theorem routeTNormalizedZetaRegularMellinBoundary_eq_neg_zeroPacket
    {N H c d T : ℝ} (hN : 0 ≤ N) (hH : 0 < H)
    (hc : 0 < c) (hcd : c < d) (hT : 0 < T)
    (hbot : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0)
    (htop : ∀ x ∈ uIcc c d,
      zetaResidueUnit ((x : ℂ) + ((T : ℝ) : ℂ) * I) ≠ 0)
    (hright : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((d : ℂ) + (y : ℝ) * I) ≠ 0)
    (hleft : ∀ y ∈ uIcc (-T) T,
      zetaResidueUnit ((c : ℂ) + (y : ℝ) * I) ≠ 0) :
    routeTNormalizedZetaRegularMellinBoundary N H c d T =
      -routeTNormalizedZetaRegularMellinZeroPacket N H c d T := by
  let U : Set ℂ := {s : ℂ | 0 < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsub : (uIcc c d ×ℂ uIcc (-T) T) ⊆ U := by
    intro z hz
    have hzre := (Complex.mem_reProdIm.mp hz).1
    rw [uIcc_of_le hcd.le] at hzre
    exact hc.trans_le hzre.1
  have hrect := rectIntegral_mul_zetaLogDerivReg_eq_neg_closedRectangleZeroSum
    (g := routeTNormalizedSmoothWindowMellin N H)
    (z₁ := (c : ℂ) + ((-T : ℝ) : ℂ) * I)
    (z₂ := (d : ℂ) + ((T : ℝ) : ℂ) * I)
    hUopen (analyticOnNhd_routeTNormalizedSmoothWindowMellin_re_pos hN hH)
    (by simpa using hsub) (by simpa using hcd) (by simp; linarith)
    (by simpa using hbot) (by simpa using htop)
    (by simpa using hright) (by simpa using hleft)
  simp [rectIntegral, routeTNormalizedZetaRegularMellinBoundary,
    routeTNormalizedZetaRegularMellinZeroPacket, smul_eq_mul, mul_comm] at hrect ⊢
  linear_combination hrect

/-- Any finite subpacket of the common rectangle inherits the lossless normalized Mellin bound. -/
theorem norm_routeTNormalizedMellinZeroSum_le_commonMass
    {X : ℕ} (hX : 3 ≤ X) {Z : Finset ℂ}
    (hZ : Z ⊆ inghamRouteTCommonZeroPacket X) :
    ‖∑ w ∈ Z,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinPhysicalWidth X) w‖ ≤
      inghamRouteTCommonZeroWeightedMass X := by
  calc
    ‖∑ w ∈ Z,
        ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinPhysicalWidth X) w‖ ≤
      ∑ w ∈ Z,
        ‖((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
          routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinPhysicalWidth X) w‖ := norm_sum_le _ _
    _ ≤ ∑ w ∈ Z,
        (X : ℝ) ^
          (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
            inghamRouteTZeroMultiplicity w := by
      apply Finset.sum_le_sum
      intro w hw
      rw [norm_mul, Complex.norm_natCast]
      change inghamRouteTZeroMultiplicity w *
          ‖routeTNormalizedSmoothWindowMellin
            (inghamRouteTMellinPhysicalCenter X)
            (inghamRouteTMellinPhysicalWidth X) w‖ ≤ _
      calc
        inghamRouteTZeroMultiplicity w *
            ‖routeTNormalizedSmoothWindowMellin
              (inghamRouteTMellinPhysicalCenter X)
              (inghamRouteTMellinPhysicalWidth X) w‖ ≤
          inghamRouteTZeroMultiplicity w *
            ((X : ℝ) ^
              (inghamRouteTPhysicalScaleExponent * (w.re - 1))) :=
            mul_le_mul_of_nonneg_left
              (norm_routeTNormalizedSmoothWindowMellin_physical_le hX (hZ hw))
              (inghamRouteTZeroMultiplicity_nonneg w)
        _ = (X : ℝ) ^
            (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
              inghamRouteTZeroMultiplicity w := by ring
    _ ≤ ∑ w ∈ inghamRouteTCommonZeroPacket X,
        (X : ℝ) ^
          (inghamRouteTPhysicalScaleExponent * (w.re - 1)) *
            inghamRouteTZeroMultiplicity w := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hZ (fun w _ _ =>
        mul_nonneg (Real.rpow_nonneg (by positivity) _)
          (inghamRouteTZeroMultiplicity_nonneg w))
    _ = inghamRouteTCommonZeroWeightedMass X := by
      unfold inghamRouteTCommonZeroWeightedMass
      rfl

/-- A boundary-free Route-T contour can be selected strictly inside the common rectangle, and its
entire normalized Mellin zero residue is controlled by the common packet. -/
theorem exists_routeTPhysicalMellinBoundary_eq_neg_zeroPacket_and_norm_le
    {X : ℕ} (hX : 4 ≤ X) :
    ∃ c d T : ℝ,
      c ∈ Set.Ioo (inghamUniformGabrielCenter (7 / 10 : ℝ)) (3 / 4) ∧
      d ∈ Set.Ioo 2 3 ∧
      T ∈ Set.Ioo ((X : ℝ) - 3) ((X : ℝ) - 2) ∧
      routeTNormalizedZetaRegularMellinBoundary
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinPhysicalWidth X) c d T =
        -routeTNormalizedZetaRegularMellinZeroPacket
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinPhysicalWidth X) c d T ∧
      ‖routeTNormalizedZetaRegularMellinZeroPacket
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinPhysicalWidth X) c d T‖ ≤
        2 * Real.pi * inghamRouteTCommonZeroWeightedMass X := by
  have ha : 0 < inghamUniformGabrielCenter (7 / 10 : ℝ) := by
    unfold inghamUniformGabrielCenter
    norm_num
  have hab : inghamUniformGabrielCenter (7 / 10 : ℝ) < 3 / 4 := by
    unfold inghamUniformGabrielCenter
    norm_num
  have hsep : (3 / 4 : ℝ) < 2 := by norm_num
  have hdd : (2 : ℝ) < 3 := by norm_num
  have hXR : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hT0 : 0 < (X : ℝ) - 3 := by linarith
  have hTT : (X : ℝ) - 3 < (X : ℝ) - 2 := by linarith
  obtain ⟨c, d, T, hcI, hdI, hTI, hbot, htop, hright, hleft⟩ :=
    exists_zetaResidueUnit_zeroFreeBoundary_rectangle
      ha hab hsep hdd hT0 hTT
  have hcd : c < d := lt_trans hcI.2 (hsep.trans hdI.1)
  have hT : 0 < T := hT0.trans hTI.1
  have hX1 : 1 ≤ X := by omega
  have hboundary := routeTNormalizedZetaRegularMellinBoundary_eq_neg_zeroPacket
    (N := inghamRouteTMellinPhysicalCenter X)
    (H := inghamRouteTMellinPhysicalWidth X)
    (c := c) (d := d) (T := T)
    (inghamRouteTMellinPhysicalCenter_pos hX1).le
    (inghamRouteTMellinPhysicalWidth_pos hX1)
    (ha.trans hcI.1) hcd hT hbot htop hright hleft
  let Z : Finset ℂ := zetaResidueUnitClosedRectangleZeros
    ((c : ℂ) + ((-T : ℝ) : ℂ) * I)
    ((d : ℂ) + ((T : ℝ) : ℂ) * I)
  have hZ : Z ⊆ inghamRouteTCommonZeroPacket X := by
    intro w hw
    have hwdata := mem_zetaResidueUnitClosedRectangleZeros.mp hw
    have hwK := Complex.mem_reProdIm.mp hwdata.1
    have hwre : w.re ∈ Set.Icc c d := by
      simpa [Z, uIcc_of_le hcd.le] using hwK.1
    have hwim : w.im ∈ Set.Icc (-T) T := by
      simpa [Z, uIcc_of_le (by linarith : -T ≤ T)] using hwK.2
    have hcenterFour :
        inghamUniformGabrielCenter (7 / 10 : ℝ) ≤ 4 := by
      unfold inghamUniformGabrielCenter
      norm_num
    have hreCommon :
        w.re ∈ Set.Icc (inghamUniformGabrielCenter (7 / 10 : ℝ)) 4 :=
      ⟨hcI.1.le.trans hwre.1,
        hwre.2.trans (hdI.2.le.trans (by norm_num))⟩
    have hheight : 0 ≤ (X : ℝ) - 2 := by linarith
    have himCommon :
        w.im ∈ Set.Icc (2 - (X : ℝ)) ((X : ℝ) - 2) :=
      ⟨by linarith [hwim.1, hTI.2], by linarith [hwim.2, hTI.2]⟩
    refine mem_zetaResidueUnitClosedRectangleZeros.mpr ⟨?_, hwdata.2⟩
    apply Complex.mem_reProdIm.mpr
    constructor
    · simpa [inghamRouteTCommonZeroPacket, uIcc_of_le hcenterFour] using hreCommon
    · simpa [inghamRouteTCommonZeroPacket,
        uIcc_of_le (by linarith : 2 - (X : ℝ) ≤ (X : ℝ) - 2)] using himCommon
  have hinner := norm_routeTNormalizedMellinZeroSum_le_commonMass
    (X := X) (by omega) hZ
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hzeroBound :
      ‖routeTNormalizedZetaRegularMellinZeroPacket
          (inghamRouteTMellinPhysicalCenter X)
          (inghamRouteTMellinPhysicalWidth X) c d T‖ ≤
        2 * Real.pi * inghamRouteTCommonZeroWeightedMass X := by
    unfold routeTNormalizedZetaRegularMellinZeroPacket
    change ‖(2 : ℂ) * (Real.pi : ℂ) * I *
        (∑ w ∈ Z,
          ((analyticOrderAt zetaResidueUnit w).toNat : ℂ) *
            routeTNormalizedSmoothWindowMellin
              (inghamRouteTMellinPhysicalCenter X)
              (inghamRouteTMellinPhysicalWidth X) w)‖ ≤ _
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, Complex.norm_I]
    simp only [mul_one]
    exact mul_le_mul_of_nonneg_left hinner hpi
  exact ⟨c, d, T, hcI, hdI, hTI, hboundary, hzeroBound⟩

end

end RHTower.Sieve
