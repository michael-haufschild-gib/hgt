/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
import GaloisForLFunctions.IncommensurableGaborPinching.CosineWindowArbitraryBandwidth
import Zeta23.ThmD.WindowLocalHyps

/-!
# Prime-side local data for cosine shape independent of bandwidth

Admissible-window estimates do not require a bandwidth cap. A fixed cosine
shape therefore supplies the wide prime-side local data with one uniform
regularity constant, even though its frozen profile depends on height. The
same constant controls complex Fourier decay in the critical strip.
-/

noncomputable section
open Real Set MeasureTheory Filter Topology Zeta23 Zeta23.AdmWindow Zeta23.ThmD

namespace GaloisForLFunctions.IncommensurableGaborPinching

/-- Every admissible window supplies the wide prime-side local estimates. -/
theorem admWindow_localHypsCoreW {v : ℝ → ℝ} {c : ℝ} (p : PrimeSide.Setting) (hW : AdmWindow v p.L p.w c)
    (hlam : 0 < p.lam) (hl : 1 ≤ p.l) (hX : 1 ≤ p.X)
    (hb : 1 / 2 ≤ bv v p.L) :
    PrimeSide.LocalHypsCoreW c p (localFun v p.L) := by
  have hc := hW.four_le_c
  have hw := hW.one_le_w
  have hwL := hW.w8
  have hcw : 0 ≤ c / p.w := div_nonneg hW.c_nonneg hW.w_pos.le
  have hψ1 : ∀ r, |vHatR v r| ≤ PsiC.psiC c p.L p.w r := fun r => by
    rw [PsiC.psiC_eq_psiA]; exact hW.abs_vHatR_le_psiA p rfl rfl r
  have hψ2 : ∀ r, |VPhiR v r| ≤ PsiC.psiC c p.L p.w r := fun r => by
    rw [PsiC.psiC_eq_psiA]; exact hW.abs_VPhiR_le_psiA p rfl rfl r
  exact {
    four_le_cϱ := hc
    lam_pos := hlam
    one_le_w := hw
    w_le := by linarith
    one_le_l := hl
    phiHat_cont := hW.vHatR_continuous
    phiHat_even := hW.vHatR_even
    phiHat_le_L := hW.abs_vHatR_le_L
    phiHat_le_inv := hW.abs_vHatR_mul_abs_le
    phiHat_le_sq := hW.abs_vHatR_mul_sq_le
    phiHat_sq_integrable := hW.integrable_vHatR_sq
    phiHat_sq_mul_abs_integrable := hW.integrable_vHatR_sq_mul_abs
    integral_phiHat_sq_mul_abs_le := PsiC.integral_sq_mul_abs_le_of_le_psi hc hw hwL hψ1
    phiHat_sq_mul_sq_integrable :=
      PsiC.integrable_sq_mul_sq_of_bounds hW.vHatR_continuous hcw hW.abs_vHatR_mul_abs_le
        hW.abs_vHatR_mul_sq_le
    integral_phiHat_sq_mul_sq_le :=
      PsiC.integral_sq_mul_sq_le_of_bounds hcw hW.abs_vHatR_mul_abs_le hW.abs_vHatR_mul_sq_le
    phiHat_sq_integral := hW.integral_vHatR_sq
    phiHat_sq_fourier := hW.integral_vHatR_sq_mul_cos
    g_nonneg := hW.gv_nonneg
    g_le_Aphi := hW.gv_le_Av
    Aphi_le := hW.Av_le
    Phi_contDiff := hW.VPhiR_contDiff_one
    Phi_even := hW.VPhiR_even
    Phi_le_L := hW.abs_VPhiR_le_L
    Phi_le_inv := hW.abs_VPhiR_mul_abs_le
    Phi_le_sq := hW.abs_VPhiR_mul_sq_le
    Phi_sq_integrable := hW.integrable_VPhiR_sq
    Phi_sq_mul_abs_integrable := hW.integrable_VPhiR_sq_mul_abs
    integral_Phi_sq_mul_abs_le := PsiC.integral_sq_mul_abs_le_of_le_psi hc hw hwL hψ2
    Phi_sq_mul_sq_integrable :=
      PsiC.integrable_sq_mul_sq_of_bounds hW.VPhiR_continuous hcw hW.abs_VPhiR_mul_abs_le
        hW.abs_VPhiR_mul_sq_le
    integral_Phi_sq_mul_sq_le :=
      PsiC.integral_sq_mul_sq_le_of_bounds hcw hW.abs_VPhiR_mul_abs_le hW.abs_VPhiR_mul_sq_le
    Phi_zero := hW.VPhiR_zero
    Phi_sq_integral := hW.integral_VPhiR_sq
    Phi_sq_fourier := hW.integral_VPhiR_sq_mul_cos
    poisson := fun τ τ' => hW.hasSum_vHatR_mul p.T τ τ'
    b_ge_half := hb
    b_le_a := hW.bv_le_av
    a_le_one := hW.av_le_one
    psi_integrable := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.psi_integrable hc hw hwL
    psi_sq_integrable := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.psi_sq_integrable hc hw hwL
    integral_psi_Ioi_le := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.integral_psi_Ioi_le hc hw hwL
    integral_psi_sq_le := by
      rw [← PsiC.psiC_eq_psiA]; exact PsiC.integral_psi_sq_le hc hw hwL
    phiHat_le_psi := hW.abs_vHatR_le_psiA p rfl rfl
    Phi_le_psi := hW.abs_VPhiR_le_psiA p rfl rfl
    PiX_cont := PiX_continuous p.X_pos
    PiX_bound := PiX_abs_le hX }

/-- The frozen cosine parameters have exactly the admissible cosine local data. -/
theorem cosineParams_localFun {P : Params} {κ T : ℝ} (hw : P.w ≠ 0) :
    (cosineParams P κ T).localFun T =
      AdmWindow.localFun (phiD P.ϱ κ (P.L T) P.w) (P.L T) := by
  rw [Params.localFun_eq_admWindow, cosineParams_phi hw]
  rfl

/-- Cosine shape and bandwidth enter independent admissibility conditions. -/
theorem cosineParams_localHypsCoreW {P : Params} (hϱ : TaperProfile P.ϱ)
    (hlam : 0 < P.lam) {κ T : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w)
    (h8 : 8 * P.w ≤ P.L T) (hπ : 4 * π * P.w ≤ P.L T) (hl : 1 ≤ l T) :
    PrimeSide.LocalHypsCoreW (cDT P.ϱ κ) ((cosineParams P κ T).toSetting T)
      ((cosineParams P κ T).localFun T) := by
  rw [cosineParams_localFun (by linarith : P.w ≠ 0)]
  have hW := admWindow_phiD hϱ hκ hκ1 hw h8
  apply admWindow_localHypsCoreW _ hW hlam hl
  · change 1 ≤ Real.exp (P.L T)
    exact Real.one_le_exp hW.L_pos.le
  · exact bv_phiD_ge_half hϱ hκ hκ1 hw h8 hπ

/-- A fixed cosine shape has uniform wide local estimates at every fixed positive bandwidth. -/
theorem cosineParams_eventually_localHypsCoreW {P : Params} (hϱ : TaperProfile P.ϱ)
    (hlam : 0 < P.lam) {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w) :
    ∀ᶠ T in atTop, PrimeSide.LocalHypsCoreW (cDT P.ϱ κ)
      ((cosineParams P κ T).toSetting T) ((cosineParams P κ T).localFun T) := by
  have hL := Assembly.tendsto_L_atTop P hlam
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  filter_upwards [hL.eventually_ge_atTop (8 * P.w),
    hL.eventually_ge_atTop (4 * π * P.w), hl.eventually_ge_atTop 1] with T h8 hπ hl
  exact cosineParams_localHypsCoreW hϱ hlam hκ hκ1 hw h8 hπ hl

/-- A uniform complex-strip decay bound for the frozen cosine Fourier transform. -/
theorem cosineParams_phiHat_decay {P : Params} (hϱ : TaperProfile P.ϱ)
    {κ T : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hw : 1 ≤ P.w)
    (h8 : 8 * P.w ≤ P.L T) (r y : ℝ) (hy : |y| ≤ 1 / 2)
    (hz : (r : ℂ) - Complex.I * y ≠ 0) :
    ‖(cosineParams P κ T).phiHat T ((r : ℂ) - Complex.I * y)‖ ≤
      Real.exp (P.L T / 4) * cDT P.ϱ κ / ‖(r : ℂ) - Complex.I * y‖ ^ 2 := by
  have hW := admWindow_phiD hϱ hκ hκ1 hw h8
  have hhat : (cosineParams P κ T).phiHat T =
      AdmWindow.vHat (phiD P.ϱ κ (P.L T) P.w) := by
    change AdmWindow.vHat ((cosineParams P κ T).phi T) = _
    rw [cosineParams_phi (by linarith : P.w ≠ 0)]
  have hC : (∫ u, |deriv (deriv (phiD P.ϱ κ (P.L T) P.w)) u|) ≤ cDT P.ϱ κ :=
    hW.l1_deriv2.trans (div_le_self hW.c_nonneg hw)
  have hexp : Real.exp (|((r : ℂ) - Complex.I * y).im| * (P.L T / 2)) ≤
      Real.exp (P.L T / 4) := by
    apply Real.exp_le_exp.mpr
    have him : ((r : ℂ) - Complex.I * y).im = -y := by simp
    rw [him, abs_neg]
    nlinarith only [mul_le_mul_of_nonneg_right hy hW.L_pos.le]
  rw [hhat, le_div_iff₀ (by positivity)]
  exact (hW.norm_vHat_mul_sq_le _).trans
    (mul_le_mul hexp hC (integral_nonneg fun _ => abs_nonneg _) (Real.exp_pos _).le)

end GaloisForLFunctions.IncommensurableGaborPinching
