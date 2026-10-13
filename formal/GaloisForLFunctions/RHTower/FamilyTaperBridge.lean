import GaloisForLFunctions.RHTower.Zeta23FamilyBandwidth
import Zeta23.PrimeSideA.Bridge

/-!
# The concrete taper data at bandwidth above one

Alpöge–Furman's abstract prime-side layer is stated for a functional datum satisfying `LocalHypsCoreW`,
which — unlike `LocalHyps` — imposes no upper bound on the bandwidth ratio `λ`.  Every field is a property
of the taper `φ(u) = ϱ((L/2 − |u|)/w)` at the length `L = λ log(T/2π)` alone, so it holds for any `λ > 0`
once `8w ≤ L`.  `localHypsCoreW_concrete_fam` records this for the concrete data
`(φ̂, Φ, A_φ, g, a, b)` of any parameters with `ParamsValidFam` (taper profile, `λ > 0`, `w ≥ 1`), and
`localHypsCoreW_eventually_fam` gives it for all large `T`.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23 Zeta23.PrimeSide

noncomputable section

namespace RHTower

variable {P : Params} {T : ℝ}

/-- **`LocalHypsCoreW` for the concrete taper data, any bandwidth.** -/
theorem localHypsCoreW_concrete_fam (hP : ParamsValidFam P) (hwL : 8 * P.w ≤ P.L T)
    (hl : 1 ≤ l T) (hX : 1 ≤ P.X T) :
    LocalHypsCoreW P.crho (P.toSetting T) (P.localFun T) where
  four_le_cϱ := by rw [Params.crho_eq]; exact Taper.four_le_cRho hP.taper
  lam_pos := hP.lam_pos
  one_le_w := hP.one_le_w
  w_le := by show P.w ≤ P.L T / 8; linarith
  one_le_l := hl
  phiHat_cont := Taper.phiHatR_continuous hP.taper hP.w_pos (hP.two_w_le hwL)
  phiHat_even := fun r => Taper.phiHatR_even r
  phiHat_le_L := Taper.abs_phiHatR_le_L hP.taper hP.w_pos (hP.two_w_le hwL)
  phiHat_le_inv := Taper.abs_phiHatR_mul_abs_le hP.taper hP.w_pos (hP.two_w_le hwL)
  phiHat_le_sq := Taper.abs_phiHatR_mul_sq_le hP.taper hP.one_le_w (hP.two_w_le hwL)
  phiHat_sq_integrable := Taper.integrable_phiHatR_sq hP.taper hP.w_pos (hP.two_w_le hwL)
  phiHat_sq_mul_abs_integrable :=
    Taper.integrable_phiHatR_sq_mul_abs hP.taper hP.w_pos (hP.two_w_le hwL)
  integral_phiHat_sq_mul_abs_le := Taper.integral_phiHatR_sq_mul_abs_le hP.taper hP.one_le_w hwL
  phiHat_sq_mul_sq_integrable := Taper.integrable_phiHatR_sq_mul_sq hP.taper hP.one_le_w hwL
  integral_phiHat_sq_mul_sq_le := Taper.integral_phiHatR_sq_mul_sq_le hP.taper hP.one_le_w hwL
  phiHat_sq_integral := Taper.integral_phiHatR_sq hP.taper hP.w_pos (hP.two_w_le hwL)
  phiHat_sq_fourier := Taper.integral_phiHatR_sq_mul_cos hP.taper hP.w_pos (hP.two_w_le hwL)
  g_nonneg := Taper.g_nonneg hP.taper hP.w_pos (hP.two_w_le hwL)
  g_le_Aphi := Taper.g_le_Aphi hP.taper hP.w_pos (hP.two_w_le hwL)
  Aphi_le := Taper.Aphi_le hP.taper hP.w_pos (hP.two_w_le hwL)
  Phi_contDiff := Taper.PhiR_contDiff_one hP.taper hP.w_pos (hP.two_w_le hwL)
  Phi_even := fun r => Taper.PhiR_even r
  Phi_le_L := Taper.abs_PhiR_le_L hP.taper hP.w_pos (hP.two_w_le hwL)
  Phi_le_inv := Taper.abs_PhiR_mul_abs_le hP.taper hP.w_pos (hP.two_w_le hwL)
  Phi_le_sq := Taper.abs_PhiR_mul_sq_le hP.taper hP.one_le_w (hP.two_w_le hwL)
  Phi_sq_integrable := Taper.integrable_PhiR_sq hP.taper hP.w_pos (hP.two_w_le hwL)
  Phi_sq_mul_abs_integrable := Taper.integrable_PhiR_sq_mul_abs hP.taper hP.w_pos (hP.two_w_le hwL)
  integral_Phi_sq_mul_abs_le := Taper.integral_PhiR_sq_mul_abs_le hP.taper hP.one_le_w hwL
  Phi_sq_mul_sq_integrable := Taper.integrable_PhiR_sq_mul_sq hP.taper hP.one_le_w hwL
  integral_Phi_sq_mul_sq_le := Taper.integral_PhiR_sq_mul_sq_le hP.taper hP.one_le_w hwL
  Phi_zero := Taper.PhiR_zero hP.taper hP.w_pos (hP.two_w_le hwL)
  Phi_sq_integral := Taper.integral_PhiR_sq hP.taper hP.w_pos (hP.two_w_le hwL)
  Phi_sq_fourier := Taper.integral_PhiR_sq_mul_cos hP.taper hP.w_pos (hP.two_w_le hwL)
  poisson := Taper.hasSum_phiHatR_mul hP.taper hP.w_pos (hP.two_w_le hwL) T
  b_ge_half := by
    have h1 := Taper.one_sub_le_bConst hP.taper hP.w_pos (hP.two_w_le hwL)
    have hL : 0 < P.L T := by linarith [hP.one_le_w]
    have h2 : 2 * P.w / P.L T ≤ 1 / 4 := by rw [div_le_iff₀ hL]; linarith
    show 1 / 2 ≤ Taper.bConst P.ϱ (P.L T) P.w
    linarith
  b_le_a := Taper.bConst_le_aConst hP.taper hP.w_pos (hP.two_w_le hwL)
  a_le_one := Taper.aConst_le_one hP.taper hP.w_pos (hP.two_w_le hwL)
  psi_integrable := by rw [psiA_concrete]; exact Taper.psi_integrable hP.taper hP.one_le_w hwL
  psi_sq_integrable := by
    rw [psiA_concrete]; exact Taper.psi_sq_integrable hP.taper hP.one_le_w hwL
  integral_psi_Ioi_le := by
    rw [psiA_concrete]; exact Taper.integral_psi_Ioi_le hP.taper hP.one_le_w hwL
  integral_psi_sq_le := by
    rw [psiA_concrete]; exact Taper.integral_psi_sq_le hP.taper hP.one_le_w hwL
  phiHat_le_psi := by
    rw [psiA_concrete]; exact Taper.abs_phiHatR_le_psi hP.taper hP.one_le_w (hP.two_w_le hwL)
  Phi_le_psi := by
    rw [psiA_concrete]; exact Taper.abs_PhiR_le_psi hP.taper hP.one_le_w (hP.two_w_le hwL)
  PiX_cont := PiX_continuous (Real.exp_pos _)
  PiX_bound := PiX_abs_le hX

/-- **`LocalHypsCoreW` for all large `T`, any bandwidth.** -/
theorem localHypsCoreW_eventually_fam (hP : ParamsValidFam P) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → LocalHypsCoreW P.crho (P.toSetting T) (P.localFun T) := by
  have hl : Tendsto l atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have hL : Tendsto P.L atTop atTop := hl.const_mul_atTop hP.lam_pos
  have hX : ∀ᶠ T in atTop, 1 ≤ P.X T := by
    filter_upwards [hL.eventually_ge_atTop 0] with T h
    simpa [Params.X] using Real.one_le_exp h
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp ((hl.eventually_ge_atTop 1).and
    ((hL.eventually_ge_atTop (8 * P.w)).and hX))
  exact ⟨T₀, fun T hT => localHypsCoreW_concrete_fam hP (hT₀ T hT).2.1 (hT₀ T hT).1 (hT₀ T hT).2.2⟩

end RHTower
