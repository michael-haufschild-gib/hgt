import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedLimit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Actual active integer and uniform phase control

The integer floor(exp L) has logarithmic lag at most 2*exp(-L). That lag
vanishes relative to the constructed width, so positive source mass makes it
real-active. Its cosine is uniformly bounded below throughout the low band.
No active-node existence or phase estimate is supplied as a premise.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

def jointNearestInteger (L : ℝ) : ℕ := ⌊Real.exp L⌋₊
def jointIntegerLag (L : ℝ) : ℝ := Real.log (jointNearestInteger L)-L

/-- The actual integer below exp(L) has exponentially small logarithmic lag. -/
theorem jointIntegerLag_abs_le {L : ℝ} (hL : 1 ≤ L) :
    |jointIntegerLag L| ≤ 2*Real.exp (-L) := by
  have he : 2 ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  have hfl : (jointNearestInteger L:ℝ) ≤ Real.exp L := Nat.floor_le (Real.exp_pos L).le
  have hlt : Real.exp L < (jointNearestInteger L:ℝ)+1 := Nat.lt_floor_add_one _
  have hh : Real.exp L/2 ≤ (jointNearestInteger L:ℝ) := by linarith
  have hn : (0:ℝ) < jointNearestInteger L := (div_pos (Real.exp_pos L) (by norm_num)).trans_le hh
  have hlo := Real.log_le_log hn hfl
  rw [Real.log_exp] at hlo
  have hfrac : Real.exp L/(jointNearestInteger L:ℝ) ≤ 1+1/(jointNearestInteger L:ℝ) := by
    apply (div_le_iff₀ hn).mpr
    rw [add_mul, one_mul, div_mul_cancel₀ _ hn.ne']
    linarith
  have hinv : 1/(jointNearestInteger L:ℝ) ≤ 2*Real.exp (-L) := by
    have h := one_div_le_one_div_of_le (div_pos (Real.exp_pos L) (by norm_num)) hh
    calc
      _ ≤ 1/(Real.exp L/2) := h
      _ = _ := by rw [Real.exp_neg]; field_simp
  rw [jointIntegerLag, abs_of_nonpos (by linarith), neg_sub]
  calc
    _ = Real.log (Real.exp L/(jointNearestInteger L:ℝ)) := by
      rw [Real.log_div (Real.exp_pos L).ne' hn.ne',Real.log_exp]
    _ ≤ Real.exp L/(jointNearestInteger L:ℝ)-1 :=
      Real.log_le_sub_one_of_pos (div_pos (Real.exp_pos L) hn)
    _ ≤ 1/(jointNearestInteger L:ℝ) := by linarith
    _ ≤ _ := hinv

/-- This selected integer is a genuine constrained index for all large separations. -/
theorem jointNearestInteger_ge_two {L : ℝ} (hL : 2 ≤ L) :
    2 ≤ jointNearestInteger L := by
  apply Nat.le_floor
  change (2:ℝ) ≤ Real.exp L
  linarith [Real.add_one_le_exp L]

private theorem width_phase_exp_limit {b : ℝ} (hb : 0 < b) :
    Tendsto (fun L : ℝ => Real.exp (-b*L)) atTop (𝓝 0) := by
  simpa only [Real.rpow_zero,one_mul] using
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 b hb

/-- The selected actual lag shrinks relative to the actual source width. -/
theorem tendsto_jointIntegerLag_div_width {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun L => jointIntegerLag L/jointSeedWidth κ L) atTop (𝓝 0) := by
  have he : Tendsto (fun L : ℝ => Real.exp (-L/2)) atTop (𝓝 0) := by
    convert width_phase_exp_limit (by norm_num : (0:ℝ)<1/2) using 1
    funext L
    congr 1
    ring
  have ht := he.const_mul (2/κ)
  simp only [mul_zero] at ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun L => norm_nonneg _)) _ ht
  filter_upwards [eventually_ge_atTop (1:ℝ)] with L hL
  have hLp : 0 < L := by linarith
  have hW := jointSeedWidth_pos hκ hLp
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hW]
  have heq : Real.exp (-L)=(Real.exp (-L/2))^2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  calc
    _ ≤ (2*Real.exp (-L))/jointSeedWidth κ L :=
      div_le_div_of_nonneg_right (jointIntegerLag_abs_le hL) hW.le
    _ = ((2/κ)*Real.exp (-L/2))/L := by
      rw [heq,jointSeedWidth]
      field_simp
    _ ≤ _ := div_le_self (by positivity) hL

/-- Positive mass makes the selected shrinking lag real-active for the literal dilated source. -/
theorem eventually_jointIntegerLag_active (f : JointSmoothTest)
    (hm : 0 < testMass f.1.1) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ L : ℝ in atTop,
      0 < (EF.weilTest (jointDilatedProfile f.1.1 (jointSeedWidth κ L))
        (jointDilatedProfile f.1.1 (jointSeedWidth κ L)) (jointIntegerLag L)).re := by
  have hc : Continuous (fun y => (EF.weilTest f.1.1 f.1.1 y).re) :=
    Complex.continuous_re.comp
      (EF.weilTest_contDiff f.1.2.1 f.2.continuous f.1.2.2).continuous
  have ht := (hc.tendsto 0).comp (tendsto_jointIntegerLag_div_width hκ)
  have hzero : (EF.weilTest f.1.1 f.1.1 0).re=testMass f.1.1 := by
    rw [autocorr_zero_eq_testMass,Complex.ofReal_re]
  rw [hzero] at ht
  have hp := ht.eventually (lt_mem_nhds hm)
  filter_upwards [hp,eventually_gt_atTop (0:ℝ)] with L hp hL
  have hW := jointSeedWidth_pos hκ hL
  rw [jointDilatedProfile_corr f.1.1 hW]
  simp only [Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero]
  have hlag : (jointSeedWidth κ L)⁻¹*jointIntegerLag L=
      jointIntegerLag L/jointSeedWidth κ L := by ring
  rw [hlag]
  exact mul_pos hW hp

/-- The actual integer phase remains uniformly positive below the growing frequency threshold. -/
theorem eventually_jointIntegerLag_low_cos :
    ∀ᶠ L : ℝ in atTop, ∀ T : ℝ, |T| ≤ Real.exp (7*L/8) →
      (11/12:ℝ) ≤ Real.cos (jointIntegerLag L*T) := by
  have he : Tendsto (fun L : ℝ => Real.exp (-L/8)) atTop (𝓝 0) := by
    convert width_phase_exp_limit (by norm_num : (0:ℝ)<1/8) using 1
    funext L
    congr 1
    ring
  have ht := he.const_mul 2
  simp only [mul_zero] at ht
  have hs := ht.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/3))
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with L hs hL
  intro T hT
  have hab : |jointIntegerLag L*T| ≤ 2*Real.exp (-L/8) := by
    rw [abs_mul]
    calc
      _ ≤ (2*Real.exp (-L))*Real.exp (7*L/8) :=
        mul_le_mul (jointIntegerLag_abs_le hL) hT (abs_nonneg _) (by positivity)
      _ = _ := by
        rw [mul_assoc,← Real.exp_add]
        congr 2
        ring
  have ha := abs_le.mp (hab.trans hs.le)
  have hprod := mul_nonneg (sub_nonneg.mpr ha.2)
    (show 0 ≤ (1/3:ℝ)+jointIntegerLag L*T by linarith [ha.1])
  have hc := Real.one_sub_sq_div_two_le_cos (x:=jointIntegerLag L*T)
  nlinarith

end RHTower.WeilWorkPBAP
