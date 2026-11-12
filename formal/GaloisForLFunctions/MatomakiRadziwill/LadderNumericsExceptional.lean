import GaloisForLFunctions.MatomakiRadziwill.LadderNumericsMoment
import GaloisForLFunctions.RHTower.Sieve.LargeLadderGroup

/-!
# The exceptional set, numerically

* **Measure** (`exceptional_volume_le`): for the last ladder scale (primes in `[P, Q]`, width `H ≥ 3`,
  `eH ≤ P`, `2 ≤ H log P`), thresholds `e^{-αu/H}`, `W ≥ e` and `18(log W/(log P − 1/H) + 1) ≤ H`,
  the set where some block is large has measure at most `#V · 144 W^{2α} Q^{2α}`.  Each block uses
  the moment `k = ⌈log W/(u/H)⌉`, so `e^{ku/H} ≥ W` (pure moment bound) and
  `e^{2αku/H} ≤ W^{2α} Q^{2α}`.
* **Halász–Montgomery** (`exceptional_HM_le`): for a top-scale cofactor with `1 ≤ lo ≤ X`,
  `∫_E |R_v|² ≤ 6 + 4 K |E| / lo + 384 log(2 + 4πW)`, `K = plainKernelFarConst(4X, 2πW)`.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- **The measure of the exceptional set.** -/
theorem exceptional_volume_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Pr : Finset ℕ}
    (hPr : ∀ q ∈ Pr, q.Prime) {H : ℝ} (hH : 3 ≤ H) {P Q : ℝ} (hP1 : 1 ≤ P)
    (hPrb : ∀ p ∈ Pr, P ≤ p ∧ (p : ℝ) ≤ Q) (hPH : Real.exp 1 * H ≤ P) (h2 : 2 ≤ H * Real.log P)
    (hQ1 : 1 ≤ Q) {α : ℝ} (hα0 : 0 ≤ α) {W : ℝ} (hWe : Real.exp 1 ≤ W)
    (hk : 18 * (Real.log W / (Real.log P - 1 / H) + 1) ≤ H) :
    volume.real (Icc (-W) W ∩
        (smallAt (blockQ f Pr H) (Pr.image (blk H)) (fun u => Real.exp (-α * u / H)))ᶜ)
      ≤ (Pr.image (blk H)).card * (144 * W ^ (2 * α) * Q ^ (2 * α)) := by
  classical
  have hH0 : 0 < H := by linarith
  have hW0 : 0 < W := lt_of_lt_of_le (Real.exp_pos 1) hWe
  have hW1 : 1 ≤ W := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  have hlogW : 1 ≤ Real.log W := by rw [Real.le_log_iff_exp_le hW0]; exact hWe
  set V := Pr.image (blk H) with hV
  set kk : ℕ → ℕ := fun u => ⌈Real.log W / ((u : ℝ) / H)⌉₊ with hkk
  have hcont : ∀ u, Continuous (blockQ f Pr H u) := fun u => continuous_logPoly _ _
  have hbase := volume_not_small_le (Q := blockQ f Pr H) hcont V
    (c := fun u => Real.exp (-α * u / H)) (fun u _ => Real.exp_pos _) kk W
  have hterm : ∀ u ∈ V, (Real.exp (-α * u / H) ^ (2 * kk u))⁻¹
      * (∫ w in Icc (-W) W, ‖blockQ f Pr H u w ^ kk u‖ ^ (2 : ℕ))
      ≤ 144 * W ^ (2 * α) * Q ^ (2 * α) := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hu1, hu2⟩ := blk_bounds hH0 hP1 (hPrb p hp).1 (hPrb p hp).2
    set a : ℝ := (blk H p : ℝ) / H with ha
    have ha_low : Real.log P - 1 / H ≤ a := by rw [ha, le_div_iff₀ hH0]; field_simp; linarith
    have ha_up : a ≤ Real.log Q := by rw [ha, div_le_iff₀ hH0]; linarith
    have hlogP' : 1 / H < Real.log P := by
      have : 2 / H ≤ Real.log P := by rw [div_le_iff₀ hH0]; linarith
      have : 1 / H < 2 / H := by rw [div_lt_div_iff_of_pos_right hH0]; norm_num
      linarith
    have ha0 : 0 < a := by linarith
    have hq0 : 0 < Real.log W / a := by positivity
    have hk_low := Nat.le_ceil (Real.log W / a)
    have hk_up := Nat.ceil_lt_add_one hq0.le
    have hk1 : 1 ≤ kk (blk H p) := Nat.one_le_iff_ne_zero.mpr (by
      intro h; simp only [hkk] at h; rw [← ha, Nat.ceil_eq_zero] at h; linarith)
    have hkdef : (kk (blk H p) : ℝ) = (⌈Real.log W / a⌉₊ : ℝ) := by simp only [hkk, ← ha]
    -- `S = e^{u/H} ≥ H`
    have hS : H ≤ Real.exp a := by
      have h1 : Real.log P - 1 ≤ a := by
        have : 1 / H ≤ 1 := by rw [div_le_one hH0]; linarith
        linarith
      calc H ≤ P / Real.exp 1 := by rw [le_div_iff₀ (Real.exp_pos 1)]; linarith
        _ = Real.exp (Real.log P - 1) := by rw [Real.exp_sub, Real.exp_log (by linarith)]
        _ ≤ Real.exp a := Real.exp_le_exp.mpr h1
    -- `e^{ka} ≥ W`
    have hlen : W ≤ Real.exp a ^ kk (blk H p) := by
      rw [← Real.exp_nat_mul, hkdef]
      have : Real.log W ≤ (⌈Real.log W / a⌉₊ : ℝ) * a := by
        calc Real.log W = Real.log W / a * a := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_right hk_low ha0.le
      calc W = Real.exp (Real.log W) := (Real.exp_log hW0).symm
        _ ≤ _ := Real.exp_le_exp.mpr this
    have hmom := integral_normSq_blockQ_pow_le hf hPr hH (blk H p) (kk (blk H p)) hk1 hS hW1 hlen
    -- `18k ≤ H`, so the moment is at most `144`
    have hkmax : (kk (blk H p) : ℝ) ≤ Real.log W / (Real.log P - 1 / H) + 1 := by
      rw [hkdef]
      have h3 : Real.log W / a ≤ Real.log W / (Real.log P - 1 / H) :=
        div_le_div_of_nonneg_left (by linarith) (by linarith) ha_low
      linarith
    have hratio : 18 * (kk (blk H p) : ℝ) / H ≤ 1 := by
      rw [div_le_one hH0]; linarith
    have hmom' : (∫ w in Icc (-W) W, ‖blockQ f Pr H (blk H p) w ^ kk (blk H p)‖ ^ (2 : ℕ)) ≤ 144 := by
      refine le_trans hmom ?_
      have : (18 * (kk (blk H p) : ℝ) / H) ^ kk (blk H p) ≤ 1 :=
        pow_le_one₀ (by positivity) hratio
      linarith
    -- the threshold factor
    have hthr : (Real.exp (-α * (blk H p : ℝ) / H) ^ (2 * kk (blk H p)))⁻¹
        ≤ W ^ (2 * α) * Q ^ (2 * α) := by
      rw [← Real.exp_nat_mul, ← Real.exp_neg, Real.rpow_def_of_pos hW0,
        Real.rpow_def_of_pos (by linarith), ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hka : (kk (blk H p) : ℝ) * a < Real.log W + a := by
        rw [hkdef]
        calc (⌈Real.log W / a⌉₊ : ℝ) * a < (Real.log W / a + 1) * a :=
              mul_lt_mul_of_pos_right hk_up ha0
          _ = Real.log W + a := by field_simp
      have e1 : -(((2 * kk (blk H p) : ℕ) : ℝ) * (-α * (blk H p : ℝ) / H))
          = 2 * α * ((kk (blk H p) : ℝ) * a) := by rw [ha]; push_cast; ring
      rw [e1]
      have hα2 : 0 ≤ 2 * α := by linarith
      nlinarith
    have hthr0 : 0 ≤ (Real.exp (-α * (blk H p : ℝ) / H) ^ (2 * kk (blk H p)))⁻¹ := by positivity
    calc (Real.exp (-α * (blk H p : ℝ) / H) ^ (2 * kk (blk H p)))⁻¹
          * (∫ w in Icc (-W) W, ‖blockQ f Pr H (blk H p) w ^ kk (blk H p)‖ ^ (2 : ℕ))
        ≤ (W ^ (2 * α) * Q ^ (2 * α)) * 144 :=
          mul_le_mul hthr hmom' (setIntegral_nonneg measurableSet_Icc fun w _ => by positivity)
            (by positivity)
      _ = 144 * W ^ (2 * α) * Q ^ (2 * α) := by ring
  calc volume.real (Icc (-W) W ∩
        (smallAt (blockQ f Pr H) V (fun u => Real.exp (-α * u / H)))ᶜ)
      ≤ ∑ u ∈ V, (Real.exp (-α * u / H) ^ (2 * kk u))⁻¹
          * ∫ w in Icc (-W) W, ‖blockQ f Pr H u w ^ kk u‖ ^ (2 : ℕ) := hbase
    _ ≤ ∑ _u ∈ V, 144 * W ^ (2 * α) * Q ^ (2 * α) := sum_le_sum hterm
    _ = V.card * (144 * W ^ (2 * α) * Q ^ (2 * α)) := by rw [sum_const, nsmul_eq_mul]

/-- **Halász–Montgomery on the exceptional set, numerically.** -/
theorem exceptional_HM_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) (Pr : Finset ℕ)
    (rest : ℕ → Prop) [DecidablePred rest] (X : ℕ) (H : ℝ) (v : ℕ) (hlo : 1 ≤ cofLo X H v)
    (hloX : cofLo X H v ≤ X) {E : Set ℝ} (hEm : MeasurableSet E) {W : ℝ} (hW : 1 ≤ W)
    (hEs : E ⊆ Icc (-W) W) :
    (∫ w in E, ‖blockR f Pr rest X H v w‖ ^ 2)
      ≤ 6 + 4 * plainKernelFarConst (4 * X) (2 * Real.pi * W) * volume.real E / cofLo X H v
        + 384 * Real.log (2 + 2 * (2 * Real.pi * W)) := by
  set lo := cofLo X H v with hlodef
  have hlo0 : 0 < lo := by linarith
  have hbase := setIntegral_normSq_blockR_le_HM hf Pr rest X H v hlo hEm hW hEs
  rw [← hlodef] at hbase
  set N : ℕ := ⌊4 * lo⌋₊ with hN
  have hNle : (N : ℝ) ≤ 4 * lo := Nat.floor_le (by linarith)
  have hN4X : N ≤ 4 * X := by
    have : (N : ℝ) ≤ ((4 * X : ℕ) : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hT : (1 : ℝ) ≤ 2 * Real.pi * W := by nlinarith [Real.pi_gt_three]
  have hK : plainKernelFarConst N (2 * Real.pi * W) ≤ plainKernelFarConst (4 * X) (2 * Real.pi * W) :=
    plainKernelFarConst_mono hN4X _
  have hK0 : 0 ≤ plainKernelFarConst N (2 * Real.pi * W) := plainKernelFarConst_nonneg N hT
  have hE0 : 0 ≤ volume.real E := measureReal_nonneg
  have hlog0 : 0 ≤ Real.log (2 + 2 * (2 * Real.pi * W)) := Real.log_nonneg (by linarith)
  have hpi := Real.pi_pos
  have hpi3 := Real.pi_gt_three
  have hmass : hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E)
      ≤ 2 * (4 * lo) + plainKernelFarConst (4 * X) (2 * Real.pi * W) * (2 * Real.pi * volume.real E)
        + 4 * (12 * Real.pi * (4 * lo)) * Real.log (2 + 2 * (2 * Real.pi * W)) := by
    unfold hmMassRecip
    have h1 : plainKernelFarConst N (2 * Real.pi * W) * (2 * Real.pi * volume.real E)
        ≤ plainKernelFarConst (4 * X) (2 * Real.pi * W) * (2 * Real.pi * volume.real E) :=
      mul_le_mul_of_nonneg_right hK (by positivity)
    have h2 : 4 * (12 * Real.pi * (N : ℝ)) * Real.log (2 + 2 * (2 * Real.pi * W))
        ≤ 4 * (12 * Real.pi * (4 * lo)) * Real.log (2 + 2 * (2 * Real.pi * W)) := by
      have : 4 * (12 * Real.pi * (N : ℝ)) ≤ 4 * (12 * Real.pi * (4 * lo)) := by nlinarith
      exact mul_le_mul_of_nonneg_right this hlog0
    linarith
  have hfac : 0 ≤ (2 * Real.pi)⁻¹ * (4 / lo) := by positivity
  calc (∫ w in E, ‖blockR f Pr rest X H v w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹ * (hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E) * (4 / lo)) :=
        hbase
    _ = (2 * Real.pi)⁻¹ * (4 / lo) * hmMassRecip N (2 * Real.pi * W) (2 * Real.pi * volume.real E) := by
        ring
    _ ≤ (2 * Real.pi)⁻¹ * (4 / lo) * (2 * (4 * lo)
          + plainKernelFarConst (4 * X) (2 * Real.pi * W) * (2 * Real.pi * volume.real E)
          + 4 * (12 * Real.pi * (4 * lo)) * Real.log (2 + 2 * (2 * Real.pi * W))) :=
        mul_le_mul_of_nonneg_left hmass hfac
    _ = 16 / Real.pi + 4 * plainKernelFarConst (4 * X) (2 * Real.pi * W) * volume.real E / lo
          + 384 * Real.log (2 + 2 * (2 * Real.pi * W)) := by
        field_simp
        ring
    _ ≤ 6 + 4 * plainKernelFarConst (4 * X) (2 * Real.pi * W) * volume.real E / lo
          + 384 * Real.log (2 + 2 * (2 * Real.pi * W)) := by
        have : 16 / Real.pi ≤ 6 := by rw [div_le_iff₀ hpi]; linarith
        linarith

end

end GaloisForLFunctions.MatomakiRadziwill
