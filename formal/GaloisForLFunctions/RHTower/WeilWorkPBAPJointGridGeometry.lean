import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Actual logarithmic-grid geometry at growing width

For every positive width coefficient, the concrete width
`b L log(log L) exp(-L/2)` eventually has positive integer endpoints,
short length comparable to `exp(L) W`, dyadic containment and logarithmic
coverage of the full auxiliary cutoff. Both endpoint roundings and the
padded right endpoint are paid explicitly; no interval budget is assumed
in the eventual conclusions.
-/

open Real Set Filter Topology
noncomputable section
namespace RHTower.WeilWorkPBAP

private theorem exp_window_difference_le {W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1/8) :
    exp (2*W)-exp (-2*W) ≤ 4*exp 1*W := by
  have hd : ∀ z ∈ Icc (-2*W) (2*W), DifferentiableAt ℝ exp z :=
    fun z _ => (Real.hasDerivAt_exp z).differentiableAt
  have hb : ∀ z ∈ Icc (-2*W) (2*W), ‖deriv exp z‖ ≤ exp 1 := by
    intro z hz
    rw [(Real.hasDerivAt_exp z).deriv, Real.norm_eq_abs, abs_of_pos (exp_pos z)]
    exact exp_le_exp.mpr (by linarith [hz.2])
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _)
    (show -2*W ∈ Icc (-2*W) (2*W) by constructor <;> linarith)
    (show 2*W ∈ Icc (-2*W) (2*W) by constructor <;> linarith)
  have habs : |2*W-(-2*W)| = 4*W := by
    rw [abs_of_nonneg (by linarith : 0 ≤ 2*W-(-2*W))]; ring
  rw [Real.norm_eq_abs, Real.norm_eq_abs, habs] at h
  exact (le_abs_self _).trans (h.trans_eq (by ring))

/-- Both roundings and the padded right endpoint are included in the length budget. -/
theorem joint_grid_geometry {N W : ℝ} (hN : 4 ≤ N) (hW : 0 < W)
    (hW1 : W ≤ 1/8) (hNW : 1 ≤ N*W) (hsmall : (4*exp 1+3)*W ≤ 1/2) :
    let n := ⌊N*exp (-2*W)⌋₊
    let m := ⌈N*exp (2*W)⌉₊+1
    2 ≤ n ∧ N/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ N ∧ n < m ∧ m ≤ 2*n+1 ∧
      2*N*W ≤ ((m-n:ℕ):ℝ) ∧ ((m-n:ℕ):ℝ) ≤ (4*exp 1+3)*N*W := by
  let n := ⌊N*exp (-2*W)⌋₊
  let m := ⌈N*exp (2*W)⌉₊+1
  change 2 ≤ n ∧ N/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ N ∧ n < m ∧ m ≤ 2*n+1 ∧ _
  have hN0 : 0 < N := by linarith
  have hnlo := Nat.lt_floor_add_one (N*exp (-2*W))
  have hnhi : (n:ℝ) ≤ N*exp (-2*W) := Nat.floor_le (by positivity)
  have hmlo : N*exp (2*W)+1 ≤ (m:ℝ) := by
    simpa only [m, Nat.cast_add, Nat.cast_one] using
      (add_le_add (Nat.le_ceil (N*exp (2*W))) (le_refl (1:ℝ)))
  have hmhi : (m:ℝ) < N*exp (2*W)+2 := by
    have h := Nat.ceil_lt_add_one (show 0 ≤ N*exp (2*W) by positivity)
    dsimp only [m]
    push_cast
    linarith
  have helo : 1-2*W ≤ exp (-2*W) := by linarith [Real.add_one_le_exp (-2*W)]
  have hehi : exp (-2*W) ≤ 1 := exp_le_one_iff.mpr (by linarith)
  have hntop : (n:ℝ) ≤ N :=
    hnhi.trans ((mul_le_mul_of_nonneg_left hehi hN0.le).trans_eq (mul_one N))
  have hnlow : N/2 ≤ (n:ℝ) := by
    have he := mul_le_mul_of_nonneg_left helo hN0.le
    have hw := mul_le_mul_of_nonneg_left hW1 hN0.le
    change N*exp (-2*W) < (n:ℝ)+1 at hnlo
    nlinarith
  have hnd : 2 ≤ n := by exact_mod_cast (show (2:ℝ) ≤ n by linarith)
  have hdelta : 2*W ≤ exp (2*W)-exp (-2*W) := by
    linarith [Real.add_one_le_exp (2*W)]
  have hlengthlo : 2*N*W ≤ (m:ℝ)-(n:ℝ) := by
    have h := mul_le_mul_of_nonneg_left hdelta hN0.le
    nlinarith
  have hnm : n < m := by
    have : (n:ℝ) < m := by nlinarith
    exact_mod_cast this
  have hlengthhi : (m:ℝ)-(n:ℝ) ≤ (4*exp 1+3)*N*W := by
    have h := mul_le_mul_of_nonneg_left (exp_window_difference_le hW hW1) hN0.le
    change N*exp (-2*W) < (n:ℝ)+1 at hnlo
    nlinarith
  have hdyad : m ≤ 2*n+1 := by
    have hs := mul_le_mul_of_nonneg_left hsmall hN0.le
    have : (m:ℝ) ≤ 2*(n:ℝ)+1 := by nlinarith
    exact_mod_cast this
  refine ⟨hnd, hnlow, hntop, hnm, hdyad, ?_, ?_⟩ <;>
    rw [Nat.cast_sub hnm.le]
  · exact hlengthlo
  · exact hlengthhi

/-- The source-independent growing width in the uniform two-window certificate. -/
def jointUniformWidth (b L : ℝ) : ℝ := b*L*log (log L)*exp (-L/2)

theorem jointUniformWidth_grid_scale (b L : ℝ) :
    exp L*jointUniformWidth b L = b*L*log (log L)*exp (L/2) := by
  unfold jointUniformWidth
  rw [show exp L*(b*L*log (log L)*exp (-L/2)) =
    b*L*log (log L)*(exp L*exp (-L/2)) by ring, ← exp_add]
  congr 2
  ring

theorem tendsto_jointUniformWidth_zero {b : ℝ} (hb : 0 < b) :
    Tendsto (jointUniformWidth b) atTop (𝓝 0) := by
  have hp := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (1/2) (by norm_num)).const_mul b
  have hmajor : Tendsto (fun L : ℝ => b*L^2*exp (-L/2)) atTop (𝓝 0) := by
    have he (L : ℝ) : -(1/2:ℝ)*L = -L/2 := by ring
    simpa only [Real.rpow_two, he, mul_zero, mul_assoc] using hp
  have hlog := (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (0:ℝ)
  have hL := eventually_ge_atTop (1:ℝ)
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [hlog, hL] with L hl hL
    unfold jointUniformWidth
    positivity
  · filter_upwards [hlog, hL] with L hl hL
    have hll : log (log L) ≤ L :=
      (log_le_self (log_nonneg hL)).trans (log_le_self (by linarith))
    unfold jointUniformWidth
    calc
      _ ≤ b*L*L*exp (-L/2) := by gcongr
      _ = _ := by ring

/-- The actual growing width satisfies every interval-geometry side condition. -/
theorem eventually_jointUniformWidth_grid_bounds {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop, 4 ≤ exp L ∧ 0 < jointUniformWidth b L ∧
      jointUniformWidth b L ≤ 1/8 ∧ 1 ≤ exp L*jointUniformWidth b L ∧
      (4*exp 1+3)*jointUniformWidth b L ≤ 1/2 := by
  have hw := tendsto_jointUniformWidth_zero hb
  have hs := hw.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1/8))
  have hcs := (hw.const_mul (4*exp 1+3)).eventually
    (gt_mem_nhds (by norm_num : (4*exp 1+3)*(0:ℝ) < 1/2))
  have hl := (tendsto_log_atTop.comp tendsto_log_atTop).eventually_ge_atTop (1:ℝ)
  filter_upwards [hs, hcs, hl, eventually_ge_atTop (1:ℝ),
    eventually_ge_atTop (1/b), tendsto_exp_atTop.eventually_ge_atTop (4:ℝ)]
    with L hs hcs hl hL hbL hN
  change 1 ≤ log (log L) at hl
  have hW : 0 < jointUniformWidth b L := by unfold jointUniformWidth; positivity
  refine ⟨hN, hW, hs.le, ?_, ?_⟩
  · rw [jointUniformWidth_grid_scale]
    have hbL' : 1 ≤ b*L := by
      have h := (div_le_iff₀ hb).mp hbL
      nlinarith
    have he : 1 ≤ exp (L/2) := one_le_exp_iff.mpr (by linarith)
    calc
      (1:ℝ) ≤ b*L := hbL'
      _ ≤ b*L*log (log L) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hl (zero_le_one.trans hbL')
      _ ≤ b*L*log (log L)*exp (L/2) := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left he
          (mul_nonneg (zero_le_one.trans hbL') (zero_le_one.trans hl))
  · simpa only [mul_zero] using hcs.le

/-- All actual endpoints and the short length are certified, without a supplied geometry budget. -/
theorem eventually_jointUniformWidth_grid_geometry {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop,
      let W := jointUniformWidth b L
      let N := exp L
      let n := ⌊N*exp (-2*W)⌋₊
      let m := ⌈N*exp (2*W)⌉₊+1
      2 ≤ n ∧ N/2 ≤ (n:ℝ) ∧ (n:ℝ) ≤ N ∧ n < m ∧ m ≤ 2*n+1 ∧
        2*N*W ≤ ((m-n:ℕ):ℝ) ∧ ((m-n:ℕ):ℝ) ≤ (4*exp 1+3)*N*W := by
  filter_upwards [eventually_jointUniformWidth_grid_bounds hb] with L h
  exact joint_grid_geometry h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2

/-- The actual logarithmic endpoints enclose the entire auxiliary cutoff support. -/
theorem eventually_jointUniformWidth_log_cover {b : ℝ} (hb : 0 < b) :
    ∀ᶠ L : ℝ in atTop,
      let W := jointUniformWidth b L
      let n := ⌊exp L*exp (-2*W)⌋₊
      let m := ⌈exp L*exp (2*W)⌉₊+1
      log (n:ℝ)-L ≤ -2*W ∧ 2*W ≤ log (m:ℝ)-L := by
  filter_upwards [eventually_jointUniformWidth_grid_geometry hb] with L h
  let W := jointUniformWidth b L
  let n := ⌊exp L*exp (-2*W)⌋₊
  let m := ⌈exp L*exp (2*W)⌉₊+1
  change log (n:ℝ)-L ≤ -2*W ∧ 2*W ≤ log (m:ℝ)-L
  have hn2 : 2 ≤ n := h.1
  have hnpos : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnleft : (n:ℝ) ≤ exp (L-2*W) := by
    have hn : (n:ℝ) ≤ exp L*exp (-2*W) := Nat.floor_le (by positivity)
    refine hn.trans_eq ?_
    rw [← exp_add]
    congr 1
    ring
  have hmright : exp (L+2*W) ≤ (m:ℝ) := by
    rw [exp_add]
    exact (Nat.le_ceil _).trans
      (by exact_mod_cast Nat.le_succ ⌈exp L*exp (2*W)⌉₊)
  have hleft := log_le_log hnpos hnleft
  have hright := log_le_log (exp_pos (L+2*W)) hmright
  rw [log_exp] at hleft hright
  constructor <;> linarith

end RHTower.WeilWorkPBAP
