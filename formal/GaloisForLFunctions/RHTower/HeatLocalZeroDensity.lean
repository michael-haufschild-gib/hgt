import GaloisForLFunctions.RHTower.HeatEulerAnchor
import GaloisForLFunctions.RHTower.HeatLocalGrowth
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountAntitone
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound

/-!
# Local zero counts uniform down to zero heat

An Euler-region lower anchor and polynomial relative growth on a fixed
disk give a multiplicity-exact Jensen bound when `t log X ≤ 1`.
-/

open Complex MeasureTheory Filter Topology Set Metric MeromorphicOn
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

private theorem divisor_nonzero_const_mul {f : ℂ → ℂ} {U : Set ℂ}
    (hf : AnalyticOnNhd ℂ f U) {a : ℂ} (ha : a ≠ 0) :
    divisor (fun z => a * f z) U = divisor f U := by
  have hscaled : AnalyticOnNhd ℂ (fun z => a * f z) U := fun z hz =>
    analyticAt_const.mul (hf z hz)
  ext z
  by_cases hz : z ∈ U
  · have horder : analyticOrderAt (fun w => a * f w) z = analyticOrderAt f z := by
      have hc : AnalyticAt ℂ (fun _ : ℂ => a) z := analyticAt_const
      have hm := analyticOrderAt_smul hc (hf z hz)
      change analyticOrderAt (fun w => a * f w) z = _ at hm
      rw [hc.analyticOrderAt_eq_zero.mpr ha, zero_add] at hm
      exact hm
    rw [hscaled.divisor_apply hz, hf.divisor_apply hz, horder]
  · simp [hz]

private theorem norm_heat_euler_anchor_ge {t X : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8)
    (hX : 2048 ≤ X) (hα : 8 ≤ (horizontalSlope X).re)
    (htu : 2 * t * (horizontalSlope X).re ≤ 1) :
    ‖xiLine X 16‖ ≤ 8 * ‖riemannHeat t ((X : ℂ) - 16 * I)‖ := by
  rcases ht.eq_or_lt with hzero | hpos
  · subst t
    have heq : riemannHeat 0 ((X : ℂ) - 16 * I) = xiLine X 16 := by
      rw [riemannHeat_zero, xiLine]
      congr 1
      push_cast
      ring_nf
      rw [I_sq]
      ring
    rw [heq]
    nlinarith only [norm_nonneg (xiLine X 16)]
  · exact norm_xiLine_sixteen_le_eight_mul_norm_riemannHeat hpos ht8 hX hα htu

/-- The local Jensen count retains every zero with its full multiplicity. -/
theorem sum_divisor_riemannHeat_local_le {t X : ℝ} (ht : 0 ≤ t) (ht8 : t ≤ 1 / 8)
    (hX : 4096 ≤ X) (hL : 20 ≤ Real.log X) (hα : 8 ≤ (horizontalSlope X).re)
    (htL : t * Real.log X ≤ 1) :
    ((∑ᶠ z, divisor (riemannHeat t) (closedBall ((X : ℂ) - 16 * I) 18) z : ℤ) : ℝ) ≤
      ((Real.log 32 + 4360) / Real.log 2) * Real.log X := by
  set c : ℂ := (X : ℂ) - 16 * I
  set N := ‖xiLine X 16‖
  set F : ℂ → ℂ := fun z => (xiLine X 16)⁻¹ * riemannHeat t z
  set M := 4 * Real.exp (4096 + 264 * Real.log X)
  have hX0 : 0 < X := by linarith
  have hNne : xiLine X 16 ≠ 0 := by
    unfold xiLine
    apply xi_ne_zero_of_one_lt_re
    norm_num
  have hN : 0 < N := norm_pos_iff.mpr hNne
  have hL0 : 0 ≤ Real.log X := by linarith
  have hM : 1 ≤ M := by
    have he := Real.one_le_exp (show 0 ≤ 4096 + 264 * Real.log X by positivity)
    dsimp [M]
    linarith only [he]
  have hratio : Real.log (X / (2 * Real.pi)) ≤ Real.log X :=
    Real.log_le_log (by positivity) (div_le_self hX0.le (by nlinarith only [Real.pi_gt_three]))
  have htu : 2 * t * (horizontalSlope X).re ≤ 1 := by
    rw [horizontalSlope_re]
    nlinarith only [mul_le_mul_of_nonneg_left hratio ht, htL]
  have hanchor := norm_heat_euler_anchor_ge ht ht8 (by linarith) hα htu
  have hcentre : (1 / 8 : ℝ) ≤ ‖F c‖ := by
    dsimp [F]
    rw [norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv, le_div_iff₀ hN]
    linarith only [hanchor]
  have hH : ∀ U : Set ℂ, AnalyticOnNhd ℂ (riemannHeat t) U :=
    fun U z _ => (differentiable_riemannHeat ht).analyticAt z
  have hF : AnalyticOnNhd ℂ F (closedBall c |(36 : ℝ)|) := fun z hz =>
    analyticAt_const.mul (hH _ z hz)
  have hsphere : ∀ z ∈ sphere c |(36 : ℝ)|, ‖F z‖ ≤ M := by
    intro z hz
    have hznorm : ‖z - c‖ = 36 := by simpa only [mem_sphere, dist_eq_norm, abs_of_pos (by norm_num : (0 : ℝ) < 36)] using hz
    have hre := Complex.abs_re_le_norm (z - c)
    have him := Complex.abs_im_le_norm (z - c)
    rw [hznorm] at hre him
    have hx : |z.re - X| ≤ 64 := by
      have hc : c.re = X := by dsimp [c]; simp
      rw [Complex.sub_re, hc] at hre
      linarith only [hre]
    have hy : |z.im| ≤ 64 := by
      have hc : c.im = -16 := by dsimp [c]; norm_num
      rw [Complex.sub_im, hc] at him
      obtain ⟨hlo, hhi⟩ := abs_le.mp him
      exact abs_le.mpr ⟨by linarith only [hlo], by linarith only [hhi]⟩
    have hb := norm_riemannHeat_near_le_of_nonneg ht ht8 hX hL htL hx hy
    have hpt : (z.re : ℂ) + I * z.im = z := by
      rw [mul_comm I]
      exact Complex.re_add_im z
    rw [hpt] at hb
    dsimp [F]
    rw [norm_mul, norm_inv, mul_comm, ← div_eq_mul_inv, div_le_iff₀ hN]
    change ‖riemannHeat t z‖ ≤ M * N
    simpa [M, N, mul_assoc, mul_left_comm, mul_comm] using hb
  have hj := GaloisForLFunctions.HTGeometry.sum_divisor_le_of_bounds
    (c := c) (r := 18) (R := 36) (M := M) (m := 1 / 8)
    (by norm_num) (by norm_num) hM (by norm_num) hF hcentre hsphere
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 18)] at hj
  norm_num only at hj
  rw [divisor_nonzero_const_mul (hH _) (inv_ne_zero hNne)] at hj
  have hlog : Real.log (M / (1 / 8)) = Real.log 32 + 4096 + 264 * Real.log X := by
    have heq : M / (1 / 8) = 32 * Real.exp (4096 + 264 * Real.log X) := by dsimp [M]; ring
    rw [heq, Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp]
    ring
  rw [hlog] at hj
  have hnum : Real.log 32 + 4096 + 264 * Real.log X ≤
      (Real.log 32 + 4360) * Real.log X := by
    have hlog32 : 0 ≤ Real.log (32 : ℝ) := Real.log_nonneg (by norm_num)
    nlinarith only [mul_nonneg (show 0 ≤ Real.log X - 1 by linarith)
      (show 0 ≤ Real.log 32 + 4096 by linarith)]
  refine hj.trans ?_
  have hden : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have h := div_le_div_of_nonneg_right hnum hden.le
  convert h using 1
  ring

/-- A logarithmic local zero count, uniform for `0 ≤ t ≤ 1/8` and `t log X ≤ 1`. -/
theorem exists_sum_divisor_riemannHeat_local_le_log :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
        ((∑ᶠ z, divisor (riemannHeat t) (closedBall ((X : ℂ) - 16 * I) 18) z : ℤ) : ℝ) ≤
          C * Real.log X := by
  refine ⟨(Real.log 32 + 4360) / Real.log 2, ?_,
    4096 + 2 * Real.pi * Real.exp 20, ?_, ?_⟩
  · have hnum : 0 < Real.log (32 : ℝ) := Real.log_pos (by norm_num)
    have hden : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  · have hp : 0 ≤ 2 * Real.pi * Real.exp (20 : ℝ) := by positivity
    linarith only [hp]
  · intro X hX t ht ht8 htL
    have hX4096 : 4096 ≤ X := by
      have hp : 0 ≤ 2 * Real.pi * Real.exp (20 : ℝ) := by positivity
      linarith only [hX, hp]
    have hX0 : 0 < X := by linarith
    have hprod : 2 * Real.pi * Real.exp (20 : ℝ) ≤ X := by linarith only [hX]
    have hE : Real.exp (20 : ℝ) ≤ X := by
      have hp := mul_le_mul_of_nonneg_right
        (show (1 : ℝ) ≤ 2 * Real.pi by nlinarith only [Real.pi_gt_three]) (Real.exp_pos (20 : ℝ)).le
      nlinarith only [hprod, hp]
    have hL : 20 ≤ Real.log X := by
      have h := Real.log_le_log (Real.exp_pos (20 : ℝ)) hE
      simpa only [Real.log_exp] using h
    have hratio : Real.exp (20 : ℝ) ≤ X / (2 * Real.pi) :=
      (le_div_iff₀ (by positivity)).mpr (by simpa only [mul_comm] using hprod)
    have hα : 8 ≤ (horizontalSlope X).re := by
      have h := Real.log_le_log (Real.exp_pos (20 : ℝ)) hratio
      rw [Real.log_exp] at h
      rw [horizontalSlope_re]
      linarith only [h]
    exact sum_divisor_riemannHeat_local_le ht ht8 hX4096 hL hα htL

private theorem sum_zeroMult_riemannHeat_le_divisor {t : ℝ} (ht : 0 ≤ t)
    (c : ℂ) (r : ℝ) (S : Finset ℂ) (hS : ∀ z ∈ S, z ∈ closedBall c r) :
    ((∑ z ∈ S, zeroMult (riemannHeat t) z : ℕ) : ℝ) ≤
      ((∑ᶠ z, divisor (riemannHeat t) (closedBall c r) z : ℤ) : ℝ) := by
  classical
  have han : AnalyticOnNhd ℂ (riemannHeat t) (closedBall c r) := fun z _ =>
    (differentiable_riemannHeat ht).analyticAt z
  let D := divisor (riemannHeat t) (closedBall c r)
  let f : ℂ → ℤ := fun z => if z ∈ S then (zeroMult (riemannHeat t) z : ℤ) else 0
  have hf : Function.HasFiniteSupport f := by
    apply S.finite_toSet.subset
    intro z hz
    by_contra h
    change z ∉ S at h
    exact hz (by simp [f, h])
  have hD : Function.HasFiniteSupport (fun z => D z) := D.finiteSupport (isCompact_closedBall c r)
  have hvalue : ∀ z ∈ S, D z = (zeroMult (riemannHeat t) z : ℤ) := by
    intro z hz
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_riemannHeat_ne_top ht z)
    dsimp [D]
    rw [han.divisor_apply (hS z hz)]
    simp [zeroMult, ← hn]
  have hpoint : ∀ z, f z ≤ D z := by
    intro z
    by_cases hz : z ∈ S
    · simp only [f, hz, if_true, hvalue z hz, le_refl]
    · simp only [f, hz, if_false]
      exact MeromorphicOn.AnalyticOnNhd.divisor_nonneg han z
  have hsum := finsum_le_finsum' hf hD hpoint
  have hsumf : (∑ᶠ z, f z) = ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℤ) := by
    rw [finsum_eq_sum_of_support_subset f (s := S)]
    · exact Finset.sum_congr rfl fun z hz => by simp [f, hz]
    · intro z hz
      by_contra h
      change z ∉ S at h
      exact hz (by simp [f, h])
  rw [hsumf] at hsum
  exact_mod_cast hsum

private theorem heat_zero_mem_local_disk {t X : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) (hx : |z.re - X| ≤ 1) :
    z ∈ closedBall ((X : ℂ) - 16 * I) 18 := by
  have hy : |z.im| ≤ 1 / 2 := by
    rcases ht.eq_or_lt with hzero | hpos
    · subst t
      rw [riemannHeat_zero] at hz
      obtain ⟨hlo, hhi⟩ := xi_zero_re_mem_open_unit hz
      have hre : ((1 / 2 : ℂ) + I * z).re = 1 / 2 - z.im := by simp; ring
      rw [hre] at hlo hhi
      exact abs_le.mpr ⟨by linarith only [hhi], by linarith only [hlo]⟩
    · exact abs_im_le_half_of_riemannHeat_eq_zero hpos hz
  have him : |z.im + 16| ≤ 33 / 2 := by
    have h := abs_add_le z.im (16 : ℝ)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 16)] at h
    linarith only [h, hy]
  have hn := Complex.norm_le_abs_re_add_abs_im (z - ((X : ℂ) - 16 * I))
  have hre : (z - ((X : ℂ) - 16 * I)).re = z.re - X := by simp
  have him' : (z - ((X : ℂ) - 16 * I)).im = z.im + 16 := by simp
  rw [hre, him'] at hn
  rw [mem_closedBall, dist_eq_norm]
  linarith only [hn, hx, him]

/-- Every unit height window has logarithmically many heat zeros, counted with multiplicity,
uniformly throughout the range `t log X ≤ 1`. -/
theorem exists_sum_zeroMult_riemannHeat_near_le_log :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      ∀ X : ℝ, X₀ ≤ X → ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 8 → t * Real.log X ≤ 1 →
        ∀ S : Finset ℂ, (∀ z ∈ S, riemannHeat t z = 0) →
          (∀ z ∈ S, |z.re - X| ≤ 1) →
          ((∑ z ∈ S, zeroMult (riemannHeat t) z : ℕ) : ℝ) ≤ C * Real.log X := by
  obtain ⟨C, hC, X₀, hX₀, hbound⟩ := exists_sum_divisor_riemannHeat_local_le_log
  refine ⟨C, hC, X₀, hX₀, ?_⟩
  intro X hX t ht ht8 htL S hzero hnear
  have hmem : ∀ z ∈ S, z ∈ closedBall ((X : ℂ) - 16 * I) 18 :=
    fun z hz => heat_zero_mem_local_disk ht (hzero z hz) (hnear z hz)
  exact (sum_zeroMult_riemannHeat_le_divisor ht _ _ S hmem).trans (hbound X hX t ht ht8 htL)

end

end RHTower.DeBruijn
