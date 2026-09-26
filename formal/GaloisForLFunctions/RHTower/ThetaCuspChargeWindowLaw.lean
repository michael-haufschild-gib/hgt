import GaloisForLFunctions.RHTower.ThetaModularFareyBound
import GaloisForLFunctions.RHTower.ThetaCuspChargeContourShift
import GaloisForLFunctions.Bottcher.ThetaWronskian
import GaloisForLFunctions.Bottcher.QuarticCusp

open Complex
open scoped Real

namespace RHTower

noncomputable section

open Bottcher

theorem norm_jacobiTheta₂_half_sub_two_le_exp {τ : ℂ} (hτ : (4 : ℝ) / 5 ≤ τ.im) :
    ‖jacobiTheta₂ (τ / 2) τ - 2‖ ≤ 3 * Real.exp (-(Real.pi / 2 * τ.im)) := by
  have hτ0 : 0 < τ.im := by linarith
  set t : ℝ := Real.exp (-(Real.pi / 2 * τ.im)) with ht_def
  have ht0 : 0 ≤ t := (Real.exp_pos _).le
  have ht35 : t < 7 / 20 := by
    have : Real.exp (-(Real.pi / 2 * τ.im)) ≤ Real.exp (-(2 / 5 * Real.pi)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    linarith [exp_neg_two_fifths_pi_lt]
  have ht1 : t < 1 := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hnat : Summable (fun n : ℕ => t ^ n) := summable_geometric_of_lt_one ht0 ht1
  have hgsum : Summable (fun n : ℤ => t ^ n.natAbs) := by
    rw [summable_int_iff_summable_nat_and_neg]; exact ⟨by simpa using hnat, by simpa using hnat⟩
  have hgval : ∑' n : ℤ, t ^ n.natAbs = (1 + t) / (1 - t) := by
    have heven : (fun n : ℤ => t ^ n.natAbs).Even := fun n => by simp only [Int.natAbs_neg]
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat heven hgsum]
    have hpnat : (∑' n : ℕ+, t ^ ((n : ℤ)).natAbs) = t / (1 - t) := by
      have h1 : (∑' n : ℕ+, t ^ ((n : ℤ)).natAbs) = ∑' n : ℕ+, t ^ ((n : ℕ)) := by
        apply tsum_congr; intro n; simp
      rw [h1, tsum_pnat_eq_tsum_succ (f := fun k => t ^ k),
        show (fun n : ℕ => t ^ (n + 1)) = (fun n => t * t ^ n) from by funext n; rw [pow_succ]; ring,
        tsum_mul_left, tsum_geometric_of_lt_one ht0 ht1, div_eq_mul_inv]
    rw [hpnat, show ((0 : ℤ)).natAbs = 0 from rfl, pow_zero]
    simp only [nsmul_eq_mul]
    field_simp
    ring
  set f : ℤ → ℂ := fun n => jacobiTheta₂_term n (τ / 2) τ with hf_def
  have hfsum : Summable f := (summable_jacobiTheta₂_term_iff (τ / 2) τ).mpr hτ0
  set c : ℤ → ℂ := fun n => if n = 0 ∨ n = -1 then 1 else 0 with hc_def
  have hcHS : HasSum c (∑ i ∈ ({0, -1} : Finset ℤ), c i) := by
    apply hasSum_sum_of_ne_finset_zero
    intro n hn; rw [hc_def]; simp only; rw [if_neg]; rintro (rfl | rfl) <;> simp at hn
  have hc_tsum : ∑' n, c n = 2 := by
    rw [hcHS.tsum_eq, Finset.sum_pair (show (0 : ℤ) ≠ -1 by norm_num)]; norm_num [hc_def]
  have hcsum : Summable c := hcHS.summable
  have hbound : ∀ n : ℤ, ‖f n - c n‖ ≤ t * t ^ n.natAbs := by
    intro n
    by_cases h : n = 0 ∨ n = -1
    · rcases h with rfl | rfl
      · rw [hf_def, hc_def]; simp only [jacobiTheta₂_half_term_zero]; norm_num; positivity
      · rw [hf_def, hc_def]; simp only [jacobiTheta₂_half_term_negone]; norm_num; positivity
    · have hc0 : c n = 0 := by rw [hc_def]; simp only; rw [if_neg h]
      rw [hc0, sub_zero, hf_def, norm_jacobiTheta₂_half_term]
      have hne : n ≠ -1 := fun he => h (Or.inr he)
      have hne0 : n ≠ 0 := fun he => h (Or.inl he)
      have hcomp : |(n : ℝ)| ≤ (n : ℝ) ^ (2 : ℕ) + n := sq_add_self_ge_abs n hne
      have hge1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hne0
      have habs : (n.natAbs : ℝ) = |(n : ℝ)| := by
        rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
      rw [ht_def, ← pow_succ', ← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      have hpt : 0 < Real.pi * τ.im := mul_pos Real.pi_pos hτ0
      push_cast
      rw [habs]
      nlinarith [hcomp, hge1, hpt]
  have hmajor : Summable (fun n : ℤ => t * t ^ n.natAbs) := hgsum.mul_left t
  have hfcsum : Summable (fun n => ‖f n - c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hmajor
  have hjt : jacobiTheta₂ (τ / 2) τ = ∑' n, f n := rfl
  have he : jacobiTheta₂ (τ / 2) τ - 2 = ∑' n, (f n - c n) := by
    rw [hjt, Summable.tsum_sub hfsum hcsum, hc_tsum]
  rw [he]
  calc ‖∑' n, (f n - c n)‖ ≤ ∑' n, ‖f n - c n‖ := norm_tsum_le_tsum_norm hfcsum
    _ ≤ ∑' n : ℤ, t * t ^ n.natAbs := Summable.tsum_mono hfcsum hmajor hbound
    _ = t * ((1 + t) / (1 - t)) := by rw [tsum_mul_left, hgval]
    _ ≤ 3 * t := by
        rw [mul_div_assoc', div_le_iff₀ h1t]; nlinarith

/-- The normalized error of `θ₄⁴θ₃⁴/θ₂⁷` against its leading atom `2⁻⁷e^{-7πiv/4}`. -/
def chargeErr (v : ℂ) : ℂ :=
  2 ^ 7 * thetaFour v ^ 4 * thetaThree v ^ 4 / jacobiTheta₂ (v / 2) v ^ 7 - 1

theorem norm_one_add_pow_sub_one_le_charge (x : ℂ) (n : ℕ) :
    ‖(1 + x) ^ n - 1‖ ≤ (1 + ‖x‖) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h : (1 + x) ^ (n + 1) - 1 = (1 + x) * ((1 + x) ^ n - 1) + x := by ring
    have h1 : ‖1 + x‖ ≤ 1 + ‖x‖ := by
      refine le_trans (norm_add_le _ _) ?_; simp
    rw [h]
    calc ‖(1 + x) * ((1 + x) ^ n - 1) + x‖ ≤ ‖1 + x‖ * ‖(1 + x) ^ n - 1‖ + ‖x‖ := by
          refine le_trans (norm_add_le _ _) ?_; rw [norm_mul]
      _ ≤ (1 + ‖x‖) * ((1 + ‖x‖) ^ n - 1) + ‖x‖ := by
          have := mul_le_mul h1 ih (norm_nonneg _) (by positivity)
          linarith
      _ = (1 + ‖x‖) ^ (n + 1) - 1 := by ring

theorem exp_neg_pi_lt_twentieth : Real.exp (-π) < 1 / 20 := by
  have hπ : 3 < π := Real.pi_gt_three
  have h1 : Real.exp (-π) < Real.exp (-3) := Real.exp_lt_exp.mpr (by linarith)
  have h2 : Real.exp (-3) < 1 / 20 := by
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos _) (by norm_num)]
    have := Real.add_one_le_exp (3 : ℝ)
    have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have he := Real.exp_one_gt_d9
    rw [h3]
    have h4 := pow_lt_pow_left₀ he (by norm_num) (by norm_num : (3:ℕ) ≠ 0)
    norm_num at h4 ⊢; linarith
  linarith

theorem norm_chargeErr_le {v : ℂ} (hv : 4 ≤ v.im) : ‖chargeErr v‖ ≤ 1 / 8 := by
  have hv0 : 0 < v.im := by linarith
  have he := exp_neg_pi_lt_twentieth
  have hepos := Real.exp_pos (-π)
  have hK := jacobiThetaTailConstant_mul_exp_neg_pi_lt
  have hKpos := jacobiThetaTailConstant_pos
  -- the three cusp errors
  set x : ℂ := thetaThree v - 1 with hx_def
  set y : ℂ := thetaFour v - 1 with hy_def
  set z : ℂ := jacobiTheta₂ (v / 2) v / 2 - 1 with hz_def
  have hsmall : jacobiThetaTailConstant * Real.exp (-π * v.im) ≤ 1 / 200 := by
    have h1 : Real.exp (-π * v.im) ≤ Real.exp (-π) * Real.exp (-π) * Real.exp (-π) := by
      rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h2 : jacobiThetaTailConstant * (Real.exp (-π) * Real.exp (-π) * Real.exp (-π)) ≤
        1 / 2 * (1 / 20) * (1 / 20) := by
      have := mul_lt_mul'' hK he (by positivity) hepos.le
      have h3 := mul_lt_mul'' this he (by positivity) hepos.le
      nlinarith [h3]
    calc jacobiThetaTailConstant * Real.exp (-π * v.im)
        ≤ jacobiThetaTailConstant * (Real.exp (-π) * Real.exp (-π) * Real.exp (-π)) :=
          mul_le_mul_of_nonneg_left h1 hKpos.le
      _ ≤ 1 / 200 := by linarith
  have hx : ‖x‖ ≤ 1 / 200 := le_trans (norm_thetaThree_sub_one_le (by linarith)) hsmall
  have hy : ‖y‖ ≤ 1 / 200 := le_trans (norm_thetaFour_sub_one_le (by linarith)) hsmall
  have hz : ‖z‖ ≤ 1 / 200 := by
    have h1 := norm_jacobiTheta₂_half_sub_two_le_exp (τ := v) (by linarith)
    have h2 : Real.exp (-(π / 2 * v.im)) ≤ Real.exp (-π) * Real.exp (-π) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos])
    have h3 : Real.exp (-π) * Real.exp (-π) ≤ 1 / 20 * (1 / 20) :=
      mul_le_mul he.le he.le hepos.le (by norm_num)
    have hzeq : z = (jacobiTheta₂ (v / 2) v - 2) / 2 := by rw [hz_def]; ring
    rw [hzeq, norm_div, Complex.norm_ofNat]
    have : ‖jacobiTheta₂ (v / 2) v - 2‖ ≤ 3 * (1 / 20 * (1 / 20)) := by
      refine le_trans h1 ?_; nlinarith
    linarith
  have h3 : thetaThree v = 1 + x := by rw [hx_def]; ring
  have h4 : thetaFour v = 1 + y := by rw [hy_def]; ring
  have hJ : jacobiTheta₂ (v / 2) v = 2 * (1 + z) := by rw [hz_def]; ring
  have hz1 : ‖(1 : ℂ) + z‖ ≥ 199 / 200 := by
    have := norm_sub_norm_le (1 + z) (-z)
    simp only [sub_neg_eq_add, norm_neg] at this
    have h5 : ‖(1:ℂ)‖ ≤ ‖1 + z‖ + ‖z‖ := by
      calc ‖(1:ℂ)‖ = ‖(1 + z) + -z‖ := by ring_nf
        _ ≤ ‖1 + z‖ + ‖-z‖ := norm_add_le _ _
        _ = ‖1 + z‖ + ‖z‖ := by rw [norm_neg]
    rw [norm_one] at h5; linarith
  have hz0 : (1 : ℂ) + z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz1; norm_num at hz1
  have herr : chargeErr v = (((1 + (x + y + x * y)) ^ 4 - 1) - ((1 + z) ^ 7 - 1)) / (1 + z) ^ 7 := by
    unfold chargeErr
    rw [h3, h4, hJ]
    field_simp
    ring
  have hxy : ‖x + y + x * y‖ ≤ 3 / 200 := by
    calc ‖x + y + x * y‖ ≤ ‖x‖ + ‖y‖ + ‖x‖ * ‖y‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_mul]; linarith [norm_add_le x y]
      _ ≤ 1 / 200 + 1 / 200 + 1 / 200 * (1 / 200) := by
          have := mul_le_mul hx hy (norm_nonneg _) (by norm_num); linarith
      _ ≤ 3 / 200 := by norm_num
  have hA := norm_one_add_pow_sub_one_le_charge (x + y + x * y) 4
  have hB := norm_one_add_pow_sub_one_le_charge z 7
  have hA' : (1 + ‖x + y + x * y‖) ^ 4 - 1 ≤ (1 + 3 / 200) ^ 4 - 1 := by
    have := pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖x + y + x * y‖ ≤ 1 + 3 / 200) 4
    linarith
  have hB' : (1 + ‖z‖) ^ 7 - 1 ≤ (1 + 1 / 200) ^ 7 - 1 := by
    have := pow_le_pow_left₀ (by positivity) (by linarith : 1 + ‖z‖ ≤ 1 + 1 / 200) 7
    linarith
  have hden : (199 / 200 : ℝ) ^ 7 ≤ ‖(1 + z) ^ 7‖ := by
    rw [norm_pow]; exact pow_le_pow_left₀ (by norm_num) hz1 7
  rw [herr, norm_div]
  rw [div_le_iff₀ (lt_of_lt_of_le (by norm_num) hden)]
  calc ‖((1 + (x + y + x * y)) ^ 4 - 1) - ((1 + z) ^ 7 - 1)‖
      ≤ ‖(1 + (x + y + x * y)) ^ 4 - 1‖ + ‖(1 + z) ^ 7 - 1‖ := norm_sub_le _ _
    _ ≤ ((1 + 3 / 200) ^ 4 - 1) + ((1 + 1 / 200) ^ 7 - 1) := by linarith
    _ ≤ 1 / 8 * (199 / 200) ^ 7 := by norm_num
    _ ≤ 1 / 8 * ‖(1 + z) ^ 7‖ := by linarith

theorem arg_neg_I_mul_ne_pi {v : ℂ} (hv : 0 < v.im) : (-Complex.I * v).arg ≠ π := by
  have hre : 0 < (-Complex.I * v).re := by simp [Complex.mul_re]; exact hv
  have := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  intro h; rw [h, abs_of_pos Real.pi_pos] at this; linarith [Real.pi_pos]

/-- **Exact window law at the pole cusp `1`.**  Near `τ = 1` the form `θ₃h = θ₂⁴θ₄⁴/θ₃⁷` is the
leading atom `-(-iv)^{1/2}2⁻⁷e^{-7πiv/4}` of the inverted variable `v = -1/(τ-1)`, times `1+ε`. -/
theorem thetaGroupBasis_one_window {v : ℂ} (hv : 0 < v.im) :
    thetaGroupBasis 1 (1 + -1 / v) = -((-Complex.I * v) ^ (1 / 2 : ℂ)) *
      ((2 : ℂ) ^ 7)⁻¹ * Complex.exp (-(7 * π * Complex.I * v / 4)) * (1 + chargeErr v) := by
  have hv0 : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  set τ₀ : ℂ := -1 / v with hτ₀
  set P : ℂ := (-Complex.I * v) ^ (1 / 2 : ℂ) with hP
  have hIv : Complex.I / v = (-Complex.I * v)⁻¹ := by
    field_simp; exact Complex.I_sq
  have hQ : (Complex.I / v) ^ (1 / 2 : ℂ) = P⁻¹ := by
    rw [hIv, Complex.inv_cpow _ _ (arg_neg_I_mul_ne_pi hv)]
  have hP0 : P ≠ 0 := by
    rw [hP]; intro h
    rw [Complex.cpow_eq_zero_iff] at h
    have : -Complex.I * v ≠ 0 := mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hv0
    exact this h.1
  have h2 := thetaTwo_S v hv0
  have h3 := thetaThree_S v hv0
  have h4 := thetaFour_S v hv0
  rw [hQ, one_div, inv_inv] at h2 h4
  rw [← hP] at h3
  have ht2 : thetaTwo v ≠ 0 := thetaTwo_ne_zero_of_im_pos hv
  have ht3 : thetaThree v ≠ 0 := thetaThree_ne_zero_of_im_pos hv
  have ht4 : thetaFour v ≠ 0 := thetaFour_ne_zero_of_im_pos hv
  have hθ2 : thetaTwo v = Complex.exp (π * Complex.I * v / 4) * jacobiTheta₂ (v / 2) v := rfl
  have hJ0 : jacobiTheta₂ (v / 2) v ≠ 0 := by
    intro h; apply ht2; rw [hθ2, h, mul_zero]
  have hexp : Complex.exp (π * Complex.I * v / 4) ^ 7 * Complex.exp (-(7 * π * Complex.I * v / 4))
      = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]; ring_nf; simp
  have hbasis : thetaGroupBasis 1 (1 + τ₀) =
      thetaFour τ₀ * (-(thetaTwo τ₀ ^ 4) * thetaThree τ₀ ^ 4 / thetaFour τ₀ ^ 8) := by
    unfold thetaGroupBasis thetaGroupHauptmodul
    rw [add_comm, thetaThree_add_one, thetaTwo_pow4_add_one, thetaFour_add_one]
    ring
  rw [hbasis, h2, h3, h4, hθ2]
  unfold chargeErr
  field_simp
  have hexp' : Complex.exp (π * Complex.I * v / 4) ^ 7 *
      Complex.exp (-(π * Complex.I * v * 7 / 4)) = 1 := by
    rw [show (π : ℂ) * Complex.I * v * 7 / 4 = 7 * π * Complex.I * v / 4 by ring]; exact hexp
  linear_combination (2 ^ 7 * thetaFour v ^ 4 * thetaThree v ^ 4) * hexp'
