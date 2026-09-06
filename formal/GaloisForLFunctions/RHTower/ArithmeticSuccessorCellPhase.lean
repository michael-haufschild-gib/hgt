import GaloisForLFunctions.RHTower.EulerDeletionPowerSumRemainder
import Mathlib.Topology.Algebra.Order.Floor

/-!
# Alternating signs in the actual successor-cell remainder

The complete Bernoulli cell is exactly a normalized successor difference of the
ordinary power-sum remainder. Finite sums retain the final endpoint, and ordinary
infinite cutoffs recover the initial normalized remainder.

At the exact height `pi / log 2`, cells starting at `2^k` alternate strictly in
imaginary sign with depth, for every real part. Both signs occur arbitrarily far
out. Thus the whole tail's proposed phase sign cannot be proved by assigning
one sign to every sufficiently late unit cell. This does not refute the proposed
whole-tail sign, concern zeros at that height, or supply an RH implication.
All statements use symbolic integration and arithmetic; no numerical input occurs.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped BigOperators
namespace RHTower.DeletionMixedRefinement

/-- Imaginary Bernoulli-tail contribution of one complete integer cell, anchored at one. -/
def bernoulliPhaseCell (sigma t : ℝ) (m : ℕ) : ℝ :=
  ∫ x in (m : ℝ)..((m : ℝ)+1),
    RHTower.bernoulliPeriodic x * x^(-sigma-2) * Real.sin (t*Real.log x)

/-- The literal complex Bernoulli-tail cell before taking its imaginary part. -/
def bernoulliComplexCell (s : ℂ) (m : ℕ) : ℂ :=
  ∫ x in (m : ℝ)..((m : ℝ)+1),
    (RHTower.bernoulliPeriodic x : ℂ) * (x : ℂ)^(-star s-2)

private theorem cell_kernel_continuous : Continuous RHTower.bernoulliPeriodic := by
  have hc : Continuous (fun x : ℝ => (x^2-x)/2) := by fun_prop
  exact hc.continuousOn.comp_fract'' (by norm_num)

private theorem cell_kernel_neg {m : ℕ} {x : ℝ}
    (hx : x ∈ Ioo (m : ℝ) ((m : ℝ)+1)) : RHTower.bernoulliPeriodic x < 0 := by
  have hf : Int.floor x = (m : ℤ) := by
    apply Int.floor_eq_iff.mpr
    simpa using And.intro hx.1.le hx.2
  have he : Int.fract x = x-(m : ℝ) := by simp only [Int.fract, hf, Int.cast_natCast]
  rw [RHTower.bernoulliPeriodic, he]
  have h0 : 0 < x-(m : ℝ) := by linarith [hx.1]
  have h1 : 0 < 1-(x-(m : ℝ)) := by linarith [hx.2]
  nlinarith [mul_pos h0 h1]

private theorem cell_integrable (sigma t : ℝ) {m : ℕ} (hm : 0 < m) :
    IntervalIntegrable (fun x : ℝ =>
      RHTower.bernoulliPeriodic x * x^(-sigma-2) * Real.sin (t*Real.log x))
      volume (m : ℝ) ((m : ℝ)+1) := by
  have hx (x : ℝ) (hx : x ∈ Icc (m : ℝ) ((m : ℝ)+1)) : 0 < x :=
    lt_of_lt_of_le (by exact_mod_cast hm) hx.1
  have hp : ContinuousOn (fun x : ℝ => x^(-sigma-2)) (Icc (m : ℝ) ((m : ℝ)+1)) :=
    continuousOn_id.rpow_const (fun x h => Or.inl (hx x h).ne')
  have hl : ContinuousOn Real.log (Icc (m : ℝ) ((m : ℝ)+1)) :=
    continuousOn_id.log (fun x h => (hx x h).ne')
  have hsin : ContinuousOn (fun x => Real.sin (t*Real.log x))
      (Icc (m : ℝ) ((m : ℝ)+1)) :=
    Real.continuous_sin.comp_continuousOn (continuousOn_const.mul hl)
  exact (cell_kernel_continuous.continuousOn.mul hp |>.mul hsin).intervalIntegrable_of_Icc (by linarith)

/-- The real phase cell is exactly the imaginary part of the literal complex cell. -/
theorem bernoulliComplexCell_im (s : ℂ) {m : ℕ} (hm : 0 < m) :
    (bernoulliComplexCell s m).im = bernoulliPhaseCell s.re s.im m := by
  have hx (x : ℝ) (hx : x ∈ uIcc (m : ℝ) ((m : ℝ)+1)) : 0 < x := by
    rw [uIcc_of_le (by linarith)] at hx
    exact lt_of_lt_of_le (by exact_mod_cast hm) hx.1
  have hi : IntervalIntegrable (fun x : ℝ =>
      (RHTower.bernoulliPeriodic x : ℂ) * (x : ℂ)^(-star s-2))
      volume (m : ℝ) ((m : ℝ)+1) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.mul
      (Complex.continuous_ofReal.comp cell_kernel_continuous).continuousOn
    exact ContinuousOn.cpow_const (by fun_prop)
      (fun x h => Or.inl (by simpa using hx x h))
  have he := Complex.imCLM.intervalIntegral_comp_comm hi
  change (∫ x in (m : ℝ)..((m : ℝ)+1),
    ((RHTower.bernoulliPeriodic x : ℂ) * (x : ℂ)^(-star s-2)).im) =
    (bernoulliComplexCell s m).im at he
  rw [← he, bernoulliPhaseCell]
  apply intervalIntegral.integral_congr
  intro x h
  have hp := hx x h
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  change ((RHTower.bernoulliPeriodic x : ℂ) * (x : ℂ)^(-star s-2)).im =
    RHTower.bernoulliPeriodic x * x^(-s.re-2) * Real.sin (s.im*Real.log x)
  rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, add_zero,
    Complex.cpow_def_of_ne_zero hxc, ← Complex.ofReal_log hp.le, Complex.exp_im,
    Real.rpow_def_of_pos hp]
  simp [Complex.mul_re, Complex.mul_im, mul_assoc, mul_comm]

/-- Exact successor recurrence, including the complete trapezoid defect. -/
theorem powerSumRemainder_successor_difference (s : ℂ) (m : ℕ) :
    powerSumRemainder s (m+1)-powerSumRemainder s m =
      (kernel s m + kernel s (m+1))/2 -
      (((m+1:ℕ):ℂ)^(1-s)-(m:ℂ)^(1-s))/(1-s) := by
  simp only [powerSumRemainder, rawPrefix, Finset.sum_range_succ]
  ring

/-- The complex cell is precisely the normalized backward difference of the actual
ordinary remainder. Thus its sign is source information, not an auxiliary model. -/
theorem bernoulliComplexCell_eq_remainder_difference {s : ℂ} (hs : 0 < s.re)
    (hs1 : s ≠ 1) {m : ℕ} (hm : 1 ≤ m) :
    bernoulliComplexCell s m =
      (star (powerSumRemainder s m)-star (powerSumRemainder s (m+1))) /
        (star s*(star s+1)) := by
  have hu : -1 < (star s).re := by simp; linarith
  have hu1 : star s ≠ 1 := by intro h; apply hs1; simpa using congrArg star h
  have hd : star s*(star s+1) ≠ 0 := by
    apply mul_ne_zero
    · intro h; have he := congrArg Complex.re h; simp at he; linarith
    · intro h; have he := congrArg Complex.re h; simp at he; linarith
  have hr0 := powerSumRemainder_eq_bernoulli hu hu1 hm
  have hr1 := powerSumRemainder_eq_bernoulli hu hu1 (show 1 ≤ m+1 by omega)
  rw [powerSumRemainder_star (by linarith : -1 < s.re) hs1] at hr0 hr1
  rw [hr0, hr1, ← mul_sub, mul_div_cancel_left₀ _ hd]
  have hi := RHTower.integrableOn_bernoulli_cpow hu hm
  have he := intervalIntegral.integral_Ioi_sub_Ioi hi
    (show (m:ℝ) ≤ ((m+1:ℕ):ℝ) by exact_mod_cast Nat.le_succ m)
  simpa only [RHTower.zetaBernoulliTail, bernoulliComplexCell,
    Nat.cast_add, Nat.cast_one, show -star s-1-1 = -star s-2 by ring] using he.symm

/-- Every finite cell decomposition retains the exact remainder at its final cutoff. -/
theorem sum_bernoulliComplexCell {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) (N : ℕ) :
    (∑ k ∈ Finset.range N, bernoulliComplexCell s (m+k)) =
      (star (powerSumRemainder s m)-star (powerSumRemainder s (m+N))) /
        (star s*(star s+1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih,
      bernoulliComplexCell_eq_remainder_difference hs hs1 (show 1 ≤ m+N by omega)]
    simp only [Nat.add_assoc]
    ring

/-- The complete ordinary-cutoff cell sum converges to the normalized actual remainder.
Alternation of selected cell signs does not determine this limit's sign. -/
theorem tendsto_sum_bernoulliComplexCell {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1)
    {m : ℕ} (hm : 1 ≤ m) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, bernoulliComplexCell s (m+k))
      atTop (𝓝 (star (powerSumRemainder s m)/(star s*(star s+1)))) := by
  have hr := (tendsto_powerSumRemainder (by linarith : -1 < s.re) hs1).star.comp
    (tendsto_add_atTop_nat m)
  have ht := (hr.const_sub (star (powerSumRemainder s m))).div_const (star s*(star s+1))
  simp only [star_zero, sub_zero] at ht
  apply ht.congr
  intro N
  rw [sum_bernoulliComplexCell hs hs1 hm]
  simp only [Function.comp_apply, Nat.add_comm N m]

private theorem dyadic_phase_in_half_turn {k : ℕ} {x : ℝ}
    (hx : x ∈ Ioo ((2:ℝ)^k) ((2:ℝ)^k+1)) :
    0 < Real.pi / Real.log 2 * Real.log x - k*Real.pi ∧
      Real.pi / Real.log 2 * Real.log x - k*Real.pi < Real.pi := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hrate : 0 < Real.pi / Real.log 2 := div_pos Real.pi_pos hlog
  have hp : 0 < (2:ℝ)^k := pow_pos (by norm_num) _
  have hp1 : (1:ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
  have hu : x < (2:ℝ)^(k+1) := by rw [pow_succ]; linarith [hx.2]
  have hl := Real.log_lt_log hp hx.1
  have hr := Real.log_lt_log (hp.trans hx.1) hu
  rw [Real.log_pow] at hl hr
  have hlo := mul_lt_mul_of_pos_left hl hrate
  have hhi := mul_lt_mul_of_pos_left hr hrate
  have he (j : ℕ) : Real.pi / Real.log 2 * (j * Real.log 2) = j*Real.pi := by
    field_simp
  rw [he] at hlo hhi
  push_cast at hhi
  constructor <;> nlinarith

/-- At an exact fixed positive height, every dyadic depth determines the cell's sign.
The real part is arbitrary: the only real-part factor is a strictly positive weight. -/
theorem bernoulliPhaseCell_dyadic_alternates (sigma : ℝ) (k : ℕ) :
    (-1:ℝ)^k * bernoulliPhaseCell sigma (Real.pi / Real.log 2) (2^k) < 0 := by
  have hm : 0 < (2:ℕ)^k := pow_pos (by omega) _
  have hi := (cell_integrable sigma (Real.pi / Real.log 2) hm).const_mul ((-1:ℝ)^k)
  have hpos : 0 < ∫ x in ((2^k:ℕ):ℝ)..(((2^k:ℕ):ℝ)+1),
      -((-1:ℝ)^k * (RHTower.bernoulliPeriodic x * x^(-sigma-2) *
        Real.sin (Real.pi / Real.log 2 * Real.log x))) := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hi.neg ?_ (by linarith)
    intro x hx
    have hx' : x ∈ Ioo ((2:ℝ)^k) ((2:ℝ)^k+1) := by exact_mod_cast hx
    have ht := dyadic_phase_in_half_turn hx'
    have hs := Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2
    have he : Real.sin (Real.pi / Real.log 2 * Real.log x) =
        (-1:ℝ)^k * Real.sin (Real.pi / Real.log 2 * Real.log x - k*Real.pi) := by
      have h := Real.sin_add_nat_mul_pi
        (Real.pi / Real.log 2 * Real.log x - k*Real.pi) k
      convert h using 1
      congr 1
      ring
    have hw : 0 < x^(-sigma-2) :=
      Real.rpow_pos_of_pos ((pow_pos (by norm_num : (0:ℝ)<2) k).trans hx'.1) _
    have hb := cell_kernel_neg hx
    have hh : (-1:ℝ)^k * (-1:ℝ)^k = 1 := by rw [← mul_pow]; norm_num
    change 0 < -((-1:ℝ)^k * (RHTower.bernoulliPeriodic x * x^(-sigma-2) *
      Real.sin (Real.pi / Real.log 2 * Real.log x)))
    rw [he]
    have halg : -((-1:ℝ)^k * (RHTower.bernoulliPeriodic x * x^(-sigma-2) *
        ((-1:ℝ)^k * Real.sin (Real.pi / Real.log 2 * Real.log x - k*Real.pi)))) =
        (-RHTower.bernoulliPeriodic x) * x^(-sigma-2) *
          Real.sin (Real.pi / Real.log 2 * Real.log x - k*Real.pi) := by
      calc
        _ = (-1:ℝ)^k * (-1:ℝ)^k * ((-RHTower.bernoulliPeriodic x) * x^(-sigma-2) *
          Real.sin (Real.pi / Real.log 2 * Real.log x - k*Real.pi)) := by ring
        _ = _ := by rw [hh, one_mul]
    rw [halg]
    exact mul_pos (mul_pos (neg_pos.mpr hb) hw) hs
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_const_mul] at hpos
  exact neg_pos.mp hpos

/-- Every even dyadic depth gives a strictly negative complete cell. -/
theorem bernoulliPhaseCell_even_depth_neg (sigma : ℝ) (k : ℕ) :
    bernoulliPhaseCell sigma (Real.pi / Real.log 2) (2^(2*k)) < 0 := by
  have h := bernoulliPhaseCell_dyadic_alternates sigma (2*k)
  simpa [pow_mul] using h

/-- Every odd dyadic depth gives a strictly positive complete cell. -/
theorem bernoulliPhaseCell_odd_depth_pos (sigma : ℝ) (k : ℕ) :
    0 < bernoulliPhaseCell sigma (Real.pi / Real.log 2) (2^(2*k+1)) := by
  have h := bernoulliPhaseCell_dyadic_alternates sigma (2*k+1)
  have he : (-1:ℝ)^(2*k+1) = -1 := by simp [pow_add, pow_mul]
  rw [he, neg_one_mul] at h
  exact neg_neg_iff_pos.mp h

/-- Both signs occur arbitrarily far along the literal integer-cell decomposition. -/
theorem bernoulliPhaseCell_both_signs_cofinally (sigma : ℝ) (N : ℕ) :
    (∃ m : ℕ, N ≤ m ∧ bernoulliPhaseCell sigma (Real.pi / Real.log 2) m < 0) ∧
    (∃ m : ℕ, N ≤ m ∧ 0 < bernoulliPhaseCell sigma (Real.pi / Real.log 2) m) := by
  constructor
  · refine ⟨2^(2*N), ?_, bernoulliPhaseCell_even_depth_neg sigma N⟩
    have h := Nat.lt_two_pow_self (n := 2*N)
    omega
  · refine ⟨2^(2*N+1), ?_, bernoulliPhaseCell_odd_depth_pos sigma N⟩
    have h := Nat.lt_two_pow_self (n := 2*N+1)
    omega

/-- In particular, no finite cell cutoff makes all later cell contributions nonpositive. -/
theorem not_eventually_bernoulliPhaseCell_nonpos (sigma : ℝ) :
    ¬ ∃ N : ℕ, ∀ m : ℕ, N ≤ m → bernoulliPhaseCell sigma (Real.pi / Real.log 2) m ≤ 0 := by
  rintro ⟨N, hN⟩
  obtain ⟨m, hm, hp⟩ := (bernoulliPhaseCell_both_signs_cofinally sigma N).2
  exact (not_lt_of_ge (hN m hm)) hp

end RHTower.DeletionMixedRefinement
