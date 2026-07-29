import GaloisForLFunctions.HTGeometry.CentralBinomialDiagonalKernel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Mixed even trigonometric moments

This file proves the exact Wallis moment on a quarter circle and identifies the resulting
quadratic moment with the diagonal central-binomial kernel.  The proof uses only an integration
by parts recurrence and the central-binomial recurrence.
-/

open MeasureTheory
open scoped BigOperators Nat Real Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- One-step recurrence for the normalized central-binomial coefficient. -/
lemma normalizedCentralBinom_succ (n : ℕ) :
    normalizedCentralBinom (n + 1) =
      normalizedCentralBinom n * (2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2) := by
  rw [normalizedCentralBinom, normalizedCentralBinom, pow_succ]
  have hcb : ((n : ℝ) + 1) * (Nat.centralBinom (n + 1) : ℝ) =
      2 * (2 * (n : ℝ) + 1) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast Nat.succ_mul_centralBinom_succ n
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [h4, hn]
  linear_combination 2 * hcb

/-- Even cosine moments on the quarter circle are normalized central-binomial coefficients. -/
lemma integral_cos_pow_even_zero_pi_div_two (n : ℕ) :
    (∫ x in (0 : ℝ)..Real.pi / 2, Real.cos x ^ (2 * n)) =
      (Real.pi / 2) * normalizedCentralBinom n := by
  induction n with
  | zero => simp [normalizedCentralBinom]
  | succ n ih =>
      have h := @integral_cos_pow (0 : ℝ) (Real.pi / 2) (2 * n)
      rw [show 2 * (n + 1) = 2 * n + 2 by omega, h, ih,
        normalizedCentralBinom_succ]
      simp only [Real.cos_pi_div_two, Real.sin_pi_div_two, Real.cos_zero,
        Real.sin_zero, Nat.cast_ofNat, mul_zero, sub_zero, Nat.cast_mul]
      have hden : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
      field_simp [hden]
      ring

/-- The mixed even trigonometric moment on the quarter circle. -/
def mixedEvenTrigQuarterIntegral (m n : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..Real.pi / 2,
    Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n)

/-- Integration by parts recurrence for mixed even quarter-circle moments. -/
lemma mixedEvenTrigQuarterIntegral_succ (m n : ℕ) :
    mixedEvenTrigQuarterIntegral (m + 1) n =
      (2 * (m : ℝ) + 1) / (2 * ((m : ℝ) + (n : ℝ) + 1)) *
        mixedEvenTrigQuarterIntegral m n := by
  let F : ℝ → ℝ := fun x =>
    Real.sin x ^ (2 * m + 1) * Real.cos x ^ (2 * n + 1)
  let dF : ℝ → ℝ := fun x =>
    (2 * (m : ℝ) + 1) *
        (Real.sin x ^ (2 * m) * Real.cos x ^ (2 * (n + 1))) -
      (2 * (n : ℝ) + 1) *
        (Real.sin x ^ (2 * (m + 1)) * Real.cos x ^ (2 * n))
  have hF (x : ℝ) : HasDerivAt F (dF x) x := by
    dsimp only [F, dF]
    have hs : HasDerivAt (fun y => Real.sin y ^ (2 * m + 1))
        ((2 * (m : ℝ) + 1) * Real.cos x * Real.sin x ^ (2 * m)) x := by
      have hp := (Real.hasDerivAt_sin x).pow (2 * m + 1)
      rw [show (fun y => Real.sin y ^ (2 * m + 1)) =
          Real.sin ^ (2 * m + 1) by
        funext y
        rfl]
      apply hp.congr_deriv
      push_cast
      ring
    have hc : HasDerivAt (fun y => Real.cos y ^ (2 * n + 1))
        (-(2 * (n : ℝ) + 1) * Real.sin x * Real.cos x ^ (2 * n)) x := by
      have hp := (Real.hasDerivAt_cos x).pow (2 * n + 1)
      rw [show (fun y => Real.cos y ^ (2 * n + 1)) =
          Real.cos ^ (2 * n + 1) by
        funext y
        rfl]
      apply hp.congr_deriv
      push_cast
      ring
    have hmul := hs.mul hc
    rw [show
      (fun y =>
        Real.sin y ^ (2 * m + 1) * Real.cos y ^ (2 * n + 1)) =
      (fun y => Real.sin y ^ (2 * m + 1)) *
        (fun y => Real.cos y ^ (2 * n + 1)) by
      funext y
      rfl]
    apply hmul.congr_deriv
    ring
  have hderiv : deriv F = dF := by
    funext x
    exact (hF x).deriv
  have hfund := intervalIntegral.integral_deriv_eq_sub'
    F hderiv (fun x _ => (hF x).differentiableAt) (by
      dsimp only [dF]
      fun_prop : ContinuousOn dF [[(0 : ℝ), Real.pi / 2]])
  have hrel :
      (2 * (m : ℝ) + 1) * mixedEvenTrigQuarterIntegral m (n + 1) =
        (2 * (n : ℝ) + 1) * mixedEvenTrigQuarterIntegral (m + 1) n := by
    have hzero : (∫ x in (0 : ℝ)..Real.pi / 2, dF x) = 0 := by
      rw [hfund]
      dsimp only [F]
      simp
    have hcalc : (∫ x in (0 : ℝ)..Real.pi / 2, dF x) =
        (2 * (m : ℝ) + 1) * mixedEvenTrigQuarterIntegral m (n + 1) -
          (2 * (n : ℝ) + 1) * mixedEvenTrigQuarterIntegral (m + 1) n := by
      dsimp only [dF, mixedEvenTrigQuarterIntegral]
      rw [intervalIntegral.integral_sub]
      · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      · apply Continuous.intervalIntegrable
        fun_prop
      · apply Continuous.intervalIntegrable
        fun_prop
    rw [hcalc] at hzero
    linarith
  have hsplit :
      mixedEvenTrigQuarterIntegral m n =
        mixedEvenTrigQuarterIntegral (m + 1) n +
          mixedEvenTrigQuarterIntegral m (n + 1) := by
    dsimp only [mixedEvenTrigQuarterIntegral]
    rw [← intervalIntegral.integral_add]
    · apply intervalIntegral.integral_congr
      intro x _
      change Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n) =
        Real.sin x ^ (2 * (m + 1)) * Real.cos x ^ (2 * n) +
          Real.sin x ^ (2 * m) * Real.cos x ^ (2 * (n + 1))
      have htrig := Real.sin_sq_add_cos_sq x
      have hsin : Real.sin x ^ (2 * (m + 1)) =
          Real.sin x ^ (2 * m) * Real.sin x ^ 2 := by
        rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
      have hcos : Real.cos x ^ (2 * (n + 1)) =
          Real.cos x ^ (2 * n) * Real.cos x ^ 2 := by
        rw [show 2 * (n + 1) = 2 * n + 2 by omega, pow_add]
      rw [hsin, hcos]
      linear_combination
        -(Real.sin x ^ (2 * m) * Real.cos x ^ (2 * n)) * htrig
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      fun_prop
  have hden : 2 * ((m : ℝ) + (n : ℝ) + 1) ≠ 0 := by positivity
  rw [div_mul_eq_mul_div]
  apply (eq_div_iff hden).2
  linear_combination -(2 * (m : ℝ) + 1) * hsplit - hrel

/-- Exact mixed Wallis moment. -/
theorem mixedEvenTrigQuarterIntegral_closed (m n : ℕ) :
    mixedEvenTrigQuarterIntegral m n =
      (Real.pi / 2) * normalizedCentralBinom m * normalizedCentralBinom n /
        (Nat.choose (m + n) m : ℝ) := by
  induction m with
  | zero =>
      simp [mixedEvenTrigQuarterIntegral, integral_cos_pow_even_zero_pi_div_two,
        normalizedCentralBinom]
  | succ m ih =>
      rw [mixedEvenTrigQuarterIntegral_succ, ih, normalizedCentralBinom_succ]
      have hchoose : ((m + n : ℝ) + 1) * (Nat.choose (m + n) m : ℝ) =
          (Nat.choose (m + 1 + n) (m + 1) : ℝ) * ((m : ℝ) + 1) := by
        have hnat : (m + n + 1) * Nat.choose (m + n) m =
            Nat.choose (m + 1 + n) (m + 1) * (m + 1) := by
          simpa only [show m + n + 1 = m + 1 + n by omega] using
            Nat.add_one_mul_choose_eq (m + n) m
        exact_mod_cast hnat
      have hC0 : (Nat.choose (m + n) m : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : m ≤ m + n)))
      have hC1 : (Nat.choose (m + 1 + n) (m + 1) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt
          (Nat.choose_pos (by omega : m + 1 ≤ m + 1 + n)))
      have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
      have hsum : (m : ℝ) + (n : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hC0, hC1, hm1, hsum]
      ring_nf at hchoose ⊢
      linear_combination -normalizedCentralBinom m * normalizedCentralBinom n * hchoose

/-- The normalized quarter-circle quadratic moment is the diagonal kernel coefficient. -/
theorem quarterIntegral_quadraticPow_eq_centralBinomialDiagonalKernelCoefficient
    (B D : ℝ) (n : ℕ) :
    (2 / Real.pi) *
        (∫ x in (0 : ℝ)..Real.pi / 2,
          (D ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2) ^ n) =
      centralBinomialDiagonalKernelCoefficient B D n := by
  rw [centralBinomialDiagonalKernelCoefficient]
  have hsum :
      (∫ x in (0 : ℝ)..Real.pi / 2,
          (D ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2) ^ n) =
        ∑ k ∈ Finset.range (n + 1),
          (Nat.choose n k : ℝ) * (D ^ 2) ^ k * (B ^ 2) ^ (n - k) *
            mixedEvenTrigQuarterIntegral k (n - k) := by
    rw [show (fun x : ℝ =>
        (D ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2) ^ n) =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (Nat.choose n k : ℝ) * (D ^ 2) ^ k * (B ^ 2) ^ (n - k) *
          (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * (n - k))) by
      funext x
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro k _
      rw [mul_pow, mul_pow, pow_mul, pow_mul]
      ring]
    rw [intervalIntegral.integral_finsetSum]
    apply Finset.sum_congr rfl
    intro k _
    rw [show (fun x : ℝ =>
        (Nat.choose n k : ℝ) * (D ^ 2) ^ k * (B ^ 2) ^ (n - k) *
          (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * (n - k)))) =
      fun x : ℝ =>
        ((Nat.choose n k : ℝ) * (D ^ 2) ^ k * (B ^ 2) ^ (n - k)) *
          (Real.sin x ^ (2 * k) * Real.cos x ^ (2 * (n - k))) by
      funext x
      ring]
    rw [intervalIntegral.integral_const_mul]
    rfl
    intro k _
    apply Continuous.intervalIntegrable
    fun_prop
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  rw [mixedEvenTrigQuarterIntegral_closed]
  have hchoose : (Nat.choose n k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos hkn))
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [Nat.add_sub_of_le hkn]
  field_simp [hchoose, hpi]

/-- A continuous, reflection-symmetric `pi`-periodic function integrates to four times its
quarter-period integral. -/
lemma integral_zero_two_pi_eq_four_mul_quarter
    {f : ℝ → ℝ} (hf : Continuous f)
    (hperiod : Function.Periodic f Real.pi)
    (hreflect : ∀ x : ℝ, f (Real.pi - x) = f x) :
    (∫ x in (0 : ℝ)..2 * Real.pi, f x) =
      4 * ∫ x in (0 : ℝ)..Real.pi / 2, f x := by
  have hint : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    fun a b => hf.intervalIntegrable a b
  have hfull := hperiod.intervalIntegral_add_zsmul_eq (2 : ℤ) (0 : ℝ) hint
  have hfull' : (∫ x in (0 : ℝ)..2 * Real.pi, f x) =
      2 * ∫ x in (0 : ℝ)..Real.pi, f x := by
    convert hfull using 1 <;> norm_num
  have hsub := intervalIntegral.integral_comp_mul_add
    (f := f) (a := (0 : ℝ)) (b := Real.pi / 2)
    (c := (-1 : ℝ)) (by norm_num) Real.pi
  have hsecond : (∫ x in Real.pi / 2..Real.pi, f x) =
      ∫ x in (0 : ℝ)..Real.pi / 2, f x := by
    have hrefIntegral :
        (∫ x in (0 : ℝ)..Real.pi / 2, f (-1 * x + Real.pi)) =
          ∫ x in (0 : ℝ)..Real.pi / 2, f x := by
      apply intervalIntegral.integral_congr
      intro x _
      change f (-1 * x + Real.pi) = f x
      rw [show -1 * x + Real.pi = Real.pi - x by ring, hreflect]
    rw [hrefIntegral] at hsub
    simpa [show -(Real.pi / 2) + Real.pi = Real.pi / 2 by ring,
      ← intervalIntegral.integral_symm] using hsub.symm
  have hhalf :
      (∫ x in (0 : ℝ)..Real.pi / 2, f x) +
          ∫ x in Real.pi / 2..Real.pi, f x =
        ∫ x in (0 : ℝ)..Real.pi, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable (0 : ℝ) (Real.pi / 2))
      (hf.intervalIntegrable (Real.pi / 2) Real.pi)
  calc
    (∫ x in (0 : ℝ)..2 * Real.pi, f x) =
        2 * ∫ x in (0 : ℝ)..Real.pi, f x := hfull'
    _ = 2 * ((∫ x in (0 : ℝ)..Real.pi / 2, f x) +
        ∫ x in Real.pi / 2..Real.pi, f x) := by rw [hhalf]
    _ = 4 * ∫ x in (0 : ℝ)..Real.pi / 2, f x := by rw [hsecond]; ring

/-- The real diagonal trigonometric kernel. -/
def diagonalTrigKernel (B D : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (D ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2) ^ n

lemma continuous_diagonalTrigKernel (B D : ℝ) (n : ℕ) :
    Continuous (diagonalTrigKernel B D n) := by
  change Continuous (fun x : ℝ =>
    (D ^ 2 * Real.sin x ^ 2 + B ^ 2 * Real.cos x ^ 2) ^ n)
  fun_prop

lemma periodic_diagonalTrigKernel (B D : ℝ) (n : ℕ) :
    Function.Periodic (diagonalTrigKernel B D n) Real.pi := by
  intro x
  simp only [diagonalTrigKernel, Real.sin_add_pi, Real.cos_add_pi, neg_sq]

lemma reflect_diagonalTrigKernel (B D : ℝ) (n : ℕ) (x : ℝ) :
    diagonalTrigKernel B D n (Real.pi - x) = diagonalTrigKernel B D n x := by
  simp only [diagonalTrigKernel, Real.sin_pi_sub, Real.cos_pi_sub, neg_sq]

/-- Full-circle normalized integral representation of the diagonal kernel coefficient. -/
theorem normalizedIntegral_diagonalTrigKernel_eq_coefficient
    (B D : ℝ) (n : ℕ) :
    (2 * Real.pi)⁻¹ *
        (∫ x in (0 : ℝ)..2 * Real.pi, diagonalTrigKernel B D n x) =
      centralBinomialDiagonalKernelCoefficient B D n := by
  rw [integral_zero_two_pi_eq_four_mul_quarter
    (continuous_diagonalTrigKernel B D n)
    (periodic_diagonalTrigKernel B D n)
    (reflect_diagonalTrigKernel B D n)]
  rw [← quarterIntegral_quadraticPow_eq_centralBinomialDiagonalKernelCoefficient B D n]
  dsimp only [diagonalTrigKernel]
  field_simp [Real.pi_ne_zero]
  ring

end


end GaloisForLFunctions.HTGeometry
