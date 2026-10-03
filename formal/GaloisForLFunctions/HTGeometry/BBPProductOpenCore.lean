import GaloisForLFunctions.HTGeometry.BaileyCrandallParityDrift
import GaloisForLFunctions.HTGeometry.ParityDriftWeylCriterion

/-!
# The open core of the Parity-Drift Hypothesis for `π` as a product of BBP phases

With `R(k) = 4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6)` (`bbpTerm`), the BBP head
`hₙ = Σ_{k≤n} 16^{n−k} R(k)` gives `e(h 16ⁿ π) = Π_{k≤n} e(h 16^{n−k} R(k)) · e(h tₙ)` with
`tₙ = O(1/n)`.  Each factor `e(h 16^{n−k} R(k))` is a root of unity of order dividing
`(8k+1)(8k+4)(8k+5)(8k+6)`.

* `not_parityDriftHypothesis_pi_of_bbpProductSums`: if
  `N⁻¹ Σ_{n<N} Π_{k≤n} e(h 16^{n−k} R(k)) → 0` for every integer `h ≠ 0`, then the parity drift of
  `π` is `o(N)`.

The hypothesis concerns only roots of unity attached to the BBP denominators; it contains no
digits and no carries.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.BBPPi

open BinaryParityDrift

/-- The product `Π_{k≤n} e(h 16^{n−k} R(k))` of BBP phases. -/
noncomputable def bbpProduct (h : ℤ) (n : ℕ) : ℂ :=
  ∏ k ∈ range (n + 1),
    Complex.exp (2 * Real.pi * Complex.I * h * (((16 : ℝ) ^ (n - k) * bbpTerm k : ℝ) : ℂ))

theorem bbpHead_eq_sum (n : ℕ) :
    bbpHead n = ∑ k ∈ range (n + 1), (16 : ℝ) ^ (n - k) * bbpTerm k := by
  induction n with
  | zero => simp [bbpHead]
  | succ n ih =>
    rw [bbpHead, ih, sum_range_succ _ (n + 1), mul_sum, Nat.sub_self, pow_zero, one_mul]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [mem_range] at hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring

theorem exp_bbpHead (h : ℤ) (n : ℕ) :
    Complex.exp (2 * Real.pi * Complex.I * h * ((bbpHead n : ℝ) : ℂ)) = bbpProduct h n := by
  rw [bbpProduct, bbpHead_eq_sum, Complex.ofReal_sum, mul_sum, Complex.exp_sum]

theorem norm_exp_sixteen_pow_sub_bbpProduct_le (h : ℤ) (n : ℕ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * h * (((16 : ℝ) ^ n * Real.pi : ℝ) : ℂ)) -
      bbpProduct h n‖ ≤ 2 * Real.pi * |(h : ℝ)| * (4 / (8 * n + 9) / 15) := by
  have hsplit : Complex.exp (2 * Real.pi * Complex.I * h * (((16 : ℝ) ^ n * Real.pi : ℝ) : ℂ)) =
      bbpProduct h n * Complex.exp (((2 * Real.pi * h * bbpTail n : ℝ)) * Complex.I) := by
    rw [sixteen_pow_mul_pi, ← exp_bbpHead, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hP : ‖bbpProduct h n‖ = 1 := by
    rw [← exp_bbpHead, Complex.norm_exp]
    simp
  rw [hsplit, ← mul_sub_one, norm_mul, hP, one_mul]
  refine (StonehamPairDrift.norm_exp_mul_I_sub_one_le _).trans ?_
  rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi),
    abs_of_nonneg (bbpTail_nonneg n)]
  gcongr
  exact bbpTail_le n

/-- Weyl sums of `16ⁿ π` from the BBP product sums. -/
theorem tendsto_weylSum_sixteen_pi {h : ℤ}
    (hP : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, bbpProduct h n) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * h * (((16 : ℝ) ^ n * Real.pi : ℝ) : ℂ))) atTop
      (𝓝 0) := by
  have herr : Tendsto (fun n : ℕ => 2 * Real.pi * |(h : ℝ)| * (4 / (8 * n + 9) / 15)) atTop
      (𝓝 0) := by
    have := tendsto_bbpTail.const_mul (2 * Real.pi * |(h : ℝ)|)
    have h' : Tendsto (fun n : ℕ => 4 / (8 * (n : ℝ) + 9) / 15) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => 8 * (n : ℝ) + 9) atTop atTop :=
        tendsto_atTop_add_const_right _ _
          (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num))
      have h'' := (this.inv_tendsto_atTop.const_mul 4).div_const 15
      rw [mul_zero, zero_div] at h''
      exact h''.congr fun n => by simp only [Pi.inv_apply]; ring
    simpa using h'.const_mul (2 * Real.pi * |(h : ℝ)|)
  have hces := (squeeze_zero (fun n => norm_nonneg _)
    (fun n => norm_exp_sixteen_pow_sub_bbpProduct_le h n) herr).cesaro
  have hE : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      (Complex.exp (2 * Real.pi * Complex.I * h * (((16 : ℝ) ^ n * Real.pi : ℝ) : ℂ)) -
        bbpProduct h n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) hces
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    exact norm_sum_le _ _
  have h2 := hP.add hE
  rw [add_zero] at h2
  refine h2.congr fun N => ?_
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun n _ => by ring

/-- From Weyl sums of `16ⁿ x` at `k` and `4k` to Weyl sums of `4ⁿ x` at `k`. -/
theorem tendsto_weylSum_four_of_sixteen {x : ℝ} {k : ℤ}
    (h1 : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * k * (((16 : ℝ) ^ n * x : ℝ) : ℂ))) atTop (𝓝 0))
    (h4 : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * (4 * k : ℤ) * (((16 : ℝ) ^ n * x : ℝ) : ℂ))) atTop
      (𝓝 0)) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      Complex.exp (2 * Real.pi * Complex.I * k * (((4 : ℝ) ^ n * x : ℝ) : ℂ))) atTop (𝓝 0) := by
  set f : ℕ → ℂ := fun n =>
    Complex.exp (2 * Real.pi * Complex.I * k * (((4 : ℝ) ^ n * x : ℝ) : ℂ)) with hf
  set A : ℕ → ℂ := fun M => ∑ m ∈ range M,
    Complex.exp (2 * Real.pi * Complex.I * k * (((16 : ℝ) ^ m * x : ℝ) : ℂ)) with hA
  set B : ℕ → ℂ := fun M => ∑ m ∈ range M,
    Complex.exp (2 * Real.pi * Complex.I * (4 * k : ℤ) * (((16 : ℝ) ^ m * x : ℝ) : ℂ)) with hB
  have hnorm : ∀ n, ‖f n‖ ≤ 1 := fun n => by
    refine le_of_eq ?_
    simp only [hf]
    rw [show 2 * (Real.pi : ℂ) * Complex.I * k * (((4 : ℝ) ^ n * x : ℝ) : ℂ) =
      ((2 * Real.pi * k * ((4 : ℝ) ^ n * x) : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  -- `Σ_{n < 2M} f n = A M + B M`
  have hpair : ∀ M, ∑ n ∈ range (2 * M), f n = A M + B M := by
    intro M
    rw [ThreeFiveOrbit.sum_range_mul_eq_sum_sum f 2 M, sum_range_succ, sum_range_succ,
      sum_range_zero, zero_add]
    simp only [hf, hA, hB]
    congr 1 <;> refine sum_congr rfl fun m _ => ?_ <;> congr 1 <;> push_cast <;>
      rw [show (16 : ℂ) = 4 ^ 2 by norm_num, ← pow_mul] <;> ring
  -- `‖Σ_{n<N} f n − (A + B)(N/2)‖ ≤ 1`
  have hS : ∀ N, ‖∑ n ∈ range N, f n - (A (N / 2) + B (N / 2))‖ ≤ 1 := by
    intro N
    rw [← hpair]
    have hN : N = 2 * (N / 2) + N % 2 := (Nat.div_add_mod N 2).symm
    have e : ∑ n ∈ range N, f n = ∑ n ∈ range (2 * (N / 2)), f n +
        ∑ i ∈ range (N % 2), f (2 * (N / 2) + i) := by
      conv_lhs => rw [hN]
      exact sum_range_add f _ _
    rw [e, add_sub_cancel_left]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i ∈ range (N % 2), ‖f (2 * (N / 2) + i)‖ ≤ ∑ _i ∈ range (N % 2), (1 : ℝ) :=
          sum_le_sum fun i _ => hnorm _
      _ ≤ 1 := by simp; exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt N (by norm_num))
  have hhalf : Tendsto (fun N : ℕ => N / 2) atTop atTop :=
    Nat.tendsto_div_const_atTop (by norm_num)
  have hAB : Tendsto (fun M : ℕ => (M : ℂ)⁻¹ * (A M + B M)) atTop (𝓝 0) := by
    have := h1.add h4
    rw [add_zero] at this
    exact this.congr fun M => by rw [mul_add]
  have hratio : ∀ N : ℕ, 2 ≤ N → ‖(N : ℂ)⁻¹ * (A (N / 2) + B (N / 2))‖ ≤
      ‖((N / 2 : ℕ) : ℂ)⁻¹ * (A (N / 2) + B (N / 2))‖ := by
    intro N hN
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_natCast, Complex.norm_natCast]
    gcongr
    · exact_mod_cast Nat.div_pos hN (by norm_num)
    · exact_mod_cast Nat.div_le_self N 2
  have hmain : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * (A (N / 2) + B (N / 2))) atTop (𝓝 0) := by
    have hb := (hAB.comp hhalf).norm
    rw [norm_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop 2] with N hN
    exact hratio N hN
  have hrest : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * (∑ n ∈ range N, f n - (A (N / 2) + B (N / 2))))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    calc (N : ℝ)⁻¹ * ‖∑ n ∈ range N, f n - (A (N / 2) + B (N / 2))‖ ≤ (N : ℝ)⁻¹ * 1 := by
          gcongr; exact hS N
      _ = (fun n : ℕ => (n : ℝ)⁻¹) N := by simp
  have := hmain.add hrest
  rw [add_zero] at this
  exact this.congr fun N => by ring

/-- **The open core for `π`.**  If the averaged BBP product sums vanish at every frequency
`h ≠ 0`, the Parity-Drift Hypothesis fails for `π`. -/
theorem not_parityDriftHypothesis_pi_of_bbpProductSums
    (hP : ∀ h : ℤ, h ≠ 0 →
      Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, bbpProduct h n) atTop (𝓝 0)) :
    ¬ ParityDriftHypothesis Real.pi := by
  refine not_parityDriftHypothesis_of_weylSums fun k hk => ?_
  exact tendsto_weylSum_four_of_sixteen (tendsto_weylSum_sixteen_pi (hP k hk))
    (tendsto_weylSum_sixteen_pi (hP (4 * k) (by omega)))

end GaloisForLFunctions.HTGeometry.BBPPi
