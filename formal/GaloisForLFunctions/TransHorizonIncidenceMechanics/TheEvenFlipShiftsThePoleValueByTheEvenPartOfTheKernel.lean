import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipPairsOverTheOddSquarefreeWeightAreClassifiedAtThePole

/-!
# The even flip shifts the pole value by the even part of the kernel

Let `k` be a kernel on `[1, J]` vanishing on multiples of four and `c = k ⋆ o`, `o` the odd squarefree
weight. Split `k = k_o + δ₂ ⋆ k_e` into its odd part and its even part `k_e(j) = 1_{odd}(j) k(2j)`.
Since `k_o ⋆ o` and `k_e ⋆ o` live on the odd integers, the even part of `c` is exactly `k_e ⋆ o`, and
**the even flip of `c` is `c^♭ = k^♭ ⋆ o` with `k^♭ = k_o + k_e − δ₂ ⋆ k_e`**: the dilation `k ↦ 2k`
moves the even part of the kernel onto the odd integers and reverses its sign at `2`.

On the pole values, with `K_o, K_e` the Dirichlet polynomials of `k_o, k_e`,
`K(1 − ε) = K_o + 2^{ε−1} K_e`, `K^♭(1 − ε) = K_o + (1 − 2^{ε−1}) K_e`, so

`K^♭(1 − ε) = K(1 − ε) + (1 − 2^{ε}) K_e(1 − ε)`.

The two weights have the same Ramanujan amplitudes, and for `0 < ε ≤ 1/2` each is paid exactly when
its pole value vanishes. **The exact loss of the even flip is `(1 − 2^{ε}) K_e(1 − ε)`:** the flip
preserves the receiver of every weight whose even part vanishes at the pole, and otherwise at most one
member of the pair is paid.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Kernel calculus -/

/-- The odd part `k_o = 1_{odd} k` of a kernel. -/
def oddPartKernel (k : ℕ → ℝ) (j : ℕ) : ℝ := if j % 2 = 1 then k j else 0

/-- The dilation by `2`: `(δ₂ ⋆ b)(j) = b(j/2)` on even `j`. -/
def shiftTwo (b : ℕ → ℝ) (j : ℕ) : ℝ := if 2 ∣ j then b (j / 2) else 0

/-- The flipped kernel `k^♭ = k_o + k_e − δ₂ ⋆ k_e`. -/
def flipKernelOf (k : ℕ → ℝ) (j : ℕ) : ℝ :=
  oddPartKernel k j + evenPartWeight k j - shiftTwo (evenPartWeight k) j

theorem dirichletConv_add_sub_left (a b e c : ℕ → ℝ) (n : ℕ) :
    RHTower.dirichletConv (fun j => a j + b j - e j) c n =
      RHTower.dirichletConv a c n + RHTower.dirichletConv b c n - RHTower.dirichletConv e c n := by
  unfold RHTower.dirichletConv
  rw [← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun j _ => by ring

theorem dirichletConv_add_left (a b c : ℕ → ℝ) (n : ℕ) :
    RHTower.dirichletConv (fun j => a j + b j) c n =
      RHTower.dirichletConv a c n + RHTower.dirichletConv b c n := by
  unfold RHTower.dirichletConv
  rw [← sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- The dilation commutes with convolution: `(δ₂ ⋆ b) ⋆ c = δ₂ ⋆ (b ⋆ c)`. -/
theorem dirichletConv_shiftTwo (b c : ℕ → ℝ) {n : ℕ} (hn : n ≠ 0) :
    RHTower.dirichletConv (shiftTwo b) c n =
      if 2 ∣ n then RHTower.dirichletConv b c (n / 2) else 0 := by
  set δ₂ : ℕ → ℝ := fun j => if j = 2 then 1 else 0
  have hδ : ∀ j, j ≠ 1 → j ≠ 2 → δ₂ j = 0 := fun j _ h2 => by simp [δ₂, h2]
  have hshift : toAF (shiftTwo b) = toAF δ₂ * toAF b := by
    ext m
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rw [← dirichletConv_eq_toAF_mul, dirichletConv_twoPoint hδ _ hm]
    simp [toAF, hm, δ₂, shiftTwo]
  rw [dirichletConv_eq_toAF_mul, hshift, mul_assoc, ← toAF_dirichletConv, ← dirichletConv_eq_toAF_mul,
    dirichletConv_twoPoint hδ _ hn]
  simp [δ₂]

/-- Convolutions of odd-supported kernels with `o` live on the odd integers. -/
theorem dirichletConv_oddSqfWeight_of_even {a : ℕ → ℝ} (ha : ∀ j, 2 ∣ j → a j = 0) (ε : ℝ) {n : ℕ}
    (hn : 2 ∣ n) : RHTower.dirichletConv a (oddSqfWeight ε) n = 0 := by
  unfold RHTower.dirichletConv
  refine sum_eq_zero fun j hj => ?_
  by_cases h2 : 2 ∣ j
  · rw [ha j h2, zero_mul]
  · have hdiv : 2 ∣ n / j := by
      obtain ⟨m, hm⟩ := Nat.dvd_of_mem_divisors hj
      have hj0 := Nat.pos_of_mem_divisors hj
      rw [hm, Nat.mul_div_cancel_left m hj0]
      rw [hm] at hn
      exact (Nat.Prime.dvd_mul Nat.prime_two).mp hn |>.resolve_left h2
    rw [oddSqfWeight_of_even hdiv, mul_zero]

theorem oddPartKernel_of_even (k : ℕ → ℝ) {j : ℕ} (hj : 2 ∣ j) : oddPartKernel k j = 0 := by
  simp [oddPartKernel, show ¬ j % 2 = 1 by omega]

theorem evenPartWeight_of_even (k : ℕ → ℝ) {j : ℕ} (hj : 2 ∣ j) : evenPartWeight k j = 0 := by
  simp [evenPartWeight, show ¬ j % 2 = 1 by omega]

/-- `k = k_o + δ₂ ⋆ k_e` for a kernel vanishing on multiples of four. -/
theorem kernel_eq_odd_add_shift {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) (j : ℕ) :
    k j = oddPartKernel k j + shiftTwo (evenPartWeight k) j := by
  unfold oddPartKernel shiftTwo evenPartWeight
  by_cases h : j % 2 = 1
  · rw [if_pos h, if_neg (by omega)]; ring
  · rw [if_neg h, if_pos (by omega), zero_add]
    by_cases h' : j / 2 % 2 = 1
    · rw [if_pos h', Nat.mul_div_cancel' (by omega)]
    · rw [if_neg h', hk4 j (by omega)]

/-! ### The flip -/

section Flip

variable {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) (ε : ℝ)
include hk4

/-- **The even flip of `k ⋆ o` is `k^♭ ⋆ o`.** -/
theorem dirichletConv_flipKernelOf :
    RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε) = fun d =>
      RHTower.dirichletConv k (oddSqfWeight ε) d +
        localFactorWeight (evenPartWeight (RHTower.dirichletConv k (oddSqfWeight ε))) 2 2 d := by
  set X := RHTower.dirichletConv (oddPartKernel k) (oddSqfWeight ε)
  set Y := RHTower.dirichletConv (evenPartWeight k) (oddSqfWeight ε)
  have hX : ∀ n, 2 ∣ n → X n = 0 := fun n hn =>
    dirichletConv_oddSqfWeight_of_even (fun j hj => oddPartKernel_of_even k hj) ε hn
  have hY : ∀ n, 2 ∣ n → Y n = 0 := fun n hn =>
    dirichletConv_oddSqfWeight_of_even (fun j hj => evenPartWeight_of_even k hj) ε hn
  have hS : ∀ n, RHTower.dirichletConv (shiftTwo (evenPartWeight k)) (oddSqfWeight ε) n =
      if 2 ∣ n then Y (n / 2) else 0 := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [RHTower.dirichletConv, hY 0 (dvd_zero 2)]
    · exact dirichletConv_shiftTwo _ _ hn
  have hc : ∀ n, RHTower.dirichletConv k (oddSqfWeight ε) n = X n + if 2 ∣ n then Y (n / 2) else 0 :=
    fun n => by
      have hk : k = fun j => oddPartKernel k j + shiftTwo (evenPartWeight k) j :=
        funext (kernel_eq_odd_add_shift hk4)
      rw [hk, dirichletConv_add_left, hS]
  have hpart : ∀ n, evenPartWeight (RHTower.dirichletConv k (oddSqfWeight ε)) n = Y n := fun n => by
    unfold evenPartWeight
    split_ifs with h
    · rw [hc, hX _ (dvd_mul_right 2 n), zero_add, if_pos (dvd_mul_right 2 n),
        Nat.mul_div_cancel_left n two_pos]
    · rw [hY n (by omega)]
  funext d
  rw [show flipKernelOf k = fun j => oddPartKernel k j + evenPartWeight k j -
      shiftTwo (evenPartWeight k) j from rfl, dirichletConv_add_sub_left, hS, hc, localFactorWeight,
    hpart, hpart]
  split_ifs <;> ring

omit hk4 in
/-- The flipped kernel is supported on `[1, J]`. -/
theorem flipKernelOf_support {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    ∀ j, J < j → flipKernelOf k j = 0 := fun j hj => by
  have h1 := hkJ j hj
  have h2 := hkJ (2 * j) (by omega)
  simp only [flipKernelOf, oddPartKernel, shiftTwo, evenPartWeight, h1, h2]
  by_cases hj2 : 2 ∣ j
  · simp [Nat.mul_div_cancel' hj2, h1]
  · simp [hj2]

end Flip

/-! ### The pole values -/

/-- **The exact loss**: `K^♭(1 − ε) = K(1 − ε) + (1 − 2^{ε}) K_e(1 − ε)`. -/
theorem poleValue_flipKernelOf {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ}
    (hkJ : ∀ j, J < j → k j = 0) (ε : ℝ) :
    poleValue (flipKernelOf k) J ε =
      poleValue k J ε + (1 - (2 : ℝ) ^ ε) * poleValue (evenPartWeight k) J ε := by
  -- the dilated part of a kernel contributes `2^{ε−1}` times its pole value
  have hshift : ∑ j ∈ Icc 1 J, shiftTwo (evenPartWeight k) j * (j : ℝ) ^ (-(1 - ε)) =
      (2 : ℝ) ^ (ε - 1) * poleValue (evenPartWeight k) J ε := by
    have hfilter : ∑ j ∈ Icc 1 J, shiftTwo (evenPartWeight k) j * (j : ℝ) ^ (-(1 - ε)) =
        ∑ j ∈ (Icc 1 J).filter (fun j => 2 ∣ j), evenPartWeight k (j / 2) * (j : ℝ) ^ (-(1 - ε)) := by
      rw [sum_filter]
      exact sum_congr rfl fun j _ => by unfold shiftTwo; split_ifs <;> simp
    rw [hfilter, RHTower.sum_Icc_filter_dvd_reindex 2 J two_pos, poleValue]
    have hJ : ∑ i ∈ Icc 1 J, evenPartWeight k i * (i : ℝ) ^ (-(1 - ε)) =
        ∑ i ∈ Icc 1 (J / 2), evenPartWeight k i * (i : ℝ) ^ (-(1 - ε)) := by
      refine (sum_subset (Icc_subset_Icc le_rfl (Nat.div_le_self J 2)) fun i hi hiJ => ?_).symm
      have : J < 2 * i := by simp only [mem_Icc] at hi hiJ; omega
      simp [evenPartWeight, hkJ (2 * i) this]
    rw [hJ, mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi0 : (0 : ℝ) < i := by exact_mod_cast (mem_Icc.mp hi).1
    rw [Nat.mul_div_cancel_left i two_pos, Nat.cast_mul, Nat.cast_two,
      Real.mul_rpow (by norm_num) hi0.le, show -(1 - ε) = ε - 1 by ring]
    ring
  have hk : poleValue k J ε = ∑ j ∈ Icc 1 J, oddPartKernel k j * (j : ℝ) ^ (-(1 - ε)) +
      (2 : ℝ) ^ (ε - 1) * poleValue (evenPartWeight k) J ε := by
    rw [← hshift, poleValue, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by rw [kernel_eq_odd_add_shift hk4 j]; ring
  have hflip : poleValue (flipKernelOf k) J ε = ∑ j ∈ Icc 1 J, oddPartKernel k j * (j : ℝ) ^ (-(1 - ε)) +
      poleValue (evenPartWeight k) J ε - (2 : ℝ) ^ (ε - 1) * poleValue (evenPartWeight k) J ε := by
    rw [← hshift, poleValue, poleValue, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by unfold flipKernelOf; ring
  have h2 : (2 : ℝ) * (2 : ℝ) ^ (ε - 1) = (2 : ℝ) ^ ε := by
    rw [show ε = 1 + (ε - 1) by ring, Real.rpow_add two_pos, Real.rpow_one]; ring_nf
  rw [hflip, hk]
  linear_combination (-(poleValue (evenPartWeight k) J ε)) * h2

/-! ### The receivers -/

theorem dirichletConv_oddSqfWeight_mem_dampedClass {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    (ε : ℝ) :
    DampedClass (∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε) ε (RHTower.dirichletConv k (oddSqfWeight ε)) :=
  fun n => by
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [RHTower.dirichletConv, Nat.divisors_zero, sum_empty, abs_zero]
    exact mul_nonneg (sum_nonneg fun j _ => by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold RHTower.dirichletConv
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j ∈ n.divisors, |k j * oddSqfWeight ε (n / j)|
      ≤ ∑ j ∈ n.divisors.filter (· ≤ J), |k j| * (j : ℝ) ^ ε * (n : ℝ) ^ (-ε) := by
        rw [sum_filter]
        refine sum_le_sum fun j hj => ?_
        have hj0 : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mem_divisors hj
        split_ifs with hjJ
        · rw [abs_mul, abs_of_nonneg (oddSqfWeight_nonneg ε _), mul_assoc]
          refine mul_le_mul_of_nonneg_left ((oddSqfWeight_le ε _).trans_eq ?_) (abs_nonneg _)
          rw [Nat.cast_div (Nat.dvd_of_mem_divisors hj) hj0.ne', Real.div_rpow hn0.le hj0.le,
            Real.rpow_neg hj0.le, div_eq_mul_inv, inv_inv, mul_comm]
        · rw [hkJ j (by omega), zero_mul, abs_zero]
    _ ≤ ∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε * (n : ℝ) ^ (-ε) :=
        sum_le_sum_of_subset_of_nonneg (fun j hj => by
          obtain ⟨hjd, hjJ⟩ := mem_filter.mp hj
          exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hjd, hjJ⟩) fun _ _ _ => by positivity
    _ = (∑ j ∈ Icc 1 J, |k j| * (j : ℝ) ^ ε) * (n : ℝ) ^ (-ε) := by rw [sum_mul]

theorem dirichletConv_oddSqfWeight_of_four_dvd {k : ℕ → ℝ} (hk4 : ∀ m, 4 ∣ m → k m = 0) (ε : ℝ)
    {n : ℕ} (hn : 4 ∣ n) : RHTower.dirichletConv k (oddSqfWeight ε) n = 0 := by
  unfold RHTower.dirichletConv
  refine sum_eq_zero fun j hj => ?_
  by_cases h4 : 4 ∣ j
  · rw [hk4 j h4, zero_mul]
  · have hdiv : 2 ∣ n / j := by
      obtain ⟨m, hm⟩ := Nat.dvd_of_mem_divisors hj
      have hj0 := Nat.pos_of_mem_divisors hj
      rw [hm, Nat.mul_div_cancel_left m hj0]
      rw [hm] at hn
      by_contra h2
      have hm2 : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2
      have : 4 ∣ j := (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left 2 hm2) (by simpa using hn))
      exact h4 this
    rw [oddSqfWeight_of_even hdiv, mul_zero]

/-- **The exact loss of the even flip.** For `0 < ε ≤ 1/2` and `k` on `[1, J]` vanishing on
multiples of four, `c = k ⋆ o` and `c^♭ = k^♭ ⋆ o`: `c^♭` is the even flip of `c`, the two have the
same Ramanujan amplitudes, `K^♭(1 − ε) = K(1 − ε) + (1 − 2^{ε}) K_e(1 − ε)`, `c` is paid iff
`K(1 − ε) = 0`, `c^♭` is paid iff `K^♭(1 − ε) = 0`; if `K_e(1 − ε) = 0` the flip preserves the
receiver, and otherwise both are paid never. -/
theorem evenFlip_exactLoss {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ}
    (hk4 : ∀ m, 4 ∣ m → k m = 0) {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε) = (fun d =>
      RHTower.dirichletConv k (oddSqfWeight ε) d +
        localFactorWeight (evenPartWeight (RHTower.dirichletConv k (oddSqfWeight ε))) 2 2 d) ∧
    (∀ e, |weightRamanujanCoeff (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) e| =
      |weightRamanujanCoeff (RHTower.dirichletConv k (oddSqfWeight ε)) e|) ∧
    poleValue (flipKernelOf k) J ε =
      poleValue k J ε + (1 - (2 : ℝ) ^ ε) * poleValue (evenPartWeight k) J ε ∧
    (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ↔ poleValue k J ε = 0) ∧
    (ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)) ↔
      poleValue (flipKernelOf k) J ε = 0) ∧
    (poleValue (evenPartWeight k) J ε = 0 →
      (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ↔
        ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)))) ∧
    (poleValue (evenPartWeight k) J ε ≠ 0 →
      ¬ (ReceiverBounded (RHTower.dirichletConv k (oddSqfWeight ε)) ∧
        ReceiverBounded (RHTower.dirichletConv (flipKernelOf k) (oddSqfWeight ε)))) := by
  have hflip := dirichletConv_flipKernelOf hk4 ε
  have hpole := poleValue_flipKernelOf hk4 hkJ ε
  have hiff := receiverBounded_dirichletConv_oddSqf_iff hε hε2 hkJ
  have hiff' := receiverBounded_dirichletConv_oddSqf_iff hε hε2 (flipKernelOf_support hkJ)
  have h2 : (2 : ℝ) ^ ε ≠ 1 := by
    have : (1 : ℝ) < (2 : ℝ) ^ ε := Real.one_lt_rpow (by norm_num) hε
    linarith
  refine ⟨hflip, fun e => ?_, hpole, hiff, hiff', fun he => ?_, fun he hboth => ?_⟩
  · rw [hflip, weightRamanujanCoeff_evenFlip hε (dirichletConv_oddSqfWeight_mem_dampedClass hkJ ε)
      (fun m h => dirichletConv_oddSqfWeight_of_four_dvd hk4 ε h) e, abs_mul]
    unfold evenSign
    split_ifs <;> simp
  · rw [hiff, hiff', hpole, he, mul_zero, add_zero]
  · have e1 := hiff.mp hboth.1
    have e2 := hiff'.mp hboth.2
    rw [hpole, e1, zero_add] at e2
    rcases mul_eq_zero.mp e2 with h | h
    · exact h2 (by linarith)
    · exact he h

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
