import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipOfTheFermiSquarefreeWeightBreaksTheReceiver

/-!
# Finite perturbations of the smooth power are decided at the pole

For a kernel `k` supported on `[1, J]` and `0 < ε ≤ 1/2`, the receiver of
`(k ⋆ d^{-ε})(n) = n^{-ε} Σ_{j ∣ n} k(j) j^{ε}` is bounded **if and only if**
`K(1 − ε) = Σ_j k(j) j^{-(1−ε)} = 0`.

* If `K(1 − ε) = 0`, the sign sequence `s = k̃ ⋆ 1` (`k̃(j) = k(j) j^{ε}`) has partial sums
  `Σ_{d ≤ n} s(d) = Σ_j k̃(j) ⌊n/j⌋ = Σ_j k̃(j)(⌊n/j⌋ − n/j)`, because the mean `Σ_j k̃(j)/j` is exactly
  `K(1 − ε)`; they are bounded by `Σ_j |k̃(j)|`, and the damped-sign engine pays the receiver.
* If `K(1 − ε) ≠ 0`, the pole law of finite kernels applies to the drift `2^{-1-ε} n^{1−ε}` of `d^{-ε}`.

So the paid finite perturbations of the smooth power form the hyperplane `K(1 − ε) = 0`: the
arithmetic of the dilations `k ↦ jk` enters the receiver only through the value of the kernel at the
pole.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The pole value `K(1 − ε) = Σ_{j ≤ J} k(j) j^{-(1−ε)}`. -/
def poleValue (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) : ℝ := ∑ j ∈ Icc 1 J, k j * (j : ℝ) ^ (-(1 - ε))

/-- The undamped kernel `k̃(j) = k(j) j^{ε}`. -/
def undampedKernel (k : ℕ → ℝ) (ε : ℝ) (j : ℕ) : ℝ := k j * (j : ℝ) ^ ε

theorem sum_undampedKernel_div (k : ℕ → ℝ) (J : ℕ) (ε : ℝ) :
    ∑ j ∈ Icc 1 J, undampedKernel k ε j / j = poleValue k J ε := by
  refine sum_congr rfl fun j hj => ?_
  have hj0 : (0 : ℝ) < j := by exact_mod_cast (mem_Icc.mp hj).1
  rw [undampedKernel, mul_div_assoc, ← Real.rpow_sub_one hj0.ne', show ε - 1 = -(1 - ε) by ring]

theorem undampedKernel_support {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) (ε : ℝ) :
    ∀ j, J < j → undampedKernel k ε j = 0 := fun j hj => by simp [undampedKernel, hkJ j hj]

/-- Damping a kernel against a damped weight: `k ⋆ (c d^{-ε}) = (k̃ ⋆ c) d^{-ε}`. -/
theorem dirichletConv_damped_eq (k c : ℕ → ℝ) (ε : ℝ) (n : ℕ) :
    RHTower.dirichletConv k (dampedSignWeight c ε) n =
      dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) c) ε n := by
  rw [dampedSignWeight_dirichletConv]
  unfold RHTower.dirichletConv
  refine sum_congr rfl fun j hj => ?_
  have hj0 : (0 : ℝ) < j := by exact_mod_cast Nat.pos_of_mem_divisors hj
  simp only [dampedSignWeight, undampedKernel]
  rw [mul_assoc (k j) ((j : ℝ) ^ ε), ← Real.rpow_add hj0, add_neg_cancel, Real.rpow_zero, mul_one]

/-- **At a zero of the pole value the sign sequence has bounded partial sums.** -/
theorem abs_sum_range_dirichletConv_unit_le {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0)
    {ε : ℝ} (hK : poleValue k J ε = 0) (x : ℕ) :
    |∑ d ∈ range x, RHTower.dirichletConv (undampedKernel k ε) unitSign d| ≤
      ∑ j ∈ Icc 1 J, |undampedKernel k ε j| := by
  have hB : 0 ≤ ∑ j ∈ Icc 1 J, |undampedKernel k ε j| := sum_nonneg fun j _ => abs_nonneg _
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa using hB
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  have h := abs_weightCenteredPrefix_finiteKernel_le (undampedKernel_support hkJ ε) n
  rw [sum_undampedKernel_div, hK] at h
  rw [dampedSign_sum_range_succ_eq_add_Icc]
  have h0 : RHTower.dirichletConv (undampedKernel k ε) unitSign 0 = 0 := by
    simp [RHTower.dirichletConv]
  rw [h0, zero_add]
  convert h using 2
  simp [weightCenteredPrefix, RHTower.dirichletConv, unitSign]

/-- The smooth power drifts: `n Σ_{(n,2n]} d^{-1-ε} ≥ 2^{-1-ε} n^{1−ε}`. -/
theorem unit_drift {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} (hn : 1 ≤ n) :
    (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), dampedSignWeight unitSign ε d / d := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hcell : ∀ d ∈ Ioc n (2 * n), (2 * (n : ℝ)) ^ (-(1 + ε)) ≤ dampedSignWeight unitSign ε d / d :=
    fun d hd => by
      have hd := mem_Ioc.mp hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
      have hd2 : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
      rw [dampedSignWeight, unitSign, one_mul, div_eq_mul_inv, ← Real.rpow_neg_one,
        ← Real.rpow_add hd0, show -ε + -1 = -(1 + ε) by ring]
      exact Real.rpow_le_rpow_of_nonpos hd0 hd2 (by linarith)
  have hsum := sum_le_sum hcell
  rw [sum_const, Nat.card_Ioc, show 2 * n - n = n by omega, nsmul_eq_mul] at hsum
  have hP : (2 * (n : ℝ)) ^ (-(1 + ε)) = (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-(1 + ε)) :=
    Real.mul_rpow (by norm_num) hn0.le
  have hpow : (n : ℝ) * ((n : ℝ) * (n : ℝ) ^ (-(1 + ε))) = (n : ℝ) ^ (1 - ε) := by
    rw [show (1 - ε) = 1 + (1 + -(1 + ε)) by ring, Real.rpow_add hn0, Real.rpow_add hn0,
      Real.rpow_one]
  calc (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε)
      = (n : ℝ) * ((n : ℝ) * (2 * (n : ℝ)) ^ (-(1 + ε))) := by rw [hP, ← hpow]; ring
    _ ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), dampedSignWeight unitSign ε d / d :=
        mul_le_mul_of_nonneg_left hsum hn0.le

/-- **Finite perturbations of the smooth power are decided at the pole.** For `0 < ε ≤ 1/2` and
`k` supported on `[1, J]`, the receiver of `k ⋆ d^{-ε}` is bounded if and only if
`Σ_j k(j) j^{-(1−ε)} = 0`. -/
theorem receiverBounded_dirichletConv_unit_iff {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight unitSign ε)) ↔
      poleValue k J ε = 0 := by
  constructor
  · intro hB
    by_contra hK
    refine not_receiverBounded_dirichletConv_of_drift hε hε2 (q := dampedSignWeight unitSign ε)
      (fun d => by simp [dampedSignWeight, unitSign, Real.rpow_nonneg]) (K := 1)
      (fun d => by simp [dampedSignWeight, unitSign, abs_of_nonneg, Real.rpow_nonneg])
      (κ := (2 : ℝ) ^ (-(1 + ε))) (by positivity)
      (by filter_upwards [eventually_ge_atTop 1] with n hn using unit_drift hε.le hn) hkJ hK hB
  · intro hK
    rw [show RHTower.dirichletConv k (dampedSignWeight unitSign ε) =
        dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) unitSign) ε from
      funext (dirichletConv_damped_eq k unitSign ε)]
    exact exists_weightPronicEnergy_dampedSign_le (sum_nonneg fun j _ => abs_nonneg _) hε
      (abs_sum_range_dirichletConv_unit_le hkJ hK)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
