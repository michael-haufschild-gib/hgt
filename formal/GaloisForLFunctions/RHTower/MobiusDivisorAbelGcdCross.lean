import GaloisForLFunctions.RHTower.MobiusDivisorAbelHomothety

/-!
# Exact common-divisor components of the literal Abel off-diagonal

The common-divisor label partitions every ordered cross term exactly. Summing
all labels reconstructs the square of the complete channel sum minus its
arithmetic diagonal, with no componentwise sign assumption.
-/

noncomputable section
open Finset
namespace RHTower

/-- Ordered cross-channel contribution having one exact common divisor. -/
def mobiusDivisorGcdCross (M r : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
    if Nat.gcd d e = r ∧ d ≠ e then
      mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0

private theorem finite_cross_decomposition (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ d ∈ s, ∑ e ∈ s, if d ≠ e then f d*f e else 0) =
      (∑ d ∈ s, f d)^2 - ∑ d ∈ s, f d^2 := by
  have hdiag : (∑ d ∈ s, ∑ e ∈ s, if d = e then f d*f e else 0) =
      ∑ d ∈ s, f d^2 := by
    apply sum_congr rfl
    intro d hd
    simp [hd,pow_two]
  have hsplit :
      (∑ d ∈ s, ∑ e ∈ s, f d*f e) =
        (∑ d ∈ s, ∑ e ∈ s, if d = e then f d*f e else 0) +
          ∑ d ∈ s, ∑ e ∈ s, if d ≠ e then f d*f e else 0 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro d _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro e _
    by_cases hde : d = e <;> simp [hde]
  have hfull : (∑ d ∈ s, ∑ e ∈ s, f d*f e) = (∑ d ∈ s, f d)^2 := by
    rw [pow_two,sum_mul_sum]
  rw [hdiag,hfull] at hsplit
  linarith only [hsplit]

/-- Every common-divisor component reconstructs the complete signed off-diagonal, without a
componentwise sign assumption or any discarded cutoff term. -/
theorem sum_mobiusDivisorGcdCross (M : ℕ) :
    (∑ r ∈ Icc 1 M, mobiusDivisorGcdCross M r) =
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)^2 -
        ∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d^2 := by
  unfold mobiusDivisorGcdCross
  rw [sum_comm]
  conv_lhs =>
    arg 2
    ext d
    rw [sum_comm]
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 M) (e : ℕ) (_he : e ∈ Icc 1 M) :
      (∑ r ∈ Icc 1 M,
        if Nat.gcd d e = r ∧ d ≠ e then
          mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0) =
        if d ≠ e then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0 := by
    have hg : Nat.gcd d e ∈ Icc 1 M := mem_Icc.mpr
      ⟨Nat.gcd_pos_of_pos_left e (mem_Icc.mp hd).1,
        (Nat.le_of_dvd (mem_Icc.mp hd).1 (Nat.gcd_dvd_left d e)).trans (mem_Icc.mp hd).2⟩
    by_cases hde : d ≠ e <;> simp [hde,hg]
  calc
    _ = ∑ d ∈ Icc 1 M, ∑ e ∈ Icc 1 M,
        if d ≠ e then mobiusDivisorDilationChannel M d*mobiusDivisorDilationChannel M e else 0 := by
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      exact hpoint d hd e he
    _ = _ := finite_cross_decomposition (Icc 1 M) (mobiusDivisorDilationChannel M)

end RHTower
