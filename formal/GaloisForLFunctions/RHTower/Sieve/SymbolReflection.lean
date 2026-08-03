import GaloisForLFunctions.RHTower.Sieve.ConcreteRoot

/-!
# The symbol bound at every frequency

`ConcreteRoot.lean` bounds the symbol only on the half range `1 ≤ j`, `2j ≤ Q`, where the base angle
lies in `(0, π]`.  The other frequencies are handled by reflection rather than by a new estimate:
`ζ^{Q-j}` is the conjugate of `ζ^j`, so the symbol at `Q-j` is the negative of the symbol at `j`, and
the frequency `j = 0` gives the zero symbol because every power of `1` is real.

Hence the uniform bound `1 + 3π` holds at *every* frequency `j < Q`, which is the hypothesis shape
that `BilinearMultiplier.abs_sum_kernel_bilinear_le` requires.
-/

namespace RHTower.Sieve

open Finset

/-- Reflecting the frequency negates the imaginary parts. -/
theorem im_pow_reflect {ζ : ℂ} {Q : ℕ} (hQ : 0 < Q) (hζ : IsPrimitiveRoot ζ Q) {j : ℕ}
    (hj : j ≤ Q) (d : ℕ) :
    ((ζ ^ (Q - j)) ^ d).im = -(((ζ ^ j) ^ d).im) := by
  have hconj : ζ ^ (Q - j) = (starRingEnd ℂ) (ζ ^ j) := by
    have h := conj_pow_eq hQ hζ hj 1
    simpa using h.symm
  rw [hconj, ← map_pow, Complex.conj_im]

/-- **Uniform symbol bound at every frequency.** -/
theorem abs_sum_im_rootOfUnity_pow_div_le_all {Q : ℕ} (hQ : 0 < Q) {j : ℕ} (hj : j < Q) (M : ℕ) :
    |∑ d ∈ Finset.range M,
        (1 / ((d : ℝ) + 1)) * (((rootOfUnity Q) ^ j) ^ d).im| ≤ 1 + 3 * Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · have hzero : ∀ d ∈ Finset.range M,
        (1 / ((d : ℝ) + 1)) * (((rootOfUnity Q) ^ (0 : ℕ)) ^ d).im = 0 := by
      intro d _
      simp
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero, abs_zero]
    linarith
  · rcases le_or_gt (2 * j) Q with hhalf | hhalf
    · exact abs_sum_im_rootOfUnity_pow_div_le hQ hj1 hhalf M
    · have hζ : IsPrimitiveRoot (rootOfUnity Q) Q := isPrimitiveRoot_rootOfUnity (by omega)
      have hj' : 1 ≤ Q - j := by omega
      have h2j' : 2 * (Q - j) ≤ Q := by omega
      have hjle : Q - j ≤ Q := by omega
      have hrefl : ∀ d ∈ Finset.range M,
          (1 / ((d : ℝ) + 1)) * (((rootOfUnity Q) ^ j) ^ d).im
            = -((1 / ((d : ℝ) + 1)) * (((rootOfUnity Q) ^ (Q - j)) ^ d).im) := by
        intro d _
        have hback : Q - (Q - j) = j := by omega
        have h := im_pow_reflect hQ hζ hjle d
        rw [hback] at h
        rw [h]
        ring
      rw [Finset.sum_congr rfl hrefl, Finset.sum_neg_distrib, abs_neg]
      exact abs_sum_im_rootOfUnity_pow_div_le hQ hj' h2j' M

end RHTower.Sieve
