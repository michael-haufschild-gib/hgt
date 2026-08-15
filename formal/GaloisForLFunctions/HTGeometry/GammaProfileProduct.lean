import GaloisForLFunctions.HTGeometry.GammaConvolutionBound

/-!
# Products against a gamma profile

The endpoint bound for a gamma profile has two immediate consequences for Cauchy products.

* At depth `0` it is **submultiplicativity**, `Θ(i) Θ(j) ≤ Θ(i+j)`: the profile of a product is no
  worse than the profile of its factors.
* At depth `N+1` it says that if both factors vanish below order `N+1`, then every term of the
  convolution is at most `Θ(N+1) Θ(n−N−1)`.  Since the number of terms is `n+1`, the product is
  smaller than a single profile value at index `n` by a factor `Θ(n−N−1)/Θ(n) ≍ n^{-s(N+1)}` —
  **as small as one likes, by choosing the truncation order**.

That second statement is what makes a Taylor defect negligible: the defect of the linearization at a
truncation of order `N` is a sum of monomials of degree at least two in the tail, and the tail
vanishes below order `N+1`.
-/

open scoped Nat

namespace GaloisForLFunctions.HTGeometry

/-- The endpoint bound, transported to the full profile. -/
theorem gammaProfilePair_le_endpoint {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {p i n : ℕ}
    (hpi : p ≤ i) (hin : i + p ≤ n) :
    gammaProfile s β i * gammaProfile s β (n - i)
      ≤ gammaProfile s β p * gammaProfile s β (n - p) := by
  have hβn : (0 : ℝ) < β ^ n := pow_pos hβ n
  have hL : gammaProfile s β i * gammaProfile s β (n - i)
      = (Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))) * β ^ n := by
    rw [gammaProfile, gammaProfile,
      show Real.Gamma (1 + s * (i : ℝ)) * β ^ i *
          (Real.Gamma (1 + s * ((n - i : ℕ) : ℝ)) * β ^ (n - i))
        = (Real.Gamma (1 + s * (i : ℝ)) * Real.Gamma (1 + s * ((n - i : ℕ) : ℝ))) *
          (β ^ i * β ^ (n - i)) by ring,
      ← pow_add, show i + (n - i) = n from by omega]
  have hR : gammaProfile s β p * gammaProfile s β (n - p)
      = (Real.Gamma (1 + s * (p : ℝ)) * Real.Gamma (1 + s * ((n - p : ℕ) : ℝ))) * β ^ n := by
    rw [gammaProfile, gammaProfile,
      show Real.Gamma (1 + s * (p : ℝ)) * β ^ p *
          (Real.Gamma (1 + s * ((n - p : ℕ) : ℝ)) * β ^ (n - p))
        = (Real.Gamma (1 + s * (p : ℝ)) * Real.Gamma (1 + s * ((n - p : ℕ) : ℝ))) *
          (β ^ p * β ^ (n - p)) by ring,
      ← pow_add, show p + (n - p) = n from by omega]
  rw [hL, hR]
  exact mul_le_mul_of_nonneg_right (gammaPair_le_endpoint hs hpi hin) hβn.le

theorem gammaProfile_zero {s β : ℝ} : gammaProfile s β 0 = 1 := by
  rw [gammaProfile]
  norm_num

/-- **Submultiplicativity of a gamma profile.** -/
theorem gammaProfile_mul_le {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) (i j : ℕ) :
    gammaProfile s β i * gammaProfile s β j ≤ gammaProfile s β (i + j) := by
  have h := gammaProfilePair_le_endpoint hs hβ (p := 0) (i := i) (n := i + j)
    (Nat.zero_le i) (by omega)
  rw [show i + j - i = j from by omega, show i + j - 0 = i + j from by omega,
    gammaProfile_zero, one_mul] at h
  exact h

/-! ### The convolution of two tails -/

/-- **Two factors vanishing below order `N+1` convolve into a profile value shifted by `N+1`.** -/
theorem norm_coeff_mul_le_of_vanishing {s β : ℝ} (hs : 0 < s) (hβ : 0 < β) {N : ℕ}
    {A B : PowerSeries ℂ} {cA cB : ℝ} (hcA : 0 ≤ cA) (hcB : 0 ≤ cB)
    (hA : ∀ k, ‖PowerSeries.coeff k A‖ ≤ cA * gammaProfile s β k)
    (hB : ∀ k, ‖PowerSeries.coeff k B‖ ≤ cB * gammaProfile s β k)
    (hA0 : ∀ k, k ≤ N → PowerSeries.coeff k A = 0)
    (hB0 : ∀ k, k ≤ N → PowerSeries.coeff k B = 0)
    (n : ℕ) :
    ‖PowerSeries.coeff n (A * B)‖
      ≤ ((n : ℝ) + 1) * (cA * cB *
        (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1)))) := by
  classical
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      ‖PowerSeries.coeff p.1 A * PowerSeries.coeff p.2 B‖
        ≤ cA * cB * (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
    intro p hp
    have hnn : (0 : ℝ) ≤ cA * cB *
        (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) := by
      have h1 : (0 : ℝ) < gammaProfile s β (N + 1) := gammaProfile_pos hs.le hβ _
      have h2 : (0 : ℝ) < gammaProfile s β (n - (N + 1)) := gammaProfile_pos hs.le hβ _
      exact mul_nonneg (mul_nonneg hcA hcB) (le_of_lt (mul_pos h1 h2))
    by_cases h1 : p.1 ≤ N
    · rw [hA0 p.1 h1, zero_mul, norm_zero]
      exact hnn
    by_cases h2 : p.2 ≤ N
    · rw [hB0 p.2 h2, mul_zero, norm_zero]
      exact hnn
    push Not at h1 h2
    have hp1 : N + 1 ≤ p.1 := h1
    have hple : p.1 + (N + 1) ≤ n := by omega
    have hp2 : p.2 = n - p.1 := by omega
    have hend := gammaProfilePair_le_endpoint hs hβ (p := N + 1) (i := p.1) (n := n) hp1 hple
    rw [norm_mul]
    calc ‖PowerSeries.coeff p.1 A‖ * ‖PowerSeries.coeff p.2 B‖
        ≤ (cA * gammaProfile s β p.1) * (cB * gammaProfile s β p.2) :=
          mul_le_mul (hA p.1) (hB p.2) (norm_nonneg _)
            (mul_nonneg hcA (gammaProfile_pos hs.le hβ _).le)
      _ = cA * cB * (gammaProfile s β p.1 * gammaProfile s β (n - p.1)) := by
          rw [hp2]; ring
      _ ≤ cA * cB * (gammaProfile s β (N + 1) * gammaProfile s β (n - (N + 1))) :=
          mul_le_mul_of_nonneg_left hend (mul_nonneg hcA hcB)
  rw [PowerSeries.coeff_mul]
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_sum
    (fun p hp => hterm p (by simpa using hp))) ?_
  simp only [Finset.sum_const, Finset.Nat.card_antidiagonal, nsmul_eq_mul]
  push_cast
  ring_nf
  exact le_rfl

end GaloisForLFunctions.HTGeometry
