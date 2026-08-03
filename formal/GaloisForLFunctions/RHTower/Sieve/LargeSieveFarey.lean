import GaloisForLFunctions.RHTower.Sieve.LargeSieveExplicit
import GaloisForLFunctions.RHTower.Sieve.FareySeparation

/-!
# The large sieve at rationals with bounded denominator

Farey separation turns the closed-form large sieve into its arithmetic shape.  Rationals with
denominators at most `Q`, pairwise distinct modulo one, are `Q^{-2}`-separated on the circle, so

`∑ |⟪e(a/q), x⟫|² ≤ (N + Q²(1 + log(Q²/2 + 1))) ‖x‖²`.

The classical constant is `N + Q²`; the logarithmic factor here is the one the absolute-value method
provably cannot remove, and its removal is Montgomery–Vaughan's theorem rather than a rearrangement
of these steps.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- **Large sieve at rationals with denominators at most `Q`.** -/
theorem largeSieve_farey {ι : Type*} [DecidableEq ι] (N : ℕ) (s : Finset ι) {Q : ℕ} (hQ : 2 ≤ Q)
    (num : ι → ℤ) (den : ι → ℕ)
    (hden : ∀ i ∈ s, 0 < den i) (hQden : ∀ i ∈ s, den i ≤ Q)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      ¬ (((den i * den j : ℕ) : ℤ) ∣ (num i * (den j : ℤ) - num j * (den i : ℤ))))
    (x : EuclideanSpace ℂ (Fin N)) :
    ∑ i ∈ s, ‖⟪expRow N (circleFreq ((num i : ℝ) / (den i : ℝ))), x⟫_ℂ‖ ^ 2
      ≤ ((N : ℝ) + (Q : ℝ) ^ 2 * (1 + Real.log ((Q : ℝ) ^ 2 / 2 + 1))) * ‖x‖ ^ 2 := by
  have hQR : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < (Q : ℝ) := by linarith
  have hδ0 : (0 : ℝ) < 1 / (Q : ℝ) ^ 2 := by positivity
  have hδ : 1 / (Q : ℝ) ^ 2 ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hQR]
  have hsep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      1 / (Q : ℝ) ^ 2 ≤ toIntDist ((num j : ℝ) / (den j : ℝ) - (num i : ℝ) / (den i : ℝ)) := by
    intro i hi j hj hij
    have hdi := hden i hi
    have hdj := hden j hj
    have hfarey := one_div_le_toIntDist_farey (q := den j) (q' := den i) hdj hdi
      (a := num j) (a' := num i) (hdist j hj i hi (Ne.symm hij))
    have hdiR : (0 : ℝ) < (den i : ℝ) := by exact_mod_cast hdi
    have hdjR : (0 : ℝ) < (den j : ℝ) := by exact_mod_cast hdj
    have hbi : (den i : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQden i hi
    have hbj : (den j : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQden j hj
    have hprod : (den j : ℝ) * (den i : ℝ) ≤ (Q : ℝ) ^ 2 := by nlinarith
    have hmono : 1 / (Q : ℝ) ^ 2 ≤ 1 / ((den j : ℝ) * (den i : ℝ)) := by
      gcongr
    exact le_trans hmono hfarey
  have hbase := largeSieve_separated_explicit (δ := 1 / (Q : ℝ) ^ 2) N s
    (fun i => (num i : ℝ) / (den i : ℝ)) hδ0 hδ hsep x
  have e1 : (1 : ℝ) / (1 / (Q : ℝ) ^ 2) = (Q : ℝ) ^ 2 := by field_simp
  have e2 : (1 : ℝ) / (2 * (1 / (Q : ℝ) ^ 2)) = (Q : ℝ) ^ 2 / 2 := by
    rw [mul_one_div, one_div_div]
  rw [e1, e2] at hbase
  exact hbase

end RHTower.Sieve
