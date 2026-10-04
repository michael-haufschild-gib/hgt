import GaloisForLFunctions.RHTower.LiouvillePrimeBandAnalysis

/-!
# Exact full-source prime-band decomposition

The degree-one slice is the sum of every selected prime response, reindexed through
all multiples and with the full band-free cofactor density. Together with the complete
constant and nonlinear slices, this gives an exact identity for the parameterized
arithmetic source. Restoring the original phases gives its actual center identity.

This closes the summation assembly needed by MC-C12.92. No finite truncation replaces
the source, and no simple-zero, convolution-root obstruction, or RH theorem is claimed.
-/

open Finset
open scoped BigOperators Classical

namespace RHTower.LiouvillePrimeBand
noncomputable section

private theorem norm_baseCoefficient_le {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) (t : ℝ) (n : ℕ) :
    ‖baseCoefficient P β t n‖ ≤ Real.exp (-t) ^ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [baseCoefficient]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [baseCoefficient, norm_mul, norm_div, Complex.norm_natCast, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_of_le_one_left (by positivity)
    ((div_le_one hn0).mpr ((norm_character_one_le hβ n).trans hn1))

private theorem norm_term_le {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) (t : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖term P β t n z‖ ≤ Real.exp (-t) ^ n := by
  rw [term, norm_mul, norm_pow]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)).trans
    (norm_baseCoefficient_le hβ t n)

private theorem summable_slice {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (D : Set ℕ) : Summable (fun n => if degree P n ∈ D then term P β t n z else 0) := by
  have hq : Real.exp (-t) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos ht)
  apply (summable_geometric_of_lt_one (Real.exp_pos (-t)).le hq).of_norm_bounded
  intro n
  split_ifs
  · exact norm_term_le hβ t hz n
  · simpa using pow_nonneg (Real.exp_pos (-t)).le n

private def primePanel (P : Finset ℕ) (β : ℕ → ℂ) (t : ℝ) (p n : ℕ) : ℂ :=
  if p ∣ n ∧ degree P (n / p) = 0 then
    β p * RHTower.LiouvilleTwistedDensity.twist (n / p) / (n : ℂ) *
      (Real.exp (-t) : ℂ) ^ n else 0

private theorem primePanel_eq_base {P : Finset ℕ} {p : ℕ} (hp : p.Prime) (hpP : p ∈ P)
    (β : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    primePanel P β t p n = if p ∣ n ∧ degree P (n / p) = 0 then baseCoefficient P β t n else 0 := by
  by_cases hc : p ∣ n ∧ degree P (n / p) = 0
  · have he : character P β 1 n = β p * RHTower.LiouvilleTwistedDensity.twist (n / p) := by
      calc
        _ = character P β 1 (p * (n / p)) := congrArg (character P β 1) (Nat.mul_div_cancel' hc.1).symm
        _ = _ := by rw [map_mul, character_prime hp hpP, one_mul, character_eq_twist_of_degree_zero hc.2]
    simp only [primePanel, hc, baseCoefficient, he]
  · simp [primePanel, hc]

private theorem summable_primePanel {P : Finset ℕ} {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {t : ℝ} (ht : 0 < t) {p : ℕ} (hp : p.Prime) (hpP : p ∈ P) :
    Summable (primePanel P β t p) := by
  have hq : Real.exp (-t) < 1 := by simpa using Real.exp_lt_exp.mpr (neg_neg_of_pos ht)
  apply (summable_geometric_of_lt_one (Real.exp_pos (-t)).le hq).of_norm_bounded
  intro n
  rw [primePanel_eq_base hp hpP]
  split_ifs
  · exact norm_baseCoefficient_le hβ t n
  · simpa using pow_nonneg (Real.exp_pos (-t)).le n

private theorem tsum_primePanel {P : Finset ℕ} {p : ℕ} (hp : 0 < p)
    (β : ℕ → ℂ) (t : ℝ) :
    (∑' n, primePanel P β t p n) = β p * cofactorResponse P t p := by
  have hinj : Function.Injective (fun m : ℕ => p * m) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hp hab
  rw [← hinj.tsum_eq]
  · rw [cofactorResponse, cofactorDensity, ← tsum_div_const, ← tsum_mul_left]
    apply tsum_congr
    intro m
    have hdiv : p ∣ p * m := dvd_mul_right p m
    have hquot : p * m / p = m := Nat.mul_div_cancel_left m hp
    have he : (Real.exp (-t) : ℂ) ^ (p * m) = (Real.exp (-((p : ℝ) * t)) : ℂ) ^ m := by
      rw [pow_mul, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
      have hmul : (p : ℝ) * -t = -((p : ℝ) * t) := by ring
      rw [hmul]
    simp only [primePanel, hdiv, hquot, true_and, he]
    by_cases hm : degree P m = 0
    · simp only [hm, ↓reduceIte, RHTower.LiouvilleTwistedDensity.coefficient, Nat.cast_mul]
      ring
    · simp [hm]
  · intro n hn
    have hd : p ∣ n := by
      by_contra h
      exact hn (by simp [primePanel, h])
    exact ⟨n / p, Nat.mul_div_cancel' hd⟩

private theorem degree_one_base_eq_sum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (β : ℕ → ℂ) (t : ℝ) (n : ℕ) :
    (if degree P n = 1 then baseCoefficient P β t n else 0) = ∑ p ∈ P, primePanel P β t p n := by
  calc
    _ = (if degree P n = 1 then character P β 1 n else 0) / (n : ℂ) *
        (Real.exp (-t) : ℂ) ^ n := by split_ifs <;> simp [baseCoefficient]
    _ = (∑ p ∈ P, if p ∣ n ∧ degree P (n / p) = 0 then
        β p * RHTower.LiouvilleTwistedDensity.twist (n / p) else 0) / (n : ℂ) *
        (Real.exp (-t) : ℂ) ^ n := by rw [character_degree_one P hP β 1 n]; simp only [one_mul]
    _ = _ := by
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p _
      by_cases hc : p ∣ n ∧ degree P (n / p) = 0 <;> simp [primePanel, hc]

/-- Exact linear cofactor response of the complete arithmetic series. -/
theorem degreeSlice_one {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    degreeSlice {1} P β t z = z * ∑ p ∈ P, β p * cofactorResponse P t p := by
  have he : degreeSlice {1} P β t z = z * ∑' n : ℕ,
      if degree P n = 1 then baseCoefficient P β t n else 0 := by
    rw [degreeSlice, ← tsum_mul_left]
    apply tsum_congr
    intro n
    by_cases hn : degree P n = 1
    · simp [hn, term, mul_comm]
    · simp [hn]
  rw [he]
  congr 1
  calc
    _ = ∑' n : ℕ, ∑ p ∈ P, primePanel P β t p n :=
      tsum_congr (degree_one_base_eq_sum P hP β t)
    _ = ∑ p ∈ P, ∑' n : ℕ, primePanel P β t p n :=
      Summable.tsum_finsetSum fun p hp => summable_primePanel hβ ht (hP p hp) hp
    _ = _ := Finset.sum_congr rfl fun p hp => tsum_primePanel (hP p hp).pos β t

/-- The full source is its constant cofactor, exact prime response, and complete nonlinear tail. -/
theorem source_decomposition {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) {β : ℕ → ℂ}
    (hβ : ∀ p ∈ P, ‖β p‖ = 1) {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    source P β t z = cofactorDensity P t +
      z * (∑ p ∈ P, β p * cofactorResponse P t p) + nonlinearRemainder P β t z := by
  rw [← degreeSlice_zero P β t z, ← degreeSlice_one hP hβ ht z]
  unfold source nonlinearRemainder degreeSlice
  have hs0 := summable_slice hβ ht hz ({0} : Set ℕ)
  have hs1 := summable_slice hβ ht hz ({1} : Set ℕ)
  have hs2 := summable_slice hβ ht hz (Set.Ici 2)
  rw [← hs0.tsum_add hs1, ← (hs0.add hs1).tsum_add hs2]
  apply tsum_congr
  intro n
  by_cases h0 : degree P n = 0
  · simp [h0]
  · by_cases h1 : degree P n = 1
    · simp [h1]
    · have h2 : 2 ≤ degree P n := by omega
      simp [h0, h1, h2]


/-- The actual fixed twist determines the constant center of the moving phase disc. -/
theorem baseline_decomposition {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (h2 : 2 ∉ P)
    {t : ℝ} (ht : 0 < t) :
    RHTower.LiouvilleTwistedDensity.exponentialDensity t = cofactorDensity P t -
      (∑ p ∈ P, cofactorResponse P t p) + nonlinearRemainder P (fun _ => -1) t 1 := by
  have h := source_decomposition hP (β := fun _ => -1)
    (by intro p hp; simp) ht (z := 1) (by simp)
  rw [source_baseline h2] at h
  simpa only [neg_one_mul, Finset.sum_neg_distrib, one_mul, sub_eq_add_neg] using h

end
end RHTower.LiouvillePrimeBand
