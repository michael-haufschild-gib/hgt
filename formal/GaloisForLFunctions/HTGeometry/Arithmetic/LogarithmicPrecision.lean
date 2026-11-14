import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationSums
import Mathlib.Tactic.Linarith

/-!
# Precision gained by logarithmic denominators

For `p>K+1` and `t>K`, the denominator `t` consumes at most `t-K-1`
units of valuation. Thus an integral numerator times `z^t/t`, with
`v_p(z)≥1`, has valuation at least `v_p(z)+K`. The bound survives finite
sums, including sums containing zero terms.
-/

namespace GaloisForLFunctions.HTGeometry.Arithmetic

variable {p : ℕ} [Fact p.Prime]

/-- The index of a logarithmic coefficient pays for its denominator and
leaves the claimed precision beyond the linear term. -/
theorem logarithmic_index_gap {K t : ℕ} (hp : K + 1 < p) (ht : K < t) :
    K + 1 + padicValNat p t ≤ t := by
  rcases lt_trichotomy t p with hlt | rfl | hgt
  · have hnd : ¬ p ∣ t := fun h => (not_le_of_gt hlt) (Nat.le_of_dvd (by omega) h)
    rw [padicValNat.eq_zero_of_not_dvd hnd]
    omega
  · rw [padicValNat_self]
    omega
  · have h := padicValNat_add_le_self hgt
    omega

/-- An integer coefficient and an integral parameter contribute no loss
beyond the explicit logarithmic denominator. -/
theorem logarithmic_term_precision (a : ℤ) (e z : ℚ) (n t K : ℕ)
    (he : 0 ≤ padicValRat p e) (hz : 1 ≤ padicValRat p z)
    (hp : K + 1 < p) (ht : K < t) :
    (a : ℚ) * e ^ n / (t : ℚ) * z ^ t = 0 ∨
      padicValRat p z + (K : ℤ) ≤
        padicValRat p ((a : ℚ) * e ^ n / (t : ℚ) * z ^ t) := by
  by_cases hzero : (a : ℚ) * e ^ n / (t : ℚ) * z ^ t = 0
  · exact Or.inl hzero
  right
  obtain ⟨hquot, hzpow⟩ := mul_ne_zero_iff.mp hzero
  obtain ⟨hnum, ht0⟩ := div_ne_zero_iff.mp hquot
  obtain ⟨ha, hepow⟩ := mul_ne_zero_iff.mp hnum
  rw [padicValRat.mul hquot hzpow, padicValRat.div hnum ht0,
    padicValRat.mul ha hepow, padicValRat.pow, padicValRat.pow,
    padicValRat.of_int, padicValRat.of_nat]
  have hindex : (K : ℤ) + 1 + (padicValNat p t : ℤ) ≤ (t : ℤ) := by
    exact_mod_cast logarithmic_index_gap hp ht
  have hcoeff : (0 : ℤ) ≤ padicValInt p a := Nat.cast_nonneg _
  have heterm := mul_nonneg (Nat.cast_nonneg n : (0 : ℤ) ≤ n) he
  have htpos : (1 : ℤ) ≤ t := by omega
  have hgrowth := mul_nonneg (sub_nonneg.mpr htpos) (sub_nonneg.mpr hz)
  nlinarith only [hindex, hcoeff, heterm, hgrowth]

/-- Every finite tail above degree `K` has precision at least `v_p(z)+K`. -/
theorem logarithmic_tail_precision {ι : Type*} (s : Finset ι)
    (a : ι → ℤ) (n t : ι → ℕ) (e z : ℚ) (K : ℕ)
    (he : 0 ≤ padicValRat p e) (hz : 1 ≤ padicValRat p z)
    (hp : K + 1 < p) (ht : ∀ i ∈ s, K < t i) :
    (∑ i ∈ s, (a i : ℚ) * e ^ n i / (t i : ℚ) * z ^ t i) = 0 ∨
      padicValRat p z + (K : ℤ) ≤
        padicValRat p (∑ i ∈ s, (a i : ℚ) * e ^ n i / (t i : ℚ) * z ^ t i) := by
  by_cases hs : (∑ i ∈ s, (a i : ℚ) * e ^ n i / (t i : ℚ) * z ^ t i) = 0
  · exact Or.inl hs
  exact Or.inr (val_finset_sum_ge s _ _
    (fun i hi => logarithmic_term_precision (a i) e z (n i) (t i) K he hz hp (ht i hi)) hs)

#print axioms logarithmic_index_gap
#print axioms logarithmic_tail_precision

end GaloisForLFunctions.HTGeometry.Arithmetic
