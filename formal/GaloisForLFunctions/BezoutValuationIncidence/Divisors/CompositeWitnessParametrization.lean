import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Exact parametrization of composite divisor witnesses

For positive parameters, a divisor of `an + u` congruent to `-1` modulo `4cua`
is equivalent to a positive solution of `n + 4cu²v = w(4cuav - 1)`.
Two polynomial identities give the divisibility transfer without a coprimality
condition or a congruence restriction on `n`. The same witnesses produce three
positive Egyptian-fraction denominators. The choices `c = 1` and `c = 3` give
moduli `4ua` and `12ua`, respectively.
-/

namespace GaloisForLFunctions.BezoutValuationIncidence

/-- A positive modulus congruent to minus one modulo the parameter product. -/
def compositeWitnessModulus (c u a v : ℕ+) : ℕ :=
  4 * (c : ℕ) * u * a * v - 1

/-- Every witness modulus is strictly positive. -/
theorem compositeWitnessModulus_pos (c u a v : ℕ+) :
    0 < compositeWitnessModulus c u a v := by
  have hh : 0 < (c : ℕ) * u * a * v := by positivity
  have hlarge : 1 < 4 * (c : ℕ) * u * a * v := by nlinarith only [hh]
  exact Nat.sub_pos_of_lt hlarge

/-- Adding one recovers the exact parameter product, with no truncated subtraction. -/
theorem compositeWitnessModulus_add_one (c u a v : ℕ+) :
    compositeWitnessModulus c u a v + 1 = 4 * (c : ℕ) * u * a * v := by
  have hp := compositeWitnessModulus_pos c u a v
  unfold compositeWitnessModulus at hp ⊢
  omega

/-- The two witness numerators have exactly the same divisibility by the witness modulus. -/
theorem compositeWitnessModulus_dvd_iff (c u a v : ℕ+) (n : ℕ) :
    compositeWitnessModulus c u a v ∣ (a : ℕ) * n + u ↔
      compositeWitnessModulus c u a v ∣ n + 4 * (c : ℕ) * (u : ℕ) ^ 2 * v := by
  have hs := compositeWitnessModulus_add_one c u a v
  have hleft : (a : ℕ) * (n + 4 * (c : ℕ) * (u : ℕ) ^ 2 * v) =
      ((a : ℕ) * n + u) + (u : ℕ) * compositeWitnessModulus c u a v := by
    have h := congrArg (fun x : ℕ => (u : ℕ) * x) hs
    nlinarith only [h]
  have hright : 4 * (c : ℕ) * u * v * ((a : ℕ) * n + u) =
      (n + 4 * (c : ℕ) * (u : ℕ) ^ 2 * v) + n * compositeWitnessModulus c u a v := by
    have h := congrArg (fun x : ℕ => n * x) hs
    nlinarith only [h]
  constructor
  · intro h
    have hm := dvd_mul_of_dvd_right h (4 * (c : ℕ) * u * v)
    rw [hright] at hm
    exact (Nat.dvd_add_left (dvd_mul_left (compositeWitnessModulus c u a v) n)).mp hm
  · intro h
    have hm := dvd_mul_of_dvd_right h (a : ℕ)
    rw [hleft] at hm
    exact (Nat.dvd_add_left
      (dvd_mul_left (compositeWitnessModulus c u a v) (u : ℕ))).mp hm

/-- Divisibility automatically supplies the size restriction on the witness modulus. -/
theorem compositeWitnessModulus_dvd_iff_with_bound (c u a v : ℕ+) (n : ℕ) :
    compositeWitnessModulus c u a v ∣ n + 4 * (c : ℕ) * (u : ℕ) ^ 2 * v ↔
      compositeWitnessModulus c u a v ∣ (a : ℕ) * n + u ∧
        compositeWitnessModulus c u a v ≤ (a : ℕ) * n + u := by
  rw [← compositeWitnessModulus_dvd_iff]
  exact ⟨fun h => ⟨h, Nat.le_of_dvd (by positivity) h⟩, And.left⟩

/-- Composite divisor witnesses are exactly positive bilinear solutions. -/
theorem compositeWitness_bilinear_iff (c u a n : ℕ+) :
    (∃ s : ℕ+, (s : ℕ) ∣ (a : ℕ) * n + u ∧
      4 * (c : ℕ) * u * a ∣ (s : ℕ) + 1) ↔
        ∃ v w : ℕ+, (n : ℕ) + 4 * (c : ℕ) * (u : ℕ) ^ 2 * v =
          (w : ℕ) * compositeWitnessModulus c u a v := by
  constructor
  · rintro ⟨s, hd, v, hv⟩
    have hvpos : 0 < v := by
      by_contra hn
      have hz : v = 0 := by omega
      simp only [hz, mul_zero] at hv
      omega
    let v' : ℕ+ := ⟨v, hvpos⟩
    have hs : compositeWitnessModulus c u a v' = s := by
      change 4 * (c : ℕ) * u * a * v - 1 = s
      omega
    have hd' : compositeWitnessModulus c u a v' ∣ (a : ℕ) * n + u := by rwa [hs]
    obtain ⟨w, hw⟩ := (compositeWitnessModulus_dvd_iff c u a v' (n : ℕ)).mp hd'
    have hwpos : 0 < w := by
      have hn := n.pos
      by_contra hnot
      have hz : w = 0 := by omega
      simp only [hz, mul_zero] at hw
      omega
    exact ⟨v', ⟨w, hwpos⟩, hw.trans (mul_comm _ _)⟩
  · rintro ⟨v, w, h⟩
    let s : ℕ+ := ⟨compositeWitnessModulus c u a v, compositeWitnessModulus_pos c u a v⟩
    refine ⟨s, ?_, ?_⟩
    · exact (compositeWitnessModulus_dvd_iff c u a v (n : ℕ)).mpr
        ⟨(w : ℕ), h.trans (mul_comm _ _)⟩
    · exact ⟨(v : ℕ), compositeWitnessModulus_add_one c u a v⟩

/-- The bilinear phase splits into a rational offset and the original divisor numerator. -/
theorem compositeWitness_partial_fraction (c u a v : ℕ+) (n : ℕ) :
    ((n : ℚ) + 4 * (c : ℕ) * (u : ℕ) ^ 2 * (v : ℕ)) /
        compositeWitnessModulus c u a v =
      (u : ℕ) / (a : ℚ) + (((a : ℕ) : ℚ) * n + (u : ℕ)) /
        ((a : ℕ) * (compositeWitnessModulus c u a v : ℚ)) := by
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt a.pos)
  have hs : (compositeWitnessModulus c u a v : ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (compositeWitnessModulus_pos c u a v))
  have he : (compositeWitnessModulus c u a v : ℚ) + 1 =
      4 * (c : ℕ) * (u : ℕ) * (a : ℕ) * (v : ℕ) := by
    exact_mod_cast compositeWitnessModulus_add_one c u a v
  field_simp
  have hm := congrArg (fun x : ℚ => ((u : ℕ) : ℚ) * x) he
  nlinarith only [hm]

/-- Any composite divisor witness yields an exact three-term Egyptian fraction with
positive integer denominators. -/
theorem compositeWitness_absent_or_egyptian (c u a n : ℕ+) :
    (¬ ∃ s : ℕ+, (s : ℕ) ∣ (a : ℕ) * n + u ∧
      4 * (c : ℕ) * u * a ∣ (s : ℕ) + 1) ∨
        ∃ v d : ℕ+,
          (4 : ℚ) / (n : ℕ) =
            1 / (((c : ℕ) * u * v * d : ℕ) : ℚ) +
            1 / (((c : ℕ) * a * v * n * d : ℕ) : ℚ) +
            1 / (((c : ℕ) * a * v * n * u : ℕ) : ℚ) := by
  classical
  by_cases hw : ∃ s : ℕ+, (s : ℕ) ∣ (a : ℕ) * n + u ∧
      4 * (c : ℕ) * u * a ∣ (s : ℕ) + 1
  swap
  · exact Or.inl hw
  right
  obtain ⟨s, ⟨d, hd⟩, v, hv⟩ := hw
  have hvpos : 0 < v := by
    by_contra hn
    have hz : v = 0 := by omega
    simp only [hz, mul_zero] at hv
    omega
  have hdpos : 0 < d := by
    by_contra hn
    have hz : d = 0 := by omega
    simp only [hz, mul_zero] at hd
    have hu := u.pos
    omega
  have hlin : (a : ℕ) * n + u + d = 4 * (c : ℕ) * u * a * v * d := by
    have hm := congrArg (fun x : ℕ => x * d) hv
    nlinarith only [hm, hd]
  have hlinQ : ((a : ℕ) : ℚ) * (n : ℕ) + (u : ℕ) + d =
      4 * (c : ℕ) * (u : ℕ) * (a : ℕ) * v * d := by exact_mod_cast hlin
  have hc : ((c : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt c.pos)
  have hu : ((u : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt u.pos)
  have ha : ((a : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt a.pos)
  have hn : ((n : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt n.pos)
  have hvQ : (v : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hvpos)
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  refine ⟨⟨v, hvpos⟩, ⟨d, hdpos⟩, ?_⟩
  change (4 : ℚ) / (n : ℕ) =
    1 / (((c : ℕ) * u * v * d : ℕ) : ℚ) +
    1 / (((c : ℕ) * a * v * n * d : ℕ) : ℚ) +
    1 / (((c : ℕ) * a * v * n * u : ℕ) : ℚ)
  simp only [Nat.cast_mul]
  field_simp
  nlinarith only [hlinQ]

end GaloisForLFunctions.BezoutValuationIncidence

#print axioms GaloisForLFunctions.BezoutValuationIncidence.compositeWitnessModulus_pos
#print axioms GaloisForLFunctions.BezoutValuationIncidence.compositeWitnessModulus_add_one
#print axioms GaloisForLFunctions.BezoutValuationIncidence.compositeWitnessModulus_dvd_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.compositeWitnessModulus_dvd_iff_with_bound
#print axioms GaloisForLFunctions.BezoutValuationIncidence.compositeWitness_bilinear_iff
#print axioms GaloisForLFunctions.BezoutValuationIncidence.compositeWitness_partial_fraction
#print axioms GaloisForLFunctions.BezoutValuationIncidence.compositeWitness_absent_or_egyptian
