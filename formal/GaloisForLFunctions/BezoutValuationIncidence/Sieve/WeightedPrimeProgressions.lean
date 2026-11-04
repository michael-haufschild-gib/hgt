import GaloisForLFunctions.BezoutValuationIncidence.Sieve.PrimeProgressionUpper
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.ReciprocalAbel

/-!
# Reciprocal prime weights in a progression

The progression count bounds its logarithmically weighted prefix by a linear
function. Abel summation then gives a bound depending on the logarithmic
width of the interval, uniformly in the residue and prime modulus.
-/

noncomputable section

namespace GaloisForLFunctions.BezoutValuationIncidence

open Finset

/-- Logarithmic prime weight restricted to a residue class. -/
def primeResidueLog (p a n : ℕ) : ℝ :=
  if n.Prime ∧ n ≡ a [MOD p] then Real.log n else 0

/-- The logarithmically weighted progression prefix has a linear upper bound. -/
theorem primeResidueLog_sum_le {p X a : ℕ} (hp : p.Prime) (hpX : p ^ 2 ≤ X)
    (hcount : ((#{n ∈ Icc 1 X | n.Prime ∧ n ≡ a [MOD p]} : ℕ) : ℝ) ≤
      1026 * (X : ℝ) / ((p : ℝ) * Real.log X)) :
    (∑ n ∈ Icc 1 X, primeResidueLog p a n) ≤ 1026 * (X : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hX1 : 1 < X := by
    have hsq : p ≤ p ^ 2 := Nat.le_pow (by omega : 0 < 2)
    exact hp.one_lt.trans_le (hsq.trans hpX)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast hX1)
  have hs : (∑ n ∈ Icc 1 X, primeResidueLog p a n) =
      ∑ n ∈ (Icc 1 X).filter (fun n => n.Prime ∧ n ≡ a [MOD p]), Real.log n := by
    rw [sum_filter]
    rfl
  rw [hs]
  calc
    _ ≤ ∑ n ∈ (Icc 1 X).filter (fun n => n.Prime ∧ n ≡ a [MOD p]),
        Real.log (X : ℝ) := by
      apply sum_le_sum
      intro n hn
      obtain ⟨hnX, hnprime, _⟩ := mem_filter.mp hn
      exact Real.log_le_log (by exact_mod_cast hnprime.pos)
        (by exact_mod_cast (mem_Icc.mp hnX).2)
    _ = ((#{n ∈ Icc 1 X | n.Prime ∧ n ≡ a [MOD p]} : ℕ) : ℝ) * Real.log X := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (1026 * (X : ℝ) / ((p : ℝ) * Real.log X)) * Real.log X :=
      mul_le_mul_of_nonneg_right hcount hlog.le
    _ = _ := by field_simp [hp0.ne', hlog.ne']

/-- Prime reciprocal weights in any progression cost only its logarithmic interval width. -/
theorem exists_weighted_prime_progression_upper :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X a : ℕ, p.Prime → p₀ ≤ p → p ^ 2 ≤ H → H ≤ X →
      (∑ n ∈ (Icc H X).filter (fun n => n.Prime ∧ n ≡ a [MOD p]),
        Real.log n / (n : ℝ)) ≤
          (1026 / (p : ℝ)) * (1 + Real.log X - Real.log H) := by
  obtain ⟨p₀, hp₀, hcount⟩ := exists_prime_progression_upper
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X a hp hpp hpH hHX
  have hH : 1 ≤ H := by
    have hsq : 1 ≤ p ^ 2 := Nat.one_le_pow 2 p hp.pos
    exact hsq.trans hpH
  have hprefix : ∀ m, H ≤ m → m ≤ X →
      (∑ n ∈ Icc H m, primeResidueLog p a n) ≤ (1026 / (p : ℝ)) * (m : ℝ) := by
    intro m hHm _
    have hsub : Icc H m ⊆ Icc 1 m := fun n hn =>
      mem_Icc.mpr ⟨hH.trans (mem_Icc.mp hn).1, (mem_Icc.mp hn).2⟩
    have hnonneg (n : ℕ) : 0 ≤ primeResidueLog p a n := by
      unfold primeResidueLog
      split_ifs
      · exact Real.log_natCast_nonneg n
      · exact le_rfl
    refine (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hnonneg n)).trans ?_
    simpa only [div_mul_eq_mul_div, mul_comm (m : ℝ)] using
      primeResidueLog_sum_le hp (hpH.trans hHm) (hcount p m a hp hpp (hpH.trans hHm))
  have h := reciprocal_sum_of_linear_prefix (by positivity : 0 ≤ 1026 / (p : ℝ)) hH hHX hprefix
  convert h using 1
  rw [sum_filter]
  apply sum_congr rfl
  intro n _
  dsimp only [primeResidueLog]
  split_ifs <;> simp only [zero_div]

#print axioms exists_weighted_prime_progression_upper

end GaloisForLFunctions.BezoutValuationIncidence
