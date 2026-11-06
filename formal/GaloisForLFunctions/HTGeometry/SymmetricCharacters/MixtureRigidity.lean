import GaloisForLFunctions.HTGeometry.CommonRealPartTuranDeterminant
import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve
import Mathlib.Data.NNReal.Basic

/-!
# Mixing characters: covariance and spectral rigidity

Mixing multiplicative cycle characters preserves positive definiteness, but not multiplicativity
on disjoint cycles. The defect for two equal cycles is a weighted variance. Vanishing at every
cycle length forces all finite alphabets in the positive support to coincide as multisets.
-/

noncomputable section
open scoped BigOperators

namespace GaloisForLFunctions.SymmetricCharacters

variable {I : Type*} [Fintype I]

/-- Unnormalized covariance of two identical observables in a finite mixture. -/
def mixtureDefect (w : I → NNReal) (v : I → ℝ) : ℝ :=
  (∑ i, (w i : ℝ)) * (∑ i, (w i : ℝ) * v i ^ 2) -
    (∑ i, (w i : ℝ) * v i) ^ 2

/-- The disjoint-copy defect is exactly half the weighted pairwise dispersion. -/
theorem two_mul_mixtureDefect (w : I → NNReal) (v : I → ℝ) :
    2 * mixtureDefect w v =
      ∑ i, ∑ j, (w i : ℝ) * (w j : ℝ) * (v i - v j) ^ 2 := by
  have h := HTGeometry.configTuranDeterminant_eq_pair_sum Finset.univ
    (fun i => (w i : ℝ)) (fun i => (v i : ℂ))
  simp only [HTGeometry.configTuranDeterminant, HTGeometry.configMoment,
    pow_zero, pow_one, mul_one] at h
  unfold mixtureDefect
  exact_mod_cast h

theorem mixtureDefect_nonneg (w : I → NNReal) (v : I → ℝ) :
    0 ≤ mixtureDefect w v := by
  have h := two_mul_mixtureDefect w v
  have hn : 0 ≤ ∑ i, ∑ j, (w i : ℝ) * (w j : ℝ) * (v i - v j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (w i).coe_nonneg (w j).coe_nonneg) (sq_nonneg _)
  linarith

/-- A zero defect permits variation only at components of zero mass. -/
theorem mixtureDefect_eq_zero_iff (w : I → NNReal) (v : I → ℝ) :
    mixtureDefect w v = 0 ↔
      ∀ i j, w i = 0 ∨ w j = 0 ∨ v i = v j := by
  classical
  have hn (i j : I) : 0 ≤ (w i : ℝ) * (w j : ℝ) * (v i - v j) ^ 2 :=
    mul_nonneg (mul_nonneg (w i).coe_nonneg (w j).coe_nonneg) (sq_nonneg _)
  have hz : mixtureDefect w v = 0 ↔
      ∀ i j, (w i : ℝ) * (w j : ℝ) * (v i - v j) ^ 2 = 0 := by
    have htwo : mixtureDefect w v = 0 ↔ 2 * mixtureDefect w v = 0 := by
      constructor <;> intro h <;> linarith
    rw [htwo, two_mul_mixtureDefect]
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hn i j))]
    simp only [Finset.mem_univ, forall_true_left]
    apply forall_congr'
    intro i
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hn i j)]
    simp
  rw [hz]
  simp only [mul_eq_zero, pow_eq_zero_iff (by omega : 2 ≠ 0), sub_eq_zero,
    NNReal.coe_eq_zero, or_assoc]

/-- A finite mixture can have every disjoint-cycle defect zero only when its positive-mass
alphabets are identical. Zero padding must be fixed, since the zeroth moment counts letters. -/
theorem all_mixtureDefects_zero_iff (w : I → NNReal) (alphabet : I → Multiset ℝ) :
    (∀ k : ℕ, mixtureDefect w (fun i => ((alphabet i).map fun x => x ^ k).sum) = 0) ↔
      ∀ i j, w i = 0 ∨ w j = 0 ∨ alphabet i = alphabet j := by
  constructor
  · intro h i j
    by_cases hi : w i = 0
    · exact Or.inl hi
    by_cases hj : w j = 0
    · exact Or.inr (Or.inl hj)
    right; right
    apply multiset_eq_of_powerSum_eq
    intro k
    exact ((mixtureDefect_eq_zero_iff w _).mp (h k) i j).resolve_left hi |>.resolve_left hj
  · intro h k
    apply (mixtureDefect_eq_zero_iff w _).mpr
    intro i j
    rcases h i j with hi | hj | hij
    · exact Or.inl hi
    · exact Or.inr (Or.inl hj)
    · exact Or.inr (Or.inr (by rw [hij]))

end GaloisForLFunctions.SymmetricCharacters
