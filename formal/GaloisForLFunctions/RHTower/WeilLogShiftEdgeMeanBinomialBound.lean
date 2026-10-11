import GaloisForLFunctions.RHTower.WeilLogShiftEdgeMoments
import GaloisForLFunctions.RHTower.WeilLogShiftEdgeTestTransfer
import GaloisForLFunctions.RHTower.WeilLogShiftMidpointBinomialBound
import GaloisForLFunctions.RHTower.WeilLogShiftBinomialProbabilityMoments

/-! The midpoint binomial law controls the canonical transport-edge barycenter. -/

open scoped BigOperators

namespace RHTower

theorem finiteWeilCanonicalEdgeIndexMean_binomial_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2| ≤
      Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
  have hf (u : Fin (r + 2)) : |((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2| ≤
      ((r + 1 : ℕ) : ℝ) / 2 := by
    have hu0 : (0 : ℝ) ≤ ((u : ℕ) : ℝ) := Nat.cast_nonneg _
    have hu1 : ((u : ℕ) : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show (u : ℕ) ≤ r + 1 by have := u.isLt; omega)
    exact abs_le.mpr ⟨by linarith only [hu0], by linarith only [hu1]⟩
  have hM : (∑ u, finiteWeilCanonicalMixture r k (1 / 2) u) = 1 :=
    (finiteWeilCanonicalMixture_mem r k (1 / 2) (by norm_num) (by norm_num)).2.1
  have hm : (∑ u : Fin (r + 2), finiteWeilCanonicalMixture r k (1 / 2) u * ((u : ℕ) : ℝ)) =
      finiteWeilCanonicalEdgeIndexMean r k + 1 / 2 := finiteWeilCanonicalMidpointIndexMean_eq_edge r k
  have hl := finiteWeil_profile_test_l1_bound
    (finiteWeilCanonicalMixture r k (1 / 2))
    (fun u : Fin (r + 2) => ((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1))
    (fun u => ((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2) (((r + 1 : ℕ) : ℝ) / 2) hf
  have hid :
      (∑ u : Fin (r + 2), finiteWeilCanonicalMixture r k (1 / 2) u *
        (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2)) -
      (∑ u : Fin (r + 2), (((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)) *
        (((u : ℕ) : ℝ) - ((r + 1 : ℕ) : ℝ) / 2)) =
      finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2 := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hM,
      finiteWeil_binomial_probability_mass, finiteWeil_binomial_probability_mean,
      one_mul, sub_self, sub_zero]
    rw [hm]
    push_cast
    ring
  rw [hid] at hl
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  calc
    _ ≤ (((r + 1 : ℕ) : ℝ) / 2) *
        (∑ u : Fin (r + 2), |finiteWeilCanonicalMixture r k (1 / 2) u -
          ((r + 1).choose (u : ℕ) : ℝ) / (2 : ℝ) ^ (r + 1)|) := hl
    _ ≤ (((r + 1 : ℕ) : ℝ) / 2) *
        (2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left (finiteWeilCanonicalMixture_midpoint_binomial_bound r k hwidth) (by positivity)
    _ = _ := by field_simp

theorem finiteWeilCanonicalEdgeIndexMean_normalized_bound (r k : ℕ)
    (hwidth : 2 * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ)) :
    |finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ) - 1 / 2| ≤
      2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  have hm := finiteWeilCanonicalEdgeIndexMean_binomial_bound r k hwidth
  have hn : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ r + 1 by omega)
  have hS : (1 : ℝ) / 2 ≤ Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
    have hs0 := Real.sqrt_nonneg ((((r + 1 : ℕ) : ℝ) + 1) / 2)
    have hs2 := Real.sq_sqrt (show 0 ≤ (((r + 1 : ℕ) : ℝ) + 1) / 2 by positivity)
    nlinarith only [hs0, hs2, hn1]
  have hraw : |finiteWeilCanonicalEdgeIndexMean r k - ((r + 1 : ℕ) : ℝ) / 2| ≤
      2 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) := by
    have ht := abs_sub (finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2) ((1 : ℝ) / 2)
    norm_num at ht
    have hid : finiteWeilCanonicalEdgeIndexMean r k - ((r + 1 : ℕ) : ℝ) / 2 =
        (finiteWeilCanonicalEdgeIndexMean r k - (r : ℝ) / 2) - 1 / 2 := by push_cast; ring
    rw [hid]
    linarith only [ht, hm, hS]
  have hid : finiteWeilCanonicalEdgeIndexMean r k / ((r + 1 : ℕ) : ℝ) - 1 / 2 =
      (finiteWeilCanonicalEdgeIndexMean r k - ((r + 1 : ℕ) : ℝ) / 2) / ((r + 1 : ℕ) : ℝ) := by
    field_simp
  rw [hid, abs_div, abs_of_nonneg hn.le]
  calc
    _ ≤ (2 * Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2)) / ((r + 1 : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hraw hn.le
    _ = _ := by ring

theorem finiteWeilCanonicalEdgeIndexMean_quadratic_bound (r t : ℕ) :
    |finiteWeilCanonicalEdgeIndexMean r (2 * (r + 1) ^ 2 + t) / ((r + 1 : ℕ) : ℝ) - 1 / 2| ≤
      2 * (Real.sqrt ((((r + 1 : ℕ) : ℝ) + 1) / 2) / ((r + 1 : ℕ) : ℝ)) := by
  apply finiteWeilCanonicalEdgeIndexMean_normalized_bound
  push_cast
  have ht : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg _
  nlinarith only [ht]

end RHTower
