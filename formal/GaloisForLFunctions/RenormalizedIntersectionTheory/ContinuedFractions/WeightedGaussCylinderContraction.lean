import GaloisForLFunctions.RenormalizedIntersectionTheory.ContinuedFractions.GaussWordCylinderEstimates
import GaloisForLFunctions.RenormalizedIntersectionTheory.ContinuedFractions.GaussDigitPerturbation

/-!
# Weighted contraction of actual Gauss cylinders

The normalized denominator row turns a successor cylinder probability into
its parent's probability times an explicit digit weight. A single summable
logarithmic moment controls the perturbation uniformly in that row. Iteration
gives the weighted cylinder estimate with exponent `β/(n+1)` and contraction
`(2n+1)/(2n+2)` for every finite digit alphabet.
-/

open Filter Topology
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWords
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWordProbability
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerBoundedDigits
open GaloisForLFunctions.RenormalizedIntersectionTheory.MayerDigitPerturbation

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWeightedCylinders
noncomputable section

/-- The actual denominator ratio belongs to the unit interval. -/
def ratio (k : ℕ) (a : Word k) : Ratio :=
  ⟨(wordMatrix k a 1 0 : ℝ) / wordMatrix k a 1 1, by
    have hd : (0 : ℝ) < wordMatrix k a 1 1 := by
      exact_mod_cast (wordMatrix_denominator_row k a).2
    refine ⟨div_nonneg (Nat.cast_nonneg _) hd.le, (div_le_one hd).mpr ?_⟩
    exact_mod_cast (wordMatrix_denominator_row k a).1⟩

private theorem normalized_successor {c d : ℝ} (hc : 0 ≤ c) (hd : 0 < d) (i : ℕ) :
    1 / ((c + d * ((i : ℝ) + 1)) * (c + d * ((i : ℝ) + 2))) =
      (1 / (d * (c + d))) *
        ((1 + c / d) / (((i : ℝ) + 1 + c / d) * ((i : ℝ) + 2 + c / d))) := by
  have hcd : c + d ≠ 0 := (add_pos_of_nonneg_of_pos hc hd).ne'
  have h1 : c + d * ((i : ℝ) + 1) ≠ 0 := (by positivity : 0 < c + d * ((i : ℝ) + 1)).ne'
  have h2 : c + d * ((i : ℝ) + 2) ≠ 0 := (by positivity : 0 < c + d * ((i : ℝ) + 2)).ne'
  have h3 : (i : ℝ) + 1 + c / d ≠ 0 := (by positivity : 0 < (i : ℝ) + 1 + c / d).ne'
  have h4 : (i : ℝ) + 2 + c / d ≠ 0 := (by positivity : 0 < (i : ℝ) + 2 + c / d).ne'
  field_simp [hd.ne', hcd, h1, h2, h3, h4]
  ring

/-- Successor probability factors through the actual parent denominator ratio. -/
theorem probability_cons (k : ℕ) (a : Word k) (i : ℕ) :
    probability (k + 1) (Fin.cons i a) = probability k a * weight (ratio k a) i := by
  have hd : (0 : ℝ) < wordMatrix k a 1 1 := by
    exact_mod_cast (wordMatrix_denominator_row k a).2
  have h := normalized_successor (Nat.cast_nonneg (wordMatrix k a 1 0)) hd i
  simp only [probability, weight, ratio, wordMatrix_col_zero, wordMatrix_col_one,
    Fin.tail_cons, Fin.cons_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
  convert h using 1
  congr 2
  ring

/-- The perturbation of one bounded-digit step fits inside half its missing mass. -/
theorem weighted_successor_le (n k : ℕ) (a : Word k) :
    (∑ i : Fin n, probability (k + 1) (Fin.cons (i : ℕ) a) *
      ((i : ℝ) + 2) ^ (2 * eta n)) ≤ cutoffRate n * probability k a := by
  have hp : 0 ≤ probability k a := by unfold probability; positivity
  have he : (∑ i : Fin n, probability (k + 1) (Fin.cons (i : ℕ) a) *
      ((i : ℝ) + 2) ^ (2 * eta n)) =
      (∑ i : Fin n, probability (k + 1) (Fin.cons (i : ℕ) a)) +
        probability k a * (∑ i : Fin n,
          weight (ratio k a) i * (((i : ℝ) + 2) ^ (2 * eta n) - 1)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [probability_cons]
    ring
  rw [he]
  calc
    _ ≤ retention n * probability k a + probability k a * (eta n * moment) :=
      add_le_add (successor_mass_le n k a)
        (mul_le_mul_of_nonneg_left (finite_correction_le (ratio k a) n) hp)
    _ = (retention n + eta n * moment) * probability k a := by ring
    _ ≤ cutoffRate n * probability k a :=
      mul_le_mul_of_nonneg_right (retained_plus_correction_le n) hp

/-- Multiplicative digit weight at the uniformly chosen exponent. -/
def digitProduct (n k : ℕ) (a : Fin k → Fin n) : ℝ :=
  ∏ j : Fin k, ((a j : ℝ) + 2) ^ (2 * eta n)

theorem digitProduct_nonneg (n k : ℕ) (a : Fin k → Fin n) :
    0 ≤ digitProduct n k a := Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)

/-- Weighted cylinder mass of the entire bounded-digit level. -/
def weightedMass (n k : ℕ) : ℝ :=
  ∑ a : Fin k → Fin n, probability k (word a) * digitProduct n k a

private def splitWord (n k : ℕ) : (Fin (k + 1) → Fin n) ≃ ((Fin k → Fin n) × Fin n) where
  toFun a := (Fin.tail a, a 0)
  invFun p := Fin.cons p.2 p.1
  left_inv a := by simp
  right_inv p := by cases p; simp

private theorem weightedMass_succ (n k : ℕ) :
    weightedMass n (k + 1) = ∑ a : Fin k → Fin n,
      (∑ i : Fin n, probability (k + 1) (Fin.cons (i : ℕ) (word a)) *
        ((i : ℝ) + 2) ^ (2 * eta n)) * digitProduct n k a := by
  rw [weightedMass, ← (splitWord n k).symm.sum_comp
    (fun a => probability (k + 1) (word a) * digitProduct n (k + 1) a),
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hw : word ((splitWord n k).symm (a, i)) = Fin.cons (i : ℕ) (word a) := by
    funext j
    refine Fin.cases ?_ (fun l => ?_) j <;> rfl
  rw [hw]
  simp only [digitProduct, Fin.prod_univ_succ]
  change probability (k + 1) (Fin.cons (i : ℕ) (word a)) *
      (((i : ℝ) + 2) ^ (2 * eta n) * ∏ j : Fin k, ((a j : ℝ) + 2) ^ (2 * eta n)) = _
  ring

/-- Weighted cylinder mass contracts geometrically at the paper's uniform exponent. -/
theorem weightedMass_le (n k : ℕ) : weightedMass n k ≤ cutoffRate n ^ k := by
  induction k with
  | zero => simp [weightedMass, digitProduct, probability, wordMatrix]
  | succ k ih =>
      rw [weightedMass_succ]
      calc
        _ ≤ ∑ a : Fin k → Fin n,
            (cutoffRate n * probability k (word a)) * digitProduct n k a :=
          Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_right
            (weighted_successor_le n k (word a)) (digitProduct_nonneg n k a))
        _ = cutoffRate n * weightedMass n k := by
          simp only [weightedMass, Finset.mul_sum, mul_assoc]
        _ ≤ cutoffRate n * cutoffRate n ^ k :=
          mul_le_mul_of_nonneg_left ih (cutoffRate_bounds n).1.le
        _ = cutoffRate n ^ (k + 1) := by rw [pow_succ, mul_comm]

/-- A single positive constant gives the weighted endpoint-width estimate for every alphabet. -/
theorem exists_uniform_cylinder_exponent : ∃ b : ℝ, 0 < b ∧ ∀ n k : ℕ,
    (∑ a : Fin k → Fin n, |realWordMap k (word a) 1 - realWordMap k (word a) 0| *
      ∏ j : Fin k, ((a j : ℝ) + 2) ^ (2 * (b / ((n : ℝ) + 1)))) ≤
        ((2 * (n : ℝ) + 1) / (2 * (n : ℝ) + 2)) ^ k := by
  refine ⟨beta, beta_pos, fun n k => ?_⟩
  simpa only [MayerCylinderEndpoints.endpoint_distance_eq_probability,
    weightedMass, digitProduct, eta, cutoffRate] using weightedMass_le n k

/-- The weighted mass tends to zero, although the exponent remains positive. -/
theorem weightedMass_tendsto_zero (n : ℕ) : Tendsto (weightedMass n) atTop (𝓝 0) := by
  apply squeeze_zero ?_ (weightedMass_le n)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (cutoffRate_bounds n).1.le (cutoffRate_bounds n).2)
  intro k
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (by unfold probability; positivity)
    (digitProduct_nonneg n k a))

#print axioms probability_cons
#print axioms weighted_successor_le
#print axioms weightedMass_le
#print axioms exists_uniform_cylinder_exponent
#print axioms weightedMass_tendsto_zero

end
end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerWeightedCylinders

