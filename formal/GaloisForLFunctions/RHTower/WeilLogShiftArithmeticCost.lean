import GaloisForLFunctions.RHTower.WeilLogShiftArithmeticMassComparison
import GaloisForLFunctions.RHTower.WeilLogShiftMassWeightedSensitivity

/-! Arithmetic-node reference mass controls actual log-cluster measurements. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem exists_finiteWeilGram_arithmetic_fiber_sensitivity :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest, ∀ a : ℝ,
        (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) ∧
      ∀ v z : Fin (r + 2) → ℝ,
        finiteWeilCanonicalMomentFiber r k v → finiteWeilCanonicalMomentFiber r k z →
        ∀ w : FiniteWeilGramTest,
          |(∑ i, v i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
            (∑ i, z i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)| *
              (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) *
                (((k + 2 : ℕ) : ℝ) ^ (r + 1) * finiteWeilArithmeticMass r) ≤
                  (∑ i, |v i - z i|) * ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) *
                    B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_mass_weighted_fiber_sensitivity
  refine ⟨B, L, hB, hL, fun r s k hmem hwidth =>
    ⟨exists_finiteWeilGram_reads_mixture_coordinate r s k hmem, fun v z hv hz w => ?_⟩⟩
  let gap : ℝ := |(∑ i, v i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
    (∑ i, z i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)|
  let q : ℝ := ((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r
  let U : ℝ := ((k + r + 3 : ℕ) : ℝ) ^ (r + 1)
  let D : ℝ := ∑ i, |v i - z i|
  have hc : gap * q * finiteWeilAbsMass (finiteWeilCanonicalCluster r k) ≤
      D * B * finiteWeilGramTailCost 1 w := hbound r s k hmem hwidth v z hv hz w
  have hm := (finiteWeilCanonicalCluster_arithmetic_mass_comparison r k).1
  change gap * q * (((k + 2 : ℕ) : ℝ) ^ (r + 1) * finiteWeilArithmeticMass r) ≤
    D * U * B * finiteWeilGramTailCost 1 w
  calc
    _ ≤ gap * q * (U * finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (abs_nonneg _) (by dsimp [q]; positivity))
    _ = U * (gap * q * finiteWeilAbsMass (finiteWeilCanonicalCluster r k)) := by ring
    _ ≤ U * (D * B * finiteWeilGramTailCost 1 w) :=
      mul_le_mul_of_nonneg_left hc (by dsimp [U]; positivity)
    _ = _ := by ring

/-- A fixed arithmetic reference gives an explicit cost bound for every actual coordinate reader. -/
theorem exists_finiteWeilGram_arithmetic_coordinate_cost :
    ∃ B L : ℝ, 0 < B ∧ 1 ≤ L ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      4 * L * ((r + 1 : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest, ∀ a : ℝ,
        (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) ∧
      ∀ w : FiniteWeilGramTest,
        (∀ a : ℝ, (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) →
        ((k + 2 : ℕ) : ℝ) ^ (r + 1) * finiteWeilArithmeticMass r *
          (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) ≤
            2 * ((k + r + 3 : ℕ) : ℝ) ^ (r + 1) * B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_arithmetic_fiber_sensitivity
  refine ⟨B, L, hB, hL, fun r s k hmem hwidth => ?_⟩
  have hb := hbound r s k hmem hwidth
  refine ⟨hb.1, fun w hw => ?_⟩
  have hc := hb.2 (finiteWeilCanonicalMixture r k 1) (finiteWeilCanonicalMixture r k 0)
    (finiteWeilCanonicalMixture_mem r k 1 (by norm_num) le_rfl)
    (finiteWeilCanonicalMixture_mem r k 0 le_rfl (by norm_num)) w
  rw [hw 1, hw 0, finiteWeilCanonicalMixture_abs_distance] at hc
  calc
    _ = (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) *
        (((k + 2 : ℕ) : ℝ) ^ (r + 1) * finiteWeilArithmeticMass r) := by ring
    _ ≤ _ := by simpa only [sub_zero, abs_one, mul_one, one_mul] using hc

end RHTower
