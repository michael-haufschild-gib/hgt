import GaloisForLFunctions.RHTower.WeilLogShiftQuadraticMass
import GaloisForLFunctions.RHTower.WeilLogShiftMassWeightedSensitivity

/-! Square-root improvement of actual Gram-test cost at quadratic cluster starts. -/

open scoped BigOperators
noncomputable section
namespace RHTower

theorem exists_finiteWeilGram_sqrt_fiber_sensitivity :
    ∃ B K : ℝ, 0 < B ∧ 1 ≤ K ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      K * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest, ∀ a : ℝ,
        (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) ∧
      ∀ v z : Fin (r + 2) → ℝ,
        finiteWeilCanonicalMomentFiber r k v → finiteWeilCanonicalMomentFiber r k z →
        ∀ w : FiniteWeilGramTest,
          |(∑ i, v i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
            (∑ i, z i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)| *
              (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) * Real.sqrt ((r + 2 : ℕ) : ℝ) ≤
                (∑ i, |v i - z i|) * B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_mass_weighted_fiber_sensitivity
  refine ⟨2 * B, 4 * L + 2, by positivity, by linarith, fun r s k hmem hwidth =>
    ⟨exists_finiteWeilGram_reads_mixture_coordinate r s k hmem, fun v z hv hz w => ?_⟩⟩
  obtain ⟨hlinear, hquad⟩ := finiteWeil_quadratic_width L hL r k hwidth
  have hc := hbound r s k hmem hlinear v z hv hz w
  have hs := finiteWeilCanonicalCluster_quadratic_sqrt_lower r k hquad
  let d : ℝ := |(∑ i, v i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) -
    (∑ i, z i * finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩)|
  let q : ℝ := ((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r
  let S := finiteWeilAbsMass (finiteWeilCanonicalCluster r k)
  let D : ℝ := ∑ i, |v i - z i|
  change d * q * S ≤ D * B * finiteWeilGramTailCost 1 w at hc
  change d * q * Real.sqrt ((r + 2 : ℕ) : ℝ) ≤ D * (2 * B) * finiteWeilGramTailCost 1 w
  calc
    _ ≤ d * q * (2 * S) := mul_le_mul_of_nonneg_left hs (by dsimp [d, q]; positivity)
    _ = 2 * (d * q * S) := by ring
    _ ≤ 2 * (D * B * finiteWeilGramTailCost 1 w) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by ring

/-- Fixed constants control every actual mixture-coordinate reader, with explicit order growth. -/
theorem exists_finiteWeilGram_sqrt_coordinate_cost :
    ∃ B K : ℝ, 0 < B ∧ 1 ≤ K ∧ ∀ (r : ℕ) (s : Finset ℕ) (k : ℕ)
      (hmem : ∀ i : Fin (r + 2), k + (i : ℕ) ∈ s),
      K * ((r + 1 : ℕ) : ℝ) ^ 2 ≤ ((k + 2 : ℕ) : ℝ) →
      (∃ w : FiniteWeilGramTest, ∀ a : ℝ,
        (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) ∧
      ∀ w : FiniteWeilGramTest,
        (∀ a : ℝ, (∑ i, finiteWeilCanonicalMixture r k a i *
          finiteWeilGramCoefficientVector s w ⟨k + (i : ℕ), hmem i⟩) = a) →
        Real.sqrt ((r + 2 : ℕ) : ℝ) *
          (((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r) ≤ B * finiteWeilGramTailCost 1 w := by
  obtain ⟨B, L, hB, hL, hbound⟩ := exists_finiteWeilGram_mass_weighted_coordinate_cost
  refine ⟨4 * B, 4 * L + 2, by positivity, by linarith, fun r s k hmem hwidth => ?_⟩
  obtain ⟨hlinear, hquad⟩ := finiteWeil_quadratic_width L hL r k hwidth
  obtain ⟨hex, hall⟩ := hbound r s k hmem hlinear
  refine ⟨hex, fun w hw => ?_⟩
  have hc := hall w hw
  have hs := finiteWeilCanonicalCluster_quadratic_sqrt_lower r k hquad
  let q : ℝ := ((k + 2 : ℕ) : ℝ) ^ 2 * (2 : ℝ) ^ r
  let S := finiteWeilAbsMass (finiteWeilCanonicalCluster r k)
  change S * q ≤ 2 * B * finiteWeilGramTailCost 1 w at hc
  change Real.sqrt ((r + 2 : ℕ) : ℝ) * q ≤ (4 * B) * finiteWeilGramTailCost 1 w
  calc
    _ ≤ (2 * S) * q := mul_le_mul_of_nonneg_right hs (by dsimp [q]; positivity)
    _ = 2 * (S * q) := by ring
    _ ≤ 2 * (2 * B * finiteWeilGramTailCost 1 w) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ = _ := by ring

end RHTower
