import GaloisForLFunctions.BiarithmeticGeometry.GoldenArithmeticSource
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.BezoutEffectivityAndTheBeurlingObstruction

/-!
# Fixed-determinant cubing breaks golden point-count positivity

The actual golden roots have sum and product five. Cubing each root and
dividing by five preserves the determinant and doubles the trace to ten.
The original datum has nonnegative point counts, but the transformed first
count is minus four and its second count is minus sixty-four.
-/

noncomputable section
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Point counts of the actual golden roots after fixed-determinant normalized cubing. -/
def goldenNormalizedCubePointCount (n : ℕ) : ℝ :=
  (5 : ℝ) ^ n + 1 -
    ((goldenPrimaryRoot ^ 3 / 5) ^ n + (goldenSecondaryRoot ^ 3 / 5) ^ n)

/-- The normalized cube keeps the actual golden determinant fixed. -/
theorem goldenNormalizedCube_product :
    (goldenPrimaryRoot ^ 3 / 5) * (goldenSecondaryRoot ^ 3 / 5) = (5 : ℝ) := by
  rw [div_mul_div_comm, ← mul_pow, golden_roots_mul]
  norm_num

/-- Newton's cubic identity gives the transformed actual trace exactly. -/
theorem goldenNormalizedCube_sum :
    goldenPrimaryRoot ^ 3 / 5 + goldenSecondaryRoot ^ 3 / 5 = (10 : ℝ) := by
  rw [← add_div]
  have he : goldenPrimaryRoot ^ 3 + goldenSecondaryRoot ^ 3 =
      (goldenPrimaryRoot + goldenSecondaryRoot) ^ 3 -
        3 * (goldenPrimaryRoot * goldenSecondaryRoot) *
          (goldenPrimaryRoot + goldenSecondaryRoot) := by ring
  rw [he, golden_roots_sum, golden_roots_mul]
  norm_num

theorem goldenNormalizedCubePointCount_one : goldenNormalizedCubePointCount 1 = -4 := by
  simp only [goldenNormalizedCubePointCount, pow_one, goldenNormalizedCube_sum]
  norm_num

theorem goldenNormalizedCubePointCount_two : goldenNormalizedCubePointCount 2 = -64 := by
  have he : (goldenPrimaryRoot ^ 3 / 5) ^ 2 + (goldenSecondaryRoot ^ 3 / 5) ^ 2 =
      (goldenPrimaryRoot ^ 3 / 5 + goldenSecondaryRoot ^ 3 / 5) ^ 2 -
        2 * ((goldenPrimaryRoot ^ 3 / 5) * (goldenSecondaryRoot ^ 3 / 5)) := by ring
  rw [goldenNormalizedCubePointCount, he, goldenNormalizedCube_sum, goldenNormalizedCube_product]
  norm_num

/-- The actual positive-count golden datum loses positivity under fixed-determinant cubing. -/
theorem golden_pointCount_positive_but_normalizedCube_negative :
    (∀ n : ℕ, 0 ≤ goldenDatum.pointCount n) ∧ goldenNormalizedCubePointCount 1 < 0 := by
  refine ⟨goldenDatum_pointCount_nonneg, ?_⟩
  rw [goldenNormalizedCubePointCount_one]
  norm_num

end GaloisForLFunctions.BiarithmeticGeometry
