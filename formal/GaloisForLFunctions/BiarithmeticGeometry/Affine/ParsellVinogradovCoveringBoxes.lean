import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovTranslatedBoxes
import GaloisForLFunctions.BiarithmeticGeometry.Affine.CoordinateCubeDoubling

/-!
# Radius-two covering boxes for complete moment manifolds

The radius-two cube encloses the compact cutoff used in moment-manifold
coverings. Doubling every ambient coordinate transfers the exact sharp
overlap exponent from unit cubes. The anisotropic volume factor remains
the vertical scale raised to the binomial total vertical weight.
-/

open MeasureTheory Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.FiniteCoordinateNorms

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- A radius-two covering box with arbitrary ambient center. -/
def scaledAffineCoveringBox (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ)
    (a : AffineAxisSpace r k) : Set (AffineAxisSpace r k) :=
  translatedLinearCube (Matrix.toLin' (scaledAffineMatrix r k ε δ t)) a 2

/-- Radius-two overlap differs from radius-one overlap by exactly the ambient doubling factor. -/
theorem volume_two_scaledAffineCoveringBoxes (r k : ℕ) (ε : ℝ)
    (δ η : Fin (r + 1) → ℝ) (t s : ℝ) (a b : AffineAxisSpace r k) :
    volume (scaledAffineCoveringBox r k ε δ t a ∩ scaledAffineCoveringBox r k ε η s b) =
      ENNReal.ofReal ((2 : ℝ) ^ Fintype.card (AffineAxisIndex r k)) *
        volume (scaledAffineBox r k ε δ t (fun i => a i / 2) ∩
          scaledAffineBox r k ε η s (fun i => b i / 2)) :=
  volume_two_translatedLinearCube_two _ _ a b

/-- The sharp Euclidean overlap exponent holds for radius-two covering boxes. -/
theorem exists_uniform_coveringBox_euclidean_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 1)),
      volume (scaledAffineCoveringBox r (k + 1) ε δ t a ∩
        scaledAffineCoveringBox r (k + 1) ε η s b) ≤
          ENNReal.ofReal (|ε| ^ verticalExponent r (k + 1) * C /
            (1 + euclideanNorm (δ - η)) ^ axisExponent r (k + 1)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_translated_scaledAffine_euclidean_decay r k
  let q : ℝ := 2 ^ Fintype.card (AffineAxisIndex r (k + 1))
  have hq : 0 < q := pow_pos (by norm_num) _
  refine ⟨q * C, mul_pos hq hC, fun ε δ η t s a b => ?_⟩
  rw [volume_two_scaledAffineCoveringBoxes]
  calc
    _ ≤ ENNReal.ofReal q *
        ENNReal.ofReal (|ε| ^ verticalExponent r (k + 1) * C /
          (1 + euclideanNorm (δ - η)) ^ axisExponent r (k + 1)) :=
      mul_le_mul_right (h ε δ η t s (fun i => a i / 2) (fun i => b i / 2)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hq.le]
      congr 1
      ring

/-- In degree at least two, the overlap has the dimension-plus-one decay needed for summation. -/
theorem exists_uniform_coveringBox_dimension_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 2)),
      volume (scaledAffineCoveringBox r (k + 2) ε δ t a ∩
        scaledAffineCoveringBox r (k + 2) ε η s b) ≤
          ENNReal.ofReal (|ε| ^ verticalExponent r (k + 2) * C /
            (1 + euclideanNorm (δ - η)) ^ (r + 3)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_translated_scaledAffine_dimension_decay r k
  let q : ℝ := 2 ^ Fintype.card (AffineAxisIndex r (k + 2))
  have hq : 0 < q := pow_pos (by norm_num) _
  refine ⟨q * C, mul_pos hq hC, fun ε δ η t s a b => ?_⟩
  rw [volume_two_scaledAffineCoveringBoxes]
  calc
    _ ≤ ENNReal.ofReal q *
        ENNReal.ofReal (|ε| ^ verticalExponent r (k + 2) * C /
          (1 + euclideanNorm (δ - η)) ^ (r + 3)) :=
      mul_le_mul_right (h ε δ η t s (fun i => a i / 2) (fun i => b i / 2)) _
    _ = _ := by
      rw [← ENNReal.ofReal_mul hq.le]
      congr 1
      ring

/-- Doubling the cutoff box does not change the exact range of uniformly bounded weighted powers. -/
theorem bounded_coveringBox_euclidean_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 1)),
      (1 + euclideanNorm (δ - η)) ^ p *
        (volume (scaledAffineCoveringBox r (k + 1) ε δ t a ∩
          scaledAffineCoveringBox r (k + 1) ε η s b)).toReal ≤
            C * |ε| ^ verticalExponent r (k + 1)) ↔ p ≤ (axisExponent r (k + 1) : ℝ) := by
  let q : ℝ := 2 ^ Fintype.card (AffineAxisIndex r (k + 1))
  have hq : 0 < q := pow_pos (by norm_num) _
  constructor
  · rintro ⟨C, h⟩
    apply (bounded_translated_scaledAffine_euclidean_iff r k p).mp
    refine ⟨C / q, fun ε δ η t s a b => ?_⟩
    have hb := h ε δ η t s (fun i => 2 * a i) (fun i => 2 * b i)
    have ha : (fun i => (2 * a i) / 2) = a := by funext i; ring
    have hb' : (fun i => (2 * b i) / 2) = b := by funext i; ring
    rw [volume_two_scaledAffineCoveringBoxes, ha, hb', ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hq.le] at hb
    apply (mul_le_mul_iff_right₀ hq).mp
    calc
      _ = (1 + euclideanNorm (δ - η)) ^ p *
          (q * (volume (scaledAffineBox r (k + 1) ε δ t a ∩
            scaledAffineBox r (k + 1) ε η s b)).toReal) := by ring
      _ ≤ C * |ε| ^ verticalExponent r (k + 1) := hb
      _ = (C / q * q) * |ε| ^ verticalExponent r (k + 1) := by
        rw [div_mul_cancel₀ C (ne_of_gt hq)]
      _ = _ := by ring
  · intro hp
    obtain ⟨C, h⟩ := (bounded_translated_scaledAffine_euclidean_iff r k p).mpr hp
    refine ⟨q * C, fun ε δ η t s a b => ?_⟩
    rw [volume_two_scaledAffineCoveringBoxes, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hq.le]
    calc
      _ = q * ((1 + euclideanNorm (δ - η)) ^ p *
          (volume (scaledAffineBox r (k + 1) ε δ t (fun i => a i / 2) ∩
            scaledAffineBox r (k + 1) ε η s (fun i => b i / 2))).toReal) := by ring
      _ ≤ q * (C * |ε| ^ verticalExponent r (k + 1)) :=
        mul_le_mul_of_nonneg_left (h ε δ η t s (fun i => a i / 2) (fun i => b i / 2)) hq.le
      _ = _ := by ring

/-- Both exponents of the sharp covering-box estimate have explicit binomial formulas. -/
theorem exists_uniform_coveringBox_binomial_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ)
      (a b : AffineAxisSpace r (k + 1)),
      volume (scaledAffineCoveringBox r (k + 1) ε δ t a ∩
        scaledAffineCoveringBox r (k + 1) ε η s b) ≤
          ENNReal.ofReal (|ε| ^ (r + (k + 1) + 2).choose (r + 3) * C /
            (1 + euclideanNorm (δ - η)) ^
              (∑ j ∈ Finset.range ((k + 1 + 1) / 2), (r + (k + 1) + 1 - 2 * j).choose (r + 2))) := by
  simpa only [verticalExponent_eq_binomial, axisExponent_eq_binomial_sum] using
    exists_uniform_coveringBox_euclidean_decay r k

/-- A covering box centered at the corresponding vertical point of the moment manifold. -/
def momentCoveringBox (r k : ℕ) (ε : ℝ) (δ : Fin (r + 1) → ℝ) (t : ℝ) :
    Set (AffineAxisSpace r k) :=
  scaledAffineCoveringBox r k ε δ t (horizontalMoment r k 0 t)

/-- Moment-centered boxes satisfy the sharp estimate for all directions and physical vertical shifts. -/
theorem exists_uniform_momentCoveringBox_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (δ η : Fin (r + 1) → ℝ) (t s : ℝ),
      volume (momentCoveringBox r (k + 1) ε δ t ∩ momentCoveringBox r (k + 1) ε η s) ≤
        ENNReal.ofReal (|ε| ^ verticalExponent r (k + 1) * C /
          (1 + euclideanNorm (δ - η)) ^ axisExponent r (k + 1)) := by
  obtain ⟨C, hC, h⟩ := exists_uniform_coveringBox_euclidean_decay r k
  exact ⟨C, hC, fun ε δ η t s => h ε δ η t s _ _⟩

#print axioms volume_two_scaledAffineCoveringBoxes
#print axioms exists_uniform_coveringBox_euclidean_decay
#print axioms exists_uniform_coveringBox_dimension_decay
#print axioms bounded_coveringBox_euclidean_iff
#print axioms exists_uniform_coveringBox_binomial_decay
#print axioms exists_uniform_momentCoveringBox_decay

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
