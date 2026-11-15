import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovHomogeneousMoments
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBlockExponent
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBinaryExponent

/-!
# Sharp overlap decay for binary polynomial moment frames

All nonconstant monomials in two variables of degree at most `k` are grouped
by total degree. The physical shear on this full moment vector is exactly
the product of the homogeneous binomial blocks of sizes `2,…,k+1`.
Consequently its optimal overlap exponent is the sum of the quarter-square
block exponents, equal to the proposed binomial sum `B₂,ₖ`.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Coordinates for all binary monomials of degrees one through `k`. -/
abbrev BinaryMomentSpace (k : ℕ) := BlockSpace (fun d : Fin k => d.val + 2)

/-- The full binary polynomial moment map, grouped by total degree. -/
def binaryMoment (k : ℕ) (x z : ℝ) : BinaryMomentSpace k :=
  fun d => homogeneousMoment (d.val + 1) x z

/-- The physical shear on the full binary moment space. -/
def binaryFrame (k : ℕ) (θ : ℝ) : BinaryMomentSpace k →ₗ[ℝ] BinaryMomentSpace k :=
  blockFrame (fun d : Fin k => d.val + 2) θ

/-- Every nonconstant monomial through degree `k` transforms by the same physical shear. -/
theorem binaryFrame_moment (k : ℕ) (θ x z : ℝ) :
    binaryFrame k θ (binaryMoment k x z) = binaryMoment k x (z + θ * x) := by
  funext d
  exact shearLinear_homogeneousMoment (d.val + 1) θ x z

/-- Overlap of two independent coordinate cubes for the full binary moment frame. -/
def binaryOverlap (k : ℕ) (θ : ℝ) (a b : BinaryMomentSpace k) : Set (BinaryMomentSpace k) :=
  blockCube (fun d : Fin k => d.val + 2) a ∩
    binaryFrame k θ ⁻¹' blockCube (fun d : Fin k => d.val + 2) b

private theorem binary_blockExponent (k : ℕ) :
    blockExponent (fun d : Fin k => d.val + 2) = binaryExponent k := by
  exact Fin.sum_univ_eq_sum_range (fun d : ℕ => (d + 2) ^ 2 / 4) k

/-- The full binary frame has the summed sharp upper bound, uniformly in both cube centers. -/
theorem exists_uniform_binary_overlap_decay (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (a b : BinaryMomentSpace k),
      volume (binaryOverlap k θ a b) ≤ ENNReal.ofReal (C / (1 + |θ|) ^ binaryExponent k) := by
  simpa only [binaryOverlap, binaryFrame, blockOverlap, binary_blockExponent] using
    exists_uniform_block_overlap_decay (fun d : Fin k => d.val + 2)

/-- Common zero centers give a matching lower bound for the entire polynomial moment frame. -/
theorem exists_binary_overlap_two_sided (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : ℝ,
      ENNReal.ofReal (c / (1 + |θ|) ^ binaryExponent k) ≤ volume (binaryOverlap k θ 0 0) ∧
      volume (binaryOverlap k θ 0 0) ≤ ENNReal.ofReal (C / (1 + |θ|) ^ binaryExponent k) := by
  simpa only [binaryOverlap, binaryFrame, blockOverlap, binary_blockExponent] using
    exists_block_overlap_two_sided (fun d : Fin k => d.val + 2)

/-- The proposed binary exponent is the exact threshold, uniformly over independent cube centers. -/
theorem bounded_binary_overlap_uniform_centers_iff (k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ : ℝ) (a b : BinaryMomentSpace k),
      (1 + |θ|) ^ p * (volume (binaryOverlap k θ a b)).toReal ≤ C) ↔
        p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (k + 1 - 2 * j).choose 2 : ℕ) := by
  simpa only [binaryOverlap, binaryFrame, blockOverlap, binary_blockExponent,
    binaryExponent_eq_binomial_sum] using
    bounded_block_overlap_uniform_centers_iff (fun d : Fin k => d.val + 2) p

#print axioms binaryFrame_moment
#print axioms exists_uniform_binary_overlap_decay
#print axioms exists_binary_overlap_two_sided
#print axioms bounded_binary_overlap_uniform_centers_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
