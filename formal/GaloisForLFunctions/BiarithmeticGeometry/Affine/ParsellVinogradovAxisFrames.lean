import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovAxisExponent
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovRelativeFrames

/-!
# Sharp coordinate-direction shear overlap in every dimension

All nonconstant monomials in `r+2` variables split into binary chains after
fixing total degree and the `r` untouched-variable exponents. Their actual
moment shear is the direct product of the corresponding binomial blocks.
The exact overlap exponent is therefore the proposed binomial sum, and the
same exponent governs two frames through their relative shear parameter.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section

/-- Binary chains among all nonconstant monomials through degree `k`. -/
abbrev AxisChain (r k : ℕ) := Σ d : Fin k, HomogeneousChain r (d.val + 1)

/-- The number of active binary coordinates in a chain. -/
def axisChainSize (r k : ℕ) (a : AxisChain r k) : ℕ := chainDegree a.2 + 1

/-- All nonconstant moment coordinates, grouped into chains for a coordinate-direction shear. -/
abbrev AxisMomentSpace (r k : ℕ) := BlockSpace (axisChainSize r k)

/-- The actual polynomial moment vector in `r+2` variables. -/
def axisMoment (r k : ℕ) (y : Fin r → ℝ) (x z : ℝ) : AxisMomentSpace r k :=
  fun a => chainMoment r (a.1.val + 1) y x z a.2

/-- Shear in the distinguished horizontal direction, fixing the other horizontal variables. -/
def axisFrame (r k : ℕ) (θ : ℝ) : AxisMomentSpace r k →ₗ[ℝ] AxisMomentSpace r k :=
  blockFrame (axisChainSize r k) θ

/-- The block matrix acts on every monomial by the physical coordinate shear. -/
theorem axisFrame_moment (r k : ℕ) (θ : ℝ) (y : Fin r → ℝ) (x z : ℝ) :
    axisFrame r k θ (axisMoment r k y x z) = axisMoment r k y x (z + θ * x) := by
  funext a
  exact shearLinear_chainMoment r (a.1.val + 1) θ y x z a.2

/-- The block exponent is exactly the multivariate sum over homogeneous degrees. -/
theorem blockExponent_axisChainSize (r k : ℕ) :
    blockExponent (axisChainSize r k) = axisExponent r k := by
  unfold blockExponent
  rw [Fintype.sum_sigma]
  change (∑ d : Fin k, homogeneousAxisExponent r (d.val + 1)) = axisExponent r k
  exact Fin.sum_univ_eq_sum_range (fun d : ℕ => homogeneousAxisExponent r (d + 1)) k

/-- Overlap with independent centers in every monomial coordinate. -/
def axisOverlap (r k : ℕ) (θ : ℝ) (a b : AxisMomentSpace r k) : Set (AxisMomentSpace r k) :=
  blockOverlap (axisChainSize r k) θ a b

/-- The proposed exponent gives a uniform bound for the genuine moment shear in every dimension. -/
theorem exists_uniform_axis_overlap_decay (r k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (a b : AxisMomentSpace r k),
      volume (axisOverlap r k θ a b) ≤
        ENNReal.ofReal (C / (1 + |θ|) ^ axisExponent r k) := by
  simpa only [axisOverlap, blockExponent_axisChainSize] using
    exists_uniform_block_overlap_decay (axisChainSize r k)

/-- Zero centers attain the same decay power in every dimension. -/
theorem exists_axis_overlap_two_sided (r k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : ℝ,
      ENNReal.ofReal (c / (1 + |θ|) ^ axisExponent r k) ≤ volume (axisOverlap r k θ 0 0) ∧
      volume (axisOverlap r k θ 0 0) ≤ ENNReal.ofReal (C / (1 + |θ|) ^ axisExponent r k) := by
  simpa only [axisOverlap, blockExponent_axisChainSize] using
    exists_block_overlap_two_sided (axisChainSize r k)

/-- The proposed `B_(r+2,k)` is the exact uniform exponent for coordinate-direction shears. -/
theorem bounded_axis_overlap_uniform_centers_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ : ℝ) (a b : AxisMomentSpace r k),
      (1 + |θ|) ^ p * (volume (axisOverlap r k θ a b)).toReal ≤ C) ↔
        p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  simpa only [axisOverlap, blockExponent_axisChainSize, axisExponent_eq_binomial_sum] using
    bounded_block_overlap_uniform_centers_iff (axisChainSize r k) p

/-- Two actual moment frames reduce exactly to the relative coordinate-direction shear. -/
theorem volume_two_axis_frames (r k : ℕ) (θ φ : ℝ) (a b : AxisMomentSpace r k) :
    volume (axisFrame r k θ '' blockCube (axisChainSize r k) a ∩
      axisFrame r k φ '' blockCube (axisChainSize r k) b) =
        volume (axisOverlap r k (θ - φ) a b) :=
  volume_two_blockFrame_images (axisChainSize r k) θ φ a b

/-- Relative coordinate-direction frames have the same exact binomial threshold. -/
theorem bounded_two_axis_frames_uniform_centers_iff (r k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ φ : ℝ) (a b : AxisMomentSpace r k),
      (1 + |θ - φ|) ^ p * (volume (axisFrame r k θ '' blockCube (axisChainSize r k) a ∩
        axisFrame r k φ '' blockCube (axisChainSize r k) b)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (r + k + 1 - 2 * j).choose (r + 2) : ℕ) := by
  rw [← bounded_axis_overlap_uniform_centers_iff]
  simp only [volume_two_axis_frames]
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun θ a b => by simpa only [sub_zero] using hC θ 0 a b⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun θ φ a b => hC (θ - φ) a b⟩

#print axioms axisFrame_moment
#print axioms blockExponent_axisChainSize
#print axioms exists_uniform_axis_overlap_decay
#print axioms exists_axis_overlap_two_sided
#print axioms bounded_axis_overlap_uniform_centers_iff
#print axioms volume_two_axis_frames
#print axioms bounded_two_axis_frames_uniform_centers_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
