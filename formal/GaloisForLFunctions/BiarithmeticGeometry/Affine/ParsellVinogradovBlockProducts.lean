import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearExponent
import Mathlib.Tactic.Choose

/-!
# Exact product structure of independent shear blocks

For a finite family of homogeneous binomial blocks, cube overlaps are
Cartesian products. Their volumes multiply, and their sharp decay exponents
add. Independent centers in every block preserve the uniform upper bound.
-/

open MeasureTheory
open scoped ENNReal BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section
variable {ι : Type*}

/-- A finite family of homogeneous coordinate blocks. -/
abbrev BlockSpace (m : ι → ℕ) := ∀ i, Fin (m i) → ℝ

/-- The shear acts separately on every homogeneous block. -/
def blockFrame (m : ι → ℕ) (θ : ℝ) : BlockSpace m →ₗ[ℝ] BlockSpace m where
  toFun x i := Matrix.toLin' (shearBlock (m i) θ) (x i)
  map_add' x y := by
    funext i
    exact (Matrix.toLin' (shearBlock (m i) θ)).map_add (x i) (y i)
  map_smul' a x := by
    funext i
    exact (Matrix.toLin' (shearBlock (m i) θ)).map_smul a (x i)

theorem blockFrame_apply (m : ι → ℕ) (θ : ℝ) (x : BlockSpace m) (i : ι) :
    blockFrame m θ x i = Matrix.toLin' (shearBlock (m i) θ) (x i) := rfl

/-- The unit cube in the product of the block coordinate spaces. -/
def blockCube (m : ι → ℕ) (a : BlockSpace m) : Set (BlockSpace m) :=
  Set.pi Set.univ (fun i => centeredCube (a i) 1)

/-- Overlap of two independently centered cubes under the block shear. -/
def blockOverlap (m : ι → ℕ) (θ : ℝ) (a b : BlockSpace m) : Set (BlockSpace m) :=
  blockCube m a ∩ blockFrame m θ ⁻¹' blockCube m b

/-- The overlap splits as a literal Cartesian product, without a coordinate change. -/
theorem blockOverlap_eq_pi (m : ι → ℕ) (θ : ℝ) (a b : BlockSpace m) :
    blockOverlap m θ a b = Set.pi Set.univ (fun i =>
      centeredCube (a i) 1 ∩
        (Matrix.toLin' (shearBlock (m i) θ)) ⁻¹' centeredCube (b i) 1) := by
  ext x
  constructor
  · rintro ⟨hx, hy⟩ i _
    exact ⟨hx i (Set.mem_univ i), hy i (Set.mem_univ i)⟩
  · intro h
    exact ⟨fun i _ => (h i (Set.mem_univ i)).1, fun i _ => (h i (Set.mem_univ i)).2⟩

variable [Fintype ι]

/-- Lebesgue volume of a block overlap is exactly the product of the block volumes. -/
theorem volume_blockOverlap (m : ι → ℕ) (θ : ℝ) (a b : BlockSpace m) :
    volume (blockOverlap m θ a b) = ∏ i, volume
      (centeredCube (a i) 1 ∩
        (Matrix.toLin' (shearBlock (m i) θ)) ⁻¹' centeredCube (b i) 1) := by
  rw [blockOverlap_eq_pi, volume_pi_pi]

/-- The full coordinate dimension is the sum of the block dimensions. -/
theorem volume_blockCube (m : ι → ℕ) (a : BlockSpace m) :
    volume (blockCube m a) = (2 : ℝ≥0∞) ^ (∑ i, m i) := by
  rw [blockCube, volume_pi_pi]
  simp only [volume_centeredCube, mul_one, ENNReal.ofReal_ofNat, Fintype.card_fin]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem volume_blockOverlap_le (m : ι → ℕ) (θ : ℝ) (a b : BlockSpace m) :
    volume (blockOverlap m θ a b) ≤ (2 : ℝ≥0∞) ^ (∑ i, m i) := by
  calc
    _ ≤ volume (blockCube m a) := measure_mono Set.inter_subset_left
    _ = _ := volume_blockCube m a

/-- The total decay power contributed by the independent blocks. -/
def blockExponent (m : ι → ℕ) : ℕ := ∑ i, (m i) ^ 2 / 4

private theorem prod_ofReal_div_pow (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (x : ℝ) (hx : 0 ≤ x) (d : ι → ℕ) :
    (∏ i, ENNReal.ofReal (c i / x ^ d i)) =
      ENNReal.ofReal ((∏ i, c i) / x ^ (∑ i, d i)) := by
  rw [← ENNReal.ofReal_prod_of_nonneg
    (fun i _ => div_nonneg (hc i) (pow_nonneg hx _)),
    Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum]

/-- The sum of block exponents gives a uniform upper bound for arbitrary cube centers. -/
theorem exists_uniform_block_overlap_decay (m : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ : ℝ) (a b : BlockSpace m),
      volume (blockOverlap m θ a b) ≤ ENNReal.ofReal (C / (1 + |θ|) ^ blockExponent m) := by
  classical
  choose C hC hbound using fun i => exists_uniform_shear_overlap_decay (m i)
  refine ⟨∏ i, C i, Finset.prod_pos (fun i _ => hC i), ?_⟩
  intro θ a b
  rw [volume_blockOverlap]
  calc
    _ ≤ ∏ i, ENNReal.ofReal (C i / (1 + |θ|) ^ ((m i) ^ 2 / 4)) :=
      Finset.prod_le_prod' (fun i _ => hbound i θ (a i) (b i))
    _ = _ := prod_ofReal_div_pow C (fun i => (hC i).le) _ (by positivity) _

/-- Centered block overlaps have matching lower and upper bounds with the summed exponent. -/
theorem exists_block_overlap_two_sided (m : ι → ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ : ℝ,
      ENNReal.ofReal (c / (1 + |θ|) ^ blockExponent m) ≤ volume (blockOverlap m θ 0 0) ∧
      volume (blockOverlap m θ 0 0) ≤ ENNReal.ofReal (C / (1 + |θ|) ^ blockExponent m) := by
  classical
  choose c C hc hC hbound using fun i => exists_shear_overlap_two_sided (m i)
  refine ⟨∏ i, c i, ∏ i, C i, Finset.prod_pos (fun i _ => hc i),
    Finset.prod_pos (fun i _ => hC i), ?_⟩
  intro θ
  rw [volume_blockOverlap]
  constructor
  · calc
      _ = ∏ i, ENNReal.ofReal (c i / (1 + |θ|) ^ ((m i) ^ 2 / 4)) :=
        (prod_ofReal_div_pow c (fun i => (hc i).le) _ (by positivity) _).symm
      _ ≤ _ := Finset.prod_le_prod' (fun i _ => (hbound i θ).1)
  · calc
      _ ≤ ∏ i, ENNReal.ofReal (C i / (1 + |θ|) ^ ((m i) ^ 2 / 4)) :=
        Finset.prod_le_prod' (fun i _ => (hbound i θ).2)
      _ = _ := prod_ofReal_div_pow C (fun i => (hC i).le) _ (by positivity) _

#print axioms blockOverlap_eq_pi
#print axioms volume_blockOverlap
#print axioms volume_blockCube
#print axioms exists_uniform_block_overlap_decay
#print axioms exists_block_overlap_two_sided

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
