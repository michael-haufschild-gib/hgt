import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovBinaryFrames
import GaloisForLFunctions.BiarithmeticGeometry.Affine.ParsellVinogradovShearGroup

/-!
# Relative overlap of full binary moment frames

Each homogeneous shear preserves volume and composes by addition. Product
structure therefore identifies two-frame overlap with the overlap at the
parameter difference. The sharp binary exponent applies uniformly to both
frame parameters and to independent cube centers.
-/

open MeasureTheory
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
noncomputable section
variable {ι : Type*}

/-- The independent block frames form an additive shear representation. -/
theorem blockFrame_comp_apply (m : ι → ℕ) (θ φ : ℝ) (x : BlockSpace m) :
    blockFrame m θ (blockFrame m φ x) = blockFrame m (θ + φ) x := by
  funext i
  exact shearLinear_comp_apply (m i) θ φ (x i)

/-- Zero shear fixes every vector in the product coordinate space. -/
theorem blockFrame_zero_apply (m : ι → ℕ) (x : BlockSpace m) :
    blockFrame m 0 x = x := by
  funext i
  exact shearLinear_zero_apply (m i) (x i)

/-- A blockwise shear sends a product cube to the product of its individual images. -/
theorem blockFrame_image_blockCube (m : ι → ℕ) (θ : ℝ) (a : BlockSpace m) :
    blockFrame m θ '' blockCube m a = Set.pi Set.univ (fun i =>
      (Matrix.toLin' (shearBlock (m i) θ)) '' centeredCube (a i) 1) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ i _
    exact ⟨x i, hx i (Set.mem_univ i), rfl⟩
  · intro hy
    choose x hx hxy using fun i => hy i (Set.mem_univ i)
    refine ⟨x, fun i _ => hx i, ?_⟩
    funext i
    exact hxy i

variable [Fintype ι]

/-- Relative block overlap depends exactly on the difference of the shear parameters. -/
theorem volume_two_blockFrame_images (m : ι → ℕ) (θ φ : ℝ) (a b : BlockSpace m) :
    volume (blockFrame m θ '' blockCube m a ∩ blockFrame m φ '' blockCube m b) =
      volume (blockOverlap m (θ - φ) a b) := by
  have hset : blockFrame m θ '' blockCube m a ∩ blockFrame m φ '' blockCube m b =
      Set.pi Set.univ (fun i =>
        (Matrix.toLin' (shearBlock (m i) θ)) '' centeredCube (a i) 1 ∩
          (Matrix.toLin' (shearBlock (m i) φ)) '' centeredCube (b i) 1) := by
    rw [blockFrame_image_blockCube, blockFrame_image_blockCube]
    ext y
    constructor
    · rintro ⟨ha, hb⟩ i _
      exact ⟨ha i (Set.mem_univ i), hb i (Set.mem_univ i)⟩
    · intro h
      exact ⟨fun i _ => (h i (Set.mem_univ i)).1, fun i _ => (h i (Set.mem_univ i)).2⟩
  rw [hset, volume_pi_pi, volume_blockOverlap]
  apply Finset.prod_congr rfl
  intro i _
  exact volume_two_shearLinear_images (m i) θ φ _ _

/-- The summed exponent controls arbitrary pairs of block frames. -/
theorem exists_uniform_two_blockFrame_decay (m : ι → ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (θ φ : ℝ) (a b : BlockSpace m),
      volume (blockFrame m θ '' blockCube m a ∩ blockFrame m φ '' blockCube m b) ≤
        ENNReal.ofReal (C / (1 + |θ - φ|) ^ blockExponent m) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_block_overlap_decay m
  refine ⟨C, hC, fun θ φ a b => ?_⟩
  rw [volume_two_blockFrame_images]
  exact hbound (θ - φ) a b

/-- Exact relative-volume identity on all binary monomials through degree `k`. -/
theorem volume_two_binary_frames (k : ℕ) (θ φ : ℝ) (a b : BinaryMomentSpace k) :
    volume (binaryFrame k θ '' blockCube (fun d : Fin k => d.val + 2) a ∩
      binaryFrame k φ '' blockCube (fun d : Fin k => d.val + 2) b) =
        volume (binaryOverlap k (θ - φ) a b) :=
  volume_two_blockFrame_images (fun d : Fin k => d.val + 2) θ φ a b

/-- Relative overlap of centered binary frames has matching sharp power bounds. -/
theorem exists_two_binary_frames_two_sided (k : ℕ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ θ φ : ℝ,
      ENNReal.ofReal (c / (1 + |θ - φ|) ^ binaryExponent k) ≤
        volume (binaryFrame k θ '' blockCube (fun d : Fin k => d.val + 2) 0 ∩
          binaryFrame k φ '' blockCube (fun d : Fin k => d.val + 2) 0) ∧
      volume (binaryFrame k θ '' blockCube (fun d : Fin k => d.val + 2) 0 ∩
          binaryFrame k φ '' blockCube (fun d : Fin k => d.val + 2) 0) ≤
        ENNReal.ofReal (C / (1 + |θ - φ|) ^ binaryExponent k) := by
  obtain ⟨c, C, hc, hC, hbound⟩ := exists_binary_overlap_two_sided k
  refine ⟨c, C, hc, hC, fun θ φ => ?_⟩
  rw [volume_two_binary_frames]
  exact hbound (θ - φ)

/-- The binary binomial exponent is sharp even with two frame parameters and arbitrary centers. -/
theorem bounded_two_binary_frames_uniform_centers_iff (k : ℕ) (p : ℝ) :
    (∃ C : ℝ, ∀ (θ φ : ℝ) (a b : BinaryMomentSpace k),
      (1 + |θ - φ|) ^ p *
        (volume (binaryFrame k θ '' blockCube (fun d : Fin k => d.val + 2) a ∩
          binaryFrame k φ '' blockCube (fun d : Fin k => d.val + 2) b)).toReal ≤ C) ↔
      p ≤ (∑ j ∈ Finset.range ((k + 1) / 2), (k + 1 - 2 * j).choose 2 : ℕ) := by
  constructor
  · rintro ⟨C, hC⟩
    apply (bounded_binary_overlap_uniform_centers_iff k p).mp
    refine ⟨C, fun θ a b => ?_⟩
    simpa only [volume_two_binary_frames, sub_zero] using hC θ 0 a b
  · intro hp
    obtain ⟨C, hC⟩ := (bounded_binary_overlap_uniform_centers_iff k p).mpr hp
    refine ⟨C, fun θ φ a b => ?_⟩
    rw [volume_two_binary_frames]
    exact hC (θ - φ) a b

#print axioms blockFrame_image_blockCube
#print axioms blockFrame_comp_apply
#print axioms volume_two_blockFrame_images
#print axioms exists_uniform_two_blockFrame_decay
#print axioms volume_two_binary_frames
#print axioms exists_two_binary_frames_two_sided
#print axioms bounded_two_binary_frames_uniform_centers_iff

end
end GaloisForLFunctions.BiarithmeticGeometry.ParsellVinogradov
