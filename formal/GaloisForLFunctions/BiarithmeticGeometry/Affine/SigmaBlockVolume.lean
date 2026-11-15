import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaBlockAlgebra
import GaloisForLFunctions.BiarithmeticGeometry.Affine.SigmaProductVolume

/-!
# Volume factorization for scalar-coordinate block overlaps

Regrouping a finite dependent family of scalar coordinates preserves
Lebesgue volume. A block-diagonal overlap therefore has the product of its
block overlap volumes, with arbitrary matrices and independent cube centers.
-/

open MeasureTheory Matrix
open scoped BigOperators
open GaloisForLFunctions.BiarithmeticGeometry.MixedCoordinateVolume
open GaloisForLFunctions.BiarithmeticGeometry.SigmaProductVolume

namespace GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
noncomputable section
variable {ι : Type*} {κ : ι → Type*} [Fintype ι] [DecidableEq ι] [∀ i, Fintype (κ i)]
  [∀ i, DecidableEq (κ i)]

/-- Arbitrary block-diagonal cube overlaps factor after regrouping scalar coordinates. -/
theorem volume_blockDiagonal_overlap (B : ∀ i, Matrix (κ i) (κ i) ℝ)
    (a b : Sigma κ → ℝ) :
    volume (centeredCube a 1 ∩ (Matrix.toLin' (Matrix.blockDiagonal' B)) ⁻¹' centeredCube b 1) =
      ∏ i, volume (centeredCube (fun j => a ⟨i, j⟩) 1 ∩
        (Matrix.toLin' (B i)) ⁻¹' centeredCube (fun j => b ⟨i, j⟩) 1) := by
  have hpre : (MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)).symm ⁻¹'
      (centeredCube a 1 ∩ (Matrix.toLin' (Matrix.blockDiagonal' B)) ⁻¹' centeredCube b 1) =
      Set.pi Set.univ (fun i => centeredCube (fun j => a ⟨i, j⟩) 1 ∩
        (Matrix.toLin' (B i)) ⁻¹' centeredCube (fun j => b ⟨i, j⟩) 1) := by
    ext x
    have hc (i : ι) (j : κ i) :
        Matrix.toLin' (Matrix.blockDiagonal' B)
            ((MeasurableEquiv.piCurry (fun (i : ι) (_ : κ i) => ℝ)).symm x) ⟨i, j⟩ =
          Matrix.toLin' (B i) (x i) j := blockDiagonal_mulVec B _ i j
    constructor
    · rintro ⟨⟨hl, hu⟩, ⟨kl, ku⟩⟩ i _
      refine ⟨⟨fun j => hl ⟨i, j⟩, fun j => hu ⟨i, j⟩⟩, ⟨?_, ?_⟩⟩
      · intro j
        simpa only [hc] using kl ⟨i, j⟩
      · intro j
        simpa only [hc] using ku ⟨i, j⟩
    · intro h
      refine ⟨⟨fun p => (h p.1 (Set.mem_univ _)).1.1 p.2,
        fun p => (h p.1 (Set.mem_univ _)).1.2 p.2⟩, ⟨?_, ?_⟩⟩
      · rintro ⟨i, j⟩
        rw [hc]
        exact (h i (Set.mem_univ _)).2.1 j
      · rintro ⟨i, j⟩
        rw [hc]
        exact (h i (Set.mem_univ _)).2.2 j
  rw [← volume_preimage_uncurry (fun (i : ι) (_ : κ i) => ℝ), hpre, volume_pi_pi]

#print axioms volume_blockDiagonal_overlap

end
end GaloisForLFunctions.BiarithmeticGeometry.SigmaBlockMatrix
