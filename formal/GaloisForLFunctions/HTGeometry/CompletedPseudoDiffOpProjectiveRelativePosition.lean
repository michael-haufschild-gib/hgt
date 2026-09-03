import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpCartanUniqueness
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingStandardApartment

/-!
# Projective Euclidean relative position of completed pseudodifferential lattices

The canonical dominant Cartan vector changes by one common integer when either lattice
representative is left-scaled.  Centering removes that translation, so the resulting zero-sum
Euclidean vector descends to the actual projective lattice quotient.  This supplies the exact
vector-valued relative position on vertices of the differential variational building.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {r : ℕ}

/-- Arbitrary right scaling of a diagonal coweight lattice adds the scalar's additive valuation
to every coweight coordinate. -/
theorem rightScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_unitAddValue
    (m : Fin r → ℤ) (a : (CompletedPseudoDiffOp K)ˣ) :
    rightScaleCompletedPseudoDiffOpLattice a
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (m + fun _ => completedPseudoDiffOpUnitAddValue a) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_rightScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff] at hx ⊢
    intro i
    have hxi := hx i
    rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg] at hxi ⊢
    change 0 ≤ completedPseudoDiffOpAddValue
      ((x i * (a : CompletedPseudoDiffOp K)) *
        (((completedPseudoDiffOpUniformizerUnit (K := K) ^
          (m i + completedPseudoDiffOpUnitAddValue a))⁻¹ :
            (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K))
    change 0 ≤ completedPseudoDiffOpAddValue
      (x i * (((completedPseudoDiffOpUniformizerUnit (K := K) ^ m i)⁻¹ :
        (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K)) at hxi
    rw [completedPseudoDiffOpAddValue_mul, completedPseudoDiffOpAddValue_mul,
      completedPseudoDiffOpAddValue_unit_eq_coe,
      completedPseudoDiffOpAddValue_unit_eq_coe,
      completedPseudoDiffOpUnitAddValue_inv,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at ⊢
    rw [completedPseudoDiffOpAddValue_mul,
      completedPseudoDiffOpAddValue_unit_eq_coe,
      completedPseudoDiffOpUnitAddValue_inv,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hxi
    simpa [add_assoc] using hxi
  · intro hy
    let x : Fin r → CompletedPseudoDiffOp K := fun i => y i * (a⁻¹ : CompletedPseudoDiffOp K)
    refine ⟨x, ?_, ?_⟩
    · rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff] at hy ⊢
      intro i
      have hyi := hy i
      rw [mem_completedPseudoDiffOpInteger_iff_addValue_nonneg] at hyi ⊢
      dsimp [x]
      simp only [completedPseudoDiffOpUniformizerCoweight]
      change 0 ≤ completedPseudoDiffOpAddValue
        ((y i * (a : CompletedPseudoDiffOp K)⁻¹) *
          (((completedPseudoDiffOpUniformizerUnit (K := K) ^ m i)⁻¹ :
            (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K))
      change 0 ≤ completedPseudoDiffOpAddValue
        (y i * (((completedPseudoDiffOpUniformizerUnit (K := K) ^
          (m i + completedPseudoDiffOpUnitAddValue a))⁻¹ :
            (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K)) at hyi
      rw [completedPseudoDiffOpAddValue_mul, completedPseudoDiffOpAddValue_mul,
        completedPseudoDiffOpAddValue_inv,
        completedPseudoDiffOpAddValue_unit_eq_coe,
        completedPseudoDiffOpAddValue_unit_eq_coe,
        completedPseudoDiffOpUnitAddValue_inv,
        completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at ⊢
      rw [completedPseudoDiffOpAddValue_mul,
        completedPseudoDiffOpAddValue_unit_eq_coe,
        completedPseudoDiffOpUnitAddValue_inv,
        completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hyi
      simpa [add_assoc] using hyi
    · funext i
      simp [x, rightMulCompletedPseudoIntegerVecLinearEquiv]

/-- Ambient right multiplication realizes lattice right scaling. -/
theorem mapCompletedPseudoDiffOpLatticeLinear_rightMul
    (a : (CompletedPseudoDiffOp K)ˣ)
    (L : CompletedPseudoDiffOpLattice K (Fin r)) :
    mapCompletedPseudoDiffOpLatticeLinear
        (rightMulCompletedPseudoVecLinearEquiv (ι := Fin r) a) L =
      rightScaleCompletedPseudoDiffOpLattice a L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff,
    mem_rightScaleCompletedPseudoDiffOpLattice_iff]
  rfl

/-- The zero coweight lattice is the standard lattice. -/
theorem standardCompletedPseudoDiffOpLatticeAtCoweight_zero :
    standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (fun _ : Fin r => 0) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff,
    mem_standardCompletedPseudoDiffOpLattice_iff]
  constructor <;> intro h i
  · simpa [completedPseudoDiffOpUniformizerCoweight] using h i
  · simpa [completedPseudoDiffOpUniformizerCoweight] using h i

/-- Scaling the second representative adds its value to every dominant Cartan coordinate. -/
theorem completedPseudoDiffOpDominantRelativePosition_second_leftScale
    (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpDominantRelativePosition L
        (leftScaleCompletedPseudoDiffOpLattice a M) =
      completedPseudoDiffOpDominantRelativePosition L M +
        fun _ => completedPseudoDiffOpUnitAddValue a := by
  let d := completedPseudoDiffOpDominantCartanData L M
  let z := completedPseudoDiffOpUnitAddValue a
  have hmap : mapCompletedPseudoDiffOpLatticeLinear d.frame
      (leftScaleCompletedPseudoDiffOpLattice a M) =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (d.coweight + fun _ => z) := by
    rw [mapCompletedPseudoDiffOpLatticeLinear_leftScale, d.map_right,
      leftScaleCompletedPseudoDiffOpLattice_eq_uniformizer_zpow_unitAddValue,
      leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const]
  have hanti : Antitone (d.coweight + fun _ => z) := by
    intro i j hij
    simpa [Pi.add_apply, add_comm] using add_le_add_right (d.dominant hij) z
  have hcanonical := completedPseudoDiffOpDominantRelativePosition_eq
    L (leftScaleCompletedPseudoDiffOpLattice a M) d.frame
    (d.coweight + fun _ => z) d.map_left hmap hanti
  exact hcanonical.symm

/-- Scaling the first representative subtracts its value from every dominant Cartan coordinate. -/
theorem completedPseudoDiffOpDominantRelativePosition_first_leftScale
    (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpDominantRelativePosition
        (leftScaleCompletedPseudoDiffOpLattice a L) M =
      completedPseudoDiffOpDominantRelativePosition L M -
        fun _ => completedPseudoDiffOpUnitAddValue a := by
  let d := completedPseudoDiffOpDominantCartanData L M
  let z := completedPseudoDiffOpUnitAddValue a
  let q := rightMulCompletedPseudoVecLinearEquiv (ι := Fin r) a⁻¹
  let f := d.frame.trans q
  have hqstd : mapCompletedPseudoDiffOpLatticeLinear q
      (leftScaleCompletedPseudoDiffOpLattice a
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r))) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
    rw [mapCompletedPseudoDiffOpLatticeLinear_leftScale,
      mapCompletedPseudoDiffOpLatticeLinear_rightMul,
      ← standardCompletedPseudoDiffOpLatticeAtCoweight_zero,
      rightScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_unitAddValue]
    rw [leftScaleCompletedPseudoDiffOpLattice_eq_uniformizer_zpow_unitAddValue,
      leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const]
    rw [completedPseudoDiffOpUnitAddValue_inv]
    congr 1
    funext i
    simp
  have hfL : mapCompletedPseudoDiffOpLatticeLinear f
      (leftScaleCompletedPseudoDiffOpLattice a L) =
      standardCompletedPseudoDiffOpLattice (K := K) (ι := Fin r) := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans,
      mapCompletedPseudoDiffOpLatticeLinear_leftScale, d.map_left, hqstd]
  have hfM : mapCompletedPseudoDiffOpLatticeLinear f M =
      standardCompletedPseudoDiffOpLatticeAtCoweight (K := K)
        (d.coweight - fun _ => z) := by
    rw [← mapCompletedPseudoDiffOpLatticeLinear_trans, d.map_right,
      mapCompletedPseudoDiffOpLatticeLinear_rightMul,
      rightScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_unitAddValue,
      completedPseudoDiffOpUnitAddValue_inv]
    congr 2
  have hanti : Antitone (d.coweight - fun _ => z) := by
    intro i j hij
    simpa [Pi.sub_apply] using sub_le_sub_right (d.dominant hij) z
  have hcanonical := completedPseudoDiffOpDominantRelativePosition_eq
    (leftScaleCompletedPseudoDiffOpLattice a L) M f
    (d.coweight - fun _ => z) hfL hfM hanti
  exact hcanonical.symm

/-- Centered Euclidean relative-position vector of two actual lattices. -/
def completedPseudoDiffOpEuclideanRelativePosition
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) : Fin r → ℝ :=
  centeredCoweight (completedPseudoDiffOpDominantRelativePosition L M)

/-- Centering removes a change of the second projective representative. -/
theorem completedPseudoDiffOpEuclideanRelativePosition_second_leftScale
    (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpEuclideanRelativePosition L
        (leftScaleCompletedPseudoDiffOpLattice a M) =
      completedPseudoDiffOpEuclideanRelativePosition L M := by
  rw [completedPseudoDiffOpEuclideanRelativePosition,
    completedPseudoDiffOpDominantRelativePosition_second_leftScale]
  exact centeredCoweight_add_const _ _

/-- Centering removes a change of the first projective representative. -/
theorem completedPseudoDiffOpEuclideanRelativePosition_first_leftScale
    (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpEuclideanRelativePosition
        (leftScaleCompletedPseudoDiffOpLattice a L) M =
      completedPseudoDiffOpEuclideanRelativePosition L M := by
  change centeredCoweight
      (completedPseudoDiffOpDominantRelativePosition
        (leftScaleCompletedPseudoDiffOpLattice a L) M) =
    centeredCoweight (completedPseudoDiffOpDominantRelativePosition L M)
  rw [completedPseudoDiffOpDominantRelativePosition_first_leftScale]
  have hrew : completedPseudoDiffOpDominantRelativePosition L M -
      (fun _ => completedPseudoDiffOpUnitAddValue a) =
      completedPseudoDiffOpDominantRelativePosition L M +
        fun _ => -completedPseudoDiffOpUnitAddValue a := by
    funext i
    simp [Pi.sub_apply, Pi.add_apply, sub_eq_add_neg]
  rw [hrew, centeredCoweight_add_const]

/-- Centered relative position as a literal point of the zero-sum Euclidean apartment. -/
def completedPseudoDiffOpEuclideanRelativePositionPoint
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    DifferentialVariationalEuclideanApartment (Fin r) :=
  ⟨WithLp.toLp 2 (completedPseudoDiffOpEuclideanRelativePosition L M),
    centeredCoweight_sum_eq_zero
      (completedPseudoDiffOpDominantRelativePosition L M)⟩

theorem completedPseudoDiffOpEuclideanRelativePositionPoint_first_leftScale
    (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpEuclideanRelativePositionPoint
        (leftScaleCompletedPseudoDiffOpLattice a L) M =
      completedPseudoDiffOpEuclideanRelativePositionPoint L M := by
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2)
    (completedPseudoDiffOpEuclideanRelativePosition_first_leftScale L M a)

theorem completedPseudoDiffOpEuclideanRelativePositionPoint_second_leftScale
    (L M : CompletedPseudoDiffOpLattice K (Fin r))
    (a : (CompletedPseudoDiffOp K)ˣ) :
    completedPseudoDiffOpEuclideanRelativePositionPoint L
        (leftScaleCompletedPseudoDiffOpLattice a M) =
      completedPseudoDiffOpEuclideanRelativePositionPoint L M := by
  apply Subtype.ext
  exact congrArg (WithLp.toLp 2)
    (completedPseudoDiffOpEuclideanRelativePosition_second_leftScale L M a)

/-- **Projective vector distance.**  The centered dominant Cartan vector is independent of both
lattice representatives and therefore descends to projective vertices. -/
def differentialVariationalProjectiveEuclideanRelativePosition
    (x y : DifferentialVariationalProjectiveBuildingCarrier K (Fin r)) :
    DifferentialVariationalEuclideanApartment (Fin r) :=
  Quotient.liftOn₂ x y completedPseudoDiffOpEuclideanRelativePositionPoint (by
    intro L M L' M' hL hM
    obtain ⟨a, rfl⟩ := hL
    obtain ⟨b, rfl⟩ := hM
    exact (completedPseudoDiffOpEuclideanRelativePositionPoint_first_leftScale
      L M a).symm.trans
        (completedPseudoDiffOpEuclideanRelativePositionPoint_second_leftScale
          (leftScaleCompletedPseudoDiffOpLattice a L) M b).symm)

@[simp] theorem differentialVariationalProjectiveEuclideanRelativePosition_mk
    (L M : CompletedPseudoDiffOpLattice K (Fin r)) :
    differentialVariationalProjectiveEuclideanRelativePosition
        (Quotient.mk _ L) (Quotient.mk _ M) =
      completedPseudoDiffOpEuclideanRelativePositionPoint L M := rfl

end

end GaloisForLFunctions.HTGeometry.DiffOp
