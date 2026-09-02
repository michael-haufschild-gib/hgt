import GaloisForLFunctions.HTGeometry.DifferentialVariationalLatticeInterleaving

/-!
# Homothety invariance of lattice interleaving

Left multiplication by a valuation-zero unit fixes every valuation lattice.  Conjugating a
uniformizer power by an arbitrary completed-skew unit changes it only by such a unit at lattice
level.  This supplies the noncommutative argument showing that simultaneous left homothety is an
isometry of the full-lattice interleaving distance.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*}

/-- A completed-skew unit of additive valuation zero stabilizes every valuation lattice. -/
theorem leftScaleCompletedPseudoDiffOpLattice_eq_self_of_unitAddValue_eq_zero
    (a : (CompletedPseudoDiffOp K)ˣ)
    (ha : completedPseudoDiffOpUnitAddValue a = 0)
    (L : CompletedPseudoDiffOpLattice K ι) :
    leftScaleCompletedPseudoDiffOpLattice a L = L := by
  apply CompletedPseudoDiffOpLattice.ext
  ext y
  rw [mem_leftScaleCompletedPseudoDiffOpLattice_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    let c : CompletedPseudoDiffOpInteger (K := K) :=
      ⟨(a : CompletedPseudoDiffOp K),
        (coe_unit_mem_completedPseudoDiffOpInteger_iff a).2 (by simp [ha])⟩
    exact L.carrier.smul_mem c hx
  · intro hy
    let x := leftMulCompletedPseudoIntegerVecSemilinearMap a⁻¹ y
    have hainv : completedPseudoDiffOpUnitAddValue a⁻¹ = 0 := by
      rw [completedPseudoDiffOpUnitAddValue_inv, ha]
      simp
    let c : CompletedPseudoDiffOpInteger (K := K) :=
      ⟨((a⁻¹ : (CompletedPseudoDiffOp K)ˣ) : CompletedPseudoDiffOp K),
        (coe_unit_mem_completedPseudoDiffOpInteger_iff a⁻¹).2 (by simp [hainv])⟩
    have hx : x ∈ L.carrier := by
      exact L.carrier.smul_mem c hy
    refine ⟨x, hx, ?_⟩
    funext i
    change (a : CompletedPseudoDiffOp K) *
      ((a⁻¹ : (CompletedPseudoDiffOp K)ˣ) * y i) = y i
    rw [← mul_assoc]
    simp

/-- Simultaneous left homothety reflects lattice inclusion. -/
theorem leftScaleCompletedPseudoDiffOpLattice_carrier_le_iff
    (a : (CompletedPseudoDiffOp K)ˣ)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    (leftScaleCompletedPseudoDiffOpLattice a L).carrier ≤
        (leftScaleCompletedPseudoDiffOpLattice a M).carrier ↔
      L.carrier ≤ M.carrier := by
  constructor
  · intro h
    have h' := leftScaleCompletedPseudoDiffOpLattice_carrier_mono a⁻¹ h
    simpa only [leftScaleCompletedPseudoDiffOpLattice_mul, inv_mul_cancel,
      leftScaleCompletedPseudoDiffOpLattice_one] using h'
  · exact leftScaleCompletedPseudoDiffOpLattice_carrier_mono a

/-- An inner conjugate of a uniformizer power acts identically on every valuation lattice. -/
theorem leftScale_inner_uniformizer_zpow_eq
    (a : (CompletedPseudoDiffOp K)ˣ) (z : ℤ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    leftScaleCompletedPseudoDiffOpLattice
        (a⁻¹ * completedPseudoDiffOpUniformizerUnit (K := K) ^ z * a) L =
      leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L := by
  let q : (CompletedPseudoDiffOp K)ˣ :=
    a⁻¹ * completedPseudoDiffOpUniformizerUnit (K := K) ^ z * a
  let u : (CompletedPseudoDiffOp K)ˣ :=
    q * (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)⁻¹
  have hu : completedPseudoDiffOpUnitAddValue u = 0 := by
    simp [u, q, completedPseudoDiffOpUnitAddValue_mul,
      completedPseudoDiffOpUnitAddValue_inv,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  have hfix :=
    leftScaleCompletedPseudoDiffOpLattice_eq_self_of_unitAddValue_eq_zero
      u hu
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L)
  calc
    leftScaleCompletedPseudoDiffOpLattice
        (a⁻¹ * completedPseudoDiffOpUniformizerUnit (K := K) ^ z * a) L =
      leftScaleCompletedPseudoDiffOpLattice q L := by rfl
    _ = leftScaleCompletedPseudoDiffOpLattice
        (u * completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L := by
          congr 1
          simp [u]
    _ = leftScaleCompletedPseudoDiffOpLattice u
        (leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L) :=
      (leftScaleCompletedPseudoDiffOpLattice_mul
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) u L).symm
    _ = leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L := hfix

/-- Uniformizer scaling commutes with arbitrary left homothety at lattice level. -/
theorem leftScale_uniformizer_zpow_leftScale
    (a : (CompletedPseudoDiffOp K)ˣ) (z : ℤ)
    (L : CompletedPseudoDiffOpLattice K ι) :
    leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)
        (leftScaleCompletedPseudoDiffOpLattice a L) =
      leftScaleCompletedPseudoDiffOpLattice a
        (leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L) := by
  let q : (CompletedPseudoDiffOp K)ˣ :=
    a⁻¹ * completedPseudoDiffOpUniformizerUnit (K := K) ^ z * a
  calc
    leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)
        (leftScaleCompletedPseudoDiffOpLattice a L) =
      leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z * a) L :=
      leftScaleCompletedPseudoDiffOpLattice_mul a
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L
    _ = leftScaleCompletedPseudoDiffOpLattice (a * q) L := by
      congr 1
      simp [q, mul_assoc]
    _ = leftScaleCompletedPseudoDiffOpLattice a
        (leftScaleCompletedPseudoDiffOpLattice q L) :=
      (leftScaleCompletedPseudoDiffOpLattice_mul q a L).symm
    _ = leftScaleCompletedPseudoDiffOpLattice a
        (leftScaleCompletedPseudoDiffOpLattice
          (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L) := by
      rw [leftScale_inner_uniformizer_zpow_eq a z L]

/-- Simultaneous arbitrary left homothety preserves every interleaving radius exactly. -/
theorem leftScaleCompletedPseudoDiffOpLattice_interleavedAt_iff
    (a : (CompletedPseudoDiffOp K)ˣ)
    (L M : CompletedPseudoDiffOpLattice K ι) (n : ℕ) :
    (leftScaleCompletedPseudoDiffOpLattice a L).InterleavedAt n
        (leftScaleCompletedPseudoDiffOpLattice a M) ↔
      L.InterleavedAt n M := by
  unfold CompletedPseudoDiffOpLattice.InterleavedAt
  rw [leftScale_uniformizer_zpow_leftScale,
    leftScale_uniformizer_zpow_leftScale,
    leftScaleCompletedPseudoDiffOpLattice_carrier_le_iff,
    leftScaleCompletedPseudoDiffOpLattice_carrier_le_iff]

variable [Fintype ι]

/-- Simultaneous arbitrary left homothety is an interleaving-distance isometry. -/
theorem completedPseudoDiffOpLatticeInterleavingDistance_leftScale
    (a : (CompletedPseudoDiffOp K)ˣ)
    (L M : CompletedPseudoDiffOpLattice K ι) :
    completedPseudoDiffOpLatticeInterleavingDistance
        (leftScaleCompletedPseudoDiffOpLattice a L)
        (leftScaleCompletedPseudoDiffOpLattice a M) =
      completedPseudoDiffOpLatticeInterleavingDistance L M := by
  apply le_antisymm
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff,
      leftScaleCompletedPseudoDiffOpLattice_interleavedAt_iff]
    exact completedPseudoDiffOpLatticeInterleavingDistance_spec L M
  · rw [completedPseudoDiffOpLatticeInterleavingDistance_le_iff]
    exact (leftScaleCompletedPseudoDiffOpLattice_interleavedAt_iff a L M _).1
      (completedPseudoDiffOpLatticeInterleavingDistance_spec
        (leftScaleCompletedPseudoDiffOpLattice a L)
        (leftScaleCompletedPseudoDiffOpLattice a M))

end

end GaloisForLFunctions.HTGeometry.DiffOp
