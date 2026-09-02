import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveInterleavingMetric

/-!
# Projective interleaving distance on the standard apartment

Diagonal lattice inclusion is exactly the coordinatewise reverse coweight order.  Every arbitrary
left scalar has the same lattice action as the uniformizer power given by its additive valuation.
Consequently the descended projective interleaving distance on the standard apartment is the
least radius after recentering all coweight differences by one common integer.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry.DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- Every left scalar acts on a valuation lattice through its integer additive valuation. -/
theorem leftScaleCompletedPseudoDiffOpLattice_eq_uniformizer_zpow_unitAddValue
    (a : (CompletedPseudoDiffOp K)ˣ) (L : CompletedPseudoDiffOpLattice K ι) :
    leftScaleCompletedPseudoDiffOpLattice a L =
      leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^
          completedPseudoDiffOpUnitAddValue a) L := by
  let z := completedPseudoDiffOpUnitAddValue a
  let u : (CompletedPseudoDiffOp K)ˣ :=
    a * (completedPseudoDiffOpUniformizerUnit (K := K) ^ z)⁻¹
  have hu : completedPseudoDiffOpUnitAddValue u = 0 := by
    simp [u, z, completedPseudoDiffOpUnitAddValue_mul,
      completedPseudoDiffOpUnitAddValue_inv,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow]
  have hfix :=
    leftScaleCompletedPseudoDiffOpLattice_eq_self_of_unitAddValue_eq_zero
      u hu
      (leftScaleCompletedPseudoDiffOpLattice
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ z) L)
  calc
    leftScaleCompletedPseudoDiffOpLattice a L =
      leftScaleCompletedPseudoDiffOpLattice
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

/-- Inclusion of diagonal valuation lattices is exactly reverse coordinatewise coweight order. -/
theorem standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff
    (m n : ι → ℤ) :
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier ≤
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n).carrier ↔
      ∀ i, n i ≤ m i := by
  classical
  constructor
  · intro h i
    let v := completedPseudoDiffOpCoweightBasisVector (K := K) m i
    have hv : v ∈
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).carrier :=
      completedPseudoDiffOpCoweightBasisVector_mem m i
    have hi := (mem_standardCompletedPseudoDiffOpLatticeAtCoweight_iff n v).1 (h hv) i
    let q : (CompletedPseudoDiffOp K)ˣ :=
      completedPseudoDiffOpUniformizerUnit (K := K) ^ m i *
        (completedPseudoDiffOpUniformizerUnit (K := K) ^ n i)⁻¹
    have hq : (q : CompletedPseudoDiffOp K) ∈
        CompletedPseudoDiffOpInteger (K := K) := by
      simpa [q, v, completedPseudoDiffOpCoweightBasisVector,
        diagonalRightMulCompletedPseudoIntegerVecLinearEquiv,
        completedPseudoDiffOpUniformizerCoweight, Pi.basisFun_apply,
        Pi.single_apply, mul_assoc] using hi
    rw [coe_unit_mem_completedPseudoDiffOpInteger_iff] at hq
    dsimp [q] at hq
    rw [completedPseudoDiffOpUnitAddValue_mul,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow,
      completedPseudoDiffOpUnitAddValue_inv,
      completedPseudoDiffOpUnitAddValue_uniformizer_zpow] at hq
    omega
  · exact standardCompletedPseudoDiffOpLatticeAtCoweight_antitone

/-- Literal interleaving of two standard lattices is the coordinatewise centered-box condition. -/
theorem standardCompletedPseudoDiffOpLattice_interleavedAt_iff
    (m n : ι → ℤ) (r : ℕ) :
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).InterleavedAt r
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n) ↔
      ∀ i, n i ≤ m i + (r : ℤ) ∧ m i ≤ n i + (r : ℤ) := by
  unfold CompletedPseudoDiffOpLattice.InterleavedAt
  rw [leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
    leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
    standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff,
    standardCompletedPseudoDiffOpLatticeAtCoweight_carrier_le_iff]
  simp only [Pi.add_apply]
  aesop

/-- Orbit interleaving on the standard apartment is exactly common-integer recentering followed
by the coordinatewise box condition. -/
theorem standardCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff
    (m n : ι → ℤ) (r : ℕ) :
    (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m).LeftOrbitInterleavedAt r
        (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n) ↔
      ∃ c : ℤ, ∀ i,
        n i + c ≤ m i + (r : ℤ) ∧
          m i ≤ n i + c + (r : ℤ) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨completedPseudoDiffOpUnitAddValue a, ?_⟩
    rw [leftScaleCompletedPseudoDiffOpLattice_eq_uniformizer_zpow_unitAddValue,
      leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const] at ha
    exact (standardCompletedPseudoDiffOpLattice_interleavedAt_iff m
      (n + fun _ => completedPseudoDiffOpUnitAddValue a) r).1 ha
  · rintro ⟨c, hc⟩
    refine ⟨completedPseudoDiffOpUniformizerUnit (K := K) ^ c, ?_⟩
    rw [leftScale_standardCompletedPseudoDiffOpLatticeAtCoweight_add_const,
      standardCompletedPseudoDiffOpLattice_interleavedAt_iff]
    simpa only [Pi.add_apply] using hc

/-- Exact standard-apartment formula for every upper bound on the descended projective distance. -/
theorem differentialVariationalProjectiveInterleavingDistance_standard_le_iff
    (m n : ι → ℤ) (r : ℕ) :
    differentialVariationalProjectiveInterleavingDistance
        (Quotient.mk _
          (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) m))
        (Quotient.mk _
          (standardCompletedPseudoDiffOpLatticeAtCoweight (K := K) n)) ≤ r ↔
      ∃ c : ℤ, ∀ i,
        n i + c ≤ m i + (r : ℤ) ∧
          m i ≤ n i + c + (r : ℤ) := by
  rw [differentialVariationalProjectiveInterleavingDistance_mk,
    completedPseudoDiffOpLatticeOrbitInterleavingDistance_le_iff,
    standardCompletedPseudoDiffOpLattice_leftOrbitInterleavedAt_iff]

end

end GaloisForLFunctions.HTGeometry.DiffOp
