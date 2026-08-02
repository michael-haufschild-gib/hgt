import GaloisForLFunctions.HTGeometry.OperatorLattice
import GaloisForLFunctions.HTGeometry.DifferentialOperatorRowSpace
import GaloisForLFunctions.HTGeometry.DiagonalLatticeIndex
import GaloisForLFunctions.HTGeometry.DifferentialOperatorPseudoRightInverse

/-!
# The length of the integral Kähler–Ore conductor

The conductor of a matrix over `K[∂;δ]` is the saturation of its row lattice modulo that lattice.
For a square matrix with left independent rows the row map over the skew field is bijective, so the
saturation is the whole integral lattice and the conductor is the quotient of the free module by
the row lattice.  Its length is therefore the sum of the orders of the elementary divisors of the
matrix, and for a single operator `d` it is `deg d`.
-/

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι ι' : Type*} [Fintype ι] [Fintype ι']

/-- The integral embedding, as a map of coefficient-field spaces. -/
def integralVecK (ι : Type*) : (ι → DiffOp K) →ₗ[K] (ι → PseudoDiffOp K) :=
  (integralVec ι).restrictScalars K

omit [Fintype ι] in
@[simp] theorem integralVecK_apply (w : ι → DiffOp K) (j : ι) :
    integralVecK ι w j = numeratorRingHom (w j) := rfl

omit [Fintype ι] in
theorem integralVecK_injective : Function.Injective (integralVecK (K := K) ι) :=
  integralVec_injective

omit [Fintype ι] in
/-- The integral row map commutes with the row map over the skew field. -/
theorem pseudoVecMul_integralVec (P : ι' → ι → DiffOp K) (y : ι' → DiffOp K) :
    pseudoVecMul P (integralVec ι' y) = integralVec ι (vecMul y P) := by
  funext j
  show ∑ i, (numeratorRingHom (y i) : PseudoDiffOp K) * toPseudoMatrix P i j
    = numeratorRingHom (∑ i, y i * P i j)
  rw [map_sum]
  exact Finset.sum_congr rfl fun i _ => (map_mul numeratorRingHom (y i) (P i j)).symm

omit [Fintype ι] in
theorem map_top_integralVecK :
    Submodule.map (integralVecK (K := K) ι) ⊤ = (integralLattice ι).restrictScalars K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, -, rfl⟩
    exact ⟨w, rfl⟩
  · rintro w ⟨v, rfl⟩
    exact ⟨v, Submodule.mem_top, rfl⟩

omit [Fintype ι] in
theorem map_rowSpace_integralVecK (P : ι' → ι → DiffOp K) :
    Submodule.map (integralVecK (K := K) ι) (rowSpace P) = (rowLattice P).restrictScalars K := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    obtain ⟨v, rfl⟩ := mem_rowSpace.mp hw
    exact ⟨integralVec ι' v, ⟨v, rfl⟩, pseudoVecMul_integralVec P v⟩
  · rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
    exact ⟨vecMul v P, mem_rowSpace.mpr ⟨v, rfl⟩, (pseudoVecMul_integralVec P v).symm⟩

/-- For a square matrix with left independent rows the row map over the skew field is bijective,
so the saturation of the row lattice is the whole integral lattice. -/
theorem satLattice_eq_integralLattice (P : ι → ι → DiffOp K) (hP : RowIndep P) :
    satLattice P = integralLattice ι := by
  have hsurj : Function.Surjective (pseudoVecMulSkewLin (K := K) P) :=
    LinearMap.injective_iff_surjective.mp (pseudoVecMul_injective P hP)
  refine le_antisymm (fun w hw => hw.2) fun w hw => ⟨?_, hw⟩
  obtain ⟨v, hv⟩ := hsurj w
  exact ⟨v, hv⟩

variable [DecidableEq ι]

/-- **The length of the conductor.**  For a square matrix with left independent rows the conductor
`Sat(row lattice) / (row lattice)` has dimension the sum of the orders of the elementary divisors
of the matrix. -/
theorem exists_degree_sum_eq_quotDim_conductor (P : ι → ι → DiffOp K) (hP : RowIndep P) :
    ∃ d : ι → DiffOp K, (∀ i, d i ≠ 0) ∧
      quotDim ((rowLattice P).restrictScalars K) ((satLattice P).restrictScalars K)
        = ∑ i, degree (d i) := by
  obtain ⟨d, hd, hsum⟩ := exists_degree_sum_eq_finrank_quotient_rowSpace P hP rfl
  refine ⟨d, hd, ?_⟩
  rw [satLattice_eq_integralLattice P hP, ← map_top_integralVecK, ← map_rowSpace_integralVecK,
    quotDim_map_injective _ integralVecK_injective, quotDim_top, hsum]

/-- **The conductor of a single operator.**  The conductor of the one-by-one matrix `d` has length
`deg d`; for `d = ∂ᵏ` this is the conductor of the substitution `y = δᵏ x`. -/
theorem quotDim_conductor_single (d : DiffOp K) (hd : d ≠ 0) :
    quotDim ((rowLattice (fun _ _ : Unit => d)).restrictScalars K)
        ((satLattice (fun _ _ : Unit => d)).restrictScalars K) = degree d := by
  have hindep : RowIndep (fun _ _ : Unit => d) := by
    intro v hv
    have h : ∑ i : Unit, v i * d = 0 := congrFun hv ()
    rw [Finset.univ_unique, Finset.sum_singleton] at h
    funext a
    show v a = 0
    rw [Subsingleton.elim a default]
    exact (mul_eq_zero.mp h).resolve_right hd
  have hdiag : Diagonalized (fun _ _ : Unit => d) := by
    intro i j _
    exact ⟨fun i' hi' => absurd (Subsingleton.elim i' i) hi',
      fun j' hj' => absurd (Subsingleton.elim j' j) hj'⟩
  rw [satLattice_eq_integralLattice _ hindep, ← map_top_integralVecK, ← map_rowSpace_integralVecK,
    quotDim_map_injective _ integralVecK_injective, quotDim_top,
    finrank_quotient_rowSpace_of_diagonalized hdiag (Equiv.refl Unit) fun _ => hd]
  simp

end

end DiffOp

end GaloisForLFunctions.HTGeometry
