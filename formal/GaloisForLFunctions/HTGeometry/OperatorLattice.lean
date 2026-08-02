import GaloisForLFunctions.HTGeometry.DifferentialOperatorOreField
import GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionDimension
import GaloisForLFunctions.HTGeometry.SubspaceRelativeDimension

/-!
# Lattices of differential operators inside the skew field

The integral vectors `R^ι` sit inside `Q^ι`, where `R = K[∂;δ]` and `Q` is its skew field of
fractions.  For a matrix `P` with left independent rows, the row lattice `j_P (R^{ι'})` sits inside
its saturation `Row_Q(P) ∩ R^ι`, and the two are commensurable: every integral vector of the row
span becomes a row combination after multiplication by a single nonzero operator, and the
saturation is finitely generated because the operator ring is left Noetherian.
-/

open scoped Differential
open nonZeroDivisors OreLocalization

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]

theorem numeratorRingHom_mul (r : DiffOp K) (x : PseudoDiffOp K) :
    (numeratorRingHom r : PseudoDiffOp K) * x = r • x := by
  have hnum : (numeratorRingHom r : PseudoDiffOp K) = r /ₒ (1 : (DiffOp K)⁰) :=
    OreLocalization.numeratorHom_apply
  rw [hnum, ← smul_eq_mul, OreLocalization.oreDiv_one_smul]

variable {ι ι' : Type*}

/-- The entrywise embedding of integral vectors into vectors of rational pseudodifferential
operators. -/
def integralVec (ι : Type*) : (ι → DiffOp K) →ₗ[DiffOp K] (ι → PseudoDiffOp K) where
  toFun w := fun j => numeratorRingHom (w j)
  map_add' w₁ w₂ := by
    funext j
    exact map_add _ _ _
  map_smul' r w := by
    funext j
    show (numeratorRingHom (r * w j) : PseudoDiffOp K) = r • numeratorRingHom (w j)
    rw [map_mul, numeratorRingHom_mul]

@[simp] theorem integralVec_apply (w : ι → DiffOp K) (j : ι) :
    integralVec ι w j = numeratorRingHom (w j) := rfl

theorem integralVec_injective : Function.Injective (integralVec (K := K) ι) := by
  intro w₁ w₂ h
  funext j
  exact numeratorRingHom_injective (congrFun h j)

/-- The lattice of integral vectors. -/
def integralLattice (ι : Type*) : Submodule (DiffOp K) (ι → PseudoDiffOp K) :=
  LinearMap.range (integralVec ι)

theorem mem_integralLattice_iff {w : ι → PseudoDiffOp K} :
    w ∈ integralLattice (K := K) ι ↔ ∃ v : ι → DiffOp K, integralVec ι v = w := Iff.rfl

variable [Fintype ι']

/-- The row map of a matrix, as a left linear map over the operator ring. -/
def pseudoVecMulLin (P : ι' → ι → DiffOp K) :
    (ι' → PseudoDiffOp K) →ₗ[DiffOp K] (ι → PseudoDiffOp K) where
  toFun := pseudoVecMul P
  map_add' v w := by
    funext j
    simp only [pseudoVecMul, Pi.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
  map_smul' r v := by
    funext j
    show ∑ i, (r • v i) * toPseudoMatrix P i j = r • ∑ i, v i * toPseudoMatrix P i j
    rw [← numeratorRingHom_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← numeratorRingHom_mul, ← mul_assoc]

@[simp] theorem pseudoVecMulLin_apply (P : ι' → ι → DiffOp K) (v : ι' → PseudoDiffOp K) :
    pseudoVecMulLin P v = pseudoVecMul P v := rfl

/-- The lattice spanned by the rows of `P`. -/
def rowLattice (P : ι' → ι → DiffOp K) : Submodule (DiffOp K) (ι → PseudoDiffOp K) :=
  (integralLattice ι').map (pseudoVecMulLin P)

/-- The saturation of the row lattice: the integral vectors of the row span. -/
def satLattice (P : ι' → ι → DiffOp K) : Submodule (DiffOp K) (ι → PseudoDiffOp K) :=
  LinearMap.range (pseudoVecMulLin P) ⊓ integralLattice ι

theorem rowLattice_le_satLattice (P : ι' → ι → DiffOp K) :
    rowLattice P ≤ satLattice P := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨w, rfl⟩ := hv
  refine ⟨⟨integralVec ι' w, rfl⟩, ?_⟩
  refine ⟨fun j => ∑ i, w i * P i j, ?_⟩
  funext j
  show (numeratorRingHom (∑ i, w i * P i j) : PseudoDiffOp K)
    = ∑ i, (integralVec ι' w) i * toPseudoMatrix P i j
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  rfl

/-- Every integral vector of the row span becomes a row combination after multiplication by one
nonzero operator. -/
theorem exists_smul_mem_rowLattice (P : ι' → ι → DiffOp K)
    {w : ι → PseudoDiffOp K} (hw : w ∈ satLattice P) :
    ∃ b : DiffOp K, b ≠ 0 ∧ b • w ∈ rowLattice P := by
  classical
  obtain ⟨⟨v, hv⟩, -⟩ := hw
  obtain ⟨b, hb, hclear⟩ := exists_common_denominator v Finset.univ
  choose y hy using fun i => hclear i (Finset.mem_univ i)
  refine ⟨b, hb, ⟨integralVec ι' y, ⟨y, rfl⟩, ?_⟩⟩
  have hyv : integralVec ι' y = b • v := by
    funext i
    rw [integralVec_apply, ← hy i, numeratorRingHom_mul]
    rfl
  rw [hyv, map_smul, hv]


variable [Fintype ι]

/-- The saturation is finitely generated over the operator ring. -/
theorem fg_satLattice (P : ι' → ι → DiffOp K) : (satLattice P).FG := by
  have hle : satLattice P ≤ LinearMap.range (integralVec ι) := fun w hw => hw.2
  have hmap : (Submodule.comap (integralVec ι) (satLattice P)).map (integralVec ι)
      = satLattice P := Submodule.map_comap_eq_self hle
  rw [← hmap]
  exact (fg_submodule _).map _

/-- **Commensurability of the row lattice and its saturation.** -/
theorem finiteDimensional_satLattice_mod_rowLattice (P : ι' → ι → DiffOp K) :
    FiniteDimensional K
      (((satLattice P).restrictScalars K).map ((rowLattice P).restrictScalars K).mkQ) :=
  finiteDimensional_map_mkQ_of_fg_torsion (fg_satLattice P)
    fun _ ht => exists_smul_mem_rowLattice P ht


/-- The row map as a map of coefficient-field spaces. -/
def rowMapK (P : ι' → ι → DiffOp K) :
    (ι' → PseudoDiffOp K) →ₗ[K] (ι → PseudoDiffOp K) :=
  (pseudoVecMulLin P).restrictScalars K

omit [Fintype ι] in
@[simp] theorem rowMapK_apply (P : ι' → ι → DiffOp K) (v : ι' → PseudoDiffOp K) :
    rowMapK P v = pseudoVecMul P v := rfl

omit [Fintype ι] in
theorem rowMapK_injective (P : ι' → ι → DiffOp K) (hP : RowIndep P) :
    Function.Injective (rowMapK P) := pseudoVecMul_injective P hP

omit [Fintype ι] in
theorem map_restrictScalars_rowMapK (P : ι' → ι → DiffOp K)
    (N : Submodule (DiffOp K) (ι' → PseudoDiffOp K)) :
    (N.restrictScalars K).map (rowMapK P) = (N.map (pseudoVecMulLin P)).restrictScalars K := by
  ext x
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, rfl⟩

omit [Fintype ι] in
/-- **Transport of the prefix invariant through the row map.**  The intrinsic prefix invariants of
a pair of lattices upstairs are the prefix invariants of their images. -/
theorem relIndexSup_rowMapK (P : ι' → ι → DiffOp K) (hP : RowIndep P) {κ : Type*}
    (cut : κ → Submodule K (ι' → PseudoDiffOp K)) (M : Submodule K (ι' → PseudoDiffOp K)) :
    relIndexSup (fun i => (cut i).map (rowMapK P))
        (((integralLattice ι').restrictScalars K).map (rowMapK P)) (M.map (rowMapK P))
      = relIndexSup cut ((integralLattice ι').restrictScalars K) M :=
  relIndexSup_map_injective (rowMapK P) (rowMapK_injective P hP) cut _ M

/-- **The Cartan prefix comparison.**  Computing the prefix invariants of a moving lattice against
the row lattice or against its saturation differs by at most twice the relative dimension of the
two base lattices — a constant depending on neither the moving lattice nor the cuts. -/
theorem relIndexSup_row_sat_comparison (P : ι' → ι → DiffOp K) {κ : Type*} [Nonempty κ]
    (cut : κ → Submodule K (ι → PseudoDiffOp K)) (M : Submodule K (ι → PseudoDiffOp K))
    (hfin₁ : ∀ i, FiniteDimensional K
      ((M ⊓ cut i).map ((((rowLattice P).restrictScalars K) ⊓ cut i)).mkQ))
    (hfin₂ : ∀ i, FiniteDimensional K
      (((((satLattice P).restrictScalars K) ⊓ cut i)).map ((M ⊓ cut i)).mkQ))
    (hbdd₁ : BddAbove (Set.range fun i =>
      relIndex (((rowLattice P).restrictScalars K) ⊓ cut i) (M ⊓ cut i)))
    (hbdd₂ : BddAbove (Set.range fun i =>
      relIndex (((satLattice P).restrictScalars K) ⊓ cut i) (M ⊓ cut i))) :
    0 ≤ relIndexSup cut ((rowLattice P).restrictScalars K) M
          - relIndexSup cut ((satLattice P).restrictScalars K) M ∧
      relIndexSup cut ((rowLattice P).restrictScalars K) M
          - relIndexSup cut ((satLattice P).restrictScalars K) M
        ≤ 2 * (quotDim ((rowLattice P).restrictScalars K)
            ((satLattice P).restrictScalars K) : ℤ) := by
  haveI := finiteDimensional_satLattice_mod_rowLattice P
  exact relIndexSup_sub_bounds cut
    (fun x hx => rowLattice_le_satLattice P hx) M hfin₁ hfin₂ hbdd₁ hbdd₂

end

end DiffOp

end GaloisForLFunctions.HTGeometry
