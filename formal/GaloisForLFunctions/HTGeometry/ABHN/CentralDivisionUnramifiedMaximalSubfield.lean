import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionLocalDegreeExact

/-!
# Unramified maximal subfields of local division algebras

Restrict the determinant valuation of a finite division algebra to any commutative subfield.  Its
valuation order embeds in the determinant order, its maximal ideal is the exact pullback of the
determinant maximal ideal, and hence its residue field embeds in the determinant residue field.

For the full-residue-degree generator constructed in `CentralDivisionLocalDegreeExact`, that
residue embedding is surjective.  Consequently one chosen field `F[x]` simultaneously has degree
`deg(A)` and residue field equal to the full determinant residue field.  This is the
valuation-theoretic unramified maximal-subfield slice needed for local cyclic exhaustion.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

universe u

variable {F A : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [DivisionRing A] [Algebra F A] [Module.Finite F A]

/-- Determinant valuation restricted to a commutative subfield of the division algebra. -/
noncomputable def divisionAlgebraDeterminantRestrictedValuation
    (T : Subalgebra F A) (hT : IsField T) :
    letI : Field T := hT.toField
    Valuation T NNReal := by
  letI : Field T := hT.toField
  exact {
    toFun := fun t => ‖Algebra.norm F (t : A)‖₊
    map_zero' := by simp [Algebra.norm_zero]
    map_one' := by simp
    map_mul' := by intro x y; simp [map_mul]
    map_add_le_max' := by
      intro x y
      apply NNReal.coe_le_coe.mp
      change ‖Algebra.norm F ((x : A) + (y : A))‖ ≤
        max ‖Algebra.norm F (x : A)‖ ‖Algebra.norm F (y : A)‖
      exact divisionAlgebra_norm_isNonarchimedean (F := F) (A := A) (x : A) (y : A) }

/-- Valuation ring cut out on a commutative subfield by the ambient determinant valuation. -/
abbrev DivisionAlgebraDeterminantRestrictedValuationSubring
    (T : Subalgebra F A) (hT : IsField T) : Type u :=
  letI : Field T := hT.toField
  (divisionAlgebraDeterminantRestrictedValuation (F := F) (A := A) T hT).valuationSubring

/-- Inclusion from the restricted valuation ring into the ambient determinant order. -/
noncomputable def divisionAlgebraDeterminantRestrictedValuationSubringToOrder
    (T : Subalgebra F A) (hT : IsField T) :
    DivisionAlgebraDeterminantRestrictedValuationSubring (F := F) (A := A) T hT →+*
      divisionAlgebraDeterminantValuationSubring (F := F) (A := A) := by
  letI : Field T := hT.toField
  exact {
    toFun := fun t => ⟨((t : T) : A), by
      change ‖Algebra.norm F ((t : T) : A)‖ ≤ 1
      exact_mod_cast t.property⟩
    map_one' := rfl
    map_mul' := by intros; rfl
    map_zero' := rfl
    map_add' := by intros; rfl }

/-- The restricted maximal ideal is exactly the pullback of the determinant maximal ideal. -/
theorem divisionAlgebraDeterminantMaximalIdeal_comap_restrictedValuationSubring
    (T : Subalgebra F A) (hT : IsField T) :
    Ideal.comap
        (divisionAlgebraDeterminantRestrictedValuationSubringToOrder
          (F := F) (A := A) T hT)
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) =
      IsLocalRing.maximalIdeal
        (DivisionAlgebraDeterminantRestrictedValuationSubring (F := F) (A := A) T hT) := by
  letI : Field T := hT.toField
  ext t
  rw [Ideal.mem_comap, mem_divisionAlgebraDeterminantMaximalIdeal_iff,
    Valuation.mem_maximalIdeal_iff T
      (divisionAlgebraDeterminantRestrictedValuation (F := F) (A := A) T hT)]
  change ‖Algebra.norm F ((t : _) : A)‖ < 1 ↔
    ‖Algebra.norm F ((t : _) : A)‖₊ < 1
  simpa only [coe_nnnorm] using
    (NNReal.coe_lt_one (r := ‖Algebra.norm F ((t : _) : A)‖₊))

/-- Residue field of the determinant valuation restricted to a commutative subfield. -/
abbrev DivisionAlgebraDeterminantRestrictedResidue
    (T : Subalgebra F A) (hT : IsField T) : Type u :=
  DivisionAlgebraDeterminantRestrictedValuationSubring (F := F) (A := A) T hT ⧸
    IsLocalRing.maximalIdeal
      (DivisionAlgebraDeterminantRestrictedValuationSubring (F := F) (A := A) T hT)

/-- Residue embedding induced by inclusion of a restricted valuation order in the determinant
order. -/
noncomputable def divisionAlgebraDeterminantRestrictedResidueToResidue
    (T : Subalgebra F A) (hT : IsField T) :
    DivisionAlgebraDeterminantRestrictedResidue (F := F) (A := A) T hT →+*
      DivisionAlgebraDeterminantResidue (F := F) (A := A) := by
  letI : Field T := hT.toField
  exact Ideal.quotientMap
      (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A))
      (divisionAlgebraDeterminantRestrictedValuationSubringToOrder
        (F := F) (A := A) T hT)
      (by rw [divisionAlgebraDeterminantMaximalIdeal_comap_restrictedValuationSubring])

/-- The residue embedding of a restricted determinant valuation is injective. -/
theorem divisionAlgebraDeterminantRestrictedResidueToResidue_injective
    (T : Subalgebra F A) (hT : IsField T) :
    Function.Injective
      (divisionAlgebraDeterminantRestrictedResidueToResidue (F := F) (A := A) T hT) := by
  letI : Field T := hT.toField
  unfold divisionAlgebraDeterminantRestrictedResidueToResidue
  apply Ideal.quotientMap_injective'
  rw [divisionAlgebraDeterminantMaximalIdeal_comap_restrictedValuationSubring]

/-- Every base-residue scalar lies in the image of the restricted residue embedding. -/
theorem algebraMap_mem_divisionAlgebraDeterminantRestrictedResidueToResidue_range
    (T : Subalgebra F A) (hT : IsField T)
    (c : NormValuationResidue (F := F)) :
    algebraMap (NormValuationResidue (F := F))
        (DivisionAlgebraDeterminantResidue (F := F) (A := A)) c ∈
      (divisionAlgebraDeterminantRestrictedResidueToResidue
        (F := F) (A := A) T hT).range := by
  letI : Field T := hT.toField
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
  let tc : T := algebraMap F T (c : F)
  let oc : DivisionAlgebraDeterminantRestrictedValuationSubring
      (F := F) (A := A) T hT := ⟨tc, by
    change ‖Algebra.norm F (algebraMap F A (c : F))‖₊ ≤ 1
    have hc : algebraMap F A (c : F) ∈
        divisionAlgebraDeterminantValuationSubring (F := F) (A := A) :=
      (algebraMap_mem_divisionAlgebraDeterminantValuationSubring_iff
        (F := F) (A := A) (c : F)).mpr (by exact_mod_cast c.property)
    exact_mod_cast hc⟩
  refine ⟨Ideal.Quotient.mk _ oc, ?_⟩
  rfl

/-- A restricted residue embedding is surjective as soon as the reduction of one element in the
subfield generates the ambient determinant residue algebra. -/
theorem divisionAlgebraDeterminantRestrictedResidueToResidue_surjective_of_generator
    (T : Subalgebra F A) (hT : IsField T)
    (x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A))
    (hxT : (x : A) ∈ T)
    (hgen : Algebra.adjoin (NormValuationResidue (F := F))
        ({Ideal.Quotient.mk
            (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) x} :
          Set (DivisionAlgebraDeterminantResidue (F := F) (A := A))) = ⊤) :
    Function.Surjective
      (divisionAlgebraDeterminantRestrictedResidueToResidue
        (F := F) (A := A) T hT) := by
  letI : Field T := hT.toField
  let tx : T := ⟨(x : A), hxT⟩
  let ox : DivisionAlgebraDeterminantRestrictedValuationSubring
      (F := F) (A := A) T hT := ⟨tx, by
    change ‖Algebra.norm F (x : A)‖₊ ≤ 1
    exact_mod_cast x.property⟩
  have hxrange : Ideal.Quotient.mk
        (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) x ∈
      (divisionAlgebraDeterminantRestrictedResidueToResidue
        (F := F) (A := A) T hT).range := by
    refine ⟨Ideal.Quotient.mk _ ox, ?_⟩
    rfl
  intro z
  have hz : z ∈ Algebra.adjoin (NormValuationResidue (F := F))
      ({Ideal.Quotient.mk
          (divisionAlgebraDeterminantMaximalIdeal (F := F) (A := A)) x} :
        Set (DivisionAlgebraDeterminantResidue (F := F) (A := A))) := by
    rw [hgen]
    exact Set.mem_univ z
  exact Algebra.adjoin_induction (p := fun y _ => y ∈
      (divisionAlgebraDeterminantRestrictedResidueToResidue
        (F := F) (A := A) T hT).range)
    (fun y hy => by simpa only [Set.mem_singleton_iff] using hy ▸ hxrange)
    (fun c => algebraMap_mem_divisionAlgebraDeterminantRestrictedResidueToResidue_range
      (F := F) (A := A) T hT c)
    (fun _ _ _ _ hy hz => add_mem hy hz)
    (fun _ _ _ _ hy hz => mul_mem hy hz) hz

variable [Algebra.IsCentral F A] [LocallyCompactSpace F]

/-- A local central division algebra contains a maximal-degree commutative subfield whose
restricted determinant residue field is the entire determinant residue field.  This packages the
unramified maximal-subfield slice as a degree identity plus an actual residue-field equivalence. -/
theorem exists_maximalSubfield_restrictedResidue_equiv :
    ∃ x : divisionAlgebraDeterminantValuationSubring (F := F) (A := A),
      let T := Algebra.adjoin F ({(x : A)} : Set A)
      ∃ hT : IsField T,
        Module.finrank F T = divisionAlgebraDegree (F := F) (A := A) ∧
          Nonempty
            (DivisionAlgebraDeterminantRestrictedResidue (F := F) (A := A) T hT ≃+*
              DivisionAlgebraDeterminantResidue (F := F) (A := A)) := by
  obtain ⟨x, hdegree, hgen⟩ :=
    exists_fullResidueDegree_maximalSubfieldGenerator (F := F) (A := A)
  let T := Algebra.adjoin F ({(x : A)} : Set A)
  let hT : IsField T := algebraAdjoinSingleton_isField_of_finiteDivisionRing F A (x : A)
  refine ⟨x, hT, hdegree, ?_⟩
  let f := divisionAlgebraDeterminantRestrictedResidueToResidue
    (F := F) (A := A) T hT
  refine ⟨RingEquiv.ofBijective f ⟨?_, ?_⟩⟩
  · exact divisionAlgebraDeterminantRestrictedResidueToResidue_injective
      (F := F) (A := A) T hT
  · exact divisionAlgebraDeterminantRestrictedResidueToResidue_surjective_of_generator
      (F := F) (A := A) T hT x
      (Algebra.self_mem_adjoin_singleton F (x : A)) hgen

end

end GaloisForLFunctions.HTGeometry.ABHN
