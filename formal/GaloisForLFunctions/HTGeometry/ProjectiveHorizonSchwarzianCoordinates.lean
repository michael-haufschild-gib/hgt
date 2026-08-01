import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFreeJetReciprocalTail
import GaloisForLFunctions.HTGeometry.SchwarzianProjectiveInvariant
import GaloisForLFunctions.HTGeometry.FiniteGeneratorDifferentialEscape

/-!
# The Schwarzian coordinate system on the free scalar jet field

The Schwarzian of the base jet coordinate solves for the third jet: `x'''` is `x'` times the
Schwarzian plus a term in `x'` and `x''` alone.  So the first three jets together with all jets of
the Schwarzian generate a differential subfield, and since it contains the base coordinate it
contains every jet.

The free scalar jet field is therefore the rational field on the Schwarzian coordinate system
`x, x', x''` together with the jets of the Schwarzian.  This is the coordinate change in which the
projective gauge acts on the first three coordinates alone.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

instance freeScalarJetField_charZero (C : Type*) [Field C] [CharZero C] :
    CharZero (FreeScalarJetField C) :=
  charZero_of_injective_algebraMap
    (algebraMap C (FreeScalarJetField C)).injective

/-- The base free jet coordinate, whose jets are the free coordinates. -/
def freeJetBase (C : Type*) [Field C] : FreeScalarJetField C := freeCoordinate C ℕ 0

theorem freeJetBase_deriv (C : Type*) [Field C] :
    (freeJetBase C)′ = freeCoordinate C ℕ 1 := by
  rw [freeJetBase, freeScalarJetField_deriv_apply, freeJetShift_freeCoordinate]

theorem freeJetBase_deriv2 (C : Type*) [Field C] :
    (freeJetBase C)′′ = freeCoordinate C ℕ 2 := by
  rw [show (freeJetBase C)′′ = ((freeJetBase C)′)′ from rfl, freeJetBase_deriv,
    freeScalarJetField_deriv_apply, freeJetShift_freeCoordinate]

theorem freeJetBase_deriv3 (C : Type*) [Field C] :
    (freeJetBase C)′′′ = freeCoordinate C ℕ 3 := by
  rw [show (freeJetBase C)′′′ = ((freeJetBase C)′′)′ from rfl, freeJetBase_deriv2,
    freeScalarJetField_deriv_apply, freeJetShift_freeCoordinate]

/-- The Schwarzian of the base free jet coordinate. -/
def freeJetSchwarzian (C : Type*) [Field C] : FreeScalarJetField C :=
  schwarzian (freeJetBase C)

/-- **The Schwarzian solves for the third jet.** -/
theorem freeCoordinate_three_eq :
    freeCoordinate C ℕ 3 =
      freeCoordinate C ℕ 1 * freeJetSchwarzian C +
        (3 / 2 : FreeScalarJetField C) * freeCoordinate C ℕ 2 ^ 2 / freeCoordinate C ℕ 1 := by
  have h1 : freeCoordinate C ℕ 1 ≠ 0 := freeScalarJetCoordinate_ne_zero 1
  rw [freeJetSchwarzian, schwarzian, freeJetBase_deriv3, freeJetBase_deriv2, freeJetBase_deriv]
  field_simp
  ring

/-- The elements of an intermediate field whose derivative stays in it form an intermediate
field. -/
def derivationStable {L' E : Type*} [Field L'] [Field E] [Algebra L' E]
    (L : IntermediateField L' E) (D : Derivation L' E E) : IntermediateField L' E where
  carrier := {y | y ∈ L ∧ D y ∈ L}
  zero_mem' := ⟨zero_mem L, by rw [map_zero]; exact zero_mem L⟩
  one_mem' := ⟨one_mem L, by rw [Derivation.map_one_eq_zero]; exact zero_mem L⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨add_mem hx.1 hy.1, by rw [map_add]; exact add_mem hx.2 hy.2⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨mul_mem hx.1 hy.1, ?_⟩
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    exact add_mem (mul_mem hx.1 hy.2) (mul_mem hy.1 hx.2)
  algebraMap_mem' := by
    intro c
    exact ⟨algebraMap_mem L c, by rw [Derivation.map_algebraMap]; exact zero_mem L⟩
  inv_mem' := by
    intro x hx
    refine ⟨inv_mem hx.1, ?_⟩
    rw [Derivation.leibniz_inv, smul_eq_mul]
    exact mul_mem (neg_mem (pow_mem (inv_mem hx.1) 2)) hx.2

theorem adjoin_le_derivationStable {L' E : Type*} [Field L'] [Field E] [Algebra L' E]
    {S : Set E} {D : Derivation L' E E}
    (h : ∀ x ∈ S, x ∈ IntermediateField.adjoin L' S ∧ D x ∈ IntermediateField.adjoin L' S) :
    IntermediateField.adjoin L' S ≤ derivationStable (IntermediateField.adjoin L' S) D := by
  rw [IntermediateField.adjoin_le_iff]
  exact fun x hx => h x hx

/-- The Schwarzian coordinate family: the first three jets of the base coordinate together with
every jet of its Schwarzian. -/
def schwarzianCoordinates (C : Type*) [Field C] : Fin 3 ⊕ ℕ → FreeScalarJetField C
  | Sum.inl k => freeCoordinate C ℕ (k : ℕ)
  | Sum.inr k => differentialJet k (freeJetSchwarzian C)

/-- **The Schwarzian coordinate system generates the free scalar jet field.** -/
theorem schwarzianCoordinates_adjoin_eq_top :
    IntermediateField.adjoin C (Set.range (schwarzianCoordinates C)) = ⊤ := by
  classical
  set L := IntermediateField.adjoin C (Set.range (schwarzianCoordinates C)) with hL
  have hmem : ∀ p : Fin 3 ⊕ ℕ, schwarzianCoordinates C p ∈ L := fun p =>
    IntermediateField.subset_adjoin _ _ ⟨p, rfl⟩
  have hclosed : ∀ y ∈ L, freeJetShift C y ∈ L := by
    have hle := adjoin_le_derivationStable (L' := C) (S := Set.range (schwarzianCoordinates C))
      (D := freeJetShift C) ?_
    · exact fun y hy => (hle hy).2
    rintro _ ⟨(k | k), rfl⟩
    · refine ⟨hmem (Sum.inl k), ?_⟩
      fin_cases k
      · show freeJetShift C (freeCoordinate C ℕ 0) ∈ L
        rw [freeJetShift_freeCoordinate]
        exact hmem (Sum.inl 1)
      · show freeJetShift C (freeCoordinate C ℕ 1) ∈ L
        rw [freeJetShift_freeCoordinate]
        exact hmem (Sum.inl 2)
      · show freeJetShift C (freeCoordinate C ℕ 2) ∈ L
        rw [freeJetShift_freeCoordinate, freeCoordinate_three_eq]
        have h3 : (3 : FreeScalarJetField C) ∈ L := by simp
        have h2 : (2 : FreeScalarJetField C) ∈ L := by simp
        exact add_mem (mul_mem (hmem (Sum.inl 1)) (hmem (Sum.inr 0)))
          (div_mem (mul_mem (div_mem h3 h2) (pow_mem (hmem (Sum.inl 2)) 2))
            (hmem (Sum.inl 1)))
    · refine ⟨hmem (Sum.inr k), ?_⟩
      show freeJetShift C (differentialJet k (freeJetSchwarzian C)) ∈ L
      rw [← freeScalarJetField_deriv_apply, ← differentialJet_succ]
      exact hmem (Sum.inr (k + 1))
  have hjet : ∀ m : ℕ, freeCoordinate C ℕ m ∈ L := by
    intro m
    induction m with
    | zero => exact hmem (Sum.inl 0)
    | succ m ih =>
        have h := hclosed _ ih
        rwa [freeJetShift_freeCoordinate] at h
  refine le_antisymm le_top ?_
  rw [← freeCoordinateField_univ (C := C) (σ := ℕ), freeCoordinateField,
    IntermediateField.adjoin_le_iff]
  rintro _ ⟨m, -, rfl⟩
  exact hjet m

end

end GaloisForLFunctions.HTGeometry
