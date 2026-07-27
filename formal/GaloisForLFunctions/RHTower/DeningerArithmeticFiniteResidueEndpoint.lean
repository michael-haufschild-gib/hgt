import GaloisForLFunctions.RHTower.DeningerArithmeticThreeTermCohomology

/-!
# Finite-residue endpoint for Deninger arithmetic cohomology

Given a linear equivalence from finite units to finite residue
coordinates, the associated three-term arithmetic complex has
`H⁰ = constants`, trivial `H¹`, and `H² = orientation`.

This is the unconditional algebraic core of the finite-prime
Milnor--Arakelov endpoint page.  No arithmetic comparison conjecture,
zeta-zero data, Riemann-hypothesis premise, or numerical computation
enters.
-/

namespace RHTower

universe u

section FiniteResidueEndpoint

variable {R Units Residues Orientation : Type u}
variable [CommRing R]
variable [AddCommGroup Units] [Module R Units]
variable [AddCommGroup Residues] [Module R Residues]
variable [AddCommGroup Orientation] [Module R Orientation]

/-- Three-term endpoint complex associated with an invertible residue
coordinate map. -/
def deningerFiniteResidueEndpointComplex
    (residue : Units ≃ₗ[R] Residues) :
    DeningerArithmeticThreeTermComplex R R Units
      (Residues × Orientation) where
  d0 := 0
  d1 :=
    { toFun := fun u => (residue u, 0)
      map_add' := by
        intro x y
        simp
      map_smul' := by
        intro c x
        simp }
  d1_comp_d0 := by
    apply LinearMap.ext
    intro x
    apply Prod.ext <;> simp

namespace deningerFiniteResidueEndpointComplex

variable (residue : Units ≃ₗ[R] Residues)

private abbrev C :
    DeningerArithmeticThreeTermComplex R R Units
      (Residues × Orientation) :=
  deningerFiniteResidueEndpointComplex residue

/-- Degree zero is canonically the constant line. -/
def H0Equiv :
    (C (Orientation := Orientation) residue).H0 ≃ₗ[R] R where
  toFun x := x.1
  invFun x := ⟨x, by
    change (0 : R →ₗ[R] Units) x = 0
    rfl⟩
  left_inv x := rfl
  right_inv x := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every middle cohomology class vanishes because the residue
coordinate map is injective. -/
theorem H1_eq_zero
    (x : (C (Orientation := Orientation) residue).H1) :
    x = 0 := by
  obtain ⟨x, rfl⟩ :=
    Submodule.Quotient.mk_surjective
      ((C (Orientation := Orientation) residue).boundaries1.comap
        (C (Orientation := Orientation) residue).cycles1.subtype) x
  apply
    ((C (Orientation := Orientation) residue).H1_mk_eq_zero_iff x).2
  have hxPair :
      ((residue (x : Units), 0) : Residues × Orientation) = 0 :=
    x.property
  have hxResidue : residue (x : Units) = 0 := by
    simpa using congrArg Prod.fst hxPair
  have hx : (x : Units) = 0 := residue.injective (by simpa using hxResidue)
  rw [hx]
  exact Submodule.zero_mem _

/-- Projection onto the real-orientation factor. -/
def orientationProjection :
    (Residues × Orientation) →ₗ[R] Orientation where
  toFun x := x.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The finite residue differential followed by orientation projection
is exact. -/
theorem exact_d1_orientationProjection :
    Function.Exact
      (C (Orientation := Orientation) residue).d1
      (orientationProjection
        (R := R) (Residues := Residues)
        (Orientation := Orientation)) := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    change x.2 = 0 at hx
    refine ⟨residue.symm x.1, ?_⟩
    ext
    · simp [C, deningerFiniteResidueEndpointComplex]
    · simpa [C, deningerFiniteResidueEndpointComplex] using hx.symm
  · rintro ⟨u, rfl⟩
    simp [orientationProjection, C, deningerFiniteResidueEndpointComplex]

/-- Orientation projection is surjective. -/
theorem orientationProjection_surjective :
    Function.Surjective
      (orientationProjection :
        (Residues × Orientation) →ₗ[R] Orientation) := by
  intro x
  exact ⟨(0, x), rfl⟩

/-- Degree two is canonically the single orientation line. -/
noncomputable def H2Equiv :
    (C (Orientation := Orientation) residue).H2 ≃ₗ[R] Orientation :=
  (exact_d1_orientationProjection residue).linearEquivOfSurjective
    (orientationProjection_surjective
      (R := R) (Residues := Residues)
      (Orientation := Orientation))

end deningerFiniteResidueEndpointComplex

end FiniteResidueEndpoint

end RHTower
