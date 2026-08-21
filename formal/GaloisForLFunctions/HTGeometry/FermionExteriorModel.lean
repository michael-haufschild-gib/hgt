import GaloisForLFunctions.HTGeometry.FermionWickTheorem
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# The exterior-algebra model of a fermionic system

The Clifford algebra of the zero quadratic form — the exterior algebra of `M` — is the fermionic
Fock space: `1` is the vacuum, left multiplication by `ι (v i)` creates a quantum in mode `i`, and
the contraction `contractLeft (d i)` by a linear functional destroys one.  Mathlib's

```text
contractLeft d (ι a * x) = d a • x - ι a * contractLeft d x
```

is exactly the canonical anticommutation relation, with elementary contraction `d i (v j)`, and the
scalar part of `T 1` is a vacuum expectation.

This realises `FermionSystem` and `FermionVacuum` for an arbitrary family of vectors and dual
vectors, so the fermionic Wick theorem specialises to: the scalar part of an ordered product of the
operators `ι (v i) · + contractLeft (d i)` applied to the vacuum is the Pfaffian of the matrix
`d i (v j)`.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

open CliffordAlgebra

variable (K : Type u) [CommRing K] (M : Type v) [AddCommGroup M] [Module K M]
variable {σ : Type w}

/-- The fermionic Fock space: the Clifford algebra of the zero form on `M`. -/
abbrev FermiFock : Type max u v := CliffordAlgebra (0 : QuadraticForm K M)

/-- **The exterior-algebra fermionic system.**  Creation is multiplication by a vector, annihilation
is contraction by a dual vector, and the elementary contraction is their pairing. -/
noncomputable def exteriorFermion (v : σ → M) (d : σ → Module.Dual K M) :
    FermionSystem K (Module.End K (FermiFock K M)) σ where
  cre i := LinearMap.mulLeft K (ι (0 : QuadraticForm K M) (v i))
  ann i := contractLeft (Q := (0 : QuadraticForm K M)) (d i)
  κ i j := d i (v j)
  cre_mul_cre i j := by
    refine LinearMap.ext fun x => ?_
    have hp : QuadraticMap.polar (0 : QuadraticForm K M) (v i) (v j) = 0 := by
      simp [QuadraticMap.polar]
    have h := ι_mul_ι_add_swap (Q := (0 : QuadraticForm K M)) (v i) (v j)
    rw [hp, map_zero] at h
    have hc : ι (0 : QuadraticForm K M) (v i) * ι (0 : QuadraticForm K M) (v j)
        = -(ι (0 : QuadraticForm K M) (v j) * ι (0 : QuadraticForm K M) (v i)) :=
      eq_neg_of_add_eq_zero_left h
    simp only [Module.End.mul_apply, LinearMap.neg_apply, LinearMap.mulLeft_apply]
    rw [← mul_assoc, hc, neg_mul, mul_assoc]
  ann_mul_ann i j := by
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, LinearMap.neg_apply]
    exact contractLeft_comm _ _ x
  ann_mul_cre i j := by
    refine LinearMap.ext fun x => ?_
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.neg_apply,
      LinearMap.smul_apply, Module.End.one_apply, LinearMap.mulLeft_apply]
    rw [contractLeft_ι_mul]
    abel

/-- The scalar part of a multivector: the algebra map killing every vector. -/
noncomputable def fermiScalarPart : FermiFock K M →ₐ[K] K :=
  CliffordAlgebra.lift _ ⟨0, by simp⟩

@[simp] theorem fermiScalarPart_ι (m : M) :
    fermiScalarPart K M (ι (0 : QuadraticForm K M) m) = 0 := by
  rw [fermiScalarPart, CliffordAlgebra.lift_ι_apply]
  simp

/-- The vacuum expectation on the fermionic Fock space: the scalar part of the image of `1`. -/
noncomputable def fermiVacuumFunctional : Module.End K (FermiFock K M) →ₗ[K] K where
  toFun T := fermiScalarPart K M (T 1)
  map_add' T S := by simp
  map_smul' c T := by simp

@[simp] theorem fermiVacuumFunctional_apply (T : Module.End K (FermiFock K M)) :
    fermiVacuumFunctional K M T = fermiScalarPart K M (T 1) := rfl

/-- **The Fock vacuum of the exterior model.** -/
noncomputable def exteriorFermionVacuum (v : σ → M) (d : σ → Module.Dual K M) :
    FermionVacuum (exteriorFermion K M v d) where
  ω := fermiVacuumFunctional K M
  ω_one := by simp
  ω_cre i x := by
    simp only [fermiVacuumFunctional_apply, Module.End.mul_apply]
    show fermiScalarPart K M (ι (0 : QuadraticForm K M) (v i) * x 1) = 0
    rw [map_mul, fermiScalarPart_ι, zero_mul]
  ω_ann i x := by
    simp only [fermiVacuumFunctional_apply, Module.End.mul_apply]
    show fermiScalarPart K M (x (contractLeft (Q := (0 : QuadraticForm K M)) (d i) 1)) = 0
    rw [contractLeft_one, map_zero, map_zero]

/-- **Wick's theorem for the exterior-algebra fermion.**  The scalar part of an ordered product of
the fermionic fields `ι (v i) · + contractLeft (d i)`, applied to the vacuum, is the Pfaffian of the
pairing matrix `d i (v j)`. -/
theorem exteriorFermion_vacuum_prod_field (v : σ → M) (d : σ → Module.Dual K M) (l : List σ) :
    fermiScalarPart K M ((l.map (exteriorFermion K M v d).field).prod (1 : FermiFock K M))
      = pfaffianPairing K (fun i j => d i (v j)) l :=
  (exteriorFermionVacuum K M v d).vacuum_prod_field l

end GaloisForLFunctions.HTGeometry
