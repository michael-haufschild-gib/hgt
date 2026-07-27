import Mathlib.Algebra.Exact
import Mathlib.LinearAlgebra.Finsupp.Defs

/-!
# Cofinite divisor splitting for Deninger arithmetic cohomology

For a set `S` of retained prime coordinates, the generic finitely supported
divisor module splits into coordinates inside and outside `S`.  Restriction
to the outside coordinates is surjective, extension from the inside
coordinates is injective, and the resulting sequence is exact.

After unique factorization identifies positive rational numbers with
finitely supported integral prime valuations, this is the algebraic core of
the divisor sequence on `Spec ℤ[S⁻¹]`.  It is independent of zeta zeros, RH,
numerical computation, and any quotient-stack comparison.
-/

namespace RHTower

universe u v

section CofiniteDivisorSplitting

variable {R : Type u} {ι : Type v} [CommRing R]
variable (S : ι → Prop)

/-- Prime coordinates retained by the cofinite open. -/
abbrev DeningerInsidePrime := {i : ι // S i}

/-- Prime coordinates occurring as residues on the cofinite open. -/
abbrev DeningerOutsidePrime := {i : ι // ¬ S i}

/-- Extension by zero from retained prime coordinates to all prime
coordinates. -/
noncomputable def deningerInsideDivisorEmbedding :
    (DeningerInsidePrime S →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.lmapDomain R R
    ((↑) : DeningerInsidePrime S → ι)

/-- Restriction of a generic divisor to residue coordinates outside the
retained set. -/
noncomputable def deningerOutsideResidue :
    (ι →₀ R) →ₗ[R] (DeningerOutsidePrime S →₀ R) :=
  Finsupp.lcomapDomain
    ((↑) : DeningerOutsidePrime S → ι) Subtype.val_injective

/-- Extension by zero gives a canonical section of the outside-residue
map. -/
noncomputable def deningerOutsideResidueSection :
    (DeningerOutsidePrime S →₀ R) →ₗ[R] (ι →₀ R) :=
  Finsupp.lmapDomain R R
    ((↑) : DeningerOutsidePrime S → ι)

@[simp]
theorem deningerOutsideResidue_section
    (x : DeningerOutsidePrime S →₀ R) :
    deningerOutsideResidue (R := R) S
        (deningerOutsideResidueSection (R := R) S x) = x := by
  exact Finsupp.leftInverse_lcomapDomain_mapDomain
    (R := R) (M := R)
    ((↑) : DeningerOutsidePrime S → ι) Subtype.val_injective x

/-- Every finitely supported outside residue profile has a generic divisor
lift, by extension by zero. -/
theorem deningerOutsideResidue_surjective :
    Function.Surjective (deningerOutsideResidue (R := R) S) := by
  intro x
  exact ⟨deningerOutsideResidueSection (R := R) S x,
    deningerOutsideResidue_section (R := R) S x⟩

/-- Extension by zero from the retained coordinates is injective. -/
theorem deningerInsideDivisorEmbedding_injective :
    Function.Injective (deningerInsideDivisorEmbedding (R := R) S) := by
  intro x y h
  ext i
  have hi := congrArg (fun z : ι →₀ R => z i.1) h
  simpa [deningerInsideDivisorEmbedding, Finsupp.lmapDomain_apply,
    Finsupp.mapDomain_apply Subtype.val_injective] using hi

/-- The kernel of restriction to outside residues consists exactly of
divisors supported on the retained prime coordinates. -/
theorem deningerCofiniteDivisor_exact :
    Function.Exact
      (deningerInsideDivisorEmbedding (R := R) S)
      (deningerOutsideResidue (R := R) S) := by
  rw [LinearMap.exact_iff]
  ext x
  constructor
  · intro hx
    let y : DeningerInsidePrime S →₀ R :=
      Finsupp.lcomapDomain (R := R) (M := R)
        ((↑) : DeningerInsidePrime S → ι) Subtype.val_injective x
    refine ⟨y, ?_⟩
    ext i
    by_cases hi : S i
    · change
        Finsupp.mapDomain
            ((↑) : DeningerInsidePrime S → ι) y
            ((⟨i, hi⟩ : DeningerInsidePrime S) : ι) =
          x i
      rw [Finsupp.mapDomain_apply Subtype.val_injective]
      simp [y, Finsupp.lcomapDomain_apply]
    · have hxi : x i = 0 := by
        have h := congrArg
          (fun z : DeningerOutsidePrime S →₀ R => z ⟨i, hi⟩) hx
        simpa [deningerOutsideResidue,
          Finsupp.lcomapDomain_apply] using h
      rw [hxi]
      simp [deningerInsideDivisorEmbedding, Finsupp.lmapDomain_apply,
        Finsupp.mapDomain_notin_range, hi]
  · rintro ⟨y, rfl⟩
    ext i
    simp [deningerInsideDivisorEmbedding, deningerOutsideResidue,
      Finsupp.lmapDomain_apply, Finsupp.lcomapDomain_apply,
      Finsupp.mapDomain_notin_range, i.property]

/-- Consecutive maps in the cofinite divisor resolution compose to zero. -/
theorem deningerOutsideResidue_comp_insideDivisorEmbedding :
    (deningerOutsideResidue (R := R) S).comp
        (deningerInsideDivisorEmbedding (R := R) S) = 0 := by
  apply LinearMap.ext
  intro x
  exact (deningerCofiniteDivisor_exact (R := R) S).apply_apply_eq_zero x

end CofiniteDivisorSplitting

end RHTower
