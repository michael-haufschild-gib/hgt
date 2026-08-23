import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.KrullTopology

/-!
# Compactness of the automorphism group of a normal algebraic extension

For a normal algebraic extension `E / F` the restriction map to the separable closure is a group
isomorphism onto `Gal (F^sep / F)`: it is surjective because `E / F` is normal, and injective
because `E / F^sep` is purely inseparable, so an automorphism fixing `F^sep` satisfies
`σ (a) ^ {q^n} = a ^ {q^n}` and hence `σ (a) = a`.  The inverse is continuous — a finite
subextension of `E` is fixed as soon as finitely many `q^n`-th powers in `F^sep` are — so the
automorphism group is the continuous image of a compact group, hence compact.  This removes the
`IsGalois` hypothesis from mathlib's compactness instance.
-/

namespace HTGeometry

open IntermediateField AlgEquiv

universe u

theorem expChar_of_algebra (F : Type u) [Field F] {E : Type u} [Field E] [Algebra F E]
    (q : ℕ) [ExpChar F q] : ExpChar E q :=
  expChar_of_injective_algebraMap (algebraMap F E).injective q

variable {F E : Type u} [Field F] [Field E] [Algebra F E] [Normal F E]

/-- An automorphism fixing the separable closure pointwise is the identity. -/
theorem algEquiv_eq_one_of_fixes_separableClosure (q : ℕ) [ExpChar F q] (σ : E ≃ₐ[F] E)
    (h : ∀ a : ↥(separableClosure F E), σ (a : E) = (a : E)) : σ = 1 := by
  haveI := expChar_of_algebra F (E := E) q
  haveI : ExpChar ↥(separableClosure F E) q :=
    expChar_of_algebra F (E := ↥(separableClosure F E)) q
  refine AlgEquiv.ext fun a => ?_
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem ↥(separableClosure F E) q a
  have hfix : σ (a ^ q ^ n) = a ^ q ^ n := by
    rw [← hb]
    exact h b
  rw [map_pow] at hfix
  have hinj : Function.Injective (iterateFrobenius E q n) :=
    (iterateFrobenius E q n).injective
  refine hinj ?_
  rw [iterateFrobenius_def, iterateFrobenius_def]
  simpa using hfix

/-- Restriction to the separable closure is injective on automorphisms. -/
theorem restrictNormalHom_separableClosure_injective (q : ℕ) [ExpChar F q] :
    Function.Injective
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := E) ↥(separableClosure F E)) := by
  refine (injective_iff_map_eq_one _).2 fun σ hσ => ?_
  refine algEquiv_eq_one_of_fixes_separableClosure q σ fun a => ?_
  have h := congrArg (fun τ : ↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E) => τ a) hσ
  have hres : (AlgEquiv.restrictNormalHom (F := F) (K₁ := E)
      ↥(separableClosure F E) σ) a = a := h
  have hcomm := AlgEquiv.restrictNormal_commutes σ ↥(separableClosure F E) a
  have hres' : σ.restrictNormal ↥(separableClosure F E) a = a := hres
  rw [hres'] at hcomm
  exact hcomm.symm

/-- Restriction to the separable closure is a group isomorphism. -/
noncomputable def restrictNormalMulEquiv (q : ℕ) [ExpChar F q] :
    (E ≃ₐ[F] E) ≃* (↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E)) :=
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom ↥(separableClosure F E))
    ⟨restrictNormalHom_separableClosure_injective q,
      AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := ↥(separableClosure F E)) (E := E)⟩

end HTGeometry
