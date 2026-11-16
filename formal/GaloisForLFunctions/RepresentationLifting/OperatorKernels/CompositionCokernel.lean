import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Operator quotients detected on kernels

Restriction to `ker T` identifies `Hom(V,W) / (Hom(U,W) ∘ T)` with
`Hom(ker T,W)`. Thus the quotient has dimension `dim W * dim ker T`.
This is the linear-algebra mechanism in Proposition 3.29 of Zehavi,
*The Chabauty–Kim dimension inequality via noncommutative Iwasawa theory*,
arXiv:2611.18218, valid here for arbitrary linear maps over a field.
-/

noncomputable section

namespace GaloisForLFunctions.RepresentationLifting.OperatorKernels

variable {K V U W : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U]
  [AddCommGroup W] [Module K W]

/-- Precomposition by an operator, with an arbitrary observation space. -/
def precompose (T : V →ₗ[K] U) : (U →ₗ[K] W) →ₗ[K] (V →ₗ[K] W) where
  toFun f := f.comp T
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Restriction of observations to the invisible vectors of an operator. -/
def restrictKernel (T : V →ₗ[K] U) : (V →ₗ[K] W) →ₗ[K] (T.ker →ₗ[K] W) where
  toFun f := f.comp T.ker.subtype
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every observation on the kernel extends to the ambient vector space. -/
theorem restrictKernel_surjective (T : V →ₗ[K] U) :
    Function.Surjective (restrictKernel (W := W) T) := by
  intro f
  exact f.exists_extend

/-- An observation factors through an operator exactly when it vanishes on its kernel. -/
theorem range_precompose (T : V →ₗ[K] U) :
    (precompose (W := W) T).range = (restrictKernel (W := W) T).ker := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    apply LinearMap.ext
    intro v
    change g (T v.val) = 0
    rw [v.property, map_zero]
  · intro hf
    have hs : Function.Surjective T.rangeRestrict := by
      rintro ⟨y, x, rfl⟩
      exact ⟨x, rfl⟩
    obtain ⟨s, hs⟩ := T.rangeRestrict.exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr hs)
    obtain ⟨g, hg⟩ := (f.comp s).exists_extend
    refine ⟨g, LinearMap.ext fun x => ?_⟩
    have hx : T (s (T.rangeRestrict x)) = T x :=
      congrArg Subtype.val (LinearMap.congr_fun hs (T.rangeRestrict x))
    have hz : s (T.rangeRestrict x) - x ∈ T.ker := by
      change T (s (T.rangeRestrict x) - x) = 0
      rw [map_sub, hx, sub_self]
    have hfz : f (s (T.rangeRestrict x) - x) = 0 :=
      LinearMap.congr_fun hf ⟨_, hz⟩
    change g (T x) = f x
    have hgx := LinearMap.congr_fun hg (T.rangeRestrict x)
    change g (T x) = f (s (T.rangeRestrict x)) at hgx
    exact hgx.trans (sub_eq_zero.mp ((map_sub f _ _).symm.trans hfz))

/-- The full quotient equivalence, retaining more information than its dimension. -/
def compositionCokernelEquiv (T : V →ₗ[K] U) :
    ((V →ₗ[K] W) ⧸ (precompose (W := W) T).range) ≃ₗ[K] (T.ker →ₗ[K] W) :=
  (Submodule.quotEquivOfEq _ _ (range_precompose T)).trans
    ((restrictKernel T).quotKerEquivOfSurjective (restrictKernel_surjective T))

/-- Each invisible input direction leaves one independent copy of the observation space. -/
theorem finrank_compositionCokernel [FiniteDimensional K V] [FiniteDimensional K W]
    (T : V →ₗ[K] U) :
    Module.finrank K ((V →ₗ[K] W) ⧸ (precompose (W := W) T).range) =
      Module.finrank K W * Module.finrank K T.ker := by
  rw [(compositionCokernelEquiv (W := W) T).finrank_eq, Module.finrank_linearMap]
  exact Nat.mul_comm _ _

/-- The endomorphism version used to amplify a kernel into a left-ideal quotient. -/
theorem finrank_endomorphism_quotient [FiniteDimensional K V] (T : Module.End K V) :
    Module.finrank K (Module.End K V ⧸ (precompose (W := V) T).range) =
      Module.finrank K V * Module.finrank K T.ker :=
  finrank_compositionCokernel T

end GaloisForLFunctions.RepresentationLifting.OperatorKernels

#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.compositionCokernelEquiv
#print axioms GaloisForLFunctions.RepresentationLifting.OperatorKernels.finrank_endomorphism_quotient
