import GaloisForLFunctions.HTGeometry.ABHN.HasseLinearMapEquality

namespace GaloisForLFunctions.HTGeometry.ABHN

open scoped TensorProduct

universe u v w x

noncomputable def algHomBaseChange {K : Type u} {L : Type v} {A : Type w} {B : Type x}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f : A →ₐ[K] B) : L ⊗[K] A →ₐ[L] L ⊗[K] B :=
  Algebra.TensorProduct.map (AlgHom.id L L) f

theorem algHom_eq_iff_baseChange_eq {K : Type u} {L : Type v} {A : Type w} {B : Type x}
    [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f g : A →ₐ[K] B) :
    f = g ↔ algHomBaseChange (L := L) f = algHomBaseChange (L := L) g := by
  constructor
  · intro h
    exact congrArg (algHomBaseChange (L := L)) h
  · intro h
    ext a
    apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := K) (B := L) B
    have happly := DFunLike.congr_fun h ((1 : L) ⊗ₜ[K] a)
    change (1 : L) ⊗ₜ[K] f a = 1 ⊗ₜ[K] g a at happly
    exact happly

theorem numberField_algHom_eq_iff_forall_place (K : Type u)
    [Field K] [NumberField K] {A : Type v} {B : Type w}
    [Ring A] [Algebra K A] [Ring B] [Algebra K B]
    (f g : A →ₐ[K] B) :
    f = g ↔ ∀ p : NumberFieldPlace K,
      algHomBaseChange (L := completion K p) f = algHomBaseChange (L := completion K p) g := by
  constructor
  · intro h p
    exact (algHom_eq_iff_baseChange_eq (L := completion K p) f g).mp h
  · intro h
    exact (algHom_eq_iff_baseChange_eq
      (L := completion K (witnessPlace K)) f g).mpr (h (witnessPlace K))

theorem rationalFunction_algHom_eq_iff_forall_place (F : Type u)
    [Field F] [Finite F] {A : Type v} {B : Type w}
    [Ring A] [Algebra (RatFunc F) A] [Ring B] [Algebra (RatFunc F) B]
    (f g : A →ₐ[RatFunc F] B) :
    f = g ↔ ∀ p : RationalFunctionPlace F,
      algHomBaseChange (L := rationalFunctionCompletion F p) f =
        algHomBaseChange (L := rationalFunctionCompletion F p) g := by
  constructor
  · intro h p
    exact (algHom_eq_iff_baseChange_eq (L := rationalFunctionCompletion F p) f g).mp h
  · intro h
    exact (algHom_eq_iff_baseChange_eq
      (L := rationalFunctionCompletion F .infinite) f g).mpr (h .infinite)

end GaloisForLFunctions.HTGeometry.ABHN
