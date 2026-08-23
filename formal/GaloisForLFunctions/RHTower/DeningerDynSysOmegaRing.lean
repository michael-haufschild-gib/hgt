import GaloisForLFunctions.RHTower.DeningerRationalWittAlgebraicallyClosedPresentation
import GaloisForLFunctions.RHTower.DeningerRationalWittLocalization

/-!
# The comparison `ω : ℤ̲κ ≅ W_rat(κ)` as a ring isomorphism

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.1(b).

Over an algebraically closed field `K` the additive comparison `ℤ[Kˣ] → W_rat (K)` sending the
generator `(a)` to the Teichmüller element `[a]` is bijective.  It is moreover multiplicative:
both sides are biadditive, so it suffices to compare them on generators, where `(a) · (b) = (a b)`
matches `[a] ⊙ [b] = [a b]`.

This gives Deninger's `ω` as an isomorphism of rings onto the canonical rational Witt ring, the
form needed to describe `Hom (W_rat (κ) , C)` by pointed multiplicative maps.
-/

namespace RHTower

noncomputable section

variable {A : Type*} [CommRing A]

/-- The underlying literal rational function of a canonical rational Witt vector, as an additive
homomorphism. -/
def deningerCanonicalRationalWittValAddHom (A : Type*) [CommRing A] :
    DeningerCanonicalRationalWittRing A →+ Additive (DeningerRationalWittAdditive A) where
  toFun := DeningerCanonicalRationalWittRing.additiveVal
  map_zero' := by
    have h := deningerCanonicalRationalWittRing_additiveVal_add
      (0 : DeningerCanonicalRationalWittRing A) 0
    rw [add_zero] at h
    refine add_left_cancel (a := (0 : DeningerCanonicalRationalWittRing A).additiveVal) ?_
    rw [add_zero]
    exact h.symm
  map_add' := deningerCanonicalRationalWittRing_additiveVal_add

@[simp] theorem deningerCanonicalRationalWittRing_additiveVal_zsmul (n : ℤ)
    (w : DeningerCanonicalRationalWittRing A) :
    (n • w).additiveVal = n • w.additiveVal :=
  map_zsmul (deningerCanonicalRationalWittValAddHom A) n w

variable (K : Type*) [Field K] [IsAlgClosed K]

/-- The additive comparison `ℤ[Kˣ] → W_rat (K)` landing in the canonical rational Witt ring. -/
def deningerOmegaAddHom :
    MonoidAlgebra ℤ Kˣ →+ DeningerCanonicalRationalWittRing K where
  toFun x := ⟨deningerRationalWittReducedMonoidAlgebraToAdditive K x⟩
  map_zero' := by
    apply DeningerCanonicalRationalWittRing.ext
    rw [map_zero]
    exact ((deningerCanonicalRationalWittValAddHom K).map_zero).symm
  map_add' x y := by
    apply DeningerCanonicalRationalWittRing.ext
    rw [deningerCanonicalRationalWittRing_additiveVal_add]
    exact map_add (deningerRationalWittReducedMonoidAlgebraToAdditive K) x y

variable {K}

omit [IsAlgClosed K] in
@[simp] theorem deningerOmegaAddHom_apply (x : MonoidAlgebra ℤ Kˣ) :
    (deningerOmegaAddHom K x).additiveVal
      = deningerRationalWittReducedMonoidAlgebraToAdditive K x := rfl

omit [IsAlgClosed K] in
@[simp] theorem deningerOmegaAddHom_single (a : Kˣ) (n : ℤ) :
    deningerOmegaAddHom K (MonoidAlgebra.single a n)
      = n • deningerCanonicalRationalWittTeichmuller (a : K) := by
  apply DeningerCanonicalRationalWittRing.ext
  rw [deningerOmegaAddHom_apply, deningerRationalWittReducedMonoidAlgebraToAdditive_single,
    deningerCanonicalRationalWittRing_additiveVal_zsmul]
  rfl

omit [IsAlgClosed K] in
theorem deningerOmegaAddHom_mul (x y : MonoidAlgebra ℤ Kˣ) :
    deningerOmegaAddHom K (x * y) = deningerOmegaAddHom K x * deningerOmegaAddHom K y := by
  classical
  have key : ∀ (b : Kˣ) (n : ℤ) (z : MonoidAlgebra ℤ Kˣ),
      deningerOmegaAddHom K (z * MonoidAlgebra.single b n)
        = deningerOmegaAddHom K z * deningerOmegaAddHom K (MonoidAlgebra.single b n) := by
    intro b n
    have h1 : ((deningerOmegaAddHom K).comp
          (AddMonoidHom.mulRight (MonoidAlgebra.single b n)))
        = (AddMonoidHom.mulRight (deningerOmegaAddHom K (MonoidAlgebra.single b n))).comp
          (deningerOmegaAddHom K) := by
      refine MonoidAlgebra.addMonoidHom_ext ?_
      intro a m
      show deningerOmegaAddHom K (MonoidAlgebra.single a m * MonoidAlgebra.single b n)
        = deningerOmegaAddHom K (MonoidAlgebra.single a m) *
          deningerOmegaAddHom K (MonoidAlgebra.single b n)
      rw [MonoidAlgebra.single_mul_single, deningerOmegaAddHom_single,
        deningerOmegaAddHom_single, deningerOmegaAddHom_single, smul_mul_smul_comm,
        deningerCanonicalRationalWittTeichmuller_mul, Units.val_mul]
    intro z
    exact congrArg (fun F : MonoidAlgebra ℤ Kˣ →+ DeningerCanonicalRationalWittRing K => F z) h1
  have h2 : ((deningerOmegaAddHom K).comp (AddMonoidHom.mulLeft x))
      = (AddMonoidHom.mulLeft (deningerOmegaAddHom K x)).comp (deningerOmegaAddHom K) := by
    refine MonoidAlgebra.addMonoidHom_ext ?_
    intro b n
    exact key b n x
  exact congrArg (fun F : MonoidAlgebra ℤ Kˣ →+ DeningerCanonicalRationalWittRing K => F y) h2

variable (K)

/-- **Deninger, Proposition 1.1(b).**  Over an algebraically closed field the comparison
`ω : ℤ̲κ → W_rat (κ)` is a ring isomorphism. -/
def deningerOmegaRingEquiv :
    MonoidAlgebra ℤ Kˣ ≃+* DeningerCanonicalRationalWittRing K where
  toFun := deningerOmegaAddHom K
  invFun w := (deningerRationalWittReducedMonoidAlgebraAddEquiv K).symm w.additiveVal
  left_inv x := (deningerRationalWittReducedMonoidAlgebraAddEquiv K).symm_apply_apply x
  right_inv w := by
    apply DeningerCanonicalRationalWittRing.ext
    exact (deningerRationalWittReducedMonoidAlgebraAddEquiv K).apply_symm_apply w.additiveVal
  map_add' := map_add (deningerOmegaAddHom K)
  map_mul' := deningerOmegaAddHom_mul

variable {K}

@[simp] theorem deningerOmegaRingEquiv_single (a : Kˣ) (n : ℤ) :
    deningerOmegaRingEquiv K (MonoidAlgebra.single a n)
      = n • deningerCanonicalRationalWittTeichmuller (a : K) :=
  deningerOmegaAddHom_single a n

end

end RHTower
