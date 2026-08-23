import GaloisForLFunctions.RHTower.DeningerDynSysOmegaRing
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Ring homomorphisms out of `W_rat (κ)` are characters of `κˣ`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1) and
Corollary 1.7(2).

For an algebraically closed field `K` the comparison `ω : ℤ[Kˣ] ≅ W_rat (K)` turns ring
homomorphisms `W_rat (K) → C` into ring homomorphisms out of the integral monoid algebra, and those
are exactly the multiplicative maps `Kˣ → C`.  Since `Kˣ` is a group, such a map lands in `Cˣ`, so

`Hom (W_rat (K) , C) ≅ Hom (Kˣ , Cˣ)` .

Together with the extension by zero this is Deninger's description of the `C`-valued points of
`W_rat (Spec K)` as the pointed multiplicative maps `K → C`.
-/

namespace RHTower

noncomputable section

open MonoidAlgebra

variable {G : Type*} [Group G] {C : Type*} [CommRing C]

/-- The character of `G` attached to a ring homomorphism out of `ℤ[G]`. -/
def deningerMonoidAlgebraToChar (ψ : MonoidAlgebra ℤ G →+* C) : G →* Cˣ :=
  (ψ.toMonoidHom.comp (MonoidAlgebra.of ℤ G)).toHomUnits

@[simp] theorem deningerMonoidAlgebraToChar_coe (ψ : MonoidAlgebra ℤ G →+* C) (g : G) :
    ((deningerMonoidAlgebraToChar ψ g : Cˣ) : C) = ψ (MonoidAlgebra.single g 1) := rfl

/-- The ring homomorphism out of `ℤ[G]` attached to a character of `G`. -/
def deningerCharToMonoidAlgebra (f : G →* Cˣ) : MonoidAlgebra ℤ G →+* C :=
  liftNCRingHom (Int.castRingHom C) ((Units.coeHom C).comp f) (fun _ _ => Commute.all _ _)

@[simp] theorem deningerCharToMonoidAlgebra_single (f : G →* Cˣ) (g : G) (n : ℤ) :
    deningerCharToMonoidAlgebra f (MonoidAlgebra.single g n) = (n : C) * (f g : C) := by
  rw [deningerCharToMonoidAlgebra, liftNCRingHom_single]
  rfl

/-- Ring homomorphisms out of the integral monoid algebra of a group are exactly the characters of
that group. -/
def deningerMonoidAlgebraRingHomEquiv (G : Type*) [Group G] (C : Type*) [CommRing C] :
    (MonoidAlgebra ℤ G →+* C) ≃ (G →* Cˣ) where
  toFun := deningerMonoidAlgebraToChar
  invFun := deningerCharToMonoidAlgebra
  left_inv ψ := by
    refine MonoidAlgebra.ringHom_ext ?_ ?_
    · intro r
      have h1 : (MonoidAlgebra.single (1 : G) r : MonoidAlgebra ℤ G)
          = r • (1 : MonoidAlgebra ℤ G) := by
        rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
      rw [h1, map_zsmul, map_one, map_zsmul, map_one]
    · intro m
      rw [deningerCharToMonoidAlgebra_single, deningerMonoidAlgebraToChar_coe]
      simp
  right_inv f := by
    ext g
    rw [deningerMonoidAlgebraToChar_coe, deningerCharToMonoidAlgebra_single]
    simp

/-- Precomposition with a ring isomorphism is a bijection on hom-sets. -/
def deningerPrecompRingHomEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S)
    (C : Type*) [CommRing C] : (S →+* C) ≃ (R →+* C) where
  toFun φ := φ.comp e.toRingHom
  invFun ψ := ψ.comp e.symm.toRingHom
  left_inv φ := by
    refine RingHom.ext fun x => ?_
    show φ (e (e.symm x)) = φ x
    rw [e.apply_symm_apply]
  right_inv ψ := by
    refine RingHom.ext fun x => ?_
    show ψ (e.symm (e x)) = ψ x
    rw [e.symm_apply_apply]

/-- **Deninger, Corollary 1.5(1) / 1.7(2), the algebraic core.**  Over an algebraically closed
field the ring homomorphisms out of `W_rat (K)` are exactly the characters of `Kˣ`. -/
def deningerWittRingHomEquivChar (K : Type*) [Field K] [IsAlgClosed K] (C : Type*) [CommRing C] :
    (DeningerCanonicalRationalWittRing K →+* C) ≃ (Kˣ →* Cˣ) :=
  (deningerPrecompRingHomEquiv (deningerOmegaRingEquiv K) C).trans
    (deningerMonoidAlgebraRingHomEquiv Kˣ C)

@[simp] theorem deningerWittRingHomEquivChar_apply (K : Type*) [Field K] [IsAlgClosed K]
    (C : Type*) [CommRing C] (φ : DeningerCanonicalRationalWittRing K →+* C) (a : Kˣ) :
    ((deningerWittRingHomEquivChar K C φ a : Cˣ) : C)
      = φ (deningerCanonicalRationalWittTeichmuller (a : K)) := by
  show ((deningerMonoidAlgebraToChar (φ.comp (deningerOmegaRingEquiv K).toRingHom) a : Cˣ) : C) = _
  rw [deningerMonoidAlgebraToChar_coe]
  show φ (deningerOmegaRingEquiv K (MonoidAlgebra.single a 1)) = _
  rw [deningerOmegaRingEquiv_single, one_smul]

end

end RHTower
