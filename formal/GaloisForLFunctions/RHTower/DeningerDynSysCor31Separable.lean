import GaloisForLFunctions.RHTower.DeningerDynSysCor31
import GaloisForLFunctions.RHTower.DeningerDynSysTwistedNorm
import GaloisForLFunctions.HTGeometry.RadicialCharacterExtension
import GaloisForLFunctions.HTGeometry.AlgebraicClosureGaloisCompact

/-!
# Corollary 3.1 (25): the separable description

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 3.1, the
bijection (25)

`Hom (W_rat (κ (x₀)) , C) ≅ Hom ((κ (x₀)^sep)ˣ , Cˣ) / G_x` .

An algebraic closure is purely inseparable over the separable closure, and on the units of an
algebraically closed field of the same exponential characteristic the `q`-th power map is
bijective; so restriction of characters to the separable closure is a bijection, and it is
equivariant for the Galois action because restriction of automorphisms commutes with the
inclusion.
-/

namespace RHTower

open MonoidAlgebra

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The inclusion of the units of the separable closure into the units of `E`. -/
def deningerSepUnits : (↥(separableClosure F E))ˣ →* Eˣ :=
  Units.map ((algebraMap ↥(separableClosure F E) E : _ →+* _) : _ →* E)

theorem deningerSepUnits_val (a : (↥(separableClosure F E))ˣ) :
    ((deningerSepUnits (F := F) (E := E) a : Eˣ) : E) = (a : ↥(separableClosure F E)) := rfl

theorem deningerSepUnits_injective :
    Function.Injective (deningerSepUnits (F := F) (E := E)) := by
  intro a b hab
  refine Units.ext ?_
  have h := congrArg (fun u : Eˣ => (u : E)) hab
  rw [deningerSepUnits_val, deningerSepUnits_val] at h
  exact (algebraMap ↥(separableClosure F E) E).injective h

variable {C : Type*} [Field C] [IsAlgClosure F E]

/-- Restriction to the separable closure is equivariant for the Galois action. -/
theorem deningerSepCharRestrict_comp (f : Eˣ →* Cˣ) (σ : E ≃ₐ[F] E) :
    (f.comp (Units.map ((σ : E →+* E) : E →* E))).comp (deningerSepUnits (F := F) (E := E))
      = (f.comp (deningerSepUnits (F := F) (E := E))).comp
        (Units.map ((σ.restrictNormal ↥(separableClosure F E) :
          ↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E)) :
          ↥(separableClosure F E) →* ↥(separableClosure F E))) := by
  refine MonoidHom.ext fun a => ?_
  show f (Units.map ((σ : E →+* E) : E →* E) (deningerSepUnits a))
    = f (deningerSepUnits (Units.map _ a))
  congr 1
  refine Units.ext ?_
  show σ ((deningerSepUnits (F := F) (E := E) a : Eˣ) : E)
    = ((deningerSepUnits (F := F) (E := E) (Units.map _ a) : Eˣ) : E)
  rw [deningerSepUnits_val, deningerSepUnits_val]
  exact (AlgEquiv.restrictNormal_commutes σ ↥(separableClosure F E) (a : _)).symm

variable (q : ℕ) [ExpChar F q] [Algebra.IsAlgebraic F E]

omit [IsAlgClosure F E] in
include q in
theorem deningerSepUnits_pow_mem (y : Eˣ) :
    ∃ (n : ℕ) (a : (↥(separableClosure F E))ˣ),
      deningerSepUnits (F := F) (E := E) a = y ^ q ^ n := by
  haveI := HTGeometry.expChar_of_algebra F (E := E) q
  obtain ⟨n, b, hb⟩ := IsPurelyInseparable.pow_mem ↥(separableClosure F E) q (y : E)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, map_zero] at hb
    exact pow_ne_zero _ y.ne_zero hb.symm
  refine ⟨n, Units.mk0 b hb0, ?_⟩
  refine Units.ext ?_
  rw [deningerSepUnits_val]
  show (b : E) = ((y ^ q ^ n : Eˣ) : E)
  rw [Units.val_pow_eq_pow_val]
  exact hb

variable [IsAlgClosed C] [ExpChar C q]

/-- The `q`-th power map is bijective on the units of an algebraically closed field of
exponential characteristic `q`. -/
theorem deningerUnitsPow_bijective : Function.Bijective (fun c : Cˣ => c ^ q) := by
  constructor
  · intro x y hxy
    have hval : ((x : C)) ^ q = ((y : C)) ^ q := by
      have := congrArg (fun u : Cˣ => (u : C)) hxy
      simpa using this
    have hfrob : (frobenius C q) (x : C) = (frobenius C q) (y : C) := by
      rw [frobenius_def, frobenius_def]
      exact hval
    exact Units.ext ((frobenius C q).injective hfrob)
  · intro c
    obtain ⟨z, hz⟩ := deningerUnits_divisible c q (expChar_pos C q)
    exact ⟨z, hz⟩

omit [IsAlgClosure F E] in
include q in
/-- **Deninger, Corollary 3.1 (25).**  Restriction of characters to the separable closure is a
bijection. -/
theorem deningerSepCharRestrict_bijective :
    Function.Bijective (fun f : Eˣ →* Cˣ => f.comp (deningerSepUnits (F := F) (E := E))) :=
  HTGeometry.charRestrict_bijective (deningerSepUnits (F := F) (E := E))
    deningerSepUnits_injective q (deningerUnitsPow_bijective (C := C) q)
    (deningerSepUnits_pow_mem q)

include q in
/-- **Deninger, Corollary 3.1 (25).**  Characters of `κˣ` and of `(κ₀^sep)ˣ` correspond. -/
def deningerSepCharEquiv : (Eˣ →* Cˣ) ≃ ((↥(separableClosure F E))ˣ →* Cˣ) :=
  Equiv.ofBijective (fun f : Eˣ →* Cˣ => f.comp (deningerSepUnits (F := F) (E := E)))
    (deningerSepCharRestrict_bijective (C := C) q)

variable [IsAlgClosed E] [DecidableEq Eˣ] [DecidableEq (Polynomial (perfectClosure F E))]

include q in
/-- **Deninger, Corollary 3.1 (25), surjectivity.**  Every homomorphism `W_rat (κ₀) → C` comes
from a character of the units of the separable closure. -/
theorem deningerSepCharToWittHom_surjective (φ : DeningerCanonicalRationalWittRing F →+* C) :
    ∃ g : (↥(separableClosure F E))ˣ →* Cˣ,
      deningerCharToWittHom ((deningerSepCharEquiv (F := F) (E := E) (C := C) q).symm g) = φ := by
  obtain ⟨f, hf⟩ := deningerCharToWittHom_surjective (F := F) (E := E) (C := C) q φ
  refine ⟨deningerSepCharEquiv (F := F) (E := E) (C := C) q f, ?_⟩
  rw [(deningerSepCharEquiv (F := F) (E := E) (C := C) q).symm_apply_apply]
  exact hf

include q in
/-- **Deninger, Corollary 3.1 (25).**  Two characters of `(κ₀^sep)ˣ` induce the same homomorphism
of `W_rat (κ₀)` exactly when they differ by an element of the Galois group. -/
theorem deningerSepCharToWittHom_eq_iff (g₁ g₂ : (↥(separableClosure F E))ˣ →* Cˣ) :
    deningerCharToWittHom (F := F) (E := E)
          ((deningerSepCharEquiv (F := F) (E := E) (C := C) q).symm g₁)
        = deningerCharToWittHom (F := F) (E := E)
          ((deningerSepCharEquiv (F := F) (E := E) (C := C) q).symm g₂)
      ↔ ∃ σ : E ≃ₐ[F] E, g₂ = g₁.comp
          (Units.map ((σ.restrictNormal ↥(separableClosure F E) :
            ↥(separableClosure F E) ≃ₐ[F] ↥(separableClosure F E)) :
            ↥(separableClosure F E) →* ↥(separableClosure F E))) := by
  rw [deningerCharToWittHom_eq_iff (F := F) (E := E) (C := C) q]
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    have h := congrArg (deningerSepCharEquiv (F := F) (E := E) (C := C) q) hσ
    rw [(deningerSepCharEquiv (F := F) (E := E) (C := C) q).apply_symm_apply] at h
    rw [h]
    show (((deningerSepCharEquiv (F := F) (E := E) (C := C) q).symm g₁).comp
        (Units.map ((σ : E →+* E) : E →* E))).comp (deningerSepUnits (F := F) (E := E)) = _
    rw [deningerSepCharRestrict_comp]
    congr 1
    exact (deningerSepCharEquiv (F := F) (E := E) (C := C) q).apply_symm_apply g₁
  · rintro ⟨σ, hσ⟩
    refine ⟨σ, ?_⟩
    refine (deningerSepCharEquiv (F := F) (E := E) (C := C) q).injective ?_
    rw [(deningerSepCharEquiv (F := F) (E := E) (C := C) q).apply_symm_apply]
    show g₂ = (((deningerSepCharEquiv (F := F) (E := E) (C := C) q).symm g₁).comp
      (Units.map ((σ : E →+* E) : E →* E))).comp (deningerSepUnits (F := F) (E := E))
    rw [deningerSepCharRestrict_comp]
    have hg1 : ((deningerSepCharEquiv (F := F) (E := E) (C := C) q).symm g₁).comp
        (deningerSepUnits (F := F) (E := E)) = g₁ :=
      (deningerSepCharEquiv (F := F) (E := E) (C := C) q).apply_symm_apply g₁
    rw [hg1]
    exact hσ

end

end RHTower
