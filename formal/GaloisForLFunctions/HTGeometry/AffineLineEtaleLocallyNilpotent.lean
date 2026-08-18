import GaloisForLFunctions.HTGeometry.EtaleDerivationLift
import GaloisForLFunctions.HTGeometry.AffineLineEtaleSplit
import GaloisForLFunctions.HTGeometry.SplitFiniteAlgebraDiscriminant

/-!
# The lift of `d/dX` to an étale algebra over the affine line is locally nilpotent

Over an algebraically closed field `E` of characteristic zero, let `B` be a finite free
`E[X]`-algebra with unit discriminant.  The unique derivation of `B` lifting `d/dX`
(`EtaleDerivationLift`) is locally nilpotent:

```text
locallyNilpotent_liftDerivation :  ∃ N, (liftDerivation e hd (polyDeriv E))^[N] b = 0
```

`AffineLineEtaleSplit` makes `B ≅ E[X]ⁿ`; conjugating the lift across that isomorphism gives a
derivation of `E[X]ⁿ` lifting `d/dX`, which by the *uniqueness* of lifts must be the componentwise
derivative, and iterated differentiation kills a polynomial.

Together with the slice theorem (`LocallyNilpotentDerivationSlice`) this says: a finite étale
algebra over `R[w]` is `C[w]` for its algebra of constants `C`, which is the `𝔸¹`-invariance that
drives the induction on the number of variables.
-/


namespace GaloisForLFunctions.HTGeometry

open Polynomial

set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false

/-- The derivative, as a derivation of the polynomial ring over the base. -/
noncomputable def polyDeriv (R : Type*) [CommRing R] : Derivation R R[X] R[X] where
  toFun := fun p => Polynomial.derivative p
  map_add' := fun p q => map_add _ p q
  map_smul' := fun r p => by simp
  map_one_eq_zero' := by simp
  leibniz' := fun p q => by
    show Polynomial.derivative (p * q) = p • Polynomial.derivative q + q • Polynomial.derivative p
    rw [Polynomial.derivative_mul, smul_eq_mul, smul_eq_mul]
    ring

@[simp] theorem polyDeriv_apply (R : Type*) [CommRing R] (p : R[X]) :
    polyDeriv R p = Polynomial.derivative p := rfl

/-- The componentwise derivative on a finite product of polynomial rings. -/
noncomputable def piPolyDeriv (R : Type*) [CommRing R] (m : ℕ) :
    Derivation R (Fin m → R[X]) (Fin m → R[X]) where
  toFun := fun f i => Polynomial.derivative (f i)
  map_add' := fun f g => by funext i; simp
  map_smul' := fun r f => by funext i; simp
  map_one_eq_zero' := by funext i; simp
  leibniz' := fun f g => by
    funext i
    show Polynomial.derivative (f i * g i)
      = (f • fun j => Polynomial.derivative (g j)) i + (g • fun j => Polynomial.derivative (f j)) i
    simp only [Pi.smul_apply', smul_eq_mul]
    rw [Polynomial.derivative_mul]
    ring

/-- Conjugating a derivation by an algebra isomorphism. -/
noncomputable def conjDerivation {R A₁ A₂ : Type*} [CommRing R] [CommRing A₁] [CommRing A₂]
    [Algebra R A₁] [Algebra R A₂] (Φ : A₁ ≃ₐ[R] A₂) (D : Derivation R A₁ A₁) :
    Derivation R A₂ A₂ where
  toFun := fun x => Φ (D (Φ.symm x))
  map_add' := fun x y => by simp
  map_smul' := fun r x => by simp
  map_one_eq_zero' := by simp
  leibniz' := fun x y => by
    show Φ (D (Φ.symm (x * y))) = x • Φ (D (Φ.symm y)) + y • Φ (D (Φ.symm x))
    rw [map_mul, D.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul]

theorem conjDerivation_apply {R A₁ A₂ : Type*} [CommRing R] [CommRing A₁] [CommRing A₂]
    [Algebra R A₁] [Algebra R A₂] (Φ : A₁ ≃ₐ[R] A₂) (D : Derivation R A₁ A₁) (x : A₂) :
    conjDerivation Φ D x = Φ (D (Φ.symm x)) := rfl


open Lift

universe u

theorem iterate_piPolyDeriv (R : Type*) [CommRing R] (m N : ℕ) (f : Fin m → R[X]) :
    (⇑(piPolyDeriv R m))^[N] f = fun i => (Polynomial.derivative)^[N] (f i) := by
  induction N generalizing f with
  | zero => rfl
  | succ N ih =>
      rw [Function.iterate_succ_apply, ih]
      funext i
      rw [Function.iterate_succ_apply]
      rfl

theorem locallyNilpotent_piPolyDeriv (R : Type*) [CommRing R] (m : ℕ) (f : Fin m → R[X]) :
    ∃ N : ℕ, (⇑(piPolyDeriv R m))^[N] f = 0 := by
  classical
  refine ⟨(Finset.univ.sup fun i => (f i).natDegree) + 1, ?_⟩
  rw [iterate_piPolyDeriv]
  funext i
  refine Polynomial.iterate_derivative_eq_zero ?_
  have : (f i).natDegree ≤ Finset.univ.sup fun j => (f j).natDegree :=
    Finset.le_sup (f := fun j => (f j).natDegree) (Finset.mem_univ i)
  omega

theorem locallyNilpotent_liftDerivation (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    {B : Type u} [CommRing B] [Algebra E[X] B] [Algebra E B] [IsScalarTower E E[X] B]
    [Module.Free E[X] B] [Module.Finite E[X] B]
    {n : ℕ} (e : Module.Basis (Fin n) E[X] B) (hd : IsUnit (Algebra.discr E[X] e)) (b : B) :
    ∃ N : ℕ, (⇑(liftDerivation e hd (polyDeriv E)))^[N] b = 0 := by
  classical
  obtain ⟨Φ₀⟩ := nonempty_algEquiv_pi_of_isUnit_discr E n e hd
  set Φ : B ≃ₐ[E] (Fin n → E[X]) := Φ₀.restrictScalars E with hΦ
  set bP : Module.Basis (Fin n) E[X] (Fin n → E[X]) := Pi.basisFun E[X] (Fin n) with hbP
  have hdP : IsUnit (Algebra.discr E[X] bP) := by
    rw [hbP, discr_pi_basisFun]
    exact isUnit_one
  set dB := liftDerivation e hd (polyDeriv E) with hdB
  set dP := conjDerivation Φ dB with hdPdef
  have hΦsym : ∀ p : E[X], Φ.symm (algebraMap E[X] (Fin n → E[X]) p) = algebraMap E[X] B p := by
    intro p
    exact Φ₀.symm.commutes p
  have hΦcom : ∀ p : E[X], Φ (algebraMap E[X] B p) = algebraMap E[X] (Fin n → E[X]) p := by
    intro p
    exact Φ₀.commutes p
  have hbase : ∀ p : E[X], dP (algebraMap E[X] (Fin n → E[X]) p)
      = piPolyDeriv E n (algebraMap E[X] (Fin n → E[X]) p) := by
    intro p
    rw [hdPdef, conjDerivation_apply, hΦsym p, hdB,
      liftDerivation_algebraMap e hd (polyDeriv E) p, hΦcom]
    funext i
    rfl
  have hkey : dP = piPolyDeriv E n :=
    derivation_ext bP hdP dP (piPolyDeriv E n) hbase
  have hstepP : ∀ y : B, dP (Φ y) = Φ (dB y) := by
    intro y
    rw [hdPdef, conjDerivation_apply, AlgEquiv.symm_apply_apply]
  have htrans : ∀ (N : ℕ) (x : B), Φ ((⇑dB)^[N] x) = (⇑dP)^[N] (Φ x) := by
    intro N
    induction N with
    | zero => intro x; rfl
    | succ N ih =>
        intro x
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih x, hstepP]
  obtain ⟨N, hN⟩ := locallyNilpotent_piPolyDeriv E n (Φ b)
  refine ⟨N, ?_⟩
  have h1 : Φ ((⇑dB)^[N] b) = 0 := by
    rw [htrans N b, hkey, hN]
  exact Φ.injective (by rw [h1, map_zero])

end GaloisForLFunctions.HTGeometry
