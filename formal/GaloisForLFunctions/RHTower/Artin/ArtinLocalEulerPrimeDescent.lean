import GaloisForLFunctions.RHTower.Artin.ArtinLocalEulerPrimeTransport
import Mathlib.LinearAlgebra.Charpoly.ToMatrix

/-!
# Conjugate-prime invariance of Artin local Euler polynomials

This file proves the actual algebraic prime-choice transport for the local Artin polynomial.  A
group element carrying `Q` to `τ • Q` transports decomposition groups, inertia invariants, and an
arithmetic Frobenius lift.  The resulting invariant-space maps are linearly conjugate, so their
reversed characteristic polynomials agree.

The result is still local: it treats conjugate prime ideals and does not yet use transitivity over
a base prime, define a global Euler product, or assert analytic continuation.
-/

open scoped Pointwise

noncomputable section

universe u

namespace GaloisForLFunctions

variable {S G V : Type u}
variable [CommRing S] [Group G] [MulSemiringAction G S]
variable [AddCommGroup V] [Module ℂ V]

/-- The natural conjugation equivalence between the decomposition stabilizers of `Q` and `τ • Q`.
-/
noncomputable def primeStabilizerConjEquiv (τ : G) (Q : Ideal S) :
    MulAction.stabilizer G Q ≃* MulAction.stabilizer G (τ • Q) :=
  MulAction.stabilizerEquivStabilizer (show τ • Q = τ • Q from rfl)

/-- The representation action of `τ` sends `I_Q`-invariants to `I_(τ • Q)`-invariants. -/
noncomputable def inertiaInvariantConjMap
    (ρ : Representation ℂ G V) (τ : G) (Q : Ideal S) :
    Representation.invariants
        ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
          (Q.inertia (MulAction.stabilizer G Q)).subtype) →ₗ[ℂ]
      Representation.invariants
        ((ρ.comp (MulAction.stabilizer G (τ • Q)).subtype).comp
          ((τ • Q).inertia (MulAction.stabilizer G (τ • Q))).subtype) where
  toFun x := ⟨ρ τ x, by
    intro j
    let e := primeStabilizerConjEquiv τ Q
    have hjmap : (j : MulAction.stabilizer G (τ • Q)) ∈
        (Q.inertia (MulAction.stabilizer G Q)).map e.toMonoidHom := by
      rw [show e = MulAction.stabilizerEquivStabilizer
        (show τ • Q = τ • Q from rfl) by rfl, inertia_map_stabilizer_conj]
      exact j.property
    rw [Subgroup.mem_map_equiv] at hjmap
    let i : Q.inertia (MulAction.stabilizer G Q) := ⟨e.symm j, hjmap⟩
    have hej : e (i : MulAction.stabilizer G Q) = j := by
      dsimp [i]
      exact e.apply_symm_apply j
    change ρ (j : G) (ρ τ x) = ρ τ x
    rw [← hej]
    dsimp [e, primeStabilizerConjEquiv]
    rw [MulAction.stabilizerEquivStabilizer_apply]
    change ρ (τ * (i : G) * τ⁻¹) (ρ τ x) = ρ τ x
    rw [ρ.map_mul, ρ.map_mul, Module.End.mul_apply, Module.End.mul_apply]
    have hinv : ρ τ⁻¹ (ρ τ (x : V)) = x := by
      rw [← Module.End.mul_apply, ← ρ.map_mul,
        show τ⁻¹ * τ = 1 by group, map_one, Module.End.one_apply]
    rw [hinv]
    have hi : ρ (i : G) (x : V) = x := by
      simpa using x.property i
    rw [hi]
    ⟩
  map_add' x y := by
    ext
    exact (ρ τ).map_add x y
  map_smul' r x := by
    ext
    exact (ρ τ).map_smul r x

/-- Conjugation by `τ` gives a concrete linear equivalence of the two inertia-invariant spaces. -/
noncomputable def inertiaInvariantConjLinearEquiv
    (ρ : Representation ℂ G V) (τ : G) (Q : Ideal S) :
    Representation.invariants
        ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
          (Q.inertia (MulAction.stabilizer G Q)).subtype) ≃ₗ[ℂ]
      Representation.invariants
        ((ρ.comp (MulAction.stabilizer G (τ • Q)).subtype).comp
          ((τ • Q).inertia (MulAction.stabilizer G (τ • Q))).subtype) where
  toFun := inertiaInvariantConjMap ρ τ Q
  invFun y := ⟨ρ τ⁻¹ y, by
    intro i
    let e := primeStabilizerConjEquiv τ Q
    have himap : e (i : MulAction.stabilizer G Q) ∈
        (τ • Q).inertia (MulAction.stabilizer G (τ • Q)) := by
      rw [← inertia_map_stabilizer_conj]
      exact Subgroup.mem_map_of_mem e.toMonoidHom i.property
    let j : (τ • Q).inertia (MulAction.stabilizer G (τ • Q)) :=
      ⟨e i, himap⟩
    have hei : e.symm (j : MulAction.stabilizer G (τ • Q)) = i := by
      dsimp [j]
      exact e.symm_apply_apply i
    change ρ (i : G) (ρ τ⁻¹ y) = ρ τ⁻¹ y
    rw [← hei]
    dsimp [e, primeStabilizerConjEquiv]
    rw [MulAction.stabilizerEquivStabilizer_symm_apply]
    rw [MulAut.conj_apply]
    simp only [inv_inv]
    rw [ρ.map_mul, ρ.map_mul, Module.End.mul_apply, Module.End.mul_apply]
    have hcancel : ρ τ (ρ τ⁻¹ (y : V)) = y := by
      rw [← Module.End.mul_apply, ← ρ.map_mul,
        show τ * τ⁻¹ = 1 by group, map_one, Module.End.one_apply]
    rw [hcancel]
    have hj : ρ (j : G) (y : V) = y := by
      simpa using y.property j
    rw [hj]
    ⟩
  left_inv x := by
    apply Subtype.ext
    change ρ τ⁻¹ (ρ τ (x : V)) = x
    rw [← Module.End.mul_apply, ← ρ.map_mul,
      show τ⁻¹ * τ = 1 by group, map_one, Module.End.one_apply]
  right_inv y := by
    apply Subtype.ext
    change ρ τ (ρ τ⁻¹ (y : V)) = y
    rw [← Module.End.mul_apply, ← ρ.map_mul,
      show τ * τ⁻¹ = 1 by group, map_one, Module.End.one_apply]
  map_add' x y := (inertiaInvariantConjMap ρ τ Q).map_add x y
  map_smul' r x := (inertiaInvariantConjMap ρ τ Q).map_smul r x

/-- The invariant-space transport intertwines each decomposition-group action with its conjugate.
-/
theorem inertiaInvariantConjMap_intertwines
    (ρ : Representation ℂ G V) (τ : G) (Q : Ideal S)
    (φ : MulAction.stabilizer G Q)
    (x : Representation.invariants
      ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
        (Q.inertia (MulAction.stabilizer G Q)).subtype)) :
    inertiaInvariantConjMap ρ τ Q
      ((Representation.toInvariants (ρ.comp (MulAction.stabilizer G Q).subtype)
        (Q.inertia (MulAction.stabilizer G Q))) φ x) =
      (Representation.toInvariants (ρ.comp (MulAction.stabilizer G (τ • Q)).subtype)
        ((τ • Q).inertia (MulAction.stabilizer G (τ • Q))))
        (primeStabilizerConjEquiv τ Q φ) (inertiaInvariantConjMap ρ τ Q x) := by
  apply Subtype.ext
  change ρ τ (ρ (φ : G) x) =
    ρ ((primeStabilizerConjEquiv τ Q φ : MulAction.stabilizer G (τ • Q)) : G) (ρ τ x)
  dsimp [primeStabilizerConjEquiv]
  rw [MulAction.stabilizerEquivStabilizer_apply]
  change ρ τ (ρ (φ : G) x) = ρ (τ * (φ : G) * τ⁻¹) (ρ τ x)
  rw [ρ.map_mul, ρ.map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have hinv : ρ τ⁻¹ (ρ τ (x : V)) = x := by
    rw [← Module.End.mul_apply, ← ρ.map_mul,
      show τ⁻¹ * τ = 1 by group, map_one, Module.End.one_apply]
  rw [hinv]

/-- The induced endomorphisms of the two inertia-invariant spaces are linearly conjugate. -/
theorem inertiaInvariantConjLinearEquiv_conj_toInvariants
    (ρ : Representation ℂ G V) (τ : G) (Q : Ideal S)
    (φ : MulAction.stabilizer G Q) :
    (inertiaInvariantConjLinearEquiv ρ τ Q).conj
      ((Representation.toInvariants (ρ.comp (MulAction.stabilizer G Q).subtype)
        (Q.inertia (MulAction.stabilizer G Q))) φ) =
      (Representation.toInvariants (ρ.comp (MulAction.stabilizer G (τ • Q)).subtype)
        ((τ • Q).inertia (MulAction.stabilizer G (τ • Q))))
        (primeStabilizerConjEquiv τ Q φ) := by
  let e := inertiaInvariantConjLinearEquiv ρ τ Q
  let f := Representation.toInvariants (ρ.comp (MulAction.stabilizer G Q).subtype)
    (Q.inertia (MulAction.stabilizer G Q)) φ
  let f' := Representation.toInvariants (ρ.comp (MulAction.stabilizer G (τ • Q)).subtype)
    ((τ • Q).inertia (MulAction.stabilizer G (τ • Q)))
    (primeStabilizerConjEquiv τ Q φ)
  change e.conj f = f'
  have hinter (x : Representation.invariants
      ((ρ.comp (MulAction.stabilizer G Q).subtype).comp
        (Q.inertia (MulAction.stabilizer G Q)).subtype)) :
      e (f x) = f' (e x) := by
    dsimp [e, inertiaInvariantConjLinearEquiv]
    exact inertiaInvariantConjMap_intertwines ρ τ Q φ x
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  exact congrArg Subtype.val (by
    calc
      (e.conj f) (e x) = e (f (e.symm (e x))) := by
        rw [LinearEquiv.conj_apply]
        rfl
      _ = e (f x) := by rw [e.symm_apply_apply]
      _ = f' (e x) := hinter x)

/-- A finite residue quotient at `Q` transports concretely to one at `τ • Q`. -/
theorem finiteQuotient_smul (τ : G) (Q : Ideal S) [Finite (S ⧸ Q)] :
    Finite (S ⧸ (τ • Q)) :=
  Finite.of_equiv (S ⧸ Q)
    (Ideal.quotientEquiv Q (τ • Q) (MulSemiringAction.toRingEquiv G S τ) (by rfl)).toEquiv

variable {R : Type u}
variable [CommRing R] [Algebra R S] [Finite G] [SMulCommClass G R S]
variable [Algebra.IsInvariant R S G] [FiniteDimensional ℂ V]

/-- The local Artin polynomial at `τ • Q`, using the residue-finiteness transported from `Q`. -/
noncomputable def frobeniusInertiaEulerPolynomial_smul
    (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) : Polynomial ℂ :=
  @frobeniusInertiaEulerPolynomial V inferInstance R S G
    inferInstance inferInstance inferInstance inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance inferInstance
    (τ • Q) (Ideal.IsPrime.smul τ) (finiteQuotient_smul τ Q) ρ

/-- The actual local Artin Euler polynomial is unchanged by replacing `Q` with the conjugate
prime `τ • Q`. -/
theorem frobeniusInertiaEulerPolynomial_eq_of_smul
    (τ : G) (Q : Ideal S) [Q.IsPrime] [Finite (S ⧸ Q)]
    (ρ : Representation ℂ G V) :
    frobeniusInertiaEulerPolynomial_smul (R := R) τ Q ρ =
      frobeniusInertiaEulerPolynomial (R := R) Q ρ := by
  letI : (τ • Q).IsPrime := Ideal.IsPrime.smul τ
  letI : Finite (S ⧸ (τ • Q)) := finiteQuotient_smul τ Q
  let φ := arithmeticFrobeniusInStabilizer (R := R) (G := G) Q
  let hφ : IsArithFrobAt R (arithFrobAt R G Q) Q :=
    IsArithFrobAt.arithFrobAt R G Q
  let hφ' : IsArithFrobAt R (τ * arithFrobAt R G Q * τ⁻¹) (τ • Q) := hφ.conj τ
  have heq : primeStabilizerConjEquiv τ Q φ =
      anyFrobeniusInStabilizer (R := R) (τ • Q) hφ' := by
    rfl
  have hchar :
      ((Representation.toInvariants (ρ.comp (MulAction.stabilizer G (τ • Q)).subtype)
        ((τ • Q).inertia (MulAction.stabilizer G (τ • Q))))
        (primeStabilizerConjEquiv τ Q φ)).charpoly =
      ((Representation.toInvariants (ρ.comp (MulAction.stabilizer G Q).subtype)
        (Q.inertia (MulAction.stabilizer G Q))) φ).charpoly := by
    rw [← inertiaInvariantConjLinearEquiv_conj_toInvariants ρ τ Q φ]
    exact LinearEquiv.charpoly_conj (inertiaInvariantConjLinearEquiv ρ τ Q) _
  have hpoly :
      localEulerPolynomial
        (ρ.comp (MulAction.stabilizer G (τ • Q)).subtype)
        ((τ • Q).inertia (MulAction.stabilizer G (τ • Q)))
        (primeStabilizerConjEquiv τ Q φ) =
      localEulerPolynomial
        (ρ.comp (MulAction.stabilizer G Q).subtype)
        (Q.inertia (MulAction.stabilizer G Q)) φ := by
    exact congrArg Polynomial.reverse hchar
  calc
    frobeniusInertiaEulerPolynomial (R := R) (τ • Q) ρ =
        localEulerPolynomial
          (ρ.comp (MulAction.stabilizer G (τ • Q)).subtype)
          ((τ • Q).inertia (MulAction.stabilizer G (τ • Q)))
          (anyFrobeniusInStabilizer (R := R) (τ • Q) hφ') :=
      (frobeniusInertiaEulerPolynomial_eq_of_isArithFrobAt (R := R) (τ • Q) ρ hφ').symm
    _ = localEulerPolynomial
          (ρ.comp (MulAction.stabilizer G (τ • Q)).subtype)
          ((τ • Q).inertia (MulAction.stabilizer G (τ • Q)))
          (primeStabilizerConjEquiv τ Q φ) := by rw [heq]
    _ = localEulerPolynomial
          (ρ.comp (MulAction.stabilizer G Q).subtype)
          (Q.inertia (MulAction.stabilizer G Q)) φ := hpoly
    _ = frobeniusInertiaEulerPolynomial (R := R) Q ρ := rfl

/-- The actual local Artin Euler polynomial is independent of the choice of prime ideal above a
fixed prime ideal of the invariant base ring. -/
theorem frobeniusInertiaEulerPolynomial_eq_of_under_eq
    (Q Q' : Ideal S) [Q.IsPrime] [Q'.IsPrime]
    [Finite (S ⧸ Q)] [Finite (S ⧸ Q')]
    (ρ : Representation ℂ G V) (hQQ' : Q.under R = Q'.under R) :
    frobeniusInertiaEulerPolynomial (R := R) Q' ρ =
      frobeniusInertiaEulerPolynomial (R := R) Q ρ := by
  obtain ⟨τ, hτ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq R S G Q Q' hQQ'
  subst Q'
  calc
    frobeniusInertiaEulerPolynomial (R := R) (τ • Q) ρ =
        frobeniusInertiaEulerPolynomial_smul (R := R) τ Q ρ := by rfl
    _ = frobeniusInertiaEulerPolynomial (R := R) Q ρ :=
      frobeniusInertiaEulerPolynomial_eq_of_smul τ Q ρ

end GaloisForLFunctions
