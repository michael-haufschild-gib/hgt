import GaloisForLFunctions.HTGeometry.SymmetricAlgebraAlgebraicIndependence
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Polynomial.Basic

/-!
# The algebraic-direction principle

Let `A` be any commutative algebra over a field `K`, and let `L : V → A` be a linear law map.
The power-state orbit in direction `v` is

`1, L(v), L(v)², ...`.

Its canonical image in the symmetric observable algebra `Sym_K(A)` is algebraically independent
exactly when `L(v)` is transcendental over `K`.  Consequently its complete algebraic-dependence
horizon is the inverse image under `L` of the integral closure of `K` in `A`.

Over a field, algebraic and integral elements coincide; integral elements form a subalgebra.
Therefore this horizon is always a vector subspace, without grading, homogeneity, reducedness, or
finite-generation assumptions on `A`.  This is the general principal mechanism behind the
linearity of cyclic commuting hypertranscendence horizons.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v

variable {K : Type u} {A : Type v} [Field K] [CommRing A] [Algebra K A]

/-- Powers of an element are linearly independent precisely when the element is transcendental. -/
theorem linearIndependent_powers_iff_transcendental (x : A) :
    LinearIndependent K (fun n : ℕ => x ^ n) ↔ Transcendental K x := by
  let T : A →ₗ[K] A := LinearMap.mulLeft K x
  have hpow : (fun n : ℕ => (T ^ n) 1) = fun n : ℕ => x ^ n := by
    funext n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ']
        change T ((T ^ n) 1) = _
        rw [ih]
        simp [T, LinearMap.mulLeft_apply, pow_succ']
  have haeval : ∀ p : Polynomial K,
      Polynomial.aeval T p 1 = Polynomial.aeval x p := by
    intro p
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp [hp, hq]
    | monomial n a =>
        simp [Polynomial.aeval_monomial, Module.End.mul_apply,
          T, LinearMap.mulLeft_apply, Algebra.smul_def]
  rw [← hpow, Polynomial.linearIndependent_powers_iff_aeval]
  rw [transcendental_iff]
  simpa [haeval]

/-- **Power-observable principle.**  Passing a power orbit to canonical degree-one observables in
the symmetric algebra turns state linear independence into observable algebraic independence. -/
theorem symmetricPowerObservable_algebraicIndependent_iff_transcendental (x : A) :
    AlgebraicIndependent K
        (fun n : ℕ => SymmetricAlgebra.ι K A (x ^ n)) ↔
      Transcendental K x := by
  rw [symmetricAlgebra_ι_algebraicIndependent_iff_linearIndependent,
    linearIndependent_powers_iff_transcendental]

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- Directions mapped to elements algebraic over the base field.  It is a submodule because over a
field the algebraic elements are exactly the integral closure, which is a subalgebra. -/
def algebraicDirectionHorizon (L : V →ₗ[K] A) : Submodule K V :=
  (integralClosure K A).toSubmodule.comap L

/-- Membership in the algebraic-direction horizon is exactly algebraicity of the law element. -/
theorem mem_algebraicDirectionHorizon_iff (L : V →ₗ[K] A) (v : V) :
    v ∈ algebraicDirectionHorizon L ↔ IsAlgebraic K (L v) := by
  change IsIntegral K (L v) ↔ IsAlgebraic K (L v)
  exact isAlgebraic_iff_isIntegral.symm

/-- **General principal-symbol horizon theorem.**  For any linear law map into any commutative
algebra, the complete dependence horizon of the canonical power observable is exactly the carrier
of the algebraic-direction submodule. -/
theorem symmetricPowerObservable_dependenceHorizon_eq
    (L : V →ₗ[K] A) :
    {v : V | ¬ AlgebraicIndependent K
      (fun n : ℕ => SymmetricAlgebra.ι K A ((L v) ^ n))} =
        (algebraicDirectionHorizon L : Set V) := by
  ext v
  rw [Set.mem_setOf_eq,
    symmetricPowerObservable_algebraicIndependent_iff_transcendental]
  simpa [Transcendental] using (mem_algebraicDirectionHorizon_iff L v).symm

end


end GaloisForLFunctions.HTGeometry
