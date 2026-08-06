import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# The simultaneous source-boundary module

The differential operators with constant coefficients form the polynomial ring `C[D]`, and the
family of source increments of a base field is a `C[D]`-module through the derivation acting
coordinatewise.  The simultaneous coboundaries `(τ_i k − k)_i` form a `C[D]`-submodule, because
the source automorphisms commute with the derivation and fix the constants.

The quotient is the simultaneous source boundary of the base field.  A finite family of source
increments is linearly independent over `C[D]` in that quotient exactly when no nonzero finite
differential character of the family is one simultaneous coboundary — the exact condition produced
by the arbitrary-family additive source theorem.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K : Type u} [Field C] [Field K] [Algebra C K] [Differential K]

/-! ### The derivation as a constant-linear endomorphism -/

/-- The derivation of the base field, as an endomorphism linear over the constants. -/
def derivC (hC : ∀ c : C, (algebraMap C K c)′ = 0) : K →ₗ[C] K where
  toFun x := x′
  map_add' x y := Differential.deriv.map_add x y
  map_smul' c x := by
    show (c • x)′ = c • x′
    rw [Algebra.smul_def, Algebra.smul_def, Derivation.leibniz, hC c, smul_zero, add_zero,
      smul_eq_mul]

@[simp] theorem derivC_apply (hC : ∀ c : C, (algebraMap C K c)′ = 0) (x : K) :
    derivC hC x = x′ := rfl

/-- The derivation acting coordinatewise on source cochains. -/
def derivPi (hC : ∀ c : C, (algebraMap C K c)′ = 0) (I : Type u) :
    (I → K) →ₗ[C] (I → K) :=
  LinearMap.pi fun i => (derivC hC).comp (LinearMap.proj i)

@[simp] theorem derivPi_apply (hC : ∀ c : C, (algebraMap C K c)′ = 0) {I : Type u}
    (w : I → K) (i : I) : derivPi hC I w i = (w i)′ := rfl

/-! ### The module of source cochains -/

/-- Source cochains: the family of increments in every source direction, as a module over the
constant-coefficient differential operators. -/
abbrev SourceCochain (hC : ∀ c : C, (algebraMap C K c)′ = 0) (I : Type u) : Type u :=
  Module.AEval' (derivPi hC I)

/-- The base field itself, as a module over the constant-coefficient differential operators. -/
abbrev BaseCochain (hC : ∀ c : C, (algebraMap C K c)′ = 0) : Type u :=
  Module.AEval' (derivC hC)

variable {I : Type u} (tau : I → K ≃+* K)

/-- The polynomial action on the operator module is the evaluation of the polynomial at the
endomorphism. -/
theorem smul_aEval_of {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] M) (P : Polynomial R) (y : M) :
    P • (Module.AEval'.of φ) y = (Module.AEval'.of φ) ((Polynomial.aeval φ) P y) := rfl

theorem aEval_of_symm_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] M) (P : Polynomial R) (x : Module.AEval' φ) :
    (Module.AEval'.of φ).symm (P • x)
      = (Polynomial.aeval φ) P ((Module.AEval'.of φ).symm x) := rfl

/-- Peeling one derivation off a monomial action. -/
theorem aeval_monomial_succ_apply {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (φ : M →ₗ[R] M) (a : R) (k : ℕ) (z : M) :
    (Polynomial.aeval φ) (Polynomial.C a * Polynomial.X ^ (k + 1)) z
      = (Polynomial.aeval φ) (Polynomial.C a * Polynomial.X ^ k) (φ z) := by
  rw [pow_succ, ← mul_assoc, map_mul, Module.End.mul_apply, Polynomial.aeval_X]

/-- The simultaneous coboundary of a base element. -/
def coboundFun (k : K) : I → K := fun i => tau i k - k

/-- The coboundary map, linear over the constants. -/
def coboundC (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c) :
    K →ₗ[C] (I → K) where
  toFun := coboundFun tau
  map_add' x y := by
    funext i
    show tau i (x + y) - (x + y) = (tau i x - x) + (tau i y - y)
    rw [map_add]
    ring
  map_smul' c x := by
    funext i
    show tau i (c • x) - c • x = (c • coboundFun tau x) i
    rw [Algebra.smul_def, map_mul, hfix]
    show algebraMap C K c * tau i x - algebraMap C K c * x
      = c • (tau i x - x)
    rw [Algebra.smul_def]
    ring

/-- The coboundary map on the operator modules. -/
def coboundPoly (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′) :
    BaseCochain hC →ₗ[Polynomial C] SourceCochain hC I where
  toFun x := (Module.AEval'.of (derivPi hC I))
    (coboundC tau hfix ((Module.AEval'.of (derivC hC)).symm x))
  map_add' x y := by
    simp only [map_add]
  map_smul' P x := by
    have hcomm : ∀ (Q : Polynomial C) (y : K),
        coboundC tau hfix ((Polynomial.aeval (derivC hC)) Q y)
          = (Polynomial.aeval (derivPi hC I)) Q (coboundC tau hfix y) := by
      intro Q
      induction Q using Polynomial.induction_on with
      | C a =>
          intro y
          rw [Polynomial.aeval_C, Polynomial.aeval_C]
          show coboundC tau hfix (a • y) = a • coboundC tau hfix y
          rw [map_smul]
      | add p q hp hq =>
          intro y
          rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
      | monomial k a hk =>
          intro y
          rw [aeval_monomial_succ_apply (derivC hC) a k y, hk,
            aeval_monomial_succ_apply (derivPi hC I) a k (coboundC tau hfix y)]
          congr 1
          funext i
          show tau i (y′) - y′ = (tau i y - y)′
          rw [hderiv, map_sub]
    show (Module.AEval'.of (derivPi hC I))
        (coboundC tau hfix ((Module.AEval'.of (derivC hC)).symm (P • x)))
      = P • (Module.AEval'.of (derivPi hC I))
        (coboundC tau hfix ((Module.AEval'.of (derivC hC)).symm x))
    rw [aEval_of_symm_smul, hcomm, smul_aEval_of]

/-- The simultaneous source-boundary module of the base field: source cochains modulo
simultaneous coboundaries. -/
abbrev sourceBoundaryModule (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′) : Type u :=
  SourceCochain hC I ⧸ LinearMap.range (coboundPoly tau hC hfix hderiv)

/-- The boundary class of a family of source increments. -/
def boundaryClass (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′) (w : I → K) :
    sourceBoundaryModule tau hC hfix hderiv :=
  Submodule.Quotient.mk ((Module.AEval'.of (derivPi hC I)) w)

/-- A cochain is a boundary exactly when it is a simultaneous coboundary. -/
theorem boundaryClass_eq_zero_iff (hC : ∀ c : C, (algebraMap C K c)′ = 0)
    (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
    (hderiv : ∀ i k, tau i k′ = (tau i k)′) (w : I → K) :
    boundaryClass tau hC hfix hderiv w = 0 ↔ ∃ k : K, ∀ i, w i = tau i k - k := by
  rw [boundaryClass, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨(Module.AEval'.of (derivC hC)).symm x, fun i => ?_⟩
    have := congrArg (Module.AEval'.of (derivPi hC I)).symm hx
    simp only [coboundPoly, LinearEquiv.symm_apply_apply, LinearMap.coe_mk,
      AddHom.coe_mk] at this
    exact congrFun this.symm i
  · rintro ⟨k, hk⟩
    refine ⟨(Module.AEval'.of (derivC hC)) k, ?_⟩
    show (Module.AEval'.of (derivPi hC I))
      (coboundC tau hfix ((Module.AEval'.of (derivC hC)).symm
        ((Module.AEval'.of (derivC hC)) k))) = _
    rw [LinearEquiv.symm_apply_apply]
    congr 1
    funext i
    exact (hk i).symm

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {C K : Type u} [Field C] [Field K] [Algebra C K] [Differential K]
  {I : Type u} (tau : I → K ≃+* K)

/-! ### The operator action in coordinates -/

theorem aeval_derivPi_apply (hC : ∀ c : C, (algebraMap C K c)′ = 0) (P : Polynomial C) :
    ∀ (w : I → K) (i : I),
      (Polynomial.aeval (derivPi hC I)) P w i = (Polynomial.aeval (derivC hC)) P (w i) := by
  induction P using Polynomial.induction_on with
  | C a =>
      intro w i
      rw [Polynomial.aeval_C, Polynomial.aeval_C]
      show (a • w) i = a • w i
      rw [Pi.smul_apply]
  | add p q hp hq =>
      intro w i
      rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Pi.add_apply, hp, hq]
  | monomial k a hk =>
      intro w i
      rw [aeval_monomial_succ_apply (derivPi hC I) a k w,
        aeval_monomial_succ_apply (derivC hC) a k (w i), hk]
      rfl

/-! ### Boundary classes are additive and operator linear -/

variable (hC : ∀ c : C, (algebraMap C K c)′ = 0)
  (hfix : ∀ i c, tau i (algebraMap C K c) = algebraMap C K c)
  (hderiv : ∀ i k, tau i k′ = (tau i k)′)

theorem boundaryClass_add (v w : I → K) :
    boundaryClass tau hC hfix hderiv (v + w)
      = boundaryClass tau hC hfix hderiv v + boundaryClass tau hC hfix hderiv w := by
  rw [boundaryClass, boundaryClass, boundaryClass, map_add, ← Submodule.Quotient.mk_add]

theorem boundaryClass_zero :
    boundaryClass tau hC hfix hderiv (0 : I → K) = 0 := by
  rw [boundaryClass, map_zero, Submodule.Quotient.mk_zero]

theorem boundaryClass_smul (P : Polynomial C) (w : I → K) :
    P • boundaryClass tau hC hfix hderiv w
      = boundaryClass tau hC hfix hderiv ((Polynomial.aeval (derivPi hC I)) P w) := by
  rw [boundaryClass, boundaryClass, ← Submodule.Quotient.mk_smul, smul_aEval_of]

theorem boundaryClass_sum {κ : Type u} (s : Finset κ) (w : κ → (I → K)) :
    boundaryClass tau hC hfix hderiv (∑ p ∈ s, w p)
      = ∑ p ∈ s, boundaryClass tau hC hfix hderiv (w p) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, boundaryClass_zero]
  | insert j S hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj, boundaryClass_add, ih]

/-! ### The operator form of the source-boundary criterion -/

/-- **The boundary classes are independent exactly when no nonzero operator character of the
source increments is a simultaneous coboundary.**  This is the linear-algebra form of the
simultaneous coboundary criterion: the operators are elements of `C[D]`, not all zero, and the
coboundary is required in every source direction at once. -/
theorem linearIndependent_boundaryClass_iff {κ : Type u} (omega : I → κ → K) :
    LinearIndependent (Polynomial C)
        (fun p : κ => boundaryClass tau hC hfix hderiv fun i => omega i p) ↔
      ∀ l : κ →₀ Polynomial C, l ≠ 0 → ∀ k : K, ∃ i,
        tau i k - k ≠
          ∑ p ∈ l.support, (Polynomial.aeval (derivC hC)) (l p) (omega i p) := by
  classical
  rw [linearIndependent_iff]
  constructor
  · intro hind l hl k
    by_contra hcon
    have hall : ∀ i, tau i k - k
        = ∑ p ∈ l.support, (Polynomial.aeval (derivC hC)) (l p) (omega i p) := by
      intro i
      by_contra hne
      exact hcon ⟨i, hne⟩
    apply hl
    refine hind l ?_
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    have hterm : ∀ p ∈ l.support,
        l p • boundaryClass tau hC hfix hderiv (fun i => omega i p)
          = boundaryClass tau hC hfix hderiv
            (fun i => (Polynomial.aeval (derivC hC)) (l p) (omega i p)) := by
      intro p _
      rw [boundaryClass_smul]
      congr 1
      funext i
      rw [aeval_derivPi_apply]
    rw [Finset.sum_congr rfl hterm, ← boundaryClass_sum]
    refine (boundaryClass_eq_zero_iff tau hC hfix hderiv _).2 ⟨k, fun i => ?_⟩
    rw [Finset.sum_apply]
    exact (hall i).symm
  · intro hcrit l hl
    by_contra hne
    have hzero : boundaryClass tau hC hfix hderiv
        (∑ p ∈ l.support, fun i => (Polynomial.aeval (derivC hC)) (l p) (omega i p)) = 0 := by
      rw [boundaryClass_sum]
      have hterm : ∀ p ∈ l.support,
          boundaryClass tau hC hfix hderiv
            (fun i => (Polynomial.aeval (derivC hC)) (l p) (omega i p))
            = l p • boundaryClass tau hC hfix hderiv (fun i => omega i p) := by
        intro p _
        rw [boundaryClass_smul]
        congr 1
        funext i
        rw [aeval_derivPi_apply]
      rw [Finset.sum_congr rfl hterm]
      rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
      exact hl
    obtain ⟨k, hk⟩ := (boundaryClass_eq_zero_iff tau hC hfix hderiv _).1 hzero
    obtain ⟨i, hi⟩ := hcrit l hne k
    exact hi ((hk i).symm.trans (Finset.sum_apply _ _ _))

end

end GaloisForLFunctions.HTGeometry
