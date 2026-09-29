import Mathlib.Algebra.MvPolynomial.Derivation
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.LinearCombination

/-!
# The first two coefficients of a polynomial family of substitutions

Let `M_i(ν) ∈ R[ν]`, `R = K[x_i]`, be substitutions depending polynomially on a parameter `ν` and
starting at the identity, `M_i(0) = x_i`.  Substitution is a `K`-algebra map `P ↦ P(M(ν))` into
`R[ν]`, whose constant coefficient is the identity.

* The `ν`-coefficient `D₁` is a derivation with `D₁ x_i = M_i'(0)`.
* The `ν²`-coefficient `D₂` obeys the second-order Leibniz rule
  `D₂(PQ) = D₂P·Q + D₁P·D₁Q + P·D₂Q`, so `D₂ − ½D₁²` is again a derivation, with value
  `[ν²]M_i − ½D₁([ν]M_i)` on `x_i`.
* If `P(M(ν)) = P` for infinitely many values `ν ∈ K`, then `P(M(ν)) = P` identically, and both
  derivations kill `P`.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] {ι : Type*} (M : ι → Polynomial (MvPolynomial ι K))

/-- Substitution along a polynomial family. -/
def familySubst : MvPolynomial ι K →ₐ[K] Polynomial (MvPolynomial ι K) := aeval M

theorem familySubst_X (i : ι) : familySubst M (X i) = M i := aeval_X M i

variable {M}

theorem polynomial_coeff_mul_one {R : Type*} [CommSemiring R] (p q : Polynomial R) :
    (p * q).coeff 1 = p.coeff 0 * q.coeff 1 + p.coeff 1 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ]
  simp

theorem polynomial_coeff_mul_two {R : Type*} [CommSemiring R] (p q : Polynomial R) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 + p.coeff 2 * q.coeff 0 := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.sum_antidiagonal_succ]
  simp
  ring

/-- The constant coefficient of the substitution is the identity. -/
theorem coeff_zero_familySubst (hM : ∀ i, (M i).coeff 0 = X i) (P : MvPolynomial ι K) :
    (familySubst M P).coeff 0 = P := by
  have h : (Polynomial.constantCoeff : Polynomial (MvPolynomial ι K) →+* MvPolynomial ι K).comp
      (familySubst M).toRingHom = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp [familySubst, Polynomial.constantCoeff_apply]
    · simp [familySubst, Polynomial.constantCoeff_apply, hM]
  have := congrArg (fun f => f P) h
  simpa [Polynomial.constantCoeff_apply] using this

variable (M)

/-- The `ν`-coefficient of the substitution, as a linear map. -/
def familyCoeffOne : MvPolynomial ι K →ₗ[K] MvPolynomial ι K :=
  ((Polynomial.lcoeff (MvPolynomial ι K) 1).restrictScalars K).comp (familySubst M).toLinearMap

/-- The `ν²`-coefficient of the substitution, as a linear map. -/
def familyCoeffTwo : MvPolynomial ι K →ₗ[K] MvPolynomial ι K :=
  ((Polynomial.lcoeff (MvPolynomial ι K) 2).restrictScalars K).comp (familySubst M).toLinearMap

variable {M}

theorem familyCoeffOne_apply (P : MvPolynomial ι K) :
    familyCoeffOne M P = (familySubst M P).coeff 1 := rfl

theorem familyCoeffTwo_apply (P : MvPolynomial ι K) :
    familyCoeffTwo M P = (familySubst M P).coeff 2 := rfl

theorem familyCoeffOne_mul (hM : ∀ i, (M i).coeff 0 = X i) (P Q : MvPolynomial ι K) :
    familyCoeffOne M (P * Q) = P * familyCoeffOne M Q + Q * familyCoeffOne M P := by
  rw [familyCoeffOne_apply, familyCoeffOne_apply, familyCoeffOne_apply, map_mul,
    polynomial_coeff_mul_one, coeff_zero_familySubst hM, coeff_zero_familySubst hM]
  ring

theorem familyCoeffTwo_mul (hM : ∀ i, (M i).coeff 0 = X i) (P Q : MvPolynomial ι K) :
    familyCoeffTwo M (P * Q) = P * familyCoeffTwo M Q + familyCoeffOne M P * familyCoeffOne M Q
      + Q * familyCoeffTwo M P := by
  rw [familyCoeffTwo_apply, familyCoeffTwo_apply, familyCoeffTwo_apply, familyCoeffOne_apply,
    familyCoeffOne_apply, map_mul, polynomial_coeff_mul_two, coeff_zero_familySubst hM,
    coeff_zero_familySubst hM]
  ring

/-- **The first-order derivation** of a substitution family starting at the identity. -/
def familyDerivOne (hM : ∀ i, (M i).coeff 0 = X i) :
    Derivation K (MvPolynomial ι K) (MvPolynomial ι K) :=
  Derivation.mk' (familyCoeffOne M) fun P Q => by
    rw [familyCoeffOne_mul hM, smul_eq_mul, smul_eq_mul]

theorem familyDerivOne_apply (hM : ∀ i, (M i).coeff 0 = X i) (P : MvPolynomial ι K) :
    familyDerivOne hM P = (familySubst M P).coeff 1 := rfl

theorem familyDerivOne_X (hM : ∀ i, (M i).coeff 0 = X i) (i : ι) :
    familyDerivOne hM (X i) = (M i).coeff 1 := by
  rw [familyDerivOne_apply, familySubst_X]

/-- The second-order combination `D₂ − ½D₁²`, as a linear map. -/
def familySecondLinear [CharZero K] (hM : ∀ i, (M i).coeff 0 = X i) :
    MvPolynomial ι K →ₗ[K] MvPolynomial ι K :=
  familyCoeffTwo M - (1 / 2 : K) •
    ((familyDerivOne hM).toLinearMap.comp (familyDerivOne hM).toLinearMap)

/-- **The second-order derivation** `D₂ − ½D₁²` of a substitution family. -/
def familyDerivTwo [CharZero K] (hM : ∀ i, (M i).coeff 0 = X i) :
    Derivation K (MvPolynomial ι K) (MvPolynomial ι K) :=
  Derivation.mk' (familySecondLinear hM) fun P Q => by
    set D := familyDerivOne hM
    have hD : ∀ a b : MvPolynomial ι K, D (a * b) = a * D b + b * D a := fun a b => by
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    have h1 : ∀ P : MvPolynomial ι K, familyCoeffOne M P = D P := fun _ => rfl
    have hsec : ∀ P : MvPolynomial ι K,
        familySecondLinear hM P = familyCoeffTwo M P - C (1 / 2 : K) * D (D P) := by
      intro P
      simp only [familySecondLinear, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.comp_apply, Derivation.coeFn_coe, smul_eq_C_mul]
      rfl
    rw [smul_eq_mul, smul_eq_mul, hsec, hsec, hsec, familyCoeffTwo_mul hM, h1, h1, hD, map_add,
      hD, hD]
    have h2 : (C (1 / 2 : K) : MvPolynomial ι K) * 2 = 1 := by
      rw [show (2 : MvPolynomial ι K) = C 2 from (map_ofNat C 2).symm, ← C_mul, one_div,
        inv_mul_cancel₀ (two_ne_zero' K), C_1]
    linear_combination (-(D P * D Q)) * h2

theorem familyDerivTwo_apply [CharZero K] (hM : ∀ i, (M i).coeff 0 = X i) (P : MvPolynomial ι K) :
    familyDerivTwo hM P
      = (familySubst M P).coeff 2 - (1 / 2 : K) • familyDerivOne hM (familyDerivOne hM P) := rfl

theorem familyDerivTwo_X [CharZero K] (hM : ∀ i, (M i).coeff 0 = X i) (i : ι) :
    familyDerivTwo hM (X i)
      = (M i).coeff 2 - (1 / 2 : K) • familyDerivOne hM ((M i).coeff 1) := by
  rw [familyDerivTwo_apply, familySubst_X, familyDerivOne_X]

/-- Evaluating the substituted polynomial at a parameter value is substitution by the evaluated
family. -/
theorem eval_familySubst (P : MvPolynomial ι K) (μ : K) :
    (familySubst M P).eval (C μ) = aeval (fun i => (M i).eval (C μ)) P := by
  have h := MvPolynomial.comp_aeval M
    ((Polynomial.aeval (C μ : MvPolynomial ι K)).restrictScalars K)
  have := congrArg (fun f => f P) h
  simpa [familySubst, Polynomial.coe_aeval_eq_eval] using this

/-- **Invariance at infinitely many parameters is invariance of the whole family.** -/
theorem familySubst_eq_C_of_infinite [Infinite K] {P : MvPolynomial ι K}
    (h : {μ : K | aeval (fun i => (M i).eval (C μ)) P = P}.Infinite) :
    familySubst M P = Polynomial.C P := by
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_infinite_isRoot _ ?_
  refine Set.Infinite.mono ?_ (h.image (C_injective ι K).injOn)
  rintro _ ⟨μ, hμ, rfl⟩
  show Polynomial.IsRoot _ _
  rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_C, eval_familySubst]
  exact sub_eq_zero.mpr hμ

/-- **An invariant of the family is killed by both derivations.** -/
theorem familyDeriv_eq_zero_of_eq_C [CharZero K] (hM : ∀ i, (M i).coeff 0 = X i)
    {P : MvPolynomial ι K} (h : familySubst M P = Polynomial.C P) :
    familyDerivOne hM P = 0 ∧ familyDerivTwo hM P = 0 := by
  have h1 : familyDerivOne hM P = 0 := by
    rw [familyDerivOne_apply, h, Polynomial.coeff_C, if_neg one_ne_zero]
  refine ⟨h1, ?_⟩
  rw [familyDerivTwo_apply, h, Polynomial.coeff_C, if_neg two_ne_zero, h1, map_zero, smul_zero,
    sub_zero]

end

end GaloisForLFunctions.HTGeometry
