import GaloisForLFunctions.RHTower.LiArithmeticProgressionSquareSourceCriterion
import GaloisForLFunctions.HTGeometry.PolynomialDistinctDegree

/-!
# Reflection quotient and blindness of the even Li square family

Even-Li source polynomials are invariant under hard-edge reflection. They are linearly
independent, so they give genuine coordinates in the reflection-even quotient.

The quotient is essential. A nonzero reflection-odd signed moment functional annihilates every
even-Li square while taking a negative value on another literal hard-edge weighted square.
Therefore the LI diagonal cannot imply the full hard-edge Hankel square cone by generic moment
algebra or generic adaptive-contact transfer. A successful proof must use arithmetic structure of
the actual completed prime--Gamma functional inside the reflection-even quotient.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- Hard-edge reflection on complex polynomials. -/
def liHardEdgeReflection (P : Polynomial ℂ) : Polynomial ℂ :=
  P.comp (C 4 - X)

/-- Hard-edge reflection is an involution. -/
theorem liHardEdgeReflection_involutive (P : Polynomial ℂ) :
    liHardEdgeReflection (liHardEdgeReflection P) = P := by
  rw [liHardEdgeReflection, liHardEdgeReflection, Polynomial.comp_assoc]
  have hinner : (C 4 - X : Polynomial ℂ).comp (C 4 - X) = X := by
    simp [Polynomial.sub_comp]
  rw [hinner, Polynomial.comp_X]

/-- Every even-LI weighted square lies in the reflection-even quotient. -/
theorem liHardEdgeReflection_liEvenShiftedSquarePolynomial (n : ℕ) :
    liHardEdgeReflection (liEvenShiftedSquarePolynomial n) =
      liEvenShiftedSquarePolynomial n := by
  apply Polynomial.funext
  intro x
  rw [liHardEdgeReflection, Polynomial.eval_comp]
  simp only [liEvenShiftedSquarePolynomial, Polynomial.eval_mul,
    Polynomial.eval_X, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_comp]
  have hreflect : 1 - 1 / 2 * (4 - x) = -(1 - 1 / 2 * x) := by ring
  rw [hreflect, Polynomial.Chebyshev.U_eval_neg]
  rw [mul_pow]
  have hsign : (((n : ℤ).negOnePow : ℤ) : ℂ) ^ (2 : ℕ) = 1 := by
    rcases Int.units_eq_one_or (n : ℤ).negOnePow with h | h
    · rw [h]
      norm_num
    · rw [h]
      norm_num
  rw [hsign, one_mul]
  ring

/-- Difference of evaluations at a reflected hard-edge pair: a signed two-atom moment
functional in the reflection-odd dual sector. -/
def liHardEdgeReflectionBlindFunctional (a : ℝ) : Polynomial ℂ →ₗ[ℝ] ℝ where
  toFun P := (P.eval (a : ℂ)).re - (P.eval ((4 - a : ℝ) : ℂ)).re
  map_add' P Q := by simp; ring
  map_smul' r P := by simp [smul_eq_mul]; ring

/-- Every reflection-invariant polynomial is invisible to a reflected two-atom difference. -/
theorem liHardEdgeReflectionBlindFunctional_eq_zero_of_invariant
    {a : ℝ} {P : Polynomial ℂ} (hP : liHardEdgeReflection P = P) :
    liHardEdgeReflectionBlindFunctional a P = 0 := by
  have h := congrArg (fun Q : Polynomial ℂ => Q.eval (a : ℂ)) hP
  simp only [liHardEdgeReflection, Polynomial.eval_comp, Polynomial.eval_sub,
    Polynomial.eval_C, Polynomial.eval_X] at h
  change (P.eval (a : ℂ)).re - (P.eval ((4 - a : ℝ) : ℂ)).re = 0
  have hre := congrArg Complex.re h
  apply sub_eq_zero.mpr
  simpa using hre.symm

/-- The entire even-LI square family is blind to every reflected two-atom difference. -/
theorem liHardEdgeReflectionBlindFunctional_liEvenShiftedSquarePolynomial
    (a : ℝ) (n : ℕ) :
    liHardEdgeReflectionBlindFunctional a (liEvenShiftedSquarePolynomial n) = 0 :=
  liHardEdgeReflectionBlindFunctional_eq_zero_of_invariant
    (liHardEdgeReflection_liEvenShiftedSquarePolynomial n)

/-- Another literal hard-edge weighted square, exposing the blind sector. -/
def liHardEdgeWeightedSquareWitness : Polynomial ℂ :=
  X * (C 4 - X) * X ^ (2 : ℕ)

/-- The reflected pair at one and three sees the witness with negative orientation. -/
theorem liHardEdgeReflectionBlindFunctional_weightedSquareWitness_neg :
    liHardEdgeReflectionBlindFunctional 1 liHardEdgeWeightedSquareWitness < 0 := by
  norm_num [liHardEdgeReflectionBlindFunctional, liHardEdgeWeightedSquareWitness]

/-- **Full-cone transfer no-go.** Nonnegativity on every even-LI weighted square does not imply
nonnegativity on all hard-edge weighted squares for a generic signed moment functional. -/
theorem exists_liEvenSquare_nonnegative_blindFunctional_not_hardEdgeSquare_nonnegative :
    ∃ L : Polynomial ℂ →ₗ[ℝ] ℝ,
      (∀ n : ℕ, 0 ≤ L (liEvenShiftedSquarePolynomial n)) ∧
        L liHardEdgeWeightedSquareWitness < 0 := by
  refine ⟨liHardEdgeReflectionBlindFunctional 1, ?_,
    liHardEdgeReflectionBlindFunctional_weightedSquareWitness_neg⟩
  intro n
  rw [liHardEdgeReflectionBlindFunctional_liEvenShiftedSquarePolynomial]

private theorem liEvenShiftedSquarePolynomial_inner_natDegree :
    (C 1 - C (1 / 2 : ℂ) * X).natDegree = 1 := by
  have hform : (C 1 - C (1 / 2 : ℂ) * X : Polynomial ℂ) =
      -(C (1 / 2 : ℂ) * X) + C 1 := by ring
  rw [hform, Polynomial.natDegree_add_C, Polynomial.natDegree_neg,
    Polynomial.natDegree_C_mul_X]
  norm_num

private theorem liEvenShiftedSquarePolynomial_outer_natDegree :
    (X * (C 4 - X) : Polynomial ℂ).natDegree = 2 := by
  have hsub : (C 4 - X : Polynomial ℂ) = -X + C 4 := by ring
  have hsubdeg : (C 4 - X : Polynomial ℂ).natDegree = 1 := by
    rw [hsub, Polynomial.natDegree_add_C, Polynomial.natDegree_neg,
      Polynomial.natDegree_X]
  have hX : (X : Polynomial ℂ) ≠ 0 := Polynomial.X_ne_zero
  have hsubne : (C 4 - X : Polynomial ℂ) ≠ 0 := by
    intro h
    have hc := congrArg (fun P : Polynomial ℂ => P.coeff 1) h
    norm_num at hc
  rw [Polynomial.natDegree_mul hX hsubne, Polynomial.natDegree_X, hsubdeg]

/-- Exact degree of the n-th even-LI hard-edge square. -/
theorem natDegree_liEvenShiftedSquarePolynomial (n : ℕ) :
    (liEvenShiftedSquarePolynomial n).natDegree = 2 * (n + 1) := by
  let U : Polynomial ℂ := Polynomial.Chebyshev.U ℂ (n : ℤ)
  let A : Polynomial ℂ := C 1 - C (1 / 2) * X
  have hU : U ≠ 0 := by
    intro hz
    have hz' := (Polynomial.Chebyshev.U_eq_zero_iff ℂ (n : ℤ)).mp (by
      simpa only [U] using hz)
    omega
  have hAdeg : A.natDegree = 1 := by
    exact liEvenShiftedSquarePolynomial_inner_natDegree
  have hAneC : A ≠ C (A.coeff 0) := by
    intro h
    have hc := congrArg (fun P : Polynomial ℂ => P.coeff 1) h
    dsimp only [A] at hc
    norm_num at hc
  have hcomp : U.comp A ≠ 0 := by
    intro hz
    rcases Polynomial.comp_eq_zero_iff.mp hz with hUzero | ⟨_, hAconst⟩
    · exact hU hUzero
    · exact hAneC hAconst
  have hUdeg : U.natDegree = n := by
    dsimp only [U]
    rw [Polynomial.Chebyshev.natDegree_U]
    have hcast : (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) := by omega
    calc
      ((n : ℤ) + 1).natAbs - 1 = (n + 1) - 1 := by rw [hcast]; rfl
      _ = n := by omega
  have hcompdeg : (U.comp A).natDegree = n := by
    rw [Polynomial.natDegree_comp, hUdeg, hAdeg, mul_one]
  have houterne : (X * (C 4 - X) : Polynomial ℂ) ≠ 0 := by
    apply mul_ne_zero Polynomial.X_ne_zero
    intro h
    have hc := congrArg (fun P : Polynomial ℂ => P.coeff 1) h
    norm_num at hc
  rw [liEvenShiftedSquarePolynomial]
  change (X * (C 4 - X) * (U.comp A) ^ (2 : ℕ)).natDegree = _
  rw [Polynomial.natDegree_mul houterne (pow_ne_zero 2 hcomp),
    liEvenShiftedSquarePolynomial_outer_natDegree,
    Polynomial.natDegree_pow, hcompdeg]
  omega

/-- Finite initial segments are linearly independent: reflection quotienting removes a blind
sector but introduces no redundancy among surviving LI coordinates. -/
theorem linearIndependent_liEvenShiftedSquarePolynomial (N : ℕ) :
    LinearIndependent ℂ (fun n : Fin N => liEvenShiftedSquarePolynomial n) := by
  apply GaloisForLFunctions.linearIndependent_of_natDegree_injective
  · intro n hzero
    have hdeg := natDegree_liEvenShiftedSquarePolynomial n
    rw [hzero, Polynomial.natDegree_zero] at hdeg
    omega
  · intro i j hij
    change (liEvenShiftedSquarePolynomial (i : ℕ)).natDegree =
      (liEvenShiftedSquarePolynomial (j : ℕ)).natDegree at hij
    rw [natDegree_liEvenShiftedSquarePolynomial,
      natDegree_liEvenShiftedSquarePolynomial] at hij
    apply Fin.ext
    omega

end

end RHTower
