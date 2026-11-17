import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeReflectionHull
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# A Hecke specialization on the actual reflection hull

On the finite reflection hull, `T(q)=q² P₊-P₋` satisfies the rank-one Hecke
relation with parameter `q²`. Its character is the specialization of one
polynomial, and its zero specialization retains precisely the negative
sector. This realizes the free-family character specialization mechanism
of Kim--Lee--Oh, arXiv:2611.20790, Remark 3.2 and Theorem 3.7, for `S₂`.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open _root_.Polynomial
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})

/-- The fixed and odd reflection projectors have disjoint images. -/
theorem hullPositive_mul_hullNegative : hullPositive p * hullNegative p = 0 := by
  unfold hullPositive hullNegative
  simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_sub,
    one_mul, mul_one, hullReflection_sq]
  module

theorem hullNegative_mul_hullPositive : hullNegative p * hullPositive p = 0 := by
  unfold hullPositive hullNegative
  simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_add,
    one_mul, mul_one, hullReflection_sq]
  module

/-- A polynomial family of rank-one Hecke actions on the actual finite probe hull. -/
def hullHecke (q : ℂ) : Module.End ℂ (reflectionHull p) :=
  q ^ 2 • hullPositive p - hullNegative p

/-- The quadratic relation of the Hecke algebra of `S₂`, for every specialization. -/
theorem hullHecke_quadratic (q : ℂ) :
    hullHecke p q * hullHecke p q =
      (q ^ 2 - 1) • hullHecke p q + q ^ 2 • 1 := by
  have hp : hullPositive p * hullPositive p = hullPositive p := hullPositive_idempotent p
  have hn : hullNegative p * hullNegative p = hullNegative p := hullNegative_idempotent p
  rw [← hullPositive_add_hullNegative p]
  simp only [hullHecke, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
    hullPositive_mul_hullNegative, hullNegative_mul_hullPositive,
    smul_zero, sub_zero, zero_sub, hp, hn]
  module

theorem hullHecke_zero : hullHecke p 0 = -hullNegative p := by
  simp only [hullHecke, zero_pow (by omega : 2 ≠ 0), zero_smul, zero_sub]

/-- At parameter one the Hecke action is the actual zeta-zero reflection. -/
theorem hullHecke_one : hullHecke p 1 = hullReflection p := by
  simp only [hullHecke, one_pow, one_smul, hullPositive, hullNegative]
  module

/-- The free family's character specializes with constant sector multiplicities. -/
theorem hullHecke_character (q : ℂ) :
    LinearMap.trace ℂ (reflectionHull p) (hullHecke p q) =
      q ^ 2 * (Module.finrank ℂ (LinearMap.range (hullPositive p)) : ℂ) -
        (Module.finrank ℂ (LinearMap.range (hullNegative p)) : ℂ) := by
  rw [hullHecke, map_sub, map_smul,
    (LinearMap.IsIdempotentElem.isProj_range _ (hullPositive_idempotent p)).trace,
    (LinearMap.IsIdempotentElem.isProj_range _ (hullNegative_idempotent p)).trace,
    smul_eq_mul]

/-- All powers retain the same two sector multiplicities, including the zero specialization. -/
theorem hullHecke_pow (q : ℂ) (n : ℕ) :
    hullHecke p q ^ n = (q ^ 2) ^ n • hullPositive p + (-1 : ℂ) ^ n • hullNegative p := by
  induction n with
  | zero => simpa only [pow_zero, one_smul] using (hullPositive_add_hullNegative p).symm
  | succ n ih =>
    have hp : hullPositive p * hullPositive p = hullPositive p := hullPositive_idempotent p
    have hn : hullNegative p * hullNegative p = hullNegative p := hullNegative_idempotent p
    rw [pow_succ, ih, hullHecke]
    simp only [add_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      hullPositive_mul_hullNegative, hullNegative_mul_hullPositive,
      smul_zero, hp, hn, pow_succ]
    module

/-- Every polynomial in the Hecke generator is evaluated separately on its two sectors. -/
theorem hullHecke_polynomial (q : ℂ) (f : _root_.Polynomial ℂ) :
    aeval (hullHecke p q) f =
      f.eval (q ^ 2) • hullPositive p + f.eval (-1) • hullNegative p := by
  induction f using _root_.Polynomial.induction_on' with
  | add f g hf hg =>
    simp only [map_add, hf, hg, eval_add, add_smul]
    abel
  | monomial n a =>
    rw [aeval_monomial, ← Algebra.smul_def, hullHecke_pow]
    simp only [eval_monomial, smul_add, smul_smul]

/-- Character specialization holds for every polynomial Hecke observable. -/
theorem hullHecke_polynomial_character (q : ℂ) (f : _root_.Polynomial ℂ) :
    LinearMap.trace ℂ (reflectionHull p) (aeval (hullHecke p q) f) =
      f.eval (q ^ 2) * (Module.finrank ℂ (LinearMap.range (hullPositive p)) : ℂ) +
        f.eval (-1) * (Module.finrank ℂ (LinearMap.range (hullNegative p)) : ℂ) := by
  rw [hullHecke_polynomial, map_add, map_smul, map_smul,
    (LinearMap.IsIdempotentElem.isProj_range _ (hullPositive_idempotent p)).trace,
    (LinearMap.IsIdempotentElem.isProj_range _ (hullNegative_idempotent p)).trace]
  rfl

/-- The zero-Hecke kernel is exactly the genuine reflection-fixed sector. -/
theorem hullHecke_zero_kernel :
    LinearMap.ker (hullHecke p 0) = LinearMap.range (hullPositive p) := by
  rw [hullHecke_zero]
  ext x
  constructor
  · intro hx
    have hn : hullNegative p x = 0 := by
      simpa only [LinearMap.mem_ker, LinearMap.neg_apply, neg_eq_zero] using hx
    refine ⟨x, ?_⟩
    have h := congrArg (fun T : Module.End ℂ (reflectionHull p) => T x)
      (hullPositive_add_hullNegative p)
    simpa only [LinearMap.add_apply, Module.End.one_apply, hn, add_zero] using h
  · rintro ⟨y, rfl⟩
    change -(hullNegative p (hullPositive p y)) = 0
    have h := congrArg (fun T : Module.End ℂ (reflectionHull p) => T y)
      (hullNegative_mul_hullPositive p)
    simpa only [Module.End.mul_apply, LinearMap.zero_apply, neg_eq_zero] using h

/-- The zero specialization has precisely the negative reflection sector as its image. -/
theorem hullHecke_zero_range :
    LinearMap.range (hullHecke p 0) = LinearMap.range (hullNegative p) := by
  rw [hullHecke_zero]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨-y, by simp only [map_neg, LinearMap.neg_apply]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨-y, by simp only [map_neg, LinearMap.neg_apply, neg_neg]⟩

#print axioms hullHecke_quadratic
#print axioms hullHecke_character
#print axioms hullHecke_polynomial
#print axioms hullHecke_polynomial_character
#print axioms hullHecke_zero_kernel
#print axioms hullHecke_zero_range

end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
