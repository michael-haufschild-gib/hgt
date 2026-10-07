import GaloisForLFunctions.HTGeometry.AlgebraicFiniteJetBranch
import GaloisForLFunctions.HTGeometry.ABHN.RationalFunctionInversion
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Reciprocal parameter for a plane algebraic equation

Reflect every coefficient polynomial at a common degree `D`. This implements
`Q(t,Y)=t^D P(1/t,Y)` exactly. The field change `t ↦ 1/t` is an automorphism,
so generic irreducibility is retained. Constant-coordinate exclusions are
retained as well. This is classical algebra for a meromorphic chart at infinity.
-/

namespace GaloisForLFunctions.HTGeometry.AlgebraicReciprocalParameter

open Polynomial AlgebraicFiniteJetBranch
open scoped Topology

noncomputable section


/-- A common degree for reversing every coefficient polynomial. -/
def parameterDegree (P : BiPoly) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natDegree)

theorem coeff_natDegree_le_parameterDegree (P : BiPoly) (i : ℕ) :
    (P.coeff i).natDegree ≤ parameterDegree P := by
  classical
  by_cases hi : P.coeff i = 0
  · simp [hi]
  · exact Finset.le_sup (f := fun j => (P.coeff j).natDegree)
      (Polynomial.mem_support_iff.mpr hi)

/-- Clear the reciprocal parameter using one common power. -/
def reciprocalParameter (P : BiPoly) : BiPoly :=
  ∑ i ∈ P.support, C ((P.coeff i).reflect (parameterDegree P)) * X ^ i

theorem reciprocalParameter_coeff (P : BiPoly) (i : ℕ) :
    (reciprocalParameter P).coeff i = (P.coeff i).reflect (parameterDegree P) := by
  classical
  simp only [reciprocalParameter, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  by_cases hi : i ∈ P.support
  · simp [hi]
  · simp [hi, Polynomial.notMem_support_iff.mp hi]

theorem reciprocalParameter_support (P : BiPoly) :
    (reciprocalParameter P).support = P.support := by
  ext i
  simp only [Polynomial.mem_support_iff, reciprocalParameter_coeff, ne_eq,
    Polynomial.reflect_eq_zero_iff]

theorem eval₂_reflect_eq {K : Type*} [Field K] (φ : ℂ →+* K) (x : K) (hx : x ≠ 0)
    (p : Polynomial ℂ) (D : ℕ) (hD : p.natDegree ≤ D) :
    (p.reflect D).eval₂ φ x = x ^ D * p.eval₂ φ x⁻¹ := by
  letI : Invertible x⁻¹ := invertibleOfNonzero (inv_ne_zero hx)
  have h := Polynomial.eval₂_reflect_mul_pow φ x⁻¹ D p hD
  simp only [invOf_eq_inv, inv_inv, inv_pow] at h
  calc
    (p.reflect D).eval₂ φ x = ((p.reflect D).eval₂ φ x * (x ^ D)⁻¹) * x ^ D := by
      rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero D hx), mul_one]
    _ = p.eval₂ φ x⁻¹ * x ^ D := by rw [h]
    _ = x ^ D * p.eval₂ φ x⁻¹ := mul_comm _ _

/-- The exact reciprocal-parameter identity, away from its pole. -/
theorem evalAt_reciprocalParameter (P : BiPoly) (s w : ℂ) (hs : s ≠ 0) :
    evalAt (reciprocalParameter P) s w = s ^ parameterDegree P * evalAt P s⁻¹ w := by
  rw [evalAt_sum, reciprocalParameter_support, evalAt_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [reciprocalParameter_coeff]
  have he := eval₂_reflect_eq (RingHom.id ℂ) s hs (P.coeff i) (parameterDegree P)
    (coeff_natDegree_le_parameterDegree P i)
  simpa [Polynomial.coe_aeval_eq_eval, mul_assoc] using congrArg (fun a => a * w ^ i) he

theorem inversion_algebraMap (p : Polynomial ℂ) :
    ABHN.rationalFunctionInversionAlgEquiv ℂ (algebraMap (Polynomial ℂ) (RatFunc ℂ) p) =
      p.eval₂ RatFunc.C (RatFunc.X⁻¹ : RatFunc ℂ) := by
  let e := ABHN.rationalFunctionInversionAlgEquiv ℂ
  have he : e.toRingEquiv.toRingHom.comp (algebraMap (Polynomial ℂ) (RatFunc ℂ)) =
      Polynomial.eval₂RingHom RatFunc.C (RatFunc.X⁻¹ : RatFunc ℂ) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RatFunc.algebraMap_C, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_C]
      change e (algebraMap ℂ (RatFunc ℂ) a) = algebraMap ℂ (RatFunc ℂ) a
      exact e.commutes a
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_X]
      change e RatFunc.X = RatFunc.X⁻¹
      exact ABHN.rationalFunctionInversionAlgEquiv_X ℂ
  exact congrArg (fun f : Polynomial ℂ →+* RatFunc ℂ => f p) he

theorem map_reciprocalParameter (P : BiPoly) :
    (reciprocalParameter P).map (algebraMap (Polynomial ℂ) (RatFunc ℂ)) =
      C ((RatFunc.X : RatFunc ℂ) ^ parameterDegree P) *
        (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ))).map
          (ABHN.rationalFunctionInversionAlgEquiv ℂ).toRingEquiv.toRingHom := by
  apply Polynomial.ext
  intro i
  rw [Polynomial.coeff_map, reciprocalParameter_coeff, Polynomial.coeff_C_mul,
    Polynomial.coeff_map, Polynomial.coeff_map]
  change algebraMap (Polynomial ℂ) (RatFunc ℂ) _ =
    RatFunc.X ^ parameterDegree P * ABHN.rationalFunctionInversionAlgEquiv ℂ
      (algebraMap (Polynomial ℂ) (RatFunc ℂ) (P.coeff i))
  rw [inversion_algebraMap, ← RatFunc.aeval_X_left_eq_algebraMap]
  exact eval₂_reflect_eq RatFunc.C RatFunc.X RatFunc.X_ne_zero (P.coeff i)
    (parameterDegree P) (coeff_natDegree_le_parameterDegree P i)

/-- Reciprocal substitution preserves irreducibility over the parameter field. -/
theorem irreducible_map_reciprocalParameter (P : BiPoly)
    (hirr : Irreducible (P.map (algebraMap (Polynomial ℂ) (RatFunc ℂ)))) :
    Irreducible ((reciprocalParameter P).map (algebraMap (Polynomial ℂ) (RatFunc ℂ))) := by
  rw [map_reciprocalParameter]
  apply (irreducible_isUnit_mul
    ((isUnit_iff_ne_zero.mpr (pow_ne_zero _ RatFunc.X_ne_zero)).map Polynomial.C)).mpr
  exact (MulEquiv.irreducible_iff
    (Polynomial.mapAlgEquiv (ABHN.rationalFunctionInversionAlgEquiv ℂ))).mpr hirr

theorem reciprocalParameter_natDegree_pos (P : BiPoly) (hd : 0 < P.natDegree) :
    0 < (reciprocalParameter P).natDegree := by
  have hc : P.coeff P.natDegree ≠ 0 := by
    change P.leadingCoeff ≠ 0
    intro heq
    have hP := Polynomial.leadingCoeff_eq_zero.mp heq
    simp [hP] at hd
  have hcr : (reciprocalParameter P).coeff P.natDegree ≠ 0 := by
    simpa only [reciprocalParameter_coeff, ne_eq, Polynomial.reflect_eq_zero_iff] using hc
  exact lt_of_lt_of_le hd (Polynomial.le_natDegree_of_ne_zero hcr)

theorem reflect_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Polynomial ℂ) (D : ℕ) :
    (∑ i ∈ s, f i).reflect D = ∑ i ∈ s, (f i).reflect D := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp only [Finset.sum_insert ha, Polynomial.reflect_add, ih]

theorem reciprocalParameter_eval_C (P : BiPoly) (c : ℂ) :
    (reciprocalParameter P).eval (C c) = (P.eval (C c)).reflect (parameterDegree P) := by
  rw [Polynomial.eval_eq_sum, Polynomial.eval_eq_sum]
  simp only [Polynomial.sum_def, reciprocalParameter_support, reciprocalParameter_coeff]
  rw [reflect_finset_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← map_pow, mul_comm (P.coeff i), Polynomial.reflect_C_mul]
  exact mul_comm _ _

theorem reciprocalParameter_eval_C_ne_zero (P : BiPoly) (c : ℂ)
    (hc : P.eval (C c) ≠ 0) : (reciprocalParameter P).eval (C c) ≠ 0 := by
  simpa only [reciprocalParameter_eval_C, ne_eq, Polynomial.reflect_eq_zero_iff] using hc

end

end GaloisForLFunctions.HTGeometry.AlgebraicReciprocalParameter
