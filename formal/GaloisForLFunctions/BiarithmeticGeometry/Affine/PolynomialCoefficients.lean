import GaloisForLFunctions.BiarithmeticGeometry.Affine.FiniteTranslationUnipotence
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Polynomial coefficients of rational affine representations

Rational translations in a finite-dimensional complex affine representation are unipotent.
Their scalar coefficients are Newton polynomials, of degree below the representation dimension.
Agreement on natural integers identifies the polynomials from all rational grids. Shifting the
linear observation extends the identity to negative rationals without any continuity assumption.
-/

open Polynomial Finset
open scoped Matrix
open GaloisForLFunctions.ArithmeticPositiveDuality
noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- Newton polynomial for a linear reading of powers of a unipotent element. -/
def unipotentPowerPolynomial (d : ℕ) (U : A) (L : A →ₗ[ℂ] ℂ) : ℂ[X] :=
  ∑ j ∈ range d, C (L ((U - 1) ^ j) / (j.factorial : ℂ)) * descPochhammer ℂ j

/-- Truncating the Newton expansion at `d` gives degree below `d`. -/
theorem unipotentPowerPolynomial_natDegree_lt (d : ℕ) (hd : 0 < d)
    (U : A) (L : A →ₗ[ℂ] ℂ) : (unipotentPowerPolynomial d U L).natDegree < d := by
  apply Nat.lt_of_le_of_lt _ (Nat.sub_lt hd (by omega : 0 < 1))
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (by rw [descPochhammer_natDegree]; exact Nat.le_sub_one_of_lt (mem_range.mp hj))

/-- Nilpotence truncates the binomial formula without changing any natural-power reading. -/
theorem unipotentPowerPolynomial_eval_nat (d : ℕ) (U : A) (L : A →ₗ[ℂ] ℂ)
    (hU : (U - 1) ^ d = 0) (n : ℕ) :
    (unipotentPowerPolynomial d U L).eval (n : ℂ) = L (U ^ n) := by
  have heval : (unipotentPowerPolynomial d U L).eval (n : ℂ) =
      ∑ j ∈ range d, (n.choose j : ℂ) * L ((U - 1) ^ j) := by
    simp only [unipotentPowerPolynomial, eval_finsetSum, eval_mul, eval_C]
    apply sum_congr rfl
    intro j _
    rw [Nat.cast_choose_eq_descPochhammer_div ℂ n j]
    ring
  have hpow : U ^ n = ∑ j ∈ range (n + 1), (n.choose j) • (U - 1) ^ j := by
    simpa only [sub_add_cancel, one_pow, mul_one, ← nsmul_eq_mul'] using
      (Commute.one_right (U - 1)).add_pow n
  have hread : L (U ^ n) =
      ∑ j ∈ range (n + 1), (n.choose j : ℂ) * L ((U - 1) ^ j) := by
    rw [hpow, map_sum]
    apply sum_congr rfl
    intro j _
    rw [map_nsmul, nsmul_eq_mul]
  rw [heval, hread]
  -- Terms beyond either truncation vanish by nilpotence or the binomial coefficient.
  rcases le_total d (n + 1) with hdn | hnd
  · apply sum_subset (range_mono hdn)
    intro j _ hj
    have hdj : d ≤ j := Nat.le_of_not_gt (fun h => hj (mem_range.mpr h))
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hdj
    rw [pow_add, hU, zero_mul, map_zero, mul_zero]
  · symm
    apply sum_subset (range_mono hnd)
    intro j _ hj
    have hnj : n < j := by
      have := Nat.le_of_not_gt (fun h => hj (mem_range.mpr h))
      omega
    rw [Nat.choose_eq_zero_of_lt hnj, Nat.cast_zero, zero_mul]

private theorem polynomial_eq_of_nat_evaluations (P Q : ℂ[X])
    (h : ∀ n : ℕ, P.eval (n : ℂ) = Q.eval (n : ℂ)) : P = Q := by
  apply P.eq_of_infinite_eval_eq Q
  apply (Set.infinite_range_of_injective
    (Nat.cast_injective : Function.Injective (fun n : ℕ => (n : ℂ)))).mono
  rintro x ⟨n, rfl⟩
  exact h n

omit [Algebra ℂ A] in
private theorem rational_curve_pow (f : ℚ → A) (h0 : f 0 = 1)
    (ha : ∀ a b, f (a + b) = f a * f b) (b : ℚ) (n : ℕ) :
    f b ^ n = f ((n : ℚ) * b) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, h0]
  | succ n ih =>
    rw [pow_succ, ih, ← ha]
    congr 1
    push_cast
    ring

private theorem unipotent_rational_coefficient_nonneg (d : ℕ)
    (f : ℚ → A) (h0 : f 0 = 1) (ha : ∀ a b, f (a + b) = f a * f b)
    (hnil : ∀ b, (f b - 1) ^ d = 0) (L : A →ₗ[ℂ] ℂ) (q : ℚ) (hq : 0 ≤ q) :
    (unipotentPowerPolynomial d (f 1) L).eval (q : ℂ) = L (f q) := by
  have hNat (b : ℚ) (n : ℕ) :
      (unipotentPowerPolynomial d (f b) L).eval (n : ℂ) = L (f ((n : ℚ) * b)) := by
    rw [unipotentPowerPolynomial_eval_nat d (f b) L (hnil b),
      rational_curve_pow f h0 ha]
  let m := q.den
  let n := q.num.toNat
  have hm : m ≠ 0 := Nat.ne_of_gt q.den_pos
  have hmQ : (m : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  have hn : (n : ℚ) = (q.num : ℚ) := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr hq)
  have hqm : q = (n : ℚ) / (m : ℚ) := by
    rw [hn]
    exact (Rat.num_div_den q).symm
  let Q := (unipotentPowerPolynomial d (f ((m : ℚ)⁻¹)) L).comp (C (m : ℂ) * X)
  -- The denominator grid and the unit grid agree at every natural integer.
  have hpoly : Q = unipotentPowerPolynomial d (f 1) L := by
    apply polynomial_eq_of_nat_evaluations
    intro a
    change ((unipotentPowerPolynomial d (f ((m : ℚ)⁻¹)) L).comp
      (C (m : ℂ) * X)).eval (a : ℂ) = _
    rw [eval_comp, eval_mul, eval_C, eval_X, ← Nat.cast_mul, hNat, hNat]
    congr 2
    push_cast
    rw [mul_one]
    calc
      (m : ℚ) * a * (m : ℚ)⁻¹ = ((m : ℚ) * (m : ℚ)⁻¹) * a := by ring
      _ = a := by rw [mul_inv_cancel₀ hmQ, one_mul]
  have hmulQ : (m : ℚ) * q = n := by
    rw [hqm, div_eq_mul_inv]
    calc
      (m : ℚ) * ((n : ℚ) * (m : ℚ)⁻¹) = ((m : ℚ) * (m : ℚ)⁻¹) * n := by ring
      _ = n := by rw [mul_inv_cancel₀ hmQ, one_mul]
  have hmulC : (m : ℂ) * (q : ℂ) = n := by exact_mod_cast hmulQ
  rw [← hpoly]
  change ((unipotentPowerPolynomial d (f ((m : ℚ)⁻¹)) L).comp
    (C (m : ℂ) * X)).eval (q : ℂ) = _
  rw [eval_comp, eval_mul, eval_C, eval_X, hmulC, hNat]
  congr 2
  exact (hqm.trans (div_eq_mul_inv _ _)).symm

/-- A uniformly unipotent rational one-parameter group has polynomial linear coefficients. -/
theorem unipotent_rational_coefficient (d : ℕ)
    (f : ℚ → A) (h0 : f 0 = 1) (ha : ∀ a b, f (a + b) = f a * f b)
    (hnil : ∀ b, (f b - 1) ^ d = 0) (L : A →ₗ[ℂ] ℂ) (q : ℚ) :
    (unipotentPowerPolynomial d (f 1) L).eval (q : ℂ) = L (f q) := by
  let Lq : A →ₗ[ℂ] ℂ :=
    { toFun := fun a => L (a * f q)
      map_add' a b := by rw [add_mul, map_add]
      map_smul' c a := by simp only [smul_mul_assoc, map_smul, RingHom.id_apply] }
  let P := unipotentPowerPolynomial d (f 1) L
  let Q := unipotentPowerPolynomial d (f 1) Lq
  obtain ⟨N, hN⟩ := exists_nat_ge (-q)
  -- A common nonnegative tail identifies the shifted observation polynomial.
  have hpoly : Q = P.comp (X + C (q : ℂ)) := by
    apply Q.eq_of_infinite_eval_eq
    have hi : Function.Injective (fun n : ℕ => ((n + N : ℕ) : ℂ)) := by
      intro a b hab
      exact Nat.add_right_cancel (Nat.cast_injective hab)
    apply (Set.infinite_range_of_injective hi).mono
    rintro x ⟨n, rfl⟩
    have hp : 0 ≤ ((n + N : ℕ) : ℚ) + q := by
      have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      push_cast
      linarith only [hN, hn]
    have hleft := unipotent_rational_coefficient_nonneg d f h0 ha hnil Lq
      ((n + N : ℕ) : ℚ) (Nat.cast_nonneg _)
    have hright := unipotent_rational_coefficient_nonneg d f h0 ha hnil L
      (((n + N : ℕ) : ℚ) + q) hp
    have he : Lq (f ((n + N : ℕ) : ℚ)) = L (f (((n + N : ℕ) : ℚ) + q)) := by
      change L (f ((n + N : ℕ) : ℚ) * f q) = _
      rw [← ha]
    simpa only [Set.mem_setOf_eq, P, Q, eval_comp, eval_add, eval_X, eval_C,
      Rat.cast_add, Rat.cast_natCast] using hleft.trans (he.trans hright.symm)
  have he := congrArg (fun p : ℂ[X] => p.eval 0) hpoly
  simp only [eval_comp, eval_add, eval_X, eval_C, zero_add] at he
  have hzero := unipotentPowerPolynomial_eval_nat d (f 1) Lq (hnil 1) 0
  simp only [Nat.cast_zero, pow_zero] at hzero
  change Q.eval 0 = L (1 * f q) at hzero
  rw [one_mul] at hzero
  exact he.symm.trans hzero

/-- Rational translations act unipotently on every finite-dimensional complex affine module. -/
theorem finite_rational_affine_end_translation_unipotent
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : AffineGroupQ →* Module.End ℂ V) (b : ℚ) :
    (ρ (translation b) - 1) ^ Module.finrank ℂ V = 0 := by
  let e := LinearMap.toMatrixAlgEquiv (Module.finBasis ℂ V)
  let σ : AffineGroupQ →*
      Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ :=
    { toFun := fun g => e (ρ g)
      map_one' := by rw [map_one, map_one]
      map_mul' a b := by rw [map_mul, map_mul] }
  have hσ : (e (ρ (translation b)) - 1) ^ Module.finrank ℂ V = 0 :=
    finite_rational_affine_translation_unipotent σ b
  apply e.injective
  simpa only [map_pow, map_sub, map_one, map_zero] using hσ

/-- Every scalar reading of rational translations in a finite affine module is polynomial. -/
theorem exists_polynomial_affine_translation_coefficient
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Module.Finite ℂ V]
    (ρ : AffineGroupQ →* Module.End ℂ V) (L : Module.End ℂ V →ₗ[ℂ] ℂ)
    (hd : 0 < Module.finrank ℂ V) :
    ∃ P : ℂ[X], P.natDegree < Module.finrank ℂ V ∧
      ∀ b : ℚ, P.eval (b : ℂ) = L (ρ (translation b)) := by
  refine ⟨unipotentPowerPolynomial (Module.finrank ℂ V) (ρ (translation 1)) L,
    unipotentPowerPolynomial_natDegree_lt _ hd _ _, fun b => ?_⟩
  exact unipotent_rational_coefficient (Module.finrank ℂ V)
    (fun q => ρ (translation q)) (by rw [translation_zero, map_one])
    (by intro a b; rw [translation_add, map_mul])
    (finite_rational_affine_end_translation_unipotent ρ) L b

#print axioms unipotentPowerPolynomial_natDegree_lt
#print axioms unipotentPowerPolynomial_eval_nat
#print axioms unipotent_rational_coefficient
#print axioms finite_rational_affine_end_translation_unipotent
#print axioms exists_polynomial_affine_translation_coefficient
end GaloisForLFunctions.BiarithmeticGeometry
