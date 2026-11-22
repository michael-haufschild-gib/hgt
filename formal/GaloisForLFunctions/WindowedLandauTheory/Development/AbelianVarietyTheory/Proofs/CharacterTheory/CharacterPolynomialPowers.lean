import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic.Ring

/-! Characteristic roots of powers of a matrix, with multiplicity. -/

open Polynomial

namespace GlobalTheory.CharpolyPow

variable {k : Type} [Field k] [IsAlgClosed k] {n : ℕ}

private theorem det_scalar_sub (M : Matrix (Fin n) (Fin n) k) (t : k) :
    (Matrix.scalar (Fin n) t - M).det = (M.charpoly.roots.map (fun z => t - z)).prod := by
  rw [← Matrix.eval_charpoly, ← prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (Matrix.charpoly_monic M) IsAlgClosed.card_roots_eq_natDegree,
    eval_multiset_prod, Multiset.map_map]
  simp

private theorem det_aeval_linear_factors (M : Matrix (Fin n) (Fin n) k) (s : Multiset k) :
    (aeval M (s.map (fun a => C a - X)).prod).det =
      (M.charpoly.roots.map (fun z => eval z (s.map (fun a => C a - X)).prod)).prod := by
  have factor (a : k) : (aeval M (C a - X)).det = (M.charpoly.roots.map (fun z => a - z)).prod := by
    rw [← det_scalar_sub]
    congr 1
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, map_mul, Matrix.det_mul, factor, ih, ← Multiset.prod_map_mul]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp

private theorem det_aeval (M : Matrix (Fin n) (Fin n) k) (q : k[X]) :
    (aeval M q).det = (M.charpoly.roots.map (fun z => eval z q)).prod := by
  let m := q.roots.card
  let c := q.leadingCoeff * (-1) ^ m
  have split : q = C c * (q.roots.map (fun a => C a - X)).prod := by
    have hneg : (q.roots.map (fun a => C a - X)).prod =
        (-1) ^ m * (q.roots.map (fun a => X - C a)).prod := by
      have hfactor : (fun a : k => C a - X) = fun a => (-1) * (X - C a) := by
        funext a
        ring
      rw [hfactor, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
    rw [hneg, show c = q.leadingCoeff * (-1) ^ m from rfl, C_mul, C_pow, C_neg, C_1]
    calc q = C q.leadingCoeff * (q.roots.map (fun a => X - C a)).prod :=
          (C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree).symm
      _ = C q.leadingCoeff * (-1) ^ m * ((-1) ^ m * (q.roots.map (fun a => X - C a)).prod) := by
        rw [← mul_assoc, mul_assoc (C q.leadingCoeff), ← pow_add, ← two_mul, pow_mul]
        simp
  have hcard : M.charpoly.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  conv_lhs => rw [split]
  conv_rhs => rw [split]
  rw [map_mul, aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, Matrix.det_smul,
    Fintype.card_fin, det_aeval_linear_factors]
  simp only [eval_mul, eval_C]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, hcard]

/-- Raising a matrix to the `r`-th power raises each characteristic root to the same power. -/
theorem roots_charpoly_pow (k : Type) [Field k] [IsAlgClosed k] (n r : ℕ)
    (M : Matrix (Fin n) (Fin n) k) :
    (Matrix.charpoly (M ^ r)).roots = M.charpoly.roots.map (· ^ r) := by
  letI : Infinite k := IsAlgClosed.instInfinite
  suffices h : (M ^ r).charpoly = ((M.charpoly.roots.map (· ^ r)).map fun a => X - C a).prod by
    rw [h, roots_multiset_prod_X_sub_C]
  apply Polynomial.funext
  intro t
  rw [Matrix.eval_charpoly, eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  have h : Matrix.scalar (Fin n) t - M ^ r = aeval M (C t - X ^ r) := by
    simp [Matrix.scalar, Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal]
  rw [h, det_aeval]
  simp [Function.comp_def]

end GlobalTheory.CharpolyPow
