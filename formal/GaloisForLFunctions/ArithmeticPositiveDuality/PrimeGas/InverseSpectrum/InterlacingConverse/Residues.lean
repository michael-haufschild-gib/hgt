import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-! # Residue probabilities for a prescribed interlacing finite spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Finset Polynomial Lagrange

/-- The probability of the original level i in the missing vector determined by a prescribed spectrum. -/
def residueMass {m : ℕ} (a : Fin (m+1) → ℝ) (b : Fin m → ℝ) (i : Fin (m+1)) : ℝ :=
  (∏ j, (a i-b j)) / ∏ k ∈ univ.erase i, (a i-a k)

private theorem erase_product {m : ℕ} (a : Fin (m+1) → ℝ) (i : Fin (m+1)) :
    (∏ k ∈ univ.erase i, (a i-a k)) = ∏ j : Fin m, (a i-a (i.succAbove j)) := by
  have he : univ.erase i = univ.map i.succAboveEmb := by
    conv_lhs => rw [Fin.univ_succAbove m i]
    simp
  rw [he,Finset.prod_map]
  rfl

theorem node_ne_gap {m : ℕ} {a : Fin (m+1) → ℝ} (ha : StrictAnti a) {b : Fin m → ℝ}
    (hb : ∀ j, a j.succ < b j ∧ b j < a j.castSucc) (i : Fin (m+1)) (j : Fin m) : a i ≠ b j := by
  by_cases h : i ≤ j.castSucc
  · exact ((hb j).2.trans_le (ha.antitone h)).ne'
  · have h' : j.succ ≤ i := Nat.succ_le_of_lt (lt_of_not_ge h : (j:ℕ) < i.val)
    exact ((ha.antitone h').trans_lt (hb j).1).ne

/-- Pair numerator and denominator factors past the omitted index to see positivity one factor at a time. -/
theorem residueMass_pos {m : ℕ} {a : Fin (m+1) → ℝ} (ha : StrictAnti a) {b : Fin m → ℝ}
    (hb : ∀ j, a j.succ < b j ∧ b j < a j.castSucc) (i : Fin (m+1)) : 0 < residueMass a b i := by
  rw [residueMass,erase_product,← Finset.prod_div_distrib]
  apply Finset.prod_pos
  intro j _
  by_cases h : i ≤ j.castSucc
  · rw [Fin.succAbove_of_le_castSucc _ _ h]
    have hi : i < j.succ := Nat.lt_succ_of_le h
    exact div_pos (sub_pos.mpr ((hb j).2.trans_le (ha.antitone h))) (sub_pos.mpr (ha hi))
  · have hi : j.castSucc < i := lt_of_not_ge h
    have hj : j.succ ≤ i := Nat.succ_le_of_lt hi
    rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    exact div_pos_of_neg_of_neg (sub_neg.mpr ((ha.antitone hj).trans_lt (hb j).1)) (sub_neg.mpr (ha hi))

/-- The leading coefficient of the interpolated monic polynomial gives total mass one. -/
theorem sum_residueMass {m : ℕ} {a : Fin (m+1) → ℝ} (ha : Function.Injective a) (b : Fin m → ℝ) :
    ∑ i, residueMass a b i = 1 := by
  let P := nodal univ b
  have hd : (↑(univ : Finset (Fin (m+1))).card : WithBot ℕ) = P.degree+1 := by
    simp [P,degree_nodal]
  have he := leadingCoeff_eq_sum ha.injOn hd
  have hP : P.Monic := nodal_monic
  rw [show P.leadingCoeff = 1 from hP] at he
  simpa only [residueMass,P,eval_nodal] using he.symm

/-- At each prescribed eigenvalue the Cauchy transform of the original occupation probabilities vanishes. -/
theorem residueMass_secular {m : ℕ} {a : Fin (m+1) → ℝ} (ha : StrictAnti a) {b : Fin m → ℝ}
    (hb : ∀ j, a j.succ < b j ∧ b j < a j.castSucc) (j : Fin m) :
    ∑ i, residueMass a b i / (a i-b j) = 0 := by
  let P := nodal univ b
  have hd : P.degree < ↑(univ : Finset (Fin (m+1))).card := by
    simp only [P,degree_nodal,card_univ,Fintype.card_fin]
    exact WithBot.coe_lt_coe.mpr (Nat.lt_succ_self m)
  have he := eq_interpolate (s := univ) ha.injective.injOn hd
  have hx (i : Fin (m+1)) (_ : i ∈ univ) : b j ≠ a i := (node_ne_gap ha hb i j).symm
  have hf := eval_interpolate_not_at_node (s := univ) (v := a) (fun i => P.eval (a i)) hx
  rw [← he,show P.eval (b j) = 0 from eval_nodal_at_node (mem_univ j)] at hf
  have hs := eq_zero_of_ne_zero_of_mul_left_eq_zero (eval_nodal_not_at_node hx) hf.symm
  have hterm (i : Fin (m+1)) : nodalWeight univ a i*(b j-a i)⁻¹*P.eval (a i) =
      -(residueMass a b i/(a i-b j)) := by
    rw [nodalWeight_eq_eval_nodal_erase_inv,eval_nodal,show P.eval (a i) = _ from eval_nodal]
    rw [← neg_sub (a i) (b j),inv_neg,residueMass]
    ring
  simpa only [hterm,Finset.sum_neg_distrib,neg_eq_zero] using hs

#print axioms residueMass_pos
#print axioms sum_residueMass
#print axioms residueMass_secular

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
