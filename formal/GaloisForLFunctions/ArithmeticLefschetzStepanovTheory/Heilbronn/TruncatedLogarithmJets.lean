import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import GaloisForLFunctions.HTGeometry.GammaShiftConfluentCasoratian

/-!
# Nonvanishing for the truncated logarithm

For the characteristic-p logarithm L, the operator D=(1-X)d/dX satisfies
DL=1-X^(p-1). Below order p, the jets of (1-X)^a L^b are confluent
Vandermonde entries at -a. Thus AB≤p makes these modes independent
modulo X^p, and independent over the polynomial ring in X^p.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

/-- The finite logarithm ∑_{1≤j<p} X^j/j in characteristic p. -/
noncomputable def truncatedLog (K : Type*) [Field K] (p : ℕ) : K[X] :=
  ∑ i ∈ range (p - 1), C (((i + 1 : ℕ) : K)⁻¹) * X ^ (i + 1)

theorem truncatedLog_derivative {K : Type*} [Field K] {p : ℕ} [CharP K p] :
    (truncatedLog K p).derivative = ∑ i ∈ range (p - 1), (X : K[X]) ^ i := by
  unfold truncatedLog
  rw [derivative_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i + 1 < p := by have := mem_range.mp hi; omega
  have hne : ((i + 1 : ℕ) : K) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff K p]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hi'
  rw [derivative_C_mul, derivative_X_pow]
  simp only [Nat.add_sub_cancel, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hne, C_1, one_mul]

theorem truncatedLog_weighted_derivative {K : Type*} [Field K] {p : ℕ} [CharP K p] :
    (1 - X) * (truncatedLog K p).derivative = 1 - X ^ (p - 1) := by
  rw [truncatedLog_derivative, mul_comm]
  exact geom_sum_mul_neg X (p - 1)

/-- The vector field (1-X)d/dX, adapted to the logarithmic coordinate. -/
noncomputable def logarithmicEuler {K : Type*} [CommRing K] (P : K[X]) : K[X] :=
  (1 - X) * P.derivative

theorem logarithmicEuler_add {K : Type*} [CommRing K] (P Q : K[X]) :
    logarithmicEuler (P + Q) = logarithmicEuler P + logarithmicEuler Q := by
  simp only [logarithmicEuler, derivative_add, mul_add]

theorem logarithmicEuler_sub {K : Type*} [CommRing K] (P Q : K[X]) :
    logarithmicEuler (P - Q) = logarithmicEuler P - logarithmicEuler Q := by
  simp only [logarithmicEuler, derivative_sub, mul_sub]

theorem logarithmicEuler_C_mul {K : Type*} [CommRing K] (c : K) (P : K[X]) :
    logarithmicEuler (C c * P) = C c * logarithmicEuler P := by
  rw [logarithmicEuler, derivative_C_mul, logarithmicEuler]
  ring

theorem logarithmicEuler_sum {K α : Type*} [CommRing K] (s : Finset α) (f : α → K[X]) :
    logarithmicEuler (∑ i ∈ s, f i) = ∑ i ∈ s, logarithmicEuler (f i) := by
  simp only [logarithmicEuler, derivative_sum, Finset.mul_sum]

theorem logarithmicEuler_dvd {K : Type*} [CommRing K] (n : ℕ) {P : K[X]}
    (h : X ^ (n + 1) ∣ P) : X ^ n ∣ logarithmicEuler P := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨(1 - X) * (C (n + 1 : K) * Q + X * Q.derivative), ?_⟩
  rw [logarithmicEuler, derivative_mul, derivative_X_pow]
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, pow_succ]
  ring

theorem logarithmicEuler_iterate_add {K : Type*} [CommRing K] (n : ℕ) (P Q : K[X]) :
    logarithmicEuler^[n] (P + Q) = logarithmicEuler^[n] P + logarithmicEuler^[n] Q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, logarithmicEuler_add,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem logarithmicEuler_iterate_C_mul {K : Type*} [CommRing K] (n : ℕ) (c : K) (P : K[X]) :
    logarithmicEuler^[n] (C c * P) = C c * logarithmicEuler^[n] P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, logarithmicEuler_C_mul,
      Function.iterate_succ_apply']

theorem logarithmicEuler_iterate_sub {K : Type*} [CommRing K] (n : ℕ) (P Q : K[X]) :
    logarithmicEuler^[n] (P - Q) = logarithmicEuler^[n] P - logarithmicEuler^[n] Q := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, logarithmicEuler_sub,
      Function.iterate_succ_apply', Function.iterate_succ_apply']

theorem logarithmicEuler_iterate_sum {K α : Type*} [CommRing K] (n : ℕ)
    (s : Finset α) (f : α → K[X]) :
    logarithmicEuler^[n] (∑ i ∈ s, f i) = ∑ i ∈ s, logarithmicEuler^[n] (f i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, logarithmicEuler_sum]
    simp only [Function.iterate_succ_apply']

theorem logarithmicEuler_iterate_dvd {K : Type*} [CommRing K] (m n : ℕ) {P : K[X]}
    (h : X ^ (m + n) ∣ P) : X ^ m ∣ logarithmicEuler^[n] P := by
  induction n generalizing P with
  | zero => simpa only [Nat.add_zero, Function.iterate_zero_apply] using h
  | succ n ih =>
    rw [Function.iterate_succ_apply]
    exact ih (logarithmicEuler_dvd (m + n) (by simpa only [Nat.add_assoc] using h))

theorem logarithmicEuler_iterate_eval_zero {K : Type*} [CommRing K] {m n : ℕ} {P : K[X]}
    (hn : n < m) (h : X ^ m ∣ P) : (logarithmicEuler^[n] P).eval 0 = 0 := by
  have hsmall : X ^ (1 + n) ∣ P :=
    (pow_dvd_pow (X : K[X]) (by omega : 1 + n ≤ m)).trans h
  have hx := logarithmicEuler_iterate_dvd 1 n hsmall
  obtain ⟨Q, hQ⟩ := hx
  rw [pow_one] at hQ
  rw [hQ, eval_mul, eval_X, zero_mul]

theorem logarithmicEuler_mul {K : Type*} [CommRing K] (P Q : K[X]) :
    logarithmicEuler (P * Q) = logarithmicEuler P * Q + P * logarithmicEuler Q := by
  simp only [logarithmicEuler, derivative_mul]
  ring

theorem logarithmicEuler_one_sub_X_pow {K : Type*} [CommRing K] (a : ℕ) :
    logarithmicEuler ((1 - X : K[X]) ^ a) = C (-(a : K)) * (1 - X) ^ a := by
  cases a with
  | zero => simp [logarithmicEuler]
  | succ a =>
    rw [logarithmicEuler, derivative_pow]
    simp only [derivative_sub, derivative_one, derivative_X, zero_sub,
      Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, C_neg, pow_succ]
    ring

theorem logarithmicEuler_pow_succ {K : Type*} [CommRing K] (P : K[X]) (b : ℕ) :
    logarithmicEuler (P ^ (b + 1)) = C ((b + 1 : ℕ) : K) * P ^ b * logarithmicEuler P := by
  rw [logarithmicEuler, derivative_pow, logarithmicEuler]
  simp only [Nat.add_sub_cancel]
  ring

theorem truncatedLog_eval_zero {K : Type*} [Field K] (p : ℕ) :
    (truncatedLog K p).eval 0 = 0 := by
  simp [truncatedLog, eval_finsetSum]

theorem logarithmicEuler_truncatedLog {K : Type*} [Field K] {p : ℕ} [CharP K p] :
    logarithmicEuler (truncatedLog K p) = 1 - X ^ (p - 1) :=
  truncatedLog_weighted_derivative

noncomputable def logarithmicMode (K : Type*) [Field K] (p a b : ℕ) : K[X] :=
  (1 - X) ^ a * truncatedLog K p ^ b

theorem logarithmicEuler_mode_zero {K : Type*} [Field K] (p a : ℕ) :
    logarithmicEuler (logarithmicMode K p a 0) = C (-(a : K)) * logarithmicMode K p a 0 := by
  simp only [logarithmicMode, pow_zero, mul_one, logarithmicEuler_one_sub_X_pow]

theorem logarithmicEuler_mode_succ {K : Type*} [Field K] {p : ℕ} [CharP K p] (a b : ℕ) :
    logarithmicEuler (logarithmicMode K p a (b + 1)) =
      C (-(a : K)) * logarithmicMode K p a (b + 1) +
      C ((b + 1 : ℕ) : K) * logarithmicMode K p a b -
      X ^ (p - 1) * (C ((b + 1 : ℕ) : K) * logarithmicMode K p a b) := by
  rw [logarithmicMode, logarithmicEuler_mul, logarithmicEuler_one_sub_X_pow, logarithmicEuler_pow_succ,
    logarithmicEuler_truncatedLog]
  simp only [logarithmicMode]
  ring


theorem factorial_ne_zero_of_lt_char {K : Type*} [Field K] {p : ℕ} [CharP K p]
    {b : ℕ} (hb : b < p) : (b.factorial : K) ≠ 0 := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.factorial_succ, Nat.cast_mul]
    apply mul_ne_zero ?_ (ih (by omega))
    rw [ne_eq, CharP.cast_eq_zero_iff K p]
    exact Nat.not_dvd_of_pos_of_lt (by omega) hb

open GaloisForLFunctions in
theorem confluent_det_ne_zero_of_mul_le_char {K : Type*} [Field K] {p A B : ℕ} [CharP K p]
    (hA : 0 < A) (hB : 0 < B) (hAB : A * B ≤ p) :
    (confluentPolynomialJetMatrix (fun i : Fin A => -((i : ℕ) : K))
      (fun _ => B) (fun k => (X : K[X]) ^ (k : ℕ))).det ≠ 0 := by
  classical
  rw [det_confluentPolynomialJetMatrix _ _ _ (fun _ => natDegree_X_pow _) (fun _ => monic_X_pow _)]
  have hAp : A ≤ p := (Nat.le_mul_of_pos_right A hB).trans hAB
  have hBp : B ≤ p := (Nat.le_mul_of_pos_left B hA).trans hAB
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro b _
    exact factorial_ne_zero_of_lt_char (b.isLt.trans_le hBp)
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    have hij : (i : ℕ) < (j : ℕ) := (Finset.mem_Ioi.mp hj : i < j)
    apply pow_ne_zero
    have hcast : (((j : ℕ) - (i : ℕ) : ℕ) : K) ≠ 0 := by
      rw [ne_eq, CharP.cast_eq_zero_iff K p]
      exact Nat.not_dvd_of_pos_of_lt (by omega) (by have := j.isLt.trans_le hAp; omega)
    rw [show -((j : ℕ) : K) - -((i : ℕ) : K) =
        -((((j : ℕ) - (i : ℕ) : ℕ) : K)) by rw [Nat.cast_sub hij.le]; ring]
    exact neg_ne_zero.mpr hcast

/-- Logarithmic jets below the characteristic are Hermite evaluation functionals. -/
theorem logarithmicMode_jet_eq {K : Type*} [Field K] {p : ℕ} [CharP K p]
    (n : ℕ) (hn : n < p) (a b : ℕ) :
    (logarithmicEuler^[n] (logarithmicMode K p a b)).eval 0 =
      (derivative^[b] (X ^ n : K[X])).eval (-(a : K)) := by
  induction n generalizing a b with
  | zero =>
    cases b with
    | zero => simp [logarithmicMode]
    | succ b => simp [logarithmicMode, truncatedLog_eval_zero]
  | succ n ih =>
    have hn' : n < p := by omega
    cases b with
    | zero =>
      rw [Function.iterate_succ_apply, logarithmicEuler_mode_zero,
        logarithmicEuler_iterate_C_mul, eval_mul, eval_C, ih hn']
      simp only [Function.iterate_zero_apply, eval_pow, eval_X]
      exact (pow_succ' (-(a : K)) n).symm
    | succ b =>
      have herr : (logarithmicEuler^[n] (X ^ (p - 1) *
          (C ((b + 1 : ℕ) : K) * logarithmicMode K p a b))).eval 0 = 0 :=
        logarithmicEuler_iterate_eval_zero (by omega) (dvd_mul_right _ _)
      rw [Function.iterate_succ_apply, logarithmicEuler_mode_succ,
        logarithmicEuler_iterate_sub, logarithmicEuler_iterate_add,
        logarithmicEuler_iterate_C_mul, logarithmicEuler_iterate_C_mul,
        eval_sub, eval_add, eval_mul, eval_C, eval_mul, eval_C,
        herr, sub_zero, ih hn', ih hn']
      rw [pow_succ, iterate_derivative_mul_X]
      simp only [eval_add, eval_mul, eval_X, eval_smul,
        Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      ring

open GaloisForLFunctions in
/-- The AB logarithmic modes are independent modulo X^p when AB≤p. -/
theorem coefficients_eq_zero_of_X_pow_dvd {K : Type*} [Field K] {p A B : ℕ} [CharP K p]
    (hA : 0 < A) (hB : 0 < B) (hAB : A * B ≤ p)
    (c : Fin (∑ _i : Fin A, B) → K)
    (hc : X ^ p ∣ ∑ k, C (c k) * logarithmicMode K p
      (gammaJetSlotNode (fun _ : Fin A => B) k)
      (gammaJetSlotOrder (fun _ : Fin A => B) k)) : c = 0 := by
  classical
  let M := confluentPolynomialJetMatrix (fun i : Fin A => -((i : ℕ) : K))
    (fun _ => B) (fun k => (X : K[X]) ^ (k : ℕ))
  have hdet : M.transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact confluent_det_ne_zero_of_mul_le_char hA hB hAB
  apply Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det M.transpose).mpr (isUnit_iff_ne_zero.mpr hdet))
  rw [Matrix.mulVec_zero]
  funext n
  have hn : (n : ℕ) < p := by
    have hn' := n.isLt
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hn'
    exact hn'.trans_le hAB
  have hz := logarithmicEuler_iterate_eval_zero hn hc
  rw [logarithmicEuler_iterate_sum, eval_finsetSum] at hz
  simp only [logarithmicEuler_iterate_C_mul, eval_mul, eval_C, logarithmicMode_jet_eq _ hn] at hz
  simpa only [M, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    confluentPolynomialJetMatrix, polynomialJetEvalMatrix, Pi.zero_apply, mul_comm] using hz

open Polynomial Finset
open GaloisForLFunctions


abbrev LogSlot (A B : ℕ) := Fin (∑ _i : Fin A, B)

def logarithmicBlock {K : Type*} [Field K] (p : ℕ) {A B : ℕ}
    (c : LogSlot A B → K) : K[X] :=
  ∑ k, C (c k) * logarithmicMode K p
    (gammaJetSlotNode (fun _ : Fin A => B) k)
    (gammaJetSlotOrder (fun _ : Fin A => B) k)

theorem logarithmicBlock_zero {K : Type*} [Field K] (p A B : ℕ) :
    logarithmicBlock p (0 : LogSlot A B → K) = 0 := by
  simp [logarithmicBlock]

/-- Horner expansion in X^p with logarithmic-mode coefficient blocks. -/
def logarithmicAuxiliary {K : Type*} [Field K] (p A B : ℕ) :
    (C : ℕ) → (Fin C → LogSlot A B → K) → K[X]
  | 0, _ => 0
  | C + 1, c => logarithmicBlock p (c 0) +
      X ^ p * logarithmicAuxiliary p A B C (fun j => c j.succ)

theorem logarithmicAuxiliary_coefficients_eq_zero {K : Type*} [Field K]
    {p A B : ℕ} [CharP K p] (hA : 0 < A) (hB : 0 < B) (hAB : A * B ≤ p)
    (C : ℕ) (c : Fin C → LogSlot A B → K)
    (hc : logarithmicAuxiliary p A B C c = 0) : c = 0 := by
  induction C with
  | zero => exact funext fun j => Fin.elim0 j
  | succ C ih =>
    have hsplit : logarithmicBlock p (c 0) +
        X ^ p * logarithmicAuxiliary p A B C (fun j => c j.succ) = 0 := hc
    have hdiv : X ^ p ∣ logarithmicBlock p (c 0) := by
      refine ⟨-logarithmicAuxiliary p A B C (fun j => c j.succ), ?_⟩
      linear_combination hsplit
    have hfirst : c 0 = 0 := coefficients_eq_zero_of_X_pow_dvd hA hB hAB (c 0) hdiv
    rw [hfirst, logarithmicBlock_zero, zero_add] at hsplit
    have htail : (fun j : Fin C => c j.succ) = 0 :=
      ih _ ((mul_eq_zero.mp hsplit).resolve_left (pow_ne_zero _ X_ne_zero))
    funext j
    exact Fin.cases hfirst (fun j => congrFun htail j) j

/-- A nonzero coefficient array remains nonzero after substitution (X,L_p,X^p). -/
theorem logarithmicAuxiliary_ne_zero {K : Type*} [Field K]
    {p A B C : ℕ} [CharP K p] (hA : 0 < A) (hB : 0 < B) (hAB : A * B ≤ p)
    {c : Fin C → LogSlot A B → K} (hc : c ≠ 0) :
    logarithmicAuxiliary p A B C c ≠ 0 :=
  fun hz => hc (logarithmicAuxiliary_coefficients_eq_zero hA hB hAB C c hz)

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn

#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.logarithmicMode_jet_eq
#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.coefficients_eq_zero_of_X_pow_dvd
#print axioms GaloisForLFunctions.ArithmeticLefschetzStepanovTheory.Heilbronn.logarithmicAuxiliary_ne_zero
