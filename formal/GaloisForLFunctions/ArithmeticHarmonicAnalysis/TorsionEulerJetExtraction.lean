import GaloisForLFunctions.ArithmeticHarmonicAnalysis.EulerOperatorsLowerMultiplicity
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.TorsionFourierResolution
import GaloisForLFunctions.HTGeometry.BorisovGabberVasiuPolynomialJacobian
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Exact Fourier extraction of Euler jets

Shifted coordinate Euler operators act diagonally on arithmetic monomials.
Fourier averaging isolates each residue fibre; falling factorials then give
the quotient-binomial Newton coefficient with exact nonzero normalization.
-/

open MvPolynomial Finset
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The monomial eigenvalue of a word of shifted Euler operators. -/
def eulerWordWeight (L : List (ι × ℂ)) (e : ι → ℕ) : ℂ :=
  (L.map fun v => (e v.1 : ℂ) - v.2).prod

theorem shiftedCoordinateEuler_monomial (i : ι) (s c : ℂ) (e : ι → ℕ) :
    shiftedCoordinateEuler i s (C c * ∏ j, (X j : MvPolynomial ι ℂ) ^ e j) =
      C (((e i : ℂ) - s) * c) * ∏ j, X j ^ e j := by
  have he := HTGeometry.bgv_coordinateEuler_product (R := ℂ) e i univ
  simp only [mem_univ, if_true] at he
  simp only [shiftedCoordinateEuler, pderiv_mul, pderiv_C, zero_mul, zero_add]
  rw [show X i * (C c * pderiv i (∏ j, (X j : MvPolynomial ι ℂ) ^ e j)) =
    C c * (X i * pderiv i (∏ j, (X j : MvPolynomial ι ℂ) ^ e j)) by ring, he]
  simp only [map_mul, map_sub, map_natCast]
  ring

theorem shiftedEulerWord_monomial (L : List (ι × ℂ)) (c : ℂ) (e : ι → ℕ) :
    shiftedEulerWord L (C c * ∏ j, (X j : MvPolynomial ι ℂ) ^ e j) =
      C (eulerWordWeight L e * c) * ∏ j, X j ^ e j := by
  induction L with
  | nil => simp only [shiftedEulerWord, eulerWordWeight, List.map_nil, List.prod_nil, one_mul]
  | cons v L ih =>
    rw [shiftedEulerWord, ih, shiftedCoordinateEuler_monomial]
    simp only [eulerWordWeight, List.map_cons, List.prod_cons, mul_assoc]

/-- The Euler factors that extract one Newton multi-index within a residue fibre. -/
def newtonEulerWord (q : ℕ) (b : ι → ZMod q) (a : ι → ℕ) : List (ι × ℂ) :=
  (univ.sigma fun i => range (a i)).toList.map
    fun v => (v.1, ((b v.1).val : ℂ) + (q : ℂ) * v.2)

omit [DecidableEq ι] in
theorem newtonEulerWord_length (q : ℕ) (b : ι → ZMod q) (a : ι → ℕ) :
    (newtonEulerWord q b a).length = ∑ i, a i := by
  simp only [newtonEulerWord, List.length_map, length_toList, card_sigma, card_range]

omit [DecidableEq ι] in
theorem newtonEulerWord_weight (q : ℕ) (b : ι → ZMod q) (a e : ι → ℕ) :
    eulerWordWeight (newtonEulerWord q b a) e =
      ∏ i, ∏ j ∈ range (a i), ((e i : ℂ) - (b i).val - (q : ℂ) * j) := by
  simp only [eulerWordWeight, newtonEulerWord, List.map_map, prod_map_toList, prod_sigma,
    Function.comp_apply]
  apply prod_congr rfl
  intro i _
  apply prod_congr rfl
  intro j _
  ring

/-- Falling factorial normalization is valid even beyond the degree. -/
theorem prod_shifted_multiples (q k a : ℕ) :
    (∏ j ∈ range a, ((q : ℂ) * k - (q : ℂ) * j)) =
      (q : ℂ) ^ a * (a.factorial : ℂ) * (k.choose a : ℂ) := by
  simp_rw [← mul_sub]
  rw [prod_mul_distrib, prod_const, card_range,
    ← descPochhammer_eval_eq_prod_range, descPochhammer_eval_eq_descFactorial,
    Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, mul_assoc]

omit [DecidableEq ι] in
theorem newtonEulerWord_weight_of_residue (q : ℕ) [NeZero q]
    (b : ι → ZMod q) (a e : ι → ℕ) (he : (fun i => (e i : ZMod q)) = b) :
    eulerWordWeight (newtonEulerWord q b a) e =
      (q : ℂ) ^ (∑ i, a i) * (∏ i, ((a i).factorial : ℂ)) *
        ∏ i, ((e i / q).choose (a i) : ℂ) := by
  rw [newtonEulerWord_weight]
  have hcoord (i : ι) :
      (∏ j ∈ range (a i), ((e i : ℂ) - (b i).val - (q : ℂ) * j)) =
        (q : ℂ) ^ a i * ((a i).factorial : ℂ) * ((e i / q).choose (a i) : ℂ) := by
    have hmod : e i % q = (b i).val := by
      simpa only [ZMod.val_natCast] using congrArg ZMod.val (congrFun he i)
    have hdiv : e i = (b i).val + q * (e i / q) := by
      rw [← hmod]
      exact (Nat.mod_add_div (e i) q).symm
    have hcast : (e i : ℂ) = ((b i).val : ℂ) + (q : ℂ) * ((e i / q : ℕ) : ℂ) := by
      exact_mod_cast hdiv
    simp_rw [hcast, add_sub_cancel_left]
    exact prod_shifted_multiples q (e i / q) (a i)
  simp_rw [hcoord]
  rw [prod_mul_distrib, prod_mul_distrib, prod_pow_eq_pow_sum]

variable {κ : Type*}

/-- A finite polynomial with explicitly indexed exponent vectors. -/
def finiteMonomialPolynomial (S : Finset κ) (e : κ → ι → ℕ) (c : κ → ℂ) :
    MvPolynomial ι ℂ := ∑ n ∈ S, C (c n) * ∏ i, X i ^ e n i

omit [DecidableEq ι] in
/-- Root-of-unity evaluation reduces each exponent modulo the torsion order. -/
theorem eval_finiteMonomialPolynomial (q : ℕ) [NeZero q]
    (S : Finset κ) (e : κ → ι → ℕ) (c : κ → ℂ) (t : ι → ZMod q) :
    eval (fun i => ZMod.stdAddChar (t i)) (finiteMonomialPolynomial S e c) =
      torsionPolynomial q S (fun n i => (e n i : ZMod q)) c t := by
  simp only [finiteMonomialPolynomial, map_sum, map_mul, eval_C, map_prod, map_pow,
    eval_X, torsionPolynomial, torsionPhase]
  apply sum_congr rfl
  intro n _
  congr 1
  apply prod_congr rfl
  intro i _
  rw [← AddChar.map_nsmul_eq_pow]
  congr 1
  simp only [nsmul_eq_mul, mul_comm]

/-- Euler words multiply each monomial coefficient by their scalar eigenvalue. -/
theorem eval_shiftedEulerWord_finiteMonomialPolynomial (q : ℕ) [NeZero q]
    (L : List (ι × ℂ)) (S : Finset κ) (e : κ → ι → ℕ) (c : κ → ℂ)
    (t : ι → ZMod q) :
    eval (fun i => ZMod.stdAddChar (t i))
        (shiftedEulerWord L (finiteMonomialPolynomial S e c)) =
      torsionPolynomial q S (fun n i => (e n i : ZMod q))
        (fun n => eulerWordWeight L (e n) * c n) t := by
  rw [finiteMonomialPolynomial, shiftedEulerWord_sum]
  simp_rw [shiftedEulerWord_monomial]
  exact eval_finiteMonomialPolynomial q S e _ t

/-- Fourier averaging shifted Euler jets extracts the exact residue Newton coefficient. -/
theorem newtonEuler_fourier_extraction (q : ℕ) [NeZero q]
    (S : Finset κ) (e : κ → ι → ℕ) (c : κ → ℂ) (b : ι → ZMod q) (a : ι → ℕ) :
    (∑ t : ι → ZMod q, eval (fun i => ZMod.stdAddChar (t i))
        (shiftedEulerWord (newtonEulerWord q b a) (finiteMonomialPolynomial S e c)) *
          conj (torsionPhase q b t)) =
      (q : ℂ) ^ Fintype.card ι * ((q : ℂ) ^ (∑ i, a i) *
        (∏ i, ((a i).factorial : ℂ))) *
        residueCoefficient q S (fun n i => (e n i : ZMod q))
          (fun n => c n * ∏ i, ((e n i / q).choose (a i) : ℂ)) b := by
  simp only [eval_shiftedEulerWord_finiteMonomialPolynomial]
  rw [torsion_coefficient_recovery]
  have hc : residueCoefficient q S (fun n i => (e n i : ZMod q))
      (fun n => eulerWordWeight (newtonEulerWord q b a) (e n) * c n) b =
        ((q : ℂ) ^ (∑ i, a i) * (∏ i, ((a i).factorial : ℂ))) *
          residueCoefficient q S (fun n i => (e n i : ZMod q))
            (fun n => c n * ∏ i, ((e n i / q).choose (a i) : ℂ)) b := by
    classical
    unfold residueCoefficient
    rw [mul_sum]
    apply sum_congr rfl
    intro n hn
    dsimp only
    rw [newtonEulerWord_weight_of_residue q b a (e n) (mem_filter.mp hn).2]
    ring
  rw [hc]
  ring

end GaloisForLFunctions.ArithmeticHarmonicAnalysis
