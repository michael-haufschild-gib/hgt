import GaloisForLFunctions.RHTower.DeningerRationalWittHazewinkelHankel
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Leading-determinant localization for Hazewinkel stages

This module isolates the exact localization mechanism in Hazewinkel's proof that the universal
Hankel determinantal ideal is prime.  It proves two unconditional pieces omitted by a bare appeal
to the published argument:

* the leading `n × n` Hankel determinant survives modulo `Jₙ` for every positive `n`;
* regularity of that class and integrality after inverting it imply primeness of `Jₙ`.

Survival is witnessed by an explicit `n`-atomic rational moment sequence.  Its arbitrary
`(n+1) × (n+1)` Hankel minors factor through an `n`-dimensional space, while its leading minor
factors into two Vandermonde determinants and a nonzero diagonal determinant.
-/

namespace RHTower

noncomputable section
open scoped BigOperators

/-- The rational `n`-atomic moment sequence with equal nonzero weights and atoms `1, …, n`. -/
def deningerHazewinkelRationalMoment (n s : ℕ) : ℚ :=
  (n : ℚ)⁻¹ * ∑ t : Fin n, ((t.val + 1 : ℕ) : ℚ) ^ s

/-- Evaluation of universal coefficients on the explicit rational `n`-atomic moment sequence. -/
def deningerHazewinkelRationalMomentEval (n : ℕ) : MvPolynomial ℕ ℤ →+* ℚ :=
  MvPolynomial.eval₂Hom (Int.castRingHom ℚ) fun j =>
    deningerHazewinkelRationalMoment n (j + 1)

@[simp] theorem deningerHazewinkelRationalMoment_zero (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelRationalMoment n 0 = 1 := by
  simp [deningerHazewinkelRationalMoment, hn.ne']

@[simp] theorem deningerHazewinkelRationalMomentEval_universalCoeff
    (n s : ℕ) (hn : 0 < n) :
    deningerHazewinkelRationalMomentEval n (deningerHazewinkelUniversalCoeff s) =
      deningerHazewinkelRationalMoment n s := by
  cases s <;>
    simp [deningerHazewinkelUniversalCoeff,
      deningerHazewinkelRationalMomentEval,
      deningerHazewinkelRationalMoment_zero, hn]

/-- Every generator of `Jₙ` vanishes on the explicit rank-`n` rational moment sequence. -/
theorem deningerHazewinkelIdeal_le_ker_rationalMomentEval (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelIdeal n ≤ RingHom.ker (deningerHazewinkelRationalMomentEval n) := by
  rw [deningerHazewinkelIdeal, deningerMatrixMinorIdeal, Ideal.span_le]
  rintro z ⟨rows, cols, rfl⟩
  apply RingHom.mem_ker.mpr
  rw [(deningerHazewinkelRationalMomentEval n).map_det]
  let U : Matrix (Fin (n + 1)) (Fin n) ℚ := fun i t =>
    (n : ℚ)⁻¹ * ((t.val + 1 : ℕ) : ℚ) ^ rows i
  let V : Matrix (Fin n) (Fin (n + 1)) ℚ := fun t j =>
    ((t.val + 1 : ℕ) : ℚ) ^ cols j
  have hfactor : (deningerHazewinkelRationalMomentEval n).mapMatrix
      (deningerHazewinkelUniversalHankel.submatrix rows cols) = U * V := by
    ext i j
    rw [Matrix.mul_apply]
    change deningerHazewinkelRationalMomentEval n
      (deningerHazewinkelUniversalCoeff (rows i + cols j)) = _
    rw [deningerHazewinkelRationalMomentEval_universalCoeff n _ hn]
    simp only [deningerHazewinkelRationalMoment, U, V, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    rw [pow_add]
    ring
  rw [hfactor]
  exact det_rectangular_factor_succ_eq_zero n U V

/-- Hazewinkel's leading `n × n` Hankel determinant `Dₙ`. -/
def deningerHazewinkelLeadingDeterminant (n : ℕ) : MvPolynomial ℕ ℤ :=
  Matrix.det fun i j : Fin n =>
    deningerHazewinkelUniversalCoeff (i.val + j.val)

/-- The explicit rational moment witness sends `Dₙ` to a nonzero number. -/
theorem deningerHazewinkelRationalMomentEval_leading_ne_zero
    (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelRationalMomentEval n
      (deningerHazewinkelLeadingDeterminant n) ≠ 0 := by
  rw [deningerHazewinkelLeadingDeterminant,
    (deningerHazewinkelRationalMomentEval n).map_det]
  let v : Fin n → ℚ := fun t => ((t.val + 1 : ℕ) : ℚ)
  let U : Matrix (Fin n) (Fin n) ℚ := (Matrix.vandermonde v).transpose
  let W : Matrix (Fin n) (Fin n) ℚ :=
    Matrix.diagonal fun _ => (n : ℚ)⁻¹
  let V : Matrix (Fin n) (Fin n) ℚ := fun t j =>
    (n : ℚ)⁻¹ * v t ^ j.val
  have hfactor : (deningerHazewinkelRationalMomentEval n).mapMatrix
      (fun i j : Fin n =>
        deningerHazewinkelUniversalCoeff (i.val + j.val)) = U * V := by
    ext i j
    rw [Matrix.mul_apply]
    change deningerHazewinkelRationalMomentEval n
      (deningerHazewinkelUniversalCoeff (i.val + j.val)) = _
    rw [deningerHazewinkelRationalMomentEval_universalCoeff n _ hn]
    simp only [deningerHazewinkelRationalMoment, U, V, Matrix.transpose_apply,
      Matrix.vandermonde]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    change (n : ℚ)⁻¹ * v t ^ (i.val + j.val) =
      v t ^ i.val * ((n : ℚ)⁻¹ * v t ^ j.val)
    rw [pow_add]
    ring
  have hVW : V = W * Matrix.vandermonde v := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [W, V, Matrix.diagonal_apply, Matrix.vandermonde]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b hb hbi
      simp [Ne.symm hbi]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hfactor, Matrix.det_mul, hVW, Matrix.det_mul, Matrix.det_transpose]
  have hv : Function.Injective v := by
    intro i j hij
    dsimp [v] at hij
    apply Fin.ext
    have hs : i.val + 1 = j.val + 1 := by exact_mod_cast hij
    omega
  have hV : (Matrix.vandermonde v).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hv
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hW : W.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    dsimp [W, v]
    exact inv_ne_zero hnq
  exact mul_ne_zero hV (mul_ne_zero hW hV)

/-- The leading determinant is not killed by the Hazewinkel relations. -/
theorem deningerHazewinkelLeadingDeterminant_not_mem
    (n : ℕ) (hn : 0 < n) :
    deningerHazewinkelLeadingDeterminant n ∉ deningerHazewinkelIdeal n := by
  intro hmem
  have hz := deningerHazewinkelIdeal_le_ker_rationalMomentEval n hn hmem
  exact deningerHazewinkelRationalMomentEval_leading_ne_zero n hn
    (RingHom.mem_ker.mp hz)

/-- Consequently the leading determinant has a nonzero class in the universal stage quotient. -/
theorem deningerHazewinkelLeadingDeterminant_quotient_ne_zero
    (n : ℕ) (hn : 0 < n) :
    Ideal.Quotient.mk (deningerHazewinkelIdeal n)
      (deningerHazewinkelLeadingDeterminant n) ≠ 0 := by
  rw [ne_eq, Ideal.Quotient.eq_zero_iff_mem]
  exact deningerHazewinkelLeadingDeterminant_not_mem n hn

/-- General localization criterion used in Hazewinkel's primeness argument. -/
theorem ideal_isPrime_of_regular_away_isDomain
    {R : Type*} [CommRing R] (I : Ideal R) (d : R)
    (hd : IsRegular (Ideal.Quotient.mk I d))
    [IsDomain (Localization.Away (Ideal.Quotient.mk I d))] : I.IsPrime := by
  rw [← Ideal.Quotient.isDomain_iff_prime]
  let f : (R ⧸ I) →+* Localization.Away (Ideal.Quotient.mk I d) := algebraMap _ _
  have hf : Function.Injective f := by
    apply IsLocalization.injective
      (M := Submonoid.powers (Ideal.Quotient.mk I d)) _
    exact Submonoid.powers_le.mpr hd.mem_nonZeroDivisors
  letI : IsCancelMulZero (R ⧸ I) :=
    hf.isCancelMulZero f (map_zero f) (map_mul f)
  letI : Nontrivial (R ⧸ I) := f.domain_nontrivial
  exact { }

/-- Hazewinkel primeness reduced exactly to leading-determinant regularity and the localized
domain theorem.  Nonvanishing of the localized element is already unconditional above. -/
theorem deningerHazewinkelIdeal_isPrime_of_leading_localization
    (n : ℕ)
    (hregular : IsRegular
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (deningerHazewinkelLeadingDeterminant n)))
    [IsDomain (Localization.Away
      (Ideal.Quotient.mk (deningerHazewinkelIdeal n)
        (deningerHazewinkelLeadingDeterminant n)))] :
    (deningerHazewinkelIdeal n).IsPrime :=
  ideal_isPrime_of_regular_away_isDomain _ _ hregular

end

end RHTower
