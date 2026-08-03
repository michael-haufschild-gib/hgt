import GaloisForLFunctions.RHTower.ResidueCorrectedDeterminantCofinalTorsion
import Mathlib.Algebra.Group.ForwardDiff

/-!
# Residue-jet determinant characters and spectral-suspension cancellation

This module formalizes unconditional algebraic core of cofinal residue-jet universality.
`residueJetDeterminant` is common divisor-carrying core multiplied by exponential polynomial;
`residueJetTorsion` is exact divisor-cancelled relative character.  Main combinatorial theorem
proves finite-difference spectral-suspension weights annihilate every lower moment and preserve
top moment as factorial.  Suspension moment matrix is proved triangular with nonzero determinant;
formal jet polynomials are classified exactly, giving independent and exhaustive character
directions.

Analytic zeta continuation and Schatten convergence remain in operator-specific modules.
-/

open scoped BigOperators
open Finset
open Filter Topology

noncomputable section

namespace RHTower

/-- Finite-difference scale moment used by graded spectral suspension. -/
def residueSuspensionMoment (j k : ℕ) : ℤ :=
  ∑ r ∈ range (j + 1),
    ((-1 : ℤ) ^ (j - r) * (j.choose r : ℤ)) * ((r + 1 : ℕ) : ℤ) ^ k

/-- Suspension moment is the corresponding iterated forward difference at one. -/
theorem residueSuspensionMoment_eq_fwdDiff (j k : ℕ) :
    residueSuspensionMoment j k =
      (fwdDiff (1 : ℤ))^[j] (fun x : ℤ => x ^ k) 1 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp only [residueSuspensionMoment, zsmul_eq_mul, Nat.cast_add, Nat.cast_one,
    nsmul_eq_mul, mul_one, add_comm, Int.cast_id]

/-- Order-j spectral suspension cancels every lower residue-jet coordinate. -/
theorem residueSuspensionMoment_eq_zero_of_lt {j k : ℕ} (h : k < j) :
    residueSuspensionMoment j k = 0 := by
  rw [residueSuspensionMoment_eq_fwdDiff]
  rw [fwdDiff_iter_pow_eq_zero_of_lt h]
  rfl

/-- First surviving suspension coordinate is exactly factorial. -/
theorem residueSuspensionMoment_self (j : ℕ) :
    residueSuspensionMoment j j = (j.factorial : ℤ) := by
  rw [residueSuspensionMoment_eq_fwdDiff]
  rw [fwdDiff_iter_eq_factorial]
  rfl

theorem residueSuspensionMoment_self_ne_zero (j : ℕ) :
    residueSuspensionMoment j j ≠ 0 := by
  rw [residueSuspensionMoment_self]
  exact_mod_cast Nat.factorial_ne_zero j

/-- Finite moment matrix for suspension orders and jet degrees 1 through p. -/
def residueSuspensionMatrix (p : ℕ) : Matrix (Fin p) (Fin p) ℤ :=
  fun j k => residueSuspensionMoment ((j : ℕ) + 1) ((k : ℕ) + 1)

/-- Cancellation makes suspension moment matrix upper triangular. -/
theorem residueSuspensionMatrix_blockTriangular (p : ℕ) :
    Matrix.BlockTriangular (residueSuspensionMatrix p) id := by
  intro i j hji
  exact residueSuspensionMoment_eq_zero_of_lt (Nat.add_lt_add_right hji 1)

/-- Diagonal of suspension moment matrix is sequence of nonzero factorials. -/
theorem residueSuspensionMatrix_diagonal (p : ℕ) (i : Fin p) :
    residueSuspensionMatrix p i i = (((i : ℕ) + 1).factorial : ℤ) := by
  exact residueSuspensionMoment_self ((i : ℕ) + 1)

/-- Exact determinant of all-order suspension moment matrix. -/
theorem residueSuspensionMatrix_det (p : ℕ) :
    (residueSuspensionMatrix p).det =
      ∏ i : Fin p, ((((i : ℕ) + 1).factorial : ℤ)) := by
  rw [Matrix.det_of_upperTriangular (residueSuspensionMatrix_blockTriangular p)]
  exact Finset.prod_congr rfl (fun i _ => residueSuspensionMatrix_diagonal p i)

/-- Every finite suspension moment matrix is nonsingular: all jet directions independent. -/
theorem residueSuspensionMatrix_det_ne_zero (p : ℕ) :
    (residueSuspensionMatrix p).det ≠ 0 := by
  rw [residueSuspensionMatrix_det]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => by
    exact_mod_cast Nat.factorial_ne_zero ((i : ℕ) + 1)

/-- Exponential polynomial determined by corrected residue jet of orders `1, ..., p - 1`. -/
def residueJetPolynomial (p : ℕ) (b : ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Ico 1 p, b k * z ^ k

/-- Zero-free character attached to corrected residue jet. -/
def residueJetCharacter (p : ℕ) (b : ℕ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (residueJetPolynomial p b z)

/-- Divisor-cancelled relative determinant torsion for two residue jets. -/
def residueJetTorsion (p : ℕ) (b c : ℕ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (residueJetPolynomial p b z - residueJetPolynomial p c z)

/-- Residue-jet determinant with arbitrary common divisor-carrying core. -/
def residueJetDeterminant (p : ℕ) (b : ℕ → ℂ) (core : ℂ → ℂ) (z : ℂ) : ℂ :=
  residueJetCharacter p b z * core z

/-- Relative torsion globally factors determinant characters, including common zeros. -/
theorem residueJetDeterminant_eq_torsion_mul (p : ℕ) (b c : ℕ → ℂ)
    (core : ℂ → ℂ) (z : ℂ) :
    residueJetDeterminant p b core z =
      residueJetTorsion p b c z * residueJetDeterminant p c core z := by
  rw [residueJetDeterminant, residueJetTorsion, residueJetDeterminant,
    residueJetCharacter, residueJetCharacter, ← mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- Residue-jet torsions form exact pair-groupoid cocycle. -/
theorem residueJetTorsion_cocycle (p : ℕ) (b c d : ℕ → ℂ) (z : ℂ) :
    residueJetTorsion p b c z * residueJetTorsion p c d z =
      residueJetTorsion p b d z := by
  rw [residueJetTorsion, residueJetTorsion, residueJetTorsion, ← Complex.exp_add]
  congr 1
  ring

theorem residueJetTorsion_ne_zero (p : ℕ) (b c : ℕ → ℂ) (z : ℂ) :
    residueJetTorsion p b c z ≠ 0 :=
  Complex.exp_ne_zero _

/-- One corrected coordinate: finite part plus harmonic multiple of local residue. -/
def correctedResidueJetCoordinate
    (k : ℕ) (harmonic finitePart residue : ℂ) : ℂ :=
  -(finitePart + harmonic * residue) / k

/-- At first non-trace-class threshold harmonic correction vanishes. -/
theorem correctedResidueJetCoordinate_one (finitePart residue : ℂ) :
    correctedResidueJetCoordinate 1 0 finitePart residue = -finitePart := by
  simp [correctedResidueJetCoordinate]

/-- A single jet coordinate produces its independent monomial direction. -/
theorem residueJetPolynomial_single {p k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p)
    (v z : ℂ) :
    residueJetPolynomial p (Pi.single k v) z = v * z ^ k := by
  rw [residueJetPolynomial, Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [Pi.single_eq_of_ne hjk]
  · simp [Finset.mem_Ico, hk1, hkp]

/-- Formal polynomial encoding of a corrected residue jet.  Unlike its exponential,
this polynomial has no period ambiguity and therefore records every coordinate exactly. -/
def residueJetPolynomialFormal (p : ℕ) (b : ℕ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Ico 1 p, Polynomial.monomial k (b k)

/-- Formal jet polynomial evaluates to the analytic exponent used by determinant characters. -/
theorem residueJetPolynomialFormal_eval (p : ℕ) (b : ℕ → ℂ) (z : ℂ) :
    (residueJetPolynomialFormal p b).eval z = residueJetPolynomial p b z := by
  rw [residueJetPolynomialFormal, residueJetPolynomial, Polynomial.eval_finsetSum]
  simp

/-- Every in-range corrected coordinate is the corresponding formal coefficient. -/
theorem residueJetPolynomialFormal_coeff {p k : ℕ} (hk1 : 1 ≤ k) (hkp : k < p)
    (b : ℕ → ℂ) :
    (residueJetPolynomialFormal p b).coeff k = b k := by
  rw [residueJetPolynomialFormal, Polynomial.finsetSum_coeff, Finset.sum_eq_single k]
  · simp
  · intro j hj hjk
    simp [Polynomial.coeff_monomial, hjk]
  · simp [Finset.mem_Ico, hk1, hkp]

/-- Full corrected residue jet is a complete invariant of its formal counterterm polynomial. -/
theorem residueJetPolynomialFormal_complete {p : ℕ} {b c : ℕ → ℂ}
    (h : residueJetPolynomialFormal p b = residueJetPolynomialFormal p c) :
    ∀ k ∈ Ico 1 p, b k = c k := by
  intro k hk
  have hk1 : 1 ≤ k := (Finset.mem_Ico.mp hk).1
  have hkp : k < p := (Finset.mem_Ico.mp hk).2
  rw [← residueJetPolynomialFormal_coeff hk1 hkp b,
    ← residueJetPolynomialFormal_coeff hk1 hkp c, h]

/-- Every polynomial supported in degrees 1 through p - 1 is a residue-jet polynomial.
Together with completeness, this is exact finite-dimensional character classification
underlying full-jet sharpness. -/
theorem residueJetPolynomialFormal_surjective_on_support
    {p : ℕ} {P : Polynomial ℂ} (hP : P.support ⊆ Ico 1 p) :
    ∃ b : ℕ → ℂ, residueJetPolynomialFormal p b = P := by
  refine ⟨fun k => P.coeff k, ?_⟩
  ext k
  by_cases hk : k ∈ Ico 1 p
  · rw [residueJetPolynomialFormal_coeff (Finset.mem_Ico.mp hk).1
      (Finset.mem_Ico.mp hk).2]
  · rw [residueJetPolynomialFormal, Polynomial.finsetSum_coeff]
    have hPk : P.coeff k = 0 := by
      by_contra hne
      exact hk (hP (Polynomial.mem_support_iff.mpr hne))
    simp [Polynomial.coeff_monomial, hk, hPk]

/-- Torsion against zero jet is exactly corresponding residue-jet character. -/
theorem residueJetTorsion_zero_eq_character (p : ℕ) (b : ℕ → ℂ) (z : ℂ) :
    residueJetTorsion p b 0 z = residueJetCharacter p b z := by
  simp [residueJetTorsion, residueJetCharacter, residueJetPolynomial]

/-- Every corrected-jet character occurs as divisor-cancelled relative torsion. -/
theorem residueJetTorsion_realizes_every_jetCharacter (p : ℕ) (v : ℕ → ℂ) :
    (fun z => residueJetTorsion p v 0 z) = residueJetCharacter p v := by
  funext z
  exact residueJetTorsion_zero_eq_character p v z

/-- Coordinatewise convergence of finite residue jet implies pointwise polynomial convergence. -/
theorem tendsto_residueJetPolynomial
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ} (z : ℂ)
    (hb : ∀ k ∈ Ico 1 p,
      Tendsto (fun n => b n k) atTop (𝓝 (bLim k))) :
    Tendsto (fun n => residueJetPolynomial p (b n) z) atTop
      (𝓝 (residueJetPolynomial p bLim z)) := by
  unfold residueJetPolynomial
  apply tendsto_finsetSum
  intro k hk
  exact (hb k hk).mul tendsto_const_nhds

/-- Forward half of cofinal law: convergent core and full jet force determinant convergence. -/
theorem tendsto_residueJetDeterminant
    {p : ℕ} {b : ℕ → ℕ → ℂ} {bLim : ℕ → ℂ}
    {core : ℕ → ℂ → ℂ} {coreLim : ℂ → ℂ} (z : ℂ)
    (hb : ∀ k ∈ Ico 1 p,
      Tendsto (fun n => b n k) atTop (𝓝 (bLim k)))
    (hcore : Tendsto (fun n => core n z) atTop (𝓝 (coreLim z))) :
    Tendsto (fun n => residueJetDeterminant p (b n) (core n) z) atTop
      (𝓝 (residueJetDeterminant p bLim coreLim z)) := by
  have hpoly := tendsto_residueJetPolynomial z hb
  have hchar := (Complex.continuous_exp.tendsto _).comp hpoly
  exact hchar.mul hcore

end RHTower
