import GaloisForLFunctions.RHTower.PrimeEulerFerromagneticInteraction
import GaloisForLFunctions.RHTower.EulerReciprocalLeeYangNoGo

/-!
# The two-spin FKG defect is the Lee--Yang and Ihara selector

`[BRIDGE]`  For the normalized zero-field two-spin weight table

`W_c = [[1, c], [c, 1]]`,

the FKG/log-supermodular cross-product defect is `det W_c = 1 - c^2`.  The existing normalized
Lee--Yang block is `1 + 2 c z + z^2`, while its Ihara coordinates are `q = 1` and
`lambda = -2c`.  Hence the following three constraints are literally the same scalar inequality:

* nonnegative two-site FKG defect;
* every zero of the Lee--Yang block lies on the unit circle;
* the Ihara spectral bound `lambda^2 <= 4q`.

This gives the inverse-Ising route a source-facing low-face test: a proposed two-site source packet
can discharge the finite zero-location hypothesis by proving one determinant inequality.  The
prime Euler square-root interaction lies strictly inside this chamber.  Reciprocal pairing of a
contracting Euler weight lies strictly outside it, with an exact negative-square defect.

The physics inputs are the Lee--Yang circle theorem and the Griffiths/FKG positive-association
inequalities for ferromagnetic Ising systems.  This file formalizes only their exact two-spin
algebraic intersection; no general-volume correlation theorem is assumed.
-/

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions

/-- The determinant of the normalized zero-field two-spin weight table
`[[1,c],[c,1]]`.  Nonnegativity is its two-site FKG/log-supermodular condition. -/
def twoSpinFKGDefect (c : ℝ) : ℝ :=
  1 - c ^ 2

/-- An unnormalized symmetric two-spin source block.  `aligned` is the weight of either aligned
configuration and `disagreement` is the weight of either disagreement configuration. -/
def symmetricTwoSpinBlock (aligned disagreement : ℝ) (z : ℂ) : ℂ :=
  aligned + (2 * disagreement : ℝ) * z + aligned * z ^ 2

/-- Circle localization for an unnormalized symmetric two-spin source block. -/
def symmetricTwoSpinCircle (aligned disagreement : ℝ) : Prop :=
  ∀ z : ℂ, symmetricTwoSpinBlock aligned disagreement z = 0 → Complex.normSq z = 1

/-- The raw FKG/log-supermodular determinant of the symmetric weight table
`[[aligned, disagreement], [disagreement, aligned]]`. -/
def symmetricTwoSpinFKGDefect (aligned disagreement : ℝ) : ℝ :=
  aligned ^ 2 - disagreement ^ 2

/-- A nonzero aligned weight normalizes the raw source block to the existing Lee--Yang block. -/
theorem symmetricTwoSpinBlock_eq_aligned_mul_leeYangPairBlock
    {aligned : ℝ} (haligned : aligned ≠ 0) (disagreement : ℝ) (z : ℂ) :
    symmetricTwoSpinBlock aligned disagreement z =
      (aligned : ℂ) * leeYangPairBlock (disagreement / aligned) z := by
  unfold symmetricTwoSpinBlock leeYangPairBlock
  push_cast
  field_simp [haligned]

/-- Circle localization is invariant under normalization by a nonzero aligned weight. -/
theorem symmetricTwoSpinCircle_iff_leeYangPairCircle
    {aligned : ℝ} (haligned : aligned ≠ 0) (disagreement : ℝ) :
    symmetricTwoSpinCircle aligned disagreement ↔
      leeYangPairCircle (disagreement / aligned) := by
  constructor
  · intro hcircle z hz
    apply hcircle z
    rw [symmetricTwoSpinBlock_eq_aligned_mul_leeYangPairBlock haligned, hz, mul_zero]
  · intro hcircle z hz
    apply hcircle z
    rw [symmetricTwoSpinBlock_eq_aligned_mul_leeYangPairBlock haligned] at hz
    exact (mul_eq_zero.mp hz).resolve_left (by exact_mod_cast haligned)

/-- Source-facing selector: for positive aligned weight, the raw FKG determinant is necessary and
sufficient for every zero of the unnormalized source block to lie on the unit circle.  For use as
a probability weight table, nonnegativity of `disagreement` remains a separate condition. -/
theorem symmetricTwoSpinCircle_iff_fkgDefect_nonneg
    {aligned disagreement : ℝ} (haligned : 0 < aligned) :
    symmetricTwoSpinCircle aligned disagreement ↔
      0 ≤ symmetricTwoSpinFKGDefect aligned disagreement := by
  rw [symmetricTwoSpinCircle_iff_leeYangPairCircle haligned.ne', leeYangPairCircle_iff]
  unfold symmetricTwoSpinFKGDefect
  rw [div_pow]
  have haligned2 : 0 < aligned ^ 2 := sq_pos_of_pos haligned
  constructor
  · intro h
    have h' := (div_le_iff₀ haligned2).mp h
    nlinarith
  · intro h
    apply (div_le_iff₀ haligned2).mpr
    nlinarith

/-- The defect is exactly the aligned-versus-disagreement cross-product difference. -/
theorem twoSpinFKGDefect_eq_crossProduct (c : ℝ) :
    twoSpinFKGDefect c = 1 * 1 - c * c := by
  unfold twoSpinFKGDefect
  ring

/-- The source-facing FKG determinant inequality is the normalized coefficient chamber. -/
theorem twoSpinFKGDefect_nonneg_iff (c : ℝ) :
    0 ≤ twoSpinFKGDefect c ↔ c ^ 2 ≤ 1 := by
  unfold twoSpinFKGDefect
  constructor <;> intro h <;> linarith

/-- Exact two-spin FKG--Lee--Yang equivalence. -/
theorem leeYangPairCircle_iff_twoSpinFKGDefect_nonneg (c : ℝ) :
    leeYangPairCircle c ↔ 0 ≤ twoSpinFKGDefect c := by
  rw [leeYangPairCircle_iff, twoSpinFKGDefect_nonneg_iff]

/-- Exact two-spin FKG--Ihara spectral equivalence. -/
theorem blockSpectralBound_one_neg_two_iff_twoSpinFKGDefect_nonneg (c : ℝ) :
    blockSpectralBound 1 (-2 * c) ↔ 0 ≤ twoSpinFKGDefect c := by
  unfold blockSpectralBound twoSpinFKGDefect
  constructor <;> intro h <;> nlinarith

/-- Exact zero-locus form of the FKG--Ihara equivalence. -/
theorem zerosOnCriticalCircle_one_neg_two_iff_twoSpinFKGDefect_nonneg (c : ℝ) :
    zerosOnCriticalCircle 1 (-2 * c) ↔ 0 ≤ twoSpinFKGDefect c := by
  rw [zerosOnCriticalCircle_iff_spectral_bound (by norm_num),
    blockSpectralBound_one_neg_two_iff_twoSpinFKGDefect_nonneg]

/-- Every nonnegative two-spin coupling `J` produces an FKG-admissible Boltzmann disagreement
weight `exp(-2J)`. -/
theorem twoSpinFKGDefect_exp_neg_two_nonneg {J : ℝ} (hJ : 0 ≤ J) :
    0 ≤ twoSpinFKGDefect (Real.exp (-2 * J)) := by
  rw [twoSpinFKGDefect_nonneg_iff]
  have hc0 : 0 < Real.exp (-2 * J) := Real.exp_pos _
  have hc1 : Real.exp (-2 * J) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  nlinarith

/-- A strictly positive two-spin coupling lies in the interior of the FKG/Lee--Yang chamber. -/
theorem twoSpinFKGDefect_exp_neg_two_pos {J : ℝ} (hJ : 0 < J) :
    0 < twoSpinFKGDefect (Real.exp (-2 * J)) := by
  unfold twoSpinFKGDefect
  have hc0 : 0 < Real.exp (-2 * J) := Real.exp_pos _
  have hc1 : Real.exp (-2 * J) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  nlinarith

end GaloisForLFunctions.RHTower

namespace RHTower

/-- Every prime Euler square-root interaction has a strict ferromagnetic margin. -/
theorem primeEulerFerromagneticCoefficient_lt_one (p : Nat.Primes) :
    primeEulerFerromagneticCoefficient p < 1 := by
  rw [primeEulerFerromagneticCoefficient, Real.exp_lt_one_iff]
  have hp : 0 < primeLeeYangLog p := by
    unfold primeLeeYangLog
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  nlinarith

/-- The prime Euler interaction satisfies the first two-site FKG face strictly, not merely on its
closed boundary. -/
theorem primeEulerTwoSpinFKGDefect_pos (p : Nat.Primes) :
    0 < GaloisForLFunctions.RHTower.twoSpinFKGDefect
      (primeEulerFerromagneticCoefficient p) := by
  unfold GaloisForLFunctions.RHTower.twoSpinFKGDefect
  have hc0 := primeEulerFerromagneticCoefficient_pos p
  have hc1 := primeEulerFerromagneticCoefficient_lt_one p
  nlinarith

end RHTower

namespace GaloisForLFunctions.RHTower

/-- Exact FKG defect of reciprocal Euler pairing.  It is a negative square away from the unit
weight, so the earlier Lee--Yang no-go is also a positive-association obstruction. -/
theorem reciprocalEulerPair_twoSpinFKGDefect_eq {a : ℝ} (ha : a ≠ 0) :
    twoSpinFKGDefect (reciprocalEulerPairCoefficient a) =
      -((a ^ 2 - 1) ^ 2) / (4 * a ^ 2) := by
  unfold twoSpinFKGDefect reciprocalEulerPairCoefficient
  field_simp [ha]
  ring

/-- A positive contracting Euler weight violates the two-site FKG condition strictly. -/
theorem reciprocalEulerPair_twoSpinFKGDefect_neg {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) :
    twoSpinFKGDefect (reciprocalEulerPairCoefficient a) < 0 := by
  rw [reciprocalEulerPair_twoSpinFKGDefect_eq ha.ne']
  have hminus : 0 < 1 - a := sub_pos.mpr ha1
  have hplus : 0 < 1 + a := by linarith
  have hsquare_lt : a ^ 2 < 1 := by
    nlinarith [mul_pos hminus hplus]
  have hnum : 0 < (a ^ 2 - 1) ^ 2 := by
    exact sq_pos_of_ne_zero (by nlinarith)
  have hden : 0 < 4 * a ^ 2 := by
    positivity
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hnum) hden

end GaloisForLFunctions.RHTower
