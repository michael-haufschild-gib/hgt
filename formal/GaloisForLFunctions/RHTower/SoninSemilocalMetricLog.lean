/-
# The regulator-free semilocal logarithmic Euler metric

The positive Gram of adjoining a finite place `p` is multiplication by
`|1-p^(-1/2-is)|²`.  Taking its scalar logarithmic metric before any Gram assembly restores the
unsquared logarithmic Euler coefficients:

`log |1-z|² = -2 Re ∑_(m≥1) z^m/m`, `z = p^(-1/2-is)`.

This file keeps the construction genuinely semilocal.  For a finite set `S` of places the metric
is the finite sum of its local logarithms, and disjoint unions add exactly; no ordering or
exhaustion of the primes is chosen.  The all-prime pointwise sum is deliberately not defined.
Indeed, even after deleting the linear `m=1` shell, the prime-square mode at `s=0` is `-1/p`, so
its absolute prime sum diverges.  Thus the square-summable Sonin column and the unsquared
logarithmic metric live in different summability regimes.  Any global comparison must be a
semilocal descent/relative pairing or perform a further canonical subtraction, not a cutoff limit.
-/
import GaloisForLFunctions.RHTower.HardyTitchmarshSemilocalSquare
import GaloisForLFunctions.RHTower.SoninPrimePowerRegularization
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.NumberTheory.SumPrimeReciprocals

noncomputable section

open scoped BigOperators

namespace RHTower

/-- The scalar logarithmic metric of adjoining the finite place `p`. -/
def semilocalPrimeLogMetric (p s : ℝ) : ℝ :=
  Real.log (semilocalPrimeWeight p s : ℝ)

/-- The `m`-th logarithmic prime-power mode of the local metric.  The `m=0` term is zero by
division in the field and is retained only so the standard Taylor-series API applies directly. -/
def semilocalPrimeLogMode (p s : ℝ) (m : ℕ) : ℝ :=
  -2 * ((((Real.sqrt p : ℂ))⁻¹ *
    (MellinL2.mellinCharacter p s)⁻¹) ^ m / m).re

/-- The local positive Gram metric has the exact logarithmic Euler expansion with unsquared
coefficients `p^(-m/2)/m`. -/
theorem hasSum_semilocalPrimeLogMode (p s : ℝ) (hp : 1 < p) :
    HasSum (semilocalPrimeLogMode p s) (semilocalPrimeLogMetric p s) := by
  let z : ℂ := ((Real.sqrt p : ℂ))⁻¹ *
    (MellinL2.mellinCharacter p s)⁻¹
  have hz : ‖z‖ < 1 := by
    change ‖((Real.sqrt p : ℂ))⁻¹ *
      (MellinL2.mellinCharacter p s)⁻¹‖ < 1
    rw [norm_sqrt_inv_mul_character_inv]
    exact sqrt_inv_lt_one p hp
  have hseries := Complex.hasSum_taylorSeries_neg_log hz
  have hre := Complex.hasSum_re hseries
  have hscaled := hre.mul_left (-2 : ℝ)
  have hmode : HasSum (semilocalPrimeLogMode p s)
      (-2 * (-Complex.log (1 - z)).re) := by
    exact hscaled.congr (fun m => rfl)
  convert hmode using 1
  change Real.log (semilocalPrimeWeight p s : ℝ) =
      -2 * (-Complex.log (1 - z)).re
  have hweight : (semilocalPrimeWeight p s : ℝ) = ‖1 - z‖ ^ 2 := by
    rw [semilocalPrimeWeight_eq_symbol_sq]
    change ‖semilocalPrimeSymbol p s‖ ^ 2 = ‖1 - z‖ ^ 2
    rfl
  rw [hweight, Real.log_pow]
  simp only [Complex.neg_re]
  rw [Complex.log_re]
  norm_num

/-- The logarithmic metric attached to a finite, unordered set of finite places. -/
def finiteSemilocalLogMetric (S : Finset Nat.Primes) (s : ℝ) : ℝ :=
  ∑ p ∈ S, semilocalPrimeLogMetric p s

/-- A finite semilocal metric has the coefficientwise sum of the local logarithmic expansions. -/
theorem hasSum_finiteSemilocalLogMetric
    (S : Finset Nat.Primes) (s : ℝ) :
    HasSum (fun m : ℕ => ∑ p ∈ S, semilocalPrimeLogMode p s m)
      (finiteSemilocalLogMetric S s) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [finiteSemilocalLogMetric]
  | @insert p S hpS ih =>
      have hp : (1 : ℝ) < p := by exact_mod_cast p.prop.one_lt
      simpa [finiteSemilocalLogMetric, Finset.sum_insert hpS] using
        (hasSum_semilocalPrimeLogMode p s hp).add ih

/-- Disjoint place sets glue additively.  This is the finite-site descent law and contains no
choice of enumeration or directed prime cutoff. -/
theorem finiteSemilocalLogMetric_union
    {S T : Finset Nat.Primes} (hST : Disjoint S T) (s : ℝ) :
    finiteSemilocalLogMetric (S ∪ T) s =
      finiteSemilocalLogMetric S s + finiteSemilocalLogMetric T s := by
  rw [finiteSemilocalLogMetric, Finset.sum_union hST,
    finiteSemilocalLogMetric, finiteSemilocalLogMetric]

/-- The tail after the linear prime shell, indexed from the prime-square mode. -/
def semilocalPrimeLogTailMode (p s : ℝ) (k : ℕ) : ℝ :=
  semilocalPrimeLogMode p s (k + 2)

/-- Exact local principal-shell/tail decomposition of the logarithmic metric. -/
theorem semilocalPrimeLogMetric_eq_principal_add_tail
    (p s : ℝ) (hp : 1 < p) :
    semilocalPrimeLogMetric p s =
      semilocalPrimeLogMode p s 1 + ∑' k : ℕ, semilocalPrimeLogTailMode p s k := by
  have h := hasSum_semilocalPrimeLogMode p s hp
  have hs := h.summable
  have hhead : ∑ m ∈ Finset.range 2, semilocalPrimeLogMode p s m =
      semilocalPrimeLogMode p s 1 := by
    norm_num [Finset.sum_range_succ, semilocalPrimeLogMode]
  rw [← h.tsum_eq, ← hs.sum_add_tsum_nat_add 2]
  rw [hhead]
  rfl

/-- At the central spectral parameter the prime-square logarithmic mode is exactly `-1/p`. -/
theorem primeSquareLogMode_zero (p : Nat.Primes) :
    semilocalPrimeLogMode p 0 2 = -(1 / (p : ℝ)) := by
  rw [semilocalPrimeLogMode]
  simp [MellinL2.mellinCharacter]
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hsq : ((Real.sqrt (p : ℝ) : ℂ)) ^ 2 = (p : ℝ) := by
    norm_cast
    exact Real.sq_sqrt hp.le
  rw [hsq]
  norm_num
  field_simp

/-- Removing only the linear shell does not make the unsquared logarithmic metric absolutely
summable: the first retained mode is the divergent prime harmonic series. -/
theorem not_summable_abs_primeSquareLogMode_zero :
    ¬ Summable (fun p : Nat.Primes =>
      |semilocalPrimeLogMode p 0 2|) := by
  intro h
  apply Nat.Primes.not_summable_one_div
  apply h.congr
  intro p
  rw [primeSquareLogMode_zero]
  simp only [abs_neg, abs_of_nonneg (by positivity : 0 ≤ (1 / (p : ℝ)))]

/-- The scalar semilocal tail uses exactly the same logarithmic coefficient as the coupled Sonin
residual block, multiplied by the corresponding unimodular Mellin phase.  Thus the column's
weights are not an ad hoc square-summable replacement: they are the coefficient magnitudes of
the canonical finite-place logarithmic metric. -/
theorem semilocalPrimeLogTailMode_eq_soninCoefficient_phase
    (pk : Nat.Primes × ℕ) (s : ℝ) :
    semilocalPrimeLogTailMode pk.1 s pk.2 =
      -2 * (soninLogPrimePowerCoefficient pk *
        ((MellinL2.mellinCharacter (pk.1 : ℝ) s)⁻¹ ^ (pk.2 + 2))).re := by
  rw [semilocalPrimeLogTailMode, semilocalPrimeLogMode,
    soninLogPrimePowerCoefficient_eq_sqrtInvPow_div]
  congr 2
  rw [mul_pow]
  push_cast
  ring

end RHTower
