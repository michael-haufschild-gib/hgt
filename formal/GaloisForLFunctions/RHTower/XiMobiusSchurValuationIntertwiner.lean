import GaloisForLFunctions.RHTower.XiTransverseGammaValuationCoherence
import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicFockLocal

/-!
# The Möbius Schur depth derivative is the summable valuation marking

At unit aperture, the forward depth difference of the actual local Möbius--Bernoulli Schur
factor is a positive diagonal damping of the half-shifted valuation coordinate selected by the
Gamma completion.  The resulting all-prime frame is square summable, retains the exact
pseudohyperbolic aperture metric after normalization, and separates every finite prime packet by
a weighted Vandermonde determinant.

The inverse diagonal dressing is unbounded along the primes.  Thus this theorem supplies a
canonical globally Hilbertian source marking, while ruling out the naive channelwise recovery of
the undamped Gamma--valuation frame as the missing bounded Xi intertwiner.
-/

namespace RHTower

noncomputable section

open scoped BigOperators
open Matrix

/-- At unit aperture the local Schur weight is the reciprocal-prime disk node. -/
theorem primeSchurWeight_one_eq_xiTransversePrimeApertureDiskNode
    (p : Nat.Primes) :
    primeSchurWeight 1 p = xiTransversePrimeApertureDiskNode 1 p := by
  simp [primeSchurWeight, xiTransversePrimeApertureDiskNode]

/-- The real nonnegative-integer depth sample of the local Möbius--Bernoulli Schur factor. -/
def xiMobiusPrimeSchurDepthSample (p : Nat.Primes) (e : ℕ) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  (1 - q ^ (e + 1)) / (1 + q)

/-- The depth sample is the literal local factor of the source Möbius Schur contraction. -/
theorem bernoulliSignedSchurFactor_one_nat_eq_xiMobiusPrimeSchurDepthSample
    (p : Nat.Primes) (e : ℕ) :
    bernoulliSignedSchurFactor (primeSchurWeight 1 p) (Real.log (p : ℝ)) (e : ℂ) =
      (xiMobiusPrimeSchurDepthSample p e : ℂ) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hshift :
      Complex.exp (-(((1 : ℕ) : ℂ) + (e : ℂ)) * (Real.log (p : ℝ) : ℂ)) =
        (q : ℂ) ^ (e + 1) := by
    rw [show -(((1 : ℕ) : ℂ) + (e : ℂ)) * (Real.log (p : ℝ) : ℂ) =
        -((e + 1 : ℕ) : ℂ) * GaloisForLFunctions.HTGeometry.primeLogClock p by
      change -(((1 : ℕ) : ℂ) + (e : ℂ)) *
          (Real.log ((p : ℕ) : ℝ) : ℂ) =
        -((e + 1 : ℕ) : ℂ) * (Real.log ((p : ℕ) : ℝ) : ℂ)
      push_cast
      ring]
    change GaloisForLFunctions.HTGeometry.primeShiftFactor ((e + 1 : ℕ) : ℂ) p =
      (q : ℂ) ^ (e + 1)
    rw [primeShiftFactor_nat_eq_xiTransversePrimeApertureDiskNode]
    rw [show e + 1 = (e + 1) * 1 by omega,
      xiTransversePrimeApertureDiskNode_mul]
    simp [q]
  have hweight : Real.exp (-1 * Real.log (p : ℝ)) = q := by
    simpa [primeSchurWeight] using
      (primeSchurWeight_one_eq_xiTransversePrimeApertureDiskNode p)
  have hexp :
      Complex.exp (-(((1 : ℝ) : ℂ) + (e : ℂ)) * (Real.log (p : ℝ) : ℂ)) =
        (q : ℂ) ^ (e + 1) := by
    simpa using hshift
  rw [bernoulliSignedSchurFactor_prime_eq, hexp, hweight]
  simp only [xiMobiusPrimeSchurDepthSample, q]
  push_cast
  rfl

/-- The source-selected forward difference in valuation depth. -/
def xiMobiusPrimeSchurForwardDifference (p : Nat.Primes) (e : ℕ) : ℝ :=
  xiMobiusPrimeSchurDepthSample p (e + 1) - xiMobiusPrimeSchurDepthSample p e

/-- Closed geometric form of the local forward difference. -/
theorem xiMobiusPrimeSchurForwardDifference_eq_geometric
    (p : Nat.Primes) (e : ℕ) :
    xiMobiusPrimeSchurForwardDifference p e =
      xiTransversePrimeApertureDiskNode 1 p ^ (e + 1) *
        (1 - xiTransversePrimeApertureDiskNode 1 p) /
          (1 + xiTransversePrimeApertureDiskNode 1 p) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hden : 1 + q ≠ 0 := by
    linarith
  simp only [xiMobiusPrimeSchurForwardDifference, xiMobiusPrimeSchurDepthSample,
    pow_succ]
  field_simp [hden]
  ring

/-- The local damping from the Gamma--valuation Hardy frame to the Möbius depth derivative. -/
def xiMobiusPrimeSchurValuationDamping (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  Real.sqrt q / (1 + q)

theorem xiMobiusPrimeSchurValuationDamping_pos (p : Nat.Primes) :
    0 < xiMobiusPrimeSchurValuationDamping p := by
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  exact div_pos (Real.sqrt_pos.2 hq) (by linarith)

/-- The source damping is exactly the square root of the local squarefree-parity Fisher
variance.  Thus the Möbius difference frame is the Fisher-damped Gamma--valuation frame. -/
theorem xiMobiusPrimeSchurValuationDamping_sq_eq_parityVariance
    (p : Nat.Primes) :
    xiMobiusPrimeSchurValuationDamping p ^ (2 : ℕ) =
      dyadicSquarefreeParityVariance (primeSchurWeight 1 p) := by
  have hq0 : 0 ≤ xiTransversePrimeApertureDiskNode 1 p :=
    (xiTransversePrimeApertureDiskNode_pos 1 p).le
  rw [primeSchurWeight_one_eq_xiTransversePrimeApertureDiskNode]
  simp only [xiMobiusPrimeSchurValuationDamping,
    dyadicSquarefreeParityVariance, div_pow]
  rw [Real.sq_sqrt hq0]

/-- The actual local Schur depth derivative is exactly the damped half-shifted valuation frame. -/
theorem xiMobiusPrimeSchurForwardDifference_eq_dampedValuation
    (p : Nat.Primes) (e : ℕ) :
    xiMobiusPrimeSchurForwardDifference p e =
      xiMobiusPrimeSchurValuationDamping p *
        xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 <= q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hden : 1 + q ≠ 0 := by linarith
  rw [xiMobiusPrimeSchurForwardDifference_eq_geometric]
  simp only [xiMobiusPrimeSchurValuationDamping,
    xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement, pow_succ]
  field_simp [hden]
  rw [Real.sq_sqrt hq0]
  ring

/-- The completed Gram kernel of the genuine Möbius Schur depth differences. -/
def xiMobiusPrimeSchurDifferenceKernel (p r : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  q * s * (1 - q) * (1 - s) / ((1 + q) * (1 + s) * (1 - q * s))

/-- The closed kernel is the exact completed Gram of all source-selected depth differences. -/
theorem tsum_xiMobiusPrimeSchurForwardDifference_mul_eq_kernel
    (p r : Nat.Primes) :
    (∑' e : ℕ, xiMobiusPrimeSchurForwardDifference p e *
      xiMobiusPrimeSchurForwardDifference r e) =
      xiMobiusPrimeSchurDifferenceKernel p r := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  have hq0 : 0 <= q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hs0 : 0 <= s := (xiTransversePrimeApertureDiskNode_pos 1 r).le
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hs1 : s < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) r
  have hqs0 : 0 <= q * s := mul_nonneg hq0 hs0
  have hqs1 : q * s < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hq0 hq1 hs1.le
  have hqplus : 1 + q ≠ 0 := by linarith
  have hsplus : 1 + s ≠ 0 := by linarith
  have hqsminus : 1 - q * s ≠ 0 := by linarith
  calc
    (∑' e : ℕ, xiMobiusPrimeSchurForwardDifference p e *
        xiMobiusPrimeSchurForwardDifference r e) =
        ∑' e : ℕ,
          (q * s * (1 - q) * (1 - s) / ((1 + q) * (1 + s))) *
            (q * s) ^ e := by
      apply tsum_congr
      intro e
      rw [xiMobiusPrimeSchurForwardDifference_eq_geometric,
        xiMobiusPrimeSchurForwardDifference_eq_geometric]
      change q ^ (e + 1) * (1 - q) / (1 + q) *
          (s ^ (e + 1) * (1 - s) / (1 + s)) = _
      simp only [pow_succ, mul_pow]
      field_simp [hqplus, hsplus]
    _ = (q * s * (1 - q) * (1 - s) / ((1 + q) * (1 + s))) *
        ∑' e : ℕ, (q * s) ^ e := by
      rw [tsum_mul_left]
    _ = (q * s * (1 - q) * (1 - s) / ((1 + q) * (1 + s))) *
        (1 - q * s)⁻¹ := by
      rw [tsum_geometric_of_lt_one hqs0 hqs1]
    _ = xiMobiusPrimeSchurDifferenceKernel p r := by
      change (q * s * (1 - q) * (1 - s) / ((1 + q) * (1 + s))) *
          (1 - q * s)⁻¹ =
        q * s * (1 - q) * (1 - s) /
          ((1 + q) * (1 + s) * (1 - q * s))
      field_simp [hqplus, hsplus, hqsminus]

/-- Exact diagonal mass of one prime in the globally damped source frame. -/
theorem xiMobiusPrimeSchurDifferenceKernel_self (p : Nat.Primes) :
    xiMobiusPrimeSchurDifferenceKernel p p =
      xiTransversePrimeApertureDiskNode 1 p ^ (2 : ℕ) *
        (1 - xiTransversePrimeApertureDiskNode 1 p) /
          (1 + xiTransversePrimeApertureDiskNode 1 p) ^ (3 : ℕ) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hplus : 1 + q ≠ 0 := by linarith
  have hminus : 1 - q ≠ 0 := by linarith
  simp only [xiMobiusPrimeSchurDifferenceKernel]
  rw [show xiTransversePrimeApertureDiskNode 1 p = q by rfl]
  rw [show 1 - q * q = (1 - q) * (1 + q) by ring]
  field_simp [hplus, hminus]

theorem xiMobiusPrimeSchurDifferenceKernel_self_nonneg (p : Nat.Primes) :
    0 <= xiMobiusPrimeSchurDifferenceKernel p p := by
  rw [xiMobiusPrimeSchurDifferenceKernel_self]
  have hq0 := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : xiTransversePrimeApertureDiskNode 1 p < 1 :=
    xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  exact div_nonneg
    (mul_nonneg (sq_nonneg _) (sub_nonneg.mpr hq1.le))
    (pow_nonneg (by linarith :
      0 ≤ 1 + xiTransversePrimeApertureDiskNode 1 p) 3)

/-- The source damping improves the prime-diagonal mass from harmonic to square summable. -/
theorem xiMobiusPrimeSchurDifferenceKernel_self_le_invSq (p : Nat.Primes) :
    xiMobiusPrimeSchurDifferenceKernel p p <=
      xiTransversePrimeApertureDiskNode 1 p ^ (2 : ℕ) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 <= q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hden : 0 < (1 + q) ^ (3 : ℕ) := by positivity
  have hnum : 1 - q <= (1 + q) ^ (3 : ℕ) := by
    nlinarith [sq_nonneg q, mul_nonneg (sq_nonneg q) hq0]
  have hfrac : (1 - q) / (1 + q) ^ (3 : ℕ) <= 1 :=
    (div_le_one hden).2 hnum
  rw [xiMobiusPrimeSchurDifferenceKernel_self]
  change q ^ (2 : ℕ) * (1 - q) / (1 + q) ^ (3 : ℕ) <= q ^ (2 : ℕ)
  calc
    q ^ (2 : ℕ) * (1 - q) / (1 + q) ^ (3 : ℕ) =
        q ^ (2 : ℕ) * ((1 - q) / (1 + q) ^ (3 : ℕ)) := by ring
    _ <= q ^ (2 : ℕ) * 1 := mul_le_mul_of_nonneg_left hfrac (sq_nonneg q)
    _ = q ^ (2 : ℕ) := mul_one _

/-- The complete all-prime Möbius difference frame has finite Hilbert mass. -/
theorem summable_xiMobiusPrimeSchurDifferenceKernel_self :
    Summable (fun p : Nat.Primes => xiMobiusPrimeSchurDifferenceKernel p p) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ (2 : ℕ))⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ (2 : ℕ))⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  have hnodes : Summable
      (fun p : Nat.Primes => xiTransversePrimeApertureDiskNode 1 p ^ (2 : ℕ)) := by
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] using hprime
  exact Summable.of_nonneg_of_le
    xiMobiusPrimeSchurDifferenceKernel_self_nonneg
    xiMobiusPrimeSchurDifferenceKernel_self_le_invSq hnodes

/-- Squared unit-normalized correlation of the globally summable source frame. -/
def xiMobiusPrimeSchurDifferenceNormalizedCorrelationSq
    (p r : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  (1 - q ^ (2 : ℕ)) * (1 - s ^ (2 : ℕ)) / (1 - q * s) ^ (2 : ℕ)

/-- The displayed correlation is literally the unit-normalized completed source Gram. -/
theorem xiMobiusPrimeSchurDifferenceNormalizedCorrelationSq_eq_kernelRatio
    (p r : Nat.Primes) :
    xiMobiusPrimeSchurDifferenceNormalizedCorrelationSq p r =
      xiMobiusPrimeSchurDifferenceKernel p r ^ (2 : ℕ) /
        (xiMobiusPrimeSchurDifferenceKernel p p *
          xiMobiusPrimeSchurDifferenceKernel r r) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hs0 : 0 < s := xiTransversePrimeApertureDiskNode_pos 1 r
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hs1 : s < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) r
  have hqminus : 1 - q ≠ 0 := by linarith
  have hsminus : 1 - s ≠ 0 := by linarith
  have hqplus : 1 + q ≠ 0 := by linarith
  have hsplus : 1 + s ≠ 0 := by linarith
  have hqsminus : 1 - q * s ≠ 0 := by
    have hqs : q * s < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hq0.le hq1 hs1.le
    linarith
  rw [xiMobiusPrimeSchurDifferenceKernel_self,
    xiMobiusPrimeSchurDifferenceKernel_self]
  change (1 - q ^ (2 : ℕ)) * (1 - s ^ (2 : ℕ)) / (1 - q * s) ^ (2 : ℕ) =
    (q * s * (1 - q) * (1 - s) /
        ((1 + q) * (1 + s) * (1 - q * s))) ^ (2 : ℕ) /
      ((q ^ (2 : ℕ) * (1 - q) / (1 + q) ^ (3 : ℕ)) *
        (s ^ (2 : ℕ) * (1 - s) / (1 + s) ^ (3 : ℕ)))
  field_simp [hq0.ne', hs0.ne', hqminus, hsminus, hqplus, hsplus, hqsminus]
  ring

/-- The source damping does not change the normalized true-aperture geometry. -/
theorem one_sub_xiMobiusPrimeSchurDifferenceNormalizedCorrelationSq
    (p r : Nat.Primes) :
    1 - xiMobiusPrimeSchurDifferenceNormalizedCorrelationSq p r =
      ((xiTransversePrimeApertureDiskNode 1 p -
          xiTransversePrimeApertureDiskNode 1 r) /
        (1 - xiTransversePrimeApertureDiskNode 1 p *
          xiTransversePrimeApertureDiskNode 1 r)) ^ (2 : ℕ) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let s := xiTransversePrimeApertureDiskNode 1 r
  have hq0 : 0 <= q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hs0 : 0 <= s := (xiTransversePrimeApertureDiskNode_pos 1 r).le
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hs1 : s < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) r
  have hden : 1 - q * s ≠ 0 := by
    have : q * s < 1 := mul_lt_one_of_nonneg_of_lt_one_left hq0 hq1 hs1.le
    linarith
  change 1 - (1 - q ^ (2 : ℕ)) * (1 - s ^ (2 : ℕ)) / (1 - q * s) ^ (2 : ℕ) =
    ((q - s) / (1 - q * s)) ^ (2 : ℕ)
  field_simp [hden]
  ring

/-- Source-difference observation matrix: rows are depths and columns are actual prime channels. -/
def xiMobiusPrimeSchurDifferenceSamplingMatrix
    {N : ℕ} (p : Fin N -> Nat.Primes) : Matrix (Fin N) (Fin N) ℝ :=
  fun e j => xiMobiusPrimeSchurForwardDifference (p j) e

/-- The actual source-difference matrix is a weighted reciprocal-prime Vandermonde. -/
theorem xiMobiusPrimeSchurDifferenceSamplingMatrix_factorization
    {N : ℕ} (p : Fin N -> Nat.Primes) :
    xiMobiusPrimeSchurDifferenceSamplingMatrix p =
      (Matrix.vandermonde
        (fun j => xiTransversePrimeApertureDiskNode 1 (p j)))ᵀ *
      Matrix.diagonal
        (fun j => xiTransversePrimeApertureDiskNode 1 (p j) *
          (1 - xiTransversePrimeApertureDiskNode 1 (p j)) /
          (1 + xiTransversePrimeApertureDiskNode 1 (p j))) := by
  classical
  ext e j
  rw [Matrix.mul_diagonal]
  change xiMobiusPrimeSchurForwardDifference (p j) e = _
  rw [xiMobiusPrimeSchurForwardDifference_eq_geometric]
  simp [Matrix.vandermonde, pow_succ]
  ring

/-- The summable source frame intrinsically marks every finite injective prime packet. -/
theorem xiMobiusPrimeSchurDifferenceSamplingMatrix_det_ne_zero
    {N : ℕ} {p : Fin N -> Nat.Primes} (hp : Function.Injective p) :
    (xiMobiusPrimeSchurDifferenceSamplingMatrix p).det ≠ 0 := by
  let q : Fin N -> ℝ := fun j => xiTransversePrimeApertureDiskNode 1 (p j)
  let d : Fin N -> ℝ := fun j => q j * (1 - q j) / (1 + q j)
  have hq : Function.Injective q :=
    xiTransversePrimeApertureDiskNode_one_injective.comp hp
  have hd : forall j, d j ≠ 0 := by
    intro j
    have hq0 : 0 < q j := xiTransversePrimeApertureDiskNode_pos 1 (p j)
    have hq1 : q j < 1 :=
      xiTransversePrimeApertureDiskNode_lt_one (by norm_num) (p j)
    dsimp only [d]
    positivity
  rw [xiMobiusPrimeSchurDifferenceSamplingMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  apply mul_ne_zero
  · exact Matrix.det_vandermonde_ne_zero_iff.mpr hq
  · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
    exact fun j _ => hd j

/-- The inverse diagonal dressing from the summable source frame to the Gamma--valuation frame. -/
def xiMobiusPrimeSchurValuationRecovery (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  (1 + q) / Real.sqrt q

theorem xiMobiusPrimeSchurValuationRecovery_pos (p : Nat.Primes) :
    0 < xiMobiusPrimeSchurValuationRecovery p := by
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  exact div_pos (by linarith)
    (Real.sqrt_pos.2 (xiTransversePrimeApertureDiskNode_pos 1 p))

/-- Recovery exactly removes the source damping at every valuation depth. -/
theorem xiMobiusPrimeSchurValuationRecovery_mul_forwardDifference
    (p : Nat.Primes) (e : ℕ) :
    xiMobiusPrimeSchurValuationRecovery p *
        xiMobiusPrimeSchurForwardDifference p e =
      xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  rw [xiMobiusPrimeSchurForwardDifference_eq_dampedValuation]
  have hq := xiTransversePrimeApertureDiskNode_pos 1 p
  simp only [xiMobiusPrimeSchurValuationRecovery,
    xiMobiusPrimeSchurValuationDamping]
  field_simp [Real.sqrt_ne_zero'.mpr hq]

/-- The corrected Gamma conductor cross is the first recovered Möbius Schur depth difference. -/
theorem gammaValuationHardyCorrectedCross_eq_mobiusSchurDifference
    (p : Nat.Primes) :
    gammaValuationHardyRenormalizer p * gammaConductorPrimeNormalizedCross p =
      -(3 * Real.sqrt 2 / 4) *
        (xiMobiusPrimeSchurValuationRecovery p *
          xiMobiusPrimeSchurForwardDifference p 0) := by
  rw [gammaValuationHardyCorrectedCross_eq,
    xiMobiusPrimeSchurValuationRecovery_mul_forwardDifference]
  rfl

/-- The inverse recovery already costs at least the square root of the prime scale. -/
theorem prime_le_xiMobiusPrimeSchurValuationRecovery_sq (p : Nat.Primes) :
    (p : ℝ) <= xiMobiusPrimeSchurValuationRecovery p ^ (2 : ℕ) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hpq : (p : ℝ) * q = 1 := by
    change (p : ℝ) * xiTransversePrimeApertureDiskNode 1 p = 1
    rw [xiTransversePrimeApertureDiskNode_one_eq_inv]
    exact mul_inv_cancel₀ hp0.ne'
  have hrec : xiMobiusPrimeSchurValuationRecovery p ^ (2 : ℕ) = (1 + q) ^ (2 : ℕ) / q := by
    simp only [xiMobiusPrimeSchurValuationRecovery, q, div_pow]
    rw [Real.sq_sqrt hq0.le]
  rw [hrec, le_div_iff₀ hq0]
  nlinarith [sq_nonneg q]

/-- The channelwise inverse dressing is unbounded along the primes. -/
theorem xiMobiusPrimeSchurValuationRecovery_sq_unbounded (B : ℝ) :
    exists p : Nat.Primes, B < xiMobiusPrimeSchurValuationRecovery p ^ (2 : ℕ) := by
  by_cases hB : B < 0
  · refine ⟨⟨2, Nat.prime_two⟩, lt_trans hB ?_⟩
    exact sq_pos_of_pos (xiMobiusPrimeSchurValuationRecovery_pos ⟨2, Nat.prime_two⟩)
  · have hB0 : 0 <= B := le_of_not_gt hB
    obtain ⟨n, hn, hprime⟩ := Nat.exists_infinite_primes (Nat.ceil B + 1)
    let p : Nat.Primes := ⟨n, hprime⟩
    refine ⟨p, lt_of_lt_of_le ?_ (prime_le_xiMobiusPrimeSchurValuationRecovery_sq p)⟩
    have hceil : B <= (Nat.ceil B : ℝ) := Nat.le_ceil B
    have hn' : (Nat.ceil B : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (Nat.lt_succ_self (Nat.ceil B)) hn)
    exact lt_of_le_of_lt hceil hn'

end

end RHTower
