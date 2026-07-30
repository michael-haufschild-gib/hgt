import GaloisForLFunctions.RHTower.XiApertureResponseGainPrimeRenormalization
import GaloisForLFunctions.HTGeometry.FredholmDeterminantInfinite

/-!
# Regularized true-aperture response correlation

The true aperture-one fused response gain has correction

`h_p = ((1 + p⁻¹) / (1 - p⁻¹))^3 - 1`.

The preceding renormalization theorem proves that `h_p` is square-summable but not summable:
its exact non-trace-class channel is `6 / p`.  This file constructs the corresponding countable
Hilbert--Schmidt diagonal and applies the HTGeometry Hilbert--Carleman determinant `det₂`.

The resulting logarithmic response is the convergent quadratic resolvent

`-∑_p z h_p^2 / (1 - z h_p)`.

In particular its linear coefficient vanishes exactly: the regularized response cancels the
prime-harmonic Jordan channel rather than estimating it.  The remaining real response is
one-signed on the positive Hilbert--Schmidt disk.  Its infinitesimal quadratic mass has the sharp
source decomposition

`h_p^2 = 36 / p^2 + c_p`,

where `c_p > 0` and `∑_p c_p < ∞`.  Thus diagonal regularization exposes a canonical positive
prime-square correlation, but cannot itself provide the sign-indefinite global FCRJ saturation;
that requires an off-diagonal completed prime--Gamma coupling.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- The non-identity true-aperture response gain, as a complex diagonal entry. -/
def xiApertureOnePrimeResponseCorrelationEntry (p : Nat.Primes) : ℂ :=
  ((xiApertureOnePrimeFusedResponseGainSq p - 1 : ℝ) : ℂ)

/-- The all-prime diagonal response-correlation kernel. -/
def xiApertureOneResponseCorrelationKernel (pq : Nat.Primes × Nat.Primes) : ℂ :=
  HilbertSchmidt.diagMul xiApertureOnePrimeResponseCorrelationEntry pq

/-- The Hilbert--Carleman determinant of the true-aperture response correction. -/
def xiApertureOneResponseCorrelationDet (z : ℂ) : ℂ :=
  HilbertSchmidt.fredholmDet xiApertureOneResponseCorrelationKernel z

/-- The coefficient `6` is the unique scalar prime-harmonic counterterm that makes the gain
correction trace class. -/
theorem summable_xiApertureOnePrimeFusedResponseGainSq_sub_one_sub_c_mul_iff
    (c : ℝ) :
    Summable (fun p : Nat.Primes =>
      xiApertureOnePrimeFusedResponseGainSq p - 1 -
        c * xiTransversePrimeApertureDiskNode 1 p) ↔ c = 6 := by
  constructor
  · intro hsum
    have hscaled : Summable (fun p : Nat.Primes =>
        (6 - c) * xiTransversePrimeApertureDiskNode 1 p) := by
      have hdiff := hsum.sub
        summable_xiApertureOnePrimeFusedResponseRenormalizedGain
      exact hdiff.congr fun p => by
        rw [xiApertureOnePrimeFusedResponseRenormalizedGain]
        ring
    by_contra hc
    have hcoeff : 6 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    have hnodes : Summable (fun p : Nat.Primes =>
        xiTransversePrimeApertureDiskNode 1 p) :=
      (summable_mul_left_iff hcoeff).mp hscaled
    apply Nat.Primes.not_summable_one_div
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, one_div] using hnodes
  · rintro rfl
    simpa [xiApertureOnePrimeFusedResponseRenormalizedGain] using!
      summable_xiApertureOnePrimeFusedResponseRenormalizedGain

/-- The response-correlation diagonal has summable energy. -/
theorem summable_norm_xiApertureOnePrimeResponseCorrelationEntry_sq :
    Summable (fun p : Nat.Primes =>
      ‖xiApertureOnePrimeResponseCorrelationEntry p‖ ^ 2) := by
  have heq : (fun p : Nat.Primes =>
      ‖xiApertureOnePrimeResponseCorrelationEntry p‖ ^ 2) =
      fun p : Nat.Primes =>
        (xiApertureOnePrimeFusedResponseGainSq p - 1) ^ 2 := by
    funext p
    simp only [xiApertureOnePrimeResponseCorrelationEntry, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [heq]
  exact summable_xiApertureOnePrimeFusedResponseGainSq_sub_one_sq

/-- The actual all-prime response-correlation kernel is Hilbert--Schmidt. -/
theorem xiApertureOneResponseCorrelationKernel_isHS :
    HilbertSchmidt.IsHS xiApertureOneResponseCorrelationKernel := by
  exact HilbertSchmidt.isHS_diagMul_infinite
    xiApertureOnePrimeResponseCorrelationEntry
    summable_norm_xiApertureOnePrimeResponseCorrelationEntry_sq

/-- The diagonal regularized response is zero-free; by itself it carries no divisor or Morse
crossing. -/
theorem xiApertureOneResponseCorrelationDet_ne_zero (z : ℂ) :
    xiApertureOneResponseCorrelationDet z ≠ 0 := by
  exact HilbertSchmidt.fredholmDet_ne_zero
    xiApertureOneResponseCorrelationKernel z

/-- Exact Plemelj identity for the regularized true-aperture response. -/
theorem logDeriv_xiApertureOneResponseCorrelationDet
    (r : ℝ)
    (hr : r * HilbertSchmidt.hsNorm xiApertureOneResponseCorrelationKernel < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) r) :
    logDeriv xiApertureOneResponseCorrelationDet z =
      -∑' p : Nat.Primes,
        z * xiApertureOnePrimeResponseCorrelationEntry p ^ 2 /
          (1 - z * xiApertureOnePrimeResponseCorrelationEntry p) := by
  exact HilbertSchmidt.logDeriv_fredholmDet_diagMul_infinite
    xiApertureOnePrimeResponseCorrelationEntry
    summable_norm_xiApertureOnePrimeResponseCorrelationEntry_sq r hr z hz

/-- Exact cancellation of the non-summable linear Jordan channel. -/
theorem logDeriv_xiApertureOneResponseCorrelationDet_zero :
    logDeriv xiApertureOneResponseCorrelationDet 0 = 0 := by
  let M := HilbertSchmidt.hsNorm xiApertureOneResponseCorrelationKernel
  let r := (M + 1)⁻¹
  have hM0 : 0 ≤ M := HilbertSchmidt.hsNorm_nonneg _
  have hden : 0 < M + 1 := by linarith
  have hr0 : 0 < r := inv_pos.mpr hden
  have hr : r * M < 1 := by
    change (M + 1)⁻¹ * M < 1
    rw [show (M + 1)⁻¹ * M = M / (M + 1) by
      rw [div_eq_mul_inv, mul_comm]]
    exact (div_lt_one hden).2 (by linarith)
  have hz : (0 : ℂ) ∈ Metric.ball (0 : ℂ) r := by
    simpa [Metric.mem_ball] using hr0
  simpa using logDeriv_xiApertureOneResponseCorrelationDet r hr 0 hz

/-- The real quadratic-resolvent summand at positive coupling. -/
def xiApertureOneResponseCorrelationResolventTerm (x : ℝ) (p : Nat.Primes) : ℝ :=
  x * (xiApertureOnePrimeFusedResponseGainSq p - 1) ^ 2 /
    (1 - x * (xiApertureOnePrimeFusedResponseGainSq p - 1))

/-- Every positive-coupling summand is strictly positive on the Hilbert--Schmidt disk. -/
theorem xiApertureOneResponseCorrelationResolventTerm_pos
    (x : ℝ) (hx : 0 < x)
    (hxK : x * HilbertSchmidt.hsNorm xiApertureOneResponseCorrelationKernel < 1)
    (p : Nat.Primes) :
    0 < xiApertureOneResponseCorrelationResolventTerm x p := by
  let h : ℝ := xiApertureOnePrimeFusedResponseGainSq p - 1
  have hhpos : 0 < h := by
    dsimp [h]
    exact lt_of_lt_of_le
      (mul_pos (by norm_num) (xiTransversePrimeApertureDiskNode_pos 1 p))
      (six_mul_diskNode_le_xiApertureOnePrimeFusedResponseGainSq_sub_one p)
  have hhK : h ≤ HilbertSchmidt.hsNorm xiApertureOneResponseCorrelationKernel := by
    have hraw := HilbertSchmidt.norm_le_hsNorm_diagMul_infinite
      xiApertureOnePrimeResponseCorrelationEntry
      summable_norm_xiApertureOnePrimeResponseCorrelationEntry_sq p
    change ‖(h : ℂ)‖ ≤
      HilbertSchmidt.hsNorm xiApertureOneResponseCorrelationKernel at hraw
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hhpos] using hraw
  have hxhh : x * h < 1 :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hhK hx.le) hxK
  have hden : 0 < 1 - x * h := by linarith
  have hnum : 0 < x * h ^ 2 := mul_pos hx (sq_pos_of_pos hhpos)
  change 0 < x * h ^ 2 / (1 - x * h)
  exact div_pos hnum hden

/-- Positive correction to the universal `36 / p²` quadratic channel. -/
def xiApertureOnePrimeResponseCorrelationRemainder (p : Nat.Primes) : ℝ :=
  (xiApertureOnePrimeFusedResponseGainSq p - 1) ^ 2 -
    36 * xiTransversePrimeApertureDiskNode 1 p ^ 2

/-- Exact pointwise correlation remainder after removing `36 / p²`. -/
theorem xiApertureOnePrimeResponseCorrelationRemainder_eq (p : Nat.Primes) :
    xiApertureOnePrimeResponseCorrelationRemainder p =
      12 * xiTransversePrimeApertureDiskNode 1 p *
          xiApertureOnePrimeFusedResponseRenormalizedGain p +
        xiApertureOnePrimeFusedResponseRenormalizedGain p ^ 2 := by
  rw [xiApertureOnePrimeResponseCorrelationRemainder,
    xiApertureOnePrimeFusedResponseRenormalizedGain]
  ring

/-- The correction beyond `36 / p²` is strictly positive at every prime. -/
theorem xiApertureOnePrimeResponseCorrelationRemainder_pos (p : Nat.Primes) :
    0 < xiApertureOnePrimeResponseCorrelationRemainder p := by
  rw [xiApertureOnePrimeResponseCorrelationRemainder_eq]
  exact add_pos_of_pos_of_nonneg
    (mul_pos
      (mul_pos (by norm_num) (xiTransversePrimeApertureDiskNode_pos 1 p))
      (xiApertureOnePrimeFusedResponseRenormalizedGain_pos p))
    (sq_nonneg _)

/-- The correction beyond the universal prime-square channel is trace class. -/
theorem summable_xiApertureOnePrimeResponseCorrelationRemainder :
    Summable xiApertureOnePrimeResponseCorrelationRemainder := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  have hnodes : Summable (fun p : Nat.Primes =>
      xiTransversePrimeApertureDiskNode 1 p ^ 2) := by
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] using hprime
  simpa [xiApertureOnePrimeResponseCorrelationRemainder] using!
    summable_xiApertureOnePrimeFusedResponseGainSq_sub_one_sq.sub
      (hnodes.mul_left 36)

end

end RHTower
