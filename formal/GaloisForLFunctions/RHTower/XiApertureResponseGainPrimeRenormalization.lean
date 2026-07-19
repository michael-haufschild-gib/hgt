import GaloisForLFunctions.RHTower.XiAperturePoissonUnitApertureHilbertTransport
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# Prime renormalization of the Xi aperture response gain

The exact aperture-one response gain is not a trace-class perturbation of the identity: its
first correction is the divergent prime-harmonic channel `6 / p`.  Subtracting that forced channel
leaves a positive remainder bounded by `144 / p^2`.  Thus the gain has the canonical decomposition

`gain = 1 + 6 / p + positive summable remainder`.

This is the positive survivor of the trace-class no-go.  It identifies the determinant-compatible
renormalization but does not construct the completed response operator or prove RH.
-/

namespace RHTower

noncomputable section

/-- The response gain after removing its identity and prime-harmonic channels. -/
def xiApertureOnePrimeFusedResponseRenormalizedGain (p : Nat.Primes) : ℝ :=
  xiApertureOnePrimeFusedResponseGainSq p - 1 -
    6 * xiTransversePrimeApertureDiskNode 1 p

/-- Exact second-order remainder after the forced `1 + 6/p` renormalization. -/
theorem xiApertureOnePrimeFusedResponseRenormalizedGain_eq (p : Nat.Primes) :
    xiApertureOnePrimeFusedResponseRenormalizedGain p =
      let q := xiTransversePrimeApertureDiskNode 1 p
      2 * q ^ 2 * (9 - 8 * q + 3 * q ^ 2) / (1 - q) ^ 3 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hden : 1 - q ≠ 0 := by linarith
  rw [xiApertureOnePrimeFusedResponseRenormalizedGain,
    xiApertureOnePrimeFusedResponseGainSq]
  change ((1 + q) / (1 - q)) ^ 3 - 1 - 6 * q =
    2 * q ^ 2 * (9 - 8 * q + 3 * q ^ 2) / (1 - q) ^ 3
  field_simp [hden]
  ring

/-- The renormalized gain is strictly positive at every prime. -/
theorem xiApertureOnePrimeFusedResponseRenormalizedGain_pos (p : Nat.Primes) :
    0 < xiApertureOnePrimeFusedResponseRenormalizedGain p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hpoly : 0 < 9 - 8 * q + 3 * q ^ 2 := by
    nlinarith [sq_nonneg (3 * q - 4)]
  rw [xiApertureOnePrimeFusedResponseRenormalizedGain_eq]
  change 0 < 2 * q ^ 2 * (9 - 8 * q + 3 * q ^ 2) / (1 - q) ^ 3
  positivity

/-- The positive remainder is uniformly dominated by the prime-square channel. -/
theorem xiApertureOnePrimeFusedResponseRenormalizedGain_le_invSq
    (p : Nat.Primes) :
    xiApertureOnePrimeFusedResponseRenormalizedGain p ≤
      144 * xiTransversePrimeApertureDiskNode 1 p ^ 2 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hqhalf : q ≤ 1 / 2 := by
    rw [show q = ((p : ℝ))⁻¹ by
      exact xiTransversePrimeApertureDiskNode_one_eq_inv p]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  have hqSq : q ^ 2 ≤ q / 2 := by
    have hmul : q * (q - 1 / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hq0.le (by linarith)
    nlinarith
  have hpoly : 9 - 8 * q + 3 * q ^ 2 ≤ 9 := by
    nlinarith
  have hbase : (1 / 2 : ℝ) ≤ 1 - q := by linarith
  have hdenlower : (1 / 8 : ℝ) ≤ (1 - q) ^ 3 := by
    calc
      (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 - q) ^ 3 := by gcongr
  rw [xiApertureOnePrimeFusedResponseRenormalizedGain_eq]
  change 2 * q ^ 2 * (9 - 8 * q + 3 * q ^ 2) / (1 - q) ^ 3 ≤ 144 * q ^ 2
  rw [div_le_iff₀ (pow_pos (by linarith : 0 < 1 - q) 3)]
  have hnum : 2 * q ^ 2 * (9 - 8 * q + 3 * q ^ 2) ≤ 18 * q ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ 2 * q ^ 2 by positivity)
    nlinarith
  have hrhs : 18 * q ^ 2 ≤ 144 * q ^ 2 * (1 - q) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hdenlower
      (show 0 ≤ 144 * q ^ 2 by positivity)
    nlinarith
  exact hnum.trans hrhs

/-- After removing the identity, the gain still dominates the divergent `6/p` channel. -/
theorem six_mul_diskNode_le_xiApertureOnePrimeFusedResponseGainSq_sub_one
    (p : Nat.Primes) :
    6 * xiTransversePrimeApertureDiskNode 1 p ≤
      xiApertureOnePrimeFusedResponseGainSq p - 1 := by
  have hpos := xiApertureOnePrimeFusedResponseRenormalizedGain_pos p
  rw [xiApertureOnePrimeFusedResponseRenormalizedGain] at hpos
  linarith

/-- The non-identity gain is at most a fixed multiple of the reciprocal-prime channel. -/
theorem xiApertureOnePrimeFusedResponseGainSq_sub_one_le
    (p : Nat.Primes) :
    xiApertureOnePrimeFusedResponseGainSq p - 1 ≤
      52 * xiTransversePrimeApertureDiskNode 1 p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.prop.two_le
  have hqhalf : q ≤ 1 / 2 := by
    rw [show q = ((p : ℝ))⁻¹ by
      exact xiTransversePrimeApertureDiskNode_one_eq_inv p]
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hp2)
  have hqSq : q ^ 2 ≤ 1 / 4 := by
    have hmul : q * (q - 1 / 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hq0.le (by linarith)
    nlinarith
  have hpoly : 3 + q ^ 2 ≤ 13 / 4 := by linarith
  have hbase : (1 / 2 : ℝ) ≤ 1 - q := by linarith
  have hdenlower : (1 / 8 : ℝ) ≤ (1 - q) ^ 3 := by
    calc
      (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 3 := by norm_num
      _ ≤ (1 - q) ^ 3 := by gcongr
  rw [xiApertureOnePrimeFusedResponseGainSq]
  change ((1 + q) / (1 - q)) ^ 3 - 1 ≤ 52 * q
  have hden : 0 < (1 - q) ^ 3 := pow_pos (by linarith) 3
  rw [show ((1 + q) / (1 - q)) ^ 3 - 1 =
      2 * q * (3 + q ^ 2) / (1 - q) ^ 3 by
    field_simp [ne_of_gt (by linarith : 0 < 1 - q)]
    ring]
  rw [div_le_iff₀ hden]
  have hnum : 2 * q * (3 + q ^ 2) ≤ (13 / 2) * q := by
    have hmul := mul_le_mul_of_nonneg_left hpoly
      (show 0 ≤ 2 * q by positivity)
    nlinarith
  have hrhs : (13 / 2) * q ≤ 52 * q * (1 - q) ^ 3 := by
    have hmul := mul_le_mul_of_nonneg_left hdenlower
      (show 0 ≤ 52 * q by positivity)
    nlinarith
  exact hnum.trans hrhs

/-- The gain correction is not summable over primes, so it is not a trace-class diagonal. -/
theorem not_summable_xiApertureOnePrimeFusedResponseGainSq_sub_one :
    ¬ Summable (fun p : Nat.Primes =>
      xiApertureOnePrimeFusedResponseGainSq p - 1) := by
  intro hsum
  have hscaled : Summable (fun p : Nat.Primes => 6 * (p : ℝ)⁻¹) := by
    apply Summable.of_nonneg_of_le
    · intro p
      positivity
    · intro p
      simpa [xiTransversePrimeApertureDiskNode_one_eq_inv] using
        six_mul_diskNode_le_xiApertureOnePrimeFusedResponseGainSq_sub_one p
    · exact hsum
  have hinv : Summable (fun p : Nat.Primes => (p : ℝ)⁻¹) :=
    (summable_mul_left_iff (by norm_num : (6 : ℝ) ≠ 0)).mp hscaled
  apply Nat.Primes.not_summable_one_div
  simpa [one_div] using hinv

/-- The exact positive remainder after the prime-harmonic subtraction is summable. -/
theorem summable_xiApertureOnePrimeFusedResponseRenormalizedGain :
    Summable xiApertureOnePrimeFusedResponseRenormalizedGain := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  have hnodes : Summable (fun p : Nat.Primes =>
      xiTransversePrimeApertureDiskNode 1 p ^ 2) := by
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] using hprime
  exact Summable.of_nonneg_of_le
    (fun p => (xiApertureOnePrimeFusedResponseRenormalizedGain_pos p).le)
    xiApertureOnePrimeFusedResponseRenormalizedGain_le_invSq
    (Summable.mul_left 144 hnodes)

/-- The non-identity gain is square-summable even though it is not summable.  At the sequence
level this is the Hilbert--Schmidt/not-trace-class dichotomy. -/
theorem summable_xiApertureOnePrimeFusedResponseGainSq_sub_one_sq :
    Summable (fun p : Nat.Primes =>
      (xiApertureOnePrimeFusedResponseGainSq p - 1) ^ 2) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  have hnodes : Summable (fun p : Nat.Primes =>
      xiTransversePrimeApertureDiskNode 1 p ^ 2) := by
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] using hprime
  exact Summable.of_nonneg_of_le
    (fun p => sq_nonneg (xiApertureOnePrimeFusedResponseGainSq p - 1))
    (fun p => by
      have hnode0 : 0 ≤ xiTransversePrimeApertureDiskNode 1 p :=
        (xiTransversePrimeApertureDiskNode_pos 1 p).le
      have hgain0 : 0 ≤ xiApertureOnePrimeFusedResponseGainSq p - 1 :=
        (mul_nonneg (by norm_num) hnode0) |>.trans
          (six_mul_diskNode_le_xiApertureOnePrimeFusedResponseGainSq_sub_one p)
      have hsq := (sq_le_sq₀ hgain0 (show
        0 ≤ 52 * xiTransversePrimeApertureDiskNode 1 p by
          exact mul_nonneg (by norm_num) hnode0)).2
          (xiApertureOnePrimeFusedResponseGainSq_sub_one_le p)
      calc
        (xiApertureOnePrimeFusedResponseGainSq p - 1) ^ 2 ≤
            (52 * xiTransversePrimeApertureDiskNode 1 p) ^ 2 := hsq
        _ = 2704 * xiTransversePrimeApertureDiskNode 1 p ^ 2 := by ring)
    (Summable.mul_left 2704 hnodes)

end

end RHTower
