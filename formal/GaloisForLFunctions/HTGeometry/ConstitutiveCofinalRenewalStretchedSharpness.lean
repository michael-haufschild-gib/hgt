import GaloisForLFunctions.HTGeometry.ConstitutiveCofinalRenewalSharpness

/-!
# Stretched-exponential sharp renewals

This module constructs a normalized stretched-exponential baseline with a positive reserve atom
and the polynomial renewal which carries constant degree-`d` current.  Its logarithmic density
ratio is absolutely summable exactly in the sharp range `d > gamma + 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Real InformationTheory Set
open scoped ENNReal

noncomputable section

private def stretchedSharpEpsilon (d : ℝ) : ℝ := (d - 1) / 2

private def stretchedSharpMajor
    (a B beta gamma d : ℝ) (n : ℕ) : ℝ :=
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let epsilon := stretchedSharpEpsilon d
  a * (|Real.log a| + |Real.log B|) * N ^ (-d) +
    (a * d / epsilon) * N ^ (epsilon - d) +
    a * beta * N ^ (gamma - d)

set_option maxHeartbeats 250000 in
private theorem summable_stretchedSharpMajor
    {a B beta gamma d : ℝ} (hgamma : 0 < gamma) (hd : gamma + 1 < d) :
    Summable (stretchedSharpMajor a B beta gamma d) := by
  let epsilon := stretchedSharpEpsilon d
  have hsum0base : Summable (fun n : ℕ => (n : ℝ) ^ (-d)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsum0 : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ (-d))) :=
    (summable_nat_add_iff 1).mpr hsum0base
  have hsumLogBase : Summable (fun n : ℕ => (n : ℝ) ^ (epsilon - d)) :=
    Real.summable_nat_rpow.mpr (by dsimp [epsilon, stretchedSharpEpsilon]; linarith)
  have hsumLog : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ (epsilon - d))) :=
    (summable_nat_add_iff 1).mpr hsumLogBase
  have hsumGammaBase : Summable (fun n : ℕ => (n : ℝ) ^ (gamma - d)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hsumGamma : Summable (fun n : ℕ =>
      (((n + 1 : ℕ) : ℝ) ^ (gamma - d))) :=
    (summable_nat_add_iff 1).mpr hsumGammaBase
  change Summable (fun n : ℕ =>
    a * (|Real.log a| + |Real.log B|) * (((n + 1 : ℕ) : ℝ) ^ (-d)) +
      (a * d / epsilon) * (((n + 1 : ℕ) : ℝ) ^ (epsilon - d)) +
      a * beta * (((n + 1 : ℕ) : ℝ) ^ (gamma - d)))
  exact ((hsum0.mul_left (a * (|Real.log a| + |Real.log B|))).add
      (hsumLog.mul_left (a * d / epsilon))).add
        (hsumGamma.mul_left (a * beta))

private theorem polynomial_stretched_logRatio_le_major
    (a B beta gamma d : ℝ) (ha : 0 < a) (hB : 0 < B) (hbeta : 0 < beta)
    (hgamma : 0 < gamma) (hd : gamma + 1 < d) (n : ℕ) :
    (a * (((n + 1 : ℕ) : ℝ) ^ (-d))) *
        |Real.log ((a * (((n + 1 : ℕ) : ℝ) ^ (-d)) /
          (B * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))))| ≤
      stretchedSharpMajor a B beta gamma d n := by
  let N : ℝ := ((n + 1 : ℕ) : ℝ)
  let C : ℝ := |Real.log a| + |Real.log B|
  let epsilon : ℝ := stretchedSharpEpsilon d
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon, stretchedSharpEpsilon]
    linarith
  have hd0 : 0 < d := by linarith
  have hN : 1 ≤ N := by
    dsimp [N]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlogNle : Real.log N ≤ N ^ epsilon / epsilon :=
    Real.log_le_rpow_div hN0.le hepsilon
  have hrpow : 0 < N ^ (-d) := Real.rpow_pos_of_pos hN0 _
  have hden : 0 < B * Real.exp (-beta * N ^ gamma) :=
    mul_pos hB (Real.exp_pos _)
  have hlogeq :
      Real.log ((a * N ^ (-d)) / (B * Real.exp (-beta * N ^ gamma))) =
        Real.log a - d * Real.log N - Real.log B + beta * N ^ gamma := by
    rw [Real.log_div (mul_ne_zero ha.ne' hrpow.ne') hden.ne',
      Real.log_mul ha.ne' hrpow.ne', Real.log_rpow hN0 (-d),
      Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have habs :
      |Real.log ((a * N ^ (-d)) / (B * Real.exp (-beta * N ^ gamma)))| ≤
        C + (d / epsilon) * N ^ epsilon + beta * N ^ gamma := by
    rw [hlogeq]
    calc
      |Real.log a - d * Real.log N - Real.log B + beta * N ^ gamma| ≤
          |Real.log a| + |d * Real.log N| + |Real.log B| +
            |beta * N ^ gamma| := by
        linarith [
          abs_add_le (Real.log a - d * Real.log N - Real.log B) (beta * N ^ gamma),
          abs_sub (Real.log a - d * Real.log N) (Real.log B),
          abs_sub (Real.log a) (d * Real.log N)]
      _ = C + d * Real.log N + beta * N ^ gamma := by
        rw [abs_mul, abs_mul, abs_of_nonneg hd0.le,
          abs_of_nonneg hlogN0, abs_of_nonneg hbeta.le,
          abs_of_nonneg (Real.rpow_nonneg hN0.le gamma)]
        dsimp [C]
        ring
      _ ≤ C + (d / epsilon) * N ^ epsilon + beta * N ^ gamma := by
        have hmul := mul_le_mul_of_nonneg_left hlogNle hd0.le
        have hlogTerm : d * Real.log N ≤ (d / epsilon) * N ^ epsilon := by
          calc
            d * Real.log N ≤ d * (N ^ epsilon / epsilon) := hmul
            _ = (d / epsilon) * N ^ epsilon := by ring
        linarith
  have hshiftLog : N ^ (epsilon - d) = N ^ (-d) * N ^ epsilon := by
    calc
      N ^ (epsilon - d) = N ^ ((-d) + epsilon) := by ring_nf
      _ = N ^ (-d) * N ^ epsilon := Real.rpow_add hN0 (-d) epsilon
  have hshiftGamma : N ^ (gamma - d) = N ^ (-d) * N ^ gamma := by
    calc
      N ^ (gamma - d) = N ^ ((-d) + gamma) := by ring_nf
      _ = N ^ (-d) * N ^ gamma := Real.rpow_add hN0 (-d) gamma
  have hfactor : a * N ^ (-d) *
      (C + (d / epsilon) * N ^ epsilon + beta * N ^ gamma) =
      a * C * N ^ (-d) + (a * d / epsilon) * N ^ (epsilon - d) +
        a * beta * N ^ (gamma - d) := by
    rw [hshiftLog, hshiftGamma]
    ring
  change (a * N ^ (-d)) *
      |Real.log ((a * N ^ (-d)) / (B * Real.exp (-beta * N ^ gamma)))| ≤ _
  rw [stretchedSharpMajor]
  dsimp only [N, C, epsilon]
  exact (mul_le_mul_of_nonneg_left habs
    (mul_nonneg ha.le (Real.rpow_nonneg hN0.le _))).trans_eq hfactor

/-- Absolute logarithmic density-ratio summability in the sharp stretched-exponential range. -/
theorem summable_polynomial_stretchedExponential_logRatio
    (a B beta gamma d : ℝ) (ha : 0 < a) (hB : 0 < B) (hbeta : 0 < beta)
    (hgamma : 0 < gamma) (hd : gamma + 1 < d) :
    Summable (fun n : ℕ =>
      (a * (((n + 1 : ℕ) : ℝ) ^ (-d))) *
        |Real.log ((a * (((n + 1 : ℕ) : ℝ) ^ (-d)) /
          (B * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))))|) := by
  apply Summable.of_nonneg_of_le
    (fun n => mul_nonneg (mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _)) (abs_nonneg _))
    (polynomial_stretched_logRatio_le_major a B beta gamma d ha hB hbeta hgamma hd)
  exact summable_stretchedSharpMajor hgamma hd

/-- Positive-depth stretched-exponential atom mass. -/
def stretchedExponentialBaselineTail (B beta gamma : ℝ) (n : ℕ) : ℝ :=
  B * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma))

/-- Normalized stretched-exponential law, with unused mass reserved at depth zero. -/
def stretchedExponentialBaselineMass (B beta gamma : ℝ) : ℕ → ℝ
  | 0 => 1 - ∑' n : ℕ, stretchedExponentialBaselineTail B beta gamma n
  | n + 1 => stretchedExponentialBaselineTail B beta gamma n

theorem summable_stretchedExponentialBaselineTail
    {B beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    Summable (stretchedExponentialBaselineTail B beta gamma) := by
  have hbase : Summable (fun n : ℕ =>
      Real.exp (-beta * ((n : ℝ) ^ gamma))) := by
    simpa [neg_mul] using summable_rpow_mul_exp_neg_rpow (A := 0) hbeta hgamma
  have hshift : Summable (fun n : ℕ =>
      Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma))) :=
    (summable_nat_add_iff 1).mpr hbase
  change Summable (fun n : ℕ =>
    B * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))
  exact hshift.mul_left B

theorem stretchedExponentialBaselineTail_nonneg
    {B beta gamma : ℝ} (hB : 0 ≤ B) (n : ℕ) :
    0 ≤ stretchedExponentialBaselineTail B beta gamma n :=
  mul_nonneg hB (Real.exp_pos _).le

theorem stretchedExponentialBaselineMass_nonneg
    {B beta gamma : ℝ} (hB : 0 ≤ B)
    (htotal : ∑' n, stretchedExponentialBaselineTail B beta gamma n < 1) (n : ℕ) :
    0 ≤ stretchedExponentialBaselineMass B beta gamma n := by
  cases n with
  | zero => simp only [stretchedExponentialBaselineMass]; linarith
  | succ n => exact stretchedExponentialBaselineTail_nonneg hB n

theorem summable_stretchedExponentialBaselineMass
    {B beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    Summable (stretchedExponentialBaselineMass B beta gamma) := by
  apply (summable_nat_add_iff 1).mp
  simpa [stretchedExponentialBaselineMass] using
    summable_stretchedExponentialBaselineTail (B := B) hbeta hgamma

theorem tsum_stretchedExponentialBaselineMass
    {B beta gamma : ℝ} (hbeta : 0 < beta) (hgamma : 0 < gamma) :
    ∑' n, stretchedExponentialBaselineMass B beta gamma n = 1 := by
  have hsum := summable_stretchedExponentialBaselineMass (B := B) hbeta hgamma
  have hsplit := hsum.sum_add_tsum_nat_add 1
  have htail : (∑' n, stretchedExponentialBaselineMass B beta gamma (n + 1)) =
      ∑' n, stretchedExponentialBaselineTail B beta gamma n := by
    congr
  rw [htail] at hsplit
  simpa [stretchedExponentialBaselineMass] using hsplit.symm

def stretchedExponentialBaselineENNMass
    (B beta gamma : ℝ) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (stretchedExponentialBaselineMass B beta gamma n)

theorem hasSum_stretchedExponentialBaselineENNMass
    {B beta gamma : ℝ} (hB : 0 ≤ B) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (htotal : ∑' n, stretchedExponentialBaselineTail B beta gamma n < 1) :
    HasSum (stretchedExponentialBaselineENNMass B beta gamma) 1 := by
  rw [ENNReal.summable.hasSum_iff]
  change (∑' n, ENNReal.ofReal (stretchedExponentialBaselineMass B beta gamma n)) = 1
  rw [← ENNReal.ofReal_tsum_of_nonneg
    (stretchedExponentialBaselineMass_nonneg hB htotal)
    (summable_stretchedExponentialBaselineMass (B := B) hbeta hgamma)]
  rw [tsum_stretchedExponentialBaselineMass (B := B) hbeta hgamma]
  simp

/-- Normalized stretched-exponential baseline PMF. -/
def stretchedExponentialBaselinePMF
    (B beta gamma : ℝ) (hB : 0 ≤ B) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (htotal : ∑' n, stretchedExponentialBaselineTail B beta gamma n < 1) : PMF ℕ :=
  pmfOfHasSum (stretchedExponentialBaselineENNMass B beta gamma)
    (hasSum_stretchedExponentialBaselineENNMass hB hbeta hgamma htotal)

@[simp] theorem stretchedExponentialBaselinePMF_zero
    (B beta gamma : ℝ) (hB : 0 ≤ B) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (htotal : ∑' n, stretchedExponentialBaselineTail B beta gamma n < 1) :
    stretchedExponentialBaselinePMF B beta gamma hB hbeta hgamma htotal 0 =
      ENNReal.ofReal (1 - ∑' n, stretchedExponentialBaselineTail B beta gamma n) := rfl

@[simp] theorem stretchedExponentialBaselinePMF_succ
    (B beta gamma : ℝ) (hB : 0 ≤ B) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (htotal : ∑' n, stretchedExponentialBaselineTail B beta gamma n < 1) (n : ℕ) :
    stretchedExponentialBaselinePMF B beta gamma hB hbeta hgamma htotal (n + 1) =
      ENNReal.ofReal (B * Real.exp
        (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma))) := rfl

/-- Polynomial-tail renewal has finite KL action over the normalized stretched-exponential
baseline throughout the sharp range `d > gamma + 1`. -/
theorem polynomialRenewalPMF_klDiv_stretchedExponentialBaselinePMF_ne_top
    {a B beta gamma d : ℝ}
    (ha : 0 < a) (hB : 0 < B) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hd : gamma + 1 < d)
    (hPtotal : ∑' n, stretchedExponentialBaselineTail B beta gamma n < 1)
    (hQtotal : ∑' n, polynomialRenewalTail a d n < 1) :
    klDiv (polynomialRenewalPMF a d ha.le (by linarith) hQtotal).toMeasure
      (stretchedExponentialBaselinePMF B beta gamma hB.le hbeta hgamma hPtotal).toMeasure ≠
        ⊤ := by
  apply discretePMF_klDiv_ne_top
  · intro n
    cases n with
    | zero =>
        exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hPtotal)).ne'
    | succ n =>
        exact (ENNReal.ofReal_pos.mpr
          (mul_pos hB (Real.exp_pos _))).ne'
  · apply (summable_nat_add_iff 1).mp
    have hrenewed (n : ℕ) :
        (ENNReal.ofReal (a * (((n + 1 : ℕ) : ℝ) ^ (-d)))).toReal =
          a * (((n + 1 : ℕ) : ℝ) ^ (-d)) :=
      ENNReal.toReal_ofReal
        (mul_nonneg ha.le (Real.rpow_nonneg (by positivity) _))
    have hbaseline (n : ℕ) :
        (ENNReal.ofReal (B * Real.exp
          (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))).toReal =
          B * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)) :=
      ENNReal.toReal_ofReal (mul_nonneg hB.le (Real.exp_pos _).le)
    simpa only [polynomialRenewalENNMass, polynomialRenewalMass,
      polynomialRenewalTail, stretchedExponentialBaselineENNMass,
      stretchedExponentialBaselineMass, stretchedExponentialBaselineTail,
      hrenewed, hbaseline] using
        summable_polynomial_stretchedExponential_logRatio
          a B beta gamma d ha hB hbeta hgamma hd

/-- Complete sharp model on the stretched-exponential critical surface. -/
theorem stretchedExponentialPolynomialRenewal_classSharp
    {B beta gamma K c d : ℝ}
    (hB : 0 < B) (hbeta : 0 < beta) (hgamma : 0 < gamma)
    (hK : 0 < K) (hc : 0 < c) (hd : gamma + 1 < d)
    (hPtotal : ∑' n, stretchedExponentialBaselineTail B beta gamma n < 1)
    (hQtotal : ∑' n, polynomialRenewalTail (c / K) d n < 1) :
    let P := stretchedExponentialBaselinePMF B beta gamma hB.le hbeta hgamma hPtotal
    let Q := polynomialRenewalPMF (c / K) d (div_nonneg hc.le hK.le)
      (by linarith) hQtotal
    (∀ n, P (n + 1) = ENNReal.ofReal
      (B * Real.exp (-beta * (((n + 1 : ℕ) : ℝ) ^ gamma)))) ∧
    (∀ n, Q (n + 1) = ENNReal.ofReal
      ((c / K) * (((n + 1 : ℕ) : ℝ) ^ (-d)))) ∧
    klDiv Q.toMeasure P.toMeasure ≠ ⊤ ∧
    ∀ n, (Q (n + 1)).toReal *
      (K * (((n + 1 : ℕ) : ℝ) ^ d)) = c := by
  dsimp only
  have ha : 0 < c / K := div_pos hc hK
  refine ⟨fun n => rfl, fun n => rfl, ?_, ?_⟩
  · exact polynomialRenewalPMF_klDiv_stretchedExponentialBaselinePMF_ne_top
      ha hB hbeta hgamma hd hPtotal hQtotal
  · intro n
    exact polynomialRenewalPMF_constantCurrent hK hc (by linarith) hQtotal n

end

end GaloisForLFunctions.HTGeometry
