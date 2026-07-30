import GaloisForLFunctions.HilbertMetric.PrescribedEvaluationReconstruction
import GaloisForLFunctions.RHTower.XiMobiusSchurValuationIntertwiner
import GaloisForLFunctions.RHTower.ArcsineZetaTransform
import GaloisForLFunctions.RHTower.ArithmeticSchurRenormalizationLaw

/-!
# The continuous Möbius--Szegő true-aperture metric

The integral valuation metric does not by itself reach the transverse germ `a → 0+`.  The naive
continuous repair that also moves the prime weight to `p⁻ᵃ` loses all-prime square summability at
`a ≤ 1/2`.  The actual Möbius--Bernoulli source factor supplies a different repair: retain its
critical weight `p⁻¹`, and sample only its spectral argument on the ray `z = a e`.

The forward depth differences are then

`q/(1+q) * (1-rₐ) * rₐ^e`,  where `q=p⁻¹` and `rₐ=p⁻ᵃ`.

Their completed Gram is a fixed inverse-prime-square damping of the Szegő kernel.  Consequently it
is summable over all primes for every real `a>0`, while normalization retains the exact disk
pseudohyperbolic metric.  This constructs the incoming continuous-aperture Hilbert geometry; it
does not assert the still-missing contractive map to the Xi boundary response.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

open scoped BigOperators InnerProduct
open Filter Matrix

/-- The real disk node `p⁻ᵃ` for a real observation aperture. -/
def xiMobiusContinuousApertureDiskNode (a : ℝ) (p : Nat.Primes) : ℝ :=
  Real.exp (-a * Real.log (p : ℝ))

theorem xiMobiusContinuousApertureDiskNode_pos (a : ℝ) (p : Nat.Primes) :
    0 < xiMobiusContinuousApertureDiskNode a p := by
  exact Real.exp_pos _

theorem xiMobiusContinuousApertureDiskNode_lt_one
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode a p < 1 := by
  rw [xiMobiusContinuousApertureDiskNode, ← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  nlinarith

theorem xiMobiusContinuousApertureDiskNode_injective (p : Nat.Primes) :
    Function.Injective (fun a : ℝ => xiMobiusContinuousApertureDiskNode a p) := by
  intro a b hab
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  have hexp := Real.exp_injective hab
  nlinarith

theorem xiMobiusContinuousApertureDiskNode_pow
    (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    xiMobiusContinuousApertureDiskNode a p ^ e =
      Real.exp (-(a * (e : ℝ)) * Real.log (p : ℝ)) := by
  rw [xiMobiusContinuousApertureDiskNode, ← Real.exp_nat_mul]
  congr 1
  ring

/-- The critical Möbius source factor sampled at real aperture `a` and valuation depth `e`. -/
def xiMobiusPrimeSchurContinuousDepthSample
    (a : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  (1 - q * r ^ e) / (1 + q)

/-- The continuous depth sample is the literal local Möbius--Bernoulli Schur factor on `z=ae`. -/
theorem bernoulliSignedSchurFactor_one_realApertureDepth_eq_sample
    (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    bernoulliSignedSchurFactor (primeSchurWeight 1 p) (Real.log (p : ℝ))
        ((a * (e : ℝ) : ℝ) : ℂ) =
      (xiMobiusPrimeSchurContinuousDepthSample a p e : ℂ) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  have hweight : primeSchurWeight 1 p = q :=
    primeSchurWeight_one_eq_xiTransversePrimeApertureDiskNode p
  have hexp :
      Complex.exp (-(Real.log (p : ℝ) : ℂ) * ((a * (e : ℝ) : ℝ) : ℂ)) =
        (r ^ e : ℝ) := by
    rw [show -(Real.log (p : ℝ) : ℂ) * ((a * (e : ℝ) : ℝ) : ℂ) =
        ((-(a * (e : ℝ)) * Real.log (p : ℝ) : ℝ) : ℂ) by
      push_cast
      ring]
    rw [← Complex.ofReal_exp]
    exact_mod_cast (xiMobiusContinuousApertureDiskNode_pow a p e).symm
  rw [bernoulliSignedSchurFactor, hweight, hexp]
  simp only [xiMobiusPrimeSchurContinuousDepthSample, q, r]
  push_cast
  rfl

/-- The source-selected forward difference along valuation depth at real aperture `a`. -/
def xiMobiusPrimeSchurContinuousForwardDifference
    (a : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  xiMobiusPrimeSchurContinuousDepthSample a p (e + 1) -
    xiMobiusPrimeSchurContinuousDepthSample a p e

/-- Exact coherent-state form of the continuous-aperture depth difference. -/
theorem xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric
    (a : ℝ) (p : Nat.Primes) (e : ℕ) :
    xiMobiusPrimeSchurContinuousForwardDifference a p e =
      (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) *
        (1 - xiMobiusContinuousApertureDiskNode a p) *
          xiMobiusContinuousApertureDiskNode a p ^ e := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hden : 1 + q ≠ 0 := by linarith
  simp only [xiMobiusPrimeSchurContinuousForwardDifference,
    xiMobiusPrimeSchurContinuousDepthSample, pow_succ]
  field_simp [hden]
  ring

/-- The completed local Gram of two continuous Möbius aperture rays. -/
def xiMobiusPrimeContinuousApertureSzegoMetric
    (a b : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  (q / (1 + q)) ^ 2 * (1 - r) * (1 - s) / (1 - r * s)

/-- The closed kernel is exactly the completed Gram of the actual Schur-ray depth differences. -/
theorem tsum_xiMobiusPrimeSchurContinuousForwardDifference_mul_eq_metric
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    (∑' e : ℕ, xiMobiusPrimeSchurContinuousForwardDifference a p e *
      xiMobiusPrimeSchurContinuousForwardDifference b p e) =
      xiMobiusPrimeContinuousApertureSzegoMetric a b p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  have hr0 : 0 ≤ r := (xiMobiusContinuousApertureDiskNode_pos a p).le
  have hs0 : 0 ≤ s := (xiMobiusContinuousApertureDiskNode_pos b p).le
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hrs0 : 0 ≤ r * s := mul_nonneg hr0 hs0
  have hrs1 : r * s < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hr0 hr1 hs1.le
  calc
    (∑' e : ℕ, xiMobiusPrimeSchurContinuousForwardDifference a p e *
        xiMobiusPrimeSchurContinuousForwardDifference b p e) =
        ∑' e : ℕ,
          ((q / (1 + q)) ^ 2 * (1 - r) * (1 - s)) * (r * s) ^ e := by
      apply tsum_congr
      intro e
      rw [xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric,
        xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
      change (q / (1 + q) * (1 - r) * r ^ e) *
        (q / (1 + q) * (1 - s) * s ^ e) = _
      rw [mul_pow]
      ring
    _ = ((q / (1 + q)) ^ 2 * (1 - r) * (1 - s)) *
        ∑' e : ℕ, (r * s) ^ e := by
      rw [tsum_mul_left]
    _ = ((q / (1 + q)) ^ 2 * (1 - r) * (1 - s)) *
        (1 - r * s)⁻¹ := by
      rw [tsum_geometric_of_lt_one hrs0 hrs1]
    _ = xiMobiusPrimeContinuousApertureSzegoMetric a b p := by
      simp only [xiMobiusPrimeContinuousApertureSzegoMetric, q, r, s,
        div_eq_mul_inv]

/-- Exact diagonal of the local continuous-aperture Gram. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_self
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric a a p =
      (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
        ((1 - xiMobiusContinuousApertureDiskNode a p) /
          (1 + xiMobiusContinuousApertureDiskNode a p)) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hplus : 1 + r ≠ 0 := by linarith
  have hminus : 1 - r ≠ 0 := by linarith
  simp only [xiMobiusPrimeContinuousApertureSzegoMetric]
  rw [show xiTransversePrimeApertureDiskNode 1 p = q by rfl,
    show xiMobiusContinuousApertureDiskNode a p = r by rfl,
    show 1 - r * r = (1 - r) * (1 + r) by ring]
  field_simp [hplus, hminus]

/-- The closed diagonal formula holds on both nonzero real aperture chambers. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_self_eq_of_ne_zero
    {a : ℝ} (ha : a ≠ 0) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric a a p =
      (xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
        ((1 - xiMobiusContinuousApertureDiskNode a p) /
          (1 + xiMobiusContinuousApertureDiskNode a p)) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  have hqpos : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hrpos : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hrne : r ≠ 1 := by
    intro hr
    apply ha
    apply xiMobiusContinuousApertureDiskNode_injective p
    simpa [r, xiMobiusContinuousApertureDiskNode] using hr
  have hminus : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrne)
  have hplus : 1 + r ≠ 0 := by positivity
  have hqplus : 1 + q ≠ 0 := by positivity
  simp only [xiMobiusPrimeContinuousApertureSzegoMetric]
  change (q / (1 + q)) ^ 2 * (1 - r) * (1 - r) / (1 - r * r) =
    (q / (1 + q)) ^ 2 * ((1 - r) / (1 + r))
  rw [show 1 - r * r = (1 - r) * (1 + r) by ring]
  field_simp [hminus, hplus, hqplus]

/-- **Scalar chamber classification.** The completed local Szegő self-metric is strictly positive
exactly on the positive real aperture chamber. It vanishes at the boundary and is negative on the
opposite chamber. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_self_pos_iff
    (a : ℝ) (p : Nat.Primes) :
    0 < xiMobiusPrimeContinuousApertureSzegoMetric a a p ↔ 0 < a := by
  constructor
  · intro hmetric
    by_contra hapos
    have hale : a ≤ 0 := le_of_not_gt hapos
    by_cases ha0 : a = 0
    · subst a
      simp [xiMobiusPrimeContinuousApertureSzegoMetric,
        xiMobiusContinuousApertureDiskNode] at hmetric
    · have haneg : a < 0 := lt_of_le_of_ne hale ha0
      let q := xiTransversePrimeApertureDiskNode 1 p
      let r := xiMobiusContinuousApertureDiskNode a p
      have hqpos : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
      have hrgt : 1 < r := by
        dsimp [r, xiMobiusContinuousApertureDiskNode]
        rw [← Real.exp_zero]
        apply Real.exp_lt_exp.mpr
        have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
        have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
        nlinarith
      rw [xiMobiusPrimeContinuousApertureSzegoMetric_self_eq_of_ne_zero ha0 p] at hmetric
      have hratio : (1 - r) / (1 + r) < 0 :=
        div_neg_of_neg_of_pos (by linarith) (by linarith)
      have hfactor : 0 < (q / (1 + q)) ^ 2 := by positivity
      change 0 < (q / (1 + q)) ^ 2 * ((1 - r) / (1 + r)) at hmetric
      exact (not_lt_of_ge
        (mul_nonpos_of_nonneg_of_nonpos hfactor.le hratio.le)) hmetric
  · intro ha
    rw [xiMobiusPrimeContinuousApertureSzegoMetric_self ha p]
    have hq := xiTransversePrimeApertureDiskNode_pos 1 p
    have hr0 := xiMobiusContinuousApertureDiskNode_pos a p
    have hr1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
    positivity

theorem xiMobiusPrimeContinuousApertureSzegoMetric_self_nonneg
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    0 ≤ xiMobiusPrimeContinuousApertureSzegoMetric a a p := by
  rw [xiMobiusPrimeContinuousApertureSzegoMetric_self ha p]
  have hr0 := xiMobiusContinuousApertureDiskNode_pos a p
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  exact mul_nonneg (sq_nonneg _)
    (div_nonneg (by linarith) (by linarith))

/-- Fixed critical Möbius damping gives a prime-square majorant independent of the aperture. -/
theorem xiMobiusPrimeContinuousApertureSzegoMetric_self_le_invSq
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric a a p ≤
      xiTransversePrimeApertureDiskNode 1 p ^ 2 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hr0 : 0 ≤ r := (xiMobiusContinuousApertureDiskNode_pos a p).le
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hratio0 : 0 ≤ (1 - r) / (1 + r) :=
    div_nonneg (sub_nonneg.mpr hr1.le) (by linarith)
  have hratio1 : (1 - r) / (1 + r) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hdamp0 : 0 ≤ q / (1 + q) := div_nonneg hq0 (by linarith)
  have hdamp : q / (1 + q) ≤ q := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + q)]
    nlinarith [sq_nonneg q]
  rw [xiMobiusPrimeContinuousApertureSzegoMetric_self ha p]
  change (q / (1 + q)) ^ 2 * ((1 - r) / (1 + r)) ≤ q ^ 2
  calc
    (q / (1 + q)) ^ 2 * ((1 - r) / (1 + r)) ≤
        (q / (1 + q)) ^ 2 * 1 :=
      mul_le_mul_of_nonneg_left hratio1 (sq_nonneg _)
    _ ≤ q ^ 2 := by nlinarith

/-- The continuous aperture frame is all-prime Hilbertian for every `a>0`. -/
theorem summable_xiMobiusPrimeContinuousApertureSzegoMetric_self
    {a : ℝ} (ha : 0 < a) :
    Summable (fun p : Nat.Primes =>
      xiMobiusPrimeContinuousApertureSzegoMetric a a p) := by
  have hnat : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    hnat.comp_injective Subtype.val_injective
  have hnodes : Summable
      (fun p : Nat.Primes => xiTransversePrimeApertureDiskNode 1 p ^ 2) := by
    simpa [xiTransversePrimeApertureDiskNode_one_eq_inv, inv_pow] using hprime
  exact Summable.of_nonneg_of_le
    (fun p => xiMobiusPrimeContinuousApertureSzegoMetric_self_nonneg ha p)
    (fun p => xiMobiusPrimeContinuousApertureSzegoMetric_self_le_invSq ha p)
    hnodes

/-- Squared correlation after normalizing the continuous Möbius aperture features. -/
def xiMobiusPrimeContinuousApertureNormalizedCorrelationSq
    (a b : ℝ) (p : Nat.Primes) : ℝ :=
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  (1 - r ^ 2) * (1 - s ^ 2) / (1 - r * s) ^ 2

/-- The displayed correlation is literally the normalized completed Gram. -/
theorem xiMobiusPrimeContinuousApertureNormalizedCorrelationSq_eq_metricRatio
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureNormalizedCorrelationSq a b p =
      xiMobiusPrimeContinuousApertureSzegoMetric a b p ^ 2 /
        (xiMobiusPrimeContinuousApertureSzegoMetric a a p *
          xiMobiusPrimeContinuousApertureSzegoMetric b b p) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos b p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hqplus : 1 + q ≠ 0 := by linarith
  have hrminus : 1 - r ≠ 0 := by linarith
  have hsminus : 1 - s ≠ 0 := by linarith
  have hrplus : 1 + r ≠ 0 := by linarith
  have hsplus : 1 + s ≠ 0 := by linarith
  have hrsminus : 1 - r * s ≠ 0 := by
    have hrs : r * s < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
    linarith
  rw [xiMobiusPrimeContinuousApertureSzegoMetric_self ha p,
    xiMobiusPrimeContinuousApertureSzegoMetric_self hb p]
  change (1 - r ^ 2) * (1 - s ^ 2) / (1 - r * s) ^ 2 =
    ((q / (1 + q)) ^ 2 * (1 - r) * (1 - s) / (1 - r * s)) ^ 2 /
      (((q / (1 + q)) ^ 2 * ((1 - r) / (1 + r))) *
        ((q / (1 + q)) ^ 2 * ((1 - s) / (1 + s))))
  field_simp [hq0.ne', hqplus, hrminus, hsminus, hrplus, hsplus, hrsminus]
  ring

/-- The normalized Hilbert defect is exactly the real-disk pseudohyperbolic distance squared. -/
theorem one_sub_xiMobiusPrimeContinuousApertureNormalizedCorrelationSq
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    1 - xiMobiusPrimeContinuousApertureNormalizedCorrelationSq a b p =
      ((xiMobiusContinuousApertureDiskNode a p -
          xiMobiusContinuousApertureDiskNode b p) /
        (1 - xiMobiusContinuousApertureDiskNode a p *
          xiMobiusContinuousApertureDiskNode b p)) ^ 2 := by
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  have hr0 : 0 ≤ r := (xiMobiusContinuousApertureDiskNode_pos a p).le
  have hs0 : 0 ≤ s := (xiMobiusContinuousApertureDiskNode_pos b p).le
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hden : 1 - r * s ≠ 0 := by
    have : r * s < 1 := mul_lt_one_of_nonneg_of_lt_one_left hr0 hr1 hs1.le
    linarith
  change 1 - (1 - r ^ 2) * (1 - s ^ 2) / (1 - r * s) ^ 2 =
    ((r - s) / (1 - r * s)) ^ 2
  field_simp [hden]
  ring

/-- Distinct positive real apertures have positive Hilbert separation at every fixed prime. -/
theorem one_sub_xiMobiusPrimeContinuousApertureNormalizedCorrelationSq_pos
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) (p : Nat.Primes) :
    0 < 1 - xiMobiusPrimeContinuousApertureNormalizedCorrelationSq a b p := by
  rw [one_sub_xiMobiusPrimeContinuousApertureNormalizedCorrelationSq ha hb p]
  have hnode : xiMobiusContinuousApertureDiskNode a p ≠
      xiMobiusContinuousApertureDiskNode b p :=
    fun h => hab ((xiMobiusContinuousApertureDiskNode_injective p) h)
  have hr0 := (xiMobiusContinuousApertureDiskNode_pos a p).le
  have hs0 := (xiMobiusContinuousApertureDiskNode_pos b p).le
  have hr1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hden : 0 < 1 - xiMobiusContinuousApertureDiskNode a p *
      xiMobiusContinuousApertureDiskNode b p := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0 hr1 hs1.le
    linarith
  exact sq_pos_of_ne_zero (div_ne_zero (sub_ne_zero.mpr hnode) hden.ne')

/-- Rows are valuation depths and columns are positive real aperture rays. -/
def xiMobiusPrimeContinuousApertureSamplingMatrix
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) : Matrix (Fin N) (Fin N) ℝ :=
  fun e j => xiMobiusPrimeSchurContinuousForwardDifference (aperture j) p e

/-- Real feature family formed from the canonical first `N` continuous valuation-depth
differences. -/
def xiMobiusPrimeContinuousApertureCanonicalFeature
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    Fin N → Fin N → ℝ :=
  fun j e => xiMobiusPrimeSchurContinuousForwardDifference (aperture j) p e

/-- Exact dual isolation and coefficient recovery from the canonical first `N` continuous
valuation depths. -/
def XiMobiusPrimeContinuousApertureCanonicalReconstruction
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) : Prop :=
  PrescribedEvaluationDualReconstruction
    (xiMobiusPrimeContinuousApertureCanonicalFeature aperture p) id

/-- The prescribed evaluation matrix of the continuous canonical features is exactly the existing
finite source sampler. -/
theorem xiMobiusPrimeContinuousApertureCanonicalEvaluationMatrix_eq_samplingMatrix
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    evaluationMatrix
        (xiMobiusPrimeContinuousApertureCanonicalFeature aperture p) id =
      xiMobiusPrimeContinuousApertureSamplingMatrix aperture p := by
  rfl

/-- The actual source-difference matrix is a weighted real-aperture Vandermonde. -/
theorem xiMobiusPrimeContinuousApertureSamplingMatrix_factorization
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSamplingMatrix aperture p =
      (Matrix.vandermonde
        (fun j => xiMobiusContinuousApertureDiskNode (aperture j) p))ᵀ *
      Matrix.diagonal
        (fun j => (xiTransversePrimeApertureDiskNode 1 p /
            (1 + xiTransversePrimeApertureDiskNode 1 p)) *
          (1 - xiMobiusContinuousApertureDiskNode (aperture j) p)) := by
  classical
  ext e j
  rw [Matrix.mul_diagonal]
  change xiMobiusPrimeSchurContinuousForwardDifference (aperture j) p e = _
  rw [xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric]
  simp [Matrix.vandermonde]
  ring

/-- **Exact finite nondegeneracy classification.** A real-aperture packet gives an invertible
finite source sampler exactly when its apertures are distinct and avoid the boundary value zero.
No positivity chamber is needed at finite depth. -/
theorem xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero_iff_injective_ne_zero
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureSamplingMatrix aperture p).det ≠ 0 ↔
      Function.Injective aperture ∧ ∀ j, aperture j ≠ 0 := by
  rw [xiMobiusPrimeContinuousApertureSamplingMatrix_factorization,
    Matrix.det_mul, Matrix.det_transpose]
  constructor
  · intro hdet
    obtain ⟨hvandermonde, hdiagonal⟩ := mul_ne_zero_iff.mp hdet
    have hnodes : Function.Injective
        (fun j => xiMobiusContinuousApertureDiskNode (aperture j) p) :=
      Matrix.det_vandermonde_ne_zero_iff.mp hvandermonde
    rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff] at hdiagonal
    constructor
    · intro i j hij
      apply hnodes
      exact congrArg (fun a => xiMobiusContinuousApertureDiskNode a p) hij
    · intro j hj
      have hentry := hdiagonal j (Finset.mem_univ j)
      simp [hj, xiMobiusContinuousApertureDiskNode] at hentry
  · rintro ⟨hinjective, hne⟩
    apply mul_ne_zero
    · apply Matrix.det_vandermonde_ne_zero_iff.mpr
      exact (xiMobiusContinuousApertureDiskNode_injective p).comp hinjective
    · rw [Matrix.det_diagonal, Finset.prod_ne_zero_iff]
      intro j _
      have hq : xiTransversePrimeApertureDiskNode 1 p /
          (1 + xiTransversePrimeApertureDiskNode 1 p) ≠ 0 := by
        exact div_ne_zero (xiTransversePrimeApertureDiskNode_pos 1 p).ne'
          (ne_of_gt (by
            have hqpos := xiTransversePrimeApertureDiskNode_pos 1 p
            linarith))
      have hr : xiMobiusContinuousApertureDiskNode (aperture j) p ≠ 1 := by
        intro hr
        apply hne j
        apply xiMobiusContinuousApertureDiskNode_injective p
        simpa [xiMobiusContinuousApertureDiskNode] using hr
      exact mul_ne_zero hq (sub_ne_zero.mpr (Ne.symm hr))

/-- **Continuous canonical reconstruction classification.** The fixed first `N` valuation depths
recover every real-aperture coefficient vector exactly iff the apertures are distinct and avoid
zero. No positivity-chamber hypothesis remains at finite depth. -/
theorem
    xiMobiusPrimeContinuousApertureCanonicalReconstruction_iff_injective_ne_zero
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    XiMobiusPrimeContinuousApertureCanonicalReconstruction aperture p ↔
      Function.Injective aperture ∧ ∀ j, aperture j ≠ 0 := by
  rw [XiMobiusPrimeContinuousApertureCanonicalReconstruction,
    prescribedEvaluationDualReconstruction_iff_det_ne_zero,
    xiMobiusPrimeContinuousApertureCanonicalEvaluationMatrix_eq_samplingMatrix,
    xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero_iff_injective_ne_zero]

/-- Every finite injective packet of positive real apertures is separated by one prime tower. -/
theorem xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero
    {N : ℕ} {aperture : Fin N → ℝ} (haperture : Function.Injective aperture)
    (hpos : ∀ j, 0 < aperture j) (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureSamplingMatrix aperture p).det ≠ 0 := by
  exact
    (xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero_iff_injective_ne_zero
      aperture p).2 ⟨haperture, fun j => (hpos j).ne'⟩

/-- Finite congruence invariance needs only exact source nondegeneracy, not positivity of the real
apertures. -/
theorem xiMobiusPrimeContinuousAperture_congruence_posSemidef_iff_of_injective_ne_zero
    {N : ℕ} {aperture : Fin N → ℝ} (haperture : Function.Injective aperture)
    (hne : ∀ j, aperture j ≠ 0) (p : Nat.Primes)
    (X : Matrix (Fin N) (Fin N) ℝ) :
    ((xiMobiusPrimeContinuousApertureSamplingMatrix aperture p)ᴴ * X *
        xiMobiusPrimeContinuousApertureSamplingMatrix aperture p).PosSemidef ↔
      X.PosSemidef := by
  have hunit : IsUnit (xiMobiusPrimeContinuousApertureSamplingMatrix aperture p) := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    exact
      (xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero_iff_injective_ne_zero
        aperture p).2 ⟨haperture, hne⟩
  simpa only [star_eq_conjTranspose] using
    hunit.posSemidef_star_left_conjugate_iff (x := X)

/-- **Finite-aperture congruence no-go and positive survivor.**  Since the actual source sampling
matrix is invertible, dressing an arbitrary response Gram by the finite true-aperture coordinates
preserves positive semidefiniteness in both directions.  Thus no finite change to these source
coordinates can create the missing Xi positivity; any effective source-to-Xi comparison must add
genuinely infinite, aperture-coherent, non-invertible content. -/
theorem xiMobiusPrimeContinuousAperture_congruence_posSemidef_iff
    {N : ℕ} {aperture : Fin N → ℝ} (haperture : Function.Injective aperture)
    (hpos : ∀ j, 0 < aperture j) (p : Nat.Primes)
    (X : Matrix (Fin N) (Fin N) ℝ) :
    ((xiMobiusPrimeContinuousApertureSamplingMatrix aperture p)ᴴ * X *
        xiMobiusPrimeContinuousApertureSamplingMatrix aperture p).PosSemidef ↔
      X.PosSemidef := by
  exact xiMobiusPrimeContinuousAperture_congruence_posSemidef_iff_of_injective_ne_zero
    haperture (fun j => (hpos j).ne') p X

/-! ## Exact finite/completed positivity classification -/

/-- Hardy-space realization of one positive real aperture at one prime. -/
def xiMobiusPrimeContinuousApertureHardyFeature
    (a : ℝ) (p : Nat.Primes) (ha : 0 < a) : PrimeHardy :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  (q / (1 + q) * (1 - r)) • hardyKernel r (by
    rw [abs_of_pos (xiMobiusContinuousApertureDiskNode_pos a p)]
    exact xiMobiusContinuousApertureDiskNode_lt_one ha p)

/-- Completed local Szegő Gram matrix of a finite real-aperture packet. -/
def xiMobiusPrimeContinuousApertureSzegoGramMatrix
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiMobiusPrimeContinuousApertureSzegoMetric
    (aperture i) (aperture j) p

/-- On the positive aperture chamber, the completed matrix is literally the Gram matrix of the
Hardy-space aperture features. -/
theorem xiMobiusPrimeContinuousApertureSzegoGramMatrix_eq_gram
    {N : ℕ} (aperture : Fin N → ℝ) (hpos : ∀ j, 0 < aperture j)
    (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoGramMatrix aperture p =
      Matrix.gram ℝ (fun j => xiMobiusPrimeContinuousApertureHardyFeature
        (aperture j) p (hpos j)) := by
  ext i j
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode (aperture i) p
  let s := xiMobiusContinuousApertureDiskNode (aperture j) p
  let hr : |r| < 1 := by
    simpa [r, abs_of_pos (xiMobiusContinuousApertureDiskNode_pos (aperture i) p)] using
      xiMobiusContinuousApertureDiskNode_lt_one (hpos i) p
  let hs : |s| < 1 := by
    simpa [s, abs_of_pos (xiMobiusContinuousApertureDiskNode_pos (aperture j) p)] using
      xiMobiusContinuousApertureDiskNode_lt_one (hpos j) p
  change xiMobiusPrimeContinuousApertureSzegoMetric (aperture i) (aperture j) p =
    inner ℝ ((q / (1 + q) * (1 - r)) • hardyKernel r hr)
      ((q / (1 + q) * (1 - s)) • hardyKernel s hs)
  rw [real_inner_smul_left, real_inner_smul_right, inner_hardyKernel]
  simp only [xiMobiusPrimeContinuousApertureSzegoMetric, q, r, s]
  ring

/-- Distinct positive apertures give linearly independent completed Hardy features. -/
theorem linearIndependent_xiMobiusPrimeContinuousApertureHardyFeature
    {N : ℕ} (aperture : Fin N → ℝ) (hinj : Function.Injective aperture)
    (hpos : ∀ j, 0 < aperture j) (p : Nat.Primes) :
    LinearIndependent ℝ (fun j => xiMobiusPrimeContinuousApertureHardyFeature
      (aperture j) p (hpos j)) := by
  have hdet :=
    (xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero_iff_injective_ne_zero
      aperture p).2 ⟨hinj, fun j => (hpos j).ne'⟩
  have hmulVec : Function.Injective
      (xiMobiusPrimeContinuousApertureSamplingMatrix aperture p).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact hdet
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hc0 : c = 0 := hmulVec (by
    funext e
    have hcfn := congrArg (fun x : PrimeHardy => (x : ℕ → ℝ)) hc
    have hsum :
        (⇑(∑ x, c x • xiMobiusPrimeContinuousApertureHardyFeature
            (aperture x) p (hpos x)) : ℕ → ℝ) =
          ∑ x, (⇑(c x • xiMobiusPrimeContinuousApertureHardyFeature
            (aperture x) p (hpos x)) : ℕ → ℝ) := by
      simpa using (lp.coeFn_sum
        (fun x => c x • xiMobiusPrimeContinuousApertureHardyFeature
          (aperture x) p (hpos x)) Finset.univ)
    change
      (⇑(∑ x, c x • xiMobiusPrimeContinuousApertureHardyFeature
          (aperture x) p (hpos x)) : ℕ → ℝ) =
        (⇑(0 : PrimeHardy) : ℕ → ℝ) at hcfn
    rw [hsum] at hcfn
    have he := congrFun hcfn e
    simp only [Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.coeFn_zero, Pi.zero_apply] at he
    simpa [xiMobiusPrimeContinuousApertureHardyFeature,
      xiMobiusPrimeContinuousApertureSamplingMatrix,
      xiMobiusPrimeSchurContinuousForwardDifference_eq_geometric,
      Matrix.mulVec, dotProduct, mul_comm, mul_left_comm, mul_assoc] using he)
  exact fun i => congrFun hc0 i

/-- **Completed chamber classification.** The completed Szegő matrix is positive definite exactly
for a distinct packet lying entirely in the positive aperture chamber. -/
theorem xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_injective_pos
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureSzegoGramMatrix aperture p).PosDef ↔
      Function.Injective aperture ∧ ∀ j, 0 < aperture j := by
  constructor
  · intro hgram
    constructor
    · intro i j hij
      by_contra hne
      have hrows : xiMobiusPrimeContinuousApertureSzegoGramMatrix aperture p i =
          xiMobiusPrimeContinuousApertureSzegoGramMatrix aperture p j := by
        funext k
        simp [xiMobiusPrimeContinuousApertureSzegoGramMatrix, hij]
      have hdetZero := Matrix.det_zero_of_row_eq hne hrows
      exact hgram.det_pos.ne' hdetZero
    · intro j
      apply (xiMobiusPrimeContinuousApertureSzegoMetric_self_pos_iff
        (aperture j) p).mp
      simpa [xiMobiusPrimeContinuousApertureSzegoGramMatrix] using
        hgram.diag_pos (i := j)
  · rintro ⟨hinj, hpos⟩
    rw [xiMobiusPrimeContinuousApertureSzegoGramMatrix_eq_gram aperture hpos p]
    exact Matrix.posDef_gram_of_linearIndependent
      (linearIndependent_xiMobiusPrimeContinuousApertureHardyFeature
        aperture hinj hpos p)

/-- Finite-depth source Gram matrix of a real-aperture packet. -/
def xiMobiusPrimeContinuousApertureFiniteGramMatrix
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    Matrix (Fin N) (Fin N) ℝ :=
  (xiMobiusPrimeContinuousApertureSamplingMatrix aperture p)ᴴ *
    xiMobiusPrimeContinuousApertureSamplingMatrix aperture p

/-- The finite source Gram is positive definite exactly for distinct nonzero apertures. -/
theorem xiMobiusPrimeContinuousApertureFiniteGramMatrix_posDef_iff_injective_ne_zero
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureFiniteGramMatrix aperture p).PosDef ↔
      Function.Injective aperture ∧ ∀ j, aperture j ≠ 0 := by
  rw [← xiMobiusPrimeContinuousApertureSamplingMatrix_det_ne_zero_iff_injective_ne_zero
    aperture p]
  constructor
  · intro hgram hzero
    apply hgram.det_pos.ne'
    rw [xiMobiusPrimeContinuousApertureFiniteGramMatrix, Matrix.det_mul,
      hzero, mul_zero]
  · intro hdet
    rw [xiMobiusPrimeContinuousApertureFiniteGramMatrix]
    apply Matrix.PosDef.conjTranspose_mul_self
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
      isUnit_iff_ne_zero]
    exact hdet

/-- Canonical continuous-aperture coefficient recovery and strict finite source geometry have
exactly the same phase. -/
theorem
    xiMobiusPrimeContinuousApertureCanonicalReconstruction_iff_finiteGram_posDef
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    XiMobiusPrimeContinuousApertureCanonicalReconstruction aperture p ↔
      (xiMobiusPrimeContinuousApertureFiniteGramMatrix aperture p).PosDef := by
  rw [xiMobiusPrimeContinuousApertureCanonicalReconstruction_iff_injective_ne_zero,
    xiMobiusPrimeContinuousApertureFiniteGramMatrix_posDef_iff_injective_ne_zero]

/-- **Finite/completed gap theorem.** Completion adds exactly the positive-chamber condition to
finite source nondegeneracy; finite sampling alone cannot detect aperture orientation. -/
theorem xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_finiteGram_posDef_and_pos
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureSzegoGramMatrix aperture p).PosDef ↔
      (xiMobiusPrimeContinuousApertureFiniteGramMatrix aperture p).PosDef ∧
        ∀ j, 0 < aperture j := by
  rw [xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_injective_pos,
    xiMobiusPrimeContinuousApertureFiniteGramMatrix_posDef_iff_injective_ne_zero]
  constructor
  · rintro ⟨hinj, hpos⟩
    exact ⟨⟨hinj, fun j => (hpos j).ne'⟩, hpos⟩
  · rintro ⟨⟨hinj, _hne⟩, hpos⟩
    exact ⟨hinj, hpos⟩

/-- **Exact-recovery/completed-metric phase.** Completed continuous Szegő geometry is strict
exactly when the canonical finite valuation packet recovers every coefficient and all apertures
lie in the positive chamber. Thus completion adds orientation, while exact recovery supplies all
finite nondegeneracy. -/
theorem
    xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_canonicalReconstruction_and_pos
    {N : ℕ} (aperture : Fin N → ℝ) (p : Nat.Primes) :
    (xiMobiusPrimeContinuousApertureSzegoGramMatrix aperture p).PosDef ↔
      XiMobiusPrimeContinuousApertureCanonicalReconstruction aperture p ∧
        ∀ j, 0 < aperture j := by
  rw [xiMobiusPrimeContinuousApertureSzegoGramMatrix_posDef_iff_finiteGram_posDef_and_pos,
    ← xiMobiusPrimeContinuousApertureCanonicalReconstruction_iff_finiteGram_posDef]

/-- The closed diagonal formula, extended to the boundary aperture `a=0`. -/
def xiMobiusPrimeContinuousApertureDiagonal (a : ℝ) (p : Nat.Primes) : ℝ :=
  (xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
    ((1 - xiMobiusContinuousApertureDiskNode a p) /
      (1 + xiMobiusContinuousApertureDiskNode a p))

@[simp] theorem xiMobiusContinuousApertureDiskNode_zero (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode 0 p = 1 := by
  simp [xiMobiusContinuousApertureDiskNode]

@[simp] theorem xiMobiusPrimeContinuousApertureDiagonal_zero (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureDiagonal 0 p = 0 := by
  simp [xiMobiusPrimeContinuousApertureDiagonal]

theorem xiMobiusPrimeContinuousApertureSzegoMetric_self_eq_diagonal
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusPrimeContinuousApertureSzegoMetric a a p =
      xiMobiusPrimeContinuousApertureDiagonal a p := by
  exact xiMobiusPrimeContinuousApertureSzegoMetric_self ha p

/-- The logarithmic majorant and twice the infinitesimal local aperture mass. -/
def xiMobiusPrimeContinuousApertureSlopeTerm (p : Nat.Primes) : ℝ :=
  (xiTransversePrimeApertureDiskNode 1 p /
      (1 + xiTransversePrimeApertureDiskNode 1 p)) ^ 2 *
    Real.log (p : ℝ)

theorem xiMobiusPrimeContinuousApertureSlopeTerm_pos (p : Nat.Primes) :
    0 < xiMobiusPrimeContinuousApertureSlopeTerm p := by
  have hq0 : 0 < xiTransversePrimeApertureDiskNode 1 p :=
    xiTransversePrimeApertureDiskNode_pos 1 p
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
  exact mul_pos (sq_pos_of_pos (div_pos hq0 (by linarith))) hlog

/-- The logarithmic prime-square majorant is summable. -/
theorem summable_xiMobiusPrimeContinuousApertureSlopeTerm :
    Summable xiMobiusPrimeContinuousApertureSlopeTerm := by
  have hnat := GaloisForLFunctions.summable_log_div_sq
  have hprime : Summable
      (fun p : Nat.Primes => Real.log (p : ℝ) / (p : ℝ) ^ 2) :=
    hnat.comp_injective Subtype.val_injective
  refine Summable.of_nonneg_of_le
    (fun p => (xiMobiusPrimeContinuousApertureSlopeTerm_pos p).le) ?_ hprime
  intro p
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 ≤ q := (xiTransversePrimeApertureDiskNode_pos 1 p).le
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 ≤ Real.log (p : ℝ) := (Real.log_pos hp).le
  have hdamp0 : 0 ≤ q / (1 + q) := div_nonneg hq0 (by linarith)
  have hdamp : q / (1 + q) ≤ q := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + q)]
    nlinarith [sq_nonneg q]
  have hsq : (q / (1 + q)) ^ 2 ≤ q ^ 2 := by nlinarith
  calc
    xiMobiusPrimeContinuousApertureSlopeTerm p =
        (q / (1 + q)) ^ 2 * Real.log (p : ℝ) := by rfl
    _ ≤ q ^ 2 * Real.log (p : ℝ) := mul_le_mul_of_nonneg_right hsq hlog
    _ = Real.log (p : ℝ) / (p : ℝ) ^ 2 := by
      rw [show q = ((p : ℝ))⁻¹ by
        exact xiTransversePrimeApertureDiskNode_one_eq_inv p]
      simp only [inv_pow, div_eq_mul_inv]
      ring

/-- Each local diagonal has derivative one half of its logarithmic slope term at aperture zero. -/
theorem hasDerivAt_xiMobiusPrimeContinuousApertureDiagonal_zero
    (p : Nat.Primes) :
    HasDerivAt (fun a : ℝ => xiMobiusPrimeContinuousApertureDiagonal a p)
      (xiMobiusPrimeContinuousApertureSlopeTerm p / 2) 0 := by
  let L := Real.log (p : ℝ)
  let d := xiTransversePrimeApertureDiskNode 1 p /
    (1 + xiTransversePrimeApertureDiskNode 1 p)
  have harg : HasDerivAt (fun a : ℝ => -a * L) (-L) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).neg.mul_const L
  have hr : HasDerivAt (fun a : ℝ => Real.exp (-a * L)) (-L) 0 := by
    simpa using! (Real.hasDerivAt_exp (-0 * L)).comp 0 harg
  have hnum : HasDerivAt (fun a : ℝ => 1 - Real.exp (-a * L)) L 0 := by
    simpa using! (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hr
  have hden : HasDerivAt (fun a : ℝ => 1 + Real.exp (-a * L)) (-L) 0 := by
    simpa using! hr.const_add (1 : ℝ)
  have hquot : HasDerivAt
      (fun a : ℝ => (1 - Real.exp (-a * L)) / (1 + Real.exp (-a * L)))
      (L / 2) 0 := by
    have hraw := hnum.div hden (by norm_num)
    simpa using! hraw.congr_deriv (by
      norm_num [div_eq_mul_inv]
      ring)
  have hscaled := hquot.const_mul (d ^ 2)
  have hscaled' := hscaled.congr_deriv
    (g' := xiMobiusPrimeContinuousApertureSlopeTerm p / 2) (by
      simp only [xiMobiusPrimeContinuousApertureSlopeTerm, L, d]
      ring)
  simpa only [xiMobiusPrimeContinuousApertureDiagonal,
    xiMobiusContinuousApertureDiskNode, L, d] using! hscaled'

/-- A single summable logarithmic sequence dominates every positive aperture difference quotient. -/
theorem norm_xiMobiusPrimeContinuousApertureDiagonal_div_le_slopeTerm
    {a : ℝ} (ha : 0 < a) (p : Nat.Primes) :
    ‖xiMobiusPrimeContinuousApertureDiagonal a p / a‖ ≤
      xiMobiusPrimeContinuousApertureSlopeTerm p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let L := Real.log (p : ℝ)
  let d := q / (1 + q)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hone : 1 - r ≤ a * L := by
    have hr_eq : r = Real.exp (-(a * L)) := by
      simp only [r, xiMobiusContinuousApertureDiskNode, L]
      congr 1
      ring
    rw [hr_eq]
    linarith [Real.one_sub_le_exp_neg (a * L)]
  have hratio0 : 0 ≤ (1 - r) / (1 + r) :=
    div_nonneg (by linarith) (by linarith)
  have hratio : (1 - r) / (1 + r) ≤ a * L := by
    rw [div_le_iff₀ (by linarith : 0 < 1 + r)]
    nlinarith [mul_nonneg (mul_nonneg ha.le hL.le) hr0.le]
  have hdiag0 : 0 ≤ xiMobiusPrimeContinuousApertureDiagonal a p := by
    change 0 ≤ d ^ 2 * ((1 - r) / (1 + r))
    exact mul_nonneg (sq_nonneg d) hratio0
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hdiag0 ha.le)]
  change d ^ 2 * ((1 - r) / (1 + r)) / a ≤ d ^ 2 * L
  rw [div_le_iff₀ ha]
  have hmul := mul_le_mul_of_nonneg_left hratio (sq_nonneg d)
  nlinarith

/-- The all-prime incoming aperture energy. -/
def xiMobiusContinuousApertureEnergy (a : ℝ) : ℝ :=
  ∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureDiagonal a p

/-- The finite positive source constant controlling the infinitesimal aperture budget. -/
def xiMobiusContinuousApertureSlopeConstant : ℝ :=
  ∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureSlopeTerm p

theorem xiMobiusContinuousApertureSlopeConstant_pos :
    0 < xiMobiusContinuousApertureSlopeConstant := by
  exact summable_xiMobiusPrimeContinuousApertureSlopeTerm.tsum_pos
    (fun p => (xiMobiusPrimeContinuousApertureSlopeTerm_pos p).le)
    ⟨2, Nat.prime_two⟩
    (xiMobiusPrimeContinuousApertureSlopeTerm_pos ⟨2, Nat.prime_two⟩)

/-- The all-prime energy has the exact right aperture slope `C_M/2` at the origin. -/
theorem tendsto_xiMobiusContinuousApertureEnergy_div_nhdsGT_zero :
    Tendsto (fun a : ℝ => xiMobiusContinuousApertureEnergy a / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureSlopeConstant / 2)) := by
  have hpoint (p : Nat.Primes) : Tendsto
      (fun a : ℝ => xiMobiusPrimeContinuousApertureDiagonal a p / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusPrimeContinuousApertureSlopeTerm p / 2)) := by
    have hslope :=
      (hasDerivAt_xiMobiusPrimeContinuousApertureDiagonal_zero p).tendsto_slope_zero_right
    simpa [div_eq_inv_mul, mul_comm] using hslope
  have hbound : ∀ᶠ a : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ p : Nat.Primes,
      ‖xiMobiusPrimeContinuousApertureDiagonal a p / a‖ ≤
        xiMobiusPrimeContinuousApertureSlopeTerm p := by
    filter_upwards [self_mem_nhdsWithin] with a ha p
    exact norm_xiMobiusPrimeContinuousApertureDiagonal_div_le_slopeTerm ha p
  have hlimit := tendsto_tsum_of_dominated_convergence
    summable_xiMobiusPrimeContinuousApertureSlopeTerm hpoint hbound
  simpa [xiMobiusContinuousApertureEnergy,
    xiMobiusContinuousApertureSlopeConstant, tsum_div_const] using hlimit

/-- Source-prescribed normalization whose infinitesimal aperture budget is exactly four. -/
def xiMobiusContinuousApertureFourUnitEnergy (a : ℝ) : ℝ :=
  (8 / xiMobiusContinuousApertureSlopeConstant) *
    xiMobiusContinuousApertureEnergy a

theorem tendsto_xiMobiusContinuousApertureFourUnitEnergy_div_nhdsGT_zero :
    Tendsto (fun a : ℝ => xiMobiusContinuousApertureFourUnitEnergy a / a)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 4) := by
  have hC := xiMobiusContinuousApertureSlopeConstant_pos
  have hlimit :=
    tendsto_xiMobiusContinuousApertureEnergy_div_nhdsGT_zero.const_mul
      (8 / xiMobiusContinuousApertureSlopeConstant)
  convert hlimit using 1
  · funext a
    simp only [xiMobiusContinuousApertureFourUnitEnergy]
    ring
  · field_simp [hC.ne']; norm_num

/-- Real aperture addition becomes multiplication of the prime disk nodes. -/
theorem xiMobiusContinuousApertureDiskNode_add
    (a b : ℝ) (p : Nat.Primes) :
    xiMobiusContinuousApertureDiskNode (a + b) p =
      xiMobiusContinuousApertureDiskNode a p *
        xiMobiusContinuousApertureDiskNode b p := by
  simp only [xiMobiusContinuousApertureDiskNode]
  rw [← Real.exp_add]
  congr 1
  ring

/-- The first-order exponential gap along a fixed aperture direction. -/
theorem tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
    (c : ℝ) (p : Nat.Primes) :
    Tendsto
      (fun t : ℝ =>
        (1 - xiMobiusContinuousApertureDiskNode (t * c) p) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (c * Real.log (p : ℝ))) := by
  let L := Real.log (p : ℝ)
  have harg : HasDerivAt (fun t : ℝ => -(t * c) * L) (-(c * L)) 0 := by
    simpa using! ((hasDerivAt_id (0 : ℝ)).mul_const c).neg.mul_const L
  have hr : HasDerivAt (fun t : ℝ => Real.exp (-(t * c) * L)) (-(c * L)) 0 := by
    simpa using! (Real.hasDerivAt_exp (-(0 * c) * L)).comp 0 harg
  have hgap : HasDerivAt (fun t : ℝ => 1 - Real.exp (-(t * c) * L)) (c * L) 0 := by
    simpa using! (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub hr
  have hslope := hgap.tendsto_slope_zero_right
  simpa [xiMobiusContinuousApertureDiskNode, L, div_eq_inv_mul, mul_comm] using hslope

/-- Primewise two-aperture tangent law: the actual Möbius--Szegő metric tends to a logarithmically
weighted, derivative-dressed Cauchy kernel. -/
theorem tendsto_xiMobiusPrimeContinuousApertureSzegoMetric_mul_div_nhdsGT_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    Tendsto
      (fun t : ℝ =>
        xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusPrimeContinuousApertureSlopeTerm p *
        (a * b / (a + b)))) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let d := q / (1 + q)
  let L := Real.log (p : ℝ)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp
  have hab : 0 < a + b := add_pos ha hb
  have hA :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero a p
  have hB :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero b p
  have hAB :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero (a + b) p
  have hratio : Tendsto
      (fun t : ℝ =>
        ((1 - xiMobiusContinuousApertureDiskNode (t * a) p) / t) *
          ((1 - xiMobiusContinuousApertureDiskNode (t * b) p) / t) /
            ((1 - xiMobiusContinuousApertureDiskNode (t * (a + b)) p) / t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((a * L) * (b * L) / ((a + b) * L))) := by
    exact (hA.mul hB).div hAB (mul_ne_zero hab.ne' hL.ne')
  have hscaled := hratio.const_mul (d ^ 2)
  have hmetric : Tendsto
      (fun t : ℝ =>
        xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (d ^ 2 * ((a * L) * (b * L) / ((a + b) * L)))) := by
    apply hscaled.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    let r := xiMobiusContinuousApertureDiskNode (t * a) p
    let s := xiMobiusContinuousApertureDiskNode (t * b) p
    have hta : 0 < t * a := mul_pos ht0 ha
    have htb : 0 < t * b := mul_pos ht0 hb
    have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos (t * a) p
    have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos (t * b) p
    have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hta p
    have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one htb p
    have hrs : r * s = xiMobiusContinuousApertureDiskNode (t * (a + b)) p := by
      rw [← xiMobiusContinuousApertureDiskNode_add]
      congr 1
      ring
    have hden : 1 - r * s ≠ 0 := by
      have : r * s < 1 :=
        mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
      linarith
    change d ^ 2 * ((1 - r) / t * ((1 - s) / t) /
        ((1 - xiMobiusContinuousApertureDiskNode (t * (a + b)) p) / t)) =
      xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t
    rw [← hrs]
    simp only [xiMobiusPrimeContinuousApertureSzegoMetric, q, d, r, s]
    field_simp [ht0.ne', hden]
  have hlimEq :
      xiMobiusPrimeContinuousApertureSlopeTerm p * (a * b / (a + b)) =
        d ^ 2 * ((a * L) * (b * L) / ((a + b) * L)) := by
    simp only [xiMobiusPrimeContinuousApertureSlopeTerm]
    change (q / (1 + q)) ^ 2 * Real.log (p : ℝ) * (a * b / (a + b)) =
      d ^ 2 * ((a * L) * (b * L) / ((a + b) * L))
    rw [show q / (1 + q) = d by rfl, show Real.log (p : ℝ) = L by rfl]
    field_simp [hL.ne', hab.ne']
  rw [hlimEq]
  exact hmetric

/-- One logarithmic prime-square sequence dominates the two-aperture tangent quotient. -/
theorem norm_xiMobiusPrimeContinuousApertureSzegoMetric_mul_div_le
    {t a b : ℝ} (ht : 0 < t) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    ‖xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t‖ ≤
      a * xiMobiusPrimeContinuousApertureSlopeTerm p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let d := q / (1 + q)
  let r := xiMobiusContinuousApertureDiskNode (t * a) p
  let s := xiMobiusContinuousApertureDiskNode (t * b) p
  let L := Real.log (p : ℝ)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  have hL : 0 < L := Real.log_pos hp
  have hta : 0 < t * a := mul_pos ht ha
  have htb : 0 < t * b := mul_pos ht hb
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos (t * a) p
  have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos (t * b) p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hta p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one htb p
  have hden : 0 < 1 - r * s := by
    have : r * s < 1 :=
      mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
    linarith
  have hfrac0 : 0 ≤ (1 - r) * (1 - s) / (1 - r * s) :=
    div_nonneg (mul_nonneg (by linarith) (by linarith)) hden.le
  have hfrac : (1 - r) * (1 - s) / (1 - r * s) ≤ 1 - r := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hs0.le (sub_nonneg.mpr hr1.le)]
  have hr_eq : r = Real.exp (-(t * a * L)) := by
    simp only [r, xiMobiusContinuousApertureDiskNode, L]
    congr 1
    ring
  have hone : 1 - r ≤ t * a * L := by
    rw [hr_eq]
    linarith [Real.one_sub_le_exp_neg (t * a * L)]
  have hmetric0 :
      0 ≤ xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p := by
    change 0 ≤ d ^ 2 * (1 - r) * (1 - s) / (1 - r * s)
    calc
      0 ≤ d ^ 2 * ((1 - r) * (1 - s) / (1 - r * s)) :=
        mul_nonneg (sq_nonneg d) hfrac0
      _ = d ^ 2 * (1 - r) * (1 - s) / (1 - r * s) := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hmetric0 ht.le)]
  change (d ^ 2 * (1 - r) * (1 - s) / (1 - r * s)) / t ≤
    a * (d ^ 2 * L)
  rw [div_le_iff₀ ht]
  have hlocal := mul_le_mul_of_nonneg_left (hfrac.trans hone) (sq_nonneg d)
  calc
    d ^ 2 * (1 - r) * (1 - s) / (1 - r * s) =
        d ^ 2 * ((1 - r) * (1 - s) / (1 - r * s)) := by ring
    _ ≤ d ^ 2 * (t * a * L) := hlocal
    _ = a * (d ^ 2 * L) * t := by ring

/-- The completed all-prime two-aperture kernel. -/
def xiMobiusContinuousApertureKernel (a b : ℝ) : ℝ :=
  ∑' p : Nat.Primes, xiMobiusPrimeContinuousApertureSzegoMetric a b p

/-- **Cauchy tangent law.**  The full continuous Möbius source metric has the exact two-ray germ
`C_M * a*b/(a+b)`.  This strengthens the diagonal four-unit slope to the complete infinitesimal
Hilbert kernel. -/
theorem tendsto_xiMobiusContinuousApertureKernel_mul_div_nhdsGT_zero
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun t : ℝ => xiMobiusContinuousApertureKernel (t * a) (t * b) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureSlopeConstant * (a * b / (a + b)))) := by
  have hpoint (p : Nat.Primes) :=
    tendsto_xiMobiusPrimeContinuousApertureSzegoMetric_mul_div_nhdsGT_zero ha hb p
  have hsum : Summable
      (fun p : Nat.Primes => a * xiMobiusPrimeContinuousApertureSlopeTerm p) :=
    summable_xiMobiusPrimeContinuousApertureSlopeTerm.mul_left a
  have hbound : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ p : Nat.Primes,
      ‖xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t‖ ≤
        a * xiMobiusPrimeContinuousApertureSlopeTerm p := by
    filter_upwards [self_mem_nhdsWithin] with t ht p
    exact norm_xiMobiusPrimeContinuousApertureSzegoMetric_mul_div_le ht ha hb p
  have hlimit := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  simpa [xiMobiusContinuousApertureKernel,
    xiMobiusContinuousApertureSlopeConstant, tsum_div_const, tsum_mul_right] using hlimit

/-- The source-normalized infinitesimal aperture kernel. -/
def xiMobiusContinuousApertureFourUnitTangentKernel (a b : ℝ) : ℝ :=
  8 * a * b / (a + b)

theorem xiMobiusContinuousApertureFourUnitTangentKernel_self
    {a : ℝ} (ha : 0 < a) :
    xiMobiusContinuousApertureFourUnitTangentKernel a a = 4 * a := by
  simp only [xiMobiusContinuousApertureFourUnitTangentKernel]
  field_simp [ha.ne']
  ring

/-- The tangent-kernel correlation defect is the half-plane pseudohyperbolic metric. -/
theorem one_sub_xiMobiusContinuousApertureFourUnitTangentKernel_correlation
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    1 - xiMobiusContinuousApertureFourUnitTangentKernel a b ^ 2 /
        (xiMobiusContinuousApertureFourUnitTangentKernel a a *
          xiMobiusContinuousApertureFourUnitTangentKernel b b) =
      ((a - b) / (a + b)) ^ 2 := by
  rw [xiMobiusContinuousApertureFourUnitTangentKernel_self ha,
    xiMobiusContinuousApertureFourUnitTangentKernel_self hb]
  simp only [xiMobiusContinuousApertureFourUnitTangentKernel]
  have hab : a + b ≠ 0 := (add_pos ha hb).ne'
  field_simp [ha.ne', hb.ne', hab]
  ring

end

end RHTower
