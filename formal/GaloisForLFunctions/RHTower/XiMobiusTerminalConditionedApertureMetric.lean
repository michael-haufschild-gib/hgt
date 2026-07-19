import GaloisForLFunctions.RHTower.XiMobiusContinuousApertureSzegoMetric

/-!
# Terminal conditioning of the continuous Xi valuation aperture metric

The actual continuous Möbius--Schur valuation differences have a diagonally weighted Szegő Gram.
Removing one terminal aperture by a rank-one Hilbert projection does not leave that family.  The
Schur complement factorizes as another weighted Szegő kernel, with a boundary-vanishing radial
factor.  Consequently terminal conditioning changes the radial masses but preserves the complete
normalized pseudohyperbolic correlation geometry.

This identifies exactly what the physical zero-mode join can cancel: one radial aperture mode.  It
does not prove the still-missing global source-to-Xi response estimate.
-/

namespace RHTower

noncomputable section

open scoped BigOperators
open Filter

/-- The true continuous aperture metric after Hilbert-projecting away the ray at aperture `A`. -/
def xiMobiusPrimeTerminalConditionedApertureMetric
    (A a b : ℝ) (p : Nat.Primes) : ℝ :=
  xiMobiusPrimeContinuousApertureSzegoMetric a b p -
    xiMobiusPrimeContinuousApertureSzegoMetric a A p *
      xiMobiusPrimeContinuousApertureSzegoMetric A b p /
        xiMobiusPrimeContinuousApertureSzegoMetric A A p

/-- The radial factor of the terminal-conditioned Szegő feature. -/
def xiMobiusPrimeTerminalConditionedApertureScale
    (A a : ℝ) (p : Nat.Primes) : ℝ :=
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let u := xiMobiusContinuousApertureDiskNode A p
  q / (1 + q) * (1 - r) * (r - u) / (1 - r * u)

/-- Pseudohyperbolic radial gain created by removing the terminal aperture ray. -/
def xiMobiusPrimeTerminalConditioningGain
    (A a : ℝ) (p : Nat.Primes) : ℝ :=
  let r := xiMobiusContinuousApertureDiskNode a p
  let u := xiMobiusContinuousApertureDiskNode A p
  (r - u) / (1 - r * u)

/-- A canonical geometric-depth realization of the terminal-conditioned metric. -/
def xiMobiusPrimeTerminalConditionedApertureFeature
    (A a : ℝ) (p : Nat.Primes) (e : ℕ) : ℝ :=
  xiMobiusPrimeTerminalConditionedApertureScale A a p *
    xiMobiusContinuousApertureDiskNode a p ^ e

/-- Exact Schur-complement factorization.  Terminal conditioning stays inside the weighted Szegő
family instead of producing a new kernel. -/
theorem xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized
    {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditionedApertureMetric A a b p =
      let q := xiTransversePrimeApertureDiskNode 1 p
      let r := xiMobiusContinuousApertureDiskNode a p
      let s := xiMobiusContinuousApertureDiskNode b p
      let u := xiMobiusContinuousApertureDiskNode A p
      (q / (1 + q)) ^ 2 *
        (1 - r) * (1 - s) * (r - u) * (s - u) /
          ((1 - r * s) * (1 - r * u) * (1 - s * u)) := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos b p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos A p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hqplus : 1 + q ≠ 0 := by linarith
  have hrs : 1 - r * s ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
    linarith
  have hru : 1 - r * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  have hsu : 1 - s * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hs0.le hs1 hu1.le
    linarith
  have huu : 1 - u * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hu0.le hu1 hu1.le
    linarith
  have huminus : 1 - u ≠ 0 := by linarith
  simp only [xiMobiusPrimeTerminalConditionedApertureMetric,
    xiMobiusPrimeContinuousApertureSzegoMetric]
  change
    (q / (1 + q)) ^ 2 * (1 - r) * (1 - s) / (1 - r * s) -
      ((q / (1 + q)) ^ 2 * (1 - r) * (1 - u) / (1 - r * u)) *
        ((q / (1 + q)) ^ 2 * (1 - u) * (1 - s) / (1 - u * s)) /
          ((q / (1 + q)) ^ 2 * (1 - u) * (1 - u) / (1 - u * u)) =
      (q / (1 + q)) ^ 2 *
        (1 - r) * (1 - s) * (r - u) * (s - u) /
          ((1 - r * s) * (1 - r * u) * (1 - s * u))
  field_simp [hq0.ne', hqplus, hrs, hru, hsu, huu, huminus]
  ring

/-- The conditioned metric is the completed Gram of its canonical geometric-depth features. -/
theorem tsum_xiMobiusPrimeTerminalConditionedApertureFeature_mul_eq_metric
    {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    (∑' e : ℕ, xiMobiusPrimeTerminalConditionedApertureFeature A a p e *
      xiMobiusPrimeTerminalConditionedApertureFeature A b p e) =
        xiMobiusPrimeTerminalConditionedApertureMetric A a b p := by
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  let q := xiTransversePrimeApertureDiskNode 1 p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 ≤ r := (xiMobiusContinuousApertureDiskNode_pos a p).le
  have hs0 : 0 ≤ s := (xiMobiusContinuousApertureDiskNode_pos b p).le
  have hu0 : 0 ≤ u := (xiMobiusContinuousApertureDiskNode_pos A p).le
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hrs0 : 0 ≤ r * s := mul_nonneg hr0 hs0
  have hrs1 : r * s < 1 :=
    mul_lt_one_of_nonneg_of_lt_one_left hr0 hr1 hs1.le
  have hqplus : 1 + q ≠ 0 := by linarith
  have hrs : 1 - r * s ≠ 0 := by linarith
  have hru : 1 - r * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0 hr1 hu1.le
    linarith
  have hsu : 1 - s * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hs0 hs1 hu1.le
    linarith
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA ha hb]
  calc
    (∑' e : ℕ, xiMobiusPrimeTerminalConditionedApertureFeature A a p e *
        xiMobiusPrimeTerminalConditionedApertureFeature A b p e) =
      ∑' e : ℕ, (xiMobiusPrimeTerminalConditionedApertureScale A a p *
        xiMobiusPrimeTerminalConditionedApertureScale A b p) *
          (r * s) ^ e := by
            apply tsum_congr
            intro e
            simp only [xiMobiusPrimeTerminalConditionedApertureFeature, r, s, mul_pow]
            ring
    _ = (xiMobiusPrimeTerminalConditionedApertureScale A a p *
        xiMobiusPrimeTerminalConditionedApertureScale A b p) *
          ∑' e : ℕ, (r * s) ^ e := tsum_mul_left
    _ = (xiMobiusPrimeTerminalConditionedApertureScale A a p *
        xiMobiusPrimeTerminalConditionedApertureScale A b p) *
          (1 - r * s)⁻¹ := by rw [tsum_geometric_of_lt_one hrs0 hrs1]
    _ = _ := by
      simp only [xiMobiusPrimeTerminalConditionedApertureScale]
      change
        (q / (1 + q) * (1 - r) * (r - u) / (1 - r * u) *
            (q / (1 + q) * (1 - s) * (s - u) / (1 - s * u))) *
            (1 - r * s)⁻¹ =
          (q / (1 + q)) ^ 2 *
            (1 - r) * (1 - s) * (r - u) * (s - u) /
              ((1 - r * s) * (1 - r * u) * (1 - s * u))
      field_simp [hq0.ne', hqplus, hrs, hru, hsu]

/-- The terminal aperture is precisely the radical introduced by terminal conditioning. -/
theorem xiMobiusPrimeTerminalConditionedApertureMetric_terminal_left
    {A b : ℝ} (hA : 0 < A) (hb : 0 < b) (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditionedApertureMetric A A b p = 0 := by
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA hA hb]
  ring

theorem xiMobiusPrimeTerminalConditionedApertureMetric_terminal_right
    {A a : ℝ} (hA : 0 < A) (ha : 0 < a) (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditionedApertureMetric A a A p = 0 := by
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA ha hA]
  ring

/-- Inside the physical chamber `0<a<A`, the conditioned aperture ray retains positive mass. -/
theorem xiMobiusPrimeTerminalConditionedApertureMetric_self_pos
    {A a : ℝ} (ha : 0 < a) (haA : a < A) (p : Nat.Primes) :
    0 < xiMobiusPrimeTerminalConditionedApertureMetric A a a p := by
  have hA : 0 < A := ha.trans haA
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos A p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hur : u < r := by
    dsimp only [u, r, xiMobiusContinuousApertureDiskNode]
    apply Real.exp_lt_exp.mpr
    have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
    nlinarith
  have hrr : 0 < 1 - r * r := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hr1.le
    linarith
  have hru : 0 < 1 - r * u := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA ha ha]
  change 0 < (q / (1 + q)) ^ 2 *
    (1 - r) * (1 - r) * (r - u) * (r - u) /
      ((1 - r * r) * (1 - r * u) * (1 - r * u))
  positivity

/-- Terminal conditioning has a strictly positive radial gain in the physical chamber. -/
theorem xiMobiusPrimeTerminalConditioningGain_pos
    {A a : ℝ} (ha : 0 < a) (haA : a < A) (p : Nat.Primes) :
    0 < xiMobiusPrimeTerminalConditioningGain A a p := by
  have hA : 0 < A := ha.trans haA
  let r := xiMobiusContinuousApertureDiskNode a p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos A p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hur : u < r := by
    dsimp only [u, r, xiMobiusContinuousApertureDiskNode]
    apply Real.exp_lt_exp.mpr
    have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
    nlinarith
  have hru : 0 < 1 - r * u := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  exact div_pos (sub_pos.mpr hur) hru

/-- The terminal Blaschke gain is strictly smaller than the raw aperture node.  Thus conditioning
supplies one additional aperture power at every fixed positive aperture. -/
theorem xiMobiusPrimeTerminalConditioningGain_lt_diskNode
    {A a : ℝ} (ha : 0 < a) (haA : a < A) (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditioningGain A a p <
      xiMobiusContinuousApertureDiskNode a p := by
  have hA : 0 < A := ha.trans haA
  let r := xiMobiusContinuousApertureDiskNode a p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos A p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hru : 0 < 1 - r * u := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  have hsq : 0 < 1 - r ^ 2 := by nlinarith
  have hstrict : r - u < r * (1 - r * u) := by
    have hproduct : 0 < u * (1 - r ^ 2) := mul_pos hu0 hsq
    nlinarith
  rw [xiMobiusPrimeTerminalConditioningGain]
  change (r - u) / (1 - r * u) < r
  exact (div_lt_iff₀ hru).2 hstrict

/-- Exact radial form of the conditioned diagonal: the unconditioned mass is multiplied by the
squared pseudohyperbolic distance to the terminal aperture. -/
theorem xiMobiusPrimeTerminalConditionedApertureMetric_self_eq_gain_sq_mul
    {A a : ℝ} (ha : 0 < a) (haA : a < A) (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditionedApertureMetric A a a p =
      xiMobiusPrimeContinuousApertureSzegoMetric a a p *
        xiMobiusPrimeTerminalConditioningGain A a p ^ 2 := by
  have hA : 0 < A := ha.trans haA
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos A p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hqplus : 1 + q ≠ 0 := by linarith
  have hrminus : 1 - r ≠ 0 := by linarith
  have hrplus : 1 + r ≠ 0 := by linarith
  have hrr : 1 - r * r ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hr1.le
    linarith
  have hrrpow : 1 - r ^ 2 ≠ 0 := by
    simpa [pow_two] using hrr
  have hru : 1 - r * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA ha ha,
    xiMobiusPrimeContinuousApertureSzegoMetric_self ha p]
  change
    (q / (1 + q)) ^ 2 * (1 - r) * (1 - r) * (r - u) * (r - u) /
        ((1 - r * r) * (1 - r * u) * (1 - r * u)) =
      ((q / (1 + q)) ^ 2 * ((1 - r) / (1 + r))) *
        ((r - u) / (1 - r * u)) ^ 2
  field_simp [hq0.ne', hqplus, hrminus, hrplus, hrr, hrrpow, hru]
  ring

/-- Quantitative aperture-power gain.  Terminal joining strictly suppresses the diagonal by more
than the square of the raw disk node `p^{-a}`. -/
theorem xiMobiusPrimeTerminalConditionedApertureMetric_self_lt_diskNode_sq_mul
    {A a : ℝ} (ha : 0 < a) (haA : a < A) (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditionedApertureMetric A a a p <
      xiMobiusContinuousApertureDiskNode a p ^ 2 *
        xiMobiusPrimeContinuousApertureSzegoMetric a a p := by
  have hgain0 := xiMobiusPrimeTerminalConditioningGain_pos ha haA p
  have hgain := xiMobiusPrimeTerminalConditioningGain_lt_diskNode ha haA p
  have hnode0 : 0 < xiMobiusContinuousApertureDiskNode a p :=
    xiMobiusContinuousApertureDiskNode_pos a p
  have hgainSq : xiMobiusPrimeTerminalConditioningGain A a p ^ 2 <
      xiMobiusContinuousApertureDiskNode a p ^ 2 := by nlinarith
  have hmetricPos : 0 < xiMobiusPrimeContinuousApertureSzegoMetric a a p := by
    rw [xiMobiusPrimeContinuousApertureSzegoMetric_self ha p]
    have hq0 : 0 < xiTransversePrimeApertureDiskNode 1 p :=
      xiTransversePrimeApertureDiskNode_pos 1 p
    have hr1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
    positivity
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_self_eq_gain_sq_mul ha haA]
  nlinarith

/-- **Terminal-conditioning correlation invariance.**  Removing the terminal ray changes only
radial weights.  Every normalized pseudohyperbolic aperture angle is exactly preserved. -/
theorem xiMobiusPrimeTerminalConditionedAperture_metricRatio_eq_correlation
    {A a b : ℝ} (ha : 0 < a) (hb : 0 < b) (haA : a < A) (hbA : b < A)
    (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditionedApertureMetric A a b p ^ 2 /
        (xiMobiusPrimeTerminalConditionedApertureMetric A a a p *
          xiMobiusPrimeTerminalConditionedApertureMetric A b b p) =
      xiMobiusPrimeContinuousApertureNormalizedCorrelationSq a b p := by
  have hA : 0 < A := ha.trans haA
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos b p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos A p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hur : u < r := by
    dsimp only [u, r, xiMobiusContinuousApertureDiskNode]
    apply Real.exp_lt_exp.mpr
    have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
    nlinarith
  have hus : u < s := by
    dsimp only [u, s, xiMobiusContinuousApertureDiskNode]
    apply Real.exp_lt_exp.mpr
    have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos hp
    nlinarith
  have hqplus : 1 + q ≠ 0 := by linarith
  have hrminus : 1 - r ≠ 0 := by linarith
  have hsminus : 1 - s ≠ 0 := by linarith
  have hruminus : r - u ≠ 0 := by linarith
  have hsuminus : s - u ≠ 0 := by linarith
  have hrs : 1 - r * s ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
    linarith
  have hrr : 1 - r * r ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hr1.le
    linarith
  have hss : 1 - s * s ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hs0.le hs1 hs1.le
    linarith
  have hru : 1 - r * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  have hsu : 1 - s * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hs0.le hs1 hu1.le
    linarith
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA ha hb,
    xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA ha ha,
    xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA hb hb]
  change
    (((q / (1 + q)) ^ 2 * (1 - r) * (1 - s) * (r - u) * (s - u) /
        ((1 - r * s) * (1 - r * u) * (1 - s * u))) ^ 2 /
      (((q / (1 + q)) ^ 2 * (1 - r) * (1 - r) * (r - u) * (r - u) /
          ((1 - r * r) * (1 - r * u) * (1 - r * u))) *
        ((q / (1 + q)) ^ 2 * (1 - s) * (1 - s) * (s - u) * (s - u) /
          ((1 - s * s) * (1 - s * u) * (1 - s * u))))) =
      (1 - r ^ 2) * (1 - s ^ 2) / (1 - r * s) ^ 2
  field_simp [hq0.ne', hqplus, hrminus, hsminus, hruminus, hsuminus,
    hrs, hrr, hss, hru, hsu]

/-- Terminal conditioning is exactly diagonal Blaschke dressing of the original aperture metric. -/
theorem xiMobiusPrimeTerminalConditionedApertureMetric_eq_metric_mul_gains
    {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    xiMobiusPrimeTerminalConditionedApertureMetric A a b p =
      xiMobiusPrimeContinuousApertureSzegoMetric a b p *
        xiMobiusPrimeTerminalConditioningGain A a p *
          xiMobiusPrimeTerminalConditioningGain A b p := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r := xiMobiusContinuousApertureDiskNode a p
  let s := xiMobiusContinuousApertureDiskNode b p
  let u := xiMobiusContinuousApertureDiskNode A p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos a p
  have hs0 : 0 < s := xiMobiusContinuousApertureDiskNode_pos b p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos A p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one ha p
  have hs1 : s < 1 := xiMobiusContinuousApertureDiskNode_lt_one hb p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one hA p
  have hqplus : 1 + q ≠ 0 := by linarith
  have hrs : 1 - r * s ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hs1.le
    linarith
  have hru : 1 - r * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  have hsu : 1 - s * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hs0.le hs1 hu1.le
    linarith
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized hA ha hb]
  simp only [xiMobiusPrimeContinuousApertureSzegoMetric,
    xiMobiusPrimeTerminalConditioningGain]
  change
    (q / (1 + q)) ^ 2 *
        (1 - r) * (1 - s) * (r - u) * (s - u) /
          ((1 - r * s) * (1 - r * u) * (1 - s * u)) =
      ((q / (1 + q)) ^ 2 * (1 - r) * (1 - s) / (1 - r * s)) *
        ((r - u) / (1 - r * u)) * ((s - u) / (1 - s * u))
  field_simp [hqplus, hrs, hru, hsu]

/-- In the joint critical tangent, the terminal gain loses every prime weight and becomes the
scale-ratio filter `(A-a)/(A+a)`. -/
theorem tendsto_xiMobiusPrimeTerminalConditioningGain_mul_nhdsGT_zero
    {A a : ℝ} (hA : 0 < A) (ha : 0 < a) (p : Nat.Primes) :
    Tendsto
      (fun t : ℝ => xiMobiusPrimeTerminalConditioningGain (t * A) (t * a) p)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((A - a) / (A + a))) := by
  let L := Real.log (p : ℝ)
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hL : 0 < L := Real.log_pos hp
  have hAgap :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero A p
  have hagap :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero a p
  have hsumgap :=
    tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero (a + A) p
  have hdenLim : (a + A) * L ≠ 0 :=
    mul_ne_zero (add_pos ha hA).ne' hL.ne'
  have hratio : Tendsto
      (fun t : ℝ =>
        (((1 - xiMobiusContinuousApertureDiskNode (t * A) p) / t) -
            ((1 - xiMobiusContinuousApertureDiskNode (t * a) p) / t)) /
          ((1 - xiMobiusContinuousApertureDiskNode (t * (a + A)) p) / t))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (((A * L) - (a * L)) / ((a + A) * L))) := by
    exact (hAgap.sub hagap).div hsumgap hdenLim
  have hlimEq :
      ((A * L) - (a * L)) / ((a + A) * L) = (A - a) / (A + a) := by
    field_simp [hL.ne', (add_pos ha hA).ne', (add_pos hA ha).ne']
    ring
  rw [← hlimEq]
  apply hratio.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : 0 < t := ht
  let r := xiMobiusContinuousApertureDiskNode (t * a) p
  let u := xiMobiusContinuousApertureDiskNode (t * A) p
  have hta : 0 < t * a := mul_pos ht0 ha
  have htA : 0 < t * A := mul_pos ht0 hA
  have hr0 : 0 < r := xiMobiusContinuousApertureDiskNode_pos (t * a) p
  have hu0 : 0 < u := xiMobiusContinuousApertureDiskNode_pos (t * A) p
  have hr1 : r < 1 := xiMobiusContinuousApertureDiskNode_lt_one hta p
  have hu1 : u < 1 := xiMobiusContinuousApertureDiskNode_lt_one htA p
  have hru : 1 - r * u ≠ 0 := by
    have := mul_lt_one_of_nonneg_of_lt_one_left hr0.le hr1 hu1.le
    linarith
  have hsumNode :
      xiMobiusContinuousApertureDiskNode (t * (a + A)) p = r * u := by
    rw [← xiMobiusContinuousApertureDiskNode_add]
    congr 1
    ring
  rw [xiMobiusPrimeTerminalConditioningGain]
  change
    (((1 - u) / t) - ((1 - r) / t)) /
        ((1 - xiMobiusContinuousApertureDiskNode (t * (a + A)) p) / t) =
      (r - u) / (1 - r * u)
  rw [hsumNode]
  field_simp [ht0.ne', hru]
  ring

/-- The prime-independent aperture shape left by terminal conditioning in the critical tangent. -/
def xiMobiusTerminalConditionedApertureCauchyShape (A a b : ℝ) : ℝ :=
  (a * b / (a + b)) * ((A - a) / (A + a)) * ((A - b) / (A + b))

/-- Primewise critical tangent law for the terminal-conditioned true-aperture metric.  The entire
prime dependence remains the old logarithmic slope term; conditioning contributes only a common
aperture-ratio multiplier. -/
theorem tendsto_xiMobiusPrimeTerminalConditionedApertureMetric_mul_div_nhdsGT_zero
    {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b) (p : Nat.Primes) :
    Tendsto
      (fun t : ℝ =>
        xiMobiusPrimeTerminalConditionedApertureMetric
          (t * A) (t * a) (t * b) p / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusPrimeContinuousApertureSlopeTerm p *
        xiMobiusTerminalConditionedApertureCauchyShape A a b)) := by
  have hmetric :=
    tendsto_xiMobiusPrimeContinuousApertureSzegoMetric_mul_div_nhdsGT_zero ha hb p
  have hgainA :=
    tendsto_xiMobiusPrimeTerminalConditioningGain_mul_nhdsGT_zero hA ha p
  have hgainB :=
    tendsto_xiMobiusPrimeTerminalConditioningGain_mul_nhdsGT_zero hA hb p
  have hproduct := (hmetric.mul hgainA).mul hgainB
  have hcongr : Tendsto
      (fun t : ℝ =>
        xiMobiusPrimeTerminalConditionedApertureMetric
          (t * A) (t * a) (t * b) p / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((xiMobiusPrimeContinuousApertureSlopeTerm p * (a * b / (a + b))) *
        ((A - a) / (A + a)) * ((A - b) / (A + b)))) := by
    apply hproduct.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : 0 < t := ht
    rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_metric_mul_gains
      (mul_pos ht0 hA) (mul_pos ht0 ha) (mul_pos ht0 hb)]
    ring
  simpa only [xiMobiusTerminalConditionedApertureCauchyShape, mul_assoc] using hcongr

/-- The terminal-conditioned tangent quotient has the same summable logarithmic prime-square
majorant as the unconditioned metric. -/
theorem norm_xiMobiusPrimeTerminalConditionedApertureMetric_mul_div_le
    {t A a b : ℝ} (ht : 0 < t) (hA : 0 < A) (ha : 0 < a) (hb : 0 < b)
    (haA : a < A) (hbA : b < A) (p : Nat.Primes) :
    ‖xiMobiusPrimeTerminalConditionedApertureMetric
        (t * A) (t * a) (t * b) p / t‖ ≤
      a * xiMobiusPrimeContinuousApertureSlopeTerm p := by
  have hta : 0 < t * a := mul_pos ht ha
  have htb : 0 < t * b := mul_pos ht hb
  have htA : 0 < t * A := mul_pos ht hA
  have htaA : t * a < t * A := mul_lt_mul_of_pos_left haA ht
  have htbA : t * b < t * A := mul_lt_mul_of_pos_left hbA ht
  have hgainA0 := xiMobiusPrimeTerminalConditioningGain_pos hta htaA p
  have hgainB0 := xiMobiusPrimeTerminalConditioningGain_pos htb htbA p
  have hgainA := xiMobiusPrimeTerminalConditioningGain_lt_diskNode hta htaA p
  have hgainB := xiMobiusPrimeTerminalConditioningGain_lt_diskNode htb htbA p
  have hnodeA1 := xiMobiusContinuousApertureDiskNode_lt_one hta p
  have hnodeB1 := xiMobiusContinuousApertureDiskNode_lt_one htb p
  have hgainA_norm :
      ‖xiMobiusPrimeTerminalConditioningGain (t * A) (t * a) p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hgainA0]
    exact (hgainA.trans hnodeA1).le
  have hgainB_norm :
      ‖xiMobiusPrimeTerminalConditioningGain (t * A) (t * b) p‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hgainB0]
    exact (hgainB.trans hnodeB1).le
  rw [xiMobiusPrimeTerminalConditionedApertureMetric_eq_metric_mul_gains htA hta htb]
  calc
    ‖xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p *
          xiMobiusPrimeTerminalConditioningGain (t * A) (t * a) p *
            xiMobiusPrimeTerminalConditioningGain (t * A) (t * b) p / t‖ =
        ‖xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t‖ *
          ‖xiMobiusPrimeTerminalConditioningGain (t * A) (t * a) p‖ *
            ‖xiMobiusPrimeTerminalConditioningGain (t * A) (t * b) p‖ := by
              simp only [norm_div, norm_mul]
              ring
    _ ≤ ‖xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t‖ *
          1 * 1 := by gcongr
    _ = ‖xiMobiusPrimeContinuousApertureSzegoMetric (t * a) (t * b) p / t‖ := by ring
    _ ≤ a * xiMobiusPrimeContinuousApertureSlopeTerm p :=
      norm_xiMobiusPrimeContinuousApertureSzegoMetric_mul_div_le ht ha hb p

/-- The all-prime terminal-conditioned true-aperture kernel. -/
def xiMobiusTerminalConditionedApertureKernel (A a b : ℝ) : ℝ :=
  ∑' p : Nat.Primes, xiMobiusPrimeTerminalConditionedApertureMetric A a b p

/-- **Critical terminal-conditioning no-go and positive survivor.**  In the completed all-prime
joint tangent, terminal conditioning preserves the complete logarithmic prime distribution.  It
multiplies the Cauchy aperture germ only by a prime-independent scale-ratio filter. -/
theorem tendsto_xiMobiusTerminalConditionedApertureKernel_mul_div_nhdsGT_zero
    {A a b : ℝ} (hA : 0 < A) (ha : 0 < a) (hb : 0 < b)
    (haA : a < A) (hbA : b < A) :
    Tendsto
      (fun t : ℝ =>
        xiMobiusTerminalConditionedApertureKernel (t * A) (t * a) (t * b) / t)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (xiMobiusContinuousApertureSlopeConstant *
        xiMobiusTerminalConditionedApertureCauchyShape A a b)) := by
  have hpoint (p : Nat.Primes) :=
    tendsto_xiMobiusPrimeTerminalConditionedApertureMetric_mul_div_nhdsGT_zero
      hA ha hb p
  have hsum : Summable
      (fun p : Nat.Primes => a * xiMobiusPrimeContinuousApertureSlopeTerm p) :=
    summable_xiMobiusPrimeContinuousApertureSlopeTerm.mul_left a
  have hbound : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ p : Nat.Primes,
      ‖xiMobiusPrimeTerminalConditionedApertureMetric
          (t * A) (t * a) (t * b) p / t‖ ≤
        a * xiMobiusPrimeContinuousApertureSlopeTerm p := by
    filter_upwards [self_mem_nhdsWithin] with t ht p
    exact norm_xiMobiusPrimeTerminalConditionedApertureMetric_mul_div_le
      ht hA ha hb haA hbA p
  have hlimit := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  simpa [xiMobiusTerminalConditionedApertureKernel,
    xiMobiusContinuousApertureSlopeConstant, tsum_div_const, tsum_mul_right] using hlimit

end

end RHTower
