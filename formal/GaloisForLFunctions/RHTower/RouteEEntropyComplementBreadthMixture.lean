import GaloisForLFunctions.RHTower.RouteEProductTruncatedReservoirMass
import GaloisForLFunctions.RHTower.RouteEForbiddenSupportStability
import Mathlib.Data.Nat.Choose.Sum

/-!
# Route E entropy-complement breadth mixture

This module formalizes the dependency-closed finite content of the entropy-complement correction
to the Route E whole-anchor relation.  It proves:

* the exact divided-Poisson convolution recovering the complete terminal breadth layer;
* the exact conditional-binomial variance, in a denominator-free form;
* a finite Chebyshev window theorem recovering at least a `1 - C⁻²` fraction of mass under the
  central balance condition;
* the corrected column-load scale and its sharp threshold;
* the subpower cutoff/product law and the exact source-prime deletion bound;
* parity reversal for both adjacent breadth directions; and
* the finite Hellinger/chi-square endpoint consumer, including unmatched mass.

No short-interval rough-token lower bound, column-balance source, or recurrence seam estimate is
assumed or asserted.  Those remain the analytic Route E frontier.
-/

open scoped BigOperators
open Finset

namespace RHTower

noncomputable section

/-! ## Exact entropy-complement convolution -/

/-- Unnormalized conditional breadth weight.  It is the binomial coefficient multiplying a
low-reservoir mass `S^b` and complementary rough-token mass `R^(k-b)`. -/
def routeEConditionalBreadthWeight (S R : ℝ) (k b : ℕ) : ℝ :=
  (k.choose b : ℝ) * S ^ b * R ^ (k - b)

/-- Total unnormalized conditional breadth mass. -/
def routeEConditionalBreadthMass (S R : ℝ) (k : ℕ) : ℝ :=
  ∑ b ∈ Finset.range (k + 1), routeEConditionalBreadthWeight S R k b

/-- The conditional breadth weights have exact total mass `(S + R)^k`. -/
theorem routeEConditionalBreadthMass_eq (S R : ℝ) (k : ℕ) :
    routeEConditionalBreadthMass S R k = (S + R) ^ k := by
  rw [routeEConditionalBreadthMass, add_pow]
  apply Finset.sum_congr rfl
  intro b hb
  unfold routeEConditionalBreadthWeight
  ring

/-- Divided-Poisson form of one complementary breadth branch. -/
def routeEDividedBreadthWeight (S R : ℝ) (k b : ℕ) : ℝ :=
  S ^ b / (b.factorial : ℝ) *
    (R ^ (k - b) / ((k - b).factorial : ℝ))

/-- One divided-Poisson branch is its conditional-binomial weight divided by `k!`. -/
theorem routeEDividedBreadthWeight_eq_conditional_div_factorial
    (S R : ℝ) {k b : ℕ} (hb : b ≤ k) :
    routeEDividedBreadthWeight S R k b =
      routeEConditionalBreadthWeight S R k b / (k.factorial : ℝ) := by
  have hfactNat := Nat.choose_mul_factorial_mul_factorial hb
  have hfact :
      (k.choose b : ℝ) * (b.factorial : ℝ) * ((k - b).factorial : ℝ) =
        (k.factorial : ℝ) := by
    exact_mod_cast hfactNat
  have hb0 : (b.factorial : ℝ) ≠ 0 := by positivity
  have hkb0 : ((k - b).factorial : ℝ) ≠ 0 := by positivity
  have hk0 : (k.factorial : ℝ) ≠ 0 := by positivity
  unfold routeEDividedBreadthWeight routeEConditionalBreadthWeight
  field_simp [hb0, hkb0, hk0]
  rw [← hfact]
  ring

/-- **Exact entropy-complement convolution.**  Varying low and rough breadth while fixing their
sum recovers the complete divided-Poisson mass, with no local-limit loss. -/
theorem routeEDividedBreadthWeight_sum_eq (S R : ℝ) (k : ℕ) :
    (∑ b ∈ Finset.range (k + 1), routeEDividedBreadthWeight S R k b) =
      (S + R) ^ k / (k.factorial : ℝ) := by
  calc
    (∑ b ∈ Finset.range (k + 1), routeEDividedBreadthWeight S R k b) =
        ∑ b ∈ Finset.range (k + 1),
          routeEConditionalBreadthWeight S R k b / (k.factorial : ℝ) := by
            apply Finset.sum_congr rfl
            intro b hb
            exact routeEDividedBreadthWeight_eq_conditional_div_factorial S R
              (Finset.mem_range_succ_iff.mp hb)
    _ = routeEConditionalBreadthMass S R k / (k.factorial : ℝ) := by
      rw [routeEConditionalBreadthMass, Finset.sum_div]
    _ = (S + R) ^ k / (k.factorial : ℝ) := by
      rw [routeEConditionalBreadthMass_eq]

/-! ## Exact conditional variance and central-window recovery -/

/-- Denominator-free displacement from the conditional breadth center `k S / (S + R)`. -/
def routeEConditionalBreadthDisplacement (S R : ℝ) (k b : ℕ) : ℝ :=
  (b : ℝ) * (S + R) - (k : ℝ) * S

/-- Denominator-free second centered moment of the conditional breadth law. -/
def routeEConditionalBreadthCenteredVariance (S R : ℝ) (k : ℕ) : ℝ :=
  ∑ b ∈ Finset.range (k + 1),
    routeEConditionalBreadthDisplacement S R k b ^ 2 *
      routeEConditionalBreadthWeight S R k b

private theorem routeEConditionalBreadthCenteredVariance_succ
    (S R : ℝ) (n : ℕ) :
    routeEConditionalBreadthCenteredVariance S R (n + 1) =
      (S + R) * routeEConditionalBreadthCenteredVariance S R n +
        S * R * (S + R) * routeEConditionalBreadthMass S R n := by
  let f : ℕ → ℕ → ℝ := fun i j =>
    routeEConditionalBreadthDisplacement S R (n + 1) i ^ 2 * S ^ i * R ^ j
  calc
    routeEConditionalBreadthCenteredVariance S R (n + 1) =
        ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * f i (n + 1 - i) := by
          rw [routeEConditionalBreadthCenteredVariance]
          apply Finset.sum_congr rfl
          intro i hi
          simp only [f]
          unfold routeEConditionalBreadthWeight
          ring
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * f i (n + 1 - i)) +
        ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * f (i + 1) (n - i) := by
          exact Finset.sum_choose_succ_mul f n
    _ = (S + R) * routeEConditionalBreadthCenteredVariance S R n +
        S * R * (S + R) * routeEConditionalBreadthMass S R n := by
          rw [routeEConditionalBreadthCenteredVariance, routeEConditionalBreadthMass]
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          have hin : i ≤ n := Finset.mem_range_succ_iff.mp hi
          have hRexp : n + 1 - i = (n - i) + 1 := by omega
          simp only [f]
          rw [hRexp, pow_succ, pow_succ]
          unfold routeEConditionalBreadthWeight routeEConditionalBreadthDisplacement
          push_cast
          ring

/-- **Exact denominator-free conditional variance.**  If `B` has conditional binomial weights
`choose(k,b) S^b R^(k-b)`, then

`sum ((S+R)B-kS)^2 w(B) = k S R (S+R)^k`.

The identity remains valid at every degenerate endpoint and therefore needs no division or
positivity premise. -/
theorem routeEConditionalBreadthCenteredVariance_eq (S R : ℝ) (k : ℕ) :
    routeEConditionalBreadthCenteredVariance S R k =
      (k : ℝ) * S * R * (S + R) ^ k := by
  induction k with
  | zero => simp [routeEConditionalBreadthCenteredVariance,
      routeEConditionalBreadthDisplacement, routeEConditionalBreadthWeight]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl]
      rw [routeEConditionalBreadthCenteredVariance_succ, ih,
        routeEConditionalBreadthMass_eq]
      rw [pow_succ]
      push_cast
      ring

/-- A source-predeclared central entropy-complement window.  `central_balance` is the exact finite
counterpart of `k ~ S + R` and `S ~ S + R`; it is precisely what turns Chebyshev's variance budget
into a `1 - C⁻²` retained-mass law. -/
structure RouteEEntropyComplementWindowData where
  lowMass : ℝ
  roughMass : ℝ
  windowConstant : ℝ
  totalBreadth : ℕ
  lowMass_nonneg : 0 ≤ lowMass
  roughMass_pos : 0 < roughMass
  windowConstant_pos : 0 < windowConstant
  central_balance :
    (totalBreadth : ℝ) * lowMass ≤ (lowMass + roughMass) ^ 2

namespace RouteEEntropyComplementWindowData

/-- Total reciprocal breadth mass. -/
def totalMass (d : RouteEEntropyComplementWindowData) : ℝ :=
  d.lowMass + d.roughMass

/-- Denominator-free Chebyshev aperture corresponding to breadth radius
`C * sqrt(roughMass)`. -/
def aperture (d : RouteEEntropyComplementWindowData) : ℝ :=
  d.windowConstant * d.totalMass * Real.sqrt d.roughMass

/-- Closed conditional central window. -/
def window (d : RouteEEntropyComplementWindowData) : Finset ℕ :=
  (Finset.range (d.totalBreadth + 1)).filter fun b =>
    |routeEConditionalBreadthDisplacement d.lowMass d.roughMass d.totalBreadth b| ≤ d.aperture

/-- Unnormalized conditional mass retained by the central window. -/
def windowMass (d : RouteEEntropyComplementWindowData) : ℝ :=
  ∑ b ∈ d.window,
    routeEConditionalBreadthWeight d.lowMass d.roughMass d.totalBreadth b

theorem totalMass_pos (d : RouteEEntropyComplementWindowData) : 0 < d.totalMass := by
  unfold totalMass
  linarith [d.lowMass_nonneg, d.roughMass_pos]

theorem aperture_pos (d : RouteEEntropyComplementWindowData) : 0 < d.aperture := by
  unfold aperture
  exact mul_pos (mul_pos d.windowConstant_pos d.totalMass_pos)
    (Real.sqrt_pos.2 d.roughMass_pos)

theorem conditionalBreadthWeight_nonneg
    (d : RouteEEntropyComplementWindowData) (b : ℕ) :
    0 ≤ routeEConditionalBreadthWeight
      d.lowMass d.roughMass d.totalBreadth b := by
  unfold routeEConditionalBreadthWeight
  positivity

/-- Weighted Chebyshev inequality before central cancellation. -/
theorem aperture_sq_mul_tailMass_le_variance
    (d : RouteEEntropyComplementWindowData) :
    d.aperture ^ 2 *
        (∑ b ∈ Finset.range (d.totalBreadth + 1) with
          b ∉ d.window,
          routeEConditionalBreadthWeight
            d.lowMass d.roughMass d.totalBreadth b) ≤
      routeEConditionalBreadthCenteredVariance
        d.lowMass d.roughMass d.totalBreadth := by
  rw [routeEConditionalBreadthCenteredVariance, Finset.mul_sum]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.filter_subset _ _
  · intro b hb hnot
    exact mul_nonneg (sq_nonneg _)
      (d.conditionalBreadthWeight_nonneg b)
  · intro b hb
    have hbRange : b ∈ Finset.range (d.totalBreadth + 1) :=
      (Finset.mem_filter.mp hb).1
    have hbOutside : b ∉ d.window := (Finset.mem_filter.mp hb).2
    have hnotle :
        ¬|routeEConditionalBreadthDisplacement
            d.lowMass d.roughMass d.totalBreadth b| ≤ d.aperture := by
      simpa [window, hbRange] using hbOutside
    have hlt : d.aperture <
        |routeEConditionalBreadthDisplacement
          d.lowMass d.roughMass d.totalBreadth b| := lt_of_not_ge hnotle
    have hsq : d.aperture ^ 2 ≤
        routeEConditionalBreadthDisplacement
          d.lowMass d.roughMass d.totalBreadth b ^ 2 := by
      have ha := d.aperture_pos
      have habs := abs_nonneg
        (routeEConditionalBreadthDisplacement
          d.lowMass d.roughMass d.totalBreadth b)
      nlinarith [sq_abs
        (routeEConditionalBreadthDisplacement
          d.lowMass d.roughMass d.totalBreadth b)]
    exact mul_le_mul_of_nonneg_right hsq
      (d.conditionalBreadthWeight_nonneg b)

/-- **Central-window entropy recovery.**  The coupled breadth window retains at least
`(1 - C⁻²)` of the complete conditional mass.  This is an exact finite theorem, not an
asymptotic local-limit assertion. -/
theorem one_sub_inv_windowConstant_sq_mul_totalMass_le_windowMass
    (d : RouteEEntropyComplementWindowData) :
    (1 - 1 / d.windowConstant ^ 2) * d.totalMass ^ d.totalBreadth ≤
      d.windowMass := by
  let tailMass : ℝ :=
    ∑ b ∈ Finset.range (d.totalBreadth + 1) with
      b ∉ d.window,
      routeEConditionalBreadthWeight
        d.lowMass d.roughMass d.totalBreadth b
  have htailNonneg : 0 ≤ tailMass := by
    exact Finset.sum_nonneg fun b hb => d.conditionalBreadthWeight_nonneg b
  have hvariance := d.aperture_sq_mul_tailMass_le_variance
  rw [routeEConditionalBreadthCenteredVariance_eq] at hvariance
  have htotalNonneg : 0 ≤ d.totalMass := d.totalMass_pos.le
  have hcentralScaled :
      (d.totalBreadth : ℝ) * d.lowMass * d.roughMass *
          d.totalMass ^ d.totalBreadth ≤
        d.totalMass ^ 2 * d.roughMass *
          d.totalMass ^ d.totalBreadth := by
    have hfactor : 0 ≤ d.roughMass * d.totalMass ^ d.totalBreadth := by positivity
    exact mul_le_mul_of_nonneg_right d.central_balance hfactor
  have hapertureSq :
      d.aperture ^ 2 =
        d.windowConstant ^ 2 * d.totalMass ^ 2 * d.roughMass := by
    unfold aperture
    rw [Real.sq_sqrt d.roughMass_pos.le]
    ring
  have hscaled :
      d.windowConstant ^ 2 * d.totalMass ^ 2 * d.roughMass * tailMass ≤
        d.totalMass ^ 2 * d.roughMass * d.totalMass ^ d.totalBreadth := by
    rw [← hapertureSq]
    exact hvariance.trans hcentralScaled
  have hcancelPos : 0 < d.totalMass ^ 2 * d.roughMass := by positivity
  have hcancel : d.windowConstant ^ 2 * tailMass ≤
      d.totalMass ^ d.totalBreadth := by
    apply (mul_le_mul_left hcancelPos).mp
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hC2 : 0 < d.windowConstant ^ 2 := sq_pos_of_pos d.windowConstant_pos
  have htail : tailMass ≤ d.totalMass ^ d.totalBreadth / d.windowConstant ^ 2 := by
    exact (le_div_iff₀ hC2).2 hcancel
  have hsplit :
      d.windowMass + tailMass = d.totalMass ^ d.totalBreadth := by
    have hpartition := Finset.sum_filter_add_sum_filter_not
      (Finset.range (d.totalBreadth + 1))
      (fun b => b ∈ d.window)
      (fun b => routeEConditionalBreadthWeight
        d.lowMass d.roughMass d.totalBreadth b)
    have hinside :
        (∑ b ∈ Finset.range (d.totalBreadth + 1) with b ∈ d.window,
          routeEConditionalBreadthWeight
            d.lowMass d.roughMass d.totalBreadth b) = d.windowMass := by
      rw [windowMass]
      apply Finset.sum_subset
      · intro b hb
        exact (Finset.mem_filter.mp hb).1
      · intro b hbRange hbNotWindow
        simp [hbNotWindow]
    rw [hinside] at hpartition
    change d.windowMass + tailMass = _
    rw [hpartition, ← routeEConditionalBreadthMass]
    exact routeEConditionalBreadthMass_eq
      d.lowMass d.roughMass d.totalBreadth
  have hmain :
      d.totalMass ^ d.totalBreadth -
          d.totalMass ^ d.totalBreadth / d.windowConstant ^ 2 ≤
        d.windowMass := by
    linarith
  calc
    (1 - 1 / d.windowConstant ^ 2) * d.totalMass ^ d.totalBreadth =
        d.totalMass ^ d.totalBreadth -
          d.totalMass ^ d.totalBreadth / d.windowConstant ^ 2 := by ring
    _ ≤ d.windowMass := hmain

end RouteEEntropyComplementWindowData

/-! ## Corrected fixed-breadth load threshold -/

/-- Positive finite data for the sharp Route E load-scale calculation.  `logScale` represents
`log X`; no asymptotic notation is used. -/
structure RouteELoadScaleData where
  growth : ℝ
  breadthScale : ℝ
  logScale : ℝ
  tokenDensity : ℝ
  growth_pos : 0 < growth
  breadthScale_pos : 0 < breadthScale
  logScale_pos : 0 < logScale
  tokenDensity_pos : 0 < tokenDensity

namespace RouteELoadScaleData

/-- Product-truncated central reservoir scale `log X / (g L^(3/2))`. -/
def reservoirScale (d : RouteELoadScaleData) : ℝ :=
  d.logScale / (d.growth * d.breadthScale * Real.sqrt d.breadthScale)

/-- Natural incoming central breadth-layer density `L^(-1/2)`. -/
def incomingScale (d : RouteELoadScaleData) : ℝ :=
  1 / Real.sqrt d.breadthScale

/-- Column-load scale after square-root physical Jacobian cancellation. -/
def columnLoadScale (d : RouteELoadScaleData) : ℝ :=
  d.incomingScale / (d.reservoirScale * d.tokenDensity)

/-- Correct exact load formula `g L / (delta log X)`. -/
theorem columnLoadScale_eq (d : RouteELoadScaleData) :
    d.columnLoadScale =
      d.growth * d.breadthScale / (d.tokenDensity * d.logScale) := by
  have hsqrt : Real.sqrt d.breadthScale ≠ 0 :=
    (Real.sqrt_pos.2 d.breadthScale_pos).ne'
  have hg : d.growth ≠ 0 := d.growth_pos.ne'
  have hL : d.breadthScale ≠ 0 := d.breadthScale_pos.ne'
  have hlog : d.logScale ≠ 0 := d.logScale_pos.ne'
  have hdelta : d.tokenDensity ≠ 0 := d.tokenDensity_pos.ne'
  unfold columnLoadScale incomingScale reservoirScale
  field_simp [hsqrt, hg, hL, hlog, hdelta]

/-- **Sharp fixed-breadth threshold.**  Unit load is equivalent to
`delta >= g L / log X`; the formerly claimed `1 / log X` threshold is absent. -/
theorem columnLoadScale_le_one_iff (d : RouteELoadScaleData) :
    d.columnLoadScale ≤ 1 ↔
      d.growth * d.breadthScale / d.logScale ≤ d.tokenDensity := by
  rw [d.columnLoadScale_eq]
  constructor
  · intro h
    have hmul := (div_le_iff₀ (mul_pos d.tokenDensity_pos d.logScale_pos)).mp h
    apply (div_le_iff₀ d.logScale_pos).2
    nlinarith
  · intro h
    apply (div_le_iff₀ (mul_pos d.tokenDensity_pos d.logScale_pos)).2
    have hmul := (div_le_iff₀ d.logScale_pos).mp h
    nlinarith

end RouteELoadScaleData

/-! ## Product schedule and source-prime deletion -/

/-- Positive cofinal schedule for the entropy-complement cutoff `P = X^(1/(gL))`. -/
structure RouteEEntropyComplementSchedule where
  X : ℝ
  growth : ℝ
  breadthScale : ℝ
  one_le_X : 1 ≤ X
  growth_pos : 0 < growth
  breadthScale_pos : 0 < breadthScale

namespace RouteEEntropyComplementSchedule

/-- Source-predeclared low/rough prime cutoff. -/
def primeCutoff (d : RouteEEntropyComplementSchedule) : ℝ :=
  d.X ^ (1 / (d.growth * d.breadthScale))

theorem primeCutoff_pos (d : RouteEEntropyComplementSchedule) : 0 < d.primeCutoff := by
  unfold primeCutoff
  exact Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one d.one_le_X) _

end RouteEEntropyComplementSchedule

/-- One breadth branch in the central window `b <= 2L`. -/
structure RouteEEntropyComplementBranch where
  schedule : RouteEEntropyComplementSchedule
  breadth : ℕ
  breadth_le_two_scale :
    (breadth : ℝ) ≤ 2 * schedule.breadthScale

namespace RouteEEntropyComplementBranch

/-- Exact subpower reservoir-product envelope `(X^(1/(gL)))^b <= X^(2/g)`. -/
theorem primeCutoff_pow_breadth_le (d : RouteEEntropyComplementBranch) :
    d.schedule.primeCutoff ^ d.breadth ≤
      d.schedule.X ^ (2 / d.schedule.growth) := by
  have hX0 : 0 ≤ d.schedule.X :=
    le_trans zero_le_one d.schedule.one_le_X
  have hcoef : 0 ≤ 1 / (d.schedule.growth * d.schedule.breadthScale) := by positivity
  have hexp :
      1 / (d.schedule.growth * d.schedule.breadthScale) * (d.breadth : ℝ) ≤
        2 / d.schedule.growth := by
    have hmul := mul_le_mul_of_nonneg_left d.breadth_le_two_scale hcoef
    have hg : d.schedule.growth ≠ 0 := d.schedule.growth_pos.ne'
    have hL : d.schedule.breadthScale ≠ 0 := d.schedule.breadthScale_pos.ne'
    have heq :
        1 / (d.schedule.growth * d.schedule.breadthScale) *
            (2 * d.schedule.breadthScale) = 2 / d.schedule.growth := by
      field_simp [hg, hL]
    linarith
  calc
    d.schedule.primeCutoff ^ d.breadth =
        d.schedule.X ^
          (1 / (d.schedule.growth * d.schedule.breadthScale) *
            (d.breadth : ℝ)) := by
      unfold RouteEEntropyComplementSchedule.primeCutoff
      exact (Real.rpow_mul_natCast hX0 _ _).symm
    _ ≤ d.schedule.X ^ (2 / d.schedule.growth) :=
      Real.rpow_le_rpow_of_exponent_le d.schedule.one_le_X hexp

end RouteEEntropyComplementBranch

/-- Source primes above the rough cutoff, with central breadth already certified. -/
structure RouteESourcePrimeDeletionData where
  cutoff : ℝ
  breadthScale : ℝ
  sourcePrimes : Finset ℕ
  cutoff_pos : 0 < cutoff
  breadthScale_nonneg : 0 ≤ breadthScale
  above_cutoff : ∀ p ∈ sourcePrimes, cutoff ≤ (p : ℝ)
  central_card : (sourcePrimes.card : ℝ) ≤ 2 * breadthScale

namespace RouteESourcePrimeDeletionData

/-- **Exact source-deletion law.**  At most `2L` excluded primes above `P` remove harmonic mass
at most `2L/P`. -/
theorem harmonicMass_le_two_scale_div_cutoff (d : RouteESourcePrimeDeletionData) :
    (∑ p ∈ d.sourcePrimes, 1 / (p : ℝ)) ≤
      2 * d.breadthScale / d.cutoff := by
  calc
    (∑ p ∈ d.sourcePrimes, 1 / (p : ℝ)) ≤
        ∑ _p ∈ d.sourcePrimes, 1 / d.cutoff := by
      apply Finset.sum_le_sum
      intro p hp
      exact one_div_le_one_div_of_le d.cutoff_pos (d.above_cutoff p hp)
    _ = (d.sourcePrimes.card : ℝ) / d.cutoff := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    _ ≤ 2 * d.breadthScale / d.cutoff := by
      exact div_le_div_of_nonneg_right d.central_card d.cutoff_pos.le

end RouteESourcePrimeDeletionData

/-! ## Exact adjacent-grade parity -/

/-- One upward entropy-complement branch with exact terminal breadth `s+1`. -/
structure RouteEEntropyComplementUpwardBranch where
  sourceBreadth : ℕ
  reservoirBreadth : ℕ
  tokenBreadth : ℕ
  exact_grade : reservoirBreadth + tokenBreadth = sourceBreadth + 1

/-- One downward entropy-complement branch with exact terminal breadth `s-1`. -/
structure RouteEEntropyComplementDownwardBranch where
  sourceBreadth : ℕ
  reservoirBreadth : ℕ
  tokenBreadth : ℕ
  exact_grade : sourceBreadth = reservoirBreadth + tokenBreadth + 1

/-- Every upward branch reverses the squarefree Möbius parity sign. -/
theorem RouteEEntropyComplementUpwardBranch.parity_reversal
    (d : RouteEEntropyComplementUpwardBranch) :
    (-1 : ℤ) ^ (d.reservoirBreadth + d.tokenBreadth) =
      -((-1 : ℤ) ^ d.sourceBreadth) := by
  rw [d.exact_grade, pow_succ]
  ring

/-- Every downward branch reverses the squarefree Möbius parity sign. -/
theorem RouteEEntropyComplementDownwardBranch.parity_reversal
    (d : RouteEEntropyComplementDownwardBranch) :
    (-1 : ℤ) ^ (d.reservoirBreadth + d.tokenBreadth) =
      -((-1 : ℤ) ^ d.sourceBreadth) := by
  rw [d.exact_grade, pow_succ]
  ring

/-! ## Finite Hellinger/chi-square endpoint consumer -/

/-- A finite live column law.  Strict positivity of target columns is exactly the support
condition needed by the weighted chi-square expression. -/
structure RouteEFiniteColumnData (ι : Type*) [Fintype ι] where
  pushedMass : ι → ℝ
  targetMass : ι → ℝ
  pushedMass_nonneg : ∀ i, 0 ≤ pushedMass i
  targetMass_pos : ∀ i, 0 < targetMass i

namespace RouteEFiniteColumnData

variable {ι : Type*} [Fintype ι]

def pushedTotal (d : RouteEFiniteColumnData ι) : ℝ :=
  ∑ i, d.pushedMass i

def targetTotal (d : RouteEFiniteColumnData ι) : ℝ :=
  ∑ i, d.targetMass i

def matchedTotal (d : RouteEFiniteColumnData ι) : ℝ :=
  d.pushedTotal + d.targetTotal

def hellingerSq (d : RouteEFiniteColumnData ι) : ℝ :=
  ∑ i, (Real.sqrt (d.pushedMass i) - Real.sqrt (d.targetMass i)) ^ 2

def chiSquare (d : RouteEFiniteColumnData ι) : ℝ :=
  ∑ i, (d.pushedMass i - d.targetMass i) ^ 2 / d.targetMass i

theorem pushedTotal_nonneg (d : RouteEFiniteColumnData ι) : 0 ≤ d.pushedTotal := by
  exact Finset.sum_nonneg fun i hi => d.pushedMass_nonneg i

theorem targetTotal_nonneg (d : RouteEFiniteColumnData ι) : 0 ≤ d.targetTotal := by
  exact Finset.sum_nonneg fun i hi => (d.targetMass_pos i).le

theorem matchedTotal_nonneg (d : RouteEFiniteColumnData ι) : 0 ≤ d.matchedTotal := by
  exact add_nonneg d.pushedTotal_nonneg d.targetTotal_nonneg

theorem hellingerSq_nonneg (d : RouteEFiniteColumnData ι) : 0 ≤ d.hellingerSq := by
  exact Finset.sum_nonneg fun i hi => sq_nonneg _

theorem chiSquare_nonneg (d : RouteEFiniteColumnData ι) : 0 ≤ d.chiSquare := by
  exact Finset.sum_nonneg fun i hi =>
    div_nonneg (sq_nonneg _) (d.targetMass_pos i).le

private theorem massDifference_eq_sqrtFactorization
    (d : RouteEFiniteColumnData ι) :
    d.pushedTotal - d.targetTotal =
      ∑ i,
        (Real.sqrt (d.pushedMass i) - Real.sqrt (d.targetMass i)) *
          (Real.sqrt (d.pushedMass i) + Real.sqrt (d.targetMass i)) := by
  rw [pushedTotal, targetTotal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [sub_mul, mul_add, mul_add]
  rw [Real.sq_sqrt (d.pushedMass_nonneg i),
    Real.sq_sqrt (d.targetMass_pos i).le]
  ring

private theorem sqrtSumSq_le_two_matchedTotal
    (d : RouteEFiniteColumnData ι) :
    (∑ i, (Real.sqrt (d.pushedMass i) + Real.sqrt (d.targetMass i)) ^ 2) ≤
      2 * d.matchedTotal := by
  rw [matchedTotal, pushedTotal, targetTotal, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hp := Real.sqrt_nonneg (d.pushedMass i)
  have hn := Real.sqrt_nonneg (d.targetMass i)
  have hpsq := Real.sq_sqrt (d.pushedMass_nonneg i)
  have hnsq := Real.sq_sqrt (d.targetMass_pos i).le
  nlinarith [sq_nonneg
    (Real.sqrt (d.pushedMass i) - Real.sqrt (d.targetMass i))]

/-- **Finite Hellinger endpoint law.** -/
theorem massDifference_sq_le_two_matchedTotal_mul_hellingerSq
    (d : RouteEFiniteColumnData ι) :
    (d.pushedTotal - d.targetTotal) ^ 2 ≤
      2 * d.matchedTotal * d.hellingerSq := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset ι)
    (fun i => Real.sqrt (d.pushedMass i) - Real.sqrt (d.targetMass i))
    (fun i => Real.sqrt (d.pushedMass i) + Real.sqrt (d.targetMass i))
  rw [d.massDifference_eq_sqrtFactorization]
  calc
    (∑ i,
        (Real.sqrt (d.pushedMass i) - Real.sqrt (d.targetMass i)) *
          (Real.sqrt (d.pushedMass i) + Real.sqrt (d.targetMass i))) ^ 2 ≤
        d.hellingerSq *
          ∑ i, (Real.sqrt (d.pushedMass i) + Real.sqrt (d.targetMass i)) ^ 2 := by
            simpa [hellingerSq] using hcs
    _ ≤ d.hellingerSq * (2 * d.matchedTotal) :=
      mul_le_mul_of_nonneg_left d.sqrtSumSq_le_two_matchedTotal d.hellingerSq_nonneg
    _ = 2 * d.matchedTotal * d.hellingerSq := by ring

private theorem pointwise_hellingerSq_le_chiSquare
    (d : RouteEFiniteColumnData ι) (i : ι) :
    (Real.sqrt (d.pushedMass i) - Real.sqrt (d.targetMass i)) ^ 2 ≤
      (d.pushedMass i - d.targetMass i) ^ 2 / d.targetMass i := by
  let a := Real.sqrt (d.pushedMass i) - Real.sqrt (d.targetMass i)
  let b := Real.sqrt (d.pushedMass i) + Real.sqrt (d.targetMass i)
  have hnu : 0 < d.targetMass i := d.targetMass_pos i
  have hsqrtNu : 0 ≤ Real.sqrt (d.targetMass i) := Real.sqrt_nonneg _
  have hsqrtRho : 0 ≤ Real.sqrt (d.pushedMass i) := Real.sqrt_nonneg _
  have hnuSq := Real.sq_sqrt hnu.le
  have hrhoSq := Real.sq_sqrt (d.pushedMass_nonneg i)
  have hfactor :
      (d.pushedMass i - d.targetMass i) ^ 2 = a ^ 2 * b ^ 2 := by
    unfold a b
    nlinarith
  have hb : d.targetMass i ≤ b ^ 2 := by
    unfold b
    nlinarith
  calc
    a ^ 2 = a ^ 2 * d.targetMass i / d.targetMass i := by
      field_simp [hnu.ne']
    _ ≤ a ^ 2 * b ^ 2 / d.targetMass i := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hb (sq_nonneg a)) hnu.le
    _ = (d.pushedMass i - d.targetMass i) ^ 2 / d.targetMass i := by
      rw [hfactor]

/-- Hellinger square is dominated by target-weighted column chi-square. -/
theorem hellingerSq_le_chiSquare (d : RouteEFiniteColumnData ι) :
    d.hellingerSq ≤ d.chiSquare := by
  unfold hellingerSq chiSquare
  exact Finset.sum_le_sum fun i hi => d.pointwise_hellingerSq_le_chiSquare i

/-- Absolute matched-mass discrepancy controlled directly by chi-square. -/
theorem abs_massDifference_le_sqrt_two_matchedTotal_mul_chiSquare
    (d : RouteEFiniteColumnData ι) :
    |d.pushedTotal - d.targetTotal| ≤
      Real.sqrt (2 * d.matchedTotal * d.chiSquare) := by
  have hsquare :
      (d.pushedTotal - d.targetTotal) ^ 2 ≤
        2 * d.matchedTotal * d.chiSquare := by
    exact d.massDifference_sq_le_two_matchedTotal_mul_hellingerSq.trans
      (mul_le_mul_of_nonneg_left d.hellingerSq_le_chiSquare
        (mul_nonneg (by positivity) d.matchedTotal_nonneg))
  have hrad : 0 ≤ 2 * d.matchedTotal * d.chiSquare := by positivity
  have hsqrt := Real.sqrt_nonneg (2 * d.matchedTotal * d.chiSquare)
  have hsqrtSq := Real.sq_sqrt hrad
  have habsSq : |d.pushedTotal - d.targetTotal| ^ 2 =
      (d.pushedTotal - d.targetTotal) ^ 2 := sq_abs _
  nlinarith [abs_nonneg (d.pushedTotal - d.targetTotal)]

end RouteEFiniteColumnData

/-- Matched live columns together with positive and negative unmatched deficits. -/
structure RouteEFiniteMatchedColumnData (ι : Type*) [Fintype ι]
    extends RouteEFiniteColumnData ι where
  unmatchedPositive : ℝ
  unmatchedNegative : ℝ
  unmatchedPositive_nonneg : 0 ≤ unmatchedPositive
  unmatchedNegative_nonneg : 0 ≤ unmatchedNegative

namespace RouteEFiniteMatchedColumnData

variable {ι : Type*} [Fintype ι]

def unmatchedMass (d : RouteEFiniteMatchedColumnData ι) : ℝ :=
  d.unmatchedPositive + d.unmatchedNegative

def totalPositive (d : RouteEFiniteMatchedColumnData ι) : ℝ :=
  d.toRouteEFiniteColumnData.pushedTotal + d.unmatchedPositive

def totalNegative (d : RouteEFiniteMatchedColumnData ι) : ℝ :=
  d.toRouteEFiniteColumnData.targetTotal + d.unmatchedNegative

/-- **Hybrid Hellinger/chi-square endpoint consumer.**  Unmatched mass enters linearly; all matched
column imbalance enters only through global weighted chi-square. -/
theorem abs_totalDifference_le_unmatched_add_sqrt_chiSquare
    (d : RouteEFiniteMatchedColumnData ι) :
    |d.totalPositive - d.totalNegative| ≤
      d.unmatchedMass +
        Real.sqrt
          (2 * d.toRouteEFiniteColumnData.matchedTotal *
            d.toRouteEFiniteColumnData.chiSquare) := by
  have hmatched :=
    d.toRouteEFiniteColumnData.abs_massDifference_le_sqrt_two_matchedTotal_mul_chiSquare
  have hunmatched :
      |d.unmatchedPositive - d.unmatchedNegative| ≤ d.unmatchedMass := by
    rw [unmatchedMass, abs_sub_le_iff]
    constructor <;> linarith [d.unmatchedPositive_nonneg, d.unmatchedNegative_nonneg]
  have htriangle :
      |d.totalPositive - d.totalNegative| ≤
        |d.toRouteEFiniteColumnData.pushedTotal -
            d.toRouteEFiniteColumnData.targetTotal| +
          |d.unmatchedPositive - d.unmatchedNegative| := by
    unfold totalPositive totalNegative
    convert abs_add
      (d.toRouteEFiniteColumnData.pushedTotal -
        d.toRouteEFiniteColumnData.targetTotal)
      (d.unmatchedPositive - d.unmatchedNegative) using 1 <;> ring
  calc
    |d.totalPositive - d.totalNegative| ≤
        |d.toRouteEFiniteColumnData.pushedTotal -
            d.toRouteEFiniteColumnData.targetTotal| +
          |d.unmatchedPositive - d.unmatchedNegative| := htriangle
    _ ≤ Real.sqrt
          (2 * d.toRouteEFiniteColumnData.matchedTotal *
            d.toRouteEFiniteColumnData.chiSquare) + d.unmatchedMass :=
      add_le_add hmatched hunmatched
    _ = d.unmatchedMass +
        Real.sqrt
          (2 * d.toRouteEFiniteColumnData.matchedTotal *
            d.toRouteEFiniteColumnData.chiSquare) := by ring

end RouteEFiniteMatchedColumnData

end

end RHTower
