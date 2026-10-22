import GaloisForLFunctions.RHTower.CCM.CCMSharpPrimeWindowSubpowerGate
import GaloisForLFunctions.RHTower.CCM.CCMRectangularNegativePartSquareEnergyGate
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Positive-excess Dirichlet energy of the dyadic sharp prime window

The pointwise sharp-window inequality is stronger than the Landau mechanism needs.  Write

`E(n) = (W(n) - 2 * (1 - 1 / sqrt 2) * sqrt n)⁺`.

The negative part of the exact sharp source coefficient is literally `2 * E(n)`.  It is therefore
enough that the positive excess have an absolutely convergent Dirichlet series at every real
abscissa `1 + epsilon`.  Adding this negative part makes the sharp source coefficients
nonnegative; Landau transfer then detects every hypothetical positive-transverse Xi zero.

The final section gives a still more Hilbert-facing sufficient condition: weighted square energy
of `E(n)` at every exponent `1 + epsilon`.
-/

open Complex Filter Function Set LSeries

noncomputable section

namespace RHTower

/-- Positive excess of the dyadic weighted prime window above its exact square-root main term. -/
def dyadicWeightedPrimeWindowPositiveExcess (n : ℕ) : ℝ :=
  (dyadicWeightedPrimeWindow n -
    2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n)⁺

theorem dyadicWeightedPrimeWindowPositiveExcess_nonneg (n : ℕ) :
    0 ≤ dyadicWeightedPrimeWindowPositiveExcess n :=
  posPart_nonneg _

theorem dyadicWeightedPrimeWindow_nonneg (n : ℕ) :
    0 ≤ dyadicWeightedPrimeWindow n := by
  rw [dyadicWeightedPrimeWindow]
  exact Finset.sum_nonneg fun k _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k)

/-- Unconditional Chebyshev constant for the square-root envelope of the sharp window. -/
def dyadicSharpPrimeWindowHalfPowerBound : ℝ :=
  Real.sqrt 2 * (Real.log 4 + 4)

theorem dyadicSharpPrimeWindowHalfPowerBound_nonneg :
    0 ≤ dyadicSharpPrimeWindowHalfPowerBound := by
  rw [dyadicSharpPrimeWindowHalfPowerBound]
  positivity

/-- The dyadic sharp prime window has an unconditional square-root envelope. -/
theorem dyadicWeightedPrimeWindow_le_halfPower
    {n : ℕ} (hn : 0 < n) :
    dyadicWeightedPrimeWindow n ≤
      dyadicSharpPrimeWindowHalfPowerBound * Real.sqrt n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnR
  have hfactor : 0 ≤ Real.sqrt 2 / Real.sqrt n := by positivity
  rw [dyadicWeightedPrimeWindow, dyadicSharpPrimeWindowHalfPowerBound]
  calc
    (∑ k ∈ Finset.Ioc (n / 2) n,
        ArithmeticFunction.vonMangoldt k / Real.sqrt k) ≤
        ∑ k ∈ Finset.Ioc (n / 2) n,
          (Real.sqrt 2 / Real.sqrt n) * ArithmeticFunction.vonMangoldt k := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := by
        have := (Finset.mem_Ioc.mp hk).1
        omega
      have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
      have hsqrtk : 0 < Real.sqrt k := Real.sqrt_pos.mpr hkR
      have hnk : n ≤ 2 * k := by
        have := (Finset.mem_Ioc.mp hk).1
        omega
      have hsqrt : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt k := by
        rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
        exact Real.sqrt_le_sqrt (by exact_mod_cast hnk)
      have hinv : 1 / Real.sqrt k ≤ Real.sqrt 2 / Real.sqrt n := by
        rw [div_le_div_iff₀ hsqrtk hsqrtn]
        simpa only [one_mul] using hsqrt
      rw [div_eq_mul_inv]
      simpa only [one_div, mul_comm] using
        mul_le_mul_of_nonneg_right hinv
          (ArithmeticFunction.vonMangoldt_nonneg (n := k))
    _ = (Real.sqrt 2 / Real.sqrt n) *
        ∑ k ∈ Finset.Ioc (n / 2) n,
          ArithmeticFunction.vonMangoldt k := by
      rw [Finset.mul_sum]
    _ ≤ (Real.sqrt 2 / Real.sqrt n) *
        ∑ k ∈ Finset.Icc 1 n,
          ArithmeticFunction.vonMangoldt k := by
      apply mul_le_mul_of_nonneg_left _ hfactor
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro k hk
        rw [Finset.mem_Ioc] at hk
        rw [Finset.mem_Icc]
        constructor <;> omega
      · intro k hk hnot
        exact ArithmeticFunction.vonMangoldt_nonneg
    _ ≤ (Real.sqrt 2 / Real.sqrt n) *
        ((Real.log 4 + 4) * n) := by
      exact mul_le_mul_of_nonneg_left
        (Mertens.sum_vonMangoldt_Icc_le n) hfactor
    _ = Real.sqrt 2 * (Real.log 4 + 4) * Real.sqrt n := by
      have hnSq : Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ) = n := by
        nlinarith [Real.sq_sqrt hnR.le]
      have hprod : (Real.log 4 + 4) * (n : ℝ) =
          (Real.log 4 + 4) * (Real.sqrt n * Real.sqrt n) := by
        rw [hnSq]
      rw [hprod]
      calc
        (Real.sqrt 2 / Real.sqrt n) *
            ((Real.log 4 + 4) * (Real.sqrt n * Real.sqrt n)) =
            Real.sqrt 2 * (Real.log 4 + 4) *
              ((Real.sqrt n)⁻¹ * Real.sqrt n) * Real.sqrt n := by
          rw [div_eq_mul_inv]
          ring
        _ = _ := by rw [inv_mul_cancel₀ hsqrtn.ne', mul_one]

/-- The same unconditional square-root envelope controls the positive excess alone. -/
theorem dyadicWeightedPrimeWindowPositiveExcess_le_halfPower (n : ℕ) :
    dyadicWeightedPrimeWindowPositiveExcess n ≤
      dyadicSharpPrimeWindowHalfPowerBound *
        powerCorrectionCoefficient (1 / 2 : ℝ) n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · norm_num [dyadicWeightedPrimeWindowPositiveExcess,
      dyadicWeightedPrimeWindow, powerCorrectionCoefficient]
  · have hsqrtTwo : 1 ≤ Real.sqrt 2 :=
      Real.one_le_sqrt.mpr (by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hsqrtTwo
    have hmain : 0 ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n :=
      mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr hinv))
        (Real.sqrt_nonneg n)
    have hexcessWindow : dyadicWeightedPrimeWindowPositiveExcess n ≤
        dyadicWeightedPrimeWindow n := by
      rw [dyadicWeightedPrimeWindowPositiveExcess, posPart_def]
      exact max_le (by linarith) (dyadicWeightedPrimeWindow_nonneg n)
    rw [powerCorrectionCoefficient, if_neg (Nat.ne_of_gt hn)]
    rw [show (n : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt n by
      symm
      exact Real.sqrt_eq_rpow (n : ℝ)]
    exact hexcessWindow.trans (dyadicWeightedPrimeWindow_le_halfPower hn)

/-- Negative part of the exact sharp source coefficient. -/
def dyadicSharpPrimeSourceNegativePart (n : ℕ) : ℝ :=
  (dyadicSharpPrimeSourceCoefficient n)⁻

theorem dyadicSharpPrimeSourceNegativePart_nonneg (n : ℕ) :
    0 ≤ dyadicSharpPrimeSourceNegativePart n :=
  negPart_nonneg _

/-- **Exact excess relation.**  The source defect is twice the positive excess in the requested
prime-window inequality. -/
theorem dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess (n : ℕ) :
    dyadicSharpPrimeSourceNegativePart n =
      2 * dyadicWeightedPrimeWindowPositiveExcess n := by
  rw [dyadicSharpPrimeSourceNegativePart,
    dyadicWeightedPrimeWindowPositiveExcess,
    dyadicSharpPrimeSourceCoefficient]
  simp only [negPart_def, posPart_def]
  rw [show -(4 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n -
      2 * dyadicWeightedPrimeWindow n) =
      2 * (dyadicWeightedPrimeWindow n -
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n) by ring]
  conv_lhs => rw [show (0 : ℝ) = 2 * 0 by norm_num]
  rw [← mul_max_of_nonneg
    (dyadicWeightedPrimeWindow n -
      2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n) 0
    (by norm_num : (0 : ℝ) ≤ 2)]

/-- At an integer logarithmic sample, the Dirichlet source coefficient is the actual sharp
prime--polar value. -/
theorem dyadicSharpPrimeSourceCoefficient_eq_sharpPrimePolar_logSample
    {n : ℕ} (hn : 0 < n) :
    dyadicSharpPrimeSourceCoefficient n =
      sharpPrimePolarCoefficient (Real.log 2) (Real.log n) := by
  rw [sharpPrimePolarCoefficient_logTwo_logSample hn,
    ← dyadicWeightedPrimeWindow_eq_floorSum,
    dyadicSharpPrimeSourceCoefficient]

/-- **Polar-free excess relation.**  The positive excess in the prime-window inequality is half
the negative part of one normalized-Chebyshev increment.  No separate polar estimate remains. -/
theorem negPart_sharpPrimeNormalizedChebyshevIncrement_eq_two_mul_positiveExcess
    {n : ℕ} (hn : 2 ≤ n) :
    (sharpPrimeNormalizedChebyshevIncrement
      (Real.log 2) (Real.log n))⁻ =
      2 * dyadicWeightedPrimeWindowPositiveExcess n := by
  have hnpos : 0 < n := by omega
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  rw [← sharpPrimePolarCoefficient_eq_normalizedChebyshevIncrement
      (Real.log_nonneg (by norm_num)) hlog,
    ← dyadicSharpPrimeSourceCoefficient_eq_sharpPrimePolar_logSample hnpos]
  change dyadicSharpPrimeSourceNegativePart n =
    2 * dyadicWeightedPrimeWindowPositiveExcess n
  exact dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess n

/-- Adding the negative part replaces the sharp source coefficient by its positive part. -/
def dyadicSharpNegativePartLandauCoefficient (n : ℕ) : ℝ :=
  dyadicSharpPrimeSourceCoefficient n +
    dyadicSharpPrimeSourceNegativePart n

theorem dyadicSharpNegativePartLandauCoefficient_nonneg :
    ∀ n, 0 ≤ dyadicSharpNegativePartLandauCoefficient n := by
  intro n
  have hpos := posPart_nonneg (dyadicSharpPrimeSourceCoefficient n)
  have hdecomp := posPart_sub_negPart
    (dyadicSharpPrimeSourceCoefficient n)
  dsimp only [dyadicSharpNegativePartLandauCoefficient,
    dyadicSharpPrimeSourceNegativePart]
  linarith

/-- Dirichlet-energy hypothesis on only the negative part of the exact sharp source. -/
def DyadicSharpPrimeSourceNegativePartEnergy : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

/-- Meromorphic continuation of the nonnegative corrected sharp coefficient series. -/
def dyadicSharpNegativePartLandauContinuation (s : ℂ) : ℂ :=
  dyadicSharpPrimeContinuedSource s +
    LSeries
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) s

theorem dyadicSharpNegativePartLandauCoefficient_LSeriesSummable
    {s : ℂ} (hssharp : 3 / 2 < s.re)
    (hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) s) :
    LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) s := by
  have hsharp := dyadicSharpPrimeSourceCoefficient_LSeriesSummable hssharp
  have hadd : LSeriesSummable
      ((fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) +
        (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))) s :=
    hsharp.add hcorr
  change Summable (LSeries.term
    (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) s)
  change Summable (LSeries.term _ s) at hadd
  exact hadd.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.add_apply, dyadicSharpNegativePartLandauCoefficient,
        ofReal_add]

theorem LSeries_dyadicSharpNegativePartLandauCoefficient_eq_continuation
    {s : ℂ} (hssharp : 3 / 2 < s.re)
    (hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) s) :
    LSeries
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) s =
      dyadicSharpNegativePartLandauContinuation s := by
  have hsharp := dyadicSharpPrimeSourceCoefficient_LSeriesSummable hssharp
  calc
    LSeries
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) s =
        LSeries
          ((fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) +
            (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))) s := by
      apply LSeries_congr
      intro n hn
      simp only [Pi.add_apply, dyadicSharpNegativePartLandauCoefficient,
        ofReal_add]
    _ = LSeries
          (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ)) s +
        LSeries
          (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) s :=
      LSeries_add hsharp hcorr
    _ = dyadicSharpNegativePartLandauContinuation s := by
      rw [LSeries_dyadicSharpPrimeSourceCoefficient_eq_continuedSource hssharp]
      rfl

/-- The corrected continuation is holomorphic to the right of an upper bound for all
positive-transverse Xi zeros. -/
theorem differentiableOn_dyadicSharpNegativePartLandauContinuation_rightOf
    (beta delta : ℝ) (hdelta : 0 < delta)
    (hbetaDelta : beta < delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    (hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + beta : ℝ) : ℂ))) :
    DifferentiableOn ℂ dyadicSharpNegativePartLandauContinuation
      {s : ℂ | 1 + delta < s.re} := by
  have hsourcePower :=
    differentiableOn_dyadicSharpPowerLandauContinuation_rightOf
      0 0 delta hdelta.le hdelta hupper
  have hsourceEq : dyadicSharpPowerLandauContinuation 0 0 =
      dyadicSharpPrimeContinuedSource := by
    funext z
    rw [dyadicSharpPowerLandauContinuation]
    norm_num
  rw [hsourceEq] at hsourcePower
  intro s hs
  have hsource : DifferentiableWithinAt ℂ dyadicSharpPrimeContinuedSource
      {s : ℂ | 1 + delta < s.re} s := by
    exact hsourcePower s hs
  have habsc : abscissaOfAbsConv
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) ≤
      ((1 + beta : ℝ) : EReal) := hcorr.abscissaOfAbsConv_le
  have hre : 1 + beta < s.re := by
    change 1 + delta < s.re at hs
    linarith
  have habslt : abscissaOfAbsConv
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) <
      (s.re : EReal) := by
    refine habsc.trans_lt ?_
    exact_mod_cast hre
  have hcorrDiff : DifferentiableAt ℂ
      (LSeries
        (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))) s :=
    (LSeries_hasDerivAt habslt).differentiableAt
  change DifferentiableWithinAt ℂ
    (dyadicSharpPrimeContinuedSource +
      LSeries (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)))
    {s : ℂ | 1 + delta < s.re} s
  exact hsource.add hcorrDiff.differentiableWithinAt

/-- A narrow real-centered Landau ball misses every Xi zero, while the correction series stays
inside its half-plane of convergence. -/
theorem differentiableOn_dyadicSharpNegativePartLandauContinuation_landauBall
    (beta : ℝ) {delta eta r : ℝ}
    (hdelta0 : 0 ≤ delta) (hr : 0 < r)
    (hrquarter : r ≤ 1 / 4) (hreta : r ≤ eta / 2)
    (hbeta : beta + r < delta)
    (hordinate : ∀ ρ : XiDivisorSupport, eta ≤ |(ρ : ℂ).im|)
    (hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + beta : ℝ) : ℂ))) :
    DifferentiableOn ℂ dyadicSharpNegativePartLandauContinuation
      (Metric.ball (((1 + delta : ℝ) : ℂ)) r) := by
  have hsourcePower :=
    differentiableOn_dyadicSharpPowerLandauContinuation_landauBall
      0 beta hdelta0 hr hrquarter hreta hbeta hordinate
  have hsourceEq : dyadicSharpPowerLandauContinuation 0 beta =
      dyadicSharpPrimeContinuedSource := by
    funext z
    rw [dyadicSharpPowerLandauContinuation]
    norm_num
  rw [hsourceEq] at hsourcePower
  intro s hs
  have hsource : DifferentiableWithinAt ℂ dyadicSharpPrimeContinuedSource
      (Metric.ball (((1 + delta : ℝ) : ℂ)) r) s := by
    exact hsourcePower s hs
  have hdist : ‖s - (((1 + delta : ℝ) : ℂ))‖ < r := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  have habs := Complex.abs_re_le_norm
    (s - (((1 + delta : ℝ) : ℂ)))
  rw [Complex.sub_re, ofReal_re] at habs
  have hlower : -r < s.re - (1 + delta) := by
    have := lt_of_le_of_lt habs hdist
    rw [abs_lt] at this
    exact this.1
  have hre : 1 + beta < s.re := by linarith
  have habsc : abscissaOfAbsConv
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) ≤
      ((1 + beta : ℝ) : EReal) := hcorr.abscissaOfAbsConv_le
  have habslt : abscissaOfAbsConv
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) <
      (s.re : EReal) := by
    refine habsc.trans_lt ?_
    exact_mod_cast hre
  have hcorrDiff : DifferentiableAt ℂ
      (LSeries
        (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))) s :=
    (LSeries_hasDerivAt habslt).differentiableAt
  change DifferentiableWithinAt ℂ
    (dyadicSharpPrimeContinuedSource +
      LSeries (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)))
    (Metric.ball (((1 + delta : ℝ) : ℂ)) r) s
  exact hsource.add hcorrDiff.differentiableWithinAt

/-- Analytic continuation propagates the far-right corrected Dirichlet identity throughout any
right half-plane on which the corrected series is known to converge. -/
theorem dyadicSharpNegativePartLandauContinuation_eq_LSeries_rightOf
    (beta delta : ℝ) (hdelta : 0 < delta)
    (hbetaDelta : beta < delta)
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    (hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + beta : ℝ) : ℂ)))
    {sigma : ℝ} (hsigma : 1 + delta < sigma)
    (hsum : LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
      (sigma : ℂ)) :
    Set.EqOn dyadicSharpNegativePartLandauContinuation
      (LSeries
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)))
      {s : ℂ | sigma < s.re} := by
  let U : Set ℂ := {s : ℂ | sigma < s.re}
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUpre : IsPreconnected U := (convex_halfSpace_re_gt sigma).isPreconnected
  have hGdiff : DifferentiableOn ℂ
      dyadicSharpNegativePartLandauContinuation U :=
    (differentiableOn_dyadicSharpNegativePartLandauContinuation_rightOf
      beta delta hdelta hbetaDelta hupper hcorr).mono (by
        intro s hs
        change sigma < s.re at hs
        change 1 + delta < s.re
        linarith)
  have hLdiff : DifferentiableOn ℂ
      (LSeries
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))) U := by
    intro s hs
    change sigma < s.re at hs
    have habs := hsum.abscissaOfAbsConv_le
    have habslt : abscissaOfAbsConv
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) <
        s.re := lt_of_le_of_lt habs (by exact_mod_cast hs)
    exact (LSeries_hasDerivAt habslt).differentiableAt.differentiableWithinAt
  let x0 : ℝ := max sigma (3 / 2) + 1
  let z0 : ℂ := (x0 : ℂ)
  have hz0U : z0 ∈ U := by
    change sigma < x0
    dsimp only [x0]
    linarith [le_max_left sigma (3 / 2)]
  have hfar : 3 / 2 < z0.re := by
    change 3 / 2 < x0
    dsimp only [x0]
    linarith [le_max_right sigma (3 / 2)]
  have hcorrFar : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) z0 :=
    hcorr.of_re_le_re (by
      simp only [ofReal_re]
      change 1 + beta ≤ x0
      have : 1 + beta < sigma := by linarith
      dsimp only [x0]
      linarith [le_max_left sigma (3 / 2)])
  have hrightOpen : IsOpen {s : ℂ | 3 / 2 < s.re ∧ 1 + beta < s.re} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_re)
  have hevent : dyadicSharpNegativePartLandauContinuation =ᶠ[nhds z0]
      LSeries
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) := by
    filter_upwards [hrightOpen.mem_nhds ⟨hfar, by
      change 1 + beta < x0
      have : 1 + beta < sigma := by linarith
      dsimp only [x0]
      linarith [le_max_left sigma (3 / 2)]⟩] with s hs
    have hcorrS : LSeriesSummable
        (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) s :=
      hcorr.of_re_le_re (by
        simpa only [ofReal_re] using hs.2.le)
    exact (LSeries_dyadicSharpNegativePartLandauCoefficient_eq_continuation
      hs.1 hcorrS).symm
  exact AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    (hGdiff.analyticOnNhd hUopen) (hLdiff.analyticOnNhd hUopen)
      hUpre hz0U hevent

/-- One-abscissa Landau transfer for the negative-part-corrected sharp source.  The correction
need only converge at `1 + beta`, provided that abscissa lies strictly left of the hypothetical
rightmost transverse Xi boundary. -/
theorem exists_dyadicSharpNegativePartLandauCoefficient_summable_left_of_boundary_of_one_abscissa
    (beta : ℝ) (hne : Nonempty XiRightZeroCopy)
    (hbetaDelta : beta < xiRightTransverseSup)
    (hcorrBase : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (((1 + beta : ℝ) : ℂ))) :
    ∃ sigma : ℝ,
      1 + beta < sigma ∧
      sigma < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
        (sigma : ℂ) := by
  let delta : ℝ := xiRightTransverseSup
  have hdelta : 0 < delta := xiRightTransverseSup_pos hne
  have hdeltahalf : delta ≤ 1 / 2 := xiRightTransverseSup_le_half hne
  have hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta :=
    fun q => xiRightCenteredZero_re_le_sup q
  obtain ⟨eta, heta, hordinate⟩ := exists_xiDivisorSupport_abs_im_lower_bound
  let r : ℝ := min (min (1 / 8) (eta / 4)) ((delta - beta) / 4)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min
      (lt_min (by norm_num) (div_pos heta (by norm_num)))
      (div_pos (sub_pos.mpr (by simpa only [delta] using hbetaDelta)) (by norm_num))
  have hrquarter : r ≤ 1 / 4 :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hreta : r ≤ eta / 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (by linarith))
  have hrgap : r ≤ (delta - beta) / 4 := min_le_right _ _
  have hbetaGap : beta + r < delta := by
    have hgap : 0 < delta - beta := by
      simpa only [delta] using sub_pos.mpr hbetaDelta
    linarith
  let sigmaFar : ℝ := 2
  have hcorrFar : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (sigmaFar : ℂ) :=
    hcorrBase.of_re_le_re (by
      simp only [ofReal_re]
      dsimp only [sigmaFar]
      linarith)
  have hsumFar : LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
      (sigmaFar : ℂ) := by
    apply dyadicSharpNegativePartLandauCoefficient_LSeriesSummable
    · norm_num [sigmaFar]
    · exact hcorrFar
  let Rfar : NNReal :=
    ⟨2 - delta - r / 16, by
      linarith [hdeltahalf, hrquarter]⟩
  have hGfar : DifferentiableOn ℂ
      dyadicSharpNegativePartLandauContinuation
      (Metric.closedBall (((sigmaFar + 1 : ℝ) : ℂ)) (Rfar : ℝ)) := by
    apply (differentiableOn_dyadicSharpNegativePartLandauContinuation_rightOf
      beta delta hdelta
        (by simpa only [delta] using hbetaDelta) hupper hcorrBase).mono
    intro s hs
    rw [Metric.mem_closedBall, dist_eq_norm] at hs
    change 1 + delta < s.re
    have habs := Complex.abs_re_le_norm
      (s - (((sigmaFar + 1 : ℝ) : ℂ)))
    rw [Complex.sub_re, ofReal_re] at habs
    have hlower : -(Rfar : ℝ) ≤ s.re - (sigmaFar + 1) := by
      have := le_trans habs hs
      rw [abs_le] at this
      exact this.1
    change -(2 - delta - r / 16) ≤ s.re - (sigmaFar + 1) at hlower
    dsimp only [sigmaFar] at hlower
    linarith
  have hagreeFar : ∀ s : ℂ, sigmaFar < s.re →
      dyadicSharpNegativePartLandauContinuation s =
        LSeries
          (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ)) s := by
    intro s hs
    have hcorrS : LSeriesSummable
        (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ)) s :=
      hcorrBase.of_re_le_re (by
        simp only [ofReal_re]
        dsimp only [sigmaFar] at hs
        linarith)
    symm
    apply LSeries_dyadicSharpNegativePartLandauCoefficient_eq_continuation
    · dsimp only [sigmaFar] at hs
      linarith
    · exact hcorrS
  let sigmaNear : ℝ := 1 + delta + r / 8
  have hsumNear : LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
      (sigmaNear : ℂ) := by
    apply landau_local_summability_transfer
      dyadicSharpNegativePartLandauCoefficient_nonneg
      (h := 1) (by norm_num) hsumFar (R := Rfar)
      (G := dyadicSharpNegativePartLandauContinuation)
      hGfar hagreeFar
    change sigmaFar + 1 - (2 - delta - r / 16) < sigmaNear
    dsimp only [sigmaFar, sigmaNear]
    linarith
  have hsigmaNear : 1 + delta < sigmaNear := by
    dsimp only [sigmaNear]
    linarith
  have heqNear := dyadicSharpNegativePartLandauContinuation_eq_LSeries_rightOf
    beta delta hdelta (by simpa only [delta] using hbetaDelta)
      hupper hcorrBase hsigmaNear hsumNear
  have hcont :=
    differentiableOn_dyadicSharpNegativePartLandauContinuation_landauBall
      beta hdelta.le hr hrquarter hreta hbetaGap hordinate hcorrBase
  let h : ℝ := r / 8
  let R : NNReal := ⟨r / 2, div_nonneg hr.le (by norm_num)⟩
  have hh : 0 < h := by dsimp only [h]; positivity
  have hGlocal : DifferentiableOn ℂ
      dyadicSharpNegativePartLandauContinuation
      (Metric.closedBall (((sigmaNear + h : ℝ) : ℂ)) (R : ℝ)) := by
    apply hcont.mono
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have hcenter :
        ‖(((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ =
          r / 4 := by
      have heq :
          (((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ))) =
            ((r / 4 : ℝ) : ℂ) := by
        dsimp only [sigmaNear, h]
        push_cast
        ring
      rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
      positivity
    calc
      ‖z - (((1 + delta : ℝ) : ℂ))‖ ≤
          ‖z - (((sigmaNear + h : ℝ) : ℂ))‖ +
            ‖(((sigmaNear + h : ℝ) : ℂ) - (((1 + delta : ℝ) : ℂ)))‖ := by
        have := norm_add_le
          (z - (((sigmaNear + h : ℝ) : ℂ)))
          ((((sigmaNear + h : ℝ) : ℂ)) - (((1 + delta : ℝ) : ℂ)))
        simpa only [sub_add_sub_cancel] using this
      _ ≤ r / 2 + r / 4 := by
        rw [hcenter]
        exact add_le_add hz le_rfl
      _ < r := by linarith
  let sigma : ℝ := 1 + delta - r / 8
  have hsum : LSeriesSummable
      (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
      (sigma : ℂ) := by
    apply landau_local_summability_transfer
      dyadicSharpNegativePartLandauCoefficient_nonneg hh hsumNear
      (R := R) (G := dyadicSharpNegativePartLandauContinuation)
      hGlocal
    · intro s hs
      exact heqNear hs
    · change sigmaNear + h - r / 2 < sigma
      dsimp only [sigmaNear, h, sigma]
      linarith
  refine ⟨sigma, ?_, ?_, hsum⟩
  · dsimp only [sigma]
    have hgap : 0 < delta - beta := sub_pos.mpr
      (by simpa only [delta] using hbetaDelta)
    linarith [hrgap]
  · dsimp only [sigma, delta]
    linarith

/-- Landau transfer for the negative-part-corrected sharp values.  Under false RH it produces
absolute convergence of the original sharp source at a real point left of the rightmost
transverse pole. -/
theorem exists_dyadicSharpNegativePartLandauCoefficient_summable_left_of_boundary
    (hne : Nonempty XiRightZeroCopy)
    (henergy : DyadicSharpPrimeSourceNegativePartEnergy) :
    ∃ beta sigma : ℝ,
      0 < beta ∧
      1 + beta < sigma ∧
      sigma < 1 + xiRightTransverseSup ∧
      LSeriesSummable
        (fun n => ((dyadicSharpNegativePartLandauCoefficient n : ℝ) : ℂ))
        (sigma : ℂ) := by
  have hdelta : 0 < xiRightTransverseSup := xiRightTransverseSup_pos hne
  have hbeta0 : 0 < xiRightTransverseSup / 4 := by linarith
  obtain ⟨sigma, h1, h2, h3⟩ :=
    exists_dyadicSharpNegativePartLandauCoefficient_summable_left_of_boundary_of_one_abscissa
      (xiRightTransverseSup / 4) hne (by linarith) (henergy _ hbeta0)
  exact ⟨xiRightTransverseSup / 4, sigma, hbeta0, h1, h2, h3⟩
/-- **Positive-excess energy criterion.**  Dirichlet summability of only the negative sharp
source values at every abscissa `1 + epsilon` proves RH. -/
theorem riemannHypothesis_of_dyadicSharpPrimeSourceNegativePartEnergy
    (henergy : DyadicSharpPrimeSourceNegativePartEnergy) :
    RiemannHypothesis := by
  by_contra hRH
  have hne : Nonempty XiRightZeroCopy :=
    nonempty_xiRightZeroCopy_of_not_riemannHypothesis hRH
  obtain ⟨beta, sigma, hbeta, hsigmaBeta, hsigmaDelta, hsumCorrected⟩ :=
    exists_dyadicSharpNegativePartLandauCoefficient_summable_left_of_boundary
      hne henergy
  have hcorr : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
      (sigma : ℂ) :=
    (henergy beta hbeta).of_re_le_re
      (by simpa only [ofReal_re] using hsigmaBeta.le)
  have hdiff := hsumCorrected.sub hcorr
  have hsource : LSeriesSummable
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ) := by
    change Summable (LSeries.term
      (fun n => ((dyadicSharpPrimeSourceCoefficient n : ℝ) : ℂ))
      (sigma : ℂ))
    change Summable (LSeries.term _ (sigma : ℂ)) at hdiff
    exact hdiff.congr fun n => by
      rcases n.eq_zero_or_pos with rfl | hn
      · simp only [LSeries.term_zero]
      · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
        rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
        simp only [Pi.sub_apply, dyadicSharpNegativePartLandauCoefficient,
          ofReal_add]
        ring
  have hsigmaHalf : 1 / 2 < sigma := by linarith
  have hpoleBound : ∀ q : XiRightZeroCopy,
      (xiRightShiftedPole q).re ≤ sigma :=
    xiRightShiftedPole_re_le_of_dyadicSharpSource_summable
      hsigmaHalf hsource
  have hsupBound : xiRightTransverseSup ≤ sigma - 1 :=
    xiRightTransverseSup_le_of_shiftedPole_re_le hne hpoleBound
  linarith

/-- Source-facing energy written directly in the positive excess of the displayed prime-window
inequality. -/
def DyadicWeightedPrimeWindowPositiveExcessEnergy : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

theorem dyadicSharpPrimeSourceNegativePartEnergy_of_positiveExcessEnergy
    (henergy : DyadicWeightedPrimeWindowPositiveExcessEnergy) :
    DyadicSharpPrimeSourceNegativePartEnergy := by
  intro epsilon hepsilon
  have hscaled := (henergy epsilon hepsilon).smul (2 : ℂ)
  change Summable (LSeries.term
    (fun n => ((dyadicSharpPrimeSourceNegativePart n : ℝ) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hscaled
  exact hscaled.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.smul_apply, smul_eq_mul,
        dyadicSharpPrimeSourceNegativePart_eq_two_mul_positiveExcess,
        ofReal_mul]
      norm_num

/-- Direct theorem surface: weighted Dirichlet energy of only the positive overshoots of the
requested inequality proves RH. -/
theorem riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy
    (henergy : ∀ epsilon : ℝ, 0 < epsilon →
      LSeriesSummable
        (fun n => ((dyadicWeightedPrimeWindowPositiveExcess n : ℝ) : ℂ))
        (((1 + epsilon : ℝ) : ℂ))) :
    RiemannHypothesis :=
  riemannHypothesis_of_dyadicSharpPrimeSourceNegativePartEnergy
    (dyadicSharpPrimeSourceNegativePartEnergy_of_positiveExcessEnergy henergy)

/-! ## Sparse-exception decomposition of the prime-window burden -/

/-- Actual positive excess carried by an exceptional set of integer apertures. -/
def dyadicSharpExceptionalPositiveExcess (E : Set ℕ) (n : ℕ) : ℝ :=
  E.indicator dyadicWeightedPrimeWindowPositiveExcess n

theorem dyadicSharpExceptionalPositiveExcess_nonneg
    (E : Set ℕ) (n : ℕ) :
    0 ≤ dyadicSharpExceptionalPositiveExcess E n := by
  by_cases hn : n ∈ E
  · rw [dyadicSharpExceptionalPositiveExcess, Set.indicator_of_mem hn]
    exact dyadicWeightedPrimeWindowPositiveExcess_nonneg n
  · rw [dyadicSharpExceptionalPositiveExcess, Set.indicator_of_notMem hn]

/-- Exact Dirichlet-energy cost of the positive excess supported on `E`. -/
def DyadicSharpExceptionalPositiveExcessEnergy (E : Set ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((dyadicSharpExceptionalPositiveExcess E n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

/-- Universal square-root majorant supported on an exceptional aperture set. -/
def dyadicSharpHalfPowerExceptionalCoefficient (E : Set ℕ) (n : ℕ) : ℝ :=
  E.indicator (fun m => powerCorrectionCoefficient (1 / 2 : ℝ) m) n

theorem dyadicSharpHalfPowerExceptionalCoefficient_nonneg
    (E : Set ℕ) (n : ℕ) :
    0 ≤ dyadicSharpHalfPowerExceptionalCoefficient E n := by
  by_cases hn : n ∈ E
  · rw [dyadicSharpHalfPowerExceptionalCoefficient, Set.indicator_of_mem hn]
    exact powerCorrectionCoefficient_nonneg _ _
  · rw [dyadicSharpHalfPowerExceptionalCoefficient, Set.indicator_of_notMem hn]

/-- An aperture set is half-power thin when its universal square-root majorant has Dirichlet
energy on every line strictly to the right of one. -/
def DyadicSharpHalfPowerExceptionalEnergy (E : Set ℕ) : Prop :=
  ∀ epsilon : ℝ, 0 < epsilon →
    LSeriesSummable
      (fun n => ((dyadicSharpHalfPowerExceptionalCoefficient E n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ))

private theorem dyadicSharpExceptionalPositiveExcess_le_halfPowerMajorant
    (E : Set ℕ) (n : ℕ) :
    dyadicSharpExceptionalPositiveExcess E n ≤
      dyadicSharpPrimeWindowHalfPowerBound *
        dyadicSharpHalfPowerExceptionalCoefficient E n := by
  by_cases hn : n ∈ E
  · rw [dyadicSharpExceptionalPositiveExcess, Set.indicator_of_mem hn,
      dyadicSharpHalfPowerExceptionalCoefficient, Set.indicator_of_mem hn]
    exact dyadicWeightedPrimeWindowPositiveExcess_le_halfPower n
  · rw [dyadicSharpExceptionalPositiveExcess, Set.indicator_of_notMem hn,
      dyadicSharpHalfPowerExceptionalCoefficient, Set.indicator_of_notMem hn,
      mul_zero]

private theorem dyadicSharpHalfPowerExceptionalMajorant_LSeriesSummable
    (E : Set ℕ) (hE : DyadicSharpHalfPowerExceptionalEnergy E)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    LSeriesSummable
      (fun n => (((dyadicSharpPrimeWindowHalfPowerBound *
        dyadicSharpHalfPowerExceptionalCoefficient E n : ℝ)) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
  have hscaled := (hE epsilon hepsilon).smul
    (dyadicSharpPrimeWindowHalfPowerBound : ℂ)
  change Summable (LSeries.term
    (fun n => (((dyadicSharpPrimeWindowHalfPowerBound *
      dyadicSharpHalfPowerExceptionalCoefficient E n : ℝ)) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hscaled
  exact hscaled.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.smul_apply, smul_eq_mul, ofReal_mul]

/-- Pointwise subpower control away from an exceptional set.  Finite prefixes may simply be
included in `E`. -/
def DyadicWeightedPrimeWindowSubpowerUpperOff (E : Set ℕ) : Prop :=
  ∀ delta : ℝ, 0 < delta →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → n ∉ E →
      dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * powerCorrectionCoefficient delta n

private def dyadicSharpExceptionalExcessMajorant
    (E : Set ℕ) (C delta : ℝ) (n : ℕ) : ℝ :=
  C * powerCorrectionCoefficient delta n +
    dyadicSharpExceptionalPositiveExcess E n

private theorem dyadicSharpExceptionalExcessMajorant_nonneg
    (E : Set ℕ) {C : ℝ} (hC : 0 ≤ C) (delta : ℝ) (n : ℕ) :
    0 ≤ dyadicSharpExceptionalExcessMajorant E C delta n :=
  add_nonneg
    (mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _))
    (dyadicSharpExceptionalPositiveExcess_nonneg E n)

private theorem dyadicSharpExceptionalExcessMajorant_LSeriesSummable
    (E : Set ℕ) (hE : DyadicSharpExceptionalPositiveExcessEnergy E)
    {epsilon C delta : ℝ} (hepsilon : 0 < epsilon)
    (hdelta : 1 + delta < 1 + epsilon) :
    LSeriesSummable
      (fun n => ((dyadicSharpExceptionalExcessMajorant E C delta n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)) := by
  have hpower := powerCorrectionCoefficient_LSeriesSummable
    (alpha := delta) (s := (((1 + epsilon : ℝ) : ℂ))) (by
      simpa only [ofReal_re] using hdelta)
  have hexc := hE epsilon hepsilon
  have hadd := (hpower.smul (C : ℂ)).add hexc
  change Summable (LSeries.term
    (fun n => ((dyadicSharpExceptionalExcessMajorant E C delta n : ℝ) : ℂ))
    (((1 + epsilon : ℝ) : ℂ)))
  change Summable (LSeries.term _ (((1 + epsilon : ℝ) : ℂ))) at hadd
  exact hadd.congr fun n => by
    rcases n.eq_zero_or_pos with rfl | hn
    · simp only [LSeries.term_zero]
    · have hn0 : n ≠ 0 := Nat.ne_of_gt hn
      rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        dyadicSharpExceptionalExcessMajorant, ofReal_add, ofReal_mul]

private theorem dyadicWeightedPrimeWindowPositiveExcess_le_exceptionalMajorant
    (E : Set ℕ) {C delta : ℝ} (hC : 0 ≤ C)
    (hupper : ∀ n : ℕ, n ≠ 0 → n ∉ E →
      dyadicWeightedPrimeWindow n ≤
        2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
          C * powerCorrectionCoefficient delta n) :
    ∀ n : ℕ, dyadicWeightedPrimeWindowPositiveExcess n ≤
      dyadicSharpExceptionalExcessMajorant E C delta n := by
  intro n
  by_cases hnE : n ∈ E
  · rw [dyadicSharpExceptionalExcessMajorant,
      dyadicSharpExceptionalPositiveExcess, Set.indicator_of_mem hnE]
    exact le_add_of_nonneg_left
      (mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _))
  · rw [dyadicSharpExceptionalExcessMajorant,
      dyadicSharpExceptionalPositiveExcess, Set.indicator_of_notMem hnE,
      add_zero]
    by_cases hn0 : n = 0
    · subst n
      norm_num [dyadicWeightedPrimeWindowPositiveExcess,
        dyadicWeightedPrimeWindow, powerCorrectionCoefficient]
    · have hgood := hupper n hn0 hnE
      have hpow : 0 ≤ C * powerCorrectionCoefficient delta n :=
        mul_nonneg hC (powerCorrectionCoefficient_nonneg _ _)
      rw [dyadicWeightedPrimeWindowPositiveExcess, posPart_def]
      exact max_le (by linarith) hpow

/-- Sparse-exception subpower control and the exact exceptional energy together supply the
global positive-excess energy. -/
theorem dyadicWeightedPrimeWindowPositiveExcessEnergy_of_subpowerUpperOff
    (E : Set ℕ)
    (hE : DyadicSharpExceptionalPositiveExcessEnergy E)
    (hupper : DyadicWeightedPrimeWindowSubpowerUpperOff E) :
    DyadicWeightedPrimeWindowPositiveExcessEnergy := by
  intro epsilon hepsilon
  let delta := epsilon / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  obtain ⟨C, hC, hupperC⟩ := hupper delta hdelta
  apply LSeriesSummable_of_nonneg_of_le
    dyadicWeightedPrimeWindowPositiveExcess_nonneg
    (dyadicSharpExceptionalExcessMajorant_nonneg E hC delta)
    (dyadicWeightedPrimeWindowPositiveExcess_le_exceptionalMajorant
      E hC hupperC)
  apply dyadicSharpExceptionalExcessMajorant_LSeriesSummable
    E hE hepsilon
  dsimp only [delta]
  linarith

/-- **Sparse-exception sharp-window criterion.**  The pointwise inequality may fail on an
arbitrary exceptional set, provided the actual positive excess carried there has finite
Dirichlet energy. -/
theorem riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpperOff
    (E : Set ℕ)
    (hE : DyadicSharpExceptionalPositiveExcessEnergy E)
    (hupper : DyadicWeightedPrimeWindowSubpowerUpperOff E) :
    RiemannHypothesis :=
  riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy
    (dyadicWeightedPrimeWindowPositiveExcessEnergy_of_subpowerUpperOff E hE hupper)

/-- The positive excess supported on an initial aperture segment has finite Dirichlet energy. -/
theorem dyadicSharpExceptionalPositiveExcessEnergy_Iio (N : ℕ) :
    DyadicSharpExceptionalPositiveExcessEnergy (Set.Iio N) := by
  intro epsilon _hepsilon
  change Summable
    (LSeries.term
      (fun n => ((dyadicSharpExceptionalPositiveExcess (Set.Iio N) n : ℝ) : ℂ))
      (((1 + epsilon : ℝ) : ℂ)))
  apply summable_of_hasFiniteSupport
  apply (Set.finite_Iio N).subset
  intro n hn
  by_contra hnIio
  apply hn
  rw [LSeries.term_def]
  split_ifs
  · rfl
  · rw [dyadicSharpExceptionalPositiveExcess,
      Set.indicator_of_notMem hnIio]
    simp

/-- Eventual sharp-window subpower control is exactly sparse control off its initial segment. -/
theorem dyadicWeightedPrimeWindowSubpowerUpper_iff_off_Iio (N : ℕ) :
    DyadicWeightedPrimeWindowSubpowerUpper N ↔
      DyadicWeightedPrimeWindowSubpowerUpperOff (Set.Iio N) := by
  constructor
  · intro hwindow delta hdelta
    obtain ⟨C, hC, htail⟩ := hwindow delta hdelta
    refine ⟨C, hC, fun n hn0 hnIio => ?_⟩
    rw [powerCorrectionCoefficient, if_neg hn0]
    exact htail n (not_lt.mp hnIio)
  · intro hoff delta hdelta
    obtain ⟨C, hC, htail⟩ := hoff delta hdelta
    refine ⟨C, hC, fun n hnN => ?_⟩
    rcases n.eq_zero_or_pos with rfl | hn
    · norm_num [dyadicWeightedPrimeWindow]
      exact mul_nonneg hC (Real.rpow_nonneg le_rfl delta)
    · simpa [powerCorrectionCoefficient, hn.ne'] using
        htail n hn.ne' (not_lt.mpr hnN)

/-- Every eventual sharp-window subpower estimate has global positive-excess Dirichlet energy:
its finite prefix is the entire exceptional-energy cost. -/
theorem dyadicWeightedPrimeWindowPositiveExcessEnergy_of_subpowerUpper
    {N : ℕ} (hwindow : DyadicWeightedPrimeWindowSubpowerUpper N) :
    DyadicWeightedPrimeWindowPositiveExcessEnergy :=
  dyadicWeightedPrimeWindowPositiveExcessEnergy_of_subpowerUpperOff
    (Set.Iio N)
    (dyadicSharpExceptionalPositiveExcessEnergy_Iio N)
    ((dyadicWeightedPrimeWindowSubpowerUpper_iff_off_Iio N).mp hwindow)

/-- **Half-power-thin exception criterion.**  The pointwise prime-window estimate may be left
completely uncontrolled on any set whose square-root aperture majorant has finite Dirichlet
energy. -/
theorem riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpperOff_halfPower
    (E : Set ℕ)
    (hE : ∀ epsilon : ℝ, 0 < epsilon →
      LSeriesSummable
        (fun n => ((dyadicSharpHalfPowerExceptionalCoefficient E n : ℝ) : ℂ))
        (((1 + epsilon : ℝ) : ℂ)))
    (hupper : ∀ delta : ℝ, 0 < delta →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, n ≠ 0 → n ∉ E →
        dyadicWeightedPrimeWindow n ≤
          2 * (1 - (Real.sqrt 2)⁻¹) * Real.sqrt n +
            C * powerCorrectionCoefficient delta n) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicWeightedPrimeWindowSubpowerUpperOff E
  · intro epsilon hepsilon
    apply LSeriesSummable_of_nonneg_of_le
      (dyadicSharpExceptionalPositiveExcess_nonneg E)
      (fun n => mul_nonneg dyadicSharpPrimeWindowHalfPowerBound_nonneg
        (dyadicSharpHalfPowerExceptionalCoefficient_nonneg E n))
      (dyadicSharpExceptionalPositiveExcess_le_halfPowerMajorant E)
    exact dyadicSharpHalfPowerExceptionalMajorant_LSeriesSummable
      E hE hepsilon
  · exact hupper

/-- Weighted `L²` energy of the positive overshoots is already sufficient. -/
theorem riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessSquareEnergy
    (h2 : ∀ epsilon : ℝ, 0 < epsilon →
      Summable
        (realDirichletWeightedTerm
          (fun n => (dyadicWeightedPrimeWindowPositiveExcess n) ^ 2)
          (1 + epsilon))) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcessEnergy
  intro epsilon hepsilon
  exact LSeriesSummable_of_squareWeightedTerm_summable
    dyadicWeightedPrimeWindowPositiveExcess_nonneg
    (by linarith) (h2 epsilon hepsilon)

end RHTower
