import GaloisForLFunctions.RHTower.SuzukiRectangularWallGramGate
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularGammaPolarSourceLaw
import GaloisForLFunctions.RHTower.CCMPrimeGammaSourceEnergySpectrum

/-!
# Positive common-lag completion of the rectangular archimedean source

The sharp rectangular polar resolvents and Gamma cancellation kernel are separately signed
channels in the existing source formula.  This module puts them at the same positive time lag and
proves that their sum is pointwise nonnegative, and strictly positive for positive window length.

The completed kernel has an exact integral equal to the normalized archimedean contribution plus
its fixed Euler--pi boundary charge.  Consequently the full rectangular Weil value is exactly a
positive continuous lag mass minus twice the finite positive prime-wall mass and the fixed charge.
This yields a direct tail equivalence between RH and one explicit positive quadrature domination.
No asymptotic estimate or hypothesis about zeta zeros is used.
-/

open Complex Filter MeasureTheory Set

noncomputable section

namespace RHTower

/-! ## Sharp autocorrelation contraction -/

/-- The sharp two-edge autocorrelation never exceeds its zero-lag mass on the positive lag axis.
Together with `rectangularTwoEdgeAutocorrelation_zero`, this says
`0 ≤ R(L,a,h) ≤ R(L,a,0) = 2L` under the geometric window hypotheses. -/
theorem rectangularTwoEdgeAutocorrelation_le_zeroLag
    {L a h : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (hh : 0 ≤ h) :
    rectangularTwoEdgeAutocorrelation L a h ≤
      rectangularTwoEdgeAutocorrelation L a 0 := by
  rw [rectangularTwoEdgeAutocorrelation_zero hL ha,
    rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha hh]
  have hmoving := rectangularMovingAutocorrelationTent_le_min hL ha hh
  by_cases hhL : h ≤ L
  · rw [max_eq_right (by linarith : 0 ≤ L - h)]
    have hmoving_h := hmoving.trans (min_le_right L h)
    linarith
  · rw [max_eq_left (by linarith : L - h ≤ 0)]
    have hmoving_L := hmoving.trans (min_le_left L h)
    linarith

/-! ## Pointwise positive polar--Gamma completion -/

/-- The two polar resolvents combined at common positive lag. -/
def suzukiRectangularPolarLagKernel (L a t : ℝ) : ℝ :=
  2 * Real.cosh (t / 4) * rectangularTwoEdgeAutocorrelation L a (t / 2)

/-- The completed archimedean lag kernel: polar pair plus Gamma cancellation at the same lag. -/
def suzukiRectangularCompletedArchLagKernel (L a t : ℝ) : ℝ :=
  suzukiRectangularPolarLagKernel L a t + rectangularGammaCancellationKernel L a t

/-- The first positive channel in the completed split.  Prime-wall cells sample this channel
exactly at logarithmic lags `t = 2 log n`. -/
def suzukiRectangularPositiveArchSampleChannel (L a t : ℝ) : ℝ :=
  Real.exp (t / 4) * rectangularTwoEdgeAutocorrelation L a (t / 2)

/-- Exact positive-channel decomposition of the completed lag kernel. -/
theorem suzukiRectangularCompletedArchLagKernel_eq_positive_split
    {L a t : ℝ} (ht : 0 < t) :
    suzukiRectangularCompletedArchLagKernel L a t =
      Real.exp (t / 4) * rectangularTwoEdgeAutocorrelation L a (t / 2) +
        Real.exp (-t) / (1 - Real.exp (-t)) *
          (rectangularTwoEdgeAutocorrelation L a 0 -
            Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2)) := by
  have hden : 1 - Real.exp (-t) ≠ 0 :=
    ne_of_gt (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  rw [suzukiRectangularCompletedArchLagKernel, suzukiRectangularPolarLagKernel,
    rectangularGammaCancellationKernel, rectangularGammaCancellationNumerator,
    Real.cosh_eq]
  field_simp [hden]
  ring

/-- The completed polar--Gamma lag is pointwise nonnegative. -/
theorem suzukiRectangularCompletedArchLagKernel_nonneg
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 0 < t) :
    0 ≤ suzukiRectangularCompletedArchLagKernel L a t := by
  rw [suzukiRectangularCompletedArchLagKernel_eq_positive_split ht]
  have hC0 : 0 ≤ rectangularTwoEdgeAutocorrelation L a 0 :=
    rectangularTwoEdgeAutocorrelation_nonneg hL ha (le_refl 0)
  have hCt : 0 ≤ rectangularTwoEdgeAutocorrelation L a (t / 2) :=
    rectangularTwoEdgeAutocorrelation_nonneg hL ha (by positivity)
  have hCtC0 := rectangularTwoEdgeAutocorrelation_le_zeroLag
    hL ha (by positivity : 0 ≤ t / 2)
  have hexp_le : Real.exp (-(t / 4)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hbracket : 0 ≤ rectangularTwoEdgeAutocorrelation L a 0 -
      Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2) := by
    have hscaled : Real.exp (-(t / 4)) *
        rectangularTwoEdgeAutocorrelation L a (t / 2) ≤
        rectangularTwoEdgeAutocorrelation L a 0 := by
      calc
        _ ≤ 1 * rectangularTwoEdgeAutocorrelation L a (t / 2) :=
          mul_le_mul hexp_le (le_refl _) hCt (by positivity)
        _ ≤ _ := by simpa using hCtC0
    linarith
  have hquot : 0 ≤ Real.exp (-t) / (1 - Real.exp (-t)) :=
    div_nonneg (Real.exp_pos _).le
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
  positivity

/-- Positive window length makes the completed polar--Gamma lag strictly positive at every
positive lag, even when the autocorrelation at that lag vanishes. -/
theorem suzukiRectangularCompletedArchLagKernel_pos
    {L a t : ℝ} (hL : 0 < L) (ha : L ≤ a) (ht : 0 < t) :
    0 < suzukiRectangularCompletedArchLagKernel L a t := by
  rw [suzukiRectangularCompletedArchLagKernel_eq_positive_split ht]
  have hCt : 0 ≤ rectangularTwoEdgeAutocorrelation L a (t / 2) :=
    rectangularTwoEdgeAutocorrelation_nonneg hL.le ha (by positivity)
  have hCtC0 := rectangularTwoEdgeAutocorrelation_le_zeroLag
    hL.le ha (by positivity : 0 ≤ t / 2)
  have hexp_lt : Real.exp (-(t / 4)) < 1 :=
    Real.exp_lt_one_iff.mpr (by linarith)
  have hC0 : rectangularTwoEdgeAutocorrelation L a 0 = 2 * L :=
    rectangularTwoEdgeAutocorrelation_zero hL.le ha
  have hbracket : 0 < rectangularTwoEdgeAutocorrelation L a 0 -
      Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2) := by
    have hscaled : Real.exp (-(t / 4)) *
        rectangularTwoEdgeAutocorrelation L a (t / 2) <
        rectangularTwoEdgeAutocorrelation L a 0 := by
      calc
        _ ≤ Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a 0 :=
          mul_le_mul_of_nonneg_left hCtC0 (Real.exp_pos _).le
        _ < 1 * rectangularTwoEdgeAutocorrelation L a 0 := by
          exact mul_lt_mul_of_pos_right hexp_lt (by rw [hC0]; positivity)
        _ = _ := one_mul _
    linarith
  have hquot : 0 < Real.exp (-t) / (1 - Real.exp (-t)) :=
    div_pos (Real.exp_pos _)
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith)))
  have hfirst : 0 ≤ Real.exp (t / 4) *
      rectangularTwoEdgeAutocorrelation L a (t / 2) :=
    mul_nonneg (Real.exp_pos _).le hCt
  nlinarith [mul_pos hquot hbracket]

/-! ## Exact Mangoldt quadrature sampling -/

/-- One sharp von-Mangoldt prime-wall cell is exactly a logarithmic sample of the first positive
archimedean channel with atomic weight `Λ(n)/n`. -/
theorem vonMangoldt_primeCell_eq_positiveArchSample
    {n : ℕ} (hn : 0 < n) (L a : ℝ) :
    ArithmeticFunction.vonMangoldt n / (n : ℝ) *
        suzukiRectangularPositiveArchSampleChannel L a (2 * Real.log n) =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n *
        rectangularTwoEdgeAutocorrelation L a (Real.log n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hexp : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt (n : ℝ) := by
    rw [← Real.log_sqrt hnR.le, Real.exp_log hsqrt]
  rw [suzukiRectangularPositiveArchSampleChannel,
    show 2 * Real.log (n : ℝ) / 4 = Real.log (n : ℝ) / 2 by ring,
    show 2 * Real.log (n : ℝ) / 2 = Real.log (n : ℝ) by ring, hexp]
  field_simp [hnR.ne', hsqrt.ne']
  rw [Real.sq_sqrt hnR.le]

/-- The entire finite sharp prime wall is an exact positive-channel Mangoldt quadrature on the
logarithmic lag nodes `2 log k`. -/
theorem rectangularPrimeAutocorrelationSum_eq_positiveArchMangoldtQuadrature (L a : ℝ) :
    rectangularPrimeAutocorrelationSum L a =
      ∑ k ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a))),
        ArithmeticFunction.vonMangoldt k / (k : ℝ) *
          suzukiRectangularPositiveArchSampleChannel L a (2 * Real.log k) := by
  rw [rectangularPrimeAutocorrelationSum]
  apply Finset.sum_congr rfl
  intro k hk
  symm
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  exact vonMangoldt_primeCell_eq_positiveArchSample (by omega : 0 < k) L a

/-- **The source of strictness.**  The completed lag is bounded below by the zero-lag mass times
the Gamma weight and the exponential defect `1 - exp (-t/4)`; strict positivity is carried by this
term alone, not by the autocorrelation at the lag in question. -/
theorem suzukiRectangularCompletedArchLagKernel_zeroLag_lower_bound
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 0 < t) :
    Real.exp (-t) / (1 - Real.exp (-t)) *
        (rectangularTwoEdgeAutocorrelation L a 0 * (1 - Real.exp (-(t / 4)))) ≤
      suzukiRectangularCompletedArchLagKernel L a t := by
  rw [suzukiRectangularCompletedArchLagKernel_eq_positive_split ht]
  have hA : 0 ≤ Real.exp (t / 4) * rectangularTwoEdgeAutocorrelation L a (t / 2) :=
    mul_nonneg (Real.exp_pos _).le
      (rectangularTwoEdgeAutocorrelation_nonneg hL ha (by positivity))
  have hCtC0 := rectangularTwoEdgeAutocorrelation_le_zeroLag
    hL ha (by positivity : 0 ≤ t / 2)
  have hq : 0 ≤ Real.exp (-t) / (1 - Real.exp (-t)) :=
    div_nonneg (Real.exp_pos _).le
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
  have he : 0 ≤ Real.exp (-(t / 4)) := (Real.exp_pos _).le
  nlinarith [mul_nonneg hq (mul_nonneg he (sub_nonneg.mpr hCtC0))]

/-- The same lower bound written through the exact zero-lag mass `2L`. -/
theorem suzukiRectangularCompletedArchLagKernel_two_mul_lower_bound
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 0 < t) :
    Real.exp (-t) / (1 - Real.exp (-t)) * (2 * L * (1 - Real.exp (-(t / 4)))) ≤
      suzukiRectangularCompletedArchLagKernel L a t := by
  have h := suzukiRectangularCompletedArchLagKernel_zeroLag_lower_bound hL ha ht
  rwa [rectangularTwoEdgeAutocorrelation_zero hL ha] at h

/-- The sampled positive channel is nonnegative, with no window hypotheses. -/
theorem suzukiRectangularPositiveArchSampleChannel_nonneg (L a t : ℝ) :
    0 ≤ suzukiRectangularPositiveArchSampleChannel L a t :=
  mul_nonneg (Real.exp_pos _).le
    (rectangularTwoEdgeAutocorrelation_nonneg_unconditional L a (t / 2))

/-- The sampled positive channel is pointwise bounded by the full completed archimedean kernel. -/
theorem suzukiRectangularPositiveArchSampleChannel_le_completed
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 0 < t) :
    suzukiRectangularPositiveArchSampleChannel L a t ≤
      suzukiRectangularCompletedArchLagKernel L a t := by
  rw [suzukiRectangularCompletedArchLagKernel_eq_positive_split ht,
    suzukiRectangularPositiveArchSampleChannel]
  have hCt : 0 ≤ rectangularTwoEdgeAutocorrelation L a (t / 2) :=
    rectangularTwoEdgeAutocorrelation_nonneg hL ha (by positivity)
  have hCtC0 := rectangularTwoEdgeAutocorrelation_le_zeroLag
    hL ha (by positivity : 0 ≤ t / 2)
  have hexp_le : Real.exp (-(t / 4)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  have hbracket : 0 ≤ rectangularTwoEdgeAutocorrelation L a 0 -
      Real.exp (-(t / 4)) * rectangularTwoEdgeAutocorrelation L a (t / 2) := by
    calc
      0 ≤ rectangularTwoEdgeAutocorrelation L a 0 -
          rectangularTwoEdgeAutocorrelation L a (t / 2) := sub_nonneg.mpr hCtC0
      _ ≤ _ := by
        have := mul_le_mul hexp_le (le_refl _) hCt (by positivity : 0 ≤ (1 : ℝ))
        linarith
  have hquot : 0 ≤ Real.exp (-t) / (1 - Real.exp (-t)) :=
    div_nonneg (Real.exp_pos _).le
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))).le
  nlinarith [mul_nonneg hquot hbracket]

/-- The sampled positive channel lies between zero and the completed kernel at every positive
lag. -/
theorem suzukiRectangularPositiveArchSampleChannel_mem_Icc
    {L a t : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (ht : 0 < t) :
    suzukiRectangularPositiveArchSampleChannel L a t ∈
      Set.Icc 0 (suzukiRectangularCompletedArchLagKernel L a t) :=
  ⟨suzukiRectangularPositiveArchSampleChannel_nonneg L a t,
    suzukiRectangularPositiveArchSampleChannel_le_completed hL ha ht⟩

/-- The exact prime wall is bounded by the completed-kernel Mangoldt quadrature on the same
logarithmic nodes.  This is an atomic-versus-continuous positive-measure interface, not an
asymptotic prime estimate. -/
theorem rectangularPrimeAutocorrelationSum_le_completedArchMangoldtQuadrature
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    rectangularPrimeAutocorrelationSum L a ≤
      ∑ k ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a))),
        ArithmeticFunction.vonMangoldt k / (k : ℝ) *
          suzukiRectangularCompletedArchLagKernel L a (2 * Real.log k) := by
  rw [rectangularPrimeAutocorrelationSum_eq_positiveArchMangoldtQuadrature]
  apply Finset.sum_le_sum
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hkR : (0 : ℝ) < k := by positivity
  apply mul_le_mul_of_nonneg_left
  · apply suzukiRectangularPositiveArchSampleChannel_le_completed hL ha
    have hk1R : (1 : ℝ) < k := by exact_mod_cast hk2
    positivity [Real.log_pos hk1R]
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg hkR.le

/-! ## Exact completed-lag integral -/

/-- The real polar lag is the sum of the positive and reflected half-tilted autocorrelations. -/
theorem ofReal_suzukiRectangularPolarLagKernel_eq_pair (L a t : ℝ) :
    (suzukiRectangularPolarLagKernel L a t : ℂ) =
      rectangularPolarHalfAutocorrelation L a (t / 2) +
        rectangularPolarHalfAutocorrelation L a (-(t / 2)) := by
  rw [suzukiRectangularPolarLagKernel, rectangularPolarHalfAutocorrelation,
    rectangularPolarHalfAutocorrelation, rectangularTwoEdgeAutocorrelation_neg]
  rw [show Complex.exp (((t / 2 : ℝ) : ℂ) / 2) =
      (Real.exp (t / 4) : ℂ) by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring,
    show Complex.exp (((-(t / 2) : ℝ) : ℂ) / 2) =
      (Real.exp (-(t / 4)) : ℂ) by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring,
    Real.cosh_eq]
  push_cast
  ring

/-- Real-part version of the common-lag polar pair. -/
theorem suzukiRectangularPolarLagKernel_eq_pair_re (L a t : ℝ) :
    suzukiRectangularPolarLagKernel L a t =
      (rectangularPolarHalfAutocorrelation L a (t / 2) +
        rectangularPolarHalfAutocorrelation L a (-(t / 2))).re := by
  have h := congrArg Complex.re (ofReal_suzukiRectangularPolarLagKernel_eq_pair L a t)
  simpa only [ofReal_re] using h

/-- The real common-lag polar pair is absolutely integrable. -/
theorem integrable_suzukiRectangularPolarLagKernel (L a : ℝ) :
    Integrable (suzukiRectangularPolarLagKernel L a) := by
  let H : ℝ → ℂ := rectangularPolarHalfAutocorrelation L a
  have hH : Integrable H := integrable_rectangularPolarHalfAutocorrelation L a
  have hplus : Integrable (fun t : ℝ => H (t / 2)) :=
    hH.comp_div (by norm_num : (2 : ℝ) ≠ 0)
  have hminus : Integrable (fun t : ℝ => H (-(t / 2))) := by
    convert hH.comp_mul_left' (by norm_num : (-1 / 2 : ℝ) ≠ 0) using 1
    funext t
    congr 1
    ring
  have hpair := (hplus.add hminus).re
  apply hpair.congr
  filter_upwards with t
  symm
  exact suzukiRectangularPolarLagKernel_eq_pair_re L a t

/-- Exact polar common-lag mass: it is twice the elementary even polar square. -/
theorem integral_suzukiRectangularPolarLagKernel
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    (∫ t : ℝ in Ioi 0, suzukiRectangularPolarLagKernel L a t) =
      2 * rectangularEvenPolarFeature L a ^ (2 : ℕ) := by
  let H : ℝ → ℂ := rectangularPolarHalfAutocorrelation L a
  have hH : Integrable H := integrable_rectangularPolarHalfAutocorrelation L a
  have hsplit : (∫ h : ℝ in Iic 0, H h) + (∫ h : ℝ in Ioi 0, H h) =
      ∫ h : ℝ, H h := by
    convert! (setIntegral_union (Iic_disjoint_Ioi (Eq.le rfl)) measurableSet_Ioi
      hH.integrableOn hH.integrableOn).symm
    rw [Iic_union_Ioi, Measure.restrict_univ]
  have hplus := MeasureTheory.integral_comp_mul_left_Ioi H 0
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hminus := MeasureTheory.integral_comp_mul_left_Ioi (fun h : ℝ => H (-h)) 0
    (by norm_num : (0 : ℝ) < 1 / 2)
  have hplus' : (∫ t : ℝ in Ioi 0, H (t / 2)) =
      2 * ∫ h : ℝ in Ioi 0, H h := by
    norm_num at hplus
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hplus
  have hminus' : (∫ t : ℝ in Ioi 0, H (-(t / 2))) =
      2 * ∫ h : ℝ in Iic 0, H h := by
    norm_num at hminus
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hminus
  have hpair : (∫ t : ℝ in Ioi 0,
      H (t / 2) + H (-(t / 2))) = 2 * (rectangularEvenPolarFeature L a : ℂ) ^ (2 : ℕ) := by
    rw [integral_add (hH.comp_div (by norm_num : (2 : ℝ) ≠ 0)).integrableOn
      (by
        have hm : Integrable (fun t : ℝ => H (-(t / 2))) := by
          convert hH.comp_mul_left' (by norm_num : (-1 / 2 : ℝ) ≠ 0) using 1
          funext t
          congr 1
          ring
        exact hm.integrableOn), hplus', hminus', ← mul_add, add_comm, hsplit,
      integral_rectangularPolarHalfAutocorrelation hL]
  have hcast : (∫ t : ℝ in Ioi 0, (suzukiRectangularPolarLagKernel L a t : ℂ)) =
      2 * (rectangularEvenPolarFeature L a : ℂ) ^ (2 : ℕ) := by
    rw [show (fun t : ℝ => (suzukiRectangularPolarLagKernel L a t : ℂ)) =
        fun t : ℝ => H (t / 2) + H (-(t / 2)) by
      funext t
      exact ofReal_suzukiRectangularPolarLagKernel_eq_pair L a t]
    exact hpair
  norm_cast at hcast

/-- The completed archimedean lag is integrable on the positive axis. -/
theorem integrableOn_suzukiRectangularCompletedArchLagKernel
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    IntegrableOn (suzukiRectangularCompletedArchLagKernel L a) (Ioi 0) :=
  (integrable_suzukiRectangularPolarLagKernel L a).integrableOn.add
    (integrableOn_rectangularGammaCancellationKernel hL ha)

/-- Exact completed archimedean lag mass. -/
theorem integral_suzukiRectangularCompletedArchLagKernel
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    (∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel L a t) =
      2 * rectangularEvenPolarFeature L a ^ (2 : ℕ) +
        ∫ t : ℝ in Ioi 0, rectangularGammaCancellationKernel L a t := by
  change (∫ t : ℝ in Ioi 0,
      suzukiRectangularPolarLagKernel L a t + rectangularGammaCancellationKernel L a t) = _
  rw [integral_add (integrable_suzukiRectangularPolarLagKernel L a).integrableOn
      (integrableOn_rectangularGammaCancellationKernel hL ha),
    integral_suzukiRectangularPolarLagKernel hL]

/-- The completed continuous lag mass is nonnegative. -/
theorem integral_suzukiRectangularCompletedArchLagKernel_nonneg
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    0 ≤ ∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel L a t := by
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  exact suzukiRectangularCompletedArchLagKernel_nonneg hL ha ht

/-! ## Exact positive-mass versus positive-wall balance -/

/-- Adding the fixed Euler--pi charge to the archimedean contribution produces exactly the
completed positive lag mass. -/
theorem normalizedRectangularBottomArchContribution_add_boundaryCharge_eq_completedLagMass
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    normalizedRectangularBottomArchContribution L a +
        (((Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L) : ℝ) : ℂ) =
      ((∫ t : ℝ in Ioi 0,
        suzukiRectangularCompletedArchLagKernel L a t : ℝ) : ℂ) := by
  rw [normalizedRectangularBottomArchContribution_eq_two_mul_eulerIntegral,
    two_mul_integral_rectangularEulerArchIntegrand_eq hL ha,
    integral_suzukiRectangularCompletedArchLagKernel hL ha]
  push_cast
  ring

/-- The finite sharp prime-wall mass is nonnegative without any window hypotheses. -/
theorem rectangularPrimeAutocorrelationSum_nonneg (L a : ℝ) :
    0 ≤ rectangularPrimeAutocorrelationSum L a := by
  rw [rectangularPrimeAutocorrelationSum]
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg k))
      (rectangularTwoEdgeAutocorrelation_nonneg_unconditional L a (Real.log k))

/-- Full sharp Weil balance as completed positive lag mass minus twice the positive prime wall. -/
theorem xiWeilPolarization_rectangular_add_boundaryCharge_eq_completedLagMass_sub_primeWall
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a) +
        (((Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L) : ℝ) : ℂ) =
      (((∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel L a t) -
        2 * rectangularPrimeAutocorrelationSum L a : ℝ) : ℂ) := by
  rw [xiWeilPolarization_rectangular_eq_prime_add_arch hL ha]
  have harch :=
    normalizedRectangularBottomArchContribution_add_boundaryCharge_eq_completedLagMass hL ha
  push_cast at harch ⊢
  linear_combination harch

/-- At one admissible aperture, rectangular Weil positivity is exactly domination of the positive
prime wall plus fixed charge by the completed positive lag mass. -/
theorem xiWeilPolarization_rectangular_nonneg_iff_completedLagMass_dominates_primeWall
    {L a : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) :
    0 ≤ (xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
        (xiRectangularTwoEdgeTransform L a)).re ↔
      2 * rectangularPrimeAutocorrelationSum L a +
          (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L) ≤
        ∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel L a t := by
  have hbalance := congrArg Complex.re
    (xiWeilPolarization_rectangular_add_boundaryCharge_eq_completedLagMass_sub_primeWall hL ha)
  change (xiWeilPolarization (xiRectangularTwoEdgeTransform L a)
      (xiRectangularTwoEdgeTransform L a)).re +
      (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L) =
    (∫ t : ℝ in Ioi 0, suzukiRectangularCompletedArchLagKernel L a t) -
      2 * rectangularPrimeAutocorrelationSum L a at hbalance
  constructor <;> intro h <;> linarith

/-- **Positive-lag quadrature criterion for RH.**  On every admissible logarithmic tail, RH is
equivalent to completed positive archimedean lag mass dominating finite positive prime-wall mass
plus the fixed Euler--pi boundary charge. -/
theorem riemannHypothesis_iff_completedArchLagMass_dominates_primeWall_tail
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      ∀ n : ℕ, N ≤ n →
        2 * rectangularPrimeAutocorrelationSum L (Real.log n / 2) +
            (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L) ≤
          ∫ t : ℝ in Ioi 0,
            suzukiRectangularCompletedArchLagKernel L (Real.log n / 2) t := by
  constructor
  · intro hRH n hn
    apply (xiWeilPolarization_rectangular_nonneg_iff_completedLagMass_dominates_primeWall
      hL.le (hN n hn).2).mp
    exact (riemannHypothesis_iff_rectangular_logSample_weil_nonneg hL).mp hRH n
  · intro hdom
    apply (riemannHypothesis_iff_primeGammaLogCoefficient_tail_nonneg hL hN).mpr
    intro n hn
    rw [xiRectangularPrimeGammaLogCoefficient_eq_weilLogCoefficient_re
      hL.le (hN n hn).2]
    apply (xiWeilPolarization_rectangular_nonneg_iff_completedLagMass_dominates_primeWall
      hL.le (hN n hn).2).mpr
    exact hdom n hn

/-- **Atomic-versus-continuous quadrature criterion for RH.**  This removes the aggregate prime-wall
name from the preceding criterion: its atomic side is literally the positive archimedean sample
channel evaluated at logarithmic integer nodes with von-Mangoldt weights. -/
theorem riemannHypothesis_iff_positiveArchMangoldtQuadrature_le_completedLagMass_tail
    {L : ℝ} (hL : 0 < L) {N : ℕ}
    (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    RiemannHypothesis ↔
      ∀ n : ℕ, N ≤ n →
        2 * (∑ k ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * (Real.log n / 2)))),
            ArithmeticFunction.vonMangoldt k / (k : ℝ) *
              suzukiRectangularPositiveArchSampleChannel L (Real.log n / 2)
                (2 * Real.log k)) +
            (Real.eulerMascheroniConstant + Real.log Real.pi) * (2 * L) ≤
          ∫ t : ℝ in Ioi 0,
            suzukiRectangularCompletedArchLagKernel L (Real.log n / 2) t := by
  simpa only [rectangularPrimeAutocorrelationSum_eq_positiveArchMangoldtQuadrature] using
    riemannHypothesis_iff_completedArchLagMass_dominates_primeWall_tail hL hN

end RHTower
