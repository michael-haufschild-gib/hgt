import GaloisForLFunctions.RHTower.CCM.CCMRectangularTwoEdge
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Exact autocorrelation of the sharp two-edge rectangular profile

This module works at the precise regularity needed by the rectangular Guinand--Weil source
identity.  The physical profile is the sum of two half-open interval indicators.  Its Lebesgue
autocorrelation is computed exactly as two fixed tents and two cross-edge tents; on nonnegative
lags and disjoint symmetric edges, the reverse cross-edge tent vanishes and only one moving tent
remains.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Indicator of the half-open interval `(u,u+L]`. -/
def rectangularIntervalIndicator (u L x : ℝ) : ℝ :=
  (Ioc u (u + L)).indicator (fun _ => 1) x

/-- Lebesgue autocorrelation between two equal-length interval indicators, with the first
indicator evaluated at the translated point `x+h`. -/
def rectangularIntervalCrossCorrelation (u v L h : ℝ) : ℝ :=
  ∫ x : ℝ, rectangularIntervalIndicator u L (x + h) *
    rectangularIntervalIndicator v L x

/-- The cross-correlation integrand is the indicator of the interval overlap. -/
theorem rectangularIntervalCrossCorrelation_integrand_eq_indicator
    (u v L h : ℝ) :
    (fun x : ℝ =>
      rectangularIntervalIndicator u L (x + h) *
        rectangularIntervalIndicator v L x) =
      (Ioc (max (u - h) v) (min (u + L - h) (v + L))).indicator
        (fun _ => 1) := by
  have hshift : (fun x : ℝ => rectangularIntervalIndicator u L (x + h)) =
      fun x : ℝ => (Ioc (u - h) (u + L - h)).indicator (fun _ => 1) x := by
    funext x
    by_cases hx : x + h ∈ Ioc u (u + L)
    · have hx' : x ∈ Ioc (u - h) (u + L - h) := by
        simp only [mem_Ioc] at hx ⊢
        constructor <;> linarith
      simp [rectangularIntervalIndicator, hx, hx']
    · have hx' : x ∉ Ioc (u - h) (u + L - h) := by
        intro hx'
        apply hx
        simp only [mem_Ioc] at hx' ⊢
        constructor <;> linarith
      simp [rectangularIntervalIndicator, hx, hx']
  funext x
  rw [congrFun hshift x]
  by_cases hx1 : x ∈ Ioc (u - h) (u + L - h) <;>
    by_cases hx2 : x ∈ Ioc v (v + L)
  · have hx : x ∈ Ioc (max (u - h) v) (min (u + L - h) (v + L)) := by
      simpa only [← Ioc_inter_Ioc, mem_inter_iff] using And.intro hx1 hx2
    simp [rectangularIntervalIndicator, hx1, hx2, hx]
  · have hx : x ∉ Ioc (max (u - h) v) (min (u + L - h) (v + L)) := by
      simpa only [← Ioc_inter_Ioc, mem_inter_iff, not_and_or] using Or.inr hx2
    simp [rectangularIntervalIndicator, hx1, hx2, hx]
  · have hx : x ∉ Ioc (max (u - h) v) (min (u + L - h) (v + L)) := by
      simpa only [← Ioc_inter_Ioc, mem_inter_iff, not_and_or] using Or.inl hx1
    simp [rectangularIntervalIndicator, hx1, hx2, hx]
  · have hx : x ∉ Ioc (max (u - h) v) (min (u + L - h) (v + L)) := by
      simpa only [← Ioc_inter_Ioc, mem_inter_iff, not_and_or] using Or.inl hx1
    simp [rectangularIntervalIndicator, hx1, hx2, hx]

/-- Every interval cross-correlation integrand is integrable. -/
theorem integrable_rectangularIntervalCrossCorrelation (u v L h : ℝ) :
    Integrable (fun x : ℝ =>
      rectangularIntervalIndicator u L (x + h) *
        rectangularIntervalIndicator v L x) := by
  rw [rectangularIntervalCrossCorrelation_integrand_eq_indicator]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact integrableOn_const (ne_of_lt measure_Ioc_lt_top)

/-- The overlap length of two equal intervals is the triangular tent in their relative lag. -/
theorem rectangularIntervalCrossCorrelation_eq_tent
    (u v L h : ℝ) :
    rectangularIntervalCrossCorrelation u v L h =
      max 0 (L - |h - (u - v)|) := by
  rw [rectangularIntervalCrossCorrelation,
    rectangularIntervalCrossCorrelation_integrand_eq_indicator]
  change (∫ x : ℝ,
    (Ioc (max (u - h) v) (min (u + L - h) (v + L))).indicator
      (1 : ℝ → ℝ) x) = _
  rw [integral_indicator_one measurableSet_Ioc, Measure.real, Real.volume_Ioc]
  rw [show u + L - h = (u - h) + L by ring,
    min_add_add_right]
  have habs : max (u - h) v - min (u - h) v = |h - (u - v)| := by
    rw [max_sub_min_eq_abs]
    congr 1
    ring
  rw [show min (u - h) v + L - max (u - h) v =
      L - (max (u - h) v - min (u - h) v) by ring, habs]
  rw [ENNReal.toReal_ofReal', max_comm]

/-- The symmetric two-edge physical profile corresponding to
`rectangularTwoEdgeTransform`. -/
def rectangularTwoEdgeProfile (L a x : ℝ) : ℝ :=
  rectangularIntervalIndicator (a - L) L x +
    rectangularIntervalIndicator (-a) L x

/-- Lebesgue autocorrelation of the symmetric sharp two-edge profile. -/
def rectangularTwoEdgeAutocorrelation (L a h : ℝ) : ℝ :=
  ∫ x : ℝ, rectangularTwoEdgeProfile L a (x + h) *
    rectangularTwoEdgeProfile L a x

/-- Exact four-tent expansion of the two-edge autocorrelation. -/
theorem rectangularTwoEdgeAutocorrelation_eq_four_tents
    (L a h : ℝ) :
    rectangularTwoEdgeAutocorrelation L a h =
      2 * max 0 (L - |h|) +
        max 0 (L - |h - (2 * a - L)|) +
        max 0 (L - |h + (2 * a - L)|) := by
  rw [rectangularTwoEdgeAutocorrelation]
  simp only [rectangularTwoEdgeProfile]
  rw [show (fun x : ℝ =>
      (rectangularIntervalIndicator (a - L) L (x + h) +
          rectangularIntervalIndicator (-a) L (x + h)) *
        (rectangularIntervalIndicator (a - L) L x +
          rectangularIntervalIndicator (-a) L x)) =
      fun x : ℝ =>
        rectangularIntervalIndicator (a - L) L (x + h) *
            rectangularIntervalIndicator (a - L) L x +
          rectangularIntervalIndicator (a - L) L (x + h) *
            rectangularIntervalIndicator (-a) L x +
          (rectangularIntervalIndicator (-a) L (x + h) *
            rectangularIntervalIndicator (a - L) L x +
          rectangularIntervalIndicator (-a) L (x + h) *
            rectangularIntervalIndicator (-a) L x) by
    funext x
    ring]
  have h11 := integrable_rectangularIntervalCrossCorrelation (a - L) (a - L) L h
  have h12 := integrable_rectangularIntervalCrossCorrelation (a - L) (-a) L h
  have h21 := integrable_rectangularIntervalCrossCorrelation (-a) (a - L) L h
  have h22 := integrable_rectangularIntervalCrossCorrelation (-a) (-a) L h
  change (∫ x : ℝ,
      ((fun y : ℝ => rectangularIntervalIndicator (a - L) L (y + h) *
          rectangularIntervalIndicator (a - L) L y) +
        (fun y : ℝ => rectangularIntervalIndicator (a - L) L (y + h) *
          rectangularIntervalIndicator (-a) L y) +
        ((fun y : ℝ => rectangularIntervalIndicator (-a) L (y + h) *
          rectangularIntervalIndicator (a - L) L y) +
        (fun y : ℝ => rectangularIntervalIndicator (-a) L (y + h) *
          rectangularIntervalIndicator (-a) L y))) x) = _
  calc
    _ = (∫ x : ℝ,
          rectangularIntervalIndicator (a - L) L (x + h) *
              rectangularIntervalIndicator (a - L) L x +
            rectangularIntervalIndicator (a - L) L (x + h) *
              rectangularIntervalIndicator (-a) L x) +
        (∫ x : ℝ,
          rectangularIntervalIndicator (-a) L (x + h) *
              rectangularIntervalIndicator (a - L) L x +
            rectangularIntervalIndicator (-a) L (x + h) *
              rectangularIntervalIndicator (-a) L x) := by
          simpa only [Pi.add_apply] using
            integral_add (h11.add h12) (h21.add h22)
    _ = ((∫ x : ℝ,
            rectangularIntervalIndicator (a - L) L (x + h) *
              rectangularIntervalIndicator (a - L) L x) +
          (∫ x : ℝ,
            rectangularIntervalIndicator (a - L) L (x + h) *
              rectangularIntervalIndicator (-a) L x)) +
        ((∫ x : ℝ,
            rectangularIntervalIndicator (-a) L (x + h) *
              rectangularIntervalIndicator (a - L) L x) +
          (∫ x : ℝ,
            rectangularIntervalIndicator (-a) L (x + h) *
              rectangularIntervalIndicator (-a) L x)) := by
          rw [integral_add h11 h12, integral_add h21 h22]
    _ = _ := by
      change rectangularIntervalCrossCorrelation (a - L) (a - L) L h +
          rectangularIntervalCrossCorrelation (a - L) (-a) L h +
          (rectangularIntervalCrossCorrelation (-a) (a - L) L h +
            rectangularIntervalCrossCorrelation (-a) (-a) L h) = _
      rw [rectangularIntervalCrossCorrelation_eq_tent,
        rectangularIntervalCrossCorrelation_eq_tent,
        rectangularIntervalCrossCorrelation_eq_tent,
        rectangularIntervalCrossCorrelation_eq_tent]
      ring_nf

/-- At nonnegative lags and for disjoint symmetric edges (`a ≥ L`), the reverse cross-edge tent
vanishes.  The autocorrelation is exactly two fixed self-overlap tents plus one moving tent. -/
theorem rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent
    {L a h : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (hh : 0 ≤ h) :
    rectangularTwoEdgeAutocorrelation L a h =
      2 * max 0 (L - h) + max 0 (L - |h - (2 * a - L)|) := by
  rw [rectangularTwoEdgeAutocorrelation_eq_four_tents]
  rw [abs_of_nonneg hh]
  have hreverse : L - |h + (2 * a - L)| ≤ 0 := by
    rw [abs_of_nonneg]
    · linarith
    · linarith
  rw [max_eq_left hreverse]
  ring

/-- Moving triangular prime weight at arithmetic aperture `a = log N / 2`. -/
def rectangularMovingPrimeTent (L N k : ℝ) : ℝ :=
  max 0 (L - |Real.log (k / N) + L|)

/-- Exact arithmetic-aperture autocorrelation: one fixed small-prime tent and one moving tent. -/
theorem rectangularTwoEdgeAutocorrelation_logAperture
    {L N k : ℝ} (hL : 0 ≤ L) (hN : 0 < N) (hk : 1 ≤ k)
    (hNL : 2 * L ≤ Real.log N) :
    rectangularTwoEdgeAutocorrelation L (Real.log N / 2) (Real.log k) =
      2 * max 0 (L - Real.log k) + rectangularMovingPrimeTent L N k := by
  have ha : L ≤ Real.log N / 2 := by linarith
  have hh : 0 ≤ Real.log k := Real.log_nonneg hk
  rw [rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha hh]
  unfold rectangularMovingPrimeTent
  have hk0 : k ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hk)
  have hN0 : N ≠ 0 := ne_of_gt hN
  rw [Real.log_div hk0 hN0]
  congr 3
  ring

/-- The moving tent is supported inside the single multiplicative shell
`N exp(-2L) < k < N`. -/
theorem rectangularMovingPrimeTent_support
    {L N k : ℝ} (hN : 0 < N) (hk : 0 < k)
    (htent : 0 < rectangularMovingPrimeTent L N k) :
    N * Real.exp (-2 * L) < k ∧ k < N := by
  unfold rectangularMovingPrimeTent at htent
  rw [lt_max_iff] at htent
  rcases htent with hfalse | htent
  · exact (lt_irrefl 0 hfalse).elim
  have habs : |Real.log (k / N) + L| < L := by linarith
  obtain ⟨hlower, hupper⟩ := (abs_lt.mp habs)
  have hlogLower : -2 * L < Real.log (k / N) := by linarith
  have hlogUpper : Real.log (k / N) < 0 := by linarith
  have hratio : 0 < k / N := div_pos hk hN
  have hlowerExp : Real.exp (-2 * L) < k / N := by
    have h := (Real.exp_lt_exp).2 hlogLower
    rw [Real.exp_log hratio] at h
    exact h
  have hupperExp : k / N < 1 := by
    have h := (Real.exp_lt_exp).2 hlogUpper
    rw [Real.exp_log hratio, Real.exp_zero] at h
    exact h
  constructor
  · have := (lt_div_iff₀ hN).mp hlowerExp
    simpa [mul_comm] using this
  · have := (div_lt_iff₀ hN).mp hupperExp
    simpa using this

/-- Beyond lag `2a`, the complete two-edge autocorrelation vanishes. -/
theorem rectangularTwoEdgeAutocorrelation_eq_zero_of_two_mul_a_lt
    {L a h : ℝ} (hL : 0 ≤ L) (ha : L ≤ a) (hh : 2 * a < h) :
    rectangularTwoEdgeAutocorrelation L a h = 0 := by
  rw [rectangularTwoEdgeAutocorrelation_eq_fixed_add_moving_tent hL ha (by linarith)]
  have hfixed : L - h ≤ 0 := by linarith
  have hmovingArg : 0 ≤ h - (2 * a - L) := by linarith
  have hmoving : L - |h - (2 * a - L)| ≤ 0 := by
    rw [abs_of_nonneg hmovingArg]
    linarith
  rw [max_eq_left hfixed, max_eq_left hmoving]
  ring

/-- The finite von Mangoldt pairing with the exact rectangular autocorrelation. -/
def rectangularPrimeAutocorrelationSum (L a : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a))),
    ArithmeticFunction.vonMangoldt k / Real.sqrt k *
      rectangularTwoEdgeAutocorrelation L a (Real.log k)

/-- Fixed small-prime tent contribution. -/
def rectangularFixedPrimeTentSum (L : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    ArithmeticFunction.vonMangoldt k / Real.sqrt k *
      max 0 (L - Real.log k)

/-- Moving prime-window contribution at aperture `a = log N / 2`. -/
def rectangularMovingPrimeTentSum (L N : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 K,
    ArithmeticFunction.vonMangoldt k / Real.sqrt k *
      rectangularMovingPrimeTent L N k

/-- At an arithmetic aperture, the prime autocorrelation pairing splits exactly into a fixed
small-prime tent and one moving multiplicative window. -/
theorem rectangularPrimeAutocorrelationSum_logAperture
    {L N : ℝ} (hL : 0 ≤ L) (hN : 0 < N)
    (hNL : 2 * L ≤ Real.log N) :
    rectangularPrimeAutocorrelationSum L (Real.log N / 2) =
      2 * rectangularFixedPrimeTentSum L (Nat.floor N) +
        rectangularMovingPrimeTentSum L N (Nat.floor N) := by
  have hexp : Real.exp (2 * (Real.log N / 2)) = N := by
    rw [show 2 * (Real.log N / 2) = Real.log N by ring, Real.exp_log hN]
  rw [rectangularPrimeAutocorrelationSum, hexp,
    rectangularFixedPrimeTentSum, rectangularMovingPrimeTentSum]
  rw [Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (hk2.trans' (by norm_num))
  rw [rectangularTwoEdgeAutocorrelation_logAperture hL hN hk1 hNL]
  ring

/-! ## Exact bilateral Laplace transform -/

/-- A sharp interval indicator times an exponential is the corresponding restricted exponential. -/
theorem rectangularIntervalIndicator_mul_exp_eq_indicator
    (u L : ℝ) (w : ℂ) :
    (fun x : ℝ => (rectangularIntervalIndicator u L x : ℂ) *
      Complex.exp (w * x)) =
      (Ioc u (u + L)).indicator (fun x : ℝ => Complex.exp (w * x)) := by
  funext x
  by_cases hx : x ∈ Ioc u (u + L)
  · simp [rectangularIntervalIndicator, hx]
  · simp [rectangularIntervalIndicator, hx]

/-- The compactly supported sharp interval exponential is integrable. -/
theorem integrable_rectangularIntervalIndicator_mul_exp
    (u L : ℝ) (w : ℂ) :
    Integrable (fun x : ℝ => (rectangularIntervalIndicator u L x : ℂ) *
      Complex.exp (w * x)) := by
  rw [rectangularIntervalIndicator_mul_exp_eq_indicator]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)).mono_set
    Ioc_subset_Icc_self

/-- Exact Laplace integral of one length-`L` sharp interval. -/
theorem integral_rectangularIntervalIndicator_mul_exp
    {u L : ℝ} (hL : 0 ≤ L) (w : ℂ) :
    (∫ x : ℝ, (rectangularIntervalIndicator u L x : ℂ) *
      Complex.exp (w * x)) =
      Complex.exp (((u + L : ℝ) : ℂ) * w) * rectangularWindowAmplitude L w := by
  rw [rectangularIntervalIndicator_mul_exp_eq_indicator,
    integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : u ≤ u + L)]
  by_cases hw : w = 0
  · subst w
    simp
  · rw [integral_exp_mul_complex hw, rectangularWindowAmplitude_eq_div hw]
    have hexp : Complex.exp (w * u) =
        Complex.exp (((u + L : ℝ) : ℂ) * w) *
          Complex.exp (-(L : ℂ) * w) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    push_cast
    ring

/-- Integral realization of the physical two-edge profile. -/
def rectangularTwoEdgeLaplaceIntegral (L a : ℝ) (w : ℂ) : ℂ :=
  ∫ x : ℝ, (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp (w * x)

/-- The physical sharp two-edge profile has exactly the algebraic bilateral transform already used
by the Xi-Weil detector. -/
theorem rectangularTwoEdgeLaplaceIntegral_eq_transform
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) (w : ℂ) :
    rectangularTwoEdgeLaplaceIntegral L a w = rectangularTwoEdgeTransform L a w := by
  rw [rectangularTwoEdgeLaplaceIntegral]
  have hright := integrable_rectangularIntervalIndicator_mul_exp (a - L) L w
  have hleft := integrable_rectangularIntervalIndicator_mul_exp (-a) L w
  rw [show (fun x : ℝ =>
      (rectangularTwoEdgeProfile L a x : ℂ) * Complex.exp (w * x)) =
      (fun x : ℝ => (rectangularIntervalIndicator (a - L) L x : ℂ) *
        Complex.exp (w * x)) +
      (fun x : ℝ => (rectangularIntervalIndicator (-a) L x : ℂ) *
        Complex.exp (w * x)) by
    funext x
    simp only [rectangularTwoEdgeProfile]
    push_cast
    simp only [Pi.add_apply]
    ring]
  calc
    _ = (∫ x : ℝ, (rectangularIntervalIndicator (a - L) L x : ℂ) *
          Complex.exp (w * x)) +
        (∫ x : ℝ, (rectangularIntervalIndicator (-a) L x : ℂ) *
          Complex.exp (w * x)) := by
          simpa only [Pi.add_apply] using! integral_add hright hleft
    _ = Complex.exp ((((a - L) + L : ℝ) : ℂ) * w) *
          rectangularWindowAmplitude L w +
        Complex.exp (((-a + L : ℝ) : ℂ) * w) *
          rectangularWindowAmplitude L w := by
          rw [integral_rectangularIntervalIndicator_mul_exp hL,
            integral_rectangularIntervalIndicator_mul_exp hL]
    _ = rectangularTwoEdgeTransform L a w := by
      rw [rectangularTwoEdgeTransform]
      apply congrArg₂ (· + ·)
      · congr 2
        push_cast
        ring
      · by_cases hw : w = 0
        · subst w
          simp
        · rw [rectangularWindowAmplitude_neg hw]
          have hexp : Complex.exp (((-a + L : ℝ) : ℂ) * w) =
              Complex.exp (-(a : ℂ) * w) * Complex.exp ((L : ℂ) * w) := by
            rw [← Complex.exp_add]
            congr 1
            push_cast
            ring
          rw [hexp]
          ring

/-! ## Exact rank-two polar features -/

theorem intervalIntegral_cosh_half (u v : ℝ) :
    (∫ x : ℝ in u..v, Real.cosh (x / 2)) =
      2 * (Real.sinh (v / 2) - Real.sinh (u / 2)) := by
  have hderiv : deriv (fun x : ℝ => 2 * Real.sinh (x / 2)) =
      fun x : ℝ => Real.cosh (x / 2) := by
    funext x
    have h := ((hasDerivAt_id x).div_const 2).sinh.const_mul 2
    convert h.deriv using 1
    all_goals simp only [id_eq]
    all_goals ring
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => 2 * Real.sinh (x / 2)) hderiv]
  · ring
  · intro x _hx
    fun_prop
  · fun_prop

theorem intervalIntegral_sinh_half (u v : ℝ) :
    (∫ x : ℝ in u..v, Real.sinh (x / 2)) =
      2 * (Real.cosh (v / 2) - Real.cosh (u / 2)) := by
  have hderiv : deriv (fun x : ℝ => 2 * Real.cosh (x / 2)) =
      fun x : ℝ => Real.sinh (x / 2) := by
    funext x
    have h := ((hasDerivAt_id x).div_const 2).cosh.const_mul 2
    convert h.deriv using 1
    all_goals simp only [id_eq]
    all_goals ring
  rw [intervalIntegral.integral_deriv_eq_sub'
    (fun x : ℝ => 2 * Real.cosh (x / 2)) hderiv]
  · ring
  · intro x _hx
    fun_prop
  · fun_prop

theorem integrable_rectangularIntervalIndicator_mul_cosh_half (u L : ℝ) :
    Integrable (fun x : ℝ => rectangularIntervalIndicator u L x *
      Real.cosh (x / 2)) := by
  rw [show (fun x : ℝ => rectangularIntervalIndicator u L x * Real.cosh (x / 2)) =
      (Ioc u (u + L)).indicator (fun x : ℝ => Real.cosh (x / 2)) by
    funext x
    by_cases hx : x ∈ Ioc u (u + L) <;> simp [rectangularIntervalIndicator, hx]]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)).mono_set
    Ioc_subset_Icc_self

theorem integrable_rectangularIntervalIndicator_mul_sinh_half (u L : ℝ) :
    Integrable (fun x : ℝ => rectangularIntervalIndicator u L x *
      Real.sinh (x / 2)) := by
  rw [show (fun x : ℝ => rectangularIntervalIndicator u L x * Real.sinh (x / 2)) =
      (Ioc u (u + L)).indicator (fun x : ℝ => Real.sinh (x / 2)) by
    funext x
    by_cases hx : x ∈ Ioc u (u + L) <;> simp [rectangularIntervalIndicator, hx]]
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)).mono_set
    Ioc_subset_Icc_self

theorem integral_rectangularIntervalIndicator_mul_cosh_half
    {u L : ℝ} (hL : 0 ≤ L) :
    (∫ x : ℝ, rectangularIntervalIndicator u L x * Real.cosh (x / 2)) =
      2 * (Real.sinh ((u + L) / 2) - Real.sinh (u / 2)) := by
  rw [show (fun x : ℝ => rectangularIntervalIndicator u L x * Real.cosh (x / 2)) =
      (Ioc u (u + L)).indicator (fun x : ℝ => Real.cosh (x / 2)) by
    funext x
    by_cases hx : x ∈ Ioc u (u + L) <;> simp [rectangularIntervalIndicator, hx],
    integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : u ≤ u + L),
    intervalIntegral_cosh_half]

theorem integral_rectangularIntervalIndicator_mul_sinh_half
    {u L : ℝ} (hL : 0 ≤ L) :
    (∫ x : ℝ, rectangularIntervalIndicator u L x * Real.sinh (x / 2)) =
      2 * (Real.cosh ((u + L) / 2) - Real.cosh (u / 2)) := by
  rw [show (fun x : ℝ => rectangularIntervalIndicator u L x * Real.sinh (x / 2)) =
      (Ioc u (u + L)).indicator (fun x : ℝ => Real.sinh (x / 2)) by
    funext x
    by_cases hx : x ∈ Ioc u (u + L) <;> simp [rectangularIntervalIndicator, hx],
    integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : u ≤ u + L),
    intervalIntegral_sinh_half]

/-- Even and odd polar channels of the physical two-edge profile. -/
def rectangularEvenPolarFeature (L a : ℝ) : ℝ :=
  ∫ x : ℝ, rectangularTwoEdgeProfile L a x * Real.cosh (x / 2)

def rectangularOddPolarFeature (L a : ℝ) : ℝ :=
  ∫ x : ℝ, rectangularTwoEdgeProfile L a x * Real.sinh (x / 2)

theorem rectangularEvenPolarFeature_eq
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    rectangularEvenPolarFeature L a =
      4 * (Real.sinh (a / 2) - Real.sinh ((a - L) / 2)) := by
  rw [rectangularEvenPolarFeature]
  have hr := integrable_rectangularIntervalIndicator_mul_cosh_half (a - L) L
  have hl := integrable_rectangularIntervalIndicator_mul_cosh_half (-a) L
  rw [show (fun x : ℝ => rectangularTwoEdgeProfile L a x * Real.cosh (x / 2)) =
      (fun x : ℝ => rectangularIntervalIndicator (a - L) L x * Real.cosh (x / 2)) +
      (fun x : ℝ => rectangularIntervalIndicator (-a) L x * Real.cosh (x / 2)) by
    funext x
    simp only [rectangularTwoEdgeProfile, Pi.add_apply]
    ring]
  calc
    _ = (∫ x : ℝ, rectangularIntervalIndicator (a - L) L x * Real.cosh (x / 2)) +
        (∫ x : ℝ, rectangularIntervalIndicator (-a) L x * Real.cosh (x / 2)) := by
          simpa only [Pi.add_apply] using! integral_add hr hl
    _ = _ := by
      rw [integral_rectangularIntervalIndicator_mul_cosh_half hL,
        integral_rectangularIntervalIndicator_mul_cosh_half hL]
      rw [show (a - L + L) / 2 = a / 2 by ring,
        show (-a + L) / 2 = -((a - L) / 2) by ring,
        show (-a) / 2 = -(a / 2) by ring,
        Real.sinh_neg, Real.sinh_neg]
      ring

theorem rectangularOddPolarFeature_eq_zero
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    rectangularOddPolarFeature L a = 0 := by
  rw [rectangularOddPolarFeature]
  have hr := integrable_rectangularIntervalIndicator_mul_sinh_half (a - L) L
  have hl := integrable_rectangularIntervalIndicator_mul_sinh_half (-a) L
  rw [show (fun x : ℝ => rectangularTwoEdgeProfile L a x * Real.sinh (x / 2)) =
      (fun x : ℝ => rectangularIntervalIndicator (a - L) L x * Real.sinh (x / 2)) +
      (fun x : ℝ => rectangularIntervalIndicator (-a) L x * Real.sinh (x / 2)) by
    funext x
    simp only [rectangularTwoEdgeProfile, Pi.add_apply]
    ring]
  calc
    _ = (∫ x : ℝ, rectangularIntervalIndicator (a - L) L x * Real.sinh (x / 2)) +
        (∫ x : ℝ, rectangularIntervalIndicator (-a) L x * Real.sinh (x / 2)) := by
          simpa only [Pi.add_apply] using! integral_add hr hl
    _ = _ := by
      rw [integral_rectangularIntervalIndicator_mul_sinh_half hL,
        integral_rectangularIntervalIndicator_mul_sinh_half hL]
      rw [show (a - L + L) / 2 = a / 2 by ring,
        show (-a + L) / 2 = -((a - L) / 2) by ring,
        show (-a) / 2 = -(a / 2) by ring,
        Real.cosh_neg, Real.cosh_neg]
      ring

/-- Exact corrected even polar energy; the odd channel vanishes separately. -/
theorem two_mul_sq_rectangularEvenPolarFeature
    {L : ℝ} (hL : 0 ≤ L) (a : ℝ) :
    2 * rectangularEvenPolarFeature L a ^ 2 =
      32 * (Real.sinh (a / 2) - Real.sinh ((a - L) / 2)) ^ 2 := by
  rw [rectangularEvenPolarFeature_eq hL]
  ring

/-- Coefficients of the growing and decaying polar edges. -/
def rectangularPolarAlpha (L : ℝ) : ℝ := 1 - Real.exp (-L / 2)

def rectangularPolarBeta (L : ℝ) : ℝ := Real.exp (L / 2) - 1

/-- Exact three-scale expansion of the corrected even polar square. -/
theorem rectangularPolarSquare_expansion (L t : ℝ) :
    32 * (Real.sinh t - Real.sinh (t - L / 2)) ^ 2 =
      8 * rectangularPolarAlpha L ^ 2 * Real.exp (2 * t) +
        16 * rectangularPolarAlpha L * rectangularPolarBeta L +
        8 * rectangularPolarBeta L ^ 2 * Real.exp (-2 * t) := by
  rw [Real.sinh_eq, Real.sinh_eq]
  have hpos : Real.exp (t - L / 2) = Real.exp t * Real.exp (-L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-(t - L / 2)) = Real.exp (-t) * Real.exp (L / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hsqPos : Real.exp t ^ 2 = Real.exp (2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hsqNeg : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hcross : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hpos, hneg, rectangularPolarAlpha, rectangularPolarBeta]
  rw [← hsqPos, ← hsqNeg]
  ring_nf
  rw [hcross]
  ring

/-- Arithmetic-aperture form of the polar expansion: growing square-root main term, constant
cross term, and decaying reciprocal-square-root edge. -/
theorem rectangularPolarSquare_logAperture_expansion
    {N : ℝ} (hN : 0 < N) (L : ℝ) :
    32 * (Real.sinh (Real.log N / 4) -
        Real.sinh (Real.log N / 4 - L / 2)) ^ 2 =
      8 * rectangularPolarAlpha L ^ 2 * Real.sqrt N +
        16 * rectangularPolarAlpha L * rectangularPolarBeta L +
        8 * rectangularPolarBeta L ^ 2 / Real.sqrt N := by
  rw [rectangularPolarSquare_expansion]
  have hexpHalf : Real.exp (Real.log N / 2) = Real.sqrt N := by
    rw [← Real.log_sqrt hN.le, Real.exp_log (Real.sqrt_pos.mpr hN)]
  have hexpNegHalf : Real.exp (-(Real.log N / 2)) = (Real.sqrt N)⁻¹ := by
    rw [Real.exp_neg, hexpHalf]
  rw [show 2 * (Real.log N / 4) = Real.log N / 2 by ring,
    show -2 * (Real.log N / 4) = -(Real.log N / 2) by ring,
    hexpHalf, hexpNegHalf]
  rw [div_eq_mul_inv]

/-- Corrected prime--polar source coefficient at finite aperture. -/
def rectangularPrimePolarSourceCoefficient (L a : ℝ) : ℝ :=
  -2 * rectangularPrimeAutocorrelationSum L a +
    2 * rectangularEvenPolarFeature L a ^ 2

/-- Exact arithmetic-aperture prime--polar decomposition into one fixed tent, one moving tent,
and the elementary polar square. -/
theorem rectangularPrimePolarSourceCoefficient_logAperture
    {L N : ℝ} (hL : 0 ≤ L) (hN : 0 < N)
    (hNL : 2 * L ≤ Real.log N) :
    rectangularPrimePolarSourceCoefficient L (Real.log N / 2) =
      -4 * rectangularFixedPrimeTentSum L (Nat.floor N) -
        2 * rectangularMovingPrimeTentSum L N (Nat.floor N) +
        32 * (Real.sinh (Real.log N / 4) -
          Real.sinh (Real.log N / 4 - L / 2)) ^ 2 := by
  rw [rectangularPrimePolarSourceCoefficient,
    rectangularPrimeAutocorrelationSum_logAperture hL hN hNL,
    two_mul_sq_rectangularEvenPolarFeature hL]
  congr 1
  · ring
  · congr 2
    all_goals ring

/-- Fully expanded arithmetic prime--polar coefficient.  The square-root main term is displayed
with the exact coefficient that must cancel the moving von Mangoldt main mass. -/
theorem rectangularPrimePolarSourceCoefficient_logAperture_expanded
    {L N : ℝ} (hL : 0 ≤ L) (hN : 0 < N)
    (hNL : 2 * L ≤ Real.log N) :
    rectangularPrimePolarSourceCoefficient L (Real.log N / 2) =
      -4 * rectangularFixedPrimeTentSum L (Nat.floor N) -
        2 * rectangularMovingPrimeTentSum L N (Nat.floor N) +
        8 * rectangularPolarAlpha L ^ 2 * Real.sqrt N +
        16 * rectangularPolarAlpha L * rectangularPolarBeta L +
        8 * rectangularPolarBeta L ^ 2 / Real.sqrt N := by
  rw [rectangularPrimePolarSourceCoefficient_logAperture hL hN hNL,
    rectangularPolarSquare_logAperture_expansion hN]
  ring

end

end RHTower
