import GaloisForLFunctions.RHTower.CCMFirstClockVolterra
import GaloisForLFunctions.RHTower.SuzukiExplicitScrewRegularKernel
import GaloisForLFunctions.RHTower.DigammaDifferenceSeries

/-!
# Suzuki's explicit screw function equals the multiplicity-exact Xi zero series

Suzuki's prime--Lerch formula and the corpus's unconditional Xi-zero screw divisor were previously
formalized independently.  This module proves their exact normalization bridge on the source
half-line:

```text
screwFn screwLinearCoeff screwLerchConst t = -(xiScrewDivisor t).re,   t >= 0.
```

The analytic core evaluates the central removable Gamma kernel.  Its `n`th Gauss term is the sum
of a reciprocal difference and a Lerch difference.  Absolute summability then yields

```text
integral GammaKernel = (EulerGamma + Re digamma(1/4)) t
                       + 2 (screwLerchConst - screwLerchTail t).
```

Combining this with the literal central rectangular Guinand--Weil identity identifies the prime,
archimedean, and zero-series formulas without an RH hypothesis.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-- Antiderivative of an exponentially weighted triangular profile. -/
def suzukiTriangleExpPrimitive (a t : ℝ) (s : ℝ) : ℝ :=
  Real.exp (-a * s) * (s / (2 * a) + 1 / (2 * a ^ 2) - t / a)

theorem hasDerivAt_suzukiTriangleExpPrimitive
    {a t s : ℝ} (ha : a ≠ 0) :
    HasDerivAt (suzukiTriangleExpPrimitive a t)
      (Real.exp (-a * s) * (t - s / 2)) s := by
  have hE : HasDerivAt (fun x : ℝ => Real.exp (-a * x))
      (-a * Real.exp (-a * s)) s := by
    convert! (Real.hasDerivAt_exp (-a * s)).comp s
      ((hasDerivAt_id s).const_mul (-a)) using 1
    ring
  have hP : HasDerivAt
      (fun x : ℝ => x / (2 * a) + 1 / (2 * a ^ 2) - t / a)
      (1 / (2 * a)) s := by
    exact (((hasDerivAt_id s).div_const (2 * a)).add_const
      (1 / (2 * a ^ 2))).sub_const (t / a)
  unfold suzukiTriangleExpPrimitive
  convert! hE.mul hP using 1
  field_simp
  ring

/-- Exact Laplace integral of the positive triangular profile. -/
theorem integral_Ioi_exp_mul_suzukiTriangle
    {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    (∫ s : ℝ in Ioi 0, Real.exp (-a * s) * max 0 (t - s / 2)) =
      t / a - (1 - Real.exp (-(2 * a * t))) / (2 * a ^ 2) := by
  let f : ℝ → ℝ := fun s => Real.exp (-a * s) * max 0 (t - s / 2)
  have hcont : Continuous f := by
    dsimp only [f]
    fun_prop
  have hhead : IntervalIntegrable f volume 0 (2 * t) :=
    hcont.intervalIntegrable 0 (2 * t)
  have htailzero : ∀ s ∈ Ioi (2 * t), f s = 0 := by
    intro s hs
    have hs' : 2 * t < s := hs
    dsimp only [f]
    rw [max_eq_left (by linarith : t - s / 2 ≤ 0), mul_zero]
  have htail : IntegrableOn f (Ioi (2 * t)) := by
    exact (integrableOn_zero (μ := volume) (s := Ioi (2 * t))).congr_fun
      (fun s hs => (htailzero s hs).symm) measurableSet_Ioi
  have hfull : IntegrableOn f (Ioi 0) := by
    rw [show Ioi (0 : ℝ) = Ioc 0 (2 * t) ∪ Ioi (2 * t) from
      (Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 2 * t)).symm]
    exact IntegrableOn.union
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le
        (by positivity : (0 : ℝ) ≤ 2 * t)).mp hhead)
      htail
  have hsplit := intervalIntegral.integral_interval_add_Ioi hfull htail
  have htailint : (∫ s : ℝ in Ioi (2 * t), f s) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact htailzero s hs
  rw [htailint, add_zero] at hsplit
  have hinterval :
      (∫ s : ℝ in (0 : ℝ)..(2 * t), f s) =
        suzukiTriangleExpPrimitive a t (2 * t) - suzukiTriangleExpPrimitive a t 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => by
      have hs' := hs
      rw [uIcc_of_le (by positivity : (0 : ℝ) ≤ 2 * t)] at hs'
      have hmax : max 0 (t - s / 2) = t - s / 2 :=
        max_eq_right (by linarith [hs'.2])
      simpa only [f, hmax] using
        hasDerivAt_suzukiTriangleExpPrimitive (t := t) (s := s) ha.ne') hhead
  rw [← hsplit, hinterval]
  dsimp only [suzukiTriangleExpPrimitive]
  simp only [mul_zero, Real.exp_zero, zero_div]
  have hexp : Real.exp (-a * (2 * t)) = Real.exp (-(2 * a * t)) := by
    congr 1
    ring
  rw [hexp]
  field_simp
  ring

/-- The `n`th central Gauss edge is exactly a reciprocal difference plus a Lerch difference. -/
theorem rectangularEulerGaussTermValue_central_eq_gaussLerch
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    rectangularEulerGaussTermValue (t / 2) (t / 2) n =
      ((t / ((n : ℝ) + 1) - t / ((n : ℝ) + 1 / 4) +
        2 * (1 - Real.exp (-(lerchExp n * t))) / (lerchExp n) ^ 2 : ℝ) : ℂ) := by
  let a : ℝ := (n : ℝ) + 1 / 4
  have ha : 0 < a := by dsimp only [a]; positivity
  have hInt :
      (∫ s : ℝ in Ioi 0,
        Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (s : ℂ)) *
          ((rectangularTwoEdgeAutocorrelation (t / 2) (t / 2) (s / 2) : ℂ) *
            Complex.exp (s / 2))) =
        ((∫ s : ℝ in Ioi 0,
          Real.exp (-a * s) * max 0 (t - s / 2) : ℝ) : ℂ) := by
    calc
      _ = ∫ s : ℝ in Ioi 0,
          ((Real.exp (-a * s) * max 0 (t - s / 2) : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
        have hs0 : 0 < s := hs
        rw [rectangularTwoEdgeAutocorrelation_central_eq_triangle
          (T := t) (h := s / 2) ht (by positivity : 0 ≤ s / 2)]
        have hexp :
            Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (s : ℂ)) *
                Complex.exp (s / 2) = (Real.exp (-a * s) : ℂ) := by
          rw [← Complex.exp_add, Complex.ofReal_exp]
          congr 2
          dsimp only [a]
          push_cast
          ring
        calc
          _ = (Complex.exp (-(((n : ℝ) + 3 / 4 : ℝ) : ℂ) * (s : ℂ)) *
                Complex.exp (s / 2)) *
              ((max 0 (t - s / 2) : ℝ) : ℂ) := by ring
          _ = (Real.exp (-a * s) : ℂ) * ((max 0 (t - s / 2) : ℝ) : ℂ) := by rw [hexp]
          _ = _ := by push_cast; rfl
      _ = _ := integral_ofReal
  rw [rectangularEulerGaussTermValue,
    rectangularTwoEdgeAutocorrelation_central_eq_triangle ht (by norm_num), hInt]
  rw [integral_Ioi_exp_mul_suzukiTriangle ha ht]
  simp only [sub_zero, max_eq_right ht]
  norm_num only [max_eq_right, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_one,
    Complex.ofReal_pow]
  have hlerch : lerchExp n = 2 * a := by
    dsimp only [a, lerchExp]
    ring
  rw [hlerch]
  norm_cast
  dsimp only [a]
  field_simp
  ring

/-- Real Gauss summand at the quarter point. -/
def gaussQuarterRealTerm (n : ℕ) : ℝ :=
  1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 / 4)

/-- Gauss's absolutely convergent quarter-point digamma series, in real form. -/
theorem hasSum_gaussQuarterRealTerm :
    HasSum gaussQuarterRealTerm
      ((Complex.digamma (1 / 4)).re + Real.eulerMascheroniConstant) := by
  have hpos : 0 < ((1 / 4 : ℝ) : ℂ).re := by norm_num
  have hsum := summable_gaussDigammaSeriesTerm hpos
  have hvalue := digamma_eq_neg_euler_add_tsum_gauss hpos
  have hc : HasSum (gaussDigammaSeriesTerm ((1 / 4 : ℝ) : ℂ))
      (Complex.digamma ((1 / 4 : ℝ) : ℂ) +
        (Real.eulerMascheroniConstant : ℂ)) := by
    convert hsum.hasSum using 1
    rw [hvalue]
    ring
  have hre := Complex.hasSum_re hc
  convert hre using 1
  · funext n
    simp [gaussQuarterRealTerm, gaussDigammaSeriesTerm, Complex.normSq_apply]
    ring
  · norm_num

/-- Reciprocal squares of Suzuki's Lerch exponents are absolutely summable. -/
theorem summable_one_div_lerchExp_sq :
    Summable (fun n : ℕ => 1 / (lerchExp n) ^ 2) := by
  have hbase : Summable (fun n : ℕ => 1 / (((n : ℝ) + 1) ^ 2)) := by
    have h := (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
    apply h.congr
    intro n
    rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) + 1)]
    simp only [Real.rpow_two]
  apply Summable.of_nonneg_of_le
    (fun n => (by positivity : 0 ≤ 1 / (lerchExp n) ^ 2))
    (fun n => ?_) (hbase.mul_left 4)
  have hle : ((n : ℝ) + 1) / 2 ≤ lerchExp n := by
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [lerchExp]
    linarith
  have hsq : (((n : ℝ) + 1) / 2) ^ 2 ≤ (lerchExp n) ^ 2 := by
    have hleft : 0 ≤ ((n : ℝ) + 1) / 2 := by positivity
    have hright : 0 ≤ lerchExp n := (lerchExp_pos n).le
    nlinarith
  calc
    1 / (lerchExp n) ^ 2 ≤ 1 / (((n : ℝ) + 1) / 2) ^ 2 := by
      exact one_div_le_one_div_of_le (by positivity) hsq
    _ = 4 * (1 / ((n : ℝ) + 1) ^ 2) := by field_simp; ring

/-- Lerch difference summation selected by the central rectangular Gamma edge. -/
theorem hasSum_lerchCentralDifference {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      2 * (1 - Real.exp (-(lerchExp n * t))) / (lerchExp n) ^ 2)
      (2 * (screwLerchConst - screwLerchTail t)) := by
  have hzero : HasSum (fun n : ℕ => 1 / (lerchExp n) ^ 2) screwLerchConst := by
    simpa [screwLerchConst, screwLerchTail] using summable_one_div_lerchExp_sq.hasSum
  have htail : HasSum
      (fun n : ℕ => Real.exp (-(lerchExp n * t)) / (lerchExp n) ^ 2)
      (screwLerchTail t) := (summable_screwLerchTerm ht).hasSum
  apply HasSum.congr_fun ((hzero.sub htail).mul_left 2)
  intro n
  ring

/-- Combined Gauss--Lerch series of the central removable Gamma kernel. -/
theorem hasSum_centralGaussLerchTerm {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ =>
      t / ((n : ℝ) + 1) - t / ((n : ℝ) + 1 / 4) +
        2 * (1 - Real.exp (-(lerchExp n * t))) / (lerchExp n) ^ 2)
      (((Complex.digamma (1 / 4)).re + Real.eulerMascheroniConstant) * t +
        2 * (screwLerchConst - screwLerchTail t)) := by
  apply HasSum.congr_fun
    ((hasSum_gaussQuarterRealTerm.mul_right t).add (hasSum_lerchCentralDifference ht))
  intro n
  simp only [gaussQuarterRealTerm]
  ring

/-- Exact central removable-Gamma integral in Suzuki's quarter-point Lerch normalization. -/
theorem integral_rectangularGammaCancellationKernel_central_eq_gaussLerch
    {t : ℝ} (ht : 0 < t) :
    (∫ s : ℝ in Ioi 0,
      rectangularGammaCancellationKernel (t / 2) (t / 2) s) =
      ((Complex.digamma (1 / 4)).re + Real.eulerMascheroniConstant) * t +
        2 * (screwLerchConst - screwLerchTail t) := by
  let target : ℝ :=
    ((Complex.digamma (1 / 4)).re + Real.eulerMascheroniConstant) * t +
      2 * (screwLerchConst - screwLerchTail t)
  have hsource := tendsto_rectangularEulerGaussPartialValue_to_cancellationKernel
    (L := t / 2) (a := t / 2) (by positivity) (le_refl (t / 2))
  have hsum := (hasSum_centralGaussLerchTerm ht).tendsto_sum_nat
  have hcast : Tendsto
      (fun N : ℕ => ((∑ n ∈ Finset.range N,
        (t / ((n : ℝ) + 1) - t / ((n : ℝ) + 1 / 4) +
          2 * (1 - Real.exp (-(lerchExp n * t))) / (lerchExp n) ^ 2) : ℝ) : ℂ))
      atTop (nhds (target : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp hsum
  have hpartial : ∀ N : ℕ,
      rectangularEulerGaussPartialValue (t / 2) (t / 2) N =
        ((∑ n ∈ Finset.range N,
          (t / ((n : ℝ) + 1) - t / ((n : ℝ) + 1 / 4) +
            2 * (1 - Real.exp (-(lerchExp n * t))) / (lerchExp n) ^ 2) : ℝ) : ℂ) := by
    intro N
    rw [rectangularEulerGaussPartialValue]
    calc
      (∑ n ∈ Finset.range N, rectangularEulerGaussTermValue (t / 2) (t / 2) n) =
          ∑ n ∈ Finset.range N,
            ((t / ((n : ℝ) + 1) - t / ((n : ℝ) + 1 / 4) +
              2 * (1 - Real.exp (-(lerchExp n * t))) / (lerchExp n) ^ 2 : ℝ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro n hn
        exact rectangularEulerGaussTermValue_central_eq_gaussLerch n ht.le
      _ = _ := by push_cast; rfl
  have htarget : Tendsto (rectangularEulerGaussPartialValue (t / 2) (t / 2))
      atTop (nhds (target : ℂ)) :=
    hcast.congr' (Filter.Eventually.of_forall fun N => (hpartial N).symm)
  have heq := tendsto_nhds_unique hsource htarget
  exact_mod_cast heq

/-- Exact explicit archimedean side of the central rectangular Guinand--Weil identity. -/
theorem normalizedRectangularBottomArchContribution_central_explicit
    {t : ℝ} (ht : 0 < t) :
    (normalizedRectangularBottomArchContribution (t / 2) (t / 2)).re =
      16 * (Real.cosh (t / 2) - 1) +
        ((Complex.digamma (1 / 4)).re - Real.log Real.pi) * t +
          2 * (screwLerchConst - screwLerchTail t) := by
  rw [normalizedRectangularBottomArchContribution_central_re ht.le,
    integral_rectangularGammaCancellationKernel_central_eq_gaussLerch ht,
    rectangularEvenPolarFeature_central_sq ht.le]
  ring

/-- The literal central rectangular prime autocorrelation is Suzuki's prime hinge sum. -/
theorem rectangularPrimeAutocorrelationSum_central_eq_screwPrimeSum
    {t : ℝ} (ht : 0 ≤ t) :
    rectangularPrimeAutocorrelationSum (t / 2) (t / 2) = screwPrimeSum t := by
  rw [rectangularPrimeAutocorrelationSum_central_eq_commonTriangle ht (le_refl t),
    screwPrimeSum_eq_sum_max (le_refl ⌊Real.exp t⌋₊)]
  rfl

/-- **Suzuki 2022, Theorem 1.1(ii), explicit-formula normalization.**  On the source half-line,
Suzuki's literal prime--Lerch screw function is the negative of the unconditional,
multiplicity-exact Xi zero series. -/
theorem screwFn_eq_neg_xiScrewDivisor_re {t : ℝ} (ht : 0 ≤ t) :
    screwFn screwLinearCoeff screwLerchConst t = -(xiScrewDivisor t).re := by
  rcases ht.eq_or_lt with rfl | ht
  · rw [xiScrewDivisor_zero]
    simp [screwFn, screwPrimeSum, screwLerchConst]
    norm_num
  · have hcentral := two_mul_xiScrewDivisor_re_eq_central_prime_add_arch ht.le
    rw [rectangularPrimeAutocorrelationSum_central_eq_screwPrimeSum ht.le,
      normalizedRectangularBottomArchContribution_central_explicit ht] at hcentral
    rw [Real.cosh_eq] at hcentral
    rw [screwFn, screwLinearCoeff]
    linarith

/-- Complex-valued form of Suzuki's zero-series identity.  The right-hand side is real
unconditionally, by conjugation symmetry of the full Xi divisor. -/
theorem ofReal_screwFn_eq_neg_xiScrewDivisor {t : ℝ} (ht : 0 ≤ t) :
    (screwFn screwLinearCoeff screwLerchConst t : ℂ) = -xiScrewDivisor t := by
  apply Complex.ext
  · simpa using screwFn_eq_neg_xiScrewDivisor_re ht
  · simp [xiScrewDivisor_im_eq_zero]

/-- Equality of the literal source-function magnitude and the zero-divisor norm. -/
theorem abs_screwFn_eq_norm_xiScrewDivisor {t : ℝ} (ht : 0 ≤ t) :
    |screwFn screwLinearCoeff screwLerchConst t| = ‖xiScrewDivisor t‖ := by
  have h := congrArg norm (ofReal_screwFn_eq_neg_xiScrewDivisor ht)
  simpa [Real.norm_eq_abs] using h

/-- The full Xi screw divisor is even, exactly as its termwise hyperbolic-cosine formula predicts. -/
@[simp] theorem xiScrewDivisor_neg (t : ℝ) :
    xiScrewDivisor (-t) = xiScrewDivisor t := by
  unfold xiScrewDivisor
  apply tsum_congr
  intro q
  simp [xiScrewDivisorTerm]

/-- Suzuki's function `Psi`, equation (1) of arXiv:2206.03682, with the even extension prescribed
immediately after Theorem 1.1 in the source.  The displayed prime--Lerch formula applies at `|t|`. -/
def suzukiPsi (t : ℝ) : ℝ :=
  -screwFn screwLinearCoeff screwLerchConst |t|

/-- **Suzuki 2022, Theorem 1.1(ii).**  The displayed explicit function `Psi` is the full
multiplicity-exact Xi zero series for every `t >= 0`, without RH. -/
theorem ofReal_suzukiPsi_eq_xiScrewDivisor {t : ℝ} (ht : 0 ≤ t) :
    (suzukiPsi t : ℂ) = xiScrewDivisor t := by
  rw [suzukiPsi, abs_of_nonneg ht, Complex.ofReal_neg,
    ofReal_screwFn_eq_neg_xiScrewDivisor ht]
  simp

/-- **Suzuki 2022, Theorem 1.1(ii), on the source's full even extension.** -/
theorem ofReal_suzukiPsi_eq_xiScrewDivisor_all (t : ℝ) :
    (suzukiPsi t : ℂ) = xiScrewDivisor t := by
  rcases le_total 0 t with ht | ht
  · exact ofReal_suzukiPsi_eq_xiScrewDivisor ht
  · have hneg : 0 ≤ -t := by linarith
    rw [← xiScrewDivisor_neg t]
    have h := ofReal_suzukiPsi_eq_xiScrewDivisor (t := -t) hneg
    simpa [suzukiPsi] using h

/-- Suzuki's source function is even on the full real line. -/
@[simp] theorem suzukiPsi_neg (t : ℝ) : suzukiPsi (-t) = suzukiPsi t := by
  simp [suzukiPsi]

theorem suzukiPsi_eq_xiScrewDivisor_re {t : ℝ} (ht : 0 ≤ t) :
    suzukiPsi t = (xiScrewDivisor t).re := by
  exact_mod_cast congrArg Complex.re (ofReal_suzukiPsi_eq_xiScrewDivisor ht)

theorem abs_suzukiPsi_eq_norm_xiScrewDivisor {t : ℝ} (ht : 0 ≤ t) :
    |suzukiPsi t| = ‖xiScrewDivisor t‖ := by
  have h := congrArg norm (ofReal_suzukiPsi_eq_xiScrewDivisor ht)
  simpa [Real.norm_eq_abs] using h

end


end RHTower
