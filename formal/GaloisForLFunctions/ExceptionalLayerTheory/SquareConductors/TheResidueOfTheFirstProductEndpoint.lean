import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMassAtAQuadraticProductDivider
import GaloisForLFunctions.CountingHolography.Sections.TheMellinKernelOfSquareConductorPrices

/-!
# The shifted zero residue on the first product endpoint

The ordinary-prime value returned by the first positive quotient cell
differs from the rational conductor price by O(n²). Its Dirichlet series
therefore carries the entire shifted zero residue. The same subtraction
from the regular price representative is analytic at four.
-/

noncomputable section
open Filter Topology MeasureTheory
open GaloisForLFunctions.CountingHolography.Sections
open GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Returned ordinary-prime endpoint at the seventeen-ninths product cut,
with the original far horizon in both readings. -/
def firstEndpointPrice (n : ℕ) : ℂ :=
  ((n:ℝ)^2*retainedPrimeEndpoint ⌊(n:ℝ)^(17/9:ℝ)⌋₊ n : ℝ)

private def endpointError := squareConductorPrice - firstEndpointPrice

private theorem endpoint_error_abscissa : LSeries.abscissaOfAbsConv endpointError ≤ ((3:ℝ):EReal) := by
  obtain ⟨C,_,h⟩ := firstQuotientPrimeEndpoint_price
  let e (n : ℕ) := squareConductorPrice n - (((n:ℝ)^2*firstQuotientPrimeEndpoint n:ℝ):ℂ)
  have hagree : endpointError =ᶠ[atTop] e := by
    filter_upwards [eventually_ge_atTop (1:ℕ), eventually_retainedPrimeEndpoint
      (by norm_num : (0:ℝ)<17/9) (by norm_num : (17/9:ℝ)<2)] with n hn hc
    simp only [endpointError, Pi.sub_apply,firstEndpointPrice,e,hc,firstQuotientPrimeEndpoint_eq hn]
  rw [LSeries.abscissaOfAbsConv_congr' hagree]
  have he (n : ℕ) (hn : n≠0) : ‖e n‖ ≤ C*(n:ℝ)^(2:ℝ) := by
    change ‖((Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ):ℝ):ℂ) -
      (((n:ℝ)^2*firstQuotientPrimeEndpoint n:ℝ):ℂ)‖ ≤ _
    rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,Real.rpow_two]
    exact h (Nat.pos_of_ne_zero hn)
  have ha := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := e) (x := 2) ⟨C,he⟩
  refine ha.trans_eq ?_
  change ((2:ℝ):EReal)+((1:ℝ):EReal)=((3:ℝ):EReal)
  rw [←EReal.coe_add]
  norm_num

private theorem price_abscissa_four : LSeries.abscissaOfAbsConv squareConductorPrice ≤ ((4:ℝ):EReal) := by
  obtain ⟨C,hC,h⟩ := successorSquare_diagonal_log_at_width
  have he (n : ℕ) (hn : n≠0) : ‖squareConductorPrice n‖ ≤ (2*C)*(n:ℝ)^(3:ℝ) := by
    have hpos := Nat.pos_of_ne_zero hn
    have h1 : (1:ℝ) ≤ n := by exact_mod_cast hpos
    have hw := Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_left (Nat.cast_nonneg n) : (1:ℝ) ≤ n+1)
      (by linarith only [zetaZeroWidth_le_half] : 2*zetaZeroWidth ≤ 1)
    rw [Real.rpow_one] at hw
    change ‖((Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ):ℝ):ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs,show (n:ℝ)^(3:ℝ)=(n:ℝ)^3 from Real.rpow_natCast _ 3]
    apply (h n hpos).trans
    have hz := mul_le_mul_of_nonneg_left (hw.trans (by linarith only [h1] : (n:ℝ)+1 ≤ 2*n))
      (mul_nonneg hC (sq_nonneg (n:ℝ)))
    exact hz.trans_eq (by ring)
  have ha := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := squareConductorPrice) (x := 3) ⟨2*C,he⟩
  refine ha.trans_eq ?_
  change ((3:ℝ):EReal)+((1:ℝ):EReal)=((4:ℝ):EReal)
  rw [←EReal.coe_add]
  norm_num

/-- Continuation of the Dirichlet series of the literal first-cell differences. -/
def firstEndpointContinuation (s : ℂ) := squareConductorContinuation s - LSeries endpointError s

theorem LSeries_firstEndpointPrice {s : ℂ} (hs : 4 < s.re) :
    LSeries firstEndpointPrice s = firstEndpointContinuation s := by
  have hP := LSeriesSummable_of_abscissaOfAbsConv_lt_re (price_abscissa_four.trans_lt (EReal.coe_lt_coe_iff.mpr hs))
  have hE := LSeriesSummable_of_abscissaOfAbsConv_lt_re (endpoint_error_abscissa.trans_lt
    (EReal.coe_lt_coe_iff.mpr (lt_trans (by norm_num : (3:ℝ)<4) hs)))
  have he : firstEndpointPrice = squareConductorPrice - endpointError := by
    ext n
    simp only [endpointError,Pi.sub_apply,sub_sub_cancel]
  rw [he,LSeries_sub hP hE,LSeries_squareConductorPrice hs]
  rfl

private theorem analytic_endpoint_error {s : ℂ} (hs : 3 < s.re) : AnalyticAt ℂ (LSeries endpointError) s :=
  LSeries_analyticOnNhd _ s (endpoint_error_abscissa.trans_lt (EReal.coe_lt_coe_iff.mpr hs))

/-- Removing the completed quotient cells preserves the full nonzero residue
at each shifted right zero, including its multiplicity. -/
theorem firstEndpointContinuation_zero_residue {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (hhalf : 1/2 < ρ.re) (h₁ : ρ.re < 1) :
    let c := 2+2*ρ
    let A := -2*(zetaMultiplicity ρ:ℂ)*mellin squarePrimeWeight ρ
    A ≠ 0 ∧ Tendsto (fun s : ℂ => (s-c)*firstEndpointContinuation s) (𝓝[≠] c) (𝓝 A) := by
  let c := 2+2*ρ
  obtain ⟨ha,hr⟩ := squareConductorContinuation_zero_residue hz hhalf h₁
  have hc : 3 < c.re := by dsimp only [c]; simp [Complex.add_re,Complex.mul_re]; linarith only [hhalf]
  have hdiff : Tendsto (fun s : ℂ => s-c) (𝓝[≠] c) (𝓝 0) := by
    simpa only [sub_self] using ((continuous_id.sub continuous_const).continuousAt (x := c)).tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[≠] c ≤ 𝓝 c)
  have hE := (analytic_endpoint_error hc).continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds : 𝓝[≠] c ≤ 𝓝 c)
  refine ⟨ha,?_⟩
  simpa only [firstEndpointContinuation,mul_sub,zero_mul,sub_zero,c] using hr.sub (hdiff.mul hE)

/-- The representative which fills in the real pole is analytic throughout
the real interval above three, including at four. -/
theorem firstEndpoint_regular_real {x : ℝ} (hx : 3 < x) :
    AnalyticAt ℂ (fun s => squarePriceRegularContinuation s-LSeries endpointError s) (x:ℂ) :=
  (analyticAt_squarePriceRegularContinuation_real hx).sub (analytic_endpoint_error (by simpa only [Complex.ofReal_re] using hx))

theorem firstEndpoint_regular_eq {s : ℂ} (hs : s/2-1 ≠ 1) (hu : zetaResidueUnit (s/2-1) ≠ 0) :
    squarePriceRegularContinuation s-LSeries endpointError s = firstEndpointContinuation s := by
  rw [squarePriceRegularContinuation_eq hs hu,firstEndpointContinuation]

/-- Leading coefficient of the lower endpoint prices divided at the exact square. -/
def squareDividerMass : ℝ := ∫ t in (0:ℝ)..1, dyadicSpline t

/-- The cumulative density at the square is strictly positive. Its logarithmic
integral includes the positive autocorrelation at displacement zero. -/
theorem squareDividerMass_pos : 0 < squareDividerMass := by
  have he : squareDividerMass = 2*squarePrimeCumulativeWeight 1 := by
    rw [squareDividerMass,squarePrimeCumulativeWeight,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    have hx0 := (show x ∈ Set.Ioo (0:ℝ) 1 by simpa only [Set.uIoo_of_le zero_le_one] using hx).1
    exact if_pos hx0
  rw [he,squarePrimeCumulativeWeight_eq zero_lt_one,Real.log_one,zero_sub]
  apply mul_pos two_pos
  apply mul_pos two_pos
  have hlog := Real.log_pos (by norm_num : (1:ℝ)<4)
  apply intervalIntegral.integral_pos (neg_lt_zero.mpr hlog)
  · exact (GaloisForLFunctions.ArithmeticWeightTheory.continuous_splineAutoCorr.mul (by fun_prop)).continuousOn
  · exact fun x _ => mul_nonneg (GaloisForLFunctions.ArithmeticWeightTheory.splineAutoCorr_nonneg x) (Real.exp_pos _).le
  · exact ⟨0,⟨(neg_lt_zero.mpr hlog).le,le_rfl⟩,
      mul_pos GaloisForLFunctions.ArithmeticWeightTheory.splineAutoCorr_zero_pos (Real.exp_pos _)⟩

/-- At the exact square the two ordinary-prime readings have opposite nonzero
cubic coefficients per conductor, uniformly beyond the initial conductor. -/
theorem squareDivider_opposite_prices :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 2 ≤ n →
      |lowerPrimeEndpointPrice n (n^2)-(n:ℝ)^3*squareDividerMass| +
      |(n:ℝ)^2*retainedPrimeEndpoint (n^2) n+(n:ℝ)^3*squareDividerMass| ≤ C*(n:ℝ)^(25/9:ℝ) := by
  obtain ⟨A,hA,ha⟩ := lowerPrimeEndpointPrice_density
  obtain ⟨B,hB,hb⟩ := upperPrimeEndpointPrice_density
  refine ⟨A+B,add_nonneg hA hB,fun {n} hn => ?_⟩
  have hn0 : 0 < n := by omega
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn0
  have hK : 2 ≤ n^2 := hn.trans (Nat.le_self_pow (by decide) _)
  have hscale := successorSquareWindowScale_bounds n
  have hL : n^2 ≤ splineHorizon n := by
    have hr : (n:ℝ)^2 ≤ (splineHorizon n:ℝ) := by
      dsimp only [splineHorizon]; push_cast
      linarith only [hscale.1,hscale.2.2,Nat.cast_nonneg (α := ℝ) (windowEnd ((2*n+1)^2+1))]
    exact_mod_cast hr
  have h := add_le_add (ha hn0 hL) (hb hn0 hK hL)
  rw [add_mul]
  simpa only [Nat.cast_pow,div_self (sq_pos_of_pos hn').ne',squareDividerMass,
    show (1+16/9:ℝ)=25/9 by norm_num] using h

#print axioms LSeries_firstEndpointPrice
#print axioms firstEndpointContinuation_zero_residue
#print axioms firstEndpoint_regular_real
#print axioms squareDividerMass_pos
#print axioms squareDivider_opposite_prices
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
