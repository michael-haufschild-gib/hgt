import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMassAtAQuadraticProductDivider
import GaloisForLFunctions.CountingHolography.Sections.TheMellinKernelOfSquareConductorPrices
import GaloisForLFunctions.RHTower.PrimePolarDirichletBackbone
import GaloisForLFunctions.BiScaleUncertainty.InteriorOfBoxSplines

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
  rw [he,LSeries_sub hP hE,LSeries_squareConductorPrice hs,firstEndpointContinuation,squareConductorContinuation]

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
    have h : Tendsto (fun s : ℂ => s-c) (𝓝 c) (𝓝 (c-c)) := (continuous_id.sub continuous_const).tendsto c
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
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

/-- Exactly the dividers in the interior of the quadratic spline support
produce a nonzero signed density. The deciding interval is the overlap of
the logarithmic divider window with the open support of the autocorrelation. -/
theorem quadraticDividerMass_pos_iff {v : ℝ} (hv : 0 < v) :
    0 < (∫ t in (0:ℝ)..v, dyadicSpline t) ↔ Real.exp (-8) < v ∧ v < 4*Real.exp 8 := by
  let u := Real.log v
  let d := Real.log 4
  let g (x : ℝ) := GaloisForLFunctions.ArithmeticWeightTheory.splineAutoCorr x * Real.exp (x/2)
  have hd : 0 < d := Real.log_pos (by norm_num)
  have he : (∫ t in (0:ℝ)..v, dyadicSpline t) = 2*squarePrimeCumulativeWeight v := by
    rw [squarePrimeCumulativeWeight,←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_uIoo
    intro x hx
    exact if_pos (show x ∈ Set.Ioo (0:ℝ) v by simpa only [Set.uIoo_of_le hv.le] using hx).1
  have hu : v < 4*Real.exp 8 ↔ u-d < 8 := by
    have h4 : 4*Real.exp 8 = Real.exp (8+d) := by rw [Real.exp_add,Real.exp_log (by norm_num : (0:ℝ)<4)]; ring
    rw [h4,←Real.log_lt_iff_lt_exp hv]
    dsimp only [u]; constructor <;> intro h <;> linarith only [h]
  rw [he,squarePrimeCumulativeWeight_eq hv,←Real.lt_log_iff_exp_lt hv,hu]
  change 0 < 2*(2*(∫ x in u-d..u, g x)) ↔ -8 < u ∧ u-d < 8
  have hinterval := sub_lt_self u hd
  constructor
  · intro hp
    by_contra hnot
    have heq : (∫ x in u-d..u, g x)=0 := calc
      _ = ∫ _x in u-d..u, (0:ℝ) := by
        apply intervalIntegral.integral_congr_uIoo
        intro x hx
        rw [Set.uIoo_of_le hinterval.le] at hx
        have hfar : 8 < |x| := by
          by_cases hxlo : -8 < u
          · have hleft : 8 ≤ u-d := le_of_not_gt fun h => hnot ⟨hxlo,h⟩
            exact ((hleft.trans_lt hx.1).trans_le (le_abs_self _))
          · linarith only [le_of_not_gt hxlo,hx.2,neg_abs_le x]
        simp only [g,splineAutoCorr_zero_outside hfar,zero_mul]
      _ = _ := by simp
    rw [heq,mul_zero,mul_zero] at hp
    exact lt_irrefl _ hp
  · rintro ⟨hlo,hhi⟩
    apply mul_pos two_pos
    apply mul_pos two_pos
    have hab : max (u-d) (-8) < min u 8 := max_lt (lt_min hinterval hhi) (lt_min hlo (by norm_num))
    obtain ⟨x,hax,hxb⟩ := exists_between hab
    have hxmin := lt_min_iff.mp hxb
    have hxmax := max_lt_iff.mp hax
    apply intervalIntegral.integral_pos hinterval
    · exact (GaloisForLFunctions.ArithmeticWeightTheory.continuous_splineAutoCorr.mul (by fun_prop)).continuousOn
    · exact fun x _ => mul_nonneg (GaloisForLFunctions.ArithmeticWeightTheory.splineAutoCorr_nonneg x) (Real.exp_pos _).le
    · refine ⟨x,⟨hxmax.1.le,hxmin.1.le⟩,mul_pos ?_ (Real.exp_pos _)⟩
      rw [splineAutoCorr_eq_eight_boxes]
      exact GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge.upow_unit_pos 7 (by
        norm_num; exact abs_lt.mpr ⟨hxmax.2,hxmin.2⟩)

theorem squareDividerMass_pos : 0 < squareDividerMass := by
  apply (quadraticDividerMass_pos_iff zero_lt_one).mpr
  refine ⟨Real.exp_lt_one_iff.mpr (by norm_num),?_⟩
  have he := Real.one_le_exp (show (0:ℝ) ≤ 8 by norm_num)
  linarith only [he]

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

/-- On every sufficiently late terminal fragment, the price below the square
is positive and the price above is negative, each of order the sum of cubes. -/
theorem squareDivider_opposite_fragment_prices :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ L M : ℕ, n₀ ≤ L →
      c*(∑ n ∈ Finset.Ioc L M, (n:ℝ)^3) ≤
        (∑ n ∈ Finset.Ioc L M, lowerPrimeEndpointPrice n (n^2)) ∧
      (∑ n ∈ Finset.Ioc L M, (n:ℝ)^2*retainedPrimeEndpoint (n^2) n) ≤
        -c*(∑ n ∈ Finset.Ioc L M, (n:ℝ)^3) := by
  obtain ⟨C,hC,h⟩ := squareDivider_opposite_prices
  let c := squareDividerMass/2
  have hc : 0 < c := half_pos squareDividerMass_pos
  have hg : Tendsto (fun n : ℕ => (n:ℝ)^(2/9:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<2/9)).comp tendsto_natCast_atTop_atTop
  have hlate := (hg.eventually_ge_atTop (C/c)).and (eventually_ge_atTop (2:ℕ))
  obtain ⟨n₀,h₀⟩ := eventually_atTop.mp hlate
  refine ⟨c,hc,n₀,fun L M hL => ?_⟩
  have rows (n : ℕ) (hn : n ∈ Finset.Ioc L M) :
      c*(n:ℝ)^3 ≤ lowerPrimeEndpointPrice n (n^2) ∧
      (n:ℝ)^2*retainedPrimeEndpoint (n^2) n ≤ -c*(n:ℝ)^3 := by
    obtain ⟨hg',hn₂⟩ := h₀ n (hL.trans (Finset.mem_Ioc.mp hn).1.le)
    have hn' : (0:ℝ) < n := Nat.cast_pos.mpr (by omega)
    have he := mul_le_mul_of_nonneg_left ((div_le_iff₀ hc).mp hg')
      (Real.rpow_nonneg hn'.le (25/9:ℝ))
    have hr : (n:ℝ)^(25/9:ℝ)*(n:ℝ)^(2/9:ℝ)=(n:ℝ)^3 := by
      rw [←Real.rpow_add hn',show (25/9:ℝ)+2/9=((3:ℕ):ℝ) by norm_num,Real.rpow_natCast]
    change (n:ℝ)^(25/9:ℝ)*C ≤ (n:ℝ)^(25/9:ℝ)*((n:ℝ)^(2/9:ℝ)*c) at he
    rw [←mul_assoc,hr] at he
    have hlow := (abs_le.mp ((le_add_of_nonneg_right (abs_nonneg _)).trans (h hn₂))).1
    have hup := (abs_le.mp ((le_add_of_nonneg_left (abs_nonneg _)).trans (h hn₂))).2
    dsimp only [c] at he ⊢
    constructor <;> linarith only [he,hlow,hup]
  rw [Finset.mul_sum,Finset.mul_sum]
  exact ⟨Finset.sum_le_sum fun n hn => (rows n hn).1,
    Finset.sum_le_sum fun n hn => (rows n hn).2⟩

/-- The positive lower density and the negative upper density occur in the
two separate price series. Subtracting their cubic coefficients leaves
absolutely convergent errors in the half-plane to the right of 34/9. -/
theorem squareDivider_opposite_real_poles :
    ∃ H G : ℂ → ℂ,
      AnalyticOnNhd ℂ H {s : ℂ | 34/9 < s.re} ∧ AnalyticOnNhd ℂ G {s : ℂ | 34/9 < s.re} ∧
      ∀ {s : ℂ}, 4 < s.re →
        LSeries (fun n => (lowerPrimeEndpointPrice n (n^2):ℂ)) s =
          (squareDividerMass:ℂ)*riemannZeta (s-3)+H s ∧
        LSeries (fun n => (((n:ℝ)^2*retainedPrimeEndpoint (n^2) n:ℝ):ℂ)) s =
          -(squareDividerMass:ℂ)*riemannZeta (s-3)+G s := by
  obtain ⟨C,hC,h⟩ := squareDivider_opposite_prices
  have continuation (f : ℕ → ℝ) (c : ℝ)
      (hf : ∀ n : ℕ, 2 ≤ n → |f n-(n:ℝ)^3*c| ≤ C*(n:ℝ)^(25/9:ℝ)) :
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s : ℂ | 34/9 < s.re} ∧ ∀ {s : ℂ}, 4 < s.re →
        LSeries (fun n => (f n:ℂ)) s = (c:ℂ)*riemannZeta (s-3)+H s := by
    let e (n : ℕ) : ℂ := ((f n-(n:ℝ)^3*c:ℝ):ℂ)
    have he₀ := LSeries.abscissaOfAbsConv_le_of_isBigO_rpow (f := e) (x := 25/9) (by
      apply Asymptotics.isBigO_iff.mpr
      refine ⟨C,?_⟩
      filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
      simpa only [e,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)] using hf n hn)
    have he : LSeries.abscissaOfAbsConv e ≤ ((34/9:ℝ):EReal) := he₀.trans_eq (by
      change ((25/9:ℝ):EReal)+((1:ℝ):EReal)=((34/9:ℝ):EReal)
      rw [←EReal.coe_add]; norm_num)
    refine ⟨LSeries e,fun z hz => LSeries_analyticOnNhd _ z (he.trans_lt (EReal.coe_lt_coe_iff.mpr hz)),?_⟩
    intro s hs
    have hz : 1 < (s-(3:ℂ)).re := by
      change 1 < s.re-3
      linarith only [hs]
    have hsE := LSeriesSummable_of_abscissaOfAbsConv_lt_re (he.trans_lt (EReal.coe_lt_coe_iff.mpr
      (lt_trans (by norm_num : (34/9:ℝ)<4) hs)))
    let P (n : ℕ) := (n:ℂ)^(3:ℂ)
    have hsP : LSeriesSummable P s := (lseriesSummable_cpow _ _).mpr (LSeriesSummable_one_iff.mpr hz)
    have hf' : (fun n => (f n:ℂ)) = (c:ℂ) • P + e := by
      funext n
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,P,e,Complex.ofReal_sub,
        Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_natCast]
      norm_num only [Complex.cpow_ofNat]
      ring
    rw [hf',LSeries_add (hsP.smul _) hsE,LSeries_smul,lseries_cpow,LSeries_one_eq_riemannZeta hz]
  obtain ⟨H,hH,hl⟩ := continuation (fun n => lowerPrimeEndpointPrice n (n^2)) squareDividerMass
    (fun n hn => (le_add_of_nonneg_right (abs_nonneg _)).trans (h hn))
  obtain ⟨G,hG,hu⟩ := continuation (fun n => (n:ℝ)^2*retainedPrimeEndpoint (n^2) n) (-squareDividerMass)
    (fun n hn => by
      rw [mul_neg,sub_neg_eq_add]
      exact (le_add_of_nonneg_left (abs_nonneg _)).trans (h hn))
  exact ⟨H,G,hH,hG,fun {s} hs => ⟨hl hs,by simpa only [Complex.ofReal_neg] using hu hs⟩⟩

#print axioms LSeries_firstEndpointPrice
#print axioms firstEndpointContinuation_zero_residue
#print axioms firstEndpoint_regular_real
#print axioms quadraticDividerMass_pos_iff
#print axioms squareDividerMass_pos
#print axioms squareDivider_opposite_prices
#print axioms squareDivider_opposite_fragment_prices
#print axioms squareDivider_opposite_real_poles
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
