import GaloisForLFunctions.RHTower.WeilArchReLevyPoleForm
import GaloisForLFunctions.RHTower.DigammaVerticalMinimum
import GaloisForLFunctions.RHTower.DirichletArchimedeanSymbolPositivity
import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# The archimedean anomaly of the Weil functional of `ζ`

Write `A(r) = Re ψ(¼ + ir/2) - log π` for the archimedean symbol (`EF.gammaBracket`).

* `XiC_pole_points`: `Ξ(± i/2) = ξ(0) = ξ(1) = ½ ≠ 0`, so the degree is not numerical.
* `gammaBracket_zero_eq`, `exp_abs_gammaBracket_zero`: `A(0) = -(γ + π/2 + log 8π)`, hence
  `e^{|A(0)|} = 8π e^{γ + π/2}`.
* `gammaBracket_zero_le`, `gammaBracket_mono`: `A(r) ≥ A(0)`, and `A` increases with `|r|`.
* `exp_half_div_sinh_eq`, `hasSum_archLevyDensity`, `completelyMonotone_archLevyDensity`: the
  kernel `e^{x/2}/sinh x = 2 Σ_{k ≥ 0} e^{-(2k+½)x}` is completely monotone.
* `weilArchRe_eq_autocorrelation_form`: for `h = f ⋆ f̃`,
  `A(h) = 2(E² - O²) + A(0) h(0) + ∫₀^∞ (h(0) - h(x)) e^{x/2}/sinh x dx`, with
  `E, O = ∫ f cosh(u/2), ∫ f sinh(u/2)`; the integral is nonnegative.
* `weilArch_sub_pole_ge`, `pole_lt_of_violation`, `weilArchRe_nonneg_of_pole_heavy`: the
  archimedean part is at least `A(0) h(0)`, so a violator with `W_∞ < -K h(0)` has pole term below
  `-(K - |A(0)|) h(0)`, and pole-heavy tests (`P ≥ |A(0)| h(0)`) are automatically positive.
-/

open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform ComplexConjugate Real
open Zeta23

namespace RHTower.ArchimedeanAnomaly

noncomputable section

/-! ### The pole points of `Ξ` -/

/-- `Ξ(i/2) = ξ(0) = ½` and `Ξ(-i/2) = ξ(1) = ½`. -/
theorem XiC_pole_points :
    XiC (Complex.I/2)=1/2 ∧ XiC (-(Complex.I/2))=1/2 := by
  constructor
  · have h : (1/2 : ℂ)+Complex.I/2*Complex.I=0 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [XiC, h, xi_zero]
  · have h : (1/2 : ℂ)+-(Complex.I/2)*Complex.I=1 := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [XiC, h, xi_one]

/-! ### The value `A(0)` -/

theorem gammaBracket_zero_eq :
    EF.gammaBracket 0=-(Real.eulerMascheroniConstant+π/2+Real.log (8*π)) := by
  have h8 : Real.log (8*π)=3*Real.log 2+Real.log π := by
    rw [Real.log_mul (by norm_num) Real.pi_ne_zero]
    rw [show (8:ℝ)=2^3 by norm_num, Real.log_pow]
    push_cast
    ring
  unfold EF.gammaBracket
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [re_digamma_one_quarter, h8]
  ring

theorem abs_gammaBracket_zero :
    |EF.gammaBracket 0|=Real.eulerMascheroniConstant+π/2+Real.log (8*π) := by
  rw [gammaBracket_zero_eq, abs_neg]
  apply abs_of_pos
  have hγ : 0<Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant.trans' (by norm_num)
  have hl : 0<Real.log (8*π) := Real.log_pos (by nlinarith [Real.pi_gt_three])
  have hπ := Real.pi_pos
  linarith

/-- `e^{|A(0)|} = 8π e^{γ + π/2}`. -/
theorem exp_abs_gammaBracket_zero :
    Real.exp |EF.gammaBracket 0|=8*π*Real.exp (Real.eulerMascheroniConstant+π/2) := by
  rw [abs_gammaBracket_zero, Real.exp_add, Real.exp_log (by positivity)]
  ring

/-! ### Monotonicity: `A(r) ≥ A(0)` -/

theorem gammaBracket_eq_re_digamma (r : ℝ) :
    EF.gammaBracket r=
      (Complex.digamma (((1/4 : ℝ) : ℂ)+((r/2 : ℝ) : ℂ)*Complex.I)).re-Real.log π := by
  unfold EF.gammaBracket
  congr 3
  push_cast
  ring

/-- The archimedean symbol increases with `|r|`. -/
theorem gammaBracket_mono {r r' : ℝ} (h : |r|≤|r'|) : EF.gammaBracket r≤EF.gammaBracket r' := by
  rw [gammaBracket_eq_re_digamma, gammaBracket_eq_re_digamma]
  have hh : |r/2|≤|r'/2| := by
    rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right h (by norm_num)
  have := re_digamma_mono_of_abs_le (a := 1/4) (by norm_num) hh
  linarith

/-- `A(r) ≥ A(0)`. -/
theorem gammaBracket_zero_le (r : ℝ) : EF.gammaBracket 0≤EF.gammaBracket r :=
  gammaBracket_mono (by simp)

/-! ### The Lévy kernel -/

/-- `e^{x/2}/sinh x = 2 ω(x)` with `ω(x) = e^{-x/2}/(1 - e^{-2x})`. -/
theorem exp_half_div_sinh_eq {x : ℝ} (hx : 0<x) :
    Real.exp (x/2)/Real.sinh x=2*archLevyDensity x := by
  set y := Real.exp (x/2) with hy
  have hy1 : 1<y := Real.one_lt_exp_iff.mpr (by linarith)
  have hy0 : 0<y := by linarith
  have e1 : Real.exp x=y^2 := by rw [hy, ←Real.exp_nat_mul]; congr 1; push_cast; ring
  have e2 : Real.exp (-x)=(y^2)⁻¹ := by rw [Real.exp_neg, e1]
  have e3 : Real.exp (-x/2)=y⁻¹ := by rw [neg_div, Real.exp_neg]
  have e4 : Real.exp (-2*x)=(y^4)⁻¹ := by
    rw [show -2*x=-(((4:ℕ):ℝ)*(x/2)) by push_cast; ring, Real.exp_neg, Real.exp_nat_mul]
  have hy4 : y^4≠1 := by
    have : 1<y^4 := one_lt_pow₀ hy1 (by norm_num)
    exact ne_of_gt this
  have hy2 : y^2-(y^2)⁻¹≠0 := by
    have : 1<y^2 := one_lt_pow₀ hy1 (by norm_num)
    have : (y^2)⁻¹<1 := inv_lt_one_of_one_lt₀ this
    linarith
  unfold archLevyDensity
  rw [Real.sinh_eq, e1, e2, e3, e4]
  have h1 : 1-(y^4)⁻¹≠0 := by
    have : (y^4)⁻¹<1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hy1 (by norm_num))
    linarith
  field_simp

/-- `ω(x) = Σ_{k ≥ 0} e^{-(2k+½)x}` for `x > 0`. -/
theorem hasSum_archLevyDensity {x : ℝ} (hx : 0<x) :
    HasSum (fun k : ℕ => Real.exp (-(2*k+1/2)*x)) (archLevyDensity x) := by
  have he : Real.exp (-2*x)<1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hg := (hasSum_geometric_of_lt_one (Real.exp_pos (-2*x)).le he).mul_left (Real.exp (-x/2))
  have hterm : (fun k : ℕ => Real.exp (-x/2)*Real.exp (-2*x)^k)=
      fun k : ℕ => Real.exp (-(2*k+1/2)*x) := by
    funext k
    rw [←Real.exp_nat_mul, ←Real.exp_add]
    ring_nf
  rw [hterm] at hg
  have hval : archLevyDensity x=Real.exp (-x/2)*(1-Real.exp (-2*x))⁻¹ := by
    rw [archLevyDensity, div_eq_mul_inv]
  rw [hval]
  exact hg

theorem archLevyDensity_eq_tsum {x : ℝ} (hx : 0<x) :
    archLevyDensity x=∑' k : ℕ, Real.exp (-(2*k+1/2)*x) :=
  (hasSum_archLevyDensity hx).tsum_eq.symm

private theorem summable_pow_mul_exp {a : ℝ} (ha : 0<a) (m : ℕ) :
    Summable (fun k : ℕ => (2*(k:ℝ)+1/2)^m*Real.exp (-(2*k+1/2)*a)) := by
  set q := Real.exp (-2*a) with hq
  have hq0 : 0<q := Real.exp_pos _
  have hr : ‖q‖<1 := by
    rw [Real.norm_eq_abs, abs_of_pos hq0]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs0 := summable_pow_mul_geometric_of_norm_lt_one m hr
  have hs1 : Summable (fun k : ℕ => ((k+1:ℕ):ℝ)^m*q^(k+1)) := (summable_nat_add_iff 1).mpr hs0
  have hs2 := hs1.mul_left (3^m*Real.exp (-a/2)*q⁻¹)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hs2
  have hexp : Real.exp (-(2*k+1/2)*a)=Real.exp (-a/2)*q^k := by
    rw [hq, ←Real.exp_nat_mul, ←Real.exp_add]; congr 1; ring
  have hpow : (2*(k:ℝ)+1/2)^m≤3^m*((k+1:ℕ):ℝ)^m := by
    rw [←mul_pow]
    apply pow_le_pow_left₀ (by positivity)
    push_cast; linarith
  rw [hexp]
  calc (2*(k:ℝ)+1/2)^m*(Real.exp (-a/2)*q^k)≤(3^m*((k+1:ℕ):ℝ)^m)*(Real.exp (-a/2)*q^k) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _=(3^m*Real.exp (-a/2)*q⁻¹)*(((k+1:ℕ):ℝ)^m*q^(k+1)) := by
        field_simp
        ring

/-- **Complete monotonicity.**  `(-1)^m ω^{(m)}(x) = Σ_k (2k+½)^m e^{-(2k+½)x} ≥ 0` for `x > 0`. -/
theorem completelyMonotone_archLevyDensity (m : ℕ) {x : ℝ} (hx : 0<x) :
    (-1)^m*iteratedDeriv m archLevyDensity x=
        ∑' k : ℕ, (2*(k:ℝ)+1/2)^m*Real.exp (-(2*k+1/2)*x) ∧
      0≤(-1)^m*iteratedDeriv m archLevyDensity x := by
  set s : Set ℝ := Ioi 0 with hsdef
  have hs : IsOpen s := isOpen_Ioi
  set f : ℕ → ℝ → ℝ := fun k y => Real.exp (-(2*k+1/2)*y) with hfdef
  have hderiv (k j : ℕ) (y : ℝ) (hy : y ∈ s) :
      iteratedDerivWithin j (f k) s y=(-(2*(k:ℝ)+1/2))^j*Real.exp (-(2*k+1/2)*y) := by
    rw [iteratedDerivWithin_of_isOpen hs hy]
    have := iteratedDeriv_exp_const_mul j (-(2*(k:ℝ)+1/2))
    simp only [hfdef]
    rw [show (fun y : ℝ => Real.exp (-(2*(k:ℝ)+1/2)*y))=
      fun y : ℝ => Real.exp ((-(2*(k:ℝ)+1/2))*y) by funext y; ring_nf, this]
  have hcongr : EqOn archLevyDensity (fun y => ∑' k : ℕ, f k y) s :=
    fun y hy => archLevyDensity_eq_tsum hy
  have hit : iteratedDeriv m archLevyDensity x=∑' k : ℕ, iteratedDerivWithin m (f k) s x := by
    rw [←iteratedDerivWithin_of_isOpen hs (show x ∈ s from hx),
      iteratedDerivWithin_congr hcongr (show x ∈ s from hx)]
    apply iteratedDerivWithin_tsum m hs hx
    · intro t ht
      exact (hasSum_archLevyDensity ht).summable
    · intro j _ _
      apply SummableLocallyUniformlyOn_of_locally_bounded hs
      intro K hK hKc
      rcases K.eq_empty_or_nonempty with rfl | hne
      · exact ⟨fun _ => 0, summable_zero, fun _ k hk => absurd hk (Set.notMem_empty k)⟩
      obtain ⟨a, haK, hamin⟩ := hKc.exists_isMinOn hne continuousOn_id
      have ha : 0<a := hK haK
      refine ⟨fun k => (2*(k:ℝ)+1/2)^j*Real.exp (-(2*k+1/2)*a), summable_pow_mul_exp ha j,
        fun k y hy => ?_⟩
      rw [hderiv k j y (hK hy), norm_mul, norm_pow, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_neg, abs_of_pos (by positivity : (0:ℝ)<2*(k:ℝ)+1/2), abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      have : a≤y := hamin hy
      nlinarith [show (0:ℝ)≤2*(k:ℝ)+1/2 by positivity]
    · intro k j r _ hr
      have hEq : EqOn (iteratedDerivWithin j (fun z => f k z) s)
          (fun y => (-(2*(k:ℝ)+1/2))^j*Real.exp (-(2*k+1/2)*y)) s :=
        fun y hy => hderiv k j y hy
      exact ((show Differentiable ℝ (fun y => (-(2*(k:ℝ)+1/2))^j*Real.exp (-(2*k+1/2)*y)) by
        fun_prop) r).congr_of_eventuallyEq (hEq.eventuallyEq_of_mem (hs.mem_nhds hr))
  rw [hit]
  have hterm : (fun k : ℕ => (-1:ℝ)^m*iteratedDerivWithin m (f k) s x)=
      fun k : ℕ => (2*(k:ℝ)+1/2)^m*Real.exp (-(2*k+1/2)*x) := by
    funext k
    rw [hderiv k m x hx, neg_pow (2*(k:ℝ)+1/2) m, ←mul_assoc, ←mul_assoc, ←mul_pow]
    norm_num
  rw [←tsum_mul_left, hterm]
  exact ⟨rfl, tsum_nonneg fun k => by positivity⟩

/-! ### The autocorrelation form of `W_∞` and the pole-negativity of violators -/

variable {f : ℝ → ℝ}

/-- The autocorrelation `h(x) = ∫ f(u) f(u+x) du`. -/
def autocorr (f : ℝ → ℝ) (x : ℝ) : ℝ := ∫ u, f u*f (u+x)

theorem integral_sub_shift_sq (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    ∫ u, (f u-f (u+x))^2=2*(autocorr f 0-autocorr f x) := by
  have hcs1 : HasCompactSupport (fun u => f u^2) := hfc.comp_left (g := fun y : ℝ => y^2) (by norm_num)
  have hi1 : Integrable (fun u => f u^2) := (hf.pow 2).integrable_of_hasCompactSupport hcs1
  have hcs : HasCompactSupport (fun u => f (u+x)) := hfc.comp_homeomorph (Homeomorph.addRight x)
  have hcs2 : HasCompactSupport (fun u => f (u+x)^2) := hcs.comp_left (g := fun y : ℝ => y^2) (by norm_num)
  have hc2 : Continuous (fun u => f (u+x)) := hf.comp (continuous_add_const x)
  have hi2 : Integrable (fun u => f (u+x)^2) := (hc2.pow 2).integrable_of_hasCompactSupport hcs2
  have hi3 : Integrable (fun u => f u*f (u+x)) :=
    (hf.mul hc2).integrable_of_hasCompactSupport hfc.mul_right
  have e1a : (∫ u, ((f u^2+f (u+x)^2)-2*(f u*f (u+x))))=
      (∫ u, (f u^2+f (u+x)^2))-∫ u, 2*(f u*f (u+x)) := integral_sub (hi1.add hi2) (hi3.const_mul 2)
  have e1 : (∫ u, (f u-f (u+x))^2)=(∫ u, (f u^2+f (u+x)^2))-∫ u, 2*(f u*f (u+x)) := by
    rw [←e1a]
    congr 1; funext u; ring
  have e2 : (∫ u, (f u^2+f (u+x)^2))=(∫ u, f u^2)+∫ u, f (u+x)^2 := integral_add hi1 hi2
  have e3 : (∫ u, f (u+x)^2)=∫ u, f u^2 := integral_add_right_eq_self (fun u => f u^2) x
  rw [e1, e2, e3, integral_const_mul]
  unfold autocorr
  simp only [add_zero]
  rw [show (∫ u, f u*f u)=∫ u, f u^2 by congr 1; funext u; ring]
  ring

theorem integral_prod_cosh_eq_sq (hfc : HasCompactSupport f) (hf : Continuous f) :
    (∫ p : ℝ×ℝ, f p.1*f p.2*Real.cosh ((p.1-p.2)/2))=
      (∫ u, f u*Real.cosh (u/2))^2-(∫ u, f u*Real.sinh (u/2))^2 := by
  rw [WeilLevyPole.integral_prod_cosh_eq hfc hf]
  have hie : Integrable (fun u => f u*Real.exp (u/2)) :=
    (hf.mul (Real.continuous_exp.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hie' : Integrable (fun u => f u*Real.exp (-u/2)) :=
    (hf.mul (Real.continuous_exp.comp (continuous_neg.div_const 2))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hc : (∫ u, f u*Real.cosh (u/2))=((∫ u, f u*Real.exp (u/2))+∫ u, f u*Real.exp (-u/2))/2 := by
    rw [←integral_add hie hie', ←integral_div]
    congr 1; funext u; rw [Real.cosh_eq]; ring_nf
  have hs : (∫ u, f u*Real.sinh (u/2))=((∫ u, f u*Real.exp (u/2))-∫ u, f u*Real.exp (-u/2))/2 := by
    rw [←integral_sub hie hie', ←integral_div]
    congr 1; funext u; rw [Real.sinh_eq]; ring_nf
  rw [hc, hs]
  ring

/-- **Autocorrelation form of `W_∞`.**  For a real `f ∈ C²_c(ℝ)` and `h = f ⋆ f̃`,
`W_∞(h) = 2(E² - O²) + A(0) h(0) + ∫₀^∞ (h(0) - h(x)) e^{x/2}/sinh x dx`. -/
theorem weilArchRe_eq_autocorrelation_form (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))=
      2*((∫ u, f u*Real.cosh (u/2))^2-(∫ u, f u*Real.sinh (u/2))^2)+
        EF.gammaBracket 0*autocorr f 0+
        (∫⁻ x in Ioi 0, ENNReal.ofReal ((autocorr f 0-autocorr f x)*
          (Real.exp (x/2)/Real.sinh x))).toReal := by
  rw [WeilLevyPole.weilArchRe_eq_levy_pole hf hfc, integral_prod_cosh_eq_sq hfc hf.continuous]
  have h0 : autocorr f 0=∫ u, f u^2 := by
    unfold autocorr; congr 1; funext u; simp; ring
  have hlev : (∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x*∫ u, (f u-f (u+x))^2))=
      ∫⁻ x in Ioi 0, ENNReal.ofReal ((autocorr f 0-autocorr f x)*(Real.exp (x/2)/Real.sinh x)) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only
    rw [integral_sub_shift_sq hfc hf.continuous x, exp_half_div_sinh_eq hx]
    congr 1
    ring
  rw [hlev, h0]
  ring

/-- **Archimedean lower bound.**  The archimedean part (pole removed) is at least `A(0) h(0)`. -/
theorem weilArch_sub_pole_ge (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    EF.gammaBracket 0*autocorr f 0≤
      WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))-
        2*((∫ u, f u*Real.cosh (u/2))^2-(∫ u, f u*Real.sinh (u/2))^2) := by
  rw [weilArchRe_eq_autocorrelation_form hf hfc]
  have := ENNReal.toReal_nonneg (a := ∫⁻ x in Ioi 0, ENNReal.ofReal ((autocorr f 0-autocorr f x)*
    (Real.exp (x/2)/Real.sinh x)))
  linarith

theorem autocorr_zero_nonneg (f : ℝ → ℝ) : 0≤autocorr f 0 := by
  unfold autocorr
  apply integral_nonneg
  intro u
  simp only [add_zero]
  exact mul_self_nonneg (f u)

/-- **Strong violators are pole-negative.**  If `W_∞(h) < -K h(0)` then the pole term
`2(E² - O²)` is below `-(K - |A(0)|) h(0)`. -/
theorem pole_lt_of_violation (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {K : ℝ}
    (hviol : WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))<
      -K*autocorr f 0) :
    2*((∫ u, f u*Real.cosh (u/2))^2-(∫ u, f u*Real.sinh (u/2))^2)<
      -(K-|EF.gammaBracket 0|)*autocorr f 0 := by
  have hge := weilArch_sub_pole_ge hf hfc
  have hA : EF.gammaBracket 0=-|EF.gammaBracket 0| := by
    rw [abs_gammaBracket_zero]; exact gammaBracket_zero_eq
  rw [hA] at hge
  nlinarith

/-- **Pole-heavy tests are automatically positive.**  If `2(E² - O²) ≥ |A(0)| h(0)` then
`W_∞(h) ≥ 0`. -/
theorem weilArchRe_nonneg_of_pole_heavy (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hP : |EF.gammaBracket 0| * autocorr f 0≤
      2*((∫ u, f u*Real.cosh (u/2))^2-(∫ u, f u*Real.sinh (u/2))^2)) :
    0≤WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) := by
  have hge := weilArch_sub_pole_ge hf hfc
  have hA : EF.gammaBracket 0=-|EF.gammaBracket 0| := by
    rw [abs_gammaBracket_zero]; exact gammaBracket_zero_eq
  rw [hA] at hge
  linarith

/-- The Plancherel density `r tanh(πr)` of a compact hyperbolic surface is nonnegative. -/
theorem plancherelDensity_nonneg (r : ℝ) : 0≤r*Real.tanh (π*r) := by
  rw [Real.tanh_eq_sinh_div_cosh, ←mul_div_assoc]
  apply div_nonneg _ (Real.cosh_pos _).le
  rcases le_total 0 r with hr | hr
  · exact mul_nonneg hr (Real.sinh_nonneg_iff.mpr (by positivity))
  · exact mul_nonneg_of_nonpos_of_nonpos hr
      (Real.sinh_nonpos_iff.mpr (by nlinarith [Real.pi_pos]))

end

end RHTower.ArchimedeanAnomaly
