import GaloisForLFunctions.RHTower.PMPowerDampedMobiusSecondMoment
import GaloisForLFunctions.RHTower.ChiRamanujanGlobalSourceNeighborhoods
import Mathlib.Analysis.Complex.Schwarz

/-!
# BAG divisor-square source and uniform coalescing-pole cancellation

The complete actual divisor-square Dirichlet series equals the continued BAG
arithmetic axis. Both moving poles remain explicit. Actual zero-free disks,
the normal axis Euler product, and its vanishing first derivative supply
uniform damping-squared cancellation before any moving contour estimate.

No physical-window asymptotic, cubic near-resonance bound, or RH conclusion
is asserted here. The joint damping-height contour transfer is the next step.
-/

noncomputable section
open scoped BigOperators Topology
open Filter Set
open scoped Asymptotics
namespace RHTower.BAGTrace


def dampedSquareDirichlet (ε : ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (pmPowerDampedDivisorCoeff ε n : ℂ)^2 * (n : ℂ)^(-s)

theorem summable_dampedSquareDirichlet {ε : ℝ} (hε : 0 ≤ ε)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => (pmPowerDampedDivisorCoeff ε n : ℂ)^2 * (n : ℂ)^(-s)) := by
  have h := LSeriesSummable_of_bounded_of_one_lt_re
    (f := fun n => (pmPowerDampedDivisorCoeff ε n : ℂ)^2) (m := 1)
    (fun n _ => by
      rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg (pmPowerDampedDivisorCoeff_nonneg hε n)]
      exact pow_le_one₀ (pmPowerDampedDivisorCoeff_nonneg hε n)
        (pmPowerDampedDivisorCoeff_le_one hε n)) hs
  have hf0 : (fun n => (pmPowerDampedDivisorCoeff ε n : ℂ)^2) 0 = 0 := by
    simp [pmPowerDampedDivisorCoeff_zero]
  simp only [LSeriesSummable] at h
  exact h.congr (fun n => LSeries.term_def₀ hf0 s n)

private theorem dampedSquareTerm_mul (ε : ℝ) (s : ℂ) {m n : ℕ} (h : m.Coprime n) :
    (pmPowerDampedDivisorCoeff ε (m*n) : ℂ)^2 * ((m*n : ℕ) : ℂ)^(-s) =
      ((pmPowerDampedDivisorCoeff ε m : ℂ)^2 * (m : ℂ)^(-s))*
      ((pmPowerDampedDivisorCoeff ε n : ℂ)^2 * (n : ℂ)^(-s)) := by
  have hm := (DampedMobius.isMultiplicative_divisorSum (fun p => (p : ℝ)^(-ε))).map_mul_of_coprime h
  simp only [← pmPowerDampedDivisorCoeff_eq_divisorSum] at hm
  rw [hm, Complex.ofReal_mul, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

private theorem dampedSquare_primePower (ε : ℝ) (p : Nat.Primes) (k : ℕ) :
    pmPowerDampedDivisorCoeff ε ((p : ℕ)^(k+1)) = 1-(p : ℝ)^(-ε) := by
  rw [pmPowerDampedDivisorCoeff_eq_divisorSum,
    DampedMobius.divisorSum_apply_prime_pow _ p.property, if_neg (Nat.succ_ne_zero k)]

private theorem dampedSquare_primePowerTerm (ε : ℝ) (s : ℂ) (p : Nat.Primes) (k : ℕ) :
    (pmPowerDampedDivisorCoeff ε ((p : ℕ)^(k+1)) : ℂ)^2 *
      (((p : ℕ)^(k+1) : ℕ) : ℂ)^(-s) =
    (1-(((p : ℝ)^(-ε) : ℝ) : ℂ))^2*cubicPrimeBase p s*(cubicPrimeBase p s)^k := by
  rw [dampedSquare_primePower, Complex.ofReal_sub, Complex.ofReal_one, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul, pow_succ]
  dsimp [cubicPrimeBase]
  ring

theorem dampedSquareDirichlet_hasProd {ε : ℝ} (hε : 0 ≤ ε)
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => 1+(1-(((p : ℝ)^(-ε) : ℝ) : ℂ))^2*
      cubicPrimeBase p s/(1-cubicPrimeBase p s)) (dampedSquareDirichlet ε s) := by
  have hp := EulerProduct.eulerProduct_hasProd
    (f := fun n : ℕ => (pmPowerDampedDivisorCoeff ε n : ℂ)^2 * (n : ℂ)^(-s))
    (by simp [pmPowerDampedDivisorCoeff_one]) (fun {_ _} h => dampedSquareTerm_mul ε s h)
    (summable_dampedSquareDirichlet hε hs).norm (by simp [pmPowerDampedDivisorCoeff_zero])
  apply hp.congr_fun
  intro p
  have hn : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (by linarith)
  have ht := (hasSum_geometric_of_norm_lt_one hn).mul_left
    ((1-(((p : ℝ)^(-ε) : ℝ) : ℂ))^2*cubicPrimeBase p s)
  have hshift : Summable (fun k : ℕ => (pmPowerDampedDivisorCoeff ε ((p : ℕ)^(k+1)) : ℂ)^2 *
      (((p : ℕ)^(k+1) : ℕ) : ℂ)^(-s)) := by
    simp_rw [dampedSquare_primePowerTerm]
    exact ht.summable
  have hsum : Summable (fun k : ℕ => (pmPowerDampedDivisorCoeff ε ((p : ℕ)^k) : ℂ)^2 *
      (((p : ℕ)^k : ℕ) : ℂ)^(-s)) := (summable_nat_add_iff 1).mp hshift
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero, pmPowerDampedDivisorCoeff_one, Complex.ofReal_one, one_pow,
    Nat.cast_one, Complex.one_cpow, one_mul]
  rw [show (∑' k : ℕ, (pmPowerDampedDivisorCoeff ε ((p : ℕ)^(k+1)) : ℂ)^2 *
      (((p : ℕ)^(k+1) : ℕ) : ℂ)^(-s)) =
      (1-(((p : ℝ)^(-ε) : ℝ) : ℂ))^2*cubicPrimeBase p s*(1-cubicPrimeBase p s)⁻¹ by
        simpa only [dampedSquare_primePowerTerm] using ht.tsum_eq]
  simp only [div_eq_mul_inv]

private theorem prime_real_damping (p : Nat.Primes) (ε : ℝ) :
    cubicPrimeBase p (ε : ℂ) = (((p : ℝ)^(-ε) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (by positivity)]
  simp only [cubicPrimeBase, Complex.ofReal_neg, Complex.ofReal_natCast]

private theorem squareLocal_axis_identity {q t : ℂ}
    (hq : 1-q ≠ 0) (hqt : 1-q*t ≠ 0) (hqtt : 1-q*t^2 ≠ 0) :
    1+(1-t)^2*q/(1-q) =
      (1-(q*t)^2*(1-t)^2/(1-q*t)^2)*(1-q)⁻¹*(1-q*t^2)⁻¹*(1-q*t)^2 := by
  have he : (1-q*t)^2-(q*t)^2*(1-t)^2 =
      (1-q*t^2)*(1-q+(1-t)^2*q) := by ring
  have hb : (1-(q*t)^2*(1-t)^2/(1-q*t)^2)*(1-q*t)^2 =
      (1-q*t)^2-(q*t)^2*(1-t)^2 := by
    rw [sub_mul, one_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hqt)]
  calc _ = (1-q+(1-t)^2*q)/(1-q) := by rw [add_div, div_self hq]
    _ = ((1-q*t)^2-(q*t)^2*(1-t)^2)*(1-q)⁻¹*(1-q*t^2)⁻¹ := by
      rw [he, div_eq_mul_inv]
      calc _ = ((1-q+(1-t)^2*q)*(1-q)⁻¹)*((1-q*t^2)*(1-q*t^2)⁻¹) := by
              rw [mul_inv_cancel₀ hqtt, mul_one]
           _ = _ := by ring
    _ = _ := by rw [← hb]; ring

private theorem squareLocal_eq_axisPrimeFactor (p : Nat.Primes) {ε : ℝ}
    (hε : 0 ≤ ε) {s : ℂ} (hs : 1 < s.re) :
    1+(1-(((p : ℝ)^(-ε) : ℝ) : ℂ))^2*cubicPrimeBase p s/(1-cubicPrimeBase p s) =
      axisPrimeFactor p (s+ε) (-ε) * (1-cubicPrimeBase p s)⁻¹ *
        (1-cubicPrimeBase p (s+2*ε))⁻¹ * (1-cubicPrimeBase p (s+ε))^2 := by
  have h1 := one_sub_cubicPrimeBase_ne_zero p (s := s) (by linarith)
  have h2 := one_sub_cubicPrimeBase_ne_zero p (s := s+ε) (by simp only [Complex.add_re, Complex.ofReal_re]; linarith)
  have h3 := one_sub_cubicPrimeBase_ne_zero p (s := s+2*ε)
    (by simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]; linarith)
  have hb : cubicPrimeBase p (s+2*ε) = cubicPrimeBase p s * (cubicPrimeBase p ε)^2 := by
    rw [pow_two, cubicPrimeBase_mul, cubicPrimeBase_mul]
    congr 1
    ring
  rw [← prime_real_damping, axisPrimeFactor, axisRegularFactor,
    cubicPrimeBase_inv, neg_neg, hb, ← cubicPrimeBase_mul]
  rw [← cubicPrimeBase_mul] at h2
  rw [hb] at h3
  exact squareLocal_axis_identity h1 h2 h3

/-- Exact actual divisor-square source as the BAG arithmetic axis continuation. -/
theorem dampedSquareDirichlet_eq_axis {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1/16)
    {s : ℂ} (hs : 1 < s.re) :
    dampedSquareDirichlet ε s = axisEulerCorrection (s+ε) (-ε) *
      riemannZeta s * riemannZeta (s+2*ε) / riemannZeta (s+ε)^2 := by
  have hs1 : 1 < (s+(ε : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hs2 : 1 < (s+2*(ε : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
    linarith
  have hm : (s+(ε : ℂ),-(ε : ℂ)) ∈ axisTube := by
    constructor
    · linarith
    · simpa only [Complex.neg_re, Complex.ofReal_re, abs_neg, abs_of_nonneg hε] using hε1
  have hz : HasProd (fun p : Nat.Primes => 1-cubicPrimeBase p (s+ε))
      (riemannZeta (s+ε))⁻¹ := by
    have h := Filter.Tendsto.inv₀ (riemannZeta_eulerProduct_hasProd hs1)
      (riemannZeta_ne_zero_of_one_le_re hs1.le)
    simpa only [HasProd, SummationFilter.unconditional, ← Finset.prod_inv_distrib,
      inv_inv, cubicPrimeBase] using h
  have hp := ((((hasProdLocallyUniformlyOn_axisPrimeFactor.hasProd hm).mul
      (riemannZeta_eulerProduct_hasProd hs)).mul
      (riemannZeta_eulerProduct_hasProd hs2)).mul (hz.mul hz))
  have hp' : HasProd (fun p : Nat.Primes =>
      1+(1-(((p : ℝ)^(-ε) : ℝ) : ℂ))^2*cubicPrimeBase p s/(1-cubicPrimeBase p s))
      (axisEulerCorrection (s+ε) (-ε) * riemannZeta s * riemannZeta (s+2*ε) *
        ((riemannZeta (s+ε))⁻¹ * (riemannZeta (s+ε))⁻¹)) := by
    apply hp.congr_fun
    intro p
    simpa only [pow_two, cubicPrimeBase] using squareLocal_eq_axisPrimeFactor p hε hs
  have he := (dampedSquareDirichlet_hasProd hε hs).unique hp'
  simpa only [div_eq_mul_inv, pow_two, mul_inv_rev] using he

/-- The actual pole-removed arithmetic axis normalized by its central value. -/
def dampedSquareRegularSource (σ α : ℂ) : ℂ :=
  regularAxisSource σ α / zetaResidueFactor σ^2

theorem dampedSquareRegularSource_zero {σ : ℂ} (hσ : zetaResidueFactor σ ≠ 0) :
    dampedSquareRegularSource σ 0 = 1 := by
  simp only [dampedSquareRegularSource, regularAxisSource_zero, residuePair,
    add_zero, sub_zero, ← pow_two]
  exact div_self (pow_ne_zero 2 hσ)

theorem hasDerivAt_dampedSquareRegularSource_zero {σ : ℂ} (hσ : 7/8 < σ.re) :
    HasDerivAt (dampedSquareRegularSource σ) 0 0 := by
  have hp0 : HasDerivAt (fun α : ℂ => σ+α) 1 0 :=
    (hasDerivAt_id (0 : ℂ)).const_add σ
  have hm0 : HasDerivAt (fun α : ℂ => σ-α) (-1) 0 :=
    (hasDerivAt_id (0 : ℂ)).const_sub σ
  have hp : HasDerivAt (fun α : ℂ => zetaResidueFactor (σ+α))
      (deriv zetaResidueFactor σ) 0 := by
    simpa only [add_zero, mul_one, Function.comp_def] using!
      ((differentiable_zetaResidueFactor (σ+0)).hasDerivAt.comp 0 hp0)
  have hm : HasDerivAt (fun α : ℂ => zetaResidueFactor (σ-α))
      (-deriv zetaResidueFactor σ) 0 := by
    simpa only [sub_zero, mul_neg, mul_one, Function.comp_def] using!
      ((differentiable_zetaResidueFactor (σ-0)).hasDerivAt.comp 0 hm0)
  have h := ((hp.mul hm).mul (hasDerivAt_axisEulerCorrection_zero hσ)).div_const
    (zetaResidueFactor σ^2)
  have he : deriv zetaResidueFactor σ*zetaResidueFactor σ+
      zetaResidueFactor σ*(-deriv zetaResidueFactor σ) = 0 := by ring
  simpa only [dampedSquareRegularSource, regularAxisSource, residuePair, Pi.mul_apply,
    add_zero, sub_zero, he, zero_mul, mul_zero, zero_add, zero_div] using! h

/-- Two moving poles remain explicit; their merger is never replaced by an iterated limit. -/
theorem dampedSquareDirichlet_eq_twoPole {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε < 1/16)
    {s : ℂ} (hs : 1 < s.re) :
    dampedSquareDirichlet ε s =
      (1+(ε : ℂ)^2/((s-1)*(s+2*ε-1))) * dampedSquareRegularSource (s+ε) (-ε) := by
  have hs1 : 1 < (s+(ε : ℂ)).re := by simp only [Complex.add_re, Complex.ofReal_re]; linarith
  have hs2 : 1 < (s+2*(ε : ℂ)).re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero, sub_zero]
    linarith
  have hn0 : s ≠ 1 := by intro h; simp [h] at hs
  have hn1 : s+(ε : ℂ) ≠ 1 := by intro h; simp [h] at hs1
  have hn2 : s+2*(ε : ℂ) ≠ 1 := by intro h; simp [h] at hs2
  have hz := riemannZeta_ne_zero_of_one_le_re hs1.le
  rw [dampedSquareDirichlet_eq_axis hε hε1 hs]
  simp only [dampedSquareRegularSource, regularAxisSource, residuePair]
  rw [show s+(ε : ℂ)+(-ε)=s by ring, show s+(ε : ℂ)-(-ε)=s+2*ε by ring,
    zetaResidueFactor_of_ne hn0, zetaResidueFactor_of_ne hn1, zetaResidueFactor_of_ne hn2]
  have ha : s-1 ≠ 0 := sub_ne_zero.mpr hn0
  have hb : s+2*(ε : ℂ)-1 ≠ 0 := sub_ne_zero.mpr hn2
  have hc : s+(ε : ℂ)-1 ≠ 0 := sub_ne_zero.mpr hn1
  have hratio : 1+(ε : ℂ)^2/((s-1)*(s+2*ε-1)) =
      (s+ε-1)^2/((s-1)*(s+2*ε-1)) := by
    calc _ = ((s-1)*(s+2*ε-1)+(ε : ℂ)^2)/((s-1)*(s+2*ε-1)) := by
            rw [add_div, div_self (mul_ne_zero ha hb)]
         _ = _ := by congr 1; ring
  rw [hratio]
  simp only [mul_pow, div_eq_mul_inv, mul_inv, ← inv_pow]
  have hca := mul_inv_cancel₀ ha
  have hcb := mul_inv_cancel₀ hb
  have hcc : (s+ε-1)^2*((s+ε-1)⁻¹)^2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hc, one_pow]
  calc _ = (axisEulerCorrection (s+ε) (-ε) * riemannZeta s * riemannZeta (s+2*ε) *
      ((riemannZeta (s+ε))⁻¹)^2) * ((s-1)*(s-1)⁻¹) * ((s+2*ε-1)*(s+2*ε-1)⁻¹) *
        ((s+ε-1)^2*((s+ε-1)⁻¹)^2) := by rw [hca,hcb,hcc]; ring
    _ = _ := by ring

private theorem differentiableOn_dampedSquareRegularSource {σ : ℂ}
    (hσ : 7/8 < σ.re) :
    DifferentiableOn ℂ (dampedSquareRegularSource σ) axisFrequencyDomain := by
  have hg : Differentiable ℂ (fun α : ℂ => ![σ,α]) := by
    apply differentiable_pi.mpr
    intro i
    fin_cases i
    · exact differentiable_const _
    · exact differentiable_id
  have hm : MapsTo (fun α : ℂ => ![σ,α]) axisFrequencyDomain axisCoordinateTube := by
    intro α hα
    exact ⟨hσ,hα⟩
  have h := analyticOnNhd_regularAxisSource.differentiableOn.comp hg.differentiableOn hm
  exact h.div_const (zetaResidueFactor σ^2)

private theorem norm_sub_le_square_of_zero_deriv {f : ℂ → ℂ} {R M : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hd : HasDerivAt f 0 0)
    (hb : ∀ z ∈ Metric.ball 0 R, ‖f z-f 0‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.ball 0 R) :
    ‖f z-f 0‖ ≤ M*(‖z‖/R)^2 := by
  have ho : (fun w => f w-f 0) =o[𝓝 (0 : ℂ)] (fun w => ‖w-0‖^(1 : ℕ)) := by
    simpa only [sub_zero, smul_zero, pow_one] using hd.isLittleO.norm_right
  have h := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hf
    (fun w hw => by simpa only [Metric.mem_closedBall, dist_eq_norm] using hb w hw) ho hz
  simpa only [dist_eq_norm, sub_zero] using h

/-- Uniform double cancellation of the actual normalized axis on the source's
zero-free disks. This retains damping squared before the moving contour estimate. -/
theorem exists_dampedSquareRegularSource_quadratic_bound :
    ∃ d ∈ Set.Ioc (0 : ℝ) (1/128), ∃ C > 0, ∀ (t : ℝ) (σ α : ℂ),
      dist σ (1+(t : ℂ)*Complex.I) ≤ d/(1+|t|)^9 →
      ‖α‖ ≤ d/(1+|t|)^9 →
      ‖dampedSquareRegularSource σ α-1‖ ≤ C*(1+|t|)^54*‖α‖^2 := by
  obtain ⟨c,hc,M,hM,hF⟩ := exists_residue_global_polynomial_disks
  obtain ⟨H,hH,hK⟩ := exists_axisEulerCorrection_bound
  let d := min (c/8) (1/128)
  have hd : 0 < d := lt_min (div_pos hc.1 (by norm_num)) (by norm_num)
  have hdc : d ≤ c/8 := min_le_left _ _
  have hd1 : d ≤ 1/128 := min_le_right _ _
  let C := (M^4*H+1)/d^2
  refine ⟨d,⟨hd,hd1⟩,C,by dsimp [C]; positivity,?_⟩
  intro t σ α hσ hα
  let T := 1+|t|
  let center : ℂ := 1+(t : ℂ)*Complex.I
  let r := 2*d/T^9
  have hT : 1 ≤ T := le_add_of_nonneg_right (abs_nonneg t)
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hTp : 1 ≤ T^9 := one_le_pow₀ hT
  have hsmall : d/T^9 ≤ d := div_le_self hd.le hTp
  have hr : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1/64 := by
    calc r ≤ 2*d := div_le_self (by positivity) hTp
         _ ≤ 1/64 := by linarith
  have hsr : 7/8 < σ.re := by
    have h := (Complex.abs_re_le_norm (σ-center)).trans
      ((show ‖σ-center‖ ≤ d/T^9 from by simpa only [center,T,dist_eq_norm] using hσ).trans hsmall)
    have hh : |σ.re-1| ≤ d := by simpa [center] using h
    have := neg_le_of_abs_le hh
    linarith
  have hcommon (z : ℂ) (hz : dist z σ ≤ r) :
      z ∈ Metric.closedBall center (c/T^9) := by
    change dist z center ≤ c/T^9
    calc dist z center ≤ dist z σ+dist σ center := dist_triangle _ _ _
      _ ≤ r+d/T^9 := add_le_add hz hσ
      _ = (3*d)/T^9 := by dsimp [r]; ring
      _ ≤ c/T^9 := by gcongr; linarith
  have hfσ := hF 1 (by norm_num) t σ (hcommon σ (by simpa using hr.le))
  have hzero := dampedSquareRegularSource_zero hfσ.1
  have hfreq (β : ℂ) (hβ : β ∈ Metric.ball 0 r) : β ∈ axisFrequencyDomain := by
    have hb : ‖β‖ < r := by simpa using hβ
    change |β.re| < 1/16
    exact (Complex.abs_re_le_norm β).trans_lt (hb.trans_le (by linarith))
  have hdiff := (differentiableOn_dampedSquareRegularSource hsr).mono hfreq
  have hbound (β : ℂ) (hβ : β ∈ Metric.ball 0 r) :
      ‖dampedSquareRegularSource σ β‖ ≤ M^4*H*T^36 := by
    have hb : ‖β‖ ≤ r := by simpa using (Metric.ball_subset_closedBall hβ)
    have hp := hF 1 (by norm_num) t (σ+β) (hcommon _ (by simpa [dist_eq_norm] using hb))
    have hm := hF 1 (by norm_num) t (σ-β) (hcommon _ (by simpa [dist_eq_norm] using hb))
    have hk := hK σ β ⟨hsr,hfreq β hβ⟩
    calc ‖dampedSquareRegularSource σ β‖ =
        ‖zetaResidueFactor (σ+β)‖*‖zetaResidueFactor (σ-β)‖*
          ‖axisEulerCorrection σ β‖*‖(zetaResidueFactor σ)⁻¹‖^2 := by
            simp [dampedSquareRegularSource, regularAxisSource, residuePair,
              norm_pow, norm_inv, div_eq_mul_inv, inv_pow]
      _ ≤ (M*T^9)*(M*T^9)*H*(M*T^9)^2 := by
        gcongr
        · exact hp.2.1
        · exact hm.2.1
        · exact hfσ.2.2
      _ = M^4*H*T^36 := by ring
  have hsub (β : ℂ) (hβ : β ∈ Metric.ball 0 r) :
      ‖dampedSquareRegularSource σ β-dampedSquareRegularSource σ 0‖ ≤
        (M^4*H+1)*T^36 := by
    rw [hzero]
    calc _ ≤ ‖dampedSquareRegularSource σ β‖+1 := by simpa using norm_sub_le (dampedSquareRegularSource σ β) 1
      _ ≤ M^4*H*T^36+T^36 := add_le_add (hbound β hβ) (one_le_pow₀ hT)
      _ = _ := by ring
  have hαr : α ∈ Metric.ball 0 r := by
    simp only [Metric.mem_ball, dist_zero_right]
    exact hα.trans_lt (by dsimp [r]; apply div_lt_div_of_pos_right _ (by positivity); linarith)
  have hsq := norm_sub_le_square_of_zero_deriv hdiff
    (hasDerivAt_dampedSquareRegularSource_zero hsr) hsub hαr
  rw [hzero] at hsq
  calc _ ≤ (M^4*H+1)*T^36*(‖α‖/r)^2 := hsq
    _ ≤ (M^4*H+1)*T^36*(‖α‖/(d/T^9))^2 := by
      have hden : d/T^9 ≤ r := by dsimp [r]; gcongr; linarith
      have hden0 : 0 < d/T^9 := by positivity
      gcongr
    _ = C*T^54*‖α‖^2 := by dsimp [C]; field_simp

/-- Actual two-pole continuation, agreeing with the complete divisor series on Re s>1. -/
def dampedSquareContinuation (ε s : ℂ) : ℂ :=
  (1+ε^2/((s-1)*(s+2*ε-1))) * dampedSquareRegularSource (s+ε) (-ε)

theorem dampedSquareDirichlet_eq_continuation {ε : ℝ} (hε : 0 ≤ ε)
    (hε1 : ε < 1/16) {s : ℂ} (hs : 1 < s.re) :
    dampedSquareDirichlet ε s = dampedSquareContinuation ε s :=
  dampedSquareDirichlet_eq_twoPole hε hε1 hs

/-- Damping squared survives the complete continued source on the actual zero-free disks.
The explicit reciprocal retains both moving poles. -/
theorem exists_dampedSquareContinuation_remainder_bound :
    ∃ d ∈ Set.Ioc (0 : ℝ) (1/128), ∃ C > 0, ∀ (t : ℝ) (s ε : ℂ),
      dist (s+ε) (1+(t : ℂ)*Complex.I) ≤ d/(1+|t|)^9 →
      ‖ε‖ ≤ d/(1+|t|)^9 →
      ‖dampedSquareContinuation ε s-1‖ ≤
        C*‖ε‖^2*(1+|t|)^54*(1+‖((s-1)*(s+2*ε-1))⁻¹‖) := by
  obtain ⟨d,hd,C,hC,hb⟩ := exists_dampedSquareRegularSource_quadratic_bound
  refine ⟨d,hd,C+1,by linarith,?_⟩
  intro t s ε hs hε
  let T := 1+|t|
  let Q := dampedSquareRegularSource (s+ε) (-ε)
  let D := ((s-1)*(s+2*ε-1))⁻¹
  have hT : 1 ≤ T := le_add_of_nonneg_right (abs_nonneg t)
  have hT9 : 1 ≤ T^9 := one_le_pow₀ hT
  have hT54 : 1 ≤ T^54 := one_le_pow₀ hT
  have he1 : ‖ε‖ ≤ 1 := hε.trans ((div_le_self hd.1.le hT9).trans (by linarith [hd.2]))
  have he2 : ‖ε‖^2 ≤ 1 := pow_le_one₀ (norm_nonneg _) he1
  have hq : ‖Q-1‖ ≤ C*T^54*‖ε‖^2 := by
    simpa only [Q,norm_neg] using hb t (s+ε) (-ε) hs (by simpa only [norm_neg] using hε)
  have hqnorm : ‖Q‖ ≤ (C+1)*T^54 := by
    calc ‖Q‖ ≤ ‖Q-1‖+1 := by simpa using norm_le_norm_sub_add Q 1
      _ ≤ C*T^54*‖ε‖^2+1 := by linarith
      _ ≤ C*T^54+T^54 := add_le_add
        (mul_le_of_le_one_right (by positivity) he2) hT54
      _ = _ := by ring
  have he : dampedSquareContinuation ε s-1 = (Q-1)+ε^2*D*Q := by
    dsimp [dampedSquareContinuation,Q,D]
    ring
  rw [he]
  calc ‖(Q - 1) + ε^2 * D * Q‖ ≤ ‖Q - 1‖ + ‖ε^2 * D * Q‖ := norm_add_le _ _
    _ = ‖Q - 1‖ + ‖ε‖^2 * ‖D‖ * ‖Q‖ := by rw [norm_mul, norm_mul, norm_pow]
    _ ≤ C*T^54*‖ε‖^2 + ‖ε‖^2*‖D‖*((C+1)*T^54) := by gcongr
    _ ≤ (C+1)*‖ε‖^2*T^54*(1+‖D‖) := by
      nlinarith [mul_nonneg (sq_nonneg ‖ε‖) (pow_nonneg (by positivity : 0 ≤ T) 54)]

end RHTower.BAGTrace
