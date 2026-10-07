import GaloisForLFunctions.RHTower.WeilPolarConeExposedPoint
import GaloisForLFunctions.RHTower.RiemannAutocorrFourier
import Mathlib.Analysis.Polynomial.Basic

/-!
# Uniform positive tails for the polar exposing family

For the literal Riemann kernel, all nonzero pole-cancelling shifts `0 < c ≤ 1`
have a common positive autocorrelation tail. The stronger capstone proves
`D * c^4 * exp (-(C * exp y)) ≤ polarExposingKernel c y` with fixed positive
constants and one common threshold.

The proof retains the full theta series and every negative autocorrelation
contribution. A positive Green average of `(D² - 1/4)Φ` removes the small-shift
degeneracy before estimating the tail. This is a source theorem; the universal
matched-family energy lower bound of WP02 remains open.

Paper proof: `docs/reports/weil-work/results/02-exposing-ray/POLAR-UNIFORM-TAIL-PROOF.md`.
-/

open Real Polynomial MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower.ExposingRaySmallShift

private def polarPoly : ℝ[X] := riemannKernelPoly 2 - C (1 / 4) * riemannKernelPoly 0

/-- The actual polar differential source `(D²-1/4)Φ`. -/
def polarDerivative (x : ℝ) : ℝ := cuspSeries polarPoly x

private theorem poly_top : polarPoly.coeff 4 = 16 * π ^ 4 := by
  have h0 : (riemannKernelPoly 0).coeff 4 = 0 :=
    coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (natDegree_riemannKernelPoly_le 0) (by norm_num))
  have h2 := coeff_riemannKernelPoly_top 2
  norm_num at h2
  simp only [polarPoly, coeff_sub, coeff_C_mul, h0, mul_zero, sub_zero]
  rw [h2]
  ring

private theorem poly_degree : polarPoly.natDegree = 4 := by
  have hu : polarPoly.natDegree ≤ 4 := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_riemannKernelPoly_le 2
    · exact (natDegree_C_mul_le _ _).trans ((natDegree_riemannKernelPoly_le 0).trans (by norm_num))
  have hlo : 4 ≤ polarPoly.natDegree := le_natDegree_of_ne_zero (by rw [poly_top]; positivity)
  exact hu.antisymm hlo

theorem polarDerivative_eq (x : ℝ) :
    polarDerivative x = (riemannKernelDeriv 2 x).re - riemannKernelReal x / 4 := by
  unfold polarDerivative polarPoly
  rw [cuspSeries_sub, cuspSeries_smul]
  have h0 : cuspSeries (riemannKernelPoly 0) x = riemannKernelReal x := by
    have h := riemannPhiKernel_eq_ofReal x
    rw [riemannPhiKernel_eq_cuspSeries] at h
    exact Complex.ofReal_injective h
  rw [h0]
  change cuspSeries (riemannKernelPoly 2) x - (1 / 4) * riemannKernelReal x = _
  simp only [riemannKernelDeriv, Complex.ofReal_re]
  dsimp only [riemannKernelPoly]
  ring

theorem polarDerivative_even (x : ℝ) : polarDerivative (-x) = polarDerivative x := by
  rw [polarDerivative_eq, polarDerivative_eq, riemannKernelDeriv_neg]
  simp only [neg_one_sq, one_mul]
  simp [riemannKernelReal, abs_neg]

private theorem polarDerivative_abs (x : ℝ) : polarDerivative |x| = polarDerivative x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, polarDerivative_even]

theorem polarDerivative_continuous : Continuous polarDerivative := continuous_cuspSeries _

/-- A full-series theta lower bound outside a fixed compact interval. -/
theorem polarDerivative_lower :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x : ℝ, R ≤ |x| →
      exp (-(π * exp (2 * |x|))) ≤ polarDerivative x := by
  have hpoly : Tendsto (fun v : ℝ => polarPoly.eval v) atTop atTop :=
    polarPoly.tendsto_atTop_of_leadingCoeff_nonneg
      (natDegree_pos_iff_degree_pos.mp (by rw [poly_degree]; norm_num))
      (by rw [Polynomial.leadingCoeff, poly_degree, poly_top]; positivity)
  obtain ⟨V, hV⟩ := eventually_atTop.mp (hpoly.eventually_ge_atTop 1)
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))).eventually_ge_atTop V)
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hu := abs_nonneg x
  have hVx : V ≤ exp (2 * |x|) := hR _ ((le_max_left _ _).trans hx)
  have hall (n : ℕ) : 1 ≤ polarPoly.eval (((n + 1 : ℕ) : ℝ) ^ 2 * exp (2 * |x|)) := by
    apply hV
    have hn : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hn2 := one_le_pow₀ (n := 2) hn
    exact hVx.trans (by nlinarith [exp_pos (2 * |x|)])
  have hterm (n : ℕ) : 0 ≤ cuspTerm polarPoly (n+1) |x| := by
    unfold cuspTerm
    exact mul_nonneg (mul_nonneg (exp_pos _).le (le_trans (by norm_num) (hall n))) (exp_pos _).le
  have hsum := (summable_cuspTerm polarPoly |x|).le_tsum 0 (fun n _ => hterm n)
  have hfirst : exp (-(π * exp (2 * |x|))) ≤ cuspTerm polarPoly 1 |x| := by
    unfold cuspTerm
    simp only [Nat.cast_one, one_pow, one_mul]
    have hP := hall 0
    simp only [Nat.zero_add, Nat.cast_one, one_pow, one_mul] at hP
    have hE : 1 ≤ exp (|x| / 2) := Real.one_le_exp (by positivity)
    have hp := one_le_mul_of_one_le_of_one_le hE hP
    rw [neg_mul]
    exact le_mul_of_one_le_left (exp_pos _).le hp
  rw [← polarDerivative_abs x]
  exact hfirst.trans hsum

/-- A full-series upper envelope; the polynomial derivative factor is paid analytically. -/
theorem polarDerivative_upper :
    ∃ B : ℝ, 0 < B ∧ ∀ x : ℝ,
      |polarDerivative x| ≤ B * exp (-((π / 2) * exp (2 * |x|))) * exp (-|x|) := by
  let d : ℝ := π / 2
  have hd : 0 < d := by dsimp [d]; positivity
  have hC := cuspDecayConst_nonneg polarPoly
  let B : ℝ := (cuspDecayConst polarPoly + 1) * (120 / d ^ 5)
  refine ⟨B, by dsimp [B]; positivity, fun x => ?_⟩
  let u := |x|
  let V := exp (2 * u)
  have hu : 0 ≤ u := abs_nonneg x
  have hX : 0 < V := exp_pos _
  have hb := abs_cuspSeries_le polarPoly hu
  rw [poly_degree] at hb
  have he : exp (u / 2) * exp (2 * (4 : ℕ) * u) ≤ V ^ 5 * exp (-u) := by
    dsimp [V]
    rw [← exp_nat_mul, ← exp_add, ← exp_add]
    exact exp_le_exp.mpr (by norm_num; linarith)
  have ht := Real.pow_div_factorial_le_exp (x := d * V) (by positivity) 5
  norm_num [Nat.factorial] at ht
  have hpay : V ^ 5 * exp (-(d * V)) ≤ 120 / d ^ 5 := by
    have heq : exp (d*V) * exp (-(d*V)) = 1 := by rw [← exp_add]; simp
    rw [le_div_iff₀ (by positivity)]
    nlinarith [mul_pow d V 5, exp_pos (-(d*V))]
  have heq : exp (-(π * V)) = exp (-(d * V)) * exp (-(d * V)) := by
    rw [← exp_add]; congr 1; dsimp [d]; ring
  rw [← polarDerivative_abs x]
  change |cuspSeries polarPoly u| ≤ _
  calc _ ≤ (cuspDecayConst polarPoly + 1) *
        (exp (u / 2) * exp (2 * (4 : ℕ) * u)) * exp (-(π * V)) := by
        apply hb.trans
        dsimp [V]
        simp only [neg_mul, mul_assoc]
        gcongr
        linarith
    _ ≤ (cuspDecayConst polarPoly + 1) * (V ^ 5 * exp (-u)) * exp (-(π * V)) := by gcongr
    _ = (cuspDecayConst polarPoly + 1) * (V ^ 5 * exp (-(d*V))) *
        exp (-(d*V)) * exp (-u) := by rw [heq]; ring
    _ ≤ (cuspDecayConst polarPoly + 1) * (120 / d ^ 5) * exp (-(d*V)) * exp (-u) := by gcongr
    _ = _ := rfl


/-- Autocorrelation of the actual polar differential source. -/
def polarDerivativeAutocorr (y : ℝ) : ℝ := ∫ t : ℝ, polarDerivative t * polarDerivative (t-y)

private theorem simple_envelope {f : ℝ → ℝ} {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (h : ∀ x, |f x| ≤ B * exp (-(a*exp (2*|x|))) * exp (-|x|))
    (x : ℝ) : |f x| ≤ B * exp (-|x|) := by
  have he : exp (-(a*exp (2*|x|))) ≤ 1 := exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  exact (h x).trans (by
    calc _ ≤ B * 1 * exp (-|x|) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he hB.le) (exp_pos _).le
      _ = _ := by ring)

/-- Absolute tail envelopes give integrability of every signed correlation. -/
theorem general_corr_integrable {f : ℝ → ℝ} {a B : ℝ} (ha : 0 < a) (hB : 0 < B)
    (hf : Continuous f)
    (h : ∀ x, |f x| ≤ B * exp (-(a*exp (2*|x|))) * exp (-|x|)) (y : ℝ) :
    Integrable (fun t => f t * f (t-y)) := by
  apply Integrable.mono' (integrable_exp_neg_abs.const_mul (B^2))
    (hf.mul (hf.comp (continuous_id.sub continuous_const))).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  simp only [Pi.mul_apply, Function.comp_apply, Pi.sub_apply, id_eq]
  rw [Real.norm_eq_abs, abs_mul]
  have ht := simple_envelope ha hB h t
  have hty := simple_envelope ha hB h (t-y)
  have hs : exp (-|t-y|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg (t-y)])
  calc _ ≤ (B*exp (-|t|))*(B*exp (-|t-y|)) := mul_le_mul ht hty (abs_nonneg _) (by positivity)
    _ ≤ (B*exp (-|t|))*(B*1) := by gcongr
    _ = _ := by ring

private theorem negative_part_bound {f : ℝ → ℝ} {a b B R : ℝ}
    (ha : 0 < a) (hB : 0 < B)
    (hu : ∀ x, |f x| ≤ B * exp (-(a*exp (2*|x|))) * exp (-|x|))
    (hl : ∀ x, R ≤ |x| → exp (-(b*exp (2*|x|))) ≤ f x)
    (t y : ℝ) :
    -(B^2 * exp (-(a*exp (2*(y-R)))) * exp (-|t|)) ≤
      f t * f (t-y) := by
  by_cases hp : 0 ≤ f t * f (t-y)
  · exact le_trans (neg_nonpos.mpr (by positivity)) hp
  have hclose : |t| < R ∨ |t-y| < R := by
    by_contra hc
    push Not at hc
    have h1 := (exp_pos _).le.trans (hl t hc.1)
    have h2 := (exp_pos _).le.trans (hl (t-y) hc.2)
    exact hp (mul_nonneg h1 h2)
  have htri : y ≤ |t| + |t-y| := by
    calc y ≤ |y| := le_abs_self _
      _ = |t-(t-y)| := by congr 1; ring
      _ ≤ _ := abs_sub _ _
  have hex : exp (2*(y-R)) ≤ exp (2*|t|) + exp (2*|t-y|) := by
    rcases hclose with hc | hc
    · have he := exp_le_exp.mpr (show 2*(y-R) ≤ 2*|t-y| by linarith)
      linarith [exp_pos (2*|t|)]
    · have he := exp_le_exp.mpr (show 2*(y-R) ≤ 2*|t| by linarith)
      linarith [exp_pos (2*|t-y|)]
  have hexp : exp (-(a*exp (2*|t|))) * exp (-(a*exp (2*|t-y|))) ≤
      exp (-(a*exp (2*(y-R)))) := by
    rw [← exp_add]
    apply exp_le_exp.mpr
    nlinarith [ha]
  have hs : exp (-|t-y|) ≤ 1 := exp_le_one_iff.mpr (by linarith [abs_nonneg (t-y)])
  have habs : |f t * f (t-y)| ≤
      B^2 * exp (-(a*exp (2*(y-R)))) * exp (-|t|) := by
    rw [abs_mul]
    calc _ ≤ (B*exp (-(a*exp (2*|t|)))*exp (-|t|))*
          (B*exp (-(a*exp (2*|t-y|)))*exp (-|t-y|)) :=
        mul_le_mul (hu t) (hu (t-y)) (abs_nonneg _) (by positivity)
      _ = B^2*(exp (-(a*exp (2*|t|)))*exp (-(a*exp (2*|t-y|))))*
          exp (-|t|)*exp (-|t-y|) := by ring
      _ ≤ B^2*exp (-(a*exp (2*(y-R))))*exp (-|t|)*1 := by gcongr
      _ = _ := by ring
  exact (abs_le.mp habs).1

/-- A squared-exponential tail error is eventually below a fixed exponential-scale main term. -/
theorem error_absorbed (a b B R : ℝ) (ha : 0 < a) :
    ∀ᶠ y : ℝ in atTop, 2*B^2*exp (-(a*exp (2*(y-R)))) ≤
      exp (-(2*b*exp 2*exp y)) := by
  let k := a*exp (-(2*R))
  let β := 2*b*exp 2
  have hk : 0 < k := by dsimp [k]; positivity
  have he := Real.tendsto_exp_atTop.eventually_ge_atTop ((β+1)/k)
  have hs : Tendsto (fun y : ℝ => 2*B^2*exp (-exp y)) atTop (𝓝 0) := by
    have hz := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp Real.tendsto_exp_atTop)
    simpa using hz.const_mul (2*B^2)
  filter_upwards [he, hs.eventually_lt_const (by norm_num : (0 : ℝ)<1)] with y hy hsmall
  have hkX : β+1 ≤ k*exp y := by
    have := (div_le_iff₀ hk).mp hy
    nlinarith
  have hpoly : (β+1)*exp y ≤ k*(exp y)^2 := by
    have := mul_le_mul_of_nonneg_right hkX (exp_pos y).le
    nlinarith
  have heq : a*exp (2*(y-R)) = k*(exp y)^2 := by
    dsimp [k]
    rw [show 2*(y-R)=-(2*R)+(y+y) by ring, exp_add, exp_add]
    ring
  rw [heq]
  have hbound : exp (-(k*(exp y)^2)) ≤ exp (-exp y)*exp (-(β*exp y)) := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by nlinarith)
  calc _ ≤ 2*B^2*(exp (-exp y)*exp (-(β*exp y))) := by gcongr
    _ = (2*B^2*exp (-exp y))*exp (-(β*exp y)) := by ring
    _ ≤ 1*exp (-(β*exp y)) := mul_le_mul_of_nonneg_right hsmall.le (exp_pos _).le
    _ = _ := by simp [β, mul_assoc]

/-- Uniform signed-correlation estimate from common two-sided tail envelopes. -/
private theorem uniform_corr_lower (a b B R : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hB : 0 < B) (hR : 0 ≤ R) :
    ∃ Y : ℝ, ∀ f : ℝ → ℝ, Continuous f →
      (∀ x, |f x| ≤ B * exp (-(a*exp (2*|x|))) * exp (-|x|)) →
      (∀ x, R ≤ |x| → exp (-(b*exp (2*|x|))) ≤ f x) →
      ∀ y : ℝ, Y ≤ y → exp (-(2*b*exp 2*exp y)) ≤ ∫ t : ℝ, f t*f (t-y) := by
  obtain ⟨Y, hY⟩ := eventually_atTop.mp (error_absorbed a b B R ha)
  refine ⟨max Y (2*(R+1)), fun f hf hu hl y hy => ?_⟩
  have hyR : 2*(R+1) ≤ y := (le_max_right _ _).trans hy
  let L := exp (-(2*b*exp 2*exp y))
  let E := B^2*exp (-(a*exp (2*(y-R))))
  have hmid : ∀ t ∈ Ioc (y/2-1) (y/2+1), L ≤ f t*f (t-y) := by
    intro t ht
    have htR : R ≤ |t| := le_trans (by linarith [ht.1]) (le_abs_self t)
    have htyR : R ≤ |t-y| := by
      have := neg_le_abs (t-y)
      linarith [ht.2]
    have htU : |t| ≤ y/2+1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have htyU : |t-y| ≤ y/2+1 := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have h1 := exp_le_exp.mpr (show 2*|t| ≤ y+2 by linarith)
    have h2 := exp_le_exp.mpr (show 2*|t-y| ≤ y+2 by linarith)
    rw [exp_add] at h1 h2
    have hex : L ≤ exp (-(b*exp (2*|t|)))*exp (-(b*exp (2*|t-y|))) := by
      rw [← exp_add]
      apply exp_le_exp.mpr
      nlinarith [hb]
    exact hex.trans (mul_le_mul (hl t htR) (hl (t-y) htyR) (exp_pos _).le
      ((exp_pos _).le.trans (hl t htR)))
  have hnonneg : ∀ t, 0 ≤ f t*f (t-y)+E*exp (-|t|) := by
    intro t
    have := negative_part_bound ha hB hu hl t y
    dsimp [E]
    linarith
  have hi := (general_corr_integrable ha hB hf hu y).add (integrable_exp_neg_abs.const_mul E)
  have hm := setIntegral_mono_on (integrableOn_const (by simp)) hi.integrableOn measurableSet_Ioc
    (fun t ht => (hmid t ht).trans (le_add_of_nonneg_right (by dsimp [E]; positivity)))
  have hc : (∫ t in Ioc (y/2-1) (y/2+1), L) = 2*L := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    ring
  rw [hc] at hm
  have hg := hm.trans (setIntegral_le_integral hi (Eventually.of_forall hnonneg))
  simp only [Pi.add_apply] at hg
  rw [integral_add (general_corr_integrable ha hB hf hu y) (integrable_exp_neg_abs.const_mul E), integral_const_mul,
    integral_exp_neg_abs] at hg
  have herr := hY y ((le_max_left _ _).trans hy)
  change L ≤ _
  change 2*L ≤ (∫ t : ℝ, f t * f (t-y)) + E*2 at hg
  dsimp [E, L] at hg ⊢
  linarith

/-- Integrability of the actual signed differential autocorrelation. -/
theorem corr_integrable (y : ℝ) :
    Integrable (fun t => polarDerivative t * polarDerivative (t-y)) := by
  obtain ⟨B, hB, hu⟩ := polarDerivative_upper
  exact general_corr_integrable (by positivity) hB polarDerivative_continuous hu y

/-- The signed polar differential autocorrelation has an explicit positive tail. -/
theorem polarDerivativeAutocorr_lower :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y →
      exp (-(2*π*exp 2*exp y)) ≤ polarDerivativeAutocorr y := by
  obtain ⟨B, hB, hu⟩ := polarDerivative_upper
  obtain ⟨R, hR, hl⟩ := polarDerivative_lower
  obtain ⟨Y, hY⟩ := uniform_corr_lower (π/2) π B R (by positivity) pi_pos hB hR
  exact ⟨Y, hY polarDerivative polarDerivative_continuous hu hl⟩

/-- The polar differential autocorrelation has a genuinely positive tail. -/
theorem polarDerivativeAutocorr_eventually_pos :
    ∀ᶠ y : ℝ in atTop, 0 < polarDerivativeAutocorr y := by
  obtain ⟨Y, hY⟩ := polarDerivativeAutocorr_lower
  exact eventually_atTop.mpr ⟨Y, fun y hy => (exp_pos _).trans_le (hY y hy)⟩


/-- Positive Green weight for the polar second-difference operator. -/
def greenWeight (c t : ℝ) : ℝ := 2 * sinh ((c-t)/2)

private theorem phi_real (x : ℝ) : cuspSeries (riemannKernelPoly 0) x = riemannKernelReal x := by
  have h := riemannPhiKernel_eq_ofReal x
  rw [riemannPhiKernel_eq_cuspSeries] at h
  exact Complex.ofReal_injective h

private theorem phi_hasDeriv (x : ℝ) :
    HasDerivAt riemannKernelReal (cuspSeries (riemannKernelPoly 1) x) x := by
  have h := hasDerivAt_cuspSeries (riemannKernelPoly 0) x
  have he : cuspSeries (riemannKernelPoly 0) = riemannKernelReal := funext phi_real
  rw [he] at h
  exact h

/-- Exact finite-interval Green representation. It retains the complete theta source. -/
theorem polarShift_green (c x : ℝ) :
    polarShift c riemannKernelReal x = -polarWeight c *
      ∫ t in (0:ℝ)..c, greenWeight c t * (polarDerivative (x+t)+polarDerivative (x-t)) := by
  let φ₁ : ℝ → ℝ := cuspSeries (riemannKernelPoly 1)
  let φ₂ : ℝ → ℝ := cuspSeries (riemannKernelPoly 2)
  have hD1 (z : ℝ) : HasDerivAt φ₁ (φ₂ z) z := hasDerivAt_cuspSeries _ z
  have hF (z : ℝ) : φ₂ z - riemannKernelReal z / 4 = polarDerivative z := by
    rw [polarDerivative_eq]
    rfl
  let H : ℝ → ℝ := fun t => greenWeight c t * (φ₁ (x+t)-φ₁ (x-t)) +
      cosh ((c-t)/2) * (riemannKernelReal (x+t)+riemannKernelReal (x-t))
  have hD (t : ℝ) : HasDerivAt H
      (greenWeight c t * (polarDerivative (x+t)+polarDerivative (x-t))) t := by
    have harg : HasDerivAt (fun t : ℝ => (c-t)/2) (-1/2) t :=
      ((hasDerivAt_id t).const_sub c).div_const 2
    have hp : HasDerivAt (fun t : ℝ => x+t) 1 t := (hasDerivAt_id t).const_add x
    have hm : HasDerivAt (fun t : ℝ => x-t) (-1) t := (hasDerivAt_id t).const_sub x
    have hw := ((Real.hasDerivAt_sinh ((c-t)/2)).comp t harg).const_mul 2
    have hc := (Real.hasDerivAt_cosh ((c-t)/2)).comp t harg
    have h := (hw.mul ((hD1 (x+t)).comp t hp |>.sub ((hD1 (x-t)).comp t hm))).add
      (hc.mul ((phi_hasDeriv (x+t)).comp t hp |>.add ((phi_hasDeriv (x-t)).comp t hm)))
    apply h.congr_deriv
    rw [← hF, ← hF]
    dsimp only [greenWeight, φ₁, Function.comp_apply, Pi.sub_apply, Pi.add_apply]
    ring
  have hi : IntervalIntegrable (fun t => greenWeight c t *
      (polarDerivative (x+t)+polarDerivative (x-t))) volume 0 c := by
    apply Continuous.intervalIntegrable
    exact (by unfold greenWeight; fun_prop : Continuous (greenWeight c)).mul
      ((polarDerivative_continuous.comp (continuous_const.add continuous_id)).add
        (polarDerivative_continuous.comp (continuous_const.sub continuous_id)))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hD t) hi
  have hHc : H c = riemannKernelReal (x+c)+riemannKernelReal (x-c) := by simp [H, greenWeight]
  have hH0 : H 0 = 2*cosh (c/2)*riemannKernelReal x := by simp [H, greenWeight]; ring
  rw [hHc, hH0] at h
  rw [h]
  unfold polarShift
  have hp : polarWeight c * (2*cosh (c/2)) = 1 := by
    unfold polarWeight
    have := Real.cosh_pos (c/2)
    field_simp
  linear_combination -(riemannKernelReal x) * hp


/-- Every nonzero polar shift up to width one has a negative source tail, with a common
threshold even when the shift tends to zero. This is a sign of the source, not its energy. -/
theorem polarShift_uniform_negative_tail :
    ∃ R : ℝ, ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ x : ℝ, R ≤ |x| →
      polarShift c riemannKernelReal x < 0 := by
  obtain ⟨R, hR, hl⟩ := polarDerivative_lower
  refine ⟨R+1, fun c hc hc1 x hx => ?_⟩
  have harg (t : ℝ) (ht : t ∈ Icc 0 c) :
      R ≤ |x+t| ∧ R ≤ |x-t| := by
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.trans hc1
    have ha := abs_sub (x+t) t
    have hb := abs_add_le (x-t) t
    rw [add_sub_cancel_right] at ha
    rw [sub_add_cancel] at hb
    constructor <;> linarith
  have hpos (t : ℝ) (ht : t ∈ Icc 0 c) :
      0 < polarDerivative (x+t)+polarDerivative (x-t) := by
    have ha := (exp_pos _).trans_le (hl _ (harg t ht).1)
    have hb := (exp_pos _).trans_le (hl _ (harg t ht).2)
    linarith
  have hcont : Continuous (fun t => greenWeight c t *
      (polarDerivative (x+t)+polarDerivative (x-t))) :=
    (by unfold greenWeight; fun_prop : Continuous (greenWeight c)).mul
      ((polarDerivative_continuous.comp (continuous_const.add continuous_id)).add
        (polarDerivative_continuous.comp (continuous_const.sub continuous_id)))
  have hi : 0 < ∫ t in (0:ℝ)..c, greenWeight c t *
      (polarDerivative (x+t)+polarDerivative (x-t)) := by
    apply intervalIntegral.integral_pos hc hcont.continuousOn
    · intro t ht
      have hw : 0 ≤ greenWeight c t := by
        unfold greenWeight
        exact mul_nonneg (by norm_num) (Real.sinh_nonneg_iff.mpr (by linarith [ht.2]))
      exact mul_nonneg hw (hpos t ⟨ht.1.le, ht.2⟩).le
    · refine ⟨0, ⟨le_rfl, hc.le⟩, ?_⟩
      apply mul_pos _ (hpos 0 ⟨le_rfl, hc.le⟩)
      unfold greenWeight
      exact mul_pos (by norm_num) (Real.sinh_pos_iff.mpr (by linarith))
  rw [polarShift_green]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (polarWeight_pos c)) hi


private def greenIntegral (c : ℝ) : ℝ := ∫ t in (0:ℝ)..c, greenWeight c t

private theorem green_cont (c : ℝ) : Continuous (greenWeight c) := by
  unfold greenWeight
  fun_prop

private theorem green_nonneg {c t : ℝ} (ht : t ≤ c) : 0 ≤ greenWeight c t := by
  unfold greenWeight
  exact mul_nonneg (by norm_num) (sinh_nonneg_iff.mpr (by linarith))

private theorem greenIntegral_pos {c : ℝ} (hc : 0 < c) : 0 < greenIntegral c := by
  apply intervalIntegral.integral_pos hc (green_cont c).continuousOn
  · exact fun t ht => green_nonneg ht.2
  · refine ⟨0, ⟨le_rfl, hc.le⟩, ?_⟩
    unfold greenWeight
    exact mul_pos (by norm_num) (sinh_pos_iff.mpr (by linarith))

private def normalizedPolar (c x : ℝ) : ℝ :=
  -polarShift c riemannKernelReal x / (2 * polarWeight c * greenIntegral c)

private theorem normalized_cont (c : ℝ) : Continuous (normalizedPolar c) := by
  unfold normalizedPolar polarShift
  exact (((continuous_riemannKernelReal.sub (continuous_const.mul
    (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)))).sub
    (continuous_const.mul (continuous_riemannKernelReal.comp (continuous_id.add continuous_const)))).neg).div_const _

private theorem normalized_eq {c : ℝ} (hc : 0 < c) (x : ℝ) :
    normalizedPolar c x = (∫ t in (0:ℝ)..c, greenWeight c t *
      (polarDerivative (x+t)+polarDerivative (x-t))) / (2*greenIntegral c) := by
  unfold normalizedPolar
  rw [polarShift_green]
  have hp := (polarWeight_pos c).ne'
  have hi := (greenIntegral_pos hc).ne'
  field_simp

private theorem green_integrand_cont (c x : ℝ) : Continuous (fun t => greenWeight c t *
    (polarDerivative (x+t)+polarDerivative (x-t))) :=
  (green_cont c).mul ((polarDerivative_continuous.comp (continuous_const.add continuous_id)).add
    (polarDerivative_continuous.comp (continuous_const.sub continuous_id)))

private theorem normalized_lower {c x L : ℝ} (hc : 0 < c)
    (h : ∀ t ∈ Icc 0 c, L ≤ polarDerivative (x+t) ∧ L ≤ polarDerivative (x-t)) :
    L ≤ normalizedPolar c x := by
  rw [normalized_eq hc, le_div_iff₀ (mul_pos (by norm_num) (greenIntegral_pos hc))]
  have hm := intervalIntegral.integral_mono_on (μ := volume) hc.le
    (((green_cont c).mul continuous_const).intervalIntegrable 0 c)
    ((green_integrand_cont c x).intervalIntegrable 0 c)
    (fun t ht => mul_le_mul_of_nonneg_left (show 2*L ≤ polarDerivative (x+t)+polarDerivative (x-t) by
      obtain ⟨h1,h2⟩ := h t ht; linarith) (green_nonneg ht.2))
  simp only [Pi.mul_apply] at hm
  rw [intervalIntegral.integral_mul_const] at hm
  change L * (2*greenIntegral c) ≤ _
  change greenIntegral c * (2*L) ≤ _ at hm
  nlinarith

private theorem normalized_upper {c x U : ℝ} (hc : 0 < c)
    (h : ∀ t ∈ Icc 0 c, |polarDerivative (x+t)| ≤ U ∧ |polarDerivative (x-t)| ≤ U) :
    |normalizedPolar c x| ≤ U := by
  rw [normalized_eq hc, abs_div, abs_of_pos (mul_pos (by norm_num) (greenIntegral_pos hc)),
    div_le_iff₀ (mul_pos (by norm_num) (greenIntegral_pos hc))]
  have hm := intervalIntegral.integral_mono_on (μ := volume) hc.le
    ((green_integrand_cont c x).abs.intervalIntegrable 0 c)
    (((green_cont c).mul continuous_const).intervalIntegrable 0 c)
    (show ∀ t ∈ Icc 0 c, |greenWeight c t * (polarDerivative (x+t)+polarDerivative (x-t))| ≤
      greenWeight c t * (2*U) from fun t ht => by
      rw [abs_mul, abs_of_nonneg (green_nonneg ht.2)]
      apply mul_le_mul_of_nonneg_left _ (green_nonneg ht.2)
      exact (abs_add_le _ _).trans (by obtain ⟨h1,h2⟩ := h t ht; linarith))
  have hh := (intervalIntegral.abs_integral_le_integral_abs hc.le).trans hm
  simp only [Pi.mul_apply] at hh
  rw [intervalIntegral.integral_mul_const] at hh
  change _ ≤ U*(2*greenIntegral c)
  change _ ≤ greenIntegral c*(2*U) at hh
  nlinarith

private theorem shifted_abs_bounds {c : ℝ} (hc1 : c ≤ 1) (x t : ℝ) (ht : t ∈ Icc 0 c) :
    (|x|-1 ≤ |x+t| ∧ |x+t| ≤ |x|+1) ∧ (|x|-1 ≤ |x-t| ∧ |x-t| ≤ |x|+1) := by
  have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2.trans hc1
  have h1 := abs_add_le x t
  have h2 := abs_sub x t
  have h3 := abs_sub (x+t) t
  have h4 := abs_add_le (x-t) t
  rw [add_sub_cancel_right] at h3
  rw [sub_add_cancel] at h4
  constructor <;> constructor <;> linarith

private theorem normalized_envelopes :
    ∃ B R : ℝ, 0 < B ∧ 0 ≤ R ∧ ∀ c : ℝ, 0 < c → c ≤ 1 →
      (∀ x, |normalizedPolar c x| ≤ B * exp (-(((π/2)*exp (-2))*exp (2*|x|))) * exp (-|x|)) ∧
      (∀ x, R ≤ |x| → exp (-((π*exp 2)*exp (2*|x|))) ≤ normalizedPolar c x) := by
  obtain ⟨B,hB,hu⟩ := polarDerivative_upper
  obtain ⟨R,hR,hl⟩ := polarDerivative_lower
  refine ⟨B*exp 1, R+1, by positivity, by linarith, fun c hc hc1 => ⟨?_, ?_⟩⟩
  · intro x
    apply normalized_upper hc
    intro t ht
    have hu' (z : ℝ) (hz : |x|-1 ≤ |z|) :
        |polarDerivative z| ≤ (B*exp 1) * exp (-(((π/2)*exp (-2))*exp (2*|x|))) * exp (-|x|) := by
      have he : exp (2*(|x|-1)) ≤ exp (2*|z|) := exp_le_exp.mpr (by linarith)
      have hs : exp (-|z|) ≤ exp 1 * exp (-|x|) := by
        rw [← exp_add]; exact exp_le_exp.mpr (by linarith)
      have hp : exp (-((π/2)*exp (2*|z|))) ≤ exp (-(((π/2)*exp (-2))*exp (2*|x|))) := by
        apply exp_le_exp.mpr
        rw [show 2*(|x|-1)=(-2)+(2*|x|) by ring, exp_add] at he
        nlinarith [pi_pos]
      exact (hu z).trans (calc _ ≤ B*exp (-(((π/2)*exp (-2))*exp (2*|x|)))*(exp 1*exp (-|x|)) := by gcongr
        _ = _ := by ring)
    exact ⟨hu' _ (shifted_abs_bounds hc1 x t ht).1.1, hu' _ (shifted_abs_bounds hc1 x t ht).2.1⟩
  · intro x hx
    apply normalized_lower hc
    intro t ht
    have hl' (z : ℝ) (hz : |x|-1 ≤ |z| ∧ |z| ≤ |x|+1) :
        exp (-((π*exp 2)*exp (2*|x|))) ≤ polarDerivative z := by
      have he : exp (2*|z|) ≤ exp (2*(|x|+1)) := exp_le_exp.mpr (by linarith [hz.2])
      rw [show 2*(|x|+1)=2+(2*|x|) by ring, exp_add] at he
      apply le_trans _ (hl z (by linarith [hz.1]))
      apply exp_le_exp.mpr
      nlinarith [pi_pos]
    exact ⟨hl' _ (shifted_abs_bounds hc1 x t ht).1, hl' _ (shifted_abs_bounds hc1 x t ht).2⟩


private theorem phi_bounded : ∃ B : ℝ, ∀ x : ℝ, |riemannKernelReal x| ≤ B := by
  obtain ⟨C,hC,h⟩ := exists_norm_riemannPhiKernel_le_exp (B := 0) le_rfl
  refine ⟨C, fun x => ?_⟩
  simpa [riemannPhiKernel_eq_ofReal] using h x

private theorem phi_times_integrable {H : ℝ → ℝ} (hH : Continuous H)
    (hbound : ∃ B : ℝ, ∀ x, |H x| ≤ B) (a y : ℝ) :
    Integrable (fun t => riemannKernelReal (t-a) * H (t-y)) := by
  obtain ⟨B,hB⟩ := hbound
  have hi : Integrable (fun t : ℝ => riemannKernelReal (t-a)) := by
    simpa only [sub_eq_add_neg] using WeilExcess.integrable_riemannKernelReal.comp_add_right (-a)
  exact hi.mul_bdd (hH.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa only [Real.norm_eq_abs] using hB (t-y))

private theorem corr_polar_left (c : ℝ) {H : ℝ → ℝ} (hH : Continuous H)
    (hbound : ∃ B : ℝ, ∀ x, |H x| ≤ B) (y : ℝ) :
    crossCorr (polarShift c riemannKernelReal) H y =
      polarShift c (crossCorr riemannKernelReal H) y := by
  have i0 := phi_times_integrable hH hbound 0 y
  simp only [sub_zero] at i0
  have i1 := (phi_times_integrable hH hbound c y).const_mul (polarWeight c)
  have i2 := (phi_times_integrable hH hbound (-c) y).const_mul (polarWeight c)
  have s1 : ∫ t, riemannKernelReal (t-c)*H (t-y) = crossCorr riemannKernelReal H (y-c) := by
    unfold crossCorr
    rw [← integral_add_right_eq_self (μ := volume) (fun t => riemannKernelReal (t-c)*H (t-y)) c]
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [show t+c-c=t by ring, show t+c-y=t-(y-c) by ring]
  have s2 : ∫ t, riemannKernelReal (t- -c)*H (t-y) = crossCorr riemannKernelReal H (y+c) := by
    unfold crossCorr
    rw [← integral_add_right_eq_self (μ := volume) (fun t => riemannKernelReal (t- -c)*H (t-y)) (-c)]
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [show t+ -c- -c=t by ring, show t+ -c-y=t-(y+c) by ring]
  have e : crossCorr (polarShift c riemannKernelReal) H y =
      (∫ t, riemannKernelReal t*H (t-y))-
      (∫ t, polarWeight c*(riemannKernelReal (t-c)*H (t-y)))-
      (∫ t, polarWeight c*(riemannKernelReal (t- -c)*H (t-y))) := by
    have hA : Integrable (fun t => riemannKernelReal t*H (t-y)-
        polarWeight c*(riemannKernelReal (t-c)*H (t-y))) := i0.sub i1
    rw [← integral_sub i0 i1, ← integral_sub hA i2]
    unfold crossCorr polarShift
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [sub_neg_eq_add]
    ring
  rw [e, integral_const_mul, integral_const_mul, s1, s2]
  rfl

private theorem corr_polar_right (c y : ℝ) :
    crossCorr riemannKernelReal (polarShift c riemannKernelReal) y =
      polarShift c riemannKernelAutocorr y := by
  have hi (z : ℝ) : Integrable (fun t => riemannKernelReal t*riemannKernelReal (t-z)) := by
    simpa only [sub_zero] using phi_times_integrable continuous_riemannKernelReal phi_bounded 0 z
  have i1 := (hi (y+c)).const_mul (polarWeight c)
  have i2 := (hi (y-c)).const_mul (polarWeight c)
  have e : crossCorr riemannKernelReal (polarShift c riemannKernelReal) y =
      (∫ t, riemannKernelReal t*riemannKernelReal (t-y))-
      (∫ t, polarWeight c*(riemannKernelReal t*riemannKernelReal (t-(y+c))))-
      (∫ t, polarWeight c*(riemannKernelReal t*riemannKernelReal (t-(y-c)))) := by
    have hA : Integrable (fun t => riemannKernelReal t*riemannKernelReal (t-y)-
        polarWeight c*(riemannKernelReal t*riemannKernelReal (t-(y+c)))) := (hi y).sub i1
    rw [← integral_sub (hi y) i1, ← integral_sub hA i2]
    unfold crossCorr polarShift
    apply integral_congr_ae (Eventually.of_forall fun t => ?_)
    rw [show t-y-c=t-(y+c) by ring, show t-y+c=t-(y-c) by ring]
    ring
  rw [e, integral_const_mul, integral_const_mul]
  unfold polarShift riemannKernelAutocorr crossCorr
  ring

/-- The literal untruncated polar kernel is the actual polar-source autocorrelation. -/
theorem polarExposingKernel_eq_corr (c y : ℝ) :
    polarExposingKernel c y =
      crossCorr (polarShift c riemannKernelReal) (polarShift c riemannKernelReal) y := by
  have hcont : Continuous (polarShift c riemannKernelReal) := by
    unfold polarShift
    exact (continuous_riemannKernelReal.sub (continuous_const.mul
      (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)))).sub
      (continuous_const.mul (continuous_riemannKernelReal.comp (continuous_id.add continuous_const)))
  have hbound : ∃ B : ℝ, ∀ x, |polarShift c riemannKernelReal x| ≤ B := by
    obtain ⟨B,hB⟩ := phi_bounded
    refine ⟨B+2*polarWeight c*B, fun x => ?_⟩
    unfold polarShift
    calc _ ≤ |riemannKernelReal x| + |polarWeight c*riemannKernelReal (x-c)| +
        |polarWeight c*riemannKernelReal (x+c)| := (abs_sub _ _).trans (by gcongr; exact abs_sub _ _)
      _ ≤ B + polarWeight c*B + polarWeight c*B := by
        simp only [abs_mul, abs_of_pos (polarWeight_pos c)]
        gcongr <;> first | exact (polarWeight_pos c).le | exact hB _
      _ = _ := by ring
  rw [corr_polar_left c hcont hbound]
  have hfun : crossCorr riemannKernelReal (polarShift c riemannKernelReal) =
      polarShift c riemannKernelAutocorr := funext (corr_polar_right c)
  rw [hfun]
  rfl

private theorem normalized_corr_eq {c : ℝ} (hc : 0 < c) (y : ℝ) :
    polarExposingKernel c y = (2*polarWeight c*greenIntegral c)^2 *
      ∫ t : ℝ, normalizedPolar c t*normalizedPolar c (t-y) := by
  rw [polarExposingKernel_eq_corr, crossCorr, ← integral_const_mul]
  apply integral_congr_ae (Eventually.of_forall fun t => ?_)
  have hp := (polarWeight_pos c).ne'
  have hi := (greenIntegral_pos hc).ne'
  simp only [normalizedPolar]
  field_simp


private theorem greenIntegral_lower {c : ℝ} (hc : 0 < c) : c^2/2 ≤ greenIntegral c := by
  have hm := intervalIntegral.integral_mono_on (μ := volume) hc.le
    ((continuous_const.sub continuous_id).intervalIntegrable 0 c)
    ((green_cont c).intervalIntegrable 0 c)
    (show ∀ t ∈ Icc 0 c, c-t ≤ greenWeight c t from fun t ht => by
      have := self_le_sinh_iff.mpr (show (0:ℝ) ≤ (c-t)/2 by linarith [ht.2])
      unfold greenWeight
      linarith)
  have heq : (∫ t in (0:ℝ)..c, c-t) = c^2/2 := by
    calc _ = (∫ _t in (0:ℝ)..c, c) - ∫ t in (0:ℝ)..c, t :=
        intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
          (continuous_id.intervalIntegrable _ _)
      _ = _ := by rw [intervalIntegral.integral_const, integral_id]; simp; ring
  simp only [Pi.sub_apply, id_eq] at hm
  rwa [heq] at hm

private theorem polarWeight_lower {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    polarWeight 1 ≤ polarWeight c := by
  have hcosh : cosh (c/2) ≤ cosh (1/2) := cosh_le_cosh.mpr (by
    rw [abs_of_pos (by linarith : (0:ℝ)<c/2), abs_of_pos (by norm_num : (0:ℝ)<1/2)]
    linarith)
  unfold polarWeight
  exact one_div_le_one_div_of_le (by have := cosh_pos (c/2); positivity) (by linarith)

/-- A uniform quartic lower bound for the entire small-shift family on one common tail.
All constants belong to the literal Riemann kernel; no positivity premise is assumed. -/
theorem polarExposingKernel_uniform_quartic_lower :
    ∃ D C Y : ℝ, 0 < D ∧ 0 < C ∧ ∀ c : ℝ, 0 < c → c ≤ 1 →
      ∀ y : ℝ, Y ≤ y → D*c^4*exp (-(C*exp y)) ≤ polarExposingKernel c y := by
  obtain ⟨B,R,hB,hR,henv⟩ := normalized_envelopes
  obtain ⟨Y,hY⟩ := uniform_corr_lower ((π/2)*exp (-2)) (π*exp 2) B R
    (by positivity) (by positivity) hB hR
  refine ⟨(polarWeight 1)^2, 2*(π*exp 2)*exp 2, Y,
    sq_pos_of_pos (polarWeight_pos 1), by positivity, fun c hc hc1 y hy => ?_⟩
  have hlo := hY (normalizedPolar c) (normalized_cont c) (henv c hc hc1).1 (henv c hc hc1).2 y hy
  have hk : polarWeight 1*c^2 ≤ 2*polarWeight c*greenIntegral c := by
    have h1 := mul_le_mul_of_nonneg_left (greenIntegral_lower hc) (polarWeight_pos c).le
    have h2 := mul_le_mul_of_nonneg_right (polarWeight_lower hc hc1) (sq_nonneg c)
    nlinarith
  have hsq := pow_le_pow_left₀ (mul_nonneg (polarWeight_pos 1).le (sq_nonneg c)) hk 2
  rw [normalized_corr_eq hc]
  calc _ = (polarWeight 1*c^2)^2*exp (-(2*(π*exp 2)*exp 2*exp y)) := by ring
    _ ≤ (2*polarWeight c*greenIntegral c)^2*exp (-(2*(π*exp 2)*exp 2*exp y)) := by gcongr
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (sq_nonneg _)

/-- A common strictly positive tail for every nonzero pole-cancelling shift up to one.
The threshold does not depend on the shift. -/
theorem polarExposingKernel_uniform_positive_tail :
    ∃ Y : ℝ, ∀ c : ℝ, 0 < c → c ≤ 1 → ∀ y : ℝ, Y ≤ y → 0 < polarExposingKernel c y := by
  obtain ⟨D,C,Y,hD,hC,hY⟩ := polarExposingKernel_uniform_quartic_lower
  refine ⟨Y, fun c hc hc1 y hy => ?_⟩
  exact (mul_pos (mul_pos hD (pow_pos hc 4)) (exp_pos _)).trans_le (hY c hc hc1 y hy)

end RHTower.ExposingRaySmallShift
