import GaloisForLFunctions.RHTower.LandauRelativeRigidity
import GaloisForLFunctions.RHTower.FractionalPartZeta
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# No positive-mass perturbation can play the exceptional zero

A nonnegative generalized-prime perturbation of `ζ` has logarithmic Euler factor
`D(s) = Σ a_j e^{-λ_j s}` with `a_j ≥ 0` and frequencies `λ_j ≥ c > 0`, and Euler factor
`E = exp D` on the half-plane `Re s > σ_c` of convergence.  Suppose an extension of `E` makes the
perturbed zeta `ζ · E` vanish at a real point `β₁ ∈ (0,1)`.  Since `ζ` does not vanish on `(0,1)`,
relative Landau rigidity gives `β₁ ≤ σ_c`.  This module proves that `E` is then **not analytic on any
ball around `σ_c`**:

* on the real axis right of `σ_c` the exponent `D(σ)` is a nonnegative real, so `|E(σ)| ≥ 1` and by
  continuity `E(σ_c) ≠ 0`;
* on a ball where `E` is analytic and nonvanishing, `E'/E` is analytic and agrees to the right of
  `σ_c` with `D' = -Σ a_j λ_j e^{-λ_j s}`, whose coefficient series `a_j λ_j ≥ 0` has the same
  abscissa `σ_c`; Landau's theorem forbids that continuation.

So the perturbed zeta has a real singularity in `[β₁, σ_c]`: no Hadamard product, no explicit
formula, and no share ledger exists for `ζ · E`.  A surrogate exceptional zero cannot be manufactured
from positive mass.  The termwise derivative of the series is obtained from the uniform bound
`a_j λ_j e^{-λ_j Re s} ≤ a_j λ_j e^{-λ_j σ''}` on the open half-plane `Re s > σ''`.
-/

open Complex Metric Filter Topology GaloisForLFunctions.HTGeometry
open scoped Topology

namespace RHTower

noncomputable section

variable {ι : Type*} {a lam : ι → ℝ}

/-- The zeroth twist term of the frequency-weighted coefficients is the first twist term of the
original coefficients. -/
theorem gdTwistTerm_mul_lam_zero (σ : ℝ) (j : ι) :
    gdTwistTerm (fun j => a j * lam j) lam σ 0 j = gdTwistTerm a lam σ 1 j := by
  simp only [gdTwistTerm, pow_zero, pow_one, mul_one]

theorem gdTwistTerm_mul_lam_zero_fun (σ : ℝ) :
    gdTwistTerm (fun j => a j * lam j) lam σ 0 = gdTwistTerm a lam σ 1 :=
  funext (gdTwistTerm_mul_lam_zero σ)

/-- The derivative series converges strictly right of the abscissa. -/
theorem summable_gdTwistTerm_one_of_lt (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j)
    {σc σ : ℝ} (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0)) (hσ : σc < σ) :
    Summable (gdTwistTerm a lam σ 1) := by
  have hmid : σc < (σc + σ) / 2 := by linarith
  have hh : (0 : ℝ) < (σ - σc) / 2 := by linarith
  have h := summable_gdTwistTerm ha hlam (hsum _ hmid) hh 1
  have heq : (σc + σ) / 2 + (σ - σc) / 2 = σ := by ring
  rwa [heq] at h

/-- The derivative series diverges strictly left of the abscissa when the frequencies are bounded
below by a positive constant. -/
theorem not_summable_gdTwistTerm_one_of_lt (ha : ∀ j, 0 ≤ a j) {c : ℝ} (hc : 0 < c)
    (hlam : ∀ j, c ≤ lam j) {σc σ : ℝ}
    (hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a lam σ 0)) (hσ : σ < σc) :
    ¬ Summable (gdTwistTerm a lam σ 1) := by
  intro h
  apply hdiv σ hσ
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => le_trans hc.le (hlam j)
  refine Summable.of_nonneg_of_le (gdTwistTerm_nonneg ha hlam0 σ 0) (fun j => ?_)
    (h.mul_left c⁻¹)
  simp only [gdTwistTerm, pow_zero, pow_one, mul_one]
  have hlj := hlam j
  have haj := ha j
  have he := Real.exp_pos (-(σ * lam j))
  have hbase : 0 ≤ a j * Real.exp (-(σ * lam j)) := mul_nonneg haj he.le
  have hratio : 1 ≤ lam j / c := by
    rw [le_div_iff₀ hc]
    linarith
  have hrw : c⁻¹ * (a j * lam j * Real.exp (-(σ * lam j)))
      = (a j * Real.exp (-(σ * lam j))) * (lam j / c) := by
    field_simp
  rw [hrw]
  nlinarith [hbase, hratio]

/-- **Termwise derivative of a nonnegative general Dirichlet series** on its open half-plane of
convergence: `D'(s) = -Σ a_j λ_j e^{-λ_j s}`. -/
theorem hasDerivAt_gdSeries (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j) {σc : ℝ}
    (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0)) {s : ℂ} (hs : σc < s.re) :
    HasDerivAt (gdSeries a lam) (-(gdSeries (fun j => a j * lam j) lam s)) s := by
  set σ'' : ℝ := (σc + s.re) / 2 with hσ''
  have h1 : σc < σ'' := by rw [hσ'']; linarith
  have h2 : σ'' < s.re := by rw [hσ'']; linarith
  have hu : Summable (gdTwistTerm a lam σ'' 1) := summable_gdTwistTerm_one_of_lt ha hlam hsum h1
  have hopen : IsOpen {z : ℂ | σ'' < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hlin : IsLinearMap ℝ (fun z : ℂ => z.re) :=
    ⟨fun x y => Complex.add_re x y, fun c x => by simp⟩
  have hconv : Convex ℝ {z : ℂ | σ'' < z.re} := convex_halfSpace_gt hlin σ''
  have hpre : IsPreconnected {z : ℂ | σ'' < z.re} := hconv.isPreconnected
  have hg : ∀ (j : ι) (y : ℂ), y ∈ {z : ℂ | σ'' < z.re} →
      HasDerivAt (fun z => (a j : ℂ) * Complex.exp (-(z * (lam j : ℂ))))
        (-((a j * lam j : ℝ) : ℂ) * Complex.exp (-(y * (lam j : ℂ)))) y := by
    intro j y _
    have h : HasDerivAt (fun z : ℂ => (a j : ℂ) * Complex.exp (-(z * (lam j : ℂ))))
        ((a j : ℂ) * (Complex.exp (-(y * (lam j : ℂ))) * -(1 * (lam j : ℂ)))) y :=
      (((hasDerivAt_id' y).mul_const ((lam j : ℝ) : ℂ)).neg.cexp).const_mul ((a j : ℝ) : ℂ)
    refine h.congr_deriv ?_
    push_cast
    ring
  have hg' : ∀ (j : ι) (y : ℂ), y ∈ {z : ℂ | σ'' < z.re} →
      ‖-((a j * lam j : ℝ) : ℂ) * Complex.exp (-(y * (lam j : ℂ)))‖ ≤ gdTwistTerm a lam σ'' 1 j := by
    intro j y hy
    have hy' : σ'' < y.re := hy
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (mul_nonneg (ha j) (hlam j)),
      Complex.norm_exp]
    have hre : (-(y * ((lam j : ℝ) : ℂ))).re = -(y.re * lam j) := by
      simp [Complex.mul_re]
    rw [hre]
    simp only [gdTwistTerm, pow_one]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (ha j) (hlam j))
    exact Real.exp_le_exp.mpr (by nlinarith [hlam j])
  have hg0 : Summable (fun j => (a j : ℂ) * Complex.exp (-(s * (lam j : ℂ)))) :=
    summable_gd_term ha hlam (hsum σ'' h1) h2.le
  have hs' : s ∈ {z : ℂ | σ'' < z.re} := h2
  have hderiv := hasDerivAt_tsum_of_isPreconnected hu hopen hpre hg hg' hs' hg0 hs'
  refine hderiv.congr_deriv ?_
  simp only [gdSeries]
  rw [← tsum_neg]
  congr 1
  funext j
  push_cast
  ring

/-- On the real axis right of the abscissa the series is a nonnegative real number. -/
theorem gdSeries_ofReal (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j) {σ₁ σ : ℝ}
    (hsum : Summable (gdTwistTerm a lam σ₁ 0)) (hσ : σ₁ ≤ σ) :
    gdSeries a lam (σ : ℂ) = ((∑' j, gdTwistTerm a lam σ 0 j : ℝ) : ℂ) := by
  have _ := summable_gdTwistTerm_of_le ha hlam hsum hσ
  rw [gdSeries, Complex.ofReal_tsum]
  congr 1
  funext j
  simp only [gdTwistTerm, pow_zero, mul_one]
  rw [Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul]

theorem gdSeries_ofReal_nonneg (ha : ∀ j, 0 ≤ a j) (hlam : ∀ j, 0 ≤ lam j) (σ : ℝ) :
    0 ≤ ∑' j, gdTwistTerm a lam σ 0 j :=
  tsum_nonneg (fun j => gdTwistTerm_nonneg ha hlam σ 0 j)

/-- **No surrogate exceptional zero.**  If a nonnegative generalized-prime Euler perturbation with
frequencies `λ_j ≥ c > 0` and real abscissa `σ_c` extends to a function `E` with
`ζ(β₁)E(β₁) = 0` for a real `β₁ ∈ (0,1)`, then `β₁ ≤ σ_c` and `E` is not holomorphic on any ball
around `σ_c`. -/
theorem no_surrogate_annihilator (ha : ∀ j, 0 ≤ a j) {c : ℝ} (hc : 0 < c) (hlam : ∀ j, c ≤ lam j)
    {σc : ℝ} (hsum : ∀ σ, σc < σ → Summable (gdTwistTerm a lam σ 0))
    (hdiv : ∀ σ, σ < σc → ¬ Summable (gdTwistTerm a lam σ 0))
    {E : ℂ → ℂ} (hE : ∀ s : ℂ, σc < s.re → E s = Complex.exp (gdSeries a lam s))
    {β₁ : ℝ} (h0 : 0 < β₁) (h1 : β₁ < 1)
    (hzero : riemannZeta (β₁ : ℂ) * E (β₁ : ℂ) = 0) :
    β₁ ≤ σc ∧ ∀ r : ℝ, 0 < r → ¬ DifferentiableOn ℂ E (ball ((σc : ℂ)) r) := by
  have hlam0 : ∀ j, 0 ≤ lam j := fun j => le_trans hc.le (hlam j)
  have hζ : riemannZeta (β₁ : ℂ) ≠ 0 := riemannZeta_ne_zero_of_ofReal_mem_Ioo h0 h1
  have hrel := landau_relative_rigidity ha hlam0 hsum hdiv hE hζ hzero
  refine ⟨by simpa using hrel.1, ?_⟩
  intro r hr hdiff
  have hcont : ContinuousAt E (σc : ℂ) :=
    hdiff.continuousOn.continuousAt (Metric.ball_mem_nhds _ hr)
  -- `|E| ≥ 1` on the real axis right of the abscissa
  have hge : ∀ σ : ℝ, σc < σ → 1 ≤ ‖E (σ : ℂ)‖ := by
    intro σ hσ
    have hσ' : σc < ((σ : ℂ)).re := by simpa using hσ
    rw [hE _ hσ', gdSeries_ofReal ha hlam0 (hsum σ hσ) le_rfl, Complex.norm_exp,
      Complex.ofReal_re]
    exact Real.one_le_exp (gdSeries_ofReal_nonneg ha hlam0 σ)
  have hlim : Tendsto (fun σ : ℝ => ‖E (σ : ℂ)‖) (𝓝[>] σc) (𝓝 ‖E (σc : ℂ)‖) := by
    have h1' : Tendsto (fun σ : ℝ => (σ : ℂ)) (𝓝[>] σc) (𝓝 (σc : ℂ)) :=
      (Complex.continuous_ofReal.tendsto σc).mono_left nhdsWithin_le_nhds
    exact (hcont.tendsto.comp h1').norm
  have hEσc : 1 ≤ ‖E (σc : ℂ)‖ := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact hge σ hσ
  have hE0 : E (σc : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hEσc
    linarith
  -- a smaller ball on which `E` does not vanish
  obtain ⟨r', hr', hball⟩ : ∃ r' > 0, ∀ z ∈ ball (σc : ℂ) r', E z ≠ 0 := by
    have hev : ∀ᶠ z in 𝓝 (σc : ℂ), E z ≠ 0 := hcont.eventually_ne hE0
    obtain ⟨r', hr', hsub⟩ := Metric.mem_nhds_iff.mp hev
    exact ⟨r', hr', fun z hz => hsub hz⟩
  set r₀ : ℝ := min r r' with hr₀
  have hr₀pos : 0 < r₀ := lt_min hr hr'
  have hsub_r : ball (σc : ℂ) r₀ ⊆ ball (σc : ℂ) r := ball_subset_ball (min_le_left _ _)
  have hsub_r' : ball (σc : ℂ) r₀ ⊆ ball (σc : ℂ) r' := ball_subset_ball (min_le_right _ _)
  have hdiff₀ : DifferentiableOn ℂ E (ball (σc : ℂ) r₀) := hdiff.mono hsub_r
  have hderivOn : DifferentiableOn ℂ (deriv E) (ball (σc : ℂ) r₀) :=
    ((hdiff₀.analyticOnNhd Metric.isOpen_ball).deriv).differentiableOn
  have hG : DifferentiableOn ℂ (fun z => -(deriv E z / E z)) (ball (σc : ℂ) r₀) :=
    (hderivOn.div hdiff₀ (fun z hz => hball z (hsub_r' hz))).neg
  -- the logarithmic derivative continues the derivative series
  have hagree : ∀ s ∈ ball (σc : ℂ) r₀, σc < s.re →
      -(deriv E s / E s) = gdSeries (fun j => a j * lam j) lam s := by
    intro s hs hsre
    have hEs : E s ≠ 0 := hball s (hsub_r' hs)
    have hev : E =ᶠ[𝓝 s] fun z => Complex.exp (gdSeries a lam z) := by
      have hopen : IsOpen {z : ℂ | σc < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds hsre] with z hz
      exact hE z hz
    have hd : HasDerivAt (fun z => Complex.exp (gdSeries a lam z))
        (Complex.exp (gdSeries a lam s) * -(gdSeries (fun j => a j * lam j) lam s)) s :=
      (hasDerivAt_gdSeries ha hlam0 hsum hsre).cexp
    have hderiv_eq : deriv E s =
        Complex.exp (gdSeries a lam s) * -(gdSeries (fun j => a j * lam j) lam s) := by
      rw [hev.deriv_eq]
      exact hd.deriv
    rw [hderiv_eq, hE s hsre]
    have hne : Complex.exp (gdSeries a lam s) ≠ 0 := Complex.exp_ne_zero _
    field_simp
  exact gdSeries_no_continuation_at_abscissa (a := fun j => a j * lam j)
    (fun j => mul_nonneg (ha j) (hlam0 j)) hlam0
    (fun σ hσ => by
      rw [gdTwistTerm_mul_lam_zero_fun]
      exact summable_gdTwistTerm_one_of_lt ha hlam0 hsum hσ)
    (fun σ hσ => by
      rw [gdTwistTerm_mul_lam_zero_fun]
      exact not_summable_gdTwistTerm_one_of_lt ha hc hlam hdiv hσ)
    hr₀pos hG hagree

end

end RHTower
