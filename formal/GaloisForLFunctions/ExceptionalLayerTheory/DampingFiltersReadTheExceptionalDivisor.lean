import GaloisForLFunctions.ExceptionalLayerTheory.TheSharpRecurrentLayerEnvelope

/-!
# Damping filters read the exceptional divisor

Geometric changes of Gaussian damping multiply every Mellin mode by an
exact exponential character. Polynomial filters therefore cancel a chosen
finite set of modes, including the pole, at a single observation height.
-/

open Complex Filter Set Topology RHTower XiAtlasFinitePart

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

open EulerFETransportTheory

/-- The geometric damping grid, centered at exponential observation scale. -/
def geometricGaussianDamping (a h t : ℝ) (j : ℕ) : ℝ :=
  Real.exp (-a * t - 2 * j * h)

/-- A geometric change in damping acts exactly on each Mellin mode. -/
theorem gaussianMode_geometric_damping (a h t : ℝ) (j : ℕ) (w : ℂ) :
    gaussianMBKernel (geometricGaussianDamping a h t j) w =
      Complex.exp ((j : ℂ) * h * w) * gaussianMBKernel (Real.exp (-a * t)) w := by
  unfold gaussianMBKernel geometricGaussianDamping
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos _).le,
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Real.log_exp]
  have he : (((-a * t - 2 * j * h : ℝ) : ℂ) * -(w / 2)) =
      (j : ℂ) * h * w + ((-a * t : ℝ) : ℂ) * -(w / 2) := by
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

/-- The correction placing all damping samples in one real top-mode normalization. -/
def dampingSampleWeight (β h : ℝ) (s : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-((j : ℂ) * h * ((β : ℂ) - s)))

theorem norm_dampingSampleWeight (β h σ t : ℝ) (j : ℕ) :
    ‖dampingSampleWeight β h ((σ : ℂ) + t * I) j‖ =
      Real.exp (-(j * h * (β - σ))) := by
  rw [dampingSampleWeight, Complex.norm_exp]
  congr 1
  simp

/-- The literal prime observable attached to a finite damping filter. -/
def primeDampingFilter (P : Polynomial ℂ) (σ β a h t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * dampingSampleWeight β h ((σ : ℂ) + t * I) j *
      gaussianDampedPrimeSum ((σ : ℂ) + t * I) (geometricGaussianDamping a h t j)

/-- Polynomial evaluation gives exact cancellation, before any limiting argument. -/
theorem polynomial_dampingFilter_gaussianMode (P : Polynomial ℂ)
    (β a h t : ℝ) (s ρ : ℂ) :
    (∑ j ∈ Finset.range (P.natDegree + 1),
      P.coeff j * dampingSampleWeight β h s j *
        gaussianMBKernel (geometricGaussianDamping a h t j) (ρ - s)) =
      P.eval (Complex.exp ((h : ℂ) * (ρ - β))) *
        gaussianMBKernel (Real.exp (-a * t)) (ρ - s) := by
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [gaussianMode_geometric_damping, dampingSampleWeight, ← Complex.exp_nat_mul]
  have he : -((j : ℂ) * h * ((β : ℂ) - s)) + (j : ℂ) * h * (ρ - s) =
      (j : ℂ) * ((h : ℂ) * (ρ - β)) := by ring
  rw [show P.coeff j * Complex.exp (-((j : ℂ) * h * ((β : ℂ) - s))) *
      (Complex.exp ((j : ℂ) * h * (ρ - s)) *
        gaussianMBKernel (Real.exp (-a * t)) (ρ - s)) =
      P.coeff j * (Complex.exp (-((j : ℂ) * h * ((β : ℂ) - s))) *
        Complex.exp ((j : ℂ) * h * (ρ - s))) *
          gaussianMBKernel (Real.exp (-a * t)) (ρ - s) by ring,
    ← Complex.exp_add, he]

/-- The continued term appearing when the literal prime sum is expanded. -/
def continuedDampingCorrection (P : Polynomial ℂ) (σ β a h t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (P.natDegree + 1),
    P.coeff j * dampingSampleWeight β h ((σ : ℂ) + t * I) j *
      (Real.exp (-geometricGaussianDamping a h t j) : ℂ) *
        logDeriv riemannZeta ((σ : ℂ) + t * I)

/-- The full infinite-current error survives filtering exactly; the pole and
finite divisor are multiplied by the same polynomial evaluations. -/
theorem primeDampingFilter_expansion (P : Polynomial ℂ) (F : Finset XiZeroCopy)
    (σ β a h t : ℝ) :
    primeDampingFilter P σ β a h t + continuedDampingCorrection P σ β a h t -
      P.eval (Complex.exp ((h : ℂ) * (1 - β))) *
        gaussianMBKernel (Real.exp (-a * t)) (1 - ((σ : ℂ) + t * I)) +
      ∑ q ∈ F, P.eval (Complex.exp ((h : ℂ) * (xiZero q - β))) *
        gaussianMBKernel (Real.exp (-a * t)) (xiZero q - ((σ : ℂ) + t * I)) =
      ∑ j ∈ Finset.range (P.natDegree + 1),
        P.coeff j * dampingSampleWeight β h ((σ : ℂ) + t * I) j *
          exceptionalGaussianExpansionError F ((σ : ℂ) + t * I)
            (geometricGaussianDamping a h t j) := by
  have hp := polynomial_dampingFilter_gaussianMode P β a h t ((σ : ℂ) + t * I) 1
  have hz := fun q => polynomial_dampingFilter_gaussianMode P β a h t
    ((σ : ℂ) + t * I) (xiZero q)
  rw [← hp]
  simp_rw [← hz]
  rw [Finset.sum_comm (s := F) (t := Finset.range (P.natDegree + 1))]
  simp only [primeDampingFilter, continuedDampingCorrection, exceptionalGaussianExpansionError,
    mul_add, mul_sub, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    mul_assoc]

private theorem finite_layer_separates_high_line (F : Finset XiZeroCopy)
    {θ σ : ℝ} (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) :
    ∃ δ H : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 4 ≤ H ∧
      ∀ t : ℝ, H ≤ t → ∀ q : XiZeroCopy,
        δ ≤ ‖xiZero q - ((σ : ℂ) + t * I)‖ := by
  classical
  let δ := min (σ - θ) 1
  let M : ℝ := ∑ q ∈ F, |(xiZero q).im|
  have hδ : 0 < δ := lt_min (sub_pos.mpr hgap) zero_lt_one
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨δ, M + δ + 4, hδ, min_le_right _ _, by linarith only [hM, hδ], ?_⟩
  intro t ht q
  by_cases hq : q ∈ F
  · have hqm : |(xiZero q).im| ≤ M :=
      Finset.single_le_sum (fun p _ => abs_nonneg (xiZero p).im) hq
    have hb := Complex.im_le_norm (((σ : ℂ) + t * I) - xiZero q)
    simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero,
      add_zero, zero_add] at hb
    rw [norm_sub_rev] at hb
    linarith only [hb, hqm, ht, le_abs_self (xiZero q).im]
  · have hr := hrest q hq
    have hb := Complex.re_le_norm (((σ : ℂ) + t * I) - xiZero q)
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero] at hb
    rw [norm_sub_rev] at hb
    have hd : δ ≤ σ - θ := min_le_left _ _
    linarith only [hb, hr, hd]

private theorem expansionError_eq_finitePartError (F : Finset XiZeroCopy)
    {s : ℂ} (hs0 : 0 < s.re) (hsne1 : s ≠ 1) (hxi : xi s ≠ 0) (y : ℝ) :
    exceptionalGaussianExpansionError F s y = finiteGaussianFinitePartError F s y +
      ((Real.exp (-y) : ℂ) / (1 - s) + gaussianIncompleteMellin y (1 - s) -
        gaussianMBKernel y (1 - s)) := by
  have hζ : riemannZeta s ≠ 0 := by
    intro hz
    apply hxi
    have hsne0 : s ≠ 0 := by intro h; simp [h] at hs0
    rw [xi_eq_xiUnit_mul_zeta hsne0 hsne1 hs0, hz, mul_zero]
  have hdec : gaussianArchimedeanCurrent s - logDeriv xi s =
      -logDeriv riemannZeta s - (s - 1)⁻¹ := by
    rw [logDeriv_zeta_eq_logDeriv_xi hs0 hsne1 hζ, gaussianArchimedeanCurrent]
    ring
  rw [exceptionalGaussianExpansionError, finiteGaussianFinitePartError,
    gaussianPrimeContinuumGap, hdec, show (1 : ℂ) - s = -(s - 1) by ring,
    div_neg, div_eq_mul_inv]
  ring

/-- A complementary horizontal gap bounds the continued logarithmic derivative
and the complete Gaussian error uniformly on the high observation line. -/
theorem finite_layer_prime_current_bounds (F : Finset XiZeroCopy)
    {θ σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ) :
    ∃ H C D : ℝ, 4 ≤ H ∧ 0 < C ∧ 0 < D ∧
      ∀ t : ℝ, H ≤ t →
        ‖logDeriv riemannZeta ((σ : ℂ) + t * I)‖ ≤ D * t ∧
        ∀ y : ℝ, 0 < y → y ≤ 1 →
          ‖exceptionalGaussianExpansionError F ((σ : ℂ) + t * I) y‖ ≤
            C * (y + y ^ ((σ - θ) / 2)) * (1 + Real.log t) := by
  obtain ⟨δ, H, hδ, hδ1, hH, hsep⟩ := finite_layer_separates_high_line F hgap hrest
  have hσ0 : 0 < σ := by linarith only [hσ]
  obtain ⟨C, hC, hbound⟩ := exists_finiteGaussianFinitePartError_bound hσ0 hδ F hrest
  let D : ℝ := |logDerivZetaConstant / δ| + 1
  have hD : 0 < D := by dsimp only [D]; positivity
  refine ⟨H, C + 4, D, hH, by positivity, hD, ?_⟩
  intro t ht
  have ht4 : 4 ≤ t := hH.trans ht
  have ht0 : 0 < t := by linarith only [ht4]
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht4])
  have hlogt : Real.log t ≤ t := Real.log_le_self ht0.le
  have hregular : ((σ : ℂ) + t * I) ∈ gaussianRegularHighStrip σ δ := by
    exact ⟨by simp, by simpa using hσ1.le, by simpa using ht4, hsep t ht⟩
  have hxi : xi ((σ : ℂ) + t * I) ≠ 0 := xi_ne_zero_of_separated hδ (hsep t ht)
  have hs0 : 0 < ((σ : ℂ) + t * I).re := by simpa using hσ0
  have hsne1 : (σ : ℂ) + t * I ≠ 1 := by
    intro he
    have he' := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.one_im] at he'
    linarith only [he', ht4]
  constructor
  · have hb := norm_logDeriv_zeta_le hσ.le (by linarith only [hσ1] : σ ≤ 2) ht4 hδ hδ1
      (fun q => by simpa only [norm_sub_rev, xiZero] using hsep t ht q)
    calc
      _ ≤ logDerivZetaConstant * Real.log t / δ := hb
      _ ≤ D * Real.log t := by
        rw [mul_div_right_comm]
        apply mul_le_mul_of_nonneg_right _ hlog
        exact (le_abs_self _).trans (by dsimp only [D]; linarith)
      _ ≤ D * t := mul_le_mul_of_nonneg_left hlogt hD.le
  · intro y hy hy1
    have hf := hbound y hy hy1 _ hregular
    have hp := norm_gaussianContinuum_pole_error_le (s := (σ : ℂ) + t * I)
      (by simpa using hσ1.le) (by simpa using (show 1 ≤ t by linarith only [ht4])) hy hy1
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add] at hf
    rw [expansionError_eq_finitePartError F hs0 hsne1 hxi]
    refine (norm_add_le _ _).trans ((add_le_add hf hp).trans ?_)
    have hpow : 0 ≤ y ^ ((σ - θ) / 2) := by positivity
    have hL : 1 ≤ 1 + Real.log t := by linarith only [hlog]
    have hyL : y ≤ (y + y ^ ((σ - θ) / 2)) * (1 + Real.log t) := by
      calc
        y ≤ y + y ^ ((σ - θ) / 2) := le_add_of_nonneg_right hpow
        _ ≤ _ := le_mul_of_one_le_right (by positivity) hL
    nlinarith only [hyL]

/-- Any nonnegative, possibly varying geometric damping step preserves the
vanishing full-current error at positive exponential speed. -/
theorem tendsto_variable_geometric_expansion_error (F : Finset XiZeroCopy)
    {θ σ a : ℝ} {h : ℝ → ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (ha : 0 < a) (hh : ∀ᶠ t : ℝ in atTop, 0 ≤ h t) (j : ℕ) :
    Tendsto (fun t : ℝ => exceptionalGaussianExpansionError F ((σ : ℂ) + t * I)
      (geometricGaussianDamping a (h t) t j)) atTop (𝓝 0) := by
  obtain ⟨H, C, D, hH, hC, _, hb⟩ := finite_layer_prime_current_bounds F hσ hσ1 hgap hrest
  let p : ℝ := (σ - θ) / 2
  have hp : 0 < p := by dsimp only [p]; linarith only [hgap]
  have hE : Tendsto (fun t : ℝ =>
      C * (t * Real.exp (-(a * t)) + t * Real.exp (-(a * p * t)))) atTop (𝓝 0) := by
    have h₁ := HTGeometry.tendsto_pow_mul_exp_neg_scaled 1 ha
    have h₂ := HTGeometry.tendsto_pow_mul_exp_neg_scaled 1 (mul_pos ha hp)
    simpa only [pow_one, add_zero, mul_zero] using (h₁.add h₂).const_mul C
  apply squeeze_zero_norm' _ hE
  filter_upwards [eventually_ge_atTop H, hh] with t ht hht
  have ht0 : 0 < t := by linarith only [ht, hH]
  have hy : 0 < geometricGaussianDamping a (h t) t j := Real.exp_pos _
  have hyx : geometricGaussianDamping a (h t) t j ≤ Real.exp (-a * t) := by
    apply Real.exp_le_exp.mpr
    have hjh : 0 ≤ 2 * (j : ℝ) * h t := by positivity
    linarith only [hjh]
  have hx1 : Real.exp (-a * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) ht0.le)
  have hpow : geometricGaussianDamping a (h t) t j ^ p ≤ Real.exp (-a * t) ^ p := by
    gcongr
  have hlog : 1 + Real.log t ≤ t := by
    linarith only [Real.log_le_sub_one_of_pos ht0]
  have hnonneg : 0 ≤ 1 + Real.log t := by
    have := Real.log_nonneg (show 1 ≤ t by linarith only [ht, hH])
    linarith only [this]
  have hbound := (hb t ht).2 (geometricGaussianDamping a (h t) t j) hy (hyx.trans hx1)
  have he : Real.exp (-a * t) ^ p = Real.exp (-(a * p * t)) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  calc
    _ ≤ C * (geometricGaussianDamping a (h t) t j +
        geometricGaussianDamping a (h t) t j ^ p) * (1 + Real.log t) := hbound
    _ ≤ C * (Real.exp (-a * t) + Real.exp (-a * t) ^ p) * (1 + Real.log t) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hyx hpow) hC.le) hnonneg
    _ ≤ C * (Real.exp (-a * t) + Real.exp (-a * t) ^ p) * t :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by rw [he]; ring

/-- Nonnegative damping shifts give contractive sample weights below the top. -/
theorem norm_dampingSampleWeight_le_one {β σ h : ℝ}
    (hσβ : σ ≤ β) (hh : 0 ≤ h) (t : ℝ) (j : ℕ) :
    ‖dampingSampleWeight β h ((σ : ℂ) + t * I) j‖ ≤ 1 := by
  rw [norm_dampingSampleWeight, Real.exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg (mul_nonneg (Nat.cast_nonneg j) hh) (sub_nonneg.mpr hσβ))

private theorem tendsto_logDeriv_div_gaussianMode (F : Finset XiZeroCopy)
    {θ σ a : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    {ρ : ℂ} (hr : 0 < gaussianObservationRate ρ σ a) :
    Tendsto (fun t : ℝ => logDeriv riemannZeta ((σ : ℂ) + t * I) /
      gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))) atTop (𝓝 0) := by
  obtain ⟨H, C, D, hH, _, hD, hb⟩ := finite_layer_prime_current_bounds F hσ hσ1 hgap hrest
  obtain ⟨A, B, N, M, _, hB, hmode⟩ := exists_gaussianMode_exponential_bounds ρ σ
  apply HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp (C := D * B) (N := M + 1) hr
  filter_upwards [eventually_ge_atTop (max H (|ρ.im| + 2))] with t ht
  have htH : H ≤ t := (le_max_left _ _).trans ht
  have ht0 : 0 ≤ t := by linarith only [htH, hH]
  have hlarge : |ρ.im| + 2 ≤ t := (le_max_right _ _).trans ht
  rw [div_eq_mul_inv, norm_mul]
  calc
    _ ≤ (D * t) * (B * t ^ M * Real.exp (-(gaussianObservationRate ρ σ a * t))) :=
      mul_le_mul (hb t htH).1 (hmode t hlarge a).2 (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Contractive weights preserve a vanishing complex error. -/
theorem tendsto_bounded_weight_mul_zero {w f : ℝ → ℂ}
    (hw : ∀ t, ‖w t‖ ≤ 1) (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun t => w t * f t) atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa only [norm_zero] using hf.norm)
  exact Eventually.of_forall fun t => by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw t)

/-- A polynomial killing the unwanted nodes retains exactly the selected
zero's multiplicity in the finite divisor sum. -/
theorem filtered_divisor_eq_selected_mode (F : Finset XiZeroCopy)
    (P : Polynomial ℂ) (σ β a h t : ℝ) (ρ : ℂ)
    (hkill : ∀ q ∈ F, xiZero q ≠ ρ →
      P.eval (Complex.exp ((h : ℂ) * (xiZero q - β))) = 0) :
    (∑ q ∈ F, P.eval (Complex.exp ((h : ℂ) * (xiZero q - β))) *
      gaussianMBKernel (Real.exp (-a * t)) (xiZero q - ((σ : ℂ) + t * I))) =
      ((F.filter (fun q => xiZero q = ρ)).card : ℂ) *
        P.eval (Complex.exp ((h : ℂ) * (ρ - β))) *
          gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun q => xiZero q = ρ)]
  · calc
      _ = ∑ _q ∈ F.filter (fun q => xiZero q = ρ),
          P.eval (Complex.exp ((h : ℂ) * (ρ - β))) *
            gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I)) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.mp hq).2]
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring
  · intro q hq hn
    by_contra hne
    exact hn (by rw [hkill q hq hne, zero_mul])

/-- Once its pole and unwanted divisor nodes are roots, a damping filter
reads precisely the selected multiplicity from the literal prime sums. -/
theorem primeDampingFilter_reads_selected_zero (F : Finset XiZeroCopy)
    {θ σ β a h : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hgap : θ < σ)
    (hrest : ∀ q : XiZeroCopy, q ∉ F → (xiZero q).re ≤ θ)
    (hσβ : σ ≤ β) (ha : 0 < a) (hh : 0 ≤ h)
    (ρ : ℂ) (hr : 0 < gaussianObservationRate ρ σ a) (P : Polynomial ℂ)
    (hpole : P.eval (Complex.exp ((h : ℂ) * (1 - β))) = 0)
    (hkill : ∀ q ∈ F, xiZero q ≠ ρ →
      P.eval (Complex.exp ((h : ℂ) * (xiZero q - β))) = 0) :
    Tendsto (fun t : ℝ => primeDampingFilter P σ β a h t /
      gaussianMBKernel (Real.exp (-a * t)) (ρ - ((σ : ℂ) + t * I))) atTop
      (𝓝 (-((F.filter (fun q => xiZero q = ρ)).card : ℂ) *
        P.eval (Complex.exp ((h : ℂ) * (ρ - β))))) := by
  classical
  let K : ℝ → ℂ := fun t => gaussianMBKernel (Real.exp (-a * t))
    (ρ - ((σ : ℂ) + t * I))
  have hKinv : Tendsto (fun t => (K t)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_gaussianMode_zero_of_positive_rate ρ σ a hr
  have hKnorm : Tendsto (fun t => ‖K t‖) atTop atTop :=
    tendsto_norm_gaussianMode_atTop_of_positive_rate ρ σ a hr
  have hE := tendsto_finsetSum (Finset.range (P.natDegree + 1)) fun j _ =>
    (tendsto_bounded_weight_mul_zero
      (fun t => norm_dampingSampleWeight_le_one hσβ hh t j)
      (tendsto_variable_geometric_expansion_error F hσ hσ1 hgap hrest ha
        (Eventually.of_forall fun _ => hh) j)).const_mul (P.coeff j)
  simp only [mul_zero, Finset.sum_const_zero] at hE
  have hEdiv := hE.mul hKinv
  simp only [mul_zero] at hEdiv
  have hlog := tendsto_logDeriv_div_gaussianMode F hσ hσ1 hgap hrest hr
  have hLterm (j : ℕ) : Tendsto (fun t : ℝ =>
      P.coeff j * (dampingSampleWeight β h ((σ : ℂ) + t * I) j *
        (Real.exp (-geometricGaussianDamping a h t j) : ℂ)) *
          (logDeriv riemannZeta ((σ : ℂ) + t * I) / K t)) atTop (𝓝 0) := by
    have hw (t : ℝ) : ‖dampingSampleWeight β h ((σ : ℂ) + t * I) j *
        (Real.exp (-geometricGaussianDamping a h t j) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have he : Real.exp (-geometricGaussianDamping a h t j) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.exp_pos _).le)
      exact (mul_le_mul (norm_dampingSampleWeight_le_one hσβ hh t j) he
        (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
    have hh' := (tendsto_bounded_weight_mul_zero hw hlog).const_mul (P.coeff j)
    simpa only [mul_zero, mul_assoc] using hh'
  have hL : Tendsto (fun t => continuedDampingCorrection P σ β a h t / K t)
      atTop (𝓝 0) := by
    have hs := tendsto_finsetSum (Finset.range (P.natDegree + 1)) (fun j _ => hLterm j)
    simp only [Finset.sum_const_zero] at hs
    apply hs.congr
    intro t
    rw [continuedDampingCorrection, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  let c : ℂ := ((F.filter (fun q => xiZero q = ρ)).card : ℂ) *
    P.eval (Complex.exp ((h : ℂ) * (ρ - β)))
  have hdivisor (t : ℝ) : (∑ q ∈ F,
      P.eval (Complex.exp ((h : ℂ) * (xiZero q - β))) *
        gaussianMBKernel (Real.exp (-a * t)) (xiZero q - ((σ : ℂ) + t * I))) = c * K t := by
    exact filtered_divisor_eq_selected_mode F P σ β a h t ρ hkill
  have hfinal := (hEdiv.sub hL).sub_const c
  simp only [sub_zero, zero_sub] at hfinal
  have hanswer : Tendsto (fun t => primeDampingFilter P σ β a h t / K t)
      atTop (𝓝 (-c)) := by
    apply hfinal.congr'
    filter_upwards [hKnorm.eventually (eventually_gt_atTop (0 : ℝ))] with t ht
    have hne : K t ≠ 0 := norm_pos_iff.mp ht
    simp only [← mul_assoc]
    rw [← div_eq_mul_inv, ← primeDampingFilter_expansion, hpole, zero_mul, sub_zero,
      hdivisor, add_div, add_div, mul_div_cancel_right₀ _ hne]
    ring
  simpa only [c, K, neg_mul] using hanswer

private theorem exists_small_divisor_exponential_injective (S : Finset ℂ)
    (β : ℝ) {B : ℝ} (hB : 0 < B) :
    ∃ h : ℝ, 0 < h ∧ h < B ∧
      Set.InjOn (fun z : ℂ => Complex.exp ((h : ℂ) * (z - β))) (S : Set ℂ) := by
  classical
  let M : ℝ := ∑ z ∈ S, |z.im|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hden : 0 < M + 1 := by linarith only [hM]
  obtain ⟨h, hh0, hh⟩ := exists_between (lt_min hB (div_pos Real.pi_pos hden))
  have hhB : h < B := hh.trans_le (min_le_left _ _)
  have hhm : h * (M + 1) < Real.pi :=
    (lt_div_iff₀ hden).mp (hh.trans_le (min_le_right _ _))
  have hphase : ∀ z ∈ S, |((h : ℂ) * (z - β)).im| < Real.pi := by
    intro z hz
    have hb : |z.im| ≤ M := Finset.single_le_sum (fun w _ => abs_nonneg w.im) hz
    have hm := mul_le_mul_of_nonneg_left hb hh0.le
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.sub_im,
      Complex.ofReal_im, sub_zero, zero_mul, add_zero, abs_mul, abs_of_pos hh0]
    nlinarith only [hm, hhm, hh0]
  refine ⟨h, hh0, hhB, ?_⟩
  intro z hz w hw he
  have hz' := abs_lt.mp (hphase z hz)
  have hw' := abs_lt.mp (hphase w hw)
  have heq := Complex.exp_inj_of_neg_pi_lt_of_le_pi hz'.1 hz'.2.le hw'.1 hw'.2.le he
  have hs := mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hh0.ne') heq
  calc
    z = (z - β) + β := by ring
    _ = (w - β) + β := congrArg (fun x : ℂ => x + β) hs
    _ = w := by ring

/-- A polynomial removing the pole and all exceptional points except one target. -/
def divisorDampingFilter (F : Finset XiZeroCopy) (ρ : ℂ) (β h : ℝ) : Polynomial ℂ :=
  (Polynomial.X - Polynomial.C (Complex.exp ((h : ℂ) * (1 - β)))) *
    ∏ q ∈ F.filter (fun q => xiZero q ≠ ρ),
      (Polynomial.X - Polynomial.C (Complex.exp ((h : ℂ) * (xiZero q - β))))

/-- The pole node is always a root of the divisor filter. -/
theorem divisorDampingFilter_pole (F : Finset XiZeroCopy) (ρ : ℂ) (β h : ℝ) :
    (divisorDampingFilter F ρ β h).eval (Complex.exp ((h : ℂ) * (1 - β))) = 0 := by
  simp [divisorDampingFilter]

/-- Every unwanted exceptional point is a root of the divisor filter. -/
theorem divisorDampingFilter_kills (F : Finset XiZeroCopy) (ρ : ℂ) (β h : ℝ)
    {q : XiZeroCopy} (hq : q ∈ F) (hne : xiZero q ≠ ρ) :
    (divisorDampingFilter F ρ β h).eval (Complex.exp ((h : ℂ) * (xiZero q - β))) = 0 := by
  classical
  simp only [divisorDampingFilter, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hz : (∏ p ∈ F.filter (fun p => xiZero p ≠ ρ),
      (Complex.exp ((h : ℂ) * (xiZero q - β)) -
        Complex.exp ((h : ℂ) * (xiZero p - β)))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨hq, hne⟩) (sub_self _)
  rw [hz, mul_zero]

private theorem divisorDampingFilter_survives (F : Finset XiZeroCopy) (β h : ℝ)
    {q : XiZeroCopy} (hq : q ∈ F)
    (hinj : Set.InjOn (fun z : ℂ => Complex.exp ((h : ℂ) * (z - β)))
      ((insert 1 (F.image xiZero) : Finset ℂ) : Set ℂ)) :
    (divisorDampingFilter F (xiZero q) β h).eval
      (Complex.exp ((h : ℂ) * (xiZero q - β))) ≠ 0 := by
  classical
  simp only [divisorDampingFilter, Polynomial.eval_mul, Polynomial.eval_prod,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  have hqin : xiZero q ∈ (insert 1 (F.image xiZero) : Finset ℂ) :=
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hq)
  apply mul_ne_zero
  · apply sub_ne_zero.mpr
    intro he
    have heq := hinj hqin (Finset.mem_insert_self _ _) he
    have hr := xiZeroCopy_re_lt_one q
    change (xiZero q).re < 1 at hr
    rw [heq] at hr
    exact (lt_irrefl (1 : ℝ)) hr
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    obtain ⟨hpF, hpq⟩ := Finset.mem_filter.mp hp
    exact sub_ne_zero.mpr fun he => hpq
      (hinj (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hpF)) hqin he.symm)

private theorem divisorDampingFilter_degree_le (F : Finset XiZeroCopy)
    (ρ : ℂ) (β h : ℝ) :
    (divisorDampingFilter F ρ β h).natDegree ≤ F.card + 1 := by
  classical
  have hp : (∏ q ∈ F.filter (fun q => xiZero q ≠ ρ),
      (Polynomial.X - Polynomial.C (Complex.exp ((h : ℂ) * (xiZero q - β))))).natDegree ≤
      F.card := by
    calc
      _ ≤ ∑ q ∈ F.filter (fun q => xiZero q ≠ ρ),
          (Polynomial.X - Polynomial.C
            (Complex.exp ((h : ℂ) * (xiZero q - β)))).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ = (F.filter (fun q => xiZero q ≠ ρ)).card := by simp
      _ ≤ F.card := Finset.card_filter_le _ _
  have hd : (divisorDampingFilter F ρ β h).natDegree ≤
      (Polynomial.X - Polynomial.C (Complex.exp ((h : ℂ) * (1 - β)))).natDegree +
        (∏ q ∈ F.filter (fun q => xiZero q ≠ ρ),
          (Polynomial.X - Polynomial.C
            (Complex.exp ((h : ℂ) * (xiZero q - β))))).natDegree :=
    Polynomial.natDegree_mul_le
  simp only [Polynomial.natDegree_X_sub_C] at hd
  exact hd.trans (by omega)

/-- A nonzero ratio limit transfers divergence of the reference norm. -/
theorem norm_tendsto_atTop_of_ratio {f g : ℝ → ℂ} {c : ℂ}
    (hc : c ≠ 0) (hlim : Tendsto (fun t => f t / g t) atTop (𝓝 c))
    (hg : Tendsto (fun t => ‖g t‖) atTop atTop) :
    Tendsto (fun t => ‖f t‖) atTop atTop := by
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr hc
  apply tendsto_atTop.2
  intro B
  filter_upwards [hlim.norm.eventually
    (eventually_gt_nhds (show ‖c‖ / 2 < ‖c‖ by linarith only [hc0])),
    hg.eventually_ge_atTop (2 * (|B| + 1) / ‖c‖)] with t ht hgt
  have hg0 : 0 < ‖g t‖ := (by positivity : 0 < 2 * (|B| + 1) / ‖c‖).trans_le hgt
  rw [norm_div] at ht
  have hfg := (lt_div_iff₀ hg0).mp ht
  have hbig := mul_le_mul_of_nonneg_left hgt (show 0 ≤ ‖c‖ / 2 by positivity)
  have he : ‖c‖ / 2 * (2 * (|B| + 1) / ‖c‖) = |B| + 1 := by
    field_simp
  rw [he] at hbig
  linarith only [hfg, hbig, le_abs_self B]

/-- Failure of AAL is detected at every sufficiently large height by an explicit
finite weighted sum of literal prime sums. The damping samples fit inside any
prescribed logarithmic window; the filter reads each top zero's multiplicity
and cancels the zeta pole exactly. -/
theorem not_asymptoticAbscissaLaw_has_prime_only_divisor_filters :
    ¬ AsymptoticAbscissaLaw →
      ∃ (F : Finset XiZeroCopy) (σ β : ℝ),
        1 / 2 < σ ∧ σ < β ∧ β < 1 ∧
        (∃ q ∈ F, (xiZero q).re = β) ∧
        (∀ q : XiZeroCopy, (xiZero q).re ≤ β) ∧
        ∀ L : ℝ, 0 < L → ∃ h : ℝ, 0 < h ∧
          (∀ j : ℕ, j ≤ F.card + 1 → (j : ℝ) * h < L) ∧
          ∀ q ∈ F, (xiZero q).re = β →
            (divisorDampingFilter F (xiZero q) β h).natDegree ≤ F.card + 1 ∧
            (divisorDampingFilter F (xiZero q) β h).eval
              (Complex.exp ((h : ℂ) * (xiZero q - β))) ≠ 0 ∧
            ∀ a : ℝ, 0 < a → Real.pi / 2 < a * (β - σ) →
              Tendsto (fun t : ℝ =>
                primeDampingFilter (divisorDampingFilter F (xiZero q) β h) σ β a h t /
                  gaussianMBKernel (Real.exp (-a * t))
                    (xiZero q - ((σ : ℂ) + t * I))) atTop
                (𝓝 (-((F.filter (fun p => xiZero p = xiZero q)).card : ℂ) *
                  (divisorDampingFilter F (xiZero q) β h).eval
                    (Complex.exp ((h : ℂ) * (xiZero q - β))))) ∧
              Tendsto (fun t : ℝ =>
                ‖primeDampingFilter (divisorDampingFilter F (xiZero q) β h) σ β a h t‖)
                atTop atTop := by
  classical
  intro hnot
  obtain ⟨F, θ, σ, β, hθ, hgap, hσβ, hβ1, htop, hmax, hrest, _⟩ :=
    not_asymptoticAbscissaLaw_has_escaping_layer_profile hnot
  have hσ : 1 / 2 < σ := by linarith only [hθ, hgap]
  have hσ1 : σ < 1 := hσβ.trans hβ1
  have hall : ∀ q : XiZeroCopy, (xiZero q).re ≤ β := by
    intro q
    by_cases hq : q ∈ F
    · exact hmax q hq
    · exact (hrest q hq).trans (hgap.trans hσβ).le
  refine ⟨F, σ, β, hσ, hσβ, hβ1, htop, hall, ?_⟩
  intro L hL
  obtain ⟨h, hh0, hhB, hinj⟩ := exists_small_divisor_exponential_injective
    (insert 1 (F.image xiZero)) β
    (div_pos hL (by positivity : (0 : ℝ) < (F.card : ℝ) + 2))
  refine ⟨h, hh0, ?_, ?_⟩
  · intro j hj
    have hjR : (j : ℝ) ≤ (F.card : ℝ) + 1 := by exact_mod_cast hj
    have hb := (lt_div_iff₀ (by positivity : (0 : ℝ) < (F.card : ℝ) + 2)).mp hhB
    have hc := mul_le_mul_of_nonneg_right hjR hh0.le
    nlinarith only [hb, hc, hh0]
  · intro q hq hqβ
    let P := divisorDampingFilter F (xiZero q) β h
    have heval : P.eval (Complex.exp ((h : ℂ) * (xiZero q - β))) ≠ 0 :=
      divisorDampingFilter_survives F β h hq hinj
    refine ⟨divisorDampingFilter_degree_le F _ β h, heval, ?_⟩
    intro a ha hsuper
    have hr : 0 < gaussianObservationRate (xiZero q) σ a := by
      rw [gaussianObservationRate, hqβ]
      linarith only [hsuper]
    have hlim := primeDampingFilter_reads_selected_zero F hσ hσ1 hgap hrest
      hσβ.le ha hh0.le (xiZero q) hr P (divisorDampingFilter_pole F _ β h)
      (fun p hp hne => divisorDampingFilter_kills F _ β h hp hne)
    have hm : 0 < (F.filter (fun p => xiZero p = xiZero q)).card :=
      Finset.card_pos.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
    have hc : -((F.filter (fun p => xiZero p = xiZero q)).card : ℂ) *
        P.eval (Complex.exp ((h : ℂ) * (xiZero q - β))) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm))) heval
    exact ⟨hlim, norm_tendsto_atTop_of_ratio hc hlim
      (tendsto_norm_gaussianMode_atTop_of_positive_rate (xiZero q) σ a hr)⟩

#print axioms gaussianMode_geometric_damping
#print axioms polynomial_dampingFilter_gaussianMode
#print axioms primeDampingFilter_expansion
#print axioms primeDampingFilter_reads_selected_zero
#print axioms not_asymptoticAbscissaLaw_has_prime_only_divisor_filters

end GaloisForLFunctions.ExceptionalLayerTheory
