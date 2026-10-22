import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerOddModel

/-!
# Parity selection of the restricted Weil ground state fails under a finite top layer

**Theorem** (`exists_aperture_ground_odd`). Suppose the non-real Xi spectral points form a finite
set with top layer `{t_j + iδ}` (`FiniteTopLayer δ t`), and the leading-order parity balance
`F(θ) = λ_max(T(θ)) − λ_max(T(θ + π𝟙))` of the Cauchy model with the quartet multiplicities is
positive at one aperture phase `θ(a₁)`, `θ_j(a) = −2t_j a`. Then at arbitrarily large apertures every
ground state of the CCM restricted Weil form is reflection-odd.

By `ccm_exists_large_aperture_odd_wins_of_even_relations` the positivity hypothesis holds whenever
every integer relation `Σ k_j t_j = 0` has even coefficient sum, in particular for `ℚ`-independent
ordinates (`exists_aperture_ground_odd_of_even_relations`).

**Proof.**
* The aperture line returns near `θ(a₁)` with `F ≥ g > 0` (`exists_balance_ge_frequently`), and
  there `λ_max(θ) − max(λ_max(θ + π𝟙), 0) ≥ g/2` (`gap_ge_of_balance_ge`).
* Even floor: `Q ≥ −(e^{2δa}(Λ'/2 + O(e^{−δa})) + L(a)) ‖u‖²` (`sourceQuadratic_ge_of_isEven`).
* Odd test: for the maximizer `x` of the model form, the truncated odd model
  `W_a = (P(a − ·) − P(a + ·)) · 1_{(−a,a)}` has top-layer contribution
  `−e^{2δa} T(θ)[W_a(a − ·)] ≤ −e^{2δa}(λ_max − O(a e^{−δa}))`, mass `≤ 2 + O(a e^{−2δa})`, lower
  copies `O(a e^{2δ'a})` and critical-line part `O(a²)`. Coefficients of maximizers are bounded
  uniformly by coercivity, so all errors are `o(e^{2δa})` uniformly (`tendsto_errorRate`).
* A smooth cutoff of `W_a` lies below the even floor (`exists_smooth_below_model`), so the ground
  energy is below the floor and the even part of every ground state vanishes.
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-! ## Transforms of real interval sources -/

theorem norm_testTransform_sq_le_of_realIntervalSource {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℝ}
    (hg : RealIntervalSource a g) (w : ℂ) :
    ‖testTransform (fun x => (g x : ℂ)) w‖ ^ 2 ≤
      (∫ x, g x ^ 2) * (2 * a * Real.exp (2 * a * |w.im|)) := by
  have hexp : Continuous fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ)) := by fun_prop
  have heq : testTransform (fun x => (g x : ℂ)) w =
      ∫ x, (g x : ℂ) * (Icc (-a) a).indicator
        (fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ))) x := by
    unfold testTransform
    congr 1
    funext x
    by_cases hx : x ∈ Icc (-a) a
    · rw [indicator_of_mem hx]
    · rw [indicator_of_notMem hx]
      have hxa : a ≤ |x| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hx
        rcases hx with h | h
        · exact le_trans (by linarith) (neg_le_abs x)
        · exact h.le.trans (le_abs_self x)
      simp [hg.vanish x hxa]
  rw [heq]
  have hCS : ‖∫ x, ((g x : ℝ) : ℂ) * (Icc (-a) a).indicator
      (fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ))) x‖ ^ 2 ≤
      (∫ x, ‖((g x : ℝ) : ℂ)‖ ^ 2) *
        ∫ x, ‖(Icc (-a) a).indicator (fun x : ℝ => Complex.exp (Complex.I * w * (x : ℂ))) x‖ ^ 2 :=
    norm_integral_mul_sq_le (hg.memLp.ofReal (K := ℂ)) (memLp_indicator_Icc hexp a)
  refine hCS.trans ?_
  have hN : ∫ x, ‖((g x : ℝ) : ℂ)‖ ^ 2 = ∫ x, g x ^ 2 := by
    congr 1; funext x; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hN]
  apply mul_le_mul_of_nonneg_left _ (integral_nonneg fun _ => sq_nonneg _)
  apply integral_norm_sq_indicator_le ha
  intro x hx
  rw [Complex.norm_exp, ← Real.exp_nat_mul]
  apply Real.exp_le_exp.mpr
  have hre : (Complex.I * w * (x : ℂ)).re = -(w.im * x) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have hx' : |x| ≤ a := abs_le.mpr ⟨hx.1, hx.2⟩
  have : -(w.im * x) ≤ |w.im| * a := by
    have h1 : -(w.im * x) ≤ |w.im * x| := neg_le_abs _
    rw [abs_mul] at h1
    nlinarith [abs_nonneg w.im]
  push_cast
  linarith

/-- **The off-line part of the truncated odd model.** -/
theorem offLine_truncModel_le {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) (x : Fin m → ℂ)
    {a : ℝ} (ha : 0 ≤ a) :
    ∑ q ∈ h.offLine,
        (zeroSumTerm (fun y => ((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ))
          (xiSpectralPoint q)).re ≤
      -(Real.exp (2 * δ * a) * halfLineForm δ t h.mult (aperturePhase t a)
          (fun s => truncModel (oddProfileModel δ t x a) a (a - s))) +
        (∫ y, truncModel (oddProfileModel δ t x a) a y ^ 2) * h.lowWeight a := by
  set f : ℝ → ℝ := truncModel (oddProfileModel δ t x a) a with hf
  have hI : RealIntervalSource a f := realIntervalSource_truncModel t x a
  set N := ∫ y, f y ^ 2 with hN
  rw [h.sum_offLine_eq, sum_top_truncModel_eq h x a]
  have hlow : ∀ q ∈ h.lowSet, (zeroSumTerm (fun y => ((f y : ℝ) : ℂ)) (xiSpectralPoint q)).re ≤
      N * (2 * a * Real.exp (2 * a * |(xiSpectralPoint q).im|)) := by
    intro q _
    have h1 := norm_testTransform_sq_le_of_realIntervalSource ha hI (-xiSpectralPoint q)
    have h2 := norm_testTransform_sq_le_of_realIntervalSource ha hI
      (-(starRingEnd ℂ) (xiSpectralPoint q))
    simp only [Complex.neg_im, Complex.conj_im, neg_neg, abs_neg] at h1 h2
    refine (Complex.re_le_norm _).trans ?_
    unfold zeroSumTerm
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg (testTransform (fun y => ((f y : ℝ) : ℂ)) (-xiSpectralPoint q)),
      norm_nonneg (testTransform (fun y => ((f y : ℝ) : ℂ)) (-(starRingEnd ℂ) (xiSpectralPoint q))),
      sq_nonneg (‖testTransform (fun y => ((f y : ℝ) : ℂ)) (-xiSpectralPoint q)‖ -
        ‖testTransform (fun y => ((f y : ℝ) : ℂ)) (-(starRingEnd ℂ) (xiSpectralPoint q))‖)]
  have hlowsum : ∑ q ∈ h.lowSet,
      (zeroSumTerm (fun y => ((f y : ℝ) : ℂ)) (xiSpectralPoint q)).re ≤ N * h.lowWeight a := by
    rw [FiniteTopLayer.lowWeight, Finset.mul_sum]
    exact Finset.sum_le_sum hlow
  linarith

/-! ## A quantitative window and its returns -/

theorem exists_phase_window_balance_ge {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ₁ : Fin m → ℝ)
    (hpos : 0 < ccmParityBalance δ t M θ₁) :
    ∃ η : ℝ, 0 < η ∧ ∀ (θ : Fin m → ℝ) (z : Fin m → ℤ),
      (∀ j, |θ j - θ₁ j - z j * (2 * Real.pi)| ≤ η) →
        ccmParityBalance δ t M θ₁ / 2 ≤ ccmParityBalance δ t M θ := by
  set g : ℝ := ccmParityBalance δ t M θ₁ with hg
  obtain ⟨B, hB0, hB⟩ := exists_quadForm_sub_le hδ ht htpos
  set S : ℝ := ∑ j, |M j| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  refine ⟨g / (4 * (B + 1) * (S + 1)), by positivity, fun θ z hphase => ?_⟩
  set η : ℝ := g / (4 * (B + 1) * (S + 1)) with hη
  have hD := sum_norm_phaseWeight_sub_le M θ θ₁ z hphase
  have hD' := sum_norm_phaseWeight_sub_le M (halfTurn θ) (halfTurn θ₁) z
    (fun j => by rw [halfTurn_sub]; exact hphase j)
  have hL1 := abs_ccmLambdaMax_sub_le hδ ht htpos hm hB M θ θ₁
  have hL2 := abs_ccmLambdaMax_sub_le hδ ht htpos hm hB M (halfTurn θ) (halfTurn θ₁)
  have hbal : ccmParityBalance δ t M θ ≥ g - 2 * (B * (S * η)) := by
    have e1 : B * ∑ i, ‖phaseWeight M θ i - phaseWeight M θ₁ i‖ ≤ B * (S * η) :=
      mul_le_mul_of_nonneg_left hD hB0
    have e2 : B * ∑ i, ‖phaseWeight M (halfTurn θ) i - phaseWeight M (halfTurn θ₁) i‖
        ≤ B * (S * η) := mul_le_mul_of_nonneg_left hD' hB0
    rw [hg]
    unfold ccmParityBalance
    rw [abs_le] at hL1 hL2
    linarith [hL1.1, hL2.2]
  have hsmall : 2 * (B * (S * η)) ≤ g / 2 := by
    rw [hη]
    have : 2 * (B * (S * (g / (4 * (B + 1) * (S + 1))))) =
        g * (B * S) / (2 * ((B + 1) * (S + 1))) := by field_simp; ring
    rw [this, div_le_iff₀ (by positivity)]
    have hBS : B * S ≤ (B + 1) * (S + 1) := by nlinarith
    have := mul_le_mul_of_nonneg_left hBS hpos.le
    nlinarith
  linarith

/-- **Returns with a uniform positive balance.** -/
theorem exists_balance_ge_frequently {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ}
    (ht : Function.Injective t) (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M : Fin m → ℝ)
    (hpos : ∃ a₁ : ℝ, 0 < ccmParityBalance δ t M (aperturePhase t a₁)) :
    ∃ g : ℝ, 0 < g ∧ ∀ N : ℝ, ∃ a : ℝ, N ≤ a ∧ g ≤ ccmParityBalance δ t M (aperturePhase t a) := by
  obtain ⟨a₁, ha₁⟩ := hpos
  obtain ⟨η, hη, hwin⟩ := exists_phase_window_balance_ge hδ ht htpos hm M _ ha₁
  refine ⟨ccmParityBalance δ t M (aperturePhase t a₁) / 2, by linarith, fun N => ?_⟩
  obtain ⟨a, haN, z, hz⟩ := exists_large_aperture_phase_near (x := fun j => a₁ * (t j / Real.pi))
    (fun k hk => ⟨0, by
      rw [Int.cast_zero]
      have : ∑ j, (k j : ℝ) * (a₁ * (t j / Real.pi)) = a₁ / Real.pi * ∑ j, (k j : ℝ) * t j := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, hk, mul_zero]⟩) hη N
  refine ⟨a, haN, hwin _ z fun j => ?_⟩
  have h := hz j
  rwa [show -2 * Real.pi * (a₁ * (t j / Real.pi)) = -2 * t j * a₁ by field_simp] at h

/-- **The spectral gap of a positive balance.** -/
theorem gap_ge_of_balance_ge {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) {g : ℝ}
    (hg : g ≤ ccmParityBalance δ t M θ) (hg0 : 0 < g) :
    g / 2 ≤ ccmLambdaMax δ t M θ - max (ccmLambdaMax δ t M (halfTurn θ)) 0 := by
  unfold ccmParityBalance at hg
  by_cases h0 : 0 ≤ ccmLambdaMax δ t M (halfTurn θ)
  · rw [max_eq_left h0]; linarith
  · push Not at h0
    rw [max_eq_right h0.le]
    obtain ⟨x, hx, -, hle⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
    have h1 := lambdaMax_halfTurn_mul_ge hδ ht htpos hm M θ x
    have hn : normForm δ t x = 1 := hx
    rw [hn, mul_one] at h1
    have := hle x hx
    linarith

/-! ## Uniform bounds for maximizers -/

theorem profileBound_le_of_coercive {δ : ℝ} {t : Fin m → ℝ} {κ : ℝ} (hκ : 0 < κ)
    (hcoer : ∀ x, κ * ‖x‖ ^ 2 ≤ normForm δ t x) {x : Fin m → ℂ} (hx : x ∈ unitLevel δ t) :
    profileBound x ≤ 2 * m * max 1 (1 / κ) := by
  have hn : normForm δ t x = 1 := hx
  have h1 := hcoer x
  rw [hn] at h1
  have hxle : ‖x‖ ≤ max 1 (1 / κ) := by
    by_cases hx1 : ‖x‖ ≤ 1
    · exact hx1.trans (le_max_left _ _)
    · push Not at hx1
      have : ‖x‖ ≤ 1 / κ := by
        rw [le_div_iff₀ hκ]
        nlinarith [norm_nonneg x]
      exact this.trans (le_max_right _ _)
  unfold profileBound
  have hsum : ∑ j, ‖x j‖ ≤ m * max 1 (1 / κ) := by
    calc ∑ j, ‖x j‖ ≤ ∑ _j : Fin m, max 1 (1 / κ) :=
          Finset.sum_le_sum fun j _ => (norm_le_pi_norm x j).trans hxle
      _ = m * max 1 (1 / κ) := by simp
  linarith

theorem lambdaMax_le {δ : ℝ} (hδ : 0 < δ) {t : Fin m → ℝ} (ht : Function.Injective t)
    (htpos : ∀ j, 0 < t j) (hm : 0 < m) (M θ : Fin m → ℝ) :
    ccmLambdaMax δ t M θ ≤ (∑ j, |M j|) * (1 / (2 * δ)) := by
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm M θ
  have hn : normForm δ t x = 1 := hx
  rw [← hmax, quadForm_eq_halfLineForm hδ]
  unfold halfLineForm
  rw [Complex.re_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  have hP := norm_halfLinePairing_sq_le hδ t (memLp_realProfile hδ t x) j
  rw [← normForm_eq_integral hδ, hn, one_mul] at hP
  refine (Complex.re_le_norm _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I,
    mul_one, norm_pow]
  exact mul_le_mul_of_nonneg_left hP (abs_nonneg _)

/-! ## The error rate -/

theorem tendsto_pow_mul_exp_neg_mul {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Tendsto (fun a : ℝ => a ^ k * Real.exp (-(c * a))) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).comp
    (tendsto_id.const_mul_atTop hc)
  have h2 := h.const_mul ((c ^ k)⁻¹)
  rw [mul_zero] at h2
  refine h2.congr fun a => ?_
  simp only [Function.comp_apply, id]
  rw [mul_pow, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hc.ne'), one_mul]

/-- The total error rate (divided by `e^{2δa}`). -/
def errorRate {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) (C₀ Blam S : ℝ) (a : ℝ) : ℝ :=
  (∑ j, |h.mult j|) * (((2 * a * C₀ + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a))) *
      (2 * (1 + 1 / (2 * δ)) + (2 * a * C₀ + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a)))) +
    Blam * (4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) / 2 +
    3 / (2 * δ) * Real.exp (-(δ * a)) * (∑ j, |h.mult j|) *
      (2 + 4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) +
    (2 * h.lowWeight a * (2 + 4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) +
      (2 * a * (2 * C₀ * (δ + ∑ j, |t j|)) + 2 * (2 * C₀)) ^ 2 * S) *
      Real.exp (-(2 * δ * a))

theorem tendsto_lowWeight_mul_exp {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) :
    Tendsto (fun a => h.lowWeight a * Real.exp (-(2 * δ * a))) atTop (𝓝 0) := by
  have hfun : (fun a => h.lowWeight a * Real.exp (-(2 * δ * a))) = fun a =>
      ∑ q ∈ h.lowSet, 2 * (a ^ 1 * Real.exp (-((2 * (δ - |(xiSpectralPoint q).im|)) * a))) := by
    funext a
    unfold FiniteTopLayer.lowWeight
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [pow_one, mul_assoc, mul_assoc, ← Real.exp_add]
    ring_nf
  rw [hfun]
  rw [show (0 : ℝ) = ∑ q ∈ h.lowSet, 2 * 0 by simp]
  refine tendsto_finsetSum _ fun q hq => (tendsto_pow_mul_exp_neg_mul ?_ 1).const_mul 2
  have := h.abs_im_lt_of_mem_lowSet hq
  linarith

theorem tendsto_errorRate {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) (C₀ Blam S : ℝ) :
    Tendsto (errorRate h C₀ Blam S) atTop (𝓝 0) := by
  have hδ := h.pos
  have hδ2 : 0 < 2 * δ := by linarith
  set Mt := ∑ j, |h.mult j|
  set κ₁ := 1 + 1 / (2 * δ)
  set τ := δ + ∑ j, |t j|
  have tE : Tendsto (fun a : ℝ => Real.exp (-(δ * a))) atTop (𝓝 0) := by
    have := tendsto_pow_mul_exp_neg_mul hδ 0
    simpa using this
  have tA : Tendsto (fun a : ℝ => a * Real.exp (-(δ * a))) atTop (𝓝 0) := by
    have := tendsto_pow_mul_exp_neg_mul hδ 1
    simpa using this
  have tE2 : Tendsto (fun a : ℝ => Real.exp (-(2 * δ * a))) atTop (𝓝 0) := by
    have := tendsto_pow_mul_exp_neg_mul hδ2 0
    simpa using this
  have tA2 : Tendsto (fun a : ℝ => a * Real.exp (-(2 * δ * a))) atTop (𝓝 0) := by
    have := tendsto_pow_mul_exp_neg_mul hδ2 1
    simpa using this
  have tAA2 : Tendsto (fun a : ℝ => a ^ 2 * Real.exp (-(2 * δ * a))) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_mul hδ2 2
  -- `ε(a) → 0`
  have tε : Tendsto (fun a : ℝ => (2 * a * C₀ + κ₁) * Real.exp (-(δ * a))) atTop (𝓝 0) := by
    have := (tA.const_mul (2 * C₀)).add (tE.const_mul κ₁)
    rw [mul_zero, mul_zero, add_zero] at this
    refine this.congr fun a => ?_
    ring
  have t1 : Tendsto (fun a : ℝ => Mt * (((2 * a * C₀ + κ₁) * Real.exp (-(δ * a))) *
      (2 * κ₁ + (2 * a * C₀ + κ₁) * Real.exp (-(δ * a))))) atTop (𝓝 0) := by
    have := (tε.mul (tε.const_add (2 * κ₁))).const_mul Mt
    simpa using this
  have tη : Tendsto (fun a : ℝ => 4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) atTop (𝓝 0) := by
    have := tA2.const_mul (4 * C₀ ^ 2)
    rw [mul_zero] at this
    refine this.congr fun a => ?_
    ring
  have t2 : Tendsto (fun a : ℝ => Blam * (4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a))) / 2) atTop
      (𝓝 0) := by
    have := (tη.const_mul Blam).div_const 2
    simpa using this
  have t3 : Tendsto (fun a : ℝ => 3 / (2 * δ) * Real.exp (-(δ * a)) * Mt *
      (2 + 4 * a * C₀ ^ 2 * Real.exp (-(2 * δ * a)))) atTop (𝓝 0) := by
    have := ((tE.const_mul (3 / (2 * δ))).mul_const Mt).mul (tη.const_add 2)
    simpa using this
  have tL := tendsto_lowWeight_mul_exp h
  have t4 : Tendsto (fun a : ℝ => (2 * h.lowWeight a * (2 + 4 * a * C₀ ^ 2 *
      Real.exp (-(2 * δ * a))) + (2 * a * (2 * C₀ * τ) + 2 * (2 * C₀)) ^ 2 * S) *
        Real.exp (-(2 * δ * a))) atTop (𝓝 0) := by
    have hA := (tL.const_mul 2).mul (tη.const_add 2)
    have hB := ((tAA2.const_mul ((4 * C₀ * τ) ^ 2)).add
      ((tA2.const_mul (2 * (4 * C₀ * τ) * (4 * C₀))).add
        (tE2.const_mul ((4 * C₀) ^ 2)))).const_mul S
    have := hA.add hB
    simp only [mul_zero, zero_mul, add_zero] at this
    refine this.congr fun a => ?_
    ring
  have := ((t1.add t2).add t3).add t4
  simp only [add_zero] at this
  exact this

/-! ## The odd test lies below the even floor -/

/-- **The decisive inequality at one aperture.** -/
theorem oddTest_below_evenFloor {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (a : SuzukiPositiveAperture) {x : Fin m → ℂ} (hx : x ∈ unitLevel δ t)
    (hmax : quadForm δ t h.mult (aperturePhase t a.1) x =
      ccmLambdaMax δ t h.mult (aperturePhase t a.1))
    {C₀ Blam g : ℝ} (hC₀ : profileBound x ≤ C₀)
    (hBlam : max (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))) 0 ≤ Blam)
    (hgap : g / 2 ≤ ccmLambdaMax δ t h.mult (aperturePhase t a.1) -
      max (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))) 0)
    (hR : errorRate h C₀ Blam (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) a.1 < g / 2) :
    ∑ q ∈ h.offLine,
        (zeroSumTerm (fun y => ((truncModel (oddProfileModel δ t x a.1) a.1 y : ℝ) : ℂ))
          (xiSpectralPoint q)).re +
      (2 * a.1 * (2 * profileBound x * (δ + ∑ j, |t j|)) + 2 * (2 * profileBound x)) ^ 2 *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) <
      evenFloorConst h a.1 * ∫ y, truncModel (oddProfileModel δ t x a.1) a.1 y ^ 2 := by
  have hδ := h.pos
  have ha : 0 ≤ a.1 := a.2.le
  have hn : normForm δ t x = 1 := hx
  set θ := aperturePhase t a.1 with hθ
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  set N := ∫ y, truncModel (oddProfileModel δ t x a.1) a.1 y ^ 2 with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => sq_nonneg _
  set Mt := ∑ j, |h.mult j| with hMt
  have hMt0 : 0 ≤ Mt := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set κ₁ := 1 + 1 / (2 * δ) with hκ₁
  have hκ₁0 : 0 ≤ κ₁ := by positivity
  set τ := δ + ∑ j, |t j| with hτ
  have hτ0 : 0 ≤ τ := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => abs_nonneg (t j))
    linarith
  set Cx := profileBound x with hCx
  have hCx0 : 0 ≤ Cx := profileBound_nonneg x
  have hC₀0 : 0 ≤ C₀ := hCx0.trans hC₀
  set E := Real.exp (-(δ * a.1)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set E2 := Real.exp (-(2 * δ * a.1)) with hE2
  have hE20 : 0 ≤ E2 := (Real.exp_pos _).le
  set X := Real.exp (2 * δ * a.1) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hXE2 : X * E2 = 1 := by rw [hX, hE2, ← Real.exp_add]; simp
  set Lw := h.lowWeight a.1 with hLw
  have hLw0 : 0 ≤ Lw := h.lowWeight_nonneg ha
  set lam := ccmLambdaMax δ t h.mult θ with hlam
  set Λ' := max (ccmLambdaMax δ t h.mult (halfTurn θ)) 0 with hΛ'
  have hΛ'0 : 0 ≤ Λ' := le_max_right _ _
  -- the off-line part
  have hoff := offLine_truncModel_le h x ha
  have hform := halfLineForm_truncModel_ge hδ t h.mult θ x hn ha
  rw [hmax] at hform
  -- monotonicity in the coefficient bound
  have hεx : (2 * a.1 * Cx + κ₁) * E ≤ (2 * a.1 * C₀ + κ₁) * E := by gcongr
  have hεx0 : 0 ≤ (2 * a.1 * Cx + κ₁) * E := by positivity
  have herr : Mt * (((2 * a.1 * Cx + κ₁) * E) * (2 * κ₁ + (2 * a.1 * Cx + κ₁) * E)) ≤
      Mt * (((2 * a.1 * C₀ + κ₁) * E) * (2 * κ₁ + (2 * a.1 * C₀ + κ₁) * E)) := by
    gcongr
  set err := Mt * (((2 * a.1 * C₀ + κ₁) * E) * (2 * κ₁ + (2 * a.1 * C₀ + κ₁) * E)) with herr_def
  have hhalf : lam - err ≤ halfLineForm δ t h.mult θ
      (fun s => truncModel (oddProfileModel δ t x a.1) a.1 (a.1 - s)) := by linarith
  -- the mass
  have hmass := integral_truncModel_sq_le hδ t x hn ha
  set η := 4 * a.1 * C₀ ^ 2 * E2 with hη
  have hη0 : 0 ≤ η := by positivity
  have hNle : N ≤ 2 + η := by
    have : 4 * a.1 * Cx ^ 2 * E2 ≤ η := by
      rw [hη]; gcongr
    linarith
  -- the critical-line constant
  set K := 2 * a.1 * (2 * C₀ * τ) + 2 * (2 * C₀) with hK
  have hKx : (2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx)) ^ 2 ≤ K ^ 2 := by
    have h0 : 0 ≤ 2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx) := by positivity
    have h1 : 2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx) ≤ K := by rw [hK]; gcongr
    exact pow_le_pow_left₀ h0 h1 2
  -- the error rate
  set C₁ := 3 / (2 * δ) * E * Mt with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hRdef : errorRate h C₀ Blam S a.1 =
      err + Blam * η / 2 + C₁ * (2 + η) + (2 * Lw * (2 + η) + K ^ 2 * S) * E2 := by
    unfold errorRate
    simp only [hη, hC₁, herr_def, hK, hτ, hκ₁, hMt, hE, hE2, hLw]
  rw [hRdef] at hR
  have hBlam0 : 0 ≤ Blam := hΛ'0.trans hBlam
  -- assemble
  have hfloor : evenFloorConst h a.1 = -(X * (Λ' / 2 + C₁) + Lw) := by
    unfold evenFloorConst; rw [← hΛ']
  rw [hfloor]
  have hkey : X * (g / 2 - err - Blam * η / 2 - C₁ * (2 + η)) > 2 * Lw * (2 + η) + K ^ 2 * S := by
    have h1 : (2 * Lw * (2 + η) + K ^ 2 * S) * E2 < g / 2 - err - Blam * η / 2 - C₁ * (2 + η) := by
      linarith
    have h2 := mul_lt_mul_of_pos_left h1 hX0
    rw [← mul_assoc, mul_comm X, mul_assoc, hXE2, mul_one] at h2
    linarith
  have hΛη : Λ' * η ≤ Blam * η := mul_le_mul_of_nonneg_right hBlam hη0
  have hlow2 : N * Lw ≤ (2 + η) * Lw := mul_le_mul_of_nonneg_right hNle hLw0
  have hc0 : 0 ≤ X * (Λ' / 2 + C₁) + Lw := by positivity
  have hfloorN : (X * (Λ' / 2 + C₁) + Lw) * N ≤ (X * (Λ' / 2 + C₁) + Lw) * (2 + η) :=
    mul_le_mul_of_nonneg_left hNle hc0
  have hupper : X * (lam - err) ≤ X * halfLineForm δ t h.mult θ
      (fun s => truncModel (oddProfileModel δ t x a.1) a.1 (a.1 - s)) :=
    mul_le_mul_of_nonneg_left hhalf hX0.le
  have hKS : (2 * a.1 * (2 * Cx * τ) + 2 * (2 * Cx)) ^ 2 * S ≤ K ^ 2 * S :=
    mul_le_mul_of_nonneg_right hKx hS0
  have hinner : g / 2 - err - Blam * η / 2 - C₁ * (2 + η) ≤
      lam - err - Λ' - Λ' * η / 2 - C₁ * (2 + η) := by linarith
  have hmono := mul_le_mul_of_nonneg_left hinner hX0.le
  have e1 : (X * (Λ' / 2 + C₁) + Lw) * (2 + η) =
      X * (Λ' + Λ' * η / 2 + C₁ * (2 + η)) + Lw * (2 + η) := by ring
  have e2 : X * (lam - err - Λ' - Λ' * η / 2 - C₁ * (2 + η)) =
      X * (lam - err) - X * (Λ' + Λ' * η / 2 + C₁ * (2 + η)) := by ring
  have e3 : -(X * (Λ' / 2 + C₁) + Lw) * N = -((X * (Λ' / 2 + C₁) + Lw) * N) := by ring
  rw [e3]
  linarith [hoff, hkey, hfloorN, hupper, hKS, hlow2, hmono, e1, e2]

/-! ## The no-go theorem -/

/-- **Parity selection fails under a finite top layer.** If the leading-order parity balance is
positive at one aperture phase, then arbitrarily large apertures have only reflection-odd ground
states of the CCM restricted Weil form. -/
theorem exists_aperture_ground_odd {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (hpos : ∃ a₁ : ℝ, 0 < ccmParityBalance δ t h.mult (aperturePhase t a₁)) (A : ℝ) :
    ∃ a : SuzukiPositiveAperture, A < a.1 ∧
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
          ccmArchimedeanFormReflection a u = -u := by
  have hδ := h.pos
  have ht := h.injective
  have htpos := h.t_pos
  have hm := h.nonempty
  obtain ⟨g, hg0, hret⟩ := exists_balance_ge_frequently hδ ht htpos hm h.mult hpos
  obtain ⟨κ, hκ, hcoer⟩ := exists_normForm_coercive hδ ht htpos
  set C₀ : ℝ := 2 * m * max 1 (1 / κ) with hC₀
  set Blam : ℝ := (∑ j, |h.mult j|) * (1 / (2 * δ)) with hBlam
  set S : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hS
  have hev := (tendsto_errorRate h C₀ Blam S).eventually (gt_mem_nhds (show (0 : ℝ) < g / 2 by
    linarith))
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.mp hev
  obtain ⟨a₀, ha₀N, hga₀⟩ := hret (max (max A₀ (A + 1)) 1)
  have ha₀pos : 0 < a₀ := by
    have := le_max_right (max A₀ (A + 1)) 1
    linarith
  set a : SuzukiPositiveAperture := ⟨a₀, ha₀pos⟩ with ha_def
  have haA : A < a.1 := by
    have := le_max_right A₀ (A + 1)
    have := le_max_left (max A₀ (A + 1)) 1
    show A < a₀
    linarith
  refine ⟨a, haA, ?_⟩
  have hR : errorRate h C₀ Blam S a.1 < g / 2 := by
    apply hA₀
    have := le_max_left A₀ (A + 1)
    have := le_max_left (max A₀ (A + 1)) 1
    show A₀ ≤ a₀
    linarith
  -- the maximizer and the odd model
  obtain ⟨x, hx, hmax, -⟩ := exists_isMaxOn_quadForm hδ ht htpos hm h.mult (aperturePhase t a.1)
  have hCx : profileBound x ≤ C₀ := profileBound_le_of_coercive hκ hcoer hx
  have hBlamx : max (ccmLambdaMax δ t h.mult (halfTurn (aperturePhase t a.1))) 0 ≤ Blam := by
    refine max_le (lambdaMax_le hδ ht htpos hm h.mult _) ?_
    positivity
  have hgap := gap_ge_of_balance_ge hδ ht htpos hm h.mult (aperturePhase t a.1) hga₀ hg0
  have hlt := oddTest_below_evenFloor h a hx hmax hCx hBlamx hgap hR
  set W := oddProfileModel δ t x a.1 with hW
  have hWs := contDiff_oddProfileModel δ t x a.1
  have hD : ∀ y ∈ Icc (-a.1) a.1, |W y| ≤ 2 * profileBound x := fun y hy =>
    abs_oddProfileModel_le hδ.le t x hy
  have hD' : ∀ y ∈ Icc (-a.1) a.1, |deriv W y| ≤ 2 * profileBound x * (δ + ∑ j, |t j|) :=
    fun y hy => abs_deriv_oddProfileModel_le hδ.le t x hy
  obtain ⟨v, hv⟩ := exists_smooth_below_model h a W hWs hD hD' hlt
  -- the ground energy lies strictly below the even floor
  set ce := evenFloorConst h a.1 with hce
  have hμv := ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a v.toCCMFormVector
  intro u hu
  obtain ⟨heven, -⟩ := ccmRestrictedWeil_ground_evenOdd_components a u hu
  set e := ccmRestrictedWeilEvenPart a u with he
  have hRe : ccmArchimedeanFormReflection a e = e := ccmArchimedeanFormReflection_evenPart a u
  have hfloor := sourceQuadratic_ge_of_isEven h e hRe
  have hvpos : 0 < ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 := by
    by_contra hle
    push Not at hle
    have h0 : ‖ccmArchimedeanFormToAperture a v.toCCMFormVector‖ ^ 2 = 0 :=
      le_antisymm hle (by positivity)
    rw [h0] at hv hμv
    linarith
  have hμ : ccmRestrictedWeilGroundEnergy a < ce := by
    by_contra hge
    push Not at hge
    have := mul_le_mul_of_nonneg_right hge hvpos.le
    linarith
  have hJe : ‖ccmArchimedeanFormToAperture a e‖ ^ 2 = 0 := by
    have hfl : ce * ‖ccmArchimedeanFormToAperture a e‖ ^ 2 ≤
        ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := by
      rw [← heven]
      exact hfloor
    have hnn : 0 ≤ ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := by positivity
    obtain ⟨X, hXdef⟩ : ∃ X, X = ‖ccmArchimedeanFormToAperture a e‖ ^ 2 := ⟨_, rfl⟩
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = ccmRestrictedWeilGroundEnergy a := ⟨_, rfl⟩
    rw [← hXdef] at hfl hnn ⊢
    rw [← hμdef] at hfl hμ
    have hpos : 0 < ce - μ := sub_pos.mpr hμ
    have hprod : (ce - μ) * X ≤ 0 := by rw [sub_mul]; linarith
    by_contra hX
    have hXpos : 0 < X := lt_of_le_of_ne hnn (Ne.symm hX)
    have := mul_pos hpos hXpos
    linarith
  have he0 : e = 0 := by
    apply ccmArchimedeanFormToAperture_injective a
    rw [map_zero]
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hJe)
  have hsum : u + ccmArchimedeanFormReflection a u = 0 := by
    have h2 : (2 : ℂ)⁻¹ • (u + ccmArchimedeanFormReflection a u) = 0 := he0
    rwa [smul_eq_zero, or_iff_right (inv_ne_zero two_ne_zero)] at h2
  exact eq_neg_of_add_eq_zero_right hsum

/-- **Even relations suffice.** If every integer relation among the top ordinates has even
coefficient sum (for instance if the ordinates are `ℚ`-independent), then arbitrarily large apertures
have only reflection-odd ground states. -/
theorem exists_aperture_ground_odd_of_even_relations {δ : ℝ} {t : Fin m → ℝ}
    (h : FiniteTopLayer δ t)
    (heven : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → Even (∑ j, k j)) (A : ℝ) :
    ∃ a : SuzukiPositiveAperture, A < a.1 ∧
      ∀ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 →
          ccmArchimedeanFormReflection a u = -u := by
  refine exists_aperture_ground_odd h ?_ A
  obtain ⟨a₁, -, ha₁⟩ := ccm_exists_large_aperture_odd_wins_of_even_relations h.pos h.injective
    h.t_pos h.mult_pos h.nonempty heven 0
  exact ⟨a₁, ha₁⟩

/-- **Contrapositive.** If every sufficiently large aperture carries a ground state that is not
reflection-odd, then the Xi zeros off the critical line do not form a finite set whose top layer
has even relations. -/
theorem not_finiteTopLayer_of_eventually_ground_not_odd
    (hground : ∃ A : ℝ, ∀ a : SuzukiPositiveAperture, A < a.1 →
      ∃ u : CCMArchimedeanFormDomain a,
        ccmRestrictedWeilSourceQuadratic a u =
            ccmRestrictedWeilGroundEnergy a * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 ∧
          ccmArchimedeanFormReflection a u ≠ -u)
    {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t)
    (heven : ∀ k : Fin m → ℤ, ∑ j, (k j : ℝ) * t j = 0 → Even (∑ j, k j)) : False := by
  obtain ⟨A, hA⟩ := hground
  obtain ⟨a, ha, hodd⟩ := exists_aperture_ground_odd_of_even_relations h heven A
  obtain ⟨u, hu, hne⟩ := hA a ha
  exact hne (hodd u hu)

end

end RHTower.CCMParityTopLayer
