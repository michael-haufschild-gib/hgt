import GaloisForLFunctions.RHTower.CCM.CCMEvenFullGroundZeroSumRH
import GaloisForLFunctions.RHTower.CanonicalProductE1SecondDerivative
import GaloisForLFunctions.RHTower.CompletionLogDerivZeroPairs

/-!
# Even real-rooted ground states with bounded second moment force RH

Let `u_j` be ground states of the unconstrained restricted Weil forms at apertures `a_j → ∞`. Assume
their physical functions `f_j` are even, with nonzero mass `∫ f_j` and real-rooted Fourier–Laplace
transforms. Suppose that

* `∫ |f_j| ≤ M e^{a_j} |∫ f_j|`, and
* `|∫ t² f_j(t) dt| ≤ S |∫ f_j|`.

Then the Riemann hypothesis holds.

**Proof.** Let `F(z) = ∫ conj(f(t)) e^{izt} dt`. Differentiating twice under the integral gives
`F''(0) = -∫ t² conj(f(t)) dt`. Since `F` is even, `F = F(0) P` with `P` its genus-one canonical
product, and `P''(0) = -∑_ρ 1/ρ²`. Hence `∑_ρ 1/ρ² = ∫ t² conj f / ∫ conj f`. The zeros are real,
so `∑_ρ 1/|ρ|² = |∫ t² f| / |∫ f| ≤ S`, and the zero-sum capstone applies.
-/

open Complex MeasureTheory Set Filter Topology Metric
open GaloisForLFunctions.EntireZeroDivisor RHTower.OrderOneHadamard

namespace RHTower.CCMFullGroundEigen

open GaloisForLFunctions.HTGeometry
open RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

noncomputable section

/-- Differentiation under the integral for a compactly supported transform. -/
theorem hasDerivAt_integral_mul_cexp {a : ℝ} (ha : 0 ≤ a) {g : ℝ → ℂ} (hg : Integrable g)
    (hs : ∀ t, g t ≠ 0 → |t| ≤ a) (z₀ : ℂ) :
    HasDerivAt (fun z : ℂ => ∫ t : ℝ, g t * cexp (I * z * t))
      (∫ t : ℝ, g t * (I * t) * cexp (I * z₀ * t)) z₀ := by
  set B : ℝ := a * Real.exp ((‖z₀‖ + 1) * a) with hB
  have hexp : ∀ z : ℂ, ∀ t : ℝ, g t ≠ 0 → ‖z‖ ≤ ‖z₀‖ + 1 →
      ‖cexp (I * z * t)‖ ≤ Real.exp ((‖z₀‖ + 1) * a) := by
    intro z t ht hz
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hre : (I * z * (t : ℂ)).re = -(z.im * t) := by simp [mul_re, mul_im]
    rw [hre]
    have hta := hs t ht
    calc -(z.im * t) ≤ |z.im * t| := neg_le_abs _
      _ = |z.im| * |t| := abs_mul _ _
      _ ≤ ‖z‖ * a := mul_le_mul (Complex.abs_im_le_norm z) hta (abs_nonneg t) (norm_nonneg z)
      _ ≤ (‖z₀‖ + 1) * a := by gcongr
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => g t * cexp (I * z * t)) :=
    fun z => hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ =>
      cexp (I * z * t)).aestronglyMeasurable
  have hint0 : Integrable fun t : ℝ => g t * cexp (I * z₀ * t) := by
    refine (hg.norm.mul_const (Real.exp ((‖z₀‖ + 1) * a))).mono' (hmeas z₀)
      (ae_of_all _ fun t => ?_)
    rw [norm_mul]
    by_cases ht : g t = 0
    · rw [ht, norm_zero, zero_mul, zero_mul]
    · gcongr
      exact hexp z₀ t ht (by linarith)
  have hF'meas : AEStronglyMeasurable (fun t : ℝ => g t * (I * t) * cexp (I * z₀ * t)) :=
    (hg.aestronglyMeasurable.mul (by fun_prop : Continuous fun t : ℝ =>
      I * (t : ℂ)).aestronglyMeasurable).mul (by fun_prop : Continuous fun t : ℝ =>
        cexp (I * z₀ * t)).aestronglyMeasurable
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun t => ‖g t‖ * B)
    (F' := fun z t => g t * (I * t) * cexp (I * z * t)) (ball_mem_nhds z₀ one_pos)
    (Eventually.of_forall fun z => hmeas z) hint0 hF'meas
    (ae_of_all _ fun t z hz => ?_) (hg.norm.mul_const B) (ae_of_all _ fun t z _ => ?_)).2
  · rw [mem_ball] at hz
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [← dist_eq_norm] at this
      linarith
    rw [norm_mul, norm_mul]
    by_cases ht : g t = 0
    · rw [ht, norm_zero, zero_mul, zero_mul, zero_mul]
    · have hta := hs t ht
      have hIt : ‖I * (t : ℂ)‖ ≤ a := by
        rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hta
      rw [hB, mul_assoc]
      gcongr
      exact hexp z t ht hzn
  · have h1 : HasDerivAt (fun w : ℂ => I * w * (t : ℂ)) (I * (t : ℂ)) z := by
      simpa using ((hasDerivAt_id z).const_mul I).mul_const (t : ℂ)
    have h2 := h1.cexp.const_mul (g t)
    exact h2.congr_deriv (by ring)

/-- The second derivative at the origin of a compactly supported transform:
`F''(0) = -∫ t² conj(f(t)) dt`. -/
theorem hasDerivAt_deriv_conjTransform_zero {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ} (hf : Integrable f)
    (hs : ∀ t, f t ≠ 0 → |t| ≤ a) :
    HasDerivAt (deriv (conjTransform f))
      (-∫ t : ℝ, ((t : ℂ) ^ 2) * (starRingEnd ℂ) (f t)) 0 := by
  set g : ℝ → ℂ := fun t => (starRingEnd ℂ) (f t) with hgdef
  have hg : Integrable g :=
    hf.norm.mono' (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable)
      (ae_of_all _ fun t => by simp [hgdef])
  have hgs : ∀ t, g t ≠ 0 → |t| ≤ a := fun t ht => hs t (by
    intro h; apply ht; simp [hgdef, h])
  set g₁ : ℝ → ℂ := fun t => g t * (I * t) with hg₁def
  have hg₁ : Integrable g₁ := by
    refine (hg.norm.mul_const a).mono' (hg.aestronglyMeasurable.mul
      (by fun_prop : Continuous fun t : ℝ => I * (t : ℂ)).aestronglyMeasurable)
      (ae_of_all _ fun t => ?_)
    rw [hg₁def, norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases ht : g t = 0
    · rw [ht, norm_zero, zero_mul, zero_mul]
    · gcongr
      exact hgs t ht
  have hg₁s : ∀ t, g₁ t ≠ 0 → |t| ≤ a := fun t ht => hgs t (by
    intro h; apply ht; simp [hg₁def, h])
  have hderiv : deriv (conjTransform f) = fun z => ∫ t : ℝ, g₁ t * cexp (I * z * t) := by
    funext z
    exact (hasDerivAt_integral_mul_cexp ha hg hgs z).deriv
  rw [hderiv]
  have h2 := hasDerivAt_integral_mul_cexp ha hg₁ hg₁s 0
  convert h2 using 1
  rw [← integral_neg]
  congr 1
  funext t
  simp only [hg₁def, hgdef, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  ring_nf
  rw [I_sq]
  ring

/-- **The inverse-square zero sum is the normalized second moment.** For an even
compactly supported `f` with nonzero mass, `∑_ρ 1/ρ² = ∫ t² conj f / ∫ conj f` over the zeros of
`F(z) = ∫ conj(f(t)) e^{izt} dt`. -/
theorem tsum_inv_sq_zeroCopyPoint_conjTransform {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : Integrable f) (hs : ∀ t, f t ≠ 0 → |t| ≤ a)
    (hsupp : FourierZeroFlip.SupportedIn a f) (heven : ∀ t, f (-t) = f t)
    (h0 : conjTransform f 0 ≠ 0) :
    conjTransform f 0 * ∑' q : ZeroCopy (conjTransform f),
        1 / (zeroCopyPoint (conjTransform f) q) ^ 2 =
      ∫ t : ℝ, ((t : ℂ) ^ 2) * (starRingEnd ℂ) (f t) := by
  set F : ℂ → ℂ := conjTransform f with hFdef
  obtain ⟨C, hC, hbound⟩ := exists_orderOne_bound_conjTransform ha hf hs h0
  have hdiff : Differentiable ℂ F := differentiable_conjTransform ha hf hsupp
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun w _ => hdiff.analyticAt w
  have hord : ∀ w, analyticOrderAt F w ≠ ⊤ :=
    GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hdiff h0
  have hFeven : ∀ w, F (-w) = F w := conjTransform_neg_of_even heven
  have hfac := eq_const_mul_hadamardProduct_of_even hC hAn h0 hord hFeven hbound
  have hsum := summable_inv_sq_zeroCopyPoint hC hAn h0 hbound
  have hne := zeroCopyPoint_ne_zero hAn h0
  have hPan := hadamardProduct_analytic hAn h0 hsum
  have hFeq : F = fun z => F 0 * hadamardProduct F z := funext hfac
  have hderivF : deriv F = fun z => F 0 * deriv (hadamardProduct F) z := by
    funext z
    have h1 : deriv F z = deriv (fun w => F 0 * hadamardProduct F w) z :=
      congrArg (fun G => deriv G z) hFeq
    rw [h1]
    exact deriv_const_mul _ (hPan z (mem_univ z)).differentiableAt
  have hP2 := (hasDerivAt_deriv_canonicalProductE1Indexed_zero hne hsum).const_mul (F 0)
  have hF2 : HasDerivAt (deriv F) (F 0 * -∑' q, 1 / (zeroCopyPoint F q) ^ 2) 0 := by
    rw [hderivF]
    exact hP2
  have hF2' := hasDerivAt_deriv_conjTransform_zero ha hf hs
  have huniq := hF2.unique hF2'
  rw [mul_neg] at huniq
  exact neg_injective huniq

/-- **The second moment of a real-rooted even transform.** For an even compactly supported `f`
with nonzero mass whose transform has only real zeros,
`∫ t² conj f = conj(∫ f) · ∑_ρ 1/|ρ|²`. In particular `∫ t² f / ∫ f` is a nonnegative real. -/
theorem integral_sq_mul_conj_eq_of_realZeros {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : Integrable f) (hs : ∀ t, f t ≠ 0 → |t| ≤ a)
    (hsupp : FourierZeroFlip.SupportedIn a f) (heven : ∀ t, f (-t) = f t)
    (hreal : ∀ w : ℂ, FourierLaplaceDivision.unitaryLaplace f w = 0 → w.im = 0)
    (hmass : ∫ t : ℝ, f t ≠ 0) :
    ∫ t : ℝ, ((t : ℂ) ^ 2) * (starRingEnd ℂ) (f t) =
      (starRingEnd ℂ) (∫ t : ℝ, f t) * ((∑' q : ZeroCopy (conjTransform f),
        1 / ‖zeroCopyPoint (conjTransform f) q‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  set F : ℂ → ℂ := conjTransform f with hFdef
  have hF0eq : F 0 = (starRingEnd ℂ) (∫ t : ℝ, f t) := by
    simp only [hFdef, conjTransform, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact integral_conj
  have hF0 : F 0 ≠ 0 := by rw [hF0eq, map_ne_zero]; exact hmass
  have hid : F 0 * ∑' q : ZeroCopy F, 1 / (zeroCopyPoint F q) ^ 2 =
      ∫ t : ℝ, ((t : ℂ) ^ 2) * (starRingEnd ℂ) (f t) :=
    tsum_inv_sq_zeroCopyPoint_conjTransform ha hf hs hsupp heven hF0
  have hdiff : Differentiable ℂ F := differentiable_conjTransform ha hf hsupp
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun w _ => hdiff.analyticAt w
  have hrealF : ∀ q : ZeroCopy F, (zeroCopyPoint F q).im = 0 := by
    intro q
    have hz := RHTower.CompletionZeroPairs.apply_zeroCopyPoint hAn q
    set z := zeroCopyPoint F q
    rw [hFdef, conjTransform_eq_conj_unitaryLaplace, map_eq_zero] at hz
    have him := hreal _ hz
    have : ((starRingEnd ℂ) z / (2 * Real.pi : ℂ)).im = -z.im / (2 * Real.pi) := by
      rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
        Complex.div_ofReal_im, Complex.conj_im]
    rw [this] at him
    rcases div_eq_zero_iff.mp him with h | h
    · linarith
    · have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
      linarith
  have hterm : ∀ q : ZeroCopy F, 1 / (zeroCopyPoint F q) ^ 2 =
      ((1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro q
    obtain ⟨r, hre⟩ : ∃ r : ℝ, zeroCopyPoint F q = (r : ℂ) :=
      ⟨(zeroCopyPoint F q).re, by apply Complex.ext <;> simp [hrealF q]⟩
    rw [hre, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    push_cast
    ring
  simp_rw [hterm] at hid
  rw [← Complex.ofReal_tsum, hF0eq] at hid
  exact hid.symm

/-- **Even real-rooted eigenvectors with bounded second moment force RH.** -/
theorem riemannHypothesis_of_evenEigenvectors_secondMoment {η M S : ℝ} (hη : 0 < η)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (μ : ℕ → ℝ)
    (heig : ∀ j (s : CCMComplexSmoothInteriorSource (a j)),
      ccmRestrictedWeilForm (a j) (u j) s.toCCMFormVector =
        (μ j : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep (a j) (u j) t) * s t)
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hmom : ∀ j, ‖∫ t : ℝ, ((t : ℂ) ^ 2) * timeRep (a j) (u j) t‖ ≤
      S * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_evenEigenvectors_zeroSum (S := S) hη a ha u μ heig hreal hmass
    heven hl1 fun j => ?_
  set f : ℝ → ℂ := timeRep (a j) (u j) with hf
  set F : ℂ → ℂ := conjTransform f with hFdef
  have hfi := integrable_timeRep (a j) (u j)
  have hsupp := supportedIn_timeRep (a j) (u j)
  have hs := bound_support_of_supportedIn hsupp
  have hid : ∫ t : ℝ, ((t : ℂ) ^ 2) * (starRingEnd ℂ) (f t) =
      (starRingEnd ℂ) (∫ t : ℝ, f t) * ((∑' q : ZeroCopy F,
        1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) : ℝ) : ℂ) :=
    integral_sq_mul_conj_eq_of_realZeros (a j).2.le hfi hs hsupp (heven j) (hreal j) (hmass j)
  have hnorm := congrArg norm hid
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj,
    abs_of_nonneg (tsum_nonneg fun q => by positivity)] at hnorm
  have hmomconj : ‖∫ t : ℝ, ((t : ℂ) ^ 2) * (starRingEnd ℂ) (f t)‖ =
      ‖∫ t : ℝ, ((t : ℂ) ^ 2) * f t‖ := by
    rw [← Complex.norm_conj (∫ t : ℝ, ((t : ℂ) ^ 2) * f t), ← integral_conj]
    congr 2
    funext t
    simp
  rw [hmomconj] at hnorm
  have hpos : 0 < ‖∫ t : ℝ, f t‖ := norm_pos_iff.mpr (hmass j)
  have h := (hmom j)
  rw [hnorm] at h
  exact le_of_mul_le_mul_left (by linarith) hpos

/-- **Even real-rooted full ground states with bounded second moment force RH.** -/
theorem riemannHypothesis_of_evenFullGrounds_secondMoment {η M S : ℝ} (hη : 0 < η)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (a j).1 * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hmom : ∀ j, ‖∫ t : ℝ, ((t : ℂ) ^ 2) * timeRep (a j) (u j) t‖ ≤
      S * ‖∫ t : ℝ, timeRep (a j) (u j) t‖) :
    RiemannHypothesis :=
  riemannHypothesis_of_evenEigenvectors_secondMoment hη a ha u
    (fun j => ccmRestrictedWeilGroundEnergy (a j))
    (fun j => formEigen_of_isFullGround (a j) (hground j)) hreal hmass heven hl1 hmom

/-- **The card's theorem in its literal form.** Even eigenvectors `f_j` of the unconstrained
restricted Weil forms at apertures `a_j → ∞`, with real-rooted transforms, `∫ f_j = 1`,
`‖f_j‖₁ ≤ C` and `Re ∫ t² f_j ≤ C`, force RH. Under these hypotheses `∫ t² f_j` is real and
nonnegative (`integral_sq_mul_conj_eq_of_realZeros`), so the one-sided moment bound controls its
modulus. -/
theorem riemannHypothesis_of_card_hypotheses {C : ℝ}
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (μ : ℕ → ℝ)
    (heig : ∀ j (s : CCMComplexSmoothInteriorSource (a j)),
      ccmRestrictedWeilForm (a j) (u j) s.toCCMFormVector =
        (μ j : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep (a j) (u j) t) * s t)
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t = 1)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤ C)
    (hmom : ∀ j, (∫ t : ℝ, ((t : ℂ) ^ 2) * timeRep (a j) (u j) t).re ≤ C) :
    RiemannHypothesis := by
  have hC : 0 ≤ C := le_trans (integral_nonneg fun t => norm_nonneg _) (hl1 0)
  have hmass' : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0 := fun j => by
    rw [hmass j]; exact one_ne_zero
  refine riemannHypothesis_of_evenEigenvectors_secondMoment (η := 1) (M := C) (S := C) one_pos
    a ha u μ heig hreal hmass' heven (fun j => ?_) (fun j => ?_)
  · rw [hmass j, norm_one, mul_one]
    exact (hl1 j).trans (le_mul_of_one_le_right hC (Real.one_le_exp (a j).2.le))
  · rw [hmass j, norm_one, mul_one]
    set f : ℝ → ℂ := timeRep (a j) (u j) with hf
    have hid := integral_sq_mul_conj_eq_of_realZeros (a j).2.le (integrable_timeRep (a j) (u j))
      (bound_support_of_supportedIn (supportedIn_timeRep (a j) (u j)))
      (supportedIn_timeRep (a j) (u j)) (heven j) (hreal j) (hmass' j)
    rw [hmass j, map_one, one_mul] at hid
    set σ : ℝ := ∑' q : ZeroCopy (conjTransform f),
      1 / ‖zeroCopyPoint (conjTransform f) q‖ ^ (2 : ℕ) with hσ
    have hσ0 : 0 ≤ σ := tsum_nonneg fun q => by positivity
    have hreal' : ∫ t : ℝ, ((t : ℂ) ^ 2) * f t = (σ : ℂ) := by
      have h := congrArg (starRingEnd ℂ) hid
      rw [← integral_conj, Complex.conj_ofReal] at h
      rw [← h]
      congr 1
      funext t
      simp [hf]
    rw [hreal', Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hσ0]
    have h := hmom j
    rw [hreal', Complex.ofReal_re] at h
    exact h

end

end RHTower.CCMFullGroundEigen
