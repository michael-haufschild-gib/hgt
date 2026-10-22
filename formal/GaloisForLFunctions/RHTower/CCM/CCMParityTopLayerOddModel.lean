import GaloisForLFunctions.RHTower.CCM.CCMParityTopLayerOddTest

/-!
# The odd model of a Cauchy-model profile

For coefficients `x` let `P(s) = 2 Re Σ_j x_j e^{−(δ − it_j)s}` (`realProfile`) and
`W(y) = P(a − y) − P(a + y)` (`oddProfileModel`). `W` is smooth and odd, and with
`C = 2 Σ_j |x_j|` it satisfies `|W| ≤ 2C`, `|W'| ≤ 2C(δ + Σ_j |t_j|)` on `[−a, a]`.

For the truncation `W_a = W · 1_{(−a,a)}` the reflected function is
`W_a(a − s) = 1_{(0,2a)}(s) (P(s) − P(2a − s))`, so on `(0, ∞)` it equals `P + w₁ + w₂` with
`w₁ = −1_{(0,2a)} P(2a − ·)` (pointwise `O(e^{−2δa})` against `ψ_j`) and `w₂ = −1_{[2a,∞)} P`
(vanishing on `(0, a]`). Hence, when `∫_0^∞ P² = 1`:

* `T(θ)[W_a(a − ·)] ≥ T(θ)[P] − (Σ_j |M_j|) ε (2κ + ε)`, `ε = (2aC + κ) e^{−δa}`,
  `κ = 1 + 1/(2δ)` (`halfLineForm_truncModel_ge`);
* `∫ W_a² ≤ 2 + 4aC² e^{−2δa}` (`integral_truncModel_sq_le`);
* every top quartet contributes `−M_j Re Ŵ_a(−σ_j)²`, so the top layer contributes
  `−e^{2δa} T(θ(a))[W_a(a − ·)]` (`sum_top_truncModel_eq`).
-/

open Matrix Complex Filter Topology MeasureTheory Set
open RHTower.CCMParityQuartet RHTower.CCMParityCauchy GaloisForLFunctions.HTGeometry

namespace RHTower.CCMParityTopLayer

noncomputable section

variable {m : ℕ}

/-! ## The profile, its derivative and their sizes -/

theorem contDiff_realProfile (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (realProfile δ t x) := by
  have hof : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => (s : ℂ)) := Complex.ofRealCLM.contDiff
  have hF : ContDiff ℝ (⊤ : ℕ∞)
      (fun s : ℝ => ∑ j, x j * Complex.exp (-((δ : ℂ) - I * t j) * s)) := by fun_prop
  exact contDiff_const.mul (Complex.reCLM.contDiff.comp hF)

/-- `P'(s) = 2 Re Σ_j x_j (−(δ − it_j)) e^{−(δ − it_j)s}`. -/
def realProfileDeriv (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (s : ℝ) : ℝ :=
  2 * (∑ j, x j * (-((δ : ℂ) - I * t j) * Complex.exp (-((δ : ℂ) - I * t j) * s))).re

theorem hasDerivAt_realProfile (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (s : ℝ) :
    HasDerivAt (realProfile δ t x) (realProfileDeriv δ t x s) s := by
  have hF : HasDerivAt (fun s : ℝ => ∑ j, x j * Complex.exp (-((δ : ℂ) - I * t j) * s))
      (∑ j, x j * (-((δ : ℂ) - I * t j) * Complex.exp (-((δ : ℂ) - I * t j) * s))) s := by
    apply HasDerivAt.fun_sum
    intro j _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := (hasDerivAt_id s).ofReal_comp
    have h2 := ((h1.const_mul (-((δ : ℂ) - I * t j))).cexp).const_mul (x j)
    exact h2.congr_deriv (by ring)
  have hre : HasDerivAt (fun s : ℝ => (∑ j, x j * Complex.exp (-((δ : ℂ) - I * t j) * s)).re)
      (∑ j, x j * (-((δ : ℂ) - I * t j) * Complex.exp (-((δ : ℂ) - I * t j) * s))).re s :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt s hF
  exact hre.const_mul 2

/-- `C(x) = 2 Σ_j ‖x_j‖`. -/
def profileBound (x : Fin m → ℂ) : ℝ := 2 * ∑ j, ‖x j‖

theorem profileBound_nonneg (x : Fin m → ℂ) : 0 ≤ profileBound x := by
  unfold profileBound; positivity

theorem norm_exp_profile (δ tj s : ℝ) :
    ‖Complex.exp (-((δ : ℂ) - I * tj) * s)‖ = Real.exp (-(δ * s)) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

theorem abs_realProfile_le (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (s : ℝ) :
    |realProfile δ t x s| ≤ profileBound x * Real.exp (-(δ * s)) := by
  unfold realProfile profileBound
  rw [abs_mul, abs_two, mul_assoc]
  gcongr
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [norm_mul, norm_exp_profile]

theorem abs_realProfileDeriv_le (δ : ℝ) (hδ : 0 ≤ δ) (t : Fin m → ℝ) (x : Fin m → ℂ) (s : ℝ) :
    |realProfileDeriv δ t x s| ≤
      profileBound x * (δ + ∑ j, |t j|) * Real.exp (-(δ * s)) := by
  unfold realProfileDeriv profileBound
  rw [abs_mul, abs_two]
  have hτ : ∀ j, ‖-((δ : ℂ) - I * t j)‖ ≤ δ + ∑ k, |t k| := by
    intro j
    rw [norm_neg]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hδ, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have := Finset.single_le_sum (f := fun k => |t k|) (fun k _ => abs_nonneg _)
      (Finset.mem_univ j)
    linarith
  have hsum : ‖∑ j, x j * (-((δ : ℂ) - I * t j) * Complex.exp (-((δ : ℂ) - I * t j) * s))‖ ≤
      (∑ j, ‖x j‖) * (δ + ∑ k, |t k|) * Real.exp (-(δ * s)) := by
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul, norm_mul, norm_exp_profile, ← mul_assoc]
    gcongr
    exact hτ j
  calc 2 * |(∑ j, x j * (-((δ : ℂ) - I * t j) *
        Complex.exp (-((δ : ℂ) - I * t j) * s))).re|
      ≤ 2 * ((∑ j, ‖x j‖) * (δ + ∑ k, |t k|) * Real.exp (-(δ * s))) := by
        gcongr
        exact (Complex.abs_re_le_norm _).trans hsum
    _ = (2 * ∑ j, ‖x j‖) * (δ + ∑ j, |t j|) * Real.exp (-(δ * s)) := by ring

/-! ## The odd model -/

/-- The odd model `W(y) = P(a − y) − P(a + y)`. -/
def oddProfileModel (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (a y : ℝ) : ℝ :=
  realProfile δ t x (a - y) - realProfile δ t x (a + y)

theorem contDiff_oddProfileModel (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (oddProfileModel δ t x a) :=
  ((contDiff_realProfile δ t x).comp (contDiff_const.sub contDiff_id)).sub
    ((contDiff_realProfile δ t x).comp (contDiff_const.add contDiff_id))

theorem oddProfileModel_neg (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (a y : ℝ) :
    oddProfileModel δ t x a (-y) = -oddProfileModel δ t x a y := by
  unfold oddProfileModel
  rw [sub_neg_eq_add, ← sub_eq_add_neg]
  ring

theorem exp_neg_le_one {δ s : ℝ} (hδ : 0 ≤ δ) (hs : 0 ≤ s) : Real.exp (-(δ * s)) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by nlinarith)

theorem abs_oddProfileModel_le {δ : ℝ} (hδ : 0 ≤ δ) (t : Fin m → ℝ) (x : Fin m → ℂ) {a y : ℝ}
    (hy : y ∈ Icc (-a) a) : |oddProfileModel δ t x a y| ≤ 2 * profileBound x := by
  unfold oddProfileModel
  have hC := profileBound_nonneg x
  have h1 := abs_realProfile_le δ t x (a - y)
  have h2 := abs_realProfile_le δ t x (a + y)
  have e1 := exp_neg_le_one hδ (show 0 ≤ a - y by linarith [hy.2])
  have e2 := exp_neg_le_one hδ (show 0 ≤ a + y by linarith [hy.1])
  calc |realProfile δ t x (a - y) - realProfile δ t x (a + y)|
      ≤ |realProfile δ t x (a - y)| + |realProfile δ t x (a + y)| := abs_sub _ _
    _ ≤ profileBound x * 1 + profileBound x * 1 := by gcongr <;> nlinarith
    _ = 2 * profileBound x := by ring

theorem hasDerivAt_oddProfileModel (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (a y : ℝ) :
    HasDerivAt (oddProfileModel δ t x a)
      (-realProfileDeriv δ t x (a - y) - realProfileDeriv δ t x (a + y)) y := by
  have h1 := (hasDerivAt_realProfile δ t x (a - y)).comp y ((hasDerivAt_id y).const_sub a)
  have h2 := (hasDerivAt_realProfile δ t x (a + y)).comp y ((hasDerivAt_id y).const_add a)
  have h := h1.sub h2
  unfold oddProfileModel
  exact h.congr_deriv (by ring)

theorem abs_deriv_oddProfileModel_le {δ : ℝ} (hδ : 0 ≤ δ) (t : Fin m → ℝ) (x : Fin m → ℂ)
    {a y : ℝ} (hy : y ∈ Icc (-a) a) :
    |deriv (oddProfileModel δ t x a) y| ≤ 2 * profileBound x * (δ + ∑ j, |t j|) := by
  rw [(hasDerivAt_oddProfileModel δ t x a y).deriv]
  have hC := profileBound_nonneg x
  have hτ : 0 ≤ δ + ∑ j, |t j| := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) => abs_nonneg (t j))
    linarith
  have h1 := abs_realProfileDeriv_le δ hδ t x (a - y)
  have h2 := abs_realProfileDeriv_le δ hδ t x (a + y)
  have e1 := exp_neg_le_one hδ (show 0 ≤ a - y by linarith [hy.2])
  have e2 := exp_neg_le_one hδ (show 0 ≤ a + y by linarith [hy.1])
  have hCτ : 0 ≤ profileBound x * (δ + ∑ j, |t j|) := mul_nonneg hC hτ
  calc |-realProfileDeriv δ t x (a - y) - realProfileDeriv δ t x (a + y)|
      ≤ |realProfileDeriv δ t x (a - y)| + |realProfileDeriv δ t x (a + y)| := by
        rw [show -realProfileDeriv δ t x (a - y) - realProfileDeriv δ t x (a + y) =
          -(realProfileDeriv δ t x (a - y) + realProfileDeriv δ t x (a + y)) by ring, abs_neg]
        exact abs_add_le _ _
    _ ≤ profileBound x * (δ + ∑ j, |t j|) * 1 + profileBound x * (δ + ∑ j, |t j|) * 1 := by
        gcongr <;> nlinarith
    _ = 2 * profileBound x * (δ + ∑ j, |t j|) := by ring

/-! ## The truncated model as an interval source -/

theorem truncModel_neg (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (a y : ℝ) :
    truncModel (oddProfileModel δ t x a) a (-y) = -truncModel (oddProfileModel δ t x a) a y := by
  unfold truncModel
  by_cases hy : y ∈ Ioo (-a) a
  · have hy' : -y ∈ Ioo (-a) a := ⟨by linarith [hy.2], by linarith [hy.1]⟩
    rw [indicator_of_mem hy, indicator_of_mem hy', oddProfileModel_neg]
  · have hy' : -y ∉ Ioo (-a) a := fun h => hy ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [indicator_of_notMem hy, indicator_of_notMem hy', neg_zero]

theorem realIntervalSource_truncModel {δ : ℝ} (t : Fin m → ℝ) (x : Fin m → ℂ) (a : ℝ) :
    RealIntervalSource a (truncModel (oddProfileModel δ t x a) a) where
  memLp := by
    unfold truncModel
    rw [memLp_indicator_iff_restrict measurableSet_Ioo]
    obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (-a) a)
      (contDiff_oddProfileModel δ t x a).continuous.continuousOn
    haveI : IsFiniteMeasure (volume.restrict (Ioo (-a) a)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
    exact MemLp.of_bound (contDiff_oddProfileModel δ t x a).continuous.aestronglyMeasurable B
      ((ae_restrict_iff' measurableSet_Ioo).mpr
        (Filter.Eventually.of_forall fun y hy => hB y (Ioo_subset_Icc_self hy)))
  vanish := fun y hy => by
    unfold truncModel
    rw [indicator_of_notMem]
    intro h
    have := abs_lt.mpr ⟨h.1, h.2⟩
    linarith

theorem realIntervalSource_zero (a : ℝ) : RealIntervalSource a fun _ => 0 where
  memLp := MemLp.zero
  vanish := fun _ _ => rfl

/-! ## The top layer of the truncated model -/

theorem re_zeroSumTerm_truncModel {δ : ℝ} (t : Fin m → ℝ) (x : Fin m → ℂ) (a : ℝ) (σ : ℂ) :
    (zeroSumTerm (fun y => ((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ)) σ).re =
      -((testTransform (fun y => ((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ))
        (-σ)) ^ 2).re := by
  have hpar : ∀ y, ((truncModel (oddProfileModel δ t x a) a (-y) : ℝ) : ℂ) =
      ((-1 : ℝ) : ℂ) * ((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ) := by
    intro y; rw [truncModel_neg]; push_cast; ring
  have h1 : RealIntervalSource a fun y =>
      (((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ)).re := by
    simpa using realIntervalSource_truncModel (δ := δ) t x a
  have h2 : RealIntervalSource a fun y =>
      (((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ)).im := by
    simpa using realIntervalSource_zero a
  rw [re_zeroSumTerm_parity (Or.inr rfl) hpar h1 h2]
  simp only [Complex.ofReal_re, Complex.ofReal_im]
  have hz : testTransform (fun _ : ℝ => (((0 : ℝ) : ℝ) : ℂ)) (-σ) = 0 := by
    unfold testTransform; simp
  rw [hz]
  simp

/-- **The top layer of the truncated model.** -/
theorem sum_top_truncModel_eq {δ : ℝ} {t : Fin m → ℝ} (h : FiniteTopLayer δ t) (x : Fin m → ℂ)
    (a : ℝ) :
    ∑ j, ∑ q ∈ h.topSet j,
        (zeroSumTerm (fun y => ((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ))
          (xiSpectralPoint q)).re =
      -(Real.exp (2 * δ * a) * halfLineForm δ t h.mult (aperturePhase t a)
        (fun s => truncModel (oddProfileModel δ t x a) a (a - s))) := by
  set f : ℝ → ℂ := fun y => ((truncModel (oddProfileModel δ t x a) a y : ℝ) : ℂ) with hf
  have hpar : ∀ y, f (-y) = -1 * f y := by
    intro y; simp only [hf]; rw [truncModel_neg]; push_cast; ring
  have hq : ∀ j, ∀ q ∈ h.topSet j, (zeroSumTerm f (xiSpectralPoint q)).re =
      (zeroSumTerm f (topPoint δ t j)).re := by
    intro j q hq
    simp only [FiniteTopLayer.topSet, Finset.mem_filter] at hq
    have hs1 : (-1 : ℂ) * (starRingEnd ℂ) (-1) = 1 := by simp
    rw [re_zeroSumTerm_quartet hpar hs1 _ hq.2, re_zeroSumTerm_quartet hpar hs1 _ (Or.inl rfl)]
  have hj : ∀ j, ∑ q ∈ h.topSet j, (zeroSumTerm f (xiSpectralPoint q)).re =
      -(h.mult j * ((testTransform f (-topPoint δ t j)) ^ 2).re) := by
    intro j
    rw [Finset.sum_congr rfl (hq j), Finset.sum_const, nsmul_eq_mul, hf,
      re_zeroSumTerm_truncModel]
    simp only [FiniteTopLayer.mult]
    ring
  simp_rw [hj]
  rw [Finset.sum_neg_distrib]
  have e := sum_re_testTransform_sq_eq (realIntervalSource_truncModel (δ := δ) t x a) δ t h.mult
  simp only [topPoint, hf]
  rw [e]
  rfl

/-! ## The reflected truncated model against the Cauchy model -/

theorem truncModel_reflect_eq (δ : ℝ) (t : Fin m → ℝ) (x : Fin m → ℂ) (a : ℝ) {s : ℝ}
    (hs : 0 < s) :
    truncModel (oddProfileModel δ t x a) a (a - s) =
      realProfile δ t x s + (-(Ioo 0 (2 * a)).indicator
        (fun s => realProfile δ t x (2 * a - s)) s) +
        (-(Ici (2 * a)).indicator (realProfile δ t x) s) := by
  unfold truncModel
  by_cases h2 : s < 2 * a
  · have hmem : a - s ∈ Ioo (-a) a := ⟨by linarith, by linarith⟩
    rw [indicator_of_mem hmem, indicator_of_mem (show s ∈ Ioo 0 (2 * a) from ⟨hs, h2⟩),
      indicator_of_notMem (show s ∉ Ici (2 * a) by simp only [mem_Ici, not_le]; exact h2)]
    unfold oddProfileModel
    rw [show a - (a - s) = s by ring, show a + (a - s) = 2 * a - s by ring]
    ring
  · push Not at h2
    have hmem : a - s ∉ Ioo (-a) a := fun h => by linarith [h.1]
    rw [indicator_of_notMem hmem, indicator_of_notMem (show s ∉ Ioo 0 (2 * a) from
      fun h => by linarith [h.2]), indicator_of_mem (show s ∈ Ici (2 * a) from h2)]
    ring

/-- The reflected copy `−1_{(0,2a)} P(2a − ·)` pairs to `O(a e^{−2δa})`. -/
theorem norm_halfLinePairing_reflectedCopy_le (δ : ℝ) (t : Fin m → ℝ)
    (x : Fin m → ℂ) {a : ℝ} (ha : 0 ≤ a) (j : Fin m) :
    ‖halfLinePairing δ t (-(Ioo 0 (2 * a)).indicator
      (fun s => realProfile δ t x (2 * a - s))) j‖ ≤
      2 * a * (profileBound x * Real.exp (-(2 * δ * a))) := by
  unfold halfLinePairing
  have hsub : ∫ s in Ioi (0 : ℝ),
      (((-(Ioo 0 (2 * a)).indicator (fun s => realProfile δ t x (2 * a - s))) s : ℝ) : ℂ) *
        Complex.exp (-((δ : ℂ) - I * t j) * s) =
      ∫ s in Ioo (0 : ℝ) (2 * a), -((realProfile δ t x (2 * a - s) : ℝ) : ℂ) *
        Complex.exp (-((δ : ℂ) - I * t j) * s) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioo]
    congr 1
    funext s
    by_cases hs : s ∈ Ioo 0 (2 * a)
    · rw [indicator_of_mem (show s ∈ Ioi (0 : ℝ) from hs.1), indicator_of_mem hs]
      simp [indicator_of_mem hs]
    · rw [indicator_of_notMem hs]
      by_cases hs0 : s ∈ Ioi (0 : ℝ)
      · rw [indicator_of_mem hs0]
        simp [indicator_of_notMem hs]
      · rw [indicator_of_notMem hs0]
  rw [hsub]
  have hbound : ∀ s ∈ Ioo (0 : ℝ) (2 * a), ‖-((realProfile δ t x (2 * a - s) : ℝ) : ℂ) *
      Complex.exp (-((δ : ℂ) - I * t j) * s)‖ ≤ profileBound x * Real.exp (-(2 * δ * a)) := by
    intro s hs
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, norm_exp_profile]
    have h1 := abs_realProfile_le δ t x (2 * a - s)
    calc |realProfile δ t x (2 * a - s)| * Real.exp (-(δ * s))
        ≤ profileBound x * Real.exp (-(δ * (2 * a - s))) * Real.exp (-(δ * s)) :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ = profileBound x * Real.exp (-(2 * δ * a)) := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
  have hle := norm_setIntegral_le_of_norm_le_const (μ := volume) measure_Ioo_lt_top hbound
  have hvol : volume.real (Ioo (0 : ℝ) (2 * a)) = 2 * a := by
    rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]
    ring
  rw [hvol] at hle
  linarith

/-- **The odd half-line form of the truncated model.** -/
theorem halfLineForm_truncModel_ge {δ : ℝ} (hδ : 0 < δ) (t M θ : Fin m → ℝ)
    (x : Fin m → ℂ) (hx : normForm δ t x = 1) {a : ℝ} (ha : 0 ≤ a) :
    quadForm δ t M θ x -
        (∑ j, |M j|) * (((2 * a * profileBound x + (1 + 1 / (2 * δ))) *
          Real.exp (-(δ * a))) * (2 * (1 + 1 / (2 * δ)) +
            (2 * a * profileBound x + (1 + 1 / (2 * δ))) * Real.exp (-(δ * a)))) ≤
      halfLineForm δ t M θ (fun s => truncModel (oddProfileModel δ t x a) a (a - s)) := by
  set P := realProfile δ t x with hP
  set w₁ : ℝ → ℝ := -(Ioo 0 (2 * a)).indicator (fun s => realProfile δ t x (2 * a - s)) with hw₁
  set w₂ : ℝ → ℝ := -(Ici (2 * a)).indicator (realProfile δ t x) with hw₂
  have hPm : MemLp P 2 (volume.restrict (Ioi 0)) := memLp_realProfile hδ t x
  have hw₂m : MemLp w₂ 2 (volume.restrict (Ioi 0)) := (hPm.indicator measurableSet_Ici).neg
  have hw₁m : MemLp w₁ 2 (volume.restrict (Ioi 0)) := by
    have hc : MemLp (fun s => realProfile δ t x (2 * a - s)) 2 (volume.restrict (Ioo 0 (2 * a))) := by
      haveI : IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) (2 * a))) :=
        ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioo_lt_top⟩
      have hcont : Continuous fun s => realProfile δ t x (2 * a - s) :=
        (continuous_realProfile δ t x).comp (continuous_const.sub continuous_id)
      obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 (2 * a))
        hcont.continuousOn
      exact MemLp.of_bound hcont.aestronglyMeasurable B
        ((ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall fun s hs => hB s (Ioo_subset_Icc_self hs)))
    have := (memLp_indicator_iff_restrict measurableSet_Ioo).mpr hc
    exact (this.restrict (Ioi 0)).neg
  have hw : MemLp (w₁ + w₂) 2 (volume.restrict (Ioi 0)) := hw₁m.add hw₂m
  -- the pairings agree with those of `P + (w₁ + w₂)`
  have hcongr : halfLineForm δ t M θ (fun s => truncModel (oddProfileModel δ t x a) a (a - s)) =
      halfLineForm δ t M θ (P + (w₁ + w₂)) := by
    apply halfLineForm_congr
    intro j
    unfold halfLinePairing
    refine setIntegral_congr_fun measurableSet_Ioi fun s hs => ?_
    simp only [Pi.add_apply]
    rw [truncModel_reflect_eq δ t x a hs]
    simp only [hw₁, hw₂, hP, Pi.neg_apply]
    push_cast
    ring
  rw [hcongr]
  have hpert := abs_halfLineForm_add_sub_le hδ t M θ hPm hw
  rw [← quadForm_eq_halfLineForm hδ] at hpert
  set κ : ℝ := 1 + 1 / (2 * δ) with hκ
  have hκ0 : 0 ≤ κ := by positivity
  set E : ℝ := Real.exp (-(δ * a)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set ε : ℝ := (2 * a * profileBound x + κ) * E with hε
  have hε0 : 0 ≤ ε := mul_nonneg (by have := profileBound_nonneg x; positivity) hE0
  have hκsq : 1 / (2 * δ) ≤ κ ^ 2 := by
    rw [hκ]; have : 0 ≤ 1 / (2 * δ) := by positivity
    nlinarith
  -- `‖⟨P, ψ_j⟩‖ ≤ κ`
  have hPP : ∀ j, ‖halfLinePairing δ t P j‖ ≤ κ := by
    intro j
    have h := norm_halfLinePairing_sq_le hδ t hPm j
    rw [← normForm_eq_integral hδ, hx, one_mul] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hκ0 two_ne_zero).mp (h.trans hκsq)
  -- `‖⟨w₂, ψ_j⟩‖ ≤ κ e^{−δa}`
  have hW2 : ∀ j, ‖halfLinePairing δ t w₂ j‖ ≤ κ * E := by
    intro j
    have h := norm_halfLinePairing_sq_le_of_vanish hδ t hw₂m ha (fun s hs => by
      simp only [hw₂, Pi.neg_apply]
      rw [indicator_of_notMem (show s ∉ Ici (2 * a) by
        simp only [mem_Ici, not_le]; linarith [hs.2, hs.1]), neg_zero]) j
    have hint : ∫ s in Ioi (0 : ℝ), w₂ s ^ 2 ≤ 1 := by
      rw [← hx, normForm_eq_integral hδ]
      refine setIntegral_mono_on hw₂m.integrable_sq hPm.integrable_sq measurableSet_Ioi
        fun s _ => ?_
      simp only [hw₂, Pi.neg_apply, neg_sq]
      by_cases hs : s ∈ Ici (2 * a)
      · rw [indicator_of_mem hs]
      · rw [indicator_of_notMem hs]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
        exact sq_nonneg _
    have hE2 : Real.exp (-(2 * δ) * a) = E ^ 2 := by
      rw [hE, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hE2] at h
    have h' : ‖halfLinePairing δ t w₂ j‖ ^ 2 ≤ (κ * E) ^ 2 := by
      calc ‖halfLinePairing δ t w₂ j‖ ^ 2 ≤ (∫ s in Ioi (0 : ℝ), w₂ s ^ 2) * (E ^ 2 / (2 * δ)) := h
        _ ≤ 1 * (E ^ 2 / (2 * δ)) := by gcongr
        _ = (1 / (2 * δ)) * E ^ 2 := by ring
        _ ≤ κ ^ 2 * E ^ 2 := by gcongr
        _ = (κ * E) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h'
  -- `‖⟨w₁, ψ_j⟩‖ ≤ 2a C e^{−2δa}`
  have hW1 : ∀ j, ‖halfLinePairing δ t w₁ j‖ ≤ 2 * a * profileBound x * E := by
    intro j
    have h := norm_halfLinePairing_reflectedCopy_le δ t x ha j
    have hE2 : Real.exp (-(2 * δ * a)) ≤ E := by
      rw [hE]; apply Real.exp_le_exp.mpr; nlinarith
    have hC := profileBound_nonneg x
    calc ‖halfLinePairing δ t w₁ j‖ ≤ 2 * a * (profileBound x * Real.exp (-(2 * δ * a))) := h
      _ ≤ 2 * a * (profileBound x * E) := by gcongr
      _ = 2 * a * profileBound x * E := by ring
  have hWsum : ∀ j, ‖halfLinePairing δ t (w₁ + w₂) j‖ ≤ ε := by
    intro j
    rw [halfLinePairing_add hδ t hw₁m hw₂m]
    refine (norm_add_le _ _).trans ?_
    have := hW1 j
    have := hW2 j
    rw [hε]
    nlinarith
  have hbound : ∑ j, |M j| * (‖halfLinePairing δ t (w₁ + w₂) j‖ *
      (2 * ‖halfLinePairing δ t P j‖ + ‖halfLinePairing δ t (w₁ + w₂) j‖)) ≤
      (∑ j, |M j|) * (ε * (2 * κ + ε)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h1 := hWsum j
    have h2 := hPP j
    have h0 := norm_nonneg (halfLinePairing δ t (w₁ + w₂) j)
    have h0' := norm_nonneg (halfLinePairing δ t P j)
    exact mul_le_mul h1 (by linarith) (by positivity) hε0
  rw [abs_le] at hpert
  linarith [hpert.1]

/-! ## The mass of the truncated model -/

theorem integral_truncModel_sq_le {δ : ℝ} (hδ : 0 < δ) (t : Fin m → ℝ) (x : Fin m → ℂ)
    (hx : normForm δ t x = 1) {a : ℝ} (ha : 0 ≤ a) :
    ∫ y, truncModel (oddProfileModel δ t x a) a y ^ 2 ≤
      2 + 4 * a * profileBound x ^ 2 * Real.exp (-(2 * δ * a)) := by
  set P := realProfile δ t x with hP
  set C := profileBound x with hC
  have hC0 : 0 ≤ C := profileBound_nonneg x
  set F : ℝ → ℝ := (Ioi 0).indicator (fun s => P s ^ 2) with hF
  have hFint : Integrable F := by
    rw [hF, integrable_indicator_iff measurableSet_Ioi]
    exact (memLp_realProfile hδ t x).integrable_sq
  have hFtot : ∫ s, F s = 1 := by
    rw [hF, integral_indicator measurableSet_Ioi, ← normForm_eq_integral hδ, hx]
  have hcont : Continuous P := continuous_realProfile δ t x
  have hpt : ∀ y ∈ Ioo (-a) a, truncModel (oddProfileModel δ t x a) a y ^ 2 ≤
      F (a - y) + F (a + y) + 2 * (C ^ 2 * Real.exp (-(2 * δ * a))) := by
    intro y hy
    unfold truncModel oddProfileModel
    rw [indicator_of_mem hy]
    have h1 : F (a - y) = P (a - y) ^ 2 := by
      rw [hF, indicator_of_mem (show a - y ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith [hy.2])]
    have h2 : F (a + y) = P (a + y) ^ 2 := by
      rw [hF, indicator_of_mem (show a + y ∈ Ioi (0 : ℝ) by simp only [mem_Ioi]; linarith [hy.1])]
    rw [h1, h2]
    have b1 := abs_realProfile_le δ t x (a - y)
    have b2 := abs_realProfile_le δ t x (a + y)
    have hprod : |P (a - y)| * |P (a + y)| ≤ C ^ 2 * Real.exp (-(2 * δ * a)) := by
      calc |P (a - y)| * |P (a + y)|
          ≤ (C * Real.exp (-(δ * (a - y)))) * (C * Real.exp (-(δ * (a + y)))) :=
            mul_le_mul b1 b2 (abs_nonneg _) (by positivity)
        _ = C ^ 2 * Real.exp (-(2 * δ * a)) := by
            rw [show C * Real.exp (-(δ * (a - y))) * (C * Real.exp (-(δ * (a + y)))) =
              C ^ 2 * (Real.exp (-(δ * (a - y))) * Real.exp (-(δ * (a + y)))) by ring,
              ← Real.exp_add]
            ring_nf
    have : -(P (a - y) * P (a + y)) ≤ |P (a - y)| * |P (a + y)| := by
      rw [← abs_mul]; exact neg_le_abs _
    nlinarith
  have hint1 : Integrable fun y => F (a - y) := hFint.comp_sub_left a
  have hint2 : Integrable fun y => F (a + y) := by
    have := hFint.comp_add_right a
    simpa [add_comm] using this
  have hfun : (fun y => truncModel (oddProfileModel δ t x a) a y ^ 2) =
      (Ioo (-a) a).indicator (fun y => oddProfileModel δ t x a y ^ 2) := by
    funext y
    unfold truncModel
    by_cases hy : y ∈ Ioo (-a) a <;> simp [hy]
  have hmeasIoo : volume (Ioo (-a) a) < ⊤ := measure_Ioo_lt_top
  have hRint : IntegrableOn (fun y => F (a - y) + F (a + y) +
      2 * (C ^ 2 * Real.exp (-(2 * δ * a)))) (Ioo (-a) a) :=
    ((hint1.add hint2).integrableOn).add (integrableOn_const hmeasIoo.ne)
  have hLint : IntegrableOn (fun y => oddProfileModel δ t x a y ^ 2) (Ioo (-a) a) :=
    ((contDiff_oddProfileModel δ t x a).continuous.pow 2).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [hfun, integral_indicator measurableSet_Ioo]
  calc ∫ y in Ioo (-a) a, oddProfileModel δ t x a y ^ 2
      ≤ ∫ y in Ioo (-a) a, (F (a - y) + F (a + y) + 2 * (C ^ 2 * Real.exp (-(2 * δ * a)))) := by
        refine setIntegral_mono_on hLint hRint measurableSet_Ioo fun y hy => ?_
        have := hpt y hy
        unfold truncModel at this
        rwa [indicator_of_mem hy] at this
    _ = (∫ y in Ioo (-a) a, F (a - y)) + (∫ y in Ioo (-a) a, F (a + y)) +
          2 * a * (2 * (C ^ 2 * Real.exp (-(2 * δ * a)))) := by
        have hA : IntegrableOn (fun y => F (a - y) + F (a + y)) (Ioo (-a) a) :=
          (hint1.add hint2).integrableOn
        rw [integral_add hA (integrableOn_const hmeasIoo.ne),
          integral_add hint1.integrableOn hint2.integrableOn, setIntegral_const]
        rw [Measure.real, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
        ring
    _ ≤ 1 + 1 + 2 * a * (2 * (C ^ 2 * Real.exp (-(2 * δ * a)))) := by
        have hF0 : ∀ y, 0 ≤ F y := fun y => by
          rw [hF]; by_cases hy : y ∈ Ioi (0 : ℝ) <;> simp [hy, sq_nonneg]
        have e1 : ∫ y in Ioo (-a) a, F (a - y) ≤ ∫ y, F (a - y) :=
          setIntegral_le_integral hint1 (Filter.Eventually.of_forall fun y => hF0 _)
        have e2 : ∫ y in Ioo (-a) a, F (a + y) ≤ ∫ y, F (a + y) :=
          setIntegral_le_integral hint2 (Filter.Eventually.of_forall fun y => hF0 _)
        have r1 : ∫ y, F (a - y) = 1 := by rw [integral_sub_left_eq_self F volume a, hFtot]
        have r2 : ∫ y, F (a + y) = 1 := by rw [integral_add_left_eq_self F a, hFtot]
        linarith
    _ = 2 + 4 * a * C ^ 2 * Real.exp (-(2 * δ * a)) := by ring

end

end RHTower.CCMParityTopLayer
