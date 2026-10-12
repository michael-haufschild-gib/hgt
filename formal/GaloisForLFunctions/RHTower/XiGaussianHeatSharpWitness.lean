import GaloisForLFunctions.RHTower.XiGaussianHeatSharpWitnessComparison

/-!
# A Weil-negative source gives a negative heat Hankel value on the pole hyperplane

**Per-time comparison** (`exists_poleCorrected_near_smoothed`).  For a smooth even real source `u`
vanishing outside `[−A, A]` with `∫ u e^{x/2} = 0`, a heat time `0 < a ≤ 1/16` and a degree bound
`n`, there is a real polynomial `P` of degree `≤ n` with `P(−1/4) = 0` such that

`|H_a(P, P) − Σ_q F_{u_a}(z_q)²| ≤ N (M + e^{1/8} U'') S₂ + N (2e^{1/8} M S₂ + N e^{1/2}(1 + 1/a) S)`,

where `g` is the degree-`(2n+1)` Hermite truncation of `u_a` at width `(2πa)^{1/2}`,
`N = ∫|g − u_a| e^{|x|/2}`, `M = ∫|g''| e^{|x|/2}`, `U'' = ∫|u''| e^{|x|/2}`,
`S₂ = Σ_q |z_q|^{-2}` and `S = Σ_q (1 + |w_q|)^{-1}`.  `P` is the heat-test polynomial of `g`
(`exists_heatPolyR_eq`), corrected by its value at the pole.
-/

open scoped Real
open Complex MeasureTheory Set Polynomial Filter Topology
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly hasDerivAt_gaussPolyFun continuous_gaussPolyFun
  sq_integral_abs_gaussPolyFun_mul_exp_half_le)

namespace RHTower

noncomputable section

/-- The strip mass `∫ |f| e^{|x|/2}`. -/
def stripMass (f : ℝ → ℝ) : ℝ := ∫ x, |f x| * Real.exp (|x| / 2)

/-- The truncated heat test of degree `2n`. -/
def truncHeatTest (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {a : ℝ}
    (ha : 0 < a) (n : ℕ) : ℝ → ℝ :=
  gaussPolyFun (truncHeatPoly u hu hcpt ha (2 * n + 1)) (1 / (2 * a))

/-- Its second derivative. -/
def truncHeatTestDD (u : ℝ → ℝ) (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcpt : HasCompactSupport u) {a : ℝ}
    (ha : 0 < a) (n : ℕ) : ℝ → ℝ :=
  gaussPolyFun (gaussPolyDerivPoly (gaussPolyDerivPoly (truncHeatPoly u hu hcpt ha (2 * n + 1))
    (1 / (2 * a))) (1 / (2 * a))) (1 / (2 * a))

theorem integrable_norm_ofReal_gaussPolyFun_mul_exp (Q : ℝ[X]) {β : ℝ} (hβ : 1 / 2 < β) :
    Integrable (fun x => ‖((gaussPolyFun Q β x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by
  simpa only [norm_ofReal_mul_exp] using (sq_integral_abs_gaussPolyFun_mul_exp_half_le Q hβ one_pos 0).1

/-- `|z|² |F_g(z)| ≤ ∫ |g''| e^{|x|/2}` for a polynomial–Gaussian. -/
theorem sq_norm_mul_heatStripTransform_gaussPolyFun_le (Q : ℝ[X]) {β : ℝ} (hβ : 1 / 2 < β) {z : ℂ}
    (hz : |z.im| ≤ 1 / 2) :
    ‖z‖ ^ 2 * ‖heatStripTransform (fun x => ((gaussPolyFun Q β x : ℝ) : ℂ)) z‖ ≤
      stripMass (gaussPolyFun (gaussPolyDerivPoly (gaussPolyDerivPoly Q β) β) β) := by
  have h := sq_norm_mul_norm_heatStripTransform_le
    (f := fun x => ((gaussPolyFun Q β x : ℝ) : ℂ))
    (f' := fun x => ((gaussPolyFun (gaussPolyDerivPoly Q β) β x : ℝ) : ℂ))
    (f'' := fun x => ((gaussPolyFun (gaussPolyDerivPoly (gaussPolyDerivPoly Q β) β) β x : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (continuous_gaussPolyFun _ _))
    (Complex.continuous_ofReal.comp (continuous_gaussPolyFun _ _))
    (Complex.continuous_ofReal.comp (continuous_gaussPolyFun _ _))
    (fun x => (hasDerivAt_gaussPolyFun _ _ x).ofReal_comp)
    (fun x => (hasDerivAt_gaussPolyFun _ _ x).ofReal_comp)
    (integrable_norm_ofReal_gaussPolyFun_mul_exp _ hβ)
    (integrable_norm_ofReal_gaussPolyFun_mul_exp _ hβ)
    (integrable_norm_ofReal_gaussPolyFun_mul_exp _ hβ) hz
  simpa only [norm_ofReal_mul_exp, stripMass] using h

/-- `|z|² |F_u(z)| ≤ ∫ |u''| e^{|x|/2}` for a smooth compactly supported source. -/
theorem sq_norm_mul_heatStripTransform_source_le {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖z‖ ^ 2 * ‖heatStripTransform (fun x => ((u x : ℝ) : ℂ)) z‖ ≤ stripMass (deriv (deriv u)) := by
  have hu1 : ContDiff ℝ (⊤ : ℕ∞) (deriv u) := (contDiff_infty_iff_deriv.1 hu).2
  have hu2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv u)) := (contDiff_infty_iff_deriv.1 hu1).2
  have hd0 : ∀ x, HasDerivAt u (deriv u x) x := fun x =>
    ((contDiff_infty_iff_deriv.1 hu).1 x).hasDerivAt
  have hd1 : ∀ x, HasDerivAt (deriv u) (deriv (deriv u) x) x := fun x =>
    ((contDiff_infty_iff_deriv.1 hu1).1 x).hasDerivAt
  have hc1 : HasCompactSupport (deriv u) := hcpt.deriv
  have hc2 : HasCompactSupport (deriv (deriv u)) := hc1.deriv
  have h := sq_norm_mul_norm_heatStripTransform_le
    (f := fun x => ((u x : ℝ) : ℂ)) (f' := fun x => ((deriv u x : ℝ) : ℂ))
    (f'' := fun x => ((deriv (deriv u) x : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hu.continuous) (Complex.continuous_ofReal.comp hu1.continuous)
    (Complex.continuous_ofReal.comp hu2.continuous)
    (fun x => (hd0 x).ofReal_comp) (fun x => (hd1 x).ofReal_comp)
    (by simpa only [norm_ofReal_mul_exp] using integrable_abs_of_compact hu.continuous hcpt)
    (by simpa only [norm_ofReal_mul_exp] using integrable_abs_of_compact hu1.continuous hc1)
    (by simpa only [norm_ofReal_mul_exp] using integrable_abs_of_compact hu2.continuous hc2) hz
  simpa only [norm_ofReal_mul_exp, stripMass] using h

/-- `|H_a(1, 1)| ≤ e^{a/2}(1 + 1/a) Σ_q (1 + |w_q|)^{-1}`. -/
theorem norm_heatHankel_one_one_le {a : ℝ} (ha : 0 < a) :
    ‖heatHankel a 1 1‖ ≤ Real.exp (a / 2) * (1 + 1 / a) *
      ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) := by
  have hsum := summable_inv_one_add_norm_xiHeatFrequency.mul_left (Real.exp (a / 2) * (1 + 1 / a))
  have hterm : ∀ q : XiZeroCopy, ‖heatHankelTermAt a 1 1 (xiHeatFrequency q)‖ ≤
      Real.exp (a / 2) * (1 + 1 / a) * (1 / (1 + ‖xiHeatFrequency q‖)) := fun q => by
    have hz := abs_im_xiSpectralPoint_le_half q
    rw [heatHankelTermAt, eval_one, eval_one, map_one, mul_one, mul_one, Complex.norm_exp,
      show xiHeatFrequency q = xiSpectralPoint q ^ 2 from rfl]
    have : (-(a : ℂ) * xiSpectralPoint q ^ 2).re = -(a * (xiSpectralPoint q ^ 2).re) := by simp
    rw [this]
    exact exp_neg_re_le ha hz
  unfold heatHankel
  calc ‖∑' q : XiZeroCopy, heatHankelTermAt a 1 1 (xiHeatFrequency q)‖
      ≤ ∑' q : XiZeroCopy, Real.exp (a / 2) * (1 + 1 / a) * (1 / (1 + ‖xiHeatFrequency q‖)) :=
        tsum_of_norm_bounded hsum.hasSum hterm
    _ = _ := tsum_mul_left

/-- **Per-time comparison of the corrected truncated heat test with the smoothed source.** -/
theorem exists_poleCorrected_near_smoothed {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hcpt : HasCompactSupport u) {A : ℝ} (hsupp : ∀ t : ℝ, A < |t| → u t = 0)
    (heven : ∀ x, u (-x) = u x) (hpole : ∫ x, u x * Real.exp (x / 2) = 0) {a : ℝ} (ha : 0 < a)
    (ha16 : a ≤ 1 / 16) (n : ℕ) :
    ∃ P : ℝ[X], P.natDegree ≤ n ∧ P.eval (-1 / 4) = 0 ∧
      ‖heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) -
          ∑' q : XiZeroCopy, heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ))
            (xiSpectralPoint q) ^ 2‖ ≤
        stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) *
            (stripMass (truncHeatTestDD u hu hcpt ha n) +
              Real.exp (1 / 8) * stripMass (deriv (deriv u))) *
            ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 +
          stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) *
            (2 * (Real.exp (1 / 8) * stripMass (truncHeatTestDD u hu hcpt ha n) *
                ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2) +
              stripMass (fun x => truncHeatTest u hu hcpt ha n x - heatSmooth a u x) *
                (Real.exp (1 / 2) * (1 + 1 / a) *
                  ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖))) := by
  have hβ : 1 / 2 < 1 / (2 * a) := by rw [lt_div_iff₀ (by positivity)]; nlinarith
  set Q := truncHeatPoly u hu hcpt ha (2 * n + 1) with hQ_def
  have hQe : Q.comp (-X) = Q := truncHeatPoly_comp_neg u hu hcpt heven ha _
  have hQd : Q.natDegree ≤ 2 * n := (natDegree_truncHeatPoly_le u hu hcpt ha _).trans (by omega)
  obtain ⟨P₀, hP₀d, hP₀⟩ := exists_heatPolyR_eq ha n Q hQe hQd
  set c := P₀.eval (-1 / 4) with hc_def
  refine ⟨P₀ - C c, (natDegree_sub_C.le).trans hP₀d, by rw [eval_sub, eval_C, sub_self], ?_⟩
  -- notation
  set g := truncHeatTest u hu hcpt ha n with hg_def
  have hgQ : g = gaussPolyFun Q (1 / (2 * a)) := rfl
  set Ngu := stripMass (fun x => g x - heatSmooth a u x) with hNgu
  set Ng2 := stripMass (truncHeatTestDD u hu hcpt ha n) with hNg2
  set U2 := stripMass (deriv (deriv u)) with hU2
  set S₂ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 with hS₂
  set S := ∑' q : XiZeroCopy, 1 / (1 + ‖xiHeatFrequency q‖) with hS
  set Fg : ℂ → ℂ := heatStripTransform (fun x => ((g x : ℝ) : ℂ)) with hFg_def
  set Fw : ℂ → ℂ := heatStripTransform (fun x => ((heatSmooth a u x : ℝ) : ℂ)) with hFw_def
  set Fu : ℂ → ℂ := heatStripTransform (fun x => ((u x : ℝ) : ℂ)) with hFu_def
  have hFgP : ∀ z, Fg z = Complex.exp (-(a : ℂ) * z ^ 2 / 2) *
      (P₀.map (algebraMap ℝ ℂ)).eval (z ^ 2) := fun z => by
    have h := heatStripTransform_heatPhysical ha P₀ z
    rw [hP₀] at h
    exact h
  have hFw : ∀ z, Fw z = Complex.exp (-(a : ℂ) * z ^ 2 / 2) * Fu z := fun z =>
    heatStripTransform_heatSmooth ha hu.continuous hcpt z
  -- integrability
  have hgi : Integrable (fun x => ‖((g x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) :=
    integrable_norm_ofReal_gaussPolyFun_mul_exp Q hβ
  have hwi : Integrable (fun x => ‖((heatSmooth a u x : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by
    simpa only [norm_ofReal_mul_exp] using
      integrable_abs_heatSmooth_mul_exp ha ha16 hu hcpt hsupp
  have hgc : Continuous g := continuous_gaussPolyFun _ _
  have hwc : Continuous (heatSmooth a u) := continuous_heatSmooth hu hcpt ha
  have hdi : Integrable (fun x => ‖(((g x - heatSmooth a u x) : ℝ) : ℂ)‖ * Real.exp (|x| / 2)) := by
    refine (hgi.add hwi).mono' ((continuous_norm.comp (Complex.continuous_ofReal.comp
      (hgc.sub hwc))).mul (Real.continuous_exp.comp (continuous_abs.div_const 2))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply]
    rw [Complex.ofReal_sub, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (Real.exp_pos _).le
  -- (b1) the difference on the strip
  have hb1 : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖Fg z - Fw z‖ ≤ Ngu := fun z hz => by
    have h1 := integrable_mul_cexp_of_strip (f := fun x => ((g x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hgc) hgi hz
    have h2 := integrable_mul_cexp_of_strip (f := fun x => ((heatSmooth a u x : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp hwc) hwi hz
    have e : Fg z - Fw z = heatStripTransform (fun x => (((g x - heatSmooth a u x) : ℝ) : ℂ)) z := by
      rw [hFg_def, hFw_def]
      unfold heatStripTransform
      rw [← integral_sub h1 h2]
      congr 1; funext x; push_cast; ring
    rw [e]
    have := norm_heatStripTransform_le hdi hz
    simpa only [Complex.norm_real, Real.norm_eq_abs, hNgu, stripMass] using this
  -- (b2), (b3)
  have hb2 : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖z‖ ^ 2 * ‖Fg z‖ ≤ Ng2 := fun z hz =>
    sq_norm_mul_heatStripTransform_gaussPolyFun_le Q hβ hz
  have hb3 : ∀ z : ℂ, |z.im| ≤ 1 / 2 → ‖z‖ ^ 2 * ‖Fw z‖ ≤ Real.exp (1 / 8) * U2 := fun z hz => by
    rw [hFw, norm_mul]
    have he : ‖Complex.exp (-(a : ℂ) * z ^ 2 / 2)‖ ≤ Real.exp (1 / 8) :=
      (norm_cexp_heat_le ha.le hz).trans (Real.exp_le_exp.2 (by linarith))
    have hu2 := sq_norm_mul_heatStripTransform_source_le hu hcpt hz
    calc ‖z‖ ^ 2 * (‖Complex.exp (-(a : ℂ) * z ^ 2 / 2)‖ * ‖Fu z‖)
        = ‖Complex.exp (-(a : ℂ) * z ^ 2 / 2)‖ * (‖z‖ ^ 2 * ‖Fu z‖) := by ring
      _ ≤ Real.exp (1 / 8) * U2 := mul_le_mul he hu2 (by positivity) (Real.exp_pos _).le
  -- (b4) the pole value
  have hU2 : 0 ≤ U2 := integral_nonneg fun _ => by positivity
  have hNgu0 : 0 ≤ Ngu := integral_nonneg fun _ => by positivity
  have hcb : |c| ≤ Ngu := by
    have hzI : |(I / 2 : ℂ).im| ≤ 1 / 2 := by simp [abs_of_pos]
    have h := hb1 (I / 2) hzI
    have hw0 : Fw (I / 2) = 0 := by
      rw [hFw, hFu_def, heatStripTransform_I_half_eq_zero heven hpole, mul_zero]
    have hg0 : Fg (I / 2) = Complex.exp ((a : ℂ) / 8) * ((c : ℝ) : ℂ) := by
      rw [hFgP, hc_def]
      have hsq : (I / 2 : ℂ) ^ 2 = (((-1 / 4 : ℝ)) : ℂ) := by push_cast; ring_nf; rw [I_sq]; ring
      rw [hsq, eval_map_ofReal]
      congr 1
      congr 1
      push_cast
      ring_nf
    rw [hw0, sub_zero, hg0, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs] at h
    have : (((a : ℂ) / 8).re) = a / 8 := by simp
    rw [this] at h
    have he : 1 ≤ Real.exp (a / 8) := Real.one_le_exp (by positivity)
    nlinarith [abs_nonneg c]
  -- (b5), (b6) cross terms
  have hcross := norm_heatHankel_one_le (P := P₀.map (algebraMap ℝ ℂ)) ha.le (M := Ng2)
    fun z hz => by rw [← hFgP]; exact hb2 z hz
  have he8 : Real.exp (a / 8) ≤ Real.exp (1 / 8) := Real.exp_le_exp.2 (by linarith)
  have he2 : Real.exp (a / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.2 (by linarith)
  have h11 := norm_heatHankel_one_one_le ha
  -- (b7) comparison
  obtain ⟨-, -, hcmp⟩ := norm_tsum_sq_sub_le (F := fun q => Fg (xiSpectralPoint q))
    (G := fun q => Fw (xiSpectralPoint q)) (D := Ngu) (MF := Ng2) (MG := Real.exp (1 / 8) * U2)
    (fun q => hb1 _ (abs_im_xiSpectralPoint_le_half q))
    (fun q => hb2 _ (abs_im_xiSpectralPoint_le_half q))
    (fun q => hb3 _ (abs_im_xiSpectralPoint_le_half q))
  have hH0 : heatHankel a (P₀.map (algebraMap ℝ ℂ)) (P₀.map (algebraMap ℝ ℂ)) =
      ∑' q : XiZeroCopy, Fg (xiSpectralPoint q) ^ 2 := by
    have h := heatHankel_map_eq_tsum_sq ha P₀
    rw [hP₀] at h
    exact h
  have hmap : (P₀ - C c).map (algebraMap ℝ ℂ) = P₀.map (algebraMap ℝ ℂ) - C (c : ℂ) := by
    rw [Polynomial.map_sub, Polynomial.map_C]; rfl
  rw [hmap, heatHankel_sub_C ha, hH0]
  have hc' : ‖(c : ℂ)‖ ≤ Ngu := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hcb
  have hcc : ‖((starRingEnd ℂ) (c : ℂ))‖ ≤ Ngu := by rw [Complex.norm_conj]; exact hc'
  have hns : ‖((Complex.normSq (c : ℂ) : ℝ) : ℂ)‖ ≤ Ngu * Ngu := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Complex.normSq_nonneg _),
      Complex.normSq_eq_norm_sq, sq]
    exact mul_le_mul hc' hc' (norm_nonneg _) hNgu0
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hS₂0 : 0 ≤ S₂ := tsum_nonneg fun _ => by positivity
  have hNg20 : 0 ≤ Ng2 := integral_nonneg fun _ => by positivity
  have hA1 : ‖heatHankel a (P₀.map (algebraMap ℝ ℂ)) 1‖ ≤ Real.exp (1 / 8) * Ng2 * S₂ :=
    hcross.1.trans (by gcongr)
  have hA2 : ‖heatHankel a 1 (P₀.map (algebraMap ℝ ℂ))‖ ≤ Real.exp (1 / 8) * Ng2 * S₂ :=
    hcross.2.trans (by gcongr)
  have hA3 : ‖heatHankel a 1 1‖ ≤ Real.exp (1 / 2) * (1 + 1 / a) * S :=
    h11.trans (by gcongr)
  calc ‖(∑' q : XiZeroCopy, Fg (xiSpectralPoint q) ^ 2) -
          (starRingEnd ℂ) (c : ℂ) * heatHankel a (P₀.map (algebraMap ℝ ℂ)) 1 -
          (c : ℂ) * heatHankel a 1 (P₀.map (algebraMap ℝ ℂ)) +
          ((Complex.normSq (c : ℂ) : ℝ) : ℂ) * heatHankel a 1 1 -
          ∑' q : XiZeroCopy, Fw (xiSpectralPoint q) ^ 2‖
      = ‖((∑' q : XiZeroCopy, Fg (xiSpectralPoint q) ^ 2) -
            ∑' q : XiZeroCopy, Fw (xiSpectralPoint q) ^ 2) -
          ((starRingEnd ℂ) (c : ℂ) * heatHankel a (P₀.map (algebraMap ℝ ℂ)) 1 +
            (c : ℂ) * heatHankel a 1 (P₀.map (algebraMap ℝ ℂ))) +
          ((Complex.normSq (c : ℂ) : ℝ) : ℂ) * heatHankel a 1 1‖ := by ring_nf
    _ ≤ Ngu * (Ng2 + Real.exp (1 / 8) * U2) * S₂ +
          (Ngu * (Real.exp (1 / 8) * Ng2 * S₂) + Ngu * (Real.exp (1 / 8) * Ng2 * S₂)) +
          Ngu * Ngu * (Real.exp (1 / 2) * (1 + 1 / a) * S) := by
        refine (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans (add_le_add hcmp
          ((norm_add_le _ _).trans (add_le_add ?_ ?_)))) ?_)
        · rw [norm_mul]; exact mul_le_mul hcc hA1 (norm_nonneg _) hNgu0
        · rw [norm_mul]; exact mul_le_mul hc' hA2 (norm_nonneg _) hNgu0
        · rw [norm_mul]; exact mul_le_mul hns hA3 (norm_nonneg _) (by positivity)
    _ = _ := by ring

end

end RHTower
