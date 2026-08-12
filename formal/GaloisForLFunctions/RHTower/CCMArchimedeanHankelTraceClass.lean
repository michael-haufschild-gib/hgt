import GaloisForLFunctions.RHTower.CCMArchimedeanQuantizedCalculus
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.HTGeometry.SchwartzTranslation
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Half-line Hankel factorization for the CCM quantized differential

Connes--Consani reduce their Lemma `quantsmooth` to the two off-diagonal half-line Hankel
blocks with kernel `g(x+y)`, for a Schwartz function `g`.  This file constructs the exact
Hilbert--Schmidt factorization used to prove those blocks trace class.

The intermediate variable carries Lebesgue measure on `[0,∞)`.  Its first factor is the weighted
Volterra observer

`Bf(t) = (1+t²)⁻¹ ∫₀ᵗ f(y) dy`.

The intrinsic interval-vector field is proved Bochner `L²`; no boundedness, measurability, or
integrability premise is exposed to the eventual source theorem.
-/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Real SchwartzMap Topology symmDiff

namespace RHTower

/-- Lebesgue measure restricted to the positive half-line, used as the factorization carrier. -/
def ccmPositiveMeasure : Measure ℝ :=
  (volume : Measure ℝ).restrict (Ici 0)

/-- Positive-half-line `L²` carrier in the Hankel factorization. -/
abbrev CCMPositiveL2 := Lp ℂ 2 ccmPositiveMeasure

/-- Interval vector `1_[0,max(t,0)]` in full real-line `L²`. -/
def ccmHalfIntervalVec (t : ℝ) : SoninL2 :=
  indicatorConstLp 2 (measurableSet_Icc : MeasurableSet (Icc 0 (max t 0)))
    (by simp [Real.volume_Icc] : volume (Icc 0 (max t 0)) ≠ ∞) (1 : ℂ)

/-- Exact symmetric-difference measure of two anchored half-intervals. -/
theorem volume_ccmHalfInterval_symmDiff (s t : ℝ) :
    volume (Icc 0 (max s 0) ∆ Icc 0 (max t 0)) =
      ENNReal.ofReal |max s 0 - max t 0| := by
  rcases le_total (max s 0) (max t 0) with h | h
  · have hset : Icc 0 (max s 0) ∆ Icc 0 (max t 0) = Ioc (max s 0) (max t 0) := by
      ext x
      simp only [mem_symmDiff, mem_Icc, mem_Ioc]
      constructor
      · rintro (⟨⟨hx0, hxs⟩, hnot⟩ | ⟨⟨hx0, hxt⟩, hnot⟩)
        · exact False.elim (hnot ⟨hx0, hxs.trans h⟩)
        · exact ⟨lt_of_not_ge (fun hle => hnot ⟨hx0, hle⟩), hxt⟩
      · rintro ⟨hxs, hxt⟩
        exact Or.inr ⟨⟨(le_max_right s 0).trans hxs.le, hxt⟩,
          fun hx => (not_le_of_gt hxs) hx.2⟩
    rw [hset, Real.volume_Ioc, abs_of_nonpos (sub_nonpos.mpr h)]
    congr 1
    ring
  · have hset : Icc 0 (max s 0) ∆ Icc 0 (max t 0) = Ioc (max t 0) (max s 0) := by
      ext x
      simp only [mem_symmDiff, mem_Icc, mem_Ioc]
      constructor
      · rintro (⟨⟨hx0, hxs⟩, hnot⟩ | ⟨⟨hx0, hxt⟩, hnot⟩)
        · exact ⟨lt_of_not_ge (fun hle => hnot ⟨hx0, hle⟩), hxs⟩
        · exact False.elim (hnot ⟨hx0, hxt.trans h⟩)
      · rintro ⟨hxt, hxs⟩
        exact Or.inl ⟨⟨(le_max_right t 0).trans hxt.le, hxs⟩,
          fun hx => (not_le_of_gt hxt) hx.2⟩
    rw [hset, Real.volume_Ioc, abs_of_nonneg (sub_nonneg.mpr h)]

/-- The anchored interval vector is strongly continuous in its endpoint. -/
theorem continuous_ccmHalfIntervalVec : Continuous ccmHalfIntervalVec := by
  apply continuous_indicatorConstLp_set (p := (2 : ENNReal)) (c := (1 : ℂ)) (by norm_num)
  intro x
  rw [show (fun y : ℝ => volume (Icc 0 (max y 0) ∆ Icc 0 (max x 0))) =
      fun y => ENNReal.ofReal |max y 0 - max x 0| by
    funext y
    exact volume_ccmHalfInterval_symmDiff y x]
  have hc : Continuous (fun y : ℝ => ENNReal.ofReal |max y 0 - max x 0|) :=
    ENNReal.continuous_ofReal.comp
      (continuous_abs.comp ((continuous_id.max continuous_const).sub continuous_const))
  simpa using hc.tendsto x

/-- Weighted Volterra observer vector `(1+t²)⁻¹ 1_[0,max(t,0)]`. -/
def ccmVolterraObserverVec (t : ℝ) : SoninL2 :=
  (((1 + t ^ 2)⁻¹ : ℝ) : ℂ) • ccmHalfIntervalVec t

theorem continuous_ccmVolterraObserverVec : Continuous ccmVolterraObserverVec := by
  exact (Complex.continuous_ofReal.comp
    ((continuous_const.add (continuous_id.pow 2)).inv₀ (by
      intro t h
      change 1 + t ^ 2 = 0 at h
      nlinarith [sq_nonneg t])))
      |>.smul continuous_ccmHalfIntervalVec

/-- Pointwise `L²` energy bound furnishing the first Hilbert--Schmidt factor. -/
theorem norm_ccmVolterraObserverVec_sq_le {t : ℝ} (ht : 0 ≤ t) :
    ‖ccmVolterraObserverVec t‖ ^ 2 ≤ (1 + t ^ 2)⁻¹ := by
  rw [ccmVolterraObserverVec, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity)), ccmHalfIntervalVec,
    norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul,
    measureReal_def, Real.volume_Icc, max_eq_left ht, sub_zero,
    ENNReal.toReal_ofReal ht, show (2 : ENNReal).toReal = 2 by norm_num,
    one_div, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, mul_pow,
    Real.sq_sqrt ht]
  have hpos : 0 < 1 + t ^ 2 := by positivity
  rw [inv_pow]
  field_simp
  nlinarith [sq_nonneg t]

theorem ccmVolterraObserverVec_memLp :
    MemLp ccmVolterraObserverVec 2 ccmPositiveMeasure := by
  refine (memLp_two_iff_integrable_sq_norm
    continuous_ccmVolterraObserverVec.aestronglyMeasurable).mpr ?_
  refine Integrable.mono' integrable_inv_one_add_sq.integrableOn
    (continuous_ccmVolterraObserverVec.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ccmVolterraObserverVec t‖)]
  exact norm_ccmVolterraObserverVec_sq_le ht

/-- Bochner `L²` field for the weighted Volterra observer. -/
def ccmVolterraObserverField : Lp SoninL2 2 ccmPositiveMeasure :=
  ccmVolterraObserverVec_memLp.toLp ccmVolterraObserverVec

/-- First factor in the Hankel trace-class decomposition. -/
def ccmVolterraObserver : SoninL2 →L[ℂ] CCMPositiveL2 :=
  l2ObserverAnalysis ccmPositiveMeasure ccmVolterraObserverField

/-- The first Hankel factor is genuinely Hilbert--Schmidt. -/
theorem ccmVolterraObserver_isHilbertSchmidt :
    ccmVolterraObserver.IsHilbertSchmidt :=
  l2ObserverAnalysis_isHilbertSchmidt ccmPositiveMeasure ccmVolterraObserverField

/-! ## The derivative synthesis factor -/

/-- Translation is strongly continuous on the Schwartz space. -/
theorem continuous_ccmTranslateOrbit (g : 𝓢(ℝ, ℂ)) :
    Continuous (fun t : ℝ => SchwartzMap.translateCLM ℂ t g) := by
  rw [continuous_iff_continuousAt]
  intro a
  have hsub : Tendsto (fun t : ℝ => t - a) (𝓝 a) (𝓝 0) := by
    have hc : Continuous (fun _ : ℝ => a) := continuous_const
    have ht := (continuous_id.sub hc).tendsto a
    change Tendsto (fun t : ℝ => t - a) (𝓝 a) (𝓝 (a - a)) at ht
    simpa using ht
  have h := (SchwartzMap.tendsto_translateCLM_add_zero g a).comp hsub
  have hfun :
      ((fun h : ℝ => SchwartzMap.translateCLM ℂ (a + h) g) ∘ fun t : ℝ => t - a) =
        fun t : ℝ => SchwartzMap.translateCLM ℂ t g := by
    funext t
    change SchwartzMap.translateCLM ℂ (a + (t - a)) g = SchwartzMap.translateCLM ℂ t g
    rw [show a + (t - a) = t by ring]
  rw [hfun] at h
  exact h

/-- Positive-half-line slice `x ↦ -(1+t²)g'(x+t)` of the derivative factor. -/
def ccmHankelDerivativeSlice (g : 𝓢(ℝ, ℂ)) (t : ℝ) : SoninL2 :=
  ((-(1 + t ^ 2) : ℂ)) •
    ccmPositiveHalfLineProjection
      ((SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)).toLp 2 volume)

theorem continuous_ccmHankelDerivativeSlice (g : 𝓢(ℝ, ℂ)) :
    Continuous (ccmHankelDerivativeSlice g) := by
  have horbit : Continuous (fun t : ℝ =>
      SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)) :=
    continuous_ccmTranslateOrbit _
  have hlp : Continuous (fun t : ℝ =>
      (SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)).toLp 2 volume) := by
    exact (SchwartzMap.toLpCLM ℂ ℂ 2 volume).continuous.comp horbit
  have hscalar : Continuous (fun t : ℝ => (-(1 + t ^ 2) : ℂ)) := by fun_prop
  exact hscalar.smul (ccmPositiveHalfLineProjection.continuous.comp hlp)

/-- Exact almost-everywhere representative of the derivative slice. -/
theorem ccmHankelDerivativeSlice_coeFn (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    (ccmHankelDerivativeSlice g t : ℝ → ℂ) =ᵐ[volume]
      fun x => if 0 ≤ x then -(1 + t ^ 2) * deriv g (x + t) else 0 := by
  have hcut :
      (ccmPositiveHalfLineProjection
        ((SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)).toLp 2 volume) :
          ℝ → ℂ) =ᵐ[volume]
        (Ici 0).indicator fun x =>
          ((SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)).toLp 2 volume) x := by
    simpa [ccmPositiveHalfLineProjection] using
      indicatorCutoff_ae (Ici 0) measurableSet_Ici
        ((SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)).toLp 2 volume)
  have hlp := SchwartzMap.coeFn_toLp
    (SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)) 2 volume
  have hsmul := Lp.coeFn_smul (-(1 + t ^ 2) : ℂ)
    (ccmPositiveHalfLineProjection
      ((SchwartzMap.translateCLM ℂ t (SchwartzMap.derivCLM ℂ ℂ g)).toLp 2 volume))
  filter_upwards [hcut, hlp, hsmul] with x hxcut hxlp hxsmul
  simp only [Pi.smul_apply, smul_eq_mul] at hxsmul
  rw [ccmHankelDerivativeSlice, hxsmul, hxcut]
  simp only [indicator_apply, mem_Ici]
  split_ifs with hx
  · rw [hxlp, SchwartzMap.translateCLM_apply, SchwartzMap.derivCLM_apply]
  · simp

/-- Explicit Schwartz seminorm controlling all derivative slices. -/
def ccmDerivativeDecayConstant (g : 𝓢(ℝ, ℂ)) : ℝ :=
  2 ^ 6 * (Finset.Iic (6, 0)).sup
    (fun m => SchwartzMap.seminorm ℂ m.1 m.2)
      (SchwartzMap.derivCLM ℂ ℂ g)

theorem ccmDerivativeDecayConstant_nonneg (g : 𝓢(ℝ, ℂ)) :
    0 ≤ ccmDerivativeDecayConstant g := by
  exact mul_nonneg (by positivity) (apply_nonneg _ _)

/-- Sixth-order decay estimate used by the Hilbert--Schmidt majorant. -/
theorem ccm_deriv_decay (g : 𝓢(ℝ, ℂ)) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    (1 + x + t) ^ 6 * ‖deriv g (x + t)‖ ≤ ccmDerivativeDecayConstant g := by
  have h := SchwartzMap.one_add_le_sup_seminorm_apply
    (𝕜 := ℂ) (m := (6, 0)) (k := 6) (n := 0) le_rfl le_rfl
      (SchwartzMap.derivCLM ℂ ℂ g) (x + t)
  rw [Real.norm_eq_abs, abs_of_nonneg (add_nonneg hx ht)] at h
  rw [norm_iteratedFDeriv_zero, SchwartzMap.derivCLM_apply] at h
  simpa [ccmDerivativeDecayConstant, add_assoc] using h

/-- Decoupled pointwise majorant for the squared derivative slice. -/
theorem ccmHankelDerivative_pointwise_majorant
    (g : 𝓢(ℝ, ℂ)) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    (1 + t ^ 2) ^ 2 * ‖deriv g (x + t)‖ ^ 2 ≤
      ccmDerivativeDecayConstant g ^ 2 * ((1 + x) ^ 6)⁻¹ * ((1 + t) ^ 2)⁻¹ := by
  let A : ℝ := 1 + x + t
  let X : ℝ := 1 + x
  let T : ℝ := 1 + t
  let q : ℝ := 1 + t ^ 2
  let d : ℝ := ‖deriv g (x + t)‖
  let C : ℝ := ccmDerivativeDecayConstant g
  have hA : 0 < A := by dsimp [A]; linarith
  have hX : 0 < X := by dsimp [X]; linarith
  have hT : 0 < T := by dsimp [T]; linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hd : 0 ≤ d := norm_nonneg _
  have hC : 0 ≤ C := ccmDerivativeDecayConstant_nonneg g
  have hXA : X ≤ A := by dsimp [X, A]; linarith
  have hTA : T ≤ A := by dsimp [T, A]; linarith
  have hqT : q ≤ T ^ 2 := by dsimp [q, T]; nlinarith [sq_nonneg t]
  have hdecay : A ^ 6 * d ≤ C := by
    simpa [A, d, C] using ccm_deriv_decay g hx ht
  have hdecaySq : (A ^ 6 * d) ^ 2 ≤ C ^ 2 :=
    (sq_le_sq₀ (mul_nonneg (pow_nonneg hA.le _) hd) hC).2 hdecay
  have hqSq : q ^ 2 ≤ T ^ 4 := by
    calc
      q ^ 2 ≤ (T ^ 2) ^ 2 := (sq_le_sq₀ hq (sq_nonneg T)).2 hqT
      _ = T ^ 4 := by ring
  have hden : q ^ 2 * (X ^ 6 * T ^ 2) ≤ A ^ 12 := by
    calc
      q ^ 2 * (X ^ 6 * T ^ 2) ≤ T ^ 4 * (X ^ 6 * T ^ 2) := by gcongr
      _ = X ^ 6 * T ^ 6 := by ring
      _ ≤ A ^ 6 * A ^ 6 := by gcongr
      _ = A ^ 12 := by ring
  have hD : 0 < X ^ 6 * T ^ 2 := mul_pos (pow_pos hX _) (pow_pos hT _)
  change q ^ 2 * d ^ 2 ≤ C ^ 2 * (X ^ 6)⁻¹ * (T ^ 2)⁻¹
  rw [show C ^ 2 * (X ^ 6)⁻¹ * (T ^ 2)⁻¹ = C ^ 2 / (X ^ 6 * T ^ 2) by
    field_simp]
  apply (le_div_iff₀ hD).2
  calc
    q ^ 2 * d ^ 2 * (X ^ 6 * T ^ 2) =
        (q ^ 2 * (X ^ 6 * T ^ 2)) * d ^ 2 := by ring
    _ ≤ A ^ 12 * d ^ 2 := by gcongr
    _ = (A ^ 6 * d) ^ 2 := by ring
    _ ≤ C ^ 2 := hdecaySq

theorem ccmHankelDerivative_pointwise_majorant_sq
    (g : 𝓢(ℝ, ℂ)) {x t : ℝ} (hx : 0 ≤ x) (ht : 0 ≤ t) :
    (1 + t ^ 2) ^ 2 * ‖deriv g (x + t)‖ ^ 2 ≤
      ccmDerivativeDecayConstant g ^ 2 * (1 + x ^ 2)⁻¹ * (1 + t ^ 2)⁻¹ := by
  have hbase := ccmHankelDerivative_pointwise_majorant g hx ht
  have hX1 : (1 : ℝ) ≤ 1 + x := by linarith
  have hx2 : 1 + x ^ 2 ≤ (1 + x) ^ 2 := by nlinarith
  have hx6 : (1 + x) ^ 2 ≤ (1 + x) ^ 6 :=
    pow_le_pow_right₀ hX1 (by omega)
  have ht2 : 1 + t ^ 2 ≤ (1 + t) ^ 2 := by nlinarith
  have hxinv : ((1 + x) ^ 6)⁻¹ ≤ (1 + x ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 (hx2.trans hx6)
  have htinv : ((1 + t) ^ 2)⁻¹ ≤ (1 + t ^ 2)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).2 ht2
  exact hbase.trans (by gcongr)

/-- Integrated squared-norm bound for the derivative slice. -/
theorem norm_ccmHankelDerivativeSlice_sq_le (g : 𝓢(ℝ, ℂ)) {t : ℝ} (ht : 0 ≤ t) :
    ‖ccmHankelDerivativeSlice g t‖ ^ 2 ≤
      ccmDerivativeDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ * Real.pi := by
  rw [HTGeometry.norm_l2_sq_eq_integral_norm_sq]
  calc
    (∫ x : ℝ, ‖ccmHankelDerivativeSlice g t x‖ ^ 2) ≤
        ∫ x : ℝ, ccmDerivativeDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ *
          (1 + x ^ 2)⁻¹ := by
      apply integral_mono_ae
      · exact (memLp_two_iff_integrable_sq_norm
          (Lp.aestronglyMeasurable (ccmHankelDerivativeSlice g t))).mp
            (Lp.memLp (ccmHankelDerivativeSlice g t))
      · exact integrable_inv_one_add_sq.const_mul _
      · filter_upwards [ccmHankelDerivativeSlice_coeFn g t] with x hxrep
        rw [hxrep]
        by_cases hx : 0 ≤ x
        · rw [if_pos hx, norm_mul, norm_neg,
            show (1 : ℂ) + (t : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ) by norm_num,
            Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity : 0 ≤ 1 + t ^ 2)]
          simpa only [mul_pow, mul_assoc, mul_left_comm, mul_comm] using
            ccmHankelDerivative_pointwise_majorant_sq g hx ht
        · rw [if_neg hx, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
          positivity
    _ = ccmDerivativeDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ * Real.pi := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]

theorem ccmHankelDerivativeSlice_memLp (g : 𝓢(ℝ, ℂ)) :
    MemLp (ccmHankelDerivativeSlice g) 2 ccmPositiveMeasure := by
  refine (memLp_two_iff_integrable_sq_norm
    (continuous_ccmHankelDerivativeSlice g).aestronglyMeasurable).mpr ?_
  refine Integrable.mono'
    ((integrable_inv_one_add_sq.const_mul
      (ccmDerivativeDecayConstant g ^ 2 * Real.pi)).integrableOn)
    ((continuous_ccmHankelDerivativeSlice g).norm.pow 2).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖ccmHankelDerivativeSlice g t‖)]
  calc
    ‖ccmHankelDerivativeSlice g t‖ ^ 2 ≤
        ccmDerivativeDecayConstant g ^ 2 * (1 + t ^ 2)⁻¹ * Real.pi :=
      norm_ccmHankelDerivativeSlice_sq_le g ht
    _ = (ccmDerivativeDecayConstant g ^ 2 * Real.pi) * (1 + t ^ 2)⁻¹ := by ring

/-- Bochner `L²` field for the derivative synthesis factor. -/
def ccmHankelDerivativeField (g : 𝓢(ℝ, ℂ)) :
    Lp SoninL2 2 ccmPositiveMeasure :=
  (ccmHankelDerivativeSlice_memLp g).toLp (ccmHankelDerivativeSlice g)

/-- Second factor in the Hankel trace-class decomposition. -/
def ccmHankelDerivativeSynthesis (g : 𝓢(ℝ, ℂ)) :
    CCMPositiveL2 →L[ℂ] SoninL2 :=
  l2Synthesis ccmPositiveMeasure (ccmHankelDerivativeField g)

/-- The derivative synthesis factor is genuinely Hilbert--Schmidt. -/
theorem ccmHankelDerivativeSynthesis_isHilbertSchmidt (g : 𝓢(ℝ, ℂ)) :
    (ccmHankelDerivativeSynthesis g).IsHilbertSchmidt :=
  l2Synthesis_isHilbertSchmidt ccmPositiveMeasure (ccmHankelDerivativeField g)

/-! ## Exact Hankel recovery and trace-class conclusion -/

/-- The positive-quadrant Hankel operator furnished by the two explicit factors. -/
def ccmPositiveHankel (g : 𝓢(ℝ, ℂ)) : SoninL2 →L[ℂ] SoninL2 :=
  ccmHankelDerivativeSynthesis g ∘L ccmVolterraObserver

/-- The factorized positive-quadrant Hankel operator is Schatten one. -/
theorem ccmPositiveHankel_memSchattenClass_one (g : 𝓢(ℝ, ℂ)) :
    MemSchattenClass 1 (ccmPositiveHankel g) := by
  rw [← memRectSchattenClass_iff_memSchattenClass]
  exact memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted
    ccmVolterraObserver_isHilbertSchmidt
    (ccmHankelDerivativeSynthesis_isHilbertSchmidt g)

/-- A translated Schwartz derivative integrates from any point to the exact negative endpoint
value.  This is the analytic identity behind the Hankel kernel recovery. -/
theorem integral_neg_deriv_schwartz_tail (g : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    ∫ t in Ioi y, -(deriv g (x + t)) = g (x + y) := by
  have hgTop : Tendsto (g : ℝ → ℂ) atTop (𝓝 0) :=
    (SchwartzMap.tendsto_cocompact g).mono_left atTop_le_cocompact
  have hshiftTop : Tendsto (fun t : ℝ => g (x + t)) atTop (𝓝 0) :=
    hgTop.comp (tendsto_atTop_add_const_left atTop x tendsto_id)
  have hcont : ContinuousWithinAt (fun t : ℝ => g (x + t)) (Ici y) y := by
    fun_prop
  have hderiv : ∀ t ∈ Ioi y,
      HasDerivAt (fun s : ℝ => g (x + s)) (deriv g (x + t)) t := by
    intro t _
    simpa only [add_comm] using HasDerivAt.comp_add_const t x
      (((g.smooth ⊤).differentiable (by simp)).differentiableAt.hasDerivAt)
  have hint : IntegrableOn (fun t : ℝ => deriv g (x + t)) (Ioi y) volume := by
    have hbase : Integrable (fun t : ℝ => deriv g t) volume := by
      exact ((SchwartzMap.derivCLM ℂ ℂ g).integrable :
        Integrable (fun t : ℝ => deriv g t) volume)
    exact (hbase.comp_add_left x).integrableOn
  have hfund := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hshiftTop
  rw [integral_neg, hfund]
  simp

/-- Pairing with the anchored interval vector is exactly integration on that interval. -/
theorem inner_ccmHalfIntervalVec (f : SoninL2) {t : ℝ} (ht : 0 ≤ t) :
    inner ℂ (ccmHalfIntervalVec t) f = ∫ y in Icc 0 t, f y := by
  have hvec : (ccmHalfIntervalVec t : ℝ → ℂ) =ᵐ[volume]
      (Icc 0 t).indicator fun _ => (1 : ℂ) := by
    simpa [ccmHalfIntervalVec, max_eq_left ht] using
      (indicatorConstLp_coeFn :
        ((indicatorConstLp 2 (measurableSet_Icc : MeasurableSet (Icc 0 t))
          (by simp [Real.volume_Icc] : volume (Icc 0 t) ≠ ∞) (1 : ℂ) : SoninL2) :
            ℝ → ℂ) =ᵐ[volume] (Icc 0 t).indicator fun _ => (1 : ℂ))
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ y : ℝ, inner ℂ (ccmHalfIntervalVec t y) (f y)) =
        ∫ y : ℝ, (Icc 0 t).indicator (fun y => f y) y := by
      apply integral_congr_ae
      filter_upwards [hvec] with y hy
      rw [hy]
      by_cases hyt : y ∈ Icc 0 t
      · simp [RCLike.inner_apply, hyt]
      · simp [RCLike.inner_apply, hyt]
    _ = ∫ y in Icc 0 t, f y := integral_indicator measurableSet_Icc

/-- Exact scalar kernel of the weighted Volterra observer vector. -/
theorem inner_ccmVolterraObserverVec (f : SoninL2) {t : ℝ} (ht : 0 ≤ t) :
    inner ℂ (ccmVolterraObserverVec t) f =
      ((1 + t ^ 2)⁻¹ : ℂ) * ∫ y in Icc 0 t, f y := by
  rw [ccmVolterraObserverVec, inner_smul_left, inner_ccmHalfIntervalVec f ht]
  norm_num

/-- Exact almost-everywhere Volterra formula for the first factor. -/
theorem ccmVolterraObserver_coeFn (f : SoninL2) :
    (ccmVolterraObserver f : ℝ → ℂ) =ᵐ[ccmPositiveMeasure]
      fun t => ((1 + t ^ 2)⁻¹ : ℂ) * ∫ y in Icc 0 t, f y := by
  have hanalysis := l2ObserverAnalysis_coeFn ccmPositiveMeasure
    ccmVolterraObserverField f
  have hfield : (ccmVolterraObserverField : ℝ → SoninL2) =ᵐ[ccmPositiveMeasure]
      ccmVolterraObserverVec := by
    simpa [ccmVolterraObserverField] using ccmVolterraObserverVec_memLp.coeFn_toLp
  filter_upwards [hanalysis, hfield, ae_restrict_mem measurableSet_Ici] with t ht hf htpos
  rw [ccmVolterraObserver, ht, hf, inner_ccmVolterraObserverVec f htpos]

/-- **Exact Hankel-kernel factorization.**  For every pair of source coordinates, integrating the
two factor kernels over their common Volterra ray gives the literal source kernel `g(x+y)`.
This is the non-surrogate bridge from the Hilbert--Schmidt factorization to `quantsmooth`. -/
theorem ccmHankel_kernel_factorization (g : 𝓢(ℝ, ℂ)) (x y : ℝ) :
    (∫ t in Ici y,
      (-(1 + t ^ 2 : ℂ) * deriv g (x + t)) * ((1 + t ^ 2)⁻¹ : ℂ)) =
        g (x + y) := by
  rw [integral_Ici_eq_integral_Ioi]
  calc
    (∫ t in Ioi y,
        (-(1 + t ^ 2 : ℂ) * deriv g (x + t)) * ((1 + t ^ 2)⁻¹ : ℂ)) =
        ∫ t in Ioi y, -(deriv g (x + t)) := by
      apply integral_congr_ae
      filter_upwards with t
      have ht : (1 + t ^ 2 : ℂ) ≠ 0 := by
        exact_mod_cast (by positivity : (1 + t ^ 2 : ℝ) ≠ 0)
      field_simp
    _ = g (x + y) := integral_neg_deriv_schwartz_tail g x y

/-- Exact weak kernel of the derivative synthesis slice. -/
theorem inner_ccmHankelDerivativeSlice (g : 𝓢(ℝ, ℂ)) (h : SoninL2) (t : ℝ) :
    inner ℂ h (ccmHankelDerivativeSlice g t) =
      ∫ x in Ici 0, (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x) := by
  rw [MeasureTheory.L2.inner_def]
  calc
    (∫ x : ℝ, inner ℂ (h x) (ccmHankelDerivativeSlice g t x)) =
        ∫ x : ℝ, (Ici 0).indicator
          (fun x => (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x)) x := by
      apply integral_congr_ae
      filter_upwards [ccmHankelDerivativeSlice_coeFn g t] with x hx
      rw [hx]
      by_cases hxp : 0 ≤ x
      · simp [RCLike.inner_apply, hxp]
      · simp [RCLike.inner_apply, hxp]
    _ = ∫ x in Ici 0,
        (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x) :=
      integral_indicator measurableSet_Ici

/-- Exact weak factorization formula for the positive Hankel operator. -/
theorem inner_ccmPositiveHankel (g : 𝓢(ℝ, ℂ)) (f h : SoninL2) :
    inner ℂ h (ccmPositiveHankel g f) =
      ∫ t, (ccmVolterraObserver f t) *
        inner ℂ h (ccmHankelDerivativeSlice g t) ∂ccmPositiveMeasure := by
  have hint : Integrable (fun t =>
      ccmVolterraObserver f t • ccmHankelDerivativeField g t) ccmPositiveMeasure := by
    exact memLp_one_iff_integrable.mp
      ((Lp.memLp (ccmHankelDerivativeField g)).smul (Lp.memLp (ccmVolterraObserver f)))
  have hfield : (ccmHankelDerivativeField g : ℝ → SoninL2) =ᵐ[ccmPositiveMeasure]
      ccmHankelDerivativeSlice g := by
    simpa [ccmHankelDerivativeField] using
      (ccmHankelDerivativeSlice_memLp g).coeFn_toLp
  rw [ccmPositiveHankel, ContinuousLinearMap.comp_apply,
    ccmHankelDerivativeSynthesis, l2Synthesis_apply]
  calc
    inner ℂ h (∫ t, ccmVolterraObserver f t • ccmHankelDerivativeField g t
        ∂ccmPositiveMeasure) =
        ∫ t, inner ℂ h
          (ccmVolterraObserver f t • ccmHankelDerivativeField g t)
          ∂ccmPositiveMeasure :=
      (integral_inner (𝕜 := ℂ) hint h).symm
    _ = ∫ t, (ccmVolterraObserver f t) *
        inner ℂ h (ccmHankelDerivativeSlice g t) ∂ccmPositiveMeasure := by
      apply integral_congr_ae
      filter_upwards [hfield] with t ht
      rw [ht, inner_smul_right]

/-- Expanded weak integral formula exposing both Hilbert--Schmidt kernels. -/
theorem inner_ccmPositiveHankel_integral (g : 𝓢(ℝ, ℂ)) (f h : SoninL2) :
    inner ℂ h (ccmPositiveHankel g f) =
      ∫ t,
        (((1 + t ^ 2)⁻¹ : ℂ) * ∫ y in Icc 0 t, f y) *
          (∫ x in Ici 0,
            (-(1 + t ^ 2) * deriv g (x + t)) * starRingEnd ℂ (h x))
        ∂ccmPositiveMeasure := by
  rw [inner_ccmPositiveHankel]
  apply integral_congr_ae
  filter_upwards [ccmVolterraObserver_coeFn f,
    ae_restrict_mem measurableSet_Ici] with t ht htpos
  rw [ht, inner_ccmHankelDerivativeSlice]

end RHTower
