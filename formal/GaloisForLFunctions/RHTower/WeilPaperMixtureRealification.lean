import GaloisForLFunctions.RHTower.WeilPaperPacketNormalizedSeparation

/-!
# Positive realification of finite Weil mixtures

Conjugation averaging is a positive real linear operation. It preserves mass
and real correlations, and turns the integer defect kernel into full complex
integer cancellation. This supplies actual representing spectral probabilities.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Complex conjugation preserves the native compact C² test space. -/
def paperConjugateTestFn (f : WeilTestFn) : WeilTestFn :=
  ⟨fun x => conj (f.1 x), Complex.conjCLE.contDiff.comp f.2.1,
    f.2.2.comp_left (map_zero _)⟩

theorem weilTest_paperConjugateTestFn (f : WeilTestFn) (y : ℝ) :
    EF.weilTest (paperConjugateTestFn f).1 (paperConjugateTestFn f).1 y =
      conj (EF.weilTest f.1 f.1 y) := by
  rw [weilTest_apply, weilTest_apply, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by simp [paperConjugateTestFn]

/-- Average each test with its conjugate, retaining nonnegative mixture weights. -/
def paperRealMixture : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ) :=
  (1 / 2 : ℝ) • (LinearMap.id + Finsupp.lmapDomain ℝ ℝ paperConjugateTestFn)

theorem paperRealMixture_nonneg (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) :
    ∀ f, 0 ≤ paperRealMixture c f := by
  have hd : 0 ≤ Finsupp.mapDomain paperConjugateTestFn c := Finsupp.mapDomain_nonneg hc
  intro f
  exact mul_nonneg (by positivity : (0 : ℝ) ≤ 1 / 2) (add_nonneg (hc f) (hd f))

/-- Every autocorrelation becomes exactly its real part. -/
theorem mixtureSample_paperRealMixture (c : WeilTestFn →₀ ℝ) (y : ℝ) :
    mixtureSample (paperRealMixture c) y = ((mixtureSample c y).re : ℂ) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [mixtureSample]
  | add a b ha hb =>
    simp only [mixtureSample] at ha hb ⊢
    simp only [map_add, ha, hb, Complex.add_re, Complex.ofReal_add]
  | single f r =>
    simp only [paperRealMixture, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.id_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      mixtureSample, map_smul, map_add, Finsupp.linearCombination_single,
      weilTest_paperConjugateTestFn, Complex.real_smul]
    apply Complex.ext <;> simp; ring

/-- Integer defects are precisely scaled real integer autocorrelations. -/
theorem defect_eq_mixtureSample_re (c : WeilTestFn →₀ ℝ) (j : LogIndex) :
    defect c j = 2 * (mixtureSample c (Real.log (j : ℕ))).re / Real.sqrt (j : ℕ) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [mixtureSample]
  | add a b ha hb =>
    simp only [map_add, Finsupp.add_apply, ha, hb, mixtureSample, map_add, Complex.add_re]
    ring
  | single f r =>
    simp only [defect, Finsupp.linearCombination_single, Finsupp.smul_apply,
      smul_eq_mul, logVector_apply, logValue, weilTest_self_neg, Complex.add_re,
      Complex.conj_re, mixtureSample, Finsupp.linearCombination_single,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring

/-- Realification preserves every original integer defect. -/
theorem defect_paperRealMixture (c : WeilTestFn →₀ ℝ) :
    defect (paperRealMixture c) = defect c := by
  ext j
  simp only [defect_eq_mixtureSample_re, mixtureSample_paperRealMixture, Complex.ofReal_re]

/-- Mass is already real, so conjugation averaging preserves it exactly. -/
theorem mixtureSample_paperRealMixture_zero (c : WeilTestFn →₀ ℝ) :
    mixtureSample (paperRealMixture c) 0 = mixtureSample c 0 := by
  rw [mixtureSample_paperRealMixture, mixtureSample_zero_eq_integral_density,
    Complex.ofReal_re]

/-- All real integer defects vanish exactly when the realified complex samples vanish. -/
theorem defect_eq_zero_iff_paperRealMixture_complex_null (c : WeilTestFn →₀ ℝ) :
    defect c = 0 ↔ ∀ n : ℕ, 2 ≤ n → mixtureSample (paperRealMixture c) (Real.log n) = 0 := by
  constructor
  · intro hc n hn
    have h := congrArg (fun v : LogIndex →₀ ℝ => v ⟨n, hn⟩) hc
    rw [defect_eq_mixtureSample_re] at h
    have hr : (mixtureSample c (Real.log n)).re = 0 := by
      have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
      simp only [Finsupp.zero_apply, div_eq_zero_iff, hs, or_false, mul_eq_zero,
        OfNat.ofNat_ne_zero, false_or] at h
      exact h
    rw [mixtureSample_paperRealMixture, hr, Complex.ofReal_zero]
  · intro hc
    ext j
    have h := congrArg Complex.re (hc j j.property)
    rw [mixtureSample_paperRealMixture, Complex.ofReal_re, Complex.zero_re] at h
    rw [defect_eq_mixtureSample_re, h, mul_zero, zero_div, Finsupp.zero_apply]

/-- Realification acts on the native normalized positive mixtures. -/
def paperRealNormalizedMixture (c : NormalizedMixture) : NormalizedMixture :=
  ⟨paperRealMixture c.1, paperRealMixture_nonneg c.1 c.2.1,
    (mixtureSample_paperRealMixture_zero c.1).trans c.2.2⟩

/-- An integer-defect-null probability has a canonical full-complex-null realization. -/
def paperRealComplexNullMixture (c : {c : NormalizedMixture // defect c.1 = 0}) :
    ComplexNullMixture :=
  ⟨paperRealNormalizedMixture c.1,
    (defect_eq_zero_iff_paperRealMixture_complex_null c.1.1).mp c.2⟩

end RHTower.WeilWorkPBAP
