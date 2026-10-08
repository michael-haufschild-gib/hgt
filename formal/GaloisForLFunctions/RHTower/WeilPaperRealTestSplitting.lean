import GaloisForLFunctions.RHTower.WeilPaperMixtureKernelEnergy
import GaloisForLFunctions.RHTower.WeilFullConePolarizedRepresentation

/-!
# Real-valued test mixtures suffice for full-energy search

Split every native complex test into its real and imaginary parts. The resulting
positive mixture uses only real-valued tests, has the real part of the original
autocorrelation, and preserves mass, integer defects, and full energy exactly.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided WeilSpectral

/-- Real part, viewed in the native complex-valued compact C² test space. -/
def paperRealPartTestFn (f : WeilTestFn) : WeilTestFn :=
  ⟨fun x => ((f.1 x).re : ℂ),
    Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.comp f.2.1),
    f.2.2.comp_left (g := fun z : ℂ => (z.re : ℂ)) (by simp)⟩

/-- Imaginary part, viewed as a real-valued native test. -/
def paperImagPartTestFn (f : WeilTestFn) : WeilTestFn :=
  ⟨fun x => ((f.1 x).im : ℂ),
    Complex.ofRealCLM.contDiff.comp (Complex.imCLM.contDiff.comp f.2.1),
    f.2.2.comp_left (g := fun z : ℂ => (z.im : ℂ)) (by simp)⟩

/-- Real and imaginary autocorrelations add to the real original autocorrelation. -/
theorem weilTest_real_imag_split (f : WeilTestFn) (y : ℝ) :
    EF.weilTest (paperRealPartTestFn f).1 (paperRealPartTestFn f).1 y +
      EF.weilTest (paperImagPartTestFn f).1 (paperImagPartTestFn f).1 y =
        ((EF.weilTest f.1 f.1 y).re : ℂ) := by
  have hr := integrable_mul_conj_shift (paperRealPartTestFn f).2.1.continuous
    (paperRealPartTestFn f).2.2 (paperRealPartTestFn f).2.1.continuous y
  have hi := integrable_mul_conj_shift (paperImagPartTestFn f).2.1.continuous
    (paperImagPartTestFn f).2.2 (paperImagPartTestFn f).2.1.continuous y
  have hf := integrable_mul_conj_shift f.2.1.continuous f.2.2 f.2.1.continuous y
  have hre : (∫ x : ℝ, (f.1 x * conj (f.1 (x - y))).re) =
      (∫ x : ℝ, f.1 x * conj (f.1 (x - y))).re :=
    Complex.reCLM.integral_comp_comm hf
  rw [weilTest_apply, weilTest_apply, weilTest_apply, ← integral_add hr hi,
    ← hre, ← integral_complex_ofReal]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp [paperRealPartTestFn, paperImagPartTestFn, Complex.mul_re]

/-- Split each coefficient between its real and imaginary test parts. -/
def paperSplitRealMixture : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (WeilTestFn →₀ ℝ) :=
  Finsupp.lmapDomain ℝ ℝ paperRealPartTestFn + Finsupp.lmapDomain ℝ ℝ paperImagPartTestFn

theorem paperSplitRealMixture_nonneg (c : WeilTestFn →₀ ℝ) (hc : ∀ f, 0 ≤ c f) :
    ∀ f, 0 ≤ paperSplitRealMixture c f := by
  intro f
  exact add_nonneg (Finsupp.mapDomain_nonneg hc f) (Finsupp.mapDomain_nonneg hc f)

/-- Every surviving test in the split mixture is real-valued. -/
theorem paperSplitRealMixture_real (c : WeilTestFn →₀ ℝ) (f : WeilTestFn)
    (hf : paperSplitRealMixture c f ≠ 0) (y : ℝ) : (f.1 y).im = 0 := by
  classical
  by_contra h
  have hr : f ∉ Set.range paperRealPartTestFn := by
    rintro ⟨g, rfl⟩
    exact h (by simp [paperRealPartTestFn])
  have hi : f ∉ Set.range paperImagPartTestFn := by
    rintro ⟨g, rfl⟩
    exact h (by simp [paperImagPartTestFn])
  apply hf
  change Finsupp.mapDomain paperRealPartTestFn c f +
    Finsupp.mapDomain paperImagPartTestFn c f = 0
  rw [Finsupp.mapDomain_notin_range c f hr, Finsupp.mapDomain_notin_range c f hi, add_zero]

/-- Splitting discards precisely the imaginary part of the aggregate autocorrelation. -/
theorem mixtureSample_paperSplitRealMixture (c : WeilTestFn →₀ ℝ) (y : ℝ) :
    mixtureSample (paperSplitRealMixture c) y = ((mixtureSample c y).re : ℂ) := by
  induction c using Finsupp.induction_linear with
  | zero => simp [mixtureSample]
  | add a b ha hb =>
    simp only [mixtureSample] at ha hb ⊢
    simp only [map_add, ha, hb, Complex.add_re, Complex.ofReal_add]
  | single f r =>
    simp only [paperSplitRealMixture, LinearMap.add_apply, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single, mixtureSample, map_add, Finsupp.linearCombination_single,
      Complex.real_smul]
    rw [← mul_add, weilTest_real_imag_split]
    simp

theorem mixtureSample_paperSplitRealMixture_eq_realification (c : WeilTestFn →₀ ℝ) :
    mixtureSample (paperSplitRealMixture c) = mixtureSample (paperRealMixture c) := by
  funext y
  rw [mixtureSample_paperSplitRealMixture, mixtureSample_paperRealMixture]

/-- Splitting preserves autocorrelation mass, even for signed mixtures. -/
theorem mixtureSample_paperSplitRealMixture_zero (c : WeilTestFn →₀ ℝ) :
    mixtureSample (paperSplitRealMixture c) 0 = mixtureSample c 0 := by
  rw [mixtureSample_paperSplitRealMixture_eq_realification, mixtureSample_paperRealMixture_zero]

theorem defect_paperSplitRealMixture (c : WeilTestFn →₀ ℝ) :
    defect (paperSplitRealMixture c) = defect c := by
  ext j
  simp only [defect_eq_mixtureSample_re, mixtureSample_paperSplitRealMixture, Complex.ofReal_re]

theorem energy_paperSplitRealMixture (c : WeilTestFn →₀ ℝ) :
    energy (paperSplitRealMixture c) = energy c := by
  exact (energy_eq_of_mixtureSample_eq _ _
    (mixtureSample_paperSplitRealMixture_eq_realification c)).trans (energy_paperRealMixture c)

/-- Splitting preserves positivity and unit autocorrelation mass. -/
def paperSplitRealNormalizedMixture (c : NormalizedMixture) : NormalizedMixture :=
  ⟨paperSplitRealMixture c.1, paperSplitRealMixture_nonneg c.1 c.2.1, by
    rw [mixtureSample_paperSplitRealMixture, c.2.2]
    simp⟩

/-- A real-defect-null mixture has a canonical complex-null version with real-valued tests. -/
def paperSplitRealComplexNullMixture (c : {c : NormalizedMixture // defect c.1 = 0}) :
    ComplexNullMixture :=
  ⟨paperSplitRealNormalizedMixture c.1, by
    intro n hn
    change mixtureSample (paperSplitRealMixture c.1.1) (Real.log n) = 0
    rw [mixtureSample_paperSplitRealMixture_eq_realification]
    exact (defect_eq_zero_iff_paperRealMixture_complex_null c.1.1).mp c.2 n hn⟩

/-- All attainable full energies can be realized by complex-null mixtures of real tests. -/
theorem attainable_energy_eq_real_test_complex_null :
    {e : ℝ | ∃ c : NormalizedMixture, defect c.1 = 0 ∧ energy c.1 = e} =
      {e : ℝ | ∃ c : ComplexNullMixture, energy c.1.1 = e ∧
        ∀ f, c.1.1 f ≠ 0 → ∀ y, (f.1 y).im = 0} := by
  ext e
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨paperSplitRealComplexNullMixture ⟨c, hc⟩,
      (energy_paperSplitRealMixture c.1).trans he, paperSplitRealMixture_real c.1⟩
  · rintro ⟨c, he, _⟩
    exact ⟨c.1, defect_complexNullMixture c, he⟩

/-- Any negative-energy search can be restricted to real-valued tests and complex cancellation. -/
theorem exists_negative_energy_iff_real_test_complex_null :
    (∃ c : NormalizedMixture, defect c.1 = 0 ∧ energy c.1 < 0) ↔
      ∃ c : ComplexNullMixture, energy c.1.1 < 0 ∧
        ∀ f, c.1.1 f ≠ 0 → ∀ y, (f.1 y).im = 0 := by
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨paperSplitRealComplexNullMixture ⟨c, hc⟩,
      (energy_paperSplitRealMixture c.1).symm ▸ he, paperSplitRealMixture_real c.1⟩
  · rintro ⟨c, he, _⟩
    exact ⟨c.1, defect_complexNullMixture c, he⟩

end RHTower.WeilWorkPBAP
