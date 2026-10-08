import GaloisForLFunctions.RHTower.WeilPaperMixtureRealification
import GaloisForLFunctions.RHTower.WeilPaperPacketRealification

/-!
# Full energy survives complex-null realification

Reflection preserves the pole-plus-gamma functional for every complex kernel.
Consequently, conjugation averaging preserves the full energy of every finite
Weil mixture. The normalized integer-defect-null and complex-null cones have
exactly the same attainable energies.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Reflection reverses the complex Fourier parameter. -/
theorem paperFT_reflect_complex (f : ℝ → ℂ) (z : ℂ) :
    paperFT (fun x => f (-x)) z = paperFT f (-z) := by
  unfold paperFT
  have h : (fun x : ℝ => f (-x) * Complex.exp (I * z * x)) =
      fun x : ℝ => (fun y : ℝ => f y * Complex.exp (I * (-z) * y)) (-x) := by
    funext x
    congr 1
    congr 1
    push_cast
    ring
  rw [h, integral_neg_eq_self (fun y : ℝ => f y * Complex.exp (I * (-z) * y))]

/-- Reflection exchanges the two pole terms and preserves the gamma integral. -/
theorem weilArchRe_reflect (f : ℝ → ℂ) :
    weilArchRe (fun x => f (-x)) = weilArchRe f := by
  have hint : (∫ r : ℝ, paperFT f (-(r : ℂ)) * (EF.gammaBracket r : ℂ)) =
      ∫ r : ℝ, paperFT f r * (EF.gammaBracket r : ℂ) := by
    simpa only [Complex.ofReal_neg, packet_gammaBracket_neg] using
      integral_neg_eq_self (fun r : ℝ => paperFT f r * (EF.gammaBracket r : ℂ)) volume
  simp only [weilArchRe, paperFT_reflect_complex, hint, neg_div, neg_neg, add_comm]

/-- A test and its conjugate have identical full energy. -/
theorem weilArchRe_paperConjugateTestFn (f : WeilTestFn) :
    weilArchRe (EF.weilTest (paperConjugateTestFn f).1 (paperConjugateTestFn f).1) =
      weilArchRe (EF.weilTest f.1 f.1) := by
  have h : EF.weilTest (paperConjugateTestFn f).1 (paperConjugateTestFn f).1 =
      fun y => EF.weilTest f.1 f.1 (-y) := by
    funext y
    rw [weilTest_paperConjugateTestFn, weilTest_self_neg]
  rw [h, weilArchRe_reflect]

/-- Conjugation averaging preserves full energy, including for signed mixtures. -/
theorem energy_paperRealMixture (c : WeilTestFn →₀ ℝ) :
    energy (paperRealMixture c) = energy c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single f r =>
    simp only [paperRealMixture, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.id_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      map_smul, map_add, energy, Finsupp.linearCombination_single,
      weilArchRe_paperConjugateTestFn, smul_eq_mul]
    ring

theorem energy_paperRealComplexNullMixture
    (c : {c : NormalizedMixture // defect c.1 = 0}) :
    energy (paperRealComplexNullMixture c).1.1 = energy c.1.1 :=
  energy_paperRealMixture c.1.1

/-- Full complex integer cancellation implies all original real integer defects vanish. -/
theorem defect_complexNullMixture (c : ComplexNullMixture) : defect c.1.1 = 0 := by
  ext j
  rw [defect_eq_mixtureSample_re, c.2 j j.property]
  simp

/-- The two normalized cones have exactly the same attainable full-energy values. -/
theorem attainable_energy_real_null_eq_complex_null :
    {e : ℝ | ∃ c : NormalizedMixture, defect c.1 = 0 ∧ energy c.1 = e} =
      {e : ℝ | ∃ c : ComplexNullMixture, energy c.1.1 = e} := by
  ext e
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨paperRealComplexNullMixture ⟨c, hc⟩,
      (energy_paperRealComplexNullMixture ⟨c, hc⟩).trans he⟩
  · rintro ⟨c, he⟩
    exact ⟨c.1, defect_complexNullMixture c, he⟩

/-- Searching for negative full energy loses nothing by imposing full complex cancellation. -/
theorem exists_negative_energy_real_null_iff_complex_null :
    (∃ c : NormalizedMixture, defect c.1 = 0 ∧ energy c.1 < 0) ↔
      ∃ c : ComplexNullMixture, energy c.1.1 < 0 := by
  constructor
  · rintro ⟨c, hc, he⟩
    exact ⟨paperRealComplexNullMixture ⟨c, hc⟩,
      (energy_paperRealComplexNullMixture ⟨c, hc⟩).symm ▸ he⟩
  · rintro ⟨c, he⟩
    exact ⟨c.1, defect_complexNullMixture c, he⟩

end RHTower.WeilWorkPBAP
