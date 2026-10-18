import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic

/-!
# Squarefree incidence against Gaussian moment growth

A summable nonnegative incidence weight has finite-support products of arbitrarily small
exponential type. Splitting off a finite head is essential: the bound using the full trace
would restrict the formation parameter to a fixed disk.

This supplies simultaneous Hilbert admission of all squarefree compounds against one Gaussian
moment envelope. Complex coefficients are retained pointwise; no cancellation or phase erasure
is used. The Gamma--theta specialization uses the literal unbounded Mellin grade.
-/

open Filter MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

/-- A summable incidence family has arbitrarily small exponential type, uniformly over every
finite support. The finite head contributes only a constant. -/
theorem exists_squarefree_product_exp_bound {ι : Type*}
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset ι) (u : ℝ), 0 ≤ u →
      (∏ i ∈ S, (1 + b i * u)) ≤ C * Real.exp (c * u) := by
  classical
  obtain ⟨H, hH⟩ := (hs.hasSum.eventually
    (lt_mem_nhds (show (∑' i, b i) - c / 2 < ∑' i, b i by linarith))).exists
  have htail (T : Finset ι) (hT : Disjoint H T) : ∑ i ∈ T, b i ≤ c / 2 := by
    have hsum := hs.sum_le_tsum (H ∪ T) (fun i _ => hb i)
    rw [Finset.sum_union hT] at hsum
    linarith
  let d : ℝ := c / (2 * ((H.card : ℝ) + 1))
  have hd : 0 < d := by dsimp [d]; positivity
  have hdcard : (H.card : ℝ) * d ≤ c / 2 := by
    have heq : d * ((H.card : ℝ) + 1) = c / 2 := by
      dsimp [d]
      field_simp
    nlinarith
  let C : ℝ := ∏ i ∈ H, (1 + b i / d)
  have hC : 0 < C := Finset.prod_pos fun i _ => by
    have := div_nonneg (hb i) hd.le
    linarith
  refine ⟨C, hC, fun S u hu => ?_⟩
  have hfactor (i : ι) :
      1 + b i * u ≤ (1 + b i / d) * Real.exp (d * u) := by
    have h1 : 1 ≤ Real.exp (d * u) := Real.one_le_exp_iff.mpr (mul_nonneg hd.le hu)
    have hu' : u ≤ Real.exp (d * u) / d := by
      apply (le_div_iff₀ hd).mpr
      have := Real.add_one_le_exp (d * u)
      nlinarith
    calc
      1 + b i * u ≤ Real.exp (d * u) + b i * (Real.exp (d * u) / d) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left hu' (hb i))
      _ = (1 + b i / d) * Real.exp (d * u) := by ring
  have hhead : (∏ i ∈ H, (1 + b i * u)) ≤ C * Real.exp (c / 2 * u) := by
    calc
      (∏ i ∈ H, (1 + b i * u)) ≤
          ∏ i ∈ H, ((1 + b i / d) * Real.exp (d * u)) :=
        Finset.prod_le_prod (fun i _ => add_nonneg zero_le_one (mul_nonneg (hb i) hu))
          (fun i _ => hfactor i)
      _ = C * Real.exp ((H.card : ℝ) * (d * u)) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_nat_mul]
      _ ≤ C * Real.exp (c / 2 * u) := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_right hdcard hu]
  have hdisj : Disjoint H (S \ H) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    exact (Finset.mem_sdiff.mp hj).2 hi
  have htailProd : (∏ i ∈ S \ H, (1 + b i * u)) ≤ Real.exp (c / 2 * u) := by
    calc
      (∏ i ∈ S \ H, (1 + b i * u)) ≤ Real.exp (∑ i ∈ S \ H, b i * u) :=
        Real.prod_one_add_le_exp_sum _ (fun i => mul_nonneg (hb i) hu)
      _ ≤ Real.exp (c / 2 * u) := by
        rw [← Finset.sum_mul]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (htail _ hdisj) hu)
  calc
    (∏ i ∈ S, (1 + b i * u)) ≤ ∏ i ∈ H ∪ (S \ H), (1 + b i * u) := by
      apply Finset.prod_le_prod_of_subset_of_one_le
      · intro i hi
        by_cases hiH : i ∈ H
        · exact Finset.mem_union_left _ hiH
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hi, hiH⟩)
      · intro i _; have := mul_nonneg (hb i) hu; linarith
      · intro i _ _; have := mul_nonneg (hb i) hu; linarith
    _ = (∏ i ∈ H, (1 + b i * u)) * ∏ i ∈ S \ H, (1 + b i * u) :=
      Finset.prod_union hdisj
    _ ≤ (C * Real.exp (c / 2 * u)) * Real.exp (c / 2 * u) :=
      mul_le_mul hhead htailProd
        (Finset.prod_nonneg fun i _ => add_nonneg zero_le_one (mul_nonneg (hb i) hu))
        (by positivity)
    _ = C * Real.exp (c * u) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Gaussian control of one scalar moment variable admits every squarefree incidence compound.
The conclusion ranges over all finite supports, not a prescribed cutoff sequence. -/
theorem summable_integral_squarefree_products {ι Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    (u w : Ω → ℝ) (hu : Measurable u) (hw : Measurable w)
    (hu0 : ∀ x, 0 ≤ u x) (hw0 : ∀ x, 0 ≤ w x)
    {c : ℝ} (hc : 0 < c) (hG : Integrable (fun x => Real.exp (c * u x) * w x) μ) :
    Summable (fun P : Finset ι => ∫ x, (∏ i ∈ P, (b i * u x)) * w x ∂μ) := by
  classical
  obtain ⟨C, hC, hbound⟩ := exists_squarefree_product_exp_bound b hb hs hc
  have hnonneg (P : Finset ι) (x : Ω) : 0 ≤ (∏ i ∈ P, (b i * u x)) * w x :=
    mul_nonneg (Finset.prod_nonneg fun i _ => mul_nonneg (hb i) (hu0 x)) (hw0 x)
  have hint (P : Finset ι) : Integrable (fun x => (∏ i ∈ P, (b i * u x)) * w x) μ := by
    have hm : Measurable (fun x => (∏ i ∈ P, (b i * u x)) * w x) := by fun_prop
    apply (hG.const_mul C).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg P x)]
      calc
        (∏ i ∈ P, (b i * u x)) * w x ≤ (∏ i ∈ P, (1 + b i * u x)) * w x :=
          mul_le_mul_of_nonneg_right (Finset.prod_le_prod
            (fun i _ => mul_nonneg (hb i) (hu0 x)) (fun i _ => by linarith)) (hw0 x)
        _ ≤ C * Real.exp (c * u x) * w x :=
          mul_le_mul_of_nonneg_right (hbound P (u x) (hu0 x)) (hw0 x)
        _ = C * (Real.exp (c * u x) * w x) := by ring
  apply summable_of_sum_le (c := C * ∫ x, Real.exp (c * u x) * w x ∂μ)
    (fun P => integral_nonneg (hnonneg P))
  intro T
  rw [← integral_finsetSum T (fun P _ => hint P), ← integral_const_mul]
  apply integral_mono (integrable_finsetSum T (fun P _ => hint P)) (hG.const_mul C)
  intro x
  dsimp only
  rw [← Finset.sum_mul]
  have hsum : (∑ P ∈ T, ∏ i ∈ P, (b i * u x)) ≤
      ∏ i ∈ T.biUnion id, (1 + b i * u x) := by
    rw [Finset.prod_one_add]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro P hP
      exact Finset.mem_powerset.mpr (Finset.subset_biUnion_of_mem id hP)
    · intro P _ _
      exact Finset.prod_nonneg fun i _ => mul_nonneg (hb i) (hu0 x)
  calc
    (∑ P ∈ T, ∏ i ∈ P, (b i * u x)) * w x ≤
        (∏ i ∈ T.biUnion id, (1 + b i * u x)) * w x :=
      mul_le_mul_of_nonneg_right hsum (hw0 x)
    _ ≤ (C * Real.exp (c * u x)) * w x :=
      mul_le_mul_of_nonneg_right (hbound _ _ (hu0 x)) (hw0 x)
    _ = C * (Real.exp (c * u x) * w x) := by ring

/-- A coefficient-faithful complex family dominated by squarefree Gaussian moments belongs to
the counting-measure product Hilbert space. -/
theorem memLp_squarefree_gaussian_majorant {ι Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]
    {μ : Measure Ω} [SFinite μ]
    (b : ι → ℝ) (hb : ∀ i, 0 ≤ b i) (hs : Summable b)
    (u w : Ω → ℝ) (hu : Measurable u) (hw : Measurable w)
    (hu0 : ∀ x, 0 ≤ u x) (hw0 : ∀ x, 0 ≤ w x)
    {c : ℝ} (hc : 0 < c) (hG : Integrable (fun x => Real.exp (c * u x) * w x) μ)
    (f : Finset ι × Ω → ℂ) (hf : Measurable f)
    (hfbound : ∀ P x, ‖f (P, x)‖ ^ 2 ≤ (∏ i ∈ P, (b i * u x)) * w x) :
    MemLp f 2 (Measure.count.prod μ) := by
  classical
  have hsum := summable_integral_squarefree_products b hb hs u w hu hw hu0 hw0 hc hG
  obtain ⟨C, hC, hbound⟩ := exists_squarefree_product_exp_bound b hb hs hc
  have hmajor (P : Finset ι) : Integrable (fun x => (∏ i ∈ P, (b i * u x)) * w x) μ := by
    have hm : Measurable (fun x => (∏ i ∈ P, (b i * u x)) * w x) := by fun_prop
    apply (hG.const_mul C).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
        (Finset.prod_nonneg fun i _ => mul_nonneg (hb i) (hu0 x)) (hw0 x))]
      have hp := Finset.prod_le_prod (s := P)
        (fun i _ => mul_nonneg (hb i) (hu0 x)) (fun i _ => le_add_of_nonneg_left zero_le_one)
      calc
        (∏ i ∈ P, (b i * u x)) * w x ≤ (∏ i ∈ P, (1 + b i * u x)) * w x :=
          mul_le_mul_of_nonneg_right hp (hw0 x)
        _ ≤ C * (Real.exp (c * u x) * w x) := by
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
            (hbound P (u x) (hu0 x)) (hw0 x)
  have hint (P : Finset ι) : Integrable (fun x => ‖f (P, x)‖ ^ 2) μ := by
    have hm : Measurable (fun x => ‖f (P, x)‖ ^ 2) := by fun_prop
    apply (hmajor P).mono' hm.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hfbound P x
  have hsquare : Summable (fun P : Finset ι => ∫ x, ‖f (P, x)‖ ^ 2 ∂μ) :=
    hsum.of_nonneg_of_le (fun P => integral_nonneg fun x => sq_nonneg _)
      (fun P => integral_mono (hint P) (hmajor P) (hfbound P))
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  apply (integrable_prod_iff (hf.norm.pow_const 2).aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall hint, integrable_count_iff.mpr ?_⟩
  apply hsquare.congr
  intro P
  simp only [Real.norm_eq_abs, abs_sq]
  rw [abs_of_nonneg (integral_nonneg fun x => sq_nonneg ‖f (P, x)‖)]

end

end GaloisForLFunctions.BiScaleUncertainty
