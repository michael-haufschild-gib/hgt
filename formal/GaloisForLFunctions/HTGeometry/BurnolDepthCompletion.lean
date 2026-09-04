import GaloisForLFunctions.HTGeometry.LocalExponentialTestClosure
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# One-depth-tower completeness and two-clock graph saturation

The geometric Burnol features `t * exp (-(n+1) * ell * t)` span the entire physical
half-line L² space for every positive `ell`.  The proof uses bounded injective
moment coordinates and the corpus's local-exponential measure determinacy.
Nonzero unsquared source amplitudes preserve this span.  Prescribing unequal
constant scalars on two towers makes the completed output relation the whole
product; equal scalars give exactly their ordinary graph.

This is the density and scalar-relation part of ULF-BFCC-001.  It neither
identifies a theta completion nor proves an RH admission hypothesis.
-/

open MeasureTheory Filter Set ProbabilityTheory

namespace HTGeometry

private theorem boundedCoordinate_window {ν : Measure ℝ} [IsFiniteMeasure ν]
    {φ : ℝ → ℝ} (hφ : MeasurableEmbedding φ)
    (hbound : ∀ᵐ x ∂ν, |φ x| ≤ 1) :
    Set.Ioo (-1 : ℝ) 1 ⊆ integrableExpSet id (Measure.map φ ν) := by
  intro t _
  change Integrable (fun x : ℝ => Real.exp (t * x)) (Measure.map φ ν)
  apply hφ.integrable_map_iff.mpr
  apply (integrable_const (Real.exp |t|)).mono'
    ((Real.continuous_exp.measurable.comp
      (measurable_const.mul hφ.measurable)).aestronglyMeasurable)
  filter_upwards [hbound] with x hx
  change ‖Real.exp (t * φ x)‖ ≤ Real.exp |t|
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * φ x ≤ |t * φ x| := le_abs_self _
    _ = |t| * |φ x| := abs_mul _ _
    _ ≤ |t| * 1 := mul_le_mul_of_nonneg_left hx (abs_nonneg _)
    _ = |t| := mul_one _

/-- A bounded injective coordinate determines every integrable signed density from its moments.
The underlying measure need not be finite. -/
theorem ae_eq_zero_of_boundedCoordinate_moments
    {μ : Measure ℝ} {φ f : ℝ → ℝ}
    (hφ : MeasurableEmbedding φ) (hbound : ∀ᵐ x ∂μ, |φ x| ≤ 1)
    (hf : Integrable f μ)
    (hmom : ∀ n : ℕ, ∫ x, φ x ^ n * f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hfm := hf.aestronglyMeasurable.aemeasurable
  have hpm : AEMeasurable (posWeight f) μ := hfm.real_toNNReal
  have hnm : AEMeasurable (negWeight f) μ := hfm.neg.real_toNNReal
  let νp := μ.withDensity (fun x => (posWeight f x : ENNReal))
  let νn := μ.withDensity (fun x => (negWeight f x : ENNReal))
  letI : IsFiniteMeasure νp := isFiniteMeasure_withDensity (lintegral_toNNReal_ne_top hf)
  letI : IsFiniteMeasure νn := isFiniteMeasure_withDensity (lintegral_toNNReal_ne_top hf.neg)
  have hbp : ∀ᵐ x ∂νp, |φ x| ≤ 1 :=
    (withDensity_absolutelyContinuous μ _).ae_le hbound
  have hbn : ∀ᵐ x ∂νn, |φ x| ≤ 1 :=
    (withDensity_absolutelyContinuous μ _).ae_le hbound
  have hpint : Integrable (fun x => (posWeight f x : ℝ)) μ :=
    hf.abs.mono' hpm.coe_nnreal_real.aestronglyMeasurable
      (Eventually.of_forall (abs_coe_posWeight_le f))
  have hnint : Integrable (fun x => (negWeight f x : ℝ)) μ :=
    hf.abs.mono' hnm.coe_nnreal_real.aestronglyMeasurable
      (Eventually.of_forall (abs_coe_negWeight_le f))
  have hpow (n : ℕ) : ∀ᵐ x ∂μ, ‖φ x ^ n‖ ≤ 1 := by
    filter_upwards [hbound] with x hx
    simpa [Real.norm_eq_abs, abs_pow] using (pow_le_one₀ (n := n) (abs_nonneg (φ x)) hx)
  have hm : ∀ n : ℕ, ∫ x : ℝ, x ^ n ∂Measure.map φ νp =
      ∫ x : ℝ, x ^ n ∂Measure.map φ νn := by
    intro n
    rw [hφ.integral_map, hφ.integral_map]
    change (∫ x, φ x ^ n ∂μ.withDensity (fun x => (posWeight f x : ENNReal))) =
      ∫ x, φ x ^ n ∂μ.withDensity (fun x => (negWeight f x : ENNReal))
    rw [integral_withDensity_eq_integral_smul₀ hpm,
      integral_withDensity_eq_integral_smul₀ hnm]
    simp only [NNReal.smul_def, smul_eq_mul]
    rw [← sub_eq_zero, ← integral_sub
      (hpint.mul_bdd (hφ.measurable.pow_const n).aestronglyMeasurable (hpow n))
      (hnint.mul_bdd (hφ.measurable.pow_const n).aestronglyMeasurable (hpow n))]
    rw [← hmom n]
    apply integral_congr_ae
    filter_upwards with x
    rw [← sub_mul, coe_posWeight_sub_coe_negWeight, mul_comm]
  have heq : νp = νn := hφ.map_injective
    (measure_eq_of_forall_real_moment_eq (by norm_num)
      (boundedCoordinate_window hφ hbp) (boundedCoordinate_window hφ hbn) hm)
  have hdens := (withDensity_eq_iff hpm.coe_nnreal_ennreal hnm.coe_nnreal_ennreal
    (lintegral_toNNReal_ne_top hf)).mp heq
  filter_upwards [hdens] with x hx
  have hxr : (posWeight f x : ℝ) = (negWeight f x : ℝ) := by
    exact_mod_cast congrArg ENNReal.toNNReal hx
  have hsub := coe_posWeight_sub_coe_negWeight f x
  rw [hxr, sub_self] at hsub
  exact hsub.symm

theorem ae_eq_zero_of_boundedCoordinate_complex_moments
    {μ : Measure ℝ} {φ : ℝ → ℝ} {f : ℝ → ℂ}
    (hφ : MeasurableEmbedding φ) (hbound : ∀ᵐ x ∂μ, |φ x| ≤ 1)
    (hf : Integrable f μ)
    (hmom : ∀ n : ℕ, ∫ x, (φ x : ℂ) ^ n * f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hint (n : ℕ) : Integrable (fun x => (φ x : ℂ) ^ n * f x) μ := by
    apply hf.bdd_mul (c := 1) ((Complex.continuous_ofReal.measurable.comp
      hφ.measurable).pow_const n).aestronglyMeasurable
    filter_upwards [hbound] with x hx
    simpa only [Function.comp_apply, norm_pow, Complex.norm_real, Real.norm_eq_abs] using
      (pow_le_one₀ (n := n) (abs_nonneg (φ x)) hx)
  have hre : (fun x => (f x).re) =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_boundedCoordinate_moments hφ hbound hf.re
    intro n
    have h := congrArg RCLike.re (hmom n)
    rw [← integral_re (hint n)] at h
    simpa [← Complex.ofReal_pow, Complex.mul_re] using h
  have him : (fun x => (f x).im) =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_boundedCoordinate_moments hφ hbound hf.im
    intro n
    have h := congrArg RCLike.im (hmom n)
    rw [← integral_im (hint n)] at h
    simpa [← Complex.ofReal_pow, Complex.mul_im] using h
  filter_upwards [hre, him] with x hx hy
  exact Complex.ext hx hy

/-- All positive integer samples of a half-line Laplace transform determine an `L¹` density.
No analytic continuation or divisor hypothesis enters. -/
theorem ae_eq_zero_of_integer_laplace_moments
    {ell : ℝ} (hell : 0 < ell) {f : ℝ → ℂ}
    (hf : IntegrableOn f (Ioi 0))
    (hmom : ∀ n : ℕ, ∫ t in Ioi (0 : ℝ),
      (Real.exp (-ell * t) : ℂ) ^ n * f t = 0) :
    f =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 := by
  have hφ : MeasurableEmbedding (fun t : ℝ => Real.exp (-ell * t)) := by
    apply (show Continuous (fun t : ℝ => Real.exp (-ell * t)) by fun_prop).measurableEmbedding
    intro x y hxy
    have := Real.exp_injective hxy
    nlinarith
  apply ae_eq_zero_of_boundedCoordinate_complex_moments hφ ?_ hf hmom
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (by nlinarith [(show 0 < t from ht)])

noncomputable section

abbrev BurnolHalfLineL2 := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

/-- Unamplified one-prime depth feature; depth zero has rate `ell`. -/
def burnolDepthFeature (ell : ℝ) (n : ℕ) (t : ℝ) : ℂ :=
  (t * Real.exp (-((n + 1 : ℝ) * ell * t)) : ℝ)

theorem memLp_burnolDepthFeature {ell : ℝ} (hell : 0 < ell) (n : ℕ) :
    MemLp (burnolDepthFeature ell n) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hrate : 0 < 2 * ((n + 1 : ℝ) * ell) := by positivity
  have hbase := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (2 : ℝ))
    (b := 2 * ((n + 1 : ℝ) * ell)) (by norm_num) (by norm_num) hrate
  apply (memLp_two_iff_integrable_sq_norm
    (show AEStronglyMeasurable (burnolDepthFeature ell n)
      (volume.restrict (Ioi (0 : ℝ))) from
      (show Continuous (burnolDepthFeature ell n) by
        unfold burnolDepthFeature; fun_prop).aestronglyMeasurable.restrict)).2
  apply hbase.congr
  filter_upwards with t
  simp only [Real.rpow_two, Real.rpow_one, burnolDepthFeature,
    Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
  congr 2
  ring

def burnolDepthFeatureL2 (ell : Ioi (0 : ℝ)) (n : ℕ) : BurnolHalfLineL2 :=
  (memLp_burnolDepthFeature ell.property n).toLp (burnolDepthFeature ell n)

theorem burnolDepthFeatureL2_ae (ell : Ioi (0 : ℝ)) (n : ℕ) :
    (burnolDepthFeatureL2 ell n : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      burnolDepthFeature ell n := (memLp_burnolDepthFeature ell.property n).coeFn_toLp

theorem burnolDepthFeature_eq_coordinate_pow (ell : ℝ) (n : ℕ) :
    burnolDepthFeature ell n = fun t =>
      (Real.exp (-ell * t) : ℂ) ^ n * burnolDepthFeature ell 0 t := by
  funext u
  simp only [burnolDepthFeature, Nat.cast_zero, zero_add, one_mul]
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul]
  congr 1
  rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  ring

def burnolDepthSpan (ell : Ioi (0 : ℝ)) : Submodule ℂ BurnolHalfLineL2 :=
  Submodule.span ℂ (Set.range (burnolDepthFeatureL2 ell))

theorem burnolDepthSpan_orthogonal (ell : Ioi (0 : ℝ)) :
    (burnolDepthSpan ell)ᗮ = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun g hg => ?_
  have hmom (n : ℕ) : ∫ t in Ioi (0 : ℝ),
      (Real.exp (-(ell : ℝ) * t) : ℂ) ^ n *
        (burnolDepthFeature ell 0 t * g t) = 0 := by
    have h := (Submodule.mem_orthogonal _ g).mp hg (burnolDepthFeatureL2 ell n)
      (Submodule.subset_span ⟨n, rfl⟩)
    rw [L2.inner_def] at h
    rw [← h]
    apply integral_congr_ae
    filter_upwards [burnolDepthFeatureL2_ae ell n] with t ht
    rw [ht, RCLike.inner_apply]
    have hreal : starRingEnd ℂ (burnolDepthFeature ell n t) =
        burnolDepthFeature ell n t := by
      simp only [burnolDepthFeature, Complex.conj_ofReal]
    rw [hreal, burnolDepthFeature_eq_coordinate_pow ell n]
    ring
  have hzero := ae_eq_zero_of_integer_laplace_moments ell.property
    ((memLp_burnolDepthFeature ell.property 0).integrable_mul (Lp.memLp g)) hmom
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [hzero, ae_restrict_mem measurableSet_Ioi] with t ht htpos
  have hw : burnolDepthFeature ell 0 t ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    exact mul_ne_zero (ne_of_gt htpos) (Real.exp_ne_zero _)
  exact (mul_eq_zero.mp ht).resolve_left hw

/-- Every positive geometric rate already spans the entire cubic Burnol output space.
In particular, an entire depth tower at one prime is not a separate closed prime sector. -/
theorem dense_burnolDepthSpan (ell : Ioi (0 : ℝ)) :
    Dense (burnolDepthSpan ell : Set BurnolHalfLineL2) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr
    (Submodule.topologicalClosure_eq_top_iff.mpr (burnolDepthSpan_orthogonal ell))

/-- The output relation retaining both depth towers and their separately prescribed scalars.
The topology is the physical Burnol output topology, not the coefficient `ell²` topology. -/
def burnolTwoClockRelation (ell m : Ioi (0 : ℝ)) (c d : ℂ) :
    Submodule ℂ (BurnolHalfLineL2 × BurnolHalfLineL2) :=
  Submodule.span ℂ
    (((fun x : BurnolHalfLineL2 => (x, c • x)) '' (burnolDepthSpan ell : Set _)) ∪
      ((fun x : BurnolHalfLineL2 => (x, d • x)) '' (burnolDepthSpan m : Set _)))

private theorem burnolTwoClockRelation_graph_left
    (ell m : Ioi (0 : ℝ)) (c d : ℂ) (x : BurnolHalfLineL2) :
    (x, c • x) ∈ (burnolTwoClockRelation ell m c d).topologicalClosure := by
  have hclosed : IsClosed {x : BurnolHalfLineL2 |
      (x, c • x) ∈ (burnolTwoClockRelation ell m c d).topologicalClosure} :=
    (burnolTwoClockRelation ell m c d).isClosed_topologicalClosure.preimage
      (show Continuous (fun x : BurnolHalfLineL2 => (x, c • x)) by fun_prop)
  apply closure_minimal (t := {x : BurnolHalfLineL2 |
    (x, c • x) ∈ (burnolTwoClockRelation ell m c d).topologicalClosure}) ?_ hclosed
    (dense_burnolDepthSpan ell x)
  intro u hu
  exact (burnolTwoClockRelation ell m c d).le_topologicalClosure
    (Submodule.subset_span (Or.inl ⟨u, hu, rfl⟩))

private theorem burnolTwoClockRelation_graph_right
    (ell m : Ioi (0 : ℝ)) (c d : ℂ) (x : BurnolHalfLineL2) :
    (x, d • x) ∈ (burnolTwoClockRelation ell m c d).topologicalClosure := by
  have hclosed : IsClosed {x : BurnolHalfLineL2 |
      (x, d • x) ∈ (burnolTwoClockRelation ell m c d).topologicalClosure} :=
    (burnolTwoClockRelation ell m c d).isClosed_topologicalClosure.preimage
      (show Continuous (fun x : BurnolHalfLineL2 => (x, d • x)) by fun_prop)
  apply closure_minimal (t := {x : BurnolHalfLineL2 |
    (x, d • x) ∈ (burnolTwoClockRelation ell m c d).topologicalClosure}) ?_ hclosed
    (dense_burnolDepthSpan m x)
  intro u hu
  exact (burnolTwoClockRelation ell m c d).le_topologicalClosure
    (Submodule.subset_span (Or.inr ⟨u, hu, rfl⟩))

/-- Distinct scalar prescriptions on two depth towers make the completed relation wholly
multivalued: every input is related to every output. -/
theorem burnolTwoClockRelation_closure_eq_top
    (ell m : Ioi (0 : ℝ)) {c d : ℂ} (hcd : c ≠ d) :
    (burnolTwoClockRelation ell m c d).topologicalClosure = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  rintro ⟨x, y⟩
  let w : BurnolHalfLineL2 := (c - d)⁻¹ • (y - c • x)
  have hdiff := (burnolTwoClockRelation ell m c d).topologicalClosure.sub_mem
    (burnolTwoClockRelation_graph_left ell m c d w)
    (burnolTwoClockRelation_graph_right ell m c d w)
  have hvertical : (0, y - c • x) ∈
      (burnolTwoClockRelation ell m c d).topologicalClosure := by
    have heq : (w, c • w) - (w, d • w) = (0, y - c • x) := by
      apply Prod.ext
      · exact sub_self w
      · change c • w - d • w = y - c • x
        rw [← sub_smul]
        dsimp only [w]
        rw [smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hcd), one_smul]
    rwa [heq] at hdiff
  have hadd := (burnolTwoClockRelation ell m c d).topologicalClosure.add_mem
    (burnolTwoClockRelation_graph_left ell m c d x) hvertical
  simpa only [Prod.mk_add_mk, add_zero, add_sub_cancel] using hadd

/-- Equal prescriptions have precisely the ordinary scalar graph as their closure. -/
theorem burnolTwoClockRelation_closure_eq_graph
    (ell m : Ioi (0 : ℝ)) (c : ℂ) :
    (burnolTwoClockRelation ell m c c).topologicalClosure =
      (c • (LinearMap.id : BurnolHalfLineL2 →ₗ[ℂ] BurnolHalfLineL2)).graph := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ (⟨x, _, rfl⟩ | ⟨x, _, rfl⟩) <;> rfl
    · exact isClosed_eq continuous_snd
        (show Continuous (fun x : BurnolHalfLineL2 × BurnolHalfLineL2 => c • x.1) by fun_prop)
  · intro z hz
    change z.2 = c • z.1 at hz
    simpa only [← hz, Prod.mk.eta] using burnolTwoClockRelation_graph_left ell m c c z.1

/-- Nonzero source amplitudes change neither the algebraic span nor its completion. -/
theorem burnolDepthSpan_eq_span_scaled (ell : Ioi (0 : ℝ))
    (b : ℕ → ℂ) (hb : ∀ n, b n ≠ 0) :
    burnolDepthSpan ell =
      Submodule.span ℂ (Set.range (fun n => b n • burnolDepthFeatureL2 ell n)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    change burnolDepthFeatureL2 ell n ∈ Submodule.span ℂ (Set.range
      (fun n => b n • burnolDepthFeatureL2 ell n))
    have h := (Submodule.span ℂ (Set.range
      (fun n => b n • burnolDepthFeatureL2 ell n))).smul_mem (b n)⁻¹
      (Submodule.subset_span ⟨n, rfl⟩)
    simpa only [smul_smul, inv_mul_cancel₀ (hb n), one_smul] using h
  · apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact (burnolDepthSpan ell).smul_mem (b n) (Submodule.subset_span ⟨n, rfl⟩)

end
end HTGeometry

