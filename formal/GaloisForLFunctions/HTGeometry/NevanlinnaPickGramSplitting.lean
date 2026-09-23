import GaloisForLFunctions.HTGeometry.NevanlinnaResolventCompleteness
import GaloisForLFunctions.HTGeometry.PositiveMeasureExtremeRays
import GaloisForLFunctions.HTGeometry.ProjectiveSingularContinuousResidual

/-!
# The three-layer Pick–Gram splitting of a boundary carrier

The Pick kernel of a boundary carrier splits along the support fibration into a rank-one mean
kernel, the boundary-law covariance of the leaf Cauchy transforms, and the within-leaf covariance.
This is the law of total covariance specialised to the Nevanlinna support fibration: the source
mean, the boundary-law covariance and the within-leaf covariance are the three intrinsic layers of
the positive orientation of a moment carrier.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint

noncomputable section

/-- The real part of a Bochner integral of a complex function. -/
theorem integral_re_eq {A : Type*} [MeasurableSpace A] {mu : Measure A} {f : A → ℂ}
    (hf : Integrable f mu) : (∫ x, f x ∂mu).re = ∫ x, (f x).re ∂mu := by
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hf]
  rfl

/-- The imaginary part of a Bochner integral of a complex function. -/
theorem integral_im_eq {A : Type*} [MeasurableSpace A] {mu : Measure A} {f : A → ℂ}
    (hf : Integrable f mu) : (∫ x, f x ∂mu).im = ∫ x, (f x).im ∂mu := by
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hf]
  rfl

/-- Integration commutes with the real-to-complex coercion. -/
theorem integral_ofReal_eq {A : Type*} [MeasurableSpace A] {mu : Measure A} {f : A → ℝ}
    (hf : Integrable f mu) : ∫ x, ((f x : ℝ) : ℂ) ∂mu = ((∫ x, f x ∂mu : ℝ) : ℂ) := by
  rw [← Complex.ofRealCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hf]
  rfl

/-- Complex Fubini for a bounded observable over a measurable probability kernel. -/
theorem integral_bind_bounded {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (m : Measure A) [IsFiniteMeasure m] (nu : A → Measure B) (hnu : Measurable nu)
    [∀ a, IsProbabilityMeasure (nu a)] {f : B → ℂ} (hf : Measurable f) {C : ℝ}
    (hCnn : 0 ≤ C) (hC : ∀ x, ‖f x‖ ≤ C) :
    (∫ x, f x ∂(m.bind nu)) = ∫ a, (∫ x, f x ∂(nu a)) ∂m := by
  have hCabs : |C| = C := abs_of_nonneg hCnn
  haveI : IsFiniteMeasure (m.bind nu) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hnu.aemeasurable]
    calc ∫⁻ a, nu a univ ∂m = ∫⁻ _a, 1 ∂m := by
          refine lintegral_congr fun a => ?_
          simp
      _ = m univ := by simp
      _ < ⊤ := measure_lt_top m univ
  have hintBind : Integrable f (m.bind nu) := by
    refine Integrable.mono' (g := fun _ => C) (integrable_const C) hf.aestronglyMeasurable ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs, hCabs] using hC x
  have hre : (∫ x, (f x).re ∂(m.bind nu)) = ∫ a, (∫ x, (f x).re ∂(nu a)) ∂m :=
    integral_bind_real m nu (fun x => (f x).re) hnu (Complex.measurable_re.comp hf) hintBind.re
  have him : (∫ x, (f x).im ∂(m.bind nu)) = ∫ a, (∫ x, (f x).im ∂(nu a)) ∂m :=
    integral_bind_real m nu (fun x => (f x).im) hnu (Complex.measurable_im.comp hf) hintBind.im
  have hleafInt : ∀ a : A, Integrable f (nu a) := by
    intro a
    refine Integrable.mono' (g := fun _ => C) (integrable_const C) hf.aestronglyMeasurable ?_
    filter_upwards with x
    simpa [Real.norm_eq_abs, hCabs] using hC x
  have hinner : ∀ a : A, (∫ x, f x ∂(nu a)) =
      ((∫ x, (f x).re ∂(nu a) : ℝ) : ℂ) + Complex.I * ((∫ x, (f x).im ∂(nu a) : ℝ) : ℂ) := by
    intro a
    rw [← integral_re_eq (hleafInt a), ← integral_im_eq (hleafInt a), mul_comm]
    exact (Complex.re_add_im _).symm
  have houter : (∫ x, f x ∂(m.bind nu)) =
      ((∫ x, (f x).re ∂(m.bind nu) : ℝ) : ℂ) +
        Complex.I * ((∫ x, (f x).im ∂(m.bind nu) : ℝ) : ℂ) := by
    rw [← integral_re_eq hintBind, ← integral_im_eq hintBind, mul_comm]
    exact (Complex.re_add_im _).symm
  have hmeasRe : Measurable fun a : A => ∫ x, (f x).re ∂(nu a) := by
    have := MeasureTheory.StronglyMeasurable.integral_kernel
      (κ := (⟨nu, hnu⟩ : ProbabilityTheory.Kernel A B))
      ((Complex.measurable_re.comp hf).stronglyMeasurable)
    exact this.measurable
  have hmeasIm : Measurable fun a : A => ∫ x, (f x).im ∂(nu a) := by
    have := MeasureTheory.StronglyMeasurable.integral_kernel
      (κ := (⟨nu, hnu⟩ : ProbabilityTheory.Kernel A B))
      ((Complex.measurable_im.comp hf).stronglyMeasurable)
    exact this.measurable
  have hintRe : Integrable (fun a : A => ∫ x, (f x).re ∂(nu a)) m := by
    refine Integrable.mono' (g := fun _ => C) (integrable_const C)
      hmeasRe.aestronglyMeasurable ?_
    filter_upwards with a
    have := norm_integral_le_of_norm_le_const (C := C) (μ := nu a) (f := fun x => (f x).re)
      (Filter.Eventually.of_forall fun x => le_trans (Complex.abs_re_le_norm _) (hC x))
    simpa [Real.norm_eq_abs, hCabs] using this
  have hintIm : Integrable (fun a : A => ∫ x, (f x).im ∂(nu a)) m := by
    refine Integrable.mono' (g := fun _ => C) (integrable_const C)
      hmeasIm.aestronglyMeasurable ?_
    filter_upwards with a
    have := norm_integral_le_of_norm_le_const (C := C) (μ := nu a) (f := fun x => (f x).im)
      (Filter.Eventually.of_forall fun x => le_trans (Complex.abs_im_le_norm _) (hC x))
    simpa [Real.norm_eq_abs, hCabs] using this
  rw [houter, hre, him]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  rw [integral_add (hintRe.ofReal) ((hintIm.ofReal).const_mul _)]
  rw [integral_const_mul, integral_ofReal_eq hintRe, integral_ofReal_eq hintIm]

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)
  (eta : Measure (OnePoint ℝ))

/-- The mean leaf Cauchy transform of a boundary law. -/
def boundaryMean (z : ℂ) : ℂ := ∫ t, F.leafCauchy z t ∂eta

/-- The boundary-law covariance kernel of the leaf Cauchy transforms. -/
def boundaryGram (z w : ℂ) : ℂ :=
  ∫ t, (F.leafCauchy z t - F.boundaryMean eta z) *
    (starRingEnd ℂ) (F.leafCauchy w t - F.boundaryMean eta w) ∂eta

/-- The within-leaf covariance kernel. -/
def withinLeafGram (z w : ℂ) : ℂ :=
  ∫ t, ((∫ x : ℝ, ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹)
      ∂((F.base.leaf t : ProbabilityMeasure ℝ) : Measure ℝ))
    - F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t)) ∂eta

/-- The ordinary Pick kernel of the boundary carrier. -/
def carrierPickGram (z w : ℂ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹)
    ∂(F.base.toBoundaryFamily.measureBarycenter eta)

variable {F eta}

theorem norm_resolvent_product_le {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (x : ℝ) :
    ‖((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹)‖ ≤ |z.im|⁻¹ * |w.im|⁻¹ := by
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_mul (norm_cauchyKernel_le hz x) (norm_cauchyKernel_le hw x) (norm_nonneg _)
    (by positivity)

/-- **The law of total covariance on the support fibration.**  The Pick kernel of the boundary
carrier is the sum of the rank-one mean kernel, the boundary-law covariance and the within-leaf
covariance. -/
theorem carrierPickGram_eq_add [IsProbabilityMeasure eta] {z w : ℂ}
    (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    F.carrierPickGram eta z w =
      F.boundaryMean eta z * (starRingEnd ℂ) (F.boundaryMean eta w) +
        F.boundaryGram eta z w + F.withinLeafGram eta z w := by
  classical
  haveI : ∀ t : OnePoint ℝ,
      IsProbabilityMeasure (F.base.toBoundaryFamily.leafMeasure t) := fun t => (F.base.leaf t).prop
  have hprodmeas : Measurable fun x : ℝ =>
      ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹) := by fun_prop
  -- the carrier Pick kernel disintegrates
  have hbind : F.carrierPickGram eta z w =
      ∫ t, (∫ x : ℝ, ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹)
        ∂(F.base.toBoundaryFamily.leafMeasure t)) ∂eta := by
    rw [carrierPickGram]
    exact integral_bind_bounded eta F.base.toBoundaryFamily.leafMeasure F.base.toBoundaryFamily.measurable_leaf hprodmeas
      (by positivity) (fun x => norm_resolvent_product_le hz hw x)
  -- the leaf-product integrals and the leaf transforms are bounded
  have hleafprod : Measurable fun t : OnePoint ℝ =>
      ∫ x : ℝ, ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹) ∂(F.base.toBoundaryFamily.leafMeasure t) := by
    have := MeasureTheory.StronglyMeasurable.integral_kernel
      (κ := F.base.toBoundaryFamily.leafKernel) hprodmeas.stronglyMeasurable
    exact this.measurable
  have hleafprodbdd : ∀ t : OnePoint ℝ,
      ‖∫ x : ℝ, ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹) ∂(F.base.toBoundaryFamily.leafMeasure t)‖
        ≤ |z.im|⁻¹ * |w.im|⁻¹ := by
    intro t
    have := norm_integral_le_of_norm_le_const (C := |z.im|⁻¹ * |w.im|⁻¹)
      (μ := F.base.toBoundaryFamily.leafMeasure t)
      (Filter.Eventually.of_forall fun x => norm_resolvent_product_le hz hw x)
    simpa using this
  have hintprod : Integrable (fun t : OnePoint ℝ =>
      ∫ x : ℝ, ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹) ∂(F.base.toBoundaryFamily.leafMeasure t)) eta := by
    refine Integrable.mono' (g := fun _ => |z.im|⁻¹ * |w.im|⁻¹) (integrable_const _)
      hleafprod.aestronglyMeasurable ?_
    filter_upwards with t
    exact hleafprodbdd t
  have hintPhiProd : Integrable (fun t : OnePoint ℝ =>
      F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t)) eta := by
    refine Integrable.mono' (g := fun _ => |z.im|⁻¹ * |w.im|⁻¹) (integrable_const _)
      ((F.measurable_leafCauchy.mul (Complex.continuous_conj.measurable.comp
        F.measurable_leafCauchy)).aestronglyMeasurable) ?_
    filter_upwards with t
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul (F.norm_leafCauchy_le hz t) (F.norm_leafCauchy_le hw t) (norm_nonneg _)
      (by positivity)
  have hintPhiz : Integrable (fun t : OnePoint ℝ => F.leafCauchy z t) eta := by
    refine Integrable.mono' (g := fun _ => |z.im|⁻¹) (integrable_const _)
      F.measurable_leafCauchy.aestronglyMeasurable ?_
    filter_upwards with t
    exact F.norm_leafCauchy_le hz t
  have hintPhiw : Integrable (fun t : OnePoint ℝ => (starRingEnd ℂ) (F.leafCauchy w t)) eta := by
    refine Integrable.mono' (g := fun _ => |w.im|⁻¹) (integrable_const _)
      ((Complex.continuous_conj.measurable.comp F.measurable_leafCauchy)).aestronglyMeasurable ?_
    filter_upwards with t
    rw [RCLike.norm_conj]
    exact F.norm_leafCauchy_le hw t
  -- the within-leaf kernel is the difference
  have hwithin : F.withinLeafGram eta z w =
      (∫ t, (∫ x : ℝ, ((x : ℂ) - z)⁻¹ * (starRingEnd ℂ) (((x : ℂ) - w)⁻¹)
          ∂(F.base.toBoundaryFamily.leafMeasure t)) ∂eta) -
        ∫ t, F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t) ∂eta := by
    rw [withinLeafGram, ← integral_sub hintprod hintPhiProd]
    rfl
  -- the boundary covariance expands
  have hmeanconj : ∫ t, (starRingEnd ℂ) (F.leafCauchy w t) ∂eta
      = (starRingEnd ℂ) (F.boundaryMean eta w) := by
    rw [boundaryMean, ← integral_conj]
  have hgram : F.boundaryGram eta z w =
      (∫ t, F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t) ∂eta) -
        F.boundaryMean eta z * (starRingEnd ℂ) (F.boundaryMean eta w) := by
    have hB : Integrable
        (fun t => F.boundaryMean eta z * (starRingEnd ℂ) (F.leafCauchy w t)) eta :=
      hintPhiw.const_mul (F.boundaryMean eta z)
    have hC : Integrable
        (fun t => (starRingEnd ℂ) (F.boundaryMean eta w) * F.leafCauchy z t) eta :=
      hintPhiz.const_mul ((starRingEnd ℂ) (F.boundaryMean eta w))
    have hD : Integrable (fun _ : OnePoint ℝ =>
        F.boundaryMean eta z * (starRingEnd ℂ) (F.boundaryMean eta w)) eta :=
      integrable_const _
    have hexpand : ∀ t : OnePoint ℝ,
        (F.leafCauchy z t - F.boundaryMean eta z) *
            (starRingEnd ℂ) (F.leafCauchy w t - F.boundaryMean eta w) =
          F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t) -
              F.boundaryMean eta z * (starRingEnd ℂ) (F.leafCauchy w t) -
              (starRingEnd ℂ) (F.boundaryMean eta w) * F.leafCauchy z t +
            F.boundaryMean eta z * (starRingEnd ℂ) (F.boundaryMean eta w) := by
      intro t
      rw [map_sub]
      ring
    have hstep : F.boundaryGram eta z w =
        ((∫ t, F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t) ∂eta) -
            (∫ t, F.boundaryMean eta z * (starRingEnd ℂ) (F.leafCauchy w t) ∂eta) -
            (∫ t, (starRingEnd ℂ) (F.boundaryMean eta w) * F.leafCauchy z t ∂eta)) +
          ∫ _t : OnePoint ℝ,
            F.boundaryMean eta z * (starRingEnd ℂ) (F.boundaryMean eta w) ∂eta := by
      have hAB : Integrable (fun t => F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t) -
          F.boundaryMean eta z * (starRingEnd ℂ) (F.leafCauchy w t)) eta := hintPhiProd.sub hB
      have hABC : Integrable (fun t =>
          (F.leafCauchy z t * (starRingEnd ℂ) (F.leafCauchy w t) -
              F.boundaryMean eta z * (starRingEnd ℂ) (F.leafCauchy w t)) -
            (starRingEnd ℂ) (F.boundaryMean eta w) * F.leafCauchy z t) eta := hAB.sub hC
      rw [boundaryGram, integral_congr_ae (Filter.Eventually.of_forall hexpand),
        integral_add hABC hD, integral_sub hAB hC, integral_sub hintPhiProd hB]
    rw [hstep, integral_const_mul, integral_const_mul, hmeanconj, integral_const]
    have hmass : eta.real univ = 1 := by simp
    rw [hmass, one_smul, ← boundaryMean]
    ring
  rw [hbind, hwithin, hgram]
  ring

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} {F : ClassicalAnalyticNevanlinnaCarrierFamily s}
  {eta : Measure (OnePoint ℝ)}

/-- Integrability of the centered leaf transform against a finite boundary law. -/
theorem integrable_centered_leafCauchy [IsProbabilityMeasure eta] {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun t => F.leafCauchy z t - F.boundaryMean eta z) eta := by
  have hint : Integrable (fun t : OnePoint ℝ => F.leafCauchy z t) eta := by
    refine Integrable.mono' (g := fun _ => |z.im|⁻¹) (integrable_const _)
      F.measurable_leafCauchy.aestronglyMeasurable ?_
    filter_upwards with t
    exact F.norm_leafCauchy_le hz t
  exact hint.sub (integrable_const _)

/-- **The self-Gram is the boundary variance.** -/
theorem boundaryGram_self [IsProbabilityMeasure eta] {z : ℂ} (hz : z.im ≠ 0) :
    F.boundaryGram eta z z =
      ((∫ t, ‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ) ∂eta : ℝ) : ℂ) := by
  have hcentered := integrable_centered_leafCauchy (F := F) (eta := eta) hz
  have hsq : Integrable (fun t => ‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ)) eta := by
    have hbound : ∀ t : OnePoint ℝ,
        ‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ) ≤ (2 * |z.im|⁻¹) ^ (2 : ℕ) := by
      intro t
      have hb : ‖F.leafCauchy z t - F.boundaryMean eta z‖ ≤ 2 * |z.im|⁻¹ := by
        have hm : ‖F.boundaryMean eta z‖ ≤ |z.im|⁻¹ := by
          have hb := norm_integral_le_of_norm_le_const (C := |z.im|⁻¹) (μ := eta)
            (f := fun t => F.leafCauchy z t)
            (Filter.Eventually.of_forall fun t => F.norm_leafCauchy_le hz t)
          have hmass : eta.real univ = 1 := by simp
          rw [hmass, mul_one] at hb
          simpa [boundaryMean] using hb
        calc ‖F.leafCauchy z t - F.boundaryMean eta z‖
            ≤ ‖F.leafCauchy z t‖ + ‖F.boundaryMean eta z‖ := norm_sub_le _ _
          _ ≤ |z.im|⁻¹ + |z.im|⁻¹ := add_le_add (F.norm_leafCauchy_le hz t) hm
          _ = 2 * |z.im|⁻¹ := by ring
      have hnn : (0:ℝ) ≤ ‖F.leafCauchy z t - F.boundaryMean eta z‖ := norm_nonneg _
      nlinarith [hb, hnn]
    refine Integrable.mono' (g := fun _ => (2 * |z.im|⁻¹) ^ (2 : ℕ)) (integrable_const _)
      ((hcentered.aestronglyMeasurable.norm.pow 2)) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound t
  rw [boundaryGram, ← integral_ofReal_eq hsq]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  show (F.leafCauchy z t - F.boundaryMean eta z) *
      (starRingEnd ℂ) (F.leafCauchy z t - F.boundaryMean eta z)
    = ((‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ) : ℝ) : ℂ)
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- A vanishing self-Gram makes the leaf transform almost everywhere constant. -/
theorem leafCauchy_ae_eq_of_boundaryGram_self_eq_zero [IsProbabilityMeasure eta] {z : ℂ}
    (hz : z.im ≠ 0) (h0 : F.boundaryGram eta z z = 0) :
    ∀ᵐ t ∂eta, F.leafCauchy z t = F.boundaryMean eta z := by
  have hcentered := integrable_centered_leafCauchy (F := F) (eta := eta) hz
  have hself := boundaryGram_self (F := F) (eta := eta) hz
  rw [h0] at hself
  have hzeroReal : ∫ t, ‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ) ∂eta = 0 := by
    exact_mod_cast hself.symm
  have hsq : Integrable (fun t => ‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ)) eta := by
    have hbound : ∀ t : OnePoint ℝ,
        ‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ) ≤ (2 * |z.im|⁻¹) ^ (2 : ℕ) := by
      intro t
      have hm : ‖F.boundaryMean eta z‖ ≤ |z.im|⁻¹ := by
        have hb := norm_integral_le_of_norm_le_const (C := |z.im|⁻¹) (μ := eta)
          (f := fun t => F.leafCauchy z t)
          (Filter.Eventually.of_forall fun t => F.norm_leafCauchy_le hz t)
        have hmass : eta.real univ = 1 := by simp
        rw [hmass, mul_one] at hb
        simpa [boundaryMean] using hb
      have hb : ‖F.leafCauchy z t - F.boundaryMean eta z‖ ≤ 2 * |z.im|⁻¹ := by
        calc ‖F.leafCauchy z t - F.boundaryMean eta z‖
            ≤ ‖F.leafCauchy z t‖ + ‖F.boundaryMean eta z‖ := norm_sub_le _ _
          _ ≤ |z.im|⁻¹ + |z.im|⁻¹ := add_le_add (F.norm_leafCauchy_le hz t) hm
          _ = 2 * |z.im|⁻¹ := by ring
      nlinarith [hb, norm_nonneg (F.leafCauchy z t - F.boundaryMean eta z)]
    refine Integrable.mono' (g := fun _ => (2 * |z.im|⁻¹) ^ (2 : ℕ)) (integrable_const _)
      (hcentered.aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hbound t
  have hae := (integral_eq_zero_iff_of_nonneg (fun t => by positivity) hsq).1 hzeroReal
  filter_upwards [hae] with t ht
  have hzero2 : ‖F.leafCauchy z t - F.boundaryMean eta z‖ ^ (2 : ℕ) = 0 := ht
  have hnorm : ‖F.leafCauchy z t - F.boundaryMean eta z‖ = 0 := by
    nlinarith [norm_nonneg (F.leafCauchy z t - F.boundaryMean eta z), hzero2]
  exact sub_eq_zero.1 (norm_eq_zero.1 hnorm)

/-- The projective line is second countable: it is homeomorphic to the circle. -/
local instance onePointRealSecondCountable : SecondCountableTopology (OnePoint ℝ) :=
  onePointRealUnitAddCircleHomeomorph.isEmbedding.secondCountableTopology

/-- **Degeneracy of the boundary covariance.**  If every self-Gram vanishes, the boundary law is a
point mass: the boundary-law covariance sees exactly the nondegeneracy of the boundary law. -/
theorem exists_eq_dirac_of_boundaryGram_eq_zero
    (hcne : ∀ z : ℂ, z.im ≠ 0 → F.c z ≠ 0)
    (hup : ∀ z : ℂ, z.im < 0 → 0 < (F.quotient z).im)
    (hlow : ∀ z : ℂ, 0 < z.im → (F.quotient z).im < 0)
    [IsProbabilityMeasure eta]
    (hzero : ∀ z : ℂ, z.im ≠ 0 → F.boundaryGram eta z z = 0) :
    ∃ t₀ : OnePoint ℝ, eta = Measure.dirac t₀ := by
  classical
  have h01 : ∀ S : Set (OnePoint ℝ), MeasurableSet S → eta S = 0 ∨ eta S = 1 := by
    intro S hS
    set c : ℝ := eta.real S with hc
    set g : OnePoint ℝ → ℂ := fun t => S.indicator (fun _ => (1 : ℂ)) t - (c : ℂ) with hg
    have hgmeas : Measurable g := (measurable_one.indicator hS).sub measurable_const
    have hgbound : ∀ t, ‖g t‖ ≤ 1 + |c| := by
      intro t
      have hind : ‖S.indicator (fun _ => (1 : ℂ)) t‖ ≤ 1 := by
        by_cases htS : t ∈ S
        · rw [Set.indicator_of_mem htS]
          simp
        · rw [Set.indicator_of_notMem htS]
          simp
      calc ‖g t‖ ≤ ‖S.indicator (fun _ => (1 : ℂ)) t‖ + ‖(c : ℂ)‖ := norm_sub_le _ _
        _ ≤ 1 + |c| := by
            refine add_le_add hind ?_
            simp
    have hgint : Integrable g eta := by
      refine Integrable.mono' (g := fun _ => 1 + |c|) (integrable_const _)
        hgmeas.aestronglyMeasurable ?_
      filter_upwards with t
      exact hgbound t
    have hconst : ∫ t, g t ∂eta = 0 := by
      have hindint : Integrable (fun t => S.indicator (fun _ => (1 : ℂ)) t) eta :=
        (integrable_const (1 : ℂ)).indicator hS
      rw [hg, integral_sub hindint (integrable_const _), integral_indicator_const _ hS,
        integral_const]
      have hmass : eta.real univ = 1 := by simp
      rw [hmass, one_smul, hc]
      simp
    have hcauchy : ∀ z : ℂ, z.im ≠ 0 → ∫ t, F.leafCauchy z t * g t ∂eta = 0 := by
      intro z hz
      have hae := leafCauchy_ae_eq_of_boundaryGram_self_eq_zero (F := F) (eta := eta) hz
        (hzero z hz)
      have hcongr : ∫ t, F.leafCauchy z t * g t ∂eta = ∫ t, F.boundaryMean eta z * g t ∂eta := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with t ht
        rw [ht]
      rw [hcongr, integral_const_mul, hconst, mul_zero]
    have hgzero := F.eq_zero_ae_of_annihilates_leafCauchy hcne hup hlow eta hgmeas hgint hconst
      hcauchy
    have hnull : eta {t : OnePoint ℝ | ¬ g t = 0} = 0 := (MeasureTheory.ae_iff).1 hgzero
    by_cases hc1 : c = 1
    · right
      have hsub : Sᶜ ⊆ {t : OnePoint ℝ | ¬ g t = 0} := by
        intro t ht
        have : g t = -(c : ℂ) := by
          rw [hg]
          simp [Set.indicator_of_notMem ht]
        rw [Set.mem_setOf_eq, this, hc1]
        norm_num
      have hcompl : eta Sᶜ = 0 := measure_mono_null hsub hnull
      have hfull : eta S + eta Sᶜ = eta univ := measure_add_measure_compl hS
      rw [hcompl, add_zero, measure_univ] at hfull
      exact hfull
    · left
      have hsub : S ⊆ {t : OnePoint ℝ | ¬ g t = 0} := by
        intro t ht
        have : g t = 1 - (c : ℂ) := by
          rw [hg]
          simp [Set.indicator_of_mem ht]
        rw [Set.mem_setOf_eq, this]
        intro hzero'
        apply hc1
        have : ((c : ℝ) : ℂ) = 1 := by linear_combination -hzero'
        exact_mod_cast this
      exact measure_mono_null hsub hnull
  exact GaloisForLFunctions.HTGeometry.exists_eq_dirac_of_measure_eq_zero_or_one eta h01

/-- A point-mass boundary law has vanishing covariance kernel. -/
theorem boundaryGram_dirac (t₀ : OnePoint ℝ) (z w : ℂ) :
    F.boundaryGram (Measure.dirac t₀) z w = 0 := by
  have hmean : ∀ v : ℂ, F.boundaryMean (Measure.dirac t₀) v = F.leafCauchy v t₀ := by
    intro v
    rw [boundaryMean, integral_dirac]
  rw [boundaryGram, integral_dirac, hmean, hmean]
  simp

/-- **The boundary covariance vanishes exactly at point masses.** -/
theorem boundaryGram_eq_zero_iff_exists_dirac
    (hcne : ∀ z : ℂ, z.im ≠ 0 → F.c z ≠ 0)
    (hup : ∀ z : ℂ, z.im < 0 → 0 < (F.quotient z).im)
    (hlow : ∀ z : ℂ, 0 < z.im → (F.quotient z).im < 0)
    [IsProbabilityMeasure eta] :
    (∀ z : ℂ, z.im ≠ 0 → F.boundaryGram eta z z = 0) ↔
      ∃ t₀ : OnePoint ℝ, eta = Measure.dirac t₀ := by
  constructor
  · intro hzero
    exact exists_eq_dirac_of_boundaryGram_eq_zero hcne hup hlow hzero
  · rintro ⟨t₀, rfl⟩ z _
    exact boundaryGram_dirac t₀ z z

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry
