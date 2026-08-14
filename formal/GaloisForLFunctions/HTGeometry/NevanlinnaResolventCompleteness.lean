import GaloisForLFunctions.HTGeometry.NevanlinnaQuotientOpenImage
import GaloisForLFunctions.HTGeometry.BoundaryConditionalExpectation
import GaloisForLFunctions.HTGeometry.NevanlinnaEntryConjugation
import GaloisForLFunctions.HTGeometry.NevanlinnaWeylDiscPole

/-!
# Resolvent completeness of the projective boundary

The leaf Cauchy transforms `Φ_z(τ) = m_τ(z)` together with the constant function span a dense
subspace of the boundary parameter space: a parameter density annihilating the constant and every
`Φ_z` vanishes almost everywhere.

The mechanism is the Möbius partial fraction `Φ_z(τ) = Φ_z(∞) − c(z)^{-2}(τ − q(z))^{-1}`.  Removing
the constant leaves the Cauchy transform of the density against the finite chart, evaluated at the
Weyl pole `q(z)`; the pole map sends each half-plane onto an open subset of the other, so the
transform vanishes on an open set of each half-plane and the density must vanish.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint

noncomputable section

/-- The finite chart of a projective parameter measure, as a measure on the line. -/
def chartMeasure (eta : Measure (OnePoint ℝ)) : Measure ℝ :=
  Measure.comap ((↑) : ℝ → OnePoint ℝ) eta

theorem measurableEmbedding_onePoint_coe : MeasurableEmbedding ((↑) : ℝ → OnePoint ℝ) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

theorem chartMeasure_apply (eta : Measure (OnePoint ℝ)) (A : Set ℝ) :
    chartMeasure eta A = eta (((↑) : ℝ → OnePoint ℝ) '' A) :=
  measurableEmbedding_onePoint_coe.comap_apply eta A

instance isFiniteMeasure_chartMeasure (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta] :
    IsFiniteMeasure (chartMeasure eta) := by
  constructor
  rw [chartMeasure_apply eta univ]
  exact lt_of_le_of_lt (measure_mono (subset_univ _)) (measure_lt_top eta univ)

/-- **Chart splitting of a projective integral.**  An integral over the projective line is the
integral over the finite chart plus the mass at infinity. -/
theorem integral_onePoint_split (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    {f : OnePoint ℝ → ℂ} (hf : Integrable f eta) :
    ∫ t, f t ∂eta =
      (∫ τ : ℝ, f (τ : OnePoint ℝ) ∂(chartMeasure eta)) + (eta {∞}).toReal • f ∞ := by
  have hinfty : MeasurableSet ({∞} : Set (OnePoint ℝ)) :=
    (OnePoint.isClosed_infty (X := ℝ)).measurableSet
  have hsplit := MeasureTheory.integral_add_compl hinfty hf
  have hsingle : ∫ t in ({∞} : Set (OnePoint ℝ)), f t ∂eta = (eta {∞}).toReal • f ∞ := by
    rw [Measure.restrict_singleton, integral_smul_measure, integral_dirac]
  have hchart : ∫ t in ({∞} : Set (OnePoint ℝ))ᶜ, f t ∂eta =
      ∫ τ : ℝ, f (τ : OnePoint ℝ) ∂(chartMeasure eta) := by
    have hrange : (range ((↑) : ℝ → OnePoint ℝ)) = ({∞} : Set (OnePoint ℝ))ᶜ := by
      ext t
      induction t using OnePoint.rec with
      | infty => simp
      | coe x => simp
    rw [← hrange, ← measurableEmbedding_onePoint_coe.map_comap eta,
      measurableEmbedding_onePoint_coe.integral_map]
    rfl
  rw [← hsplit, hsingle, hchart]
  ring

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The leaf Cauchy transform as a function of the projective parameter. -/
def leafCauchy (z : ℂ) (t : OnePoint ℝ) : ℂ :=
  ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(F.base.leaf t : Measure ℝ)

theorem leafCauchy_coe {z : ℂ} (hz : z.im ≠ 0) (tau : ℝ) :
    F.leafCauchy z (tau : OnePoint ℝ) =
      (F.a z * (tau : ℂ) + F.b z) / (F.c z * (tau : ℂ) + F.d z) :=
  F.finite_cauchy tau z hz

theorem leafCauchy_infty {z : ℂ} (hz : z.im ≠ 0) (hc : F.c z ≠ 0) :
    F.leafCauchy z ∞ = F.a z / F.c z :=
  F.infinity_cauchy z hz hc

/-- The denominator never vanishes on the finite chart when the Weyl pole is nonreal. -/
theorem denominator_ne_zero {z : ℂ} (hc : F.c z ≠ 0) (hq : (F.quotient z).im ≠ 0) (tau : ℝ) :
    F.c z * (tau : ℂ) + F.d z ≠ 0 := by
  intro hzero
  have hquot : F.quotient z = (tau : ℂ) := by
    rw [quotient, div_eq_iff hc]
    linear_combination -hzero
  rw [hquot] at hq
  simp at hq

/-- **The Möbius partial fraction.**  Removing the value at infinity leaves a single Cauchy kernel
at the Weyl pole. -/
theorem leafCauchy_sub_infty {z : ℂ} (hz : z.im ≠ 0) (hc : F.c z ≠ 0)
    (hq : (F.quotient z).im ≠ 0) (tau : ℝ) :
    F.leafCauchy z (tau : OnePoint ℝ) - F.leafCauchy z ∞ =
      (-(F.c z ^ 2)⁻¹) * ((tau : ℂ) - F.quotient z)⁻¹ := by
  have hden := F.denominator_ne_zero hc hq tau
  have hfac : (tau : ℂ) - F.quotient z = (F.c z * (tau : ℂ) + F.d z) / F.c z := by
    rw [quotient]
    field_simp
    ring
  have hsub : (tau : ℂ) - F.quotient z ≠ 0 := by
    rw [hfac]
    exact div_ne_zero hden hc
  have hdet := F.det_one z
  have hLHS : (F.a z * (tau : ℂ) + F.b z) / (F.c z * (tau : ℂ) + F.d z) - F.a z / F.c z
      = (-1 : ℂ) / ((F.c z * (tau : ℂ) + F.d z) * F.c z) := by
    rw [div_sub_div _ _ hden hc]
    congr 1
    linear_combination -hdet
  have hRHS : (-(F.c z ^ 2)⁻¹) * ((tau : ℂ) - F.quotient z)⁻¹
      = (-1 : ℂ) / ((F.c z * (tau : ℂ) + F.d z) * F.c z) := by
    rw [hfac]
    field_simp
  rw [F.leafCauchy_coe hz tau, F.leafCauchy_infty hz hc, hLHS, hRHS]

/-- **One finite-centre value separates the extremal leaves.**  For a fixed nonreal centre the leaf
Cauchy transform is injective in the projective parameter. -/
theorem leafCauchy_injective_on_chart {z : ℂ} (hz : z.im ≠ 0) (hc : F.c z ≠ 0)
    (hq : (F.quotient z).im ≠ 0) :
    Function.Injective (fun tau : ℝ => F.leafCauchy z (tau : OnePoint ℝ)) := by
  intro tau1 tau2 heq0
  have heq : F.leafCauchy z (tau1 : OnePoint ℝ) = F.leafCauchy z (tau2 : OnePoint ℝ) := heq0
  have h1 := F.leafCauchy_sub_infty hz hc hq tau1
  have h2 := F.leafCauchy_sub_infty hz hc hq tau2
  have hsub : (-(F.c z ^ 2)⁻¹) * (((tau1 : ℝ) : ℂ) - F.quotient z)⁻¹ =
      (-(F.c z ^ 2)⁻¹) * (((tau2 : ℝ) : ℂ) - F.quotient z)⁻¹ := by
    rw [← h1, ← h2, heq]
  have hBne : (-(F.c z ^ 2)⁻¹) ≠ 0 := by
    simp [hc]
  have hinv : (((tau1 : ℝ) : ℂ) - F.quotient z)⁻¹ = (((tau2 : ℝ) : ℂ) - F.quotient z)⁻¹ :=
    mul_left_cancel₀ hBne hsub
  have hne1 : ((tau1 : ℝ) : ℂ) - F.quotient z ≠ 0 := by
    intro hzero
    apply hq
    have : F.quotient z = ((tau1 : ℝ) : ℂ) := by linear_combination -hzero
    rw [this]
    simp
  have hne2 : ((tau2 : ℝ) : ℂ) - F.quotient z ≠ 0 := by
    intro hzero
    apply hq
    have : F.quotient z = ((tau2 : ℝ) : ℂ) := by linear_combination -hzero
    rw [this]
    simp
  have := inv_injective hinv
  have hreal : ((tau1 : ℝ) : ℂ) = ((tau2 : ℝ) : ℂ) := by linear_combination this
  exact_mod_cast hreal

end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Complex Filter Set Topology

open scoped OnePoint

noncomputable section

namespace ClassicalAnalyticNevanlinnaCarrierFamily

variable {s : ℕ → ℝ} (F : ClassicalAnalyticNevanlinnaCarrierFamily s)

/-- The leaf Cauchy transform is bounded by the reciprocal distance to the real axis. -/
theorem norm_leafCauchy_le {z : ℂ} (hz : z.im ≠ 0) (t : OnePoint ℝ) :
    ‖F.leafCauchy z t‖ ≤ |z.im|⁻¹ := by
  haveI : IsProbabilityMeasure ((F.base.leaf t : ProbabilityMeasure ℝ) : Measure ℝ) :=
    (F.base.leaf t).prop
  have hbound : ∀ x : ℝ, ‖((x : ℂ) - z)⁻¹‖ ≤ |z.im|⁻¹ := fun x => norm_cauchyKernel_le hz x
  have := norm_integral_le_of_norm_le_const (C := |z.im|⁻¹)
    (μ := ((F.base.leaf t : ProbabilityMeasure ℝ) : Measure ℝ))
    (f := fun x : ℝ => ((x : ℂ) - z)⁻¹)
    (Filter.Eventually.of_forall hbound)
  simpa [leafCauchy] using this

theorem measurable_leafCauchy {z : ℂ} : Measurable (F.leafCauchy z) := by
  have hker : StronglyMeasurable fun x : ℝ => ((x : ℂ) - z)⁻¹ := by
    refine Measurable.stronglyMeasurable ?_
    fun_prop
  have := MeasureTheory.StronglyMeasurable.integral_kernel
    (κ := F.base.toBoundaryFamily.leafKernel) hker
  exact this.measurable

/-- **Resolvent completeness of the projective boundary.**  A parameter density annihilating the
constant function and every leaf Cauchy transform vanishes almost everywhere. -/
theorem eq_zero_ae_of_annihilates_leafCauchy
    (hcne : ∀ z : ℂ, z.im ≠ 0 → F.c z ≠ 0)
    (hup : ∀ z : ℂ, z.im < 0 → 0 < (F.quotient z).im)
    (hlow : ∀ z : ℂ, 0 < z.im → (F.quotient z).im < 0)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    {g : OnePoint ℝ → ℂ} (hgmeas : Measurable g) (hgint : Integrable g eta)
    (hconst : ∫ t, g t ∂eta = 0)
    (hcauchy : ∀ z : ℂ, z.im ≠ 0 → ∫ t, F.leafCauchy z t * g t ∂eta = 0) :
    g =ᵐ[eta] 0 := by
  classical
  set nu : Measure ℝ := chartMeasure eta with hnu
  set gc : ℝ → ℂ := fun τ => g (τ : OnePoint ℝ) with hgc
  have hgcmeas : Measurable gc := hgmeas.comp OnePoint.continuous_coe.measurable
  have hgcint : Integrable gc nu := by
    have h1 : Integrable g (eta.restrict (range ((↑) : ℝ → OnePoint ℝ))) := hgint.restrict
    rw [← measurableEmbedding_onePoint_coe.map_comap eta] at h1
    exact (measurableEmbedding_onePoint_coe.integrable_map_iff).1 h1
  -- the transform of the chart density vanishes at every Weyl pole
  have hpole : ∀ z : ℂ, z.im ≠ 0 → densityCauchyTransform nu gc (F.quotient z) = 0 := by
    intro z hz
    have hc := hcne z hz
    have hqim : (F.quotient z).im ≠ 0 := by
      rcases lt_or_gt_of_ne hz with hneg | hpos
      · exact ne_of_gt (hup z hneg)
      · exact ne_of_lt (hlow z hpos)
    have hbdd : ∀ t : OnePoint ℝ, ‖(F.leafCauchy z t - F.leafCauchy z ∞) * g t‖ ≤
        (2 * |z.im|⁻¹) * ‖g t‖ := by
      intro t
      rw [norm_mul]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖F.leafCauchy z t - F.leafCauchy z ∞‖
          ≤ ‖F.leafCauchy z t‖ + ‖F.leafCauchy z ∞‖ := norm_sub_le _ _
        _ ≤ |z.im|⁻¹ + |z.im|⁻¹ := add_le_add (F.norm_leafCauchy_le hz t) (F.norm_leafCauchy_le hz ∞)
        _ = 2 * |z.im|⁻¹ := by ring
    have hintDiff : Integrable (fun t => (F.leafCauchy z t - F.leafCauchy z ∞) * g t) eta := by
      refine Integrable.mono' (g := fun t => (2 * |z.im|⁻¹) * ‖g t‖)
        (hgint.norm.const_mul _)
        (((F.measurable_leafCauchy.sub measurable_const).mul hgmeas).aestronglyMeasurable) ?_
      filter_upwards with t
      exact hbdd t
    have hintFull : Integrable (fun t => F.leafCauchy z t * g t) eta := by
      refine Integrable.mono' (g := fun t => |z.im|⁻¹ * ‖g t‖) (hgint.norm.const_mul _)
        ((F.measurable_leafCauchy.mul hgmeas).aestronglyMeasurable) ?_
      filter_upwards with t
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (F.norm_leafCauchy_le hz t) (norm_nonneg _)
    have hsub : ∫ t, (F.leafCauchy z t - F.leafCauchy z ∞) * g t ∂eta = 0 := by
      have hexpand : ∀ t : OnePoint ℝ, (F.leafCauchy z t - F.leafCauchy z ∞) * g t
          = F.leafCauchy z t * g t - F.leafCauchy z ∞ * g t := by
        intro t
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall hexpand),
        integral_sub hintFull (hgint.const_mul _), hcauchy z hz, integral_const_mul, hconst,
        mul_zero, sub_zero]
    rw [integral_onePoint_split eta hintDiff] at hsub
    have hinftyterm : (F.leafCauchy z (∞ : OnePoint ℝ) - F.leafCauchy z ∞) * g ∞ = 0 := by
      simp
    rw [hinftyterm, smul_zero, add_zero] at hsub
    have hchart : ∀ τ : ℝ, (F.leafCauchy z (τ : OnePoint ℝ) - F.leafCauchy z ∞) * gc τ
        = (-(F.c z ^ 2)⁻¹) * (gc τ * ((τ : ℂ) - F.quotient z)⁻¹) := by
      intro τ
      rw [F.leafCauchy_sub_infty hz hc hqim τ]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hchart), integral_const_mul] at hsub
    have hBne : (-(F.c z ^ 2)⁻¹) ≠ 0 := by
      simp [hc]
    have := mul_eq_zero.1 hsub
    rcases this with hzero | hzero
    · exact absurd hzero hBne
    · exact hzero
  -- the two open images of the Weyl pole map
  have hcLower : ∀ z ∈ lowerHalfPlaneSet, F.c z ≠ 0 := fun z hz => hcne z (ne_of_lt hz)
  have hcUpper : ∀ z ∈ upperHalfPlaneSet, F.c z ≠ 0 := fun z hz => hcne z (ne_of_gt hz)
  have hopenUp : IsOpen (F.quotient '' lowerHalfPlaneSet) :=
    F.isOpen_quotient_image isOpen_lowerHalfPlaneSet isPreconnected_lowerHalfPlaneSet
      ⟨-Complex.I, by simp [lowerHalfPlaneSet]⟩ hcLower
      (fun z hz => ne_of_gt (hup z hz))
  have hopenLow : IsOpen (F.quotient '' upperHalfPlaneSet) :=
    F.isOpen_quotient_image isOpen_upperHalfPlaneSet isPreconnected_upperHalfPlaneSet
      ⟨Complex.I, by simp [upperHalfPlaneSet]⟩ hcUpper
      (fun z hz => ne_of_lt (hlow z hz))
  have hmemUp : F.quotient (-Complex.I) ∈ F.quotient '' lowerHalfPlaneSet :=
    ⟨-Complex.I, by simp [lowerHalfPlaneSet], rfl⟩
  have hmemLow : F.quotient Complex.I ∈ F.quotient '' upperHalfPlaneSet :=
    ⟨Complex.I, by simp [upperHalfPlaneSet], rfl⟩
  have hsubUp : F.quotient '' lowerHalfPlaneSet ⊆ upperHalfPlaneSet := by
    rintro w ⟨z, hz, rfl⟩
    exact hup z hz
  have hsubLow : F.quotient '' upperHalfPlaneSet ⊆ lowerHalfPlaneSet := by
    rintro w ⟨z, hz, rfl⟩
    exact hlow z hz
  have hzeroUp : ∀ w ∈ F.quotient '' lowerHalfPlaneSet, densityCauchyTransform nu gc w = 0 := by
    rintro w ⟨z, hz, rfl⟩
    exact hpole z (ne_of_lt hz)
  have hzeroLow : ∀ w ∈ F.quotient '' upperHalfPlaneSet, densityCauchyTransform nu gc w = 0 := by
    rintro w ⟨z, hz, rfl⟩
    exact hpole z (ne_of_gt hz)
  have hchartzero : gc =ᵐ[nu] 0 :=
    density_eq_zero_of_transform_eq_zero_both hgcmeas hgcint hopenUp hopenLow hmemUp hmemLow
      hsubUp hsubLow hzeroUp hzeroLow
  -- transport back to the projective line
  have hnullChart : nu {τ : ℝ | gc τ ≠ 0} = 0 := by
    have := (MeasureTheory.ae_iff).1 hchartzero
    simpa using this
  have hinftyMass : (eta {(∞ : OnePoint ℝ)}).toReal • g ∞ = 0 := by
    have hsplit := integral_onePoint_split eta hgint
    rw [hconst] at hsplit
    have hzeroChart : ∫ τ : ℝ, g (τ : OnePoint ℝ) ∂nu = 0 := by
      rw [integral_congr_ae (show (fun τ : ℝ => g (τ : OnePoint ℝ)) =ᵐ[nu] 0 from hchartzero)]
      simp
    rw [hzeroChart, zero_add] at hsplit
    exact hsplit.symm
  refine (MeasureTheory.ae_iff).2 ?_
  have hSmeas : MeasurableSet {t : OnePoint ℝ | ¬ g t = 0} := by
    have : {t : OnePoint ℝ | ¬ g t = 0} = g ⁻¹' ({0}ᶜ) := by
      ext t
      simp
    rw [this]
    exact hgmeas (measurableSet_singleton (0 : ℂ)).compl
  have hcover : {t : OnePoint ℝ | ¬ g t = 0} ⊆
      (((↑) : ℝ → OnePoint ℝ) '' {τ : ℝ | gc τ ≠ 0}) ∪ {(∞ : OnePoint ℝ)} := by
    intro t ht
    induction t using OnePoint.rec with
    | infty => exact Or.inr rfl
    | coe x => exact Or.inl ⟨x, ht, rfl⟩
  have hchartnull : eta (((↑) : ℝ → OnePoint ℝ) '' {τ : ℝ | gc τ ≠ 0}) = 0 := by
    rw [← chartMeasure_apply eta {τ : ℝ | gc τ ≠ 0}]
    exact hnullChart
  by_cases hginf : g (∞ : OnePoint ℝ) = 0
  · have hcover' : {t : OnePoint ℝ | ¬ g t = 0} ⊆
        ((↑) : ℝ → OnePoint ℝ) '' {τ : ℝ | gc τ ≠ 0} := by
      intro t ht
      rcases hcover ht with h | h
      · exact h
      · exact absurd (by rw [show t = (∞ : OnePoint ℝ) from h]; exact hginf) ht
    exact measure_mono_null hcover' hchartnull
  · have hmassReal : (eta {(∞ : OnePoint ℝ)}).toReal = 0 := by
      rcases smul_eq_zero.1 hinftyMass with h | h
      · exact h
      · exact absurd h hginf
    have hmass : eta {(∞ : OnePoint ℝ)} = 0 :=
      (ENNReal.toReal_eq_zero_iff _).1 hmassReal |>.resolve_right (measure_ne_top eta _)
    refine measure_mono_null hcover ?_
    exact measure_union_null hchartnull hmass


end ClassicalAnalyticNevanlinnaCarrierFamily

end

end GaloisForLFunctions.HTGeometry

namespace HTGeometry

open MeasureTheory Complex Set
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
open scoped OnePoint

noncomputable section

variable {s : ℕ → ℝ}

/-- **Resolvent completeness for the constructed carrier family.**  For an indeterminate normalised
moment sequence, a parameter density annihilating the constant function and every leaf Cauchy
transform vanishes almost everywhere: the constants together with the conditional Cauchy data span
a dense subspace of the projective boundary. -/
theorem analyticNevCarrier_eq_zero_ae_of_annihilates_leafCauchy (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (eta : Measure (OnePoint ℝ)) [IsFiniteMeasure eta]
    {g : OnePoint ℝ → ℂ} (hgmeas : Measurable g) (hgint : Integrable g eta)
    (hconst : ∫ t, g t ∂eta = 0)
    (hcauchy : ∀ z : ℂ, z.im ≠ 0 →
      ∫ t, (analyticNevCarrierFamily h h0b h0).leafCauchy z t * g t ∂eta = 0) :
    g =ᵐ[eta] 0 :=
  (analyticNevCarrierFamily h h0b h0).eq_zero_ae_of_annihilates_leafCauchy
    (fun _ hz => nevBinf_ne_zero h h0b h0 hz)
    (analyticNevCarrierFamily_lowerMap h h0b h0)
    (fun _ hz => analyticNevCarrierFamily_quotient_im_neg h h0b h0 hz)
    eta hgmeas hgint hconst hcauchy

end

end HTGeometry
