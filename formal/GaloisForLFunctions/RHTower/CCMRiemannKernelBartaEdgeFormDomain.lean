import GaloisForLFunctions.RHTower.CCMRiemannKernelBartaLayerBounds
import GaloisForLFunctions.RHTower.CCMFullGroundZeroSideEigen
import GaloisForLFunctions.RHTower.SoninStripEvaluator

/-!
# The edge bound on the whole form domain

`exists_bartaEdge_bound` bounds `|Q_{b+3}(v, T_b)|` by `C(1+b) Φ(b-2w) ∫|v|` for smooth interior
sources `v`. Both sides are continuous on the form domain:
* `Q(·, T_b)` is an inner product with the form representer of `T_b`;
* `x ↦ ∫|x|` is `√(2a)`-Lipschitz in the aperture norm (`integral_norm_le_sqrt_measure`).

Smooth interior sources are dense (`denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector`),
so the bound holds for every vector of the form domain (`exists_bartaEdge_bound_formDomain`).
-/

open Complex MeasureTheory Set Filter Topology

namespace RHTower

open RHTower.CCMRealRootedGround RHTower.CCMFullGroundEigen

noncomputable section

/-- The `L¹` mass of the time function on the aperture. -/
def apertureMass (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  ∫ t in centralInterval a.1, ‖((f : SoninL2) : ℝ → ℂ) t‖

theorem integral_norm_timeRep_eq_apertureMass (a : SuzukiPositiveAperture)
    (x : CCMArchimedeanFormDomain a) :
    ∫ t, ‖timeRep a x t‖ = apertureMass a (ccmArchimedeanFormToAperture a x) := by
  unfold apertureMass timeRep
  rw [← integral_indicator (measurableSet_centralInterval a.1)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  exact norm_indicator_eq_indicator_norm _ t

theorem abs_apertureMass_sub_le (a : SuzukiPositiveAperture) (f g : suzukiApertureHilbert a) :
    |apertureMass a f - apertureMass a g| ≤ Real.sqrt (2 * a.1) * ‖f - g‖ := by
  have hfin : IsFiniteMeasure (volume.restrict (centralInterval a.1)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, centralInterval]
    exact measure_Icc_lt_top
  have hintC : ∀ h : SoninL2, IntegrableOn (h : ℝ → ℂ) (centralInterval a.1) := fun h =>
    ((Lp.memLp h).restrict _).integrable (by norm_num)
  have hint : ∀ h : SoninL2, IntegrableOn (fun t => ‖(h : ℝ → ℂ) t‖) (centralInterval a.1) :=
    fun h => (hintC h).norm
  have hsub := Lp.coeFn_sub (f : SoninL2) (g : SoninL2)
  have hkey : ∫ t in centralInterval a.1, ‖((f : SoninL2) : ℝ → ℂ) t - ((g : SoninL2) : ℝ → ℂ) t‖ ≤
      Real.sqrt (2 * a.1) * ‖f - g‖ := by
    have h := integral_norm_le_sqrt_measure a.property ((f : SoninL2) - (g : SoninL2))
    have hfg : ‖((f : SoninL2) - (g : SoninL2))‖ = ‖f - g‖ := by
      rw [← Submodule.coe_sub, Submodule.coe_norm]
    rw [hfg] at h
    refine le_trans (le_of_eq ?_) h
    refine setIntegral_congr_ae (measurableSet_centralInterval a.1) ?_
    filter_upwards [hsub] with t ht _
    rw [ht, Pi.sub_apply]
  unfold apertureMass
  rw [← integral_sub (hint f) (hint g)]
  refine (abs_integral_le_integral_abs).trans (le_trans ?_ hkey)
  refine setIntegral_mono_on ((hint f).sub (hint g)).abs ((hintC f).sub (hintC g)).norm
    (measurableSet_centralInterval a.1) fun t _ => abs_norm_sub_norm_le _ _

theorem continuous_apertureMass (a : SuzukiPositiveAperture) : Continuous (apertureMass a) := by
  refine LipschitzWith.continuous (K := (Real.sqrt (2 * a.1)).toNNReal) ?_
  refine LipschitzWith.of_dist_le_mul fun f g => ?_
  rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ (Real.sqrt_nonneg _)]
  exact abs_apertureMass_sub_le a f g

theorem integral_norm_timeRep_toCCMFormVector (a : SuzukiPositiveAperture)
    (v : CCMComplexSmoothInteriorSource a) :
    ∫ t, ‖timeRep a v.toCCMFormVector t‖ = ∫ t, ‖v t‖ := by
  refine integral_congr_ae ?_
  filter_upwards [v.toCCMFormVector_physical_coeFn] with t ht
  unfold timeRep
  by_cases hmem : t ∈ centralInterval a.1
  · rw [indicator_of_mem hmem, ht]
  · rw [indicator_of_notMem hmem, norm_zero]
    have hv : v t = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hts
      apply hmem
      exact Ioo_subset_Icc_self (v.tsupport_subset hts)
    rw [hv, norm_zero]

/-- A bound `|Q(v, T)| ≤ K ∫|v|` on smooth interior sources extends to the whole form domain. -/
theorem norm_ccmRestrictedWeilForm_le_of_smooth (a : SuzukiPositiveAperture)
    (T : CCMComplexSmoothInteriorSource a) {K : ℝ}
    (hbound : ∀ v : CCMComplexSmoothInteriorSource a,
      ‖ccmRestrictedWeilForm a v.toCCMFormVector T.toCCMFormVector‖ ≤ (∫ t, ‖v t‖) * K)
    (x : CCMArchimedeanFormDomain a) :
    ‖ccmRestrictedWeilForm a x T.toCCMFormVector‖ ≤ (∫ t, ‖timeRep a x t‖) * K := by
  have hcontQ : Continuous fun y : CCMArchimedeanFormDomain a =>
      ‖ccmRestrictedWeilForm a y T.toCCMFormVector‖ := by
    have heq : (fun y : CCMArchimedeanFormDomain a => ccmRestrictedWeilForm a y T.toCCMFormVector) =
        fun y => inner ℂ ((ccmArchimedeanFormToAperture a y : suzukiApertureHilbert a) : SoninL2)
          (formRepresenter a T) := by
      funext y; exact ccmRestrictedWeilForm_toCCMFormVector_eq a y T
    have hc : Continuous fun y : CCMArchimedeanFormDomain a =>
        ccmRestrictedWeilForm a y T.toCCMFormVector := by
      rw [heq]
      exact continuous_inner.comp (((continuous_subtype_val.comp
        (ccmArchimedeanFormToAperture a).continuous)).prodMk continuous_const)
    exact hc.norm
  have hcontN : Continuous fun y : CCMArchimedeanFormDomain a => ∫ t, ‖timeRep a y t‖ := by
    have heq : (fun y : CCMArchimedeanFormDomain a => ∫ t, ‖timeRep a y t‖) =
        fun y => apertureMass a (ccmArchimedeanFormToAperture a y) := by
      funext y; exact integral_norm_timeRep_eq_apertureMass a y
    rw [heq]
    exact (continuous_apertureMass a).comp (ccmArchimedeanFormToAperture a).continuous
  have hclosed : IsClosed {y : CCMArchimedeanFormDomain a |
      ‖ccmRestrictedWeilForm a y T.toCCMFormVector‖ ≤ (∫ t, ‖timeRep a y t‖) * K} :=
    isClosed_le hcontQ (hcontN.mul continuous_const)
  refine (denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).induction_on
    (p := fun y => ‖ccmRestrictedWeilForm a y T.toCCMFormVector‖ ≤ (∫ t, ‖timeRep a y t‖) * K)
    x hclosed fun v => ?_
  show ‖ccmRestrictedWeilForm a v.toCCMFormVector T.toCCMFormVector‖ ≤
    (∫ t, ‖timeRep a v.toCCMFormVector t‖) * K
  rw [integral_norm_timeRep_toCCMFormVector]
  exact hbound v

/-- **The edge bound on the form domain.** -/
theorem exists_bartaEdge_bound_formDomain : ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℝ) (hb : 1 ≤ b)
    (x : CCMArchimedeanFormDomain (bartaAperture b hb)),
    ‖ccmRestrictedWeilForm (bartaAperture b hb) x (bartaLayerAt b hb).toCCMFormVector‖ ≤
      (∫ t, ‖timeRep (bartaAperture b hb) x t‖) * (bartaEdge b * (C * (1 + b))) := by
  obtain ⟨C, hC, hbound⟩ := exists_bartaEdge_bound
  exact ⟨C, hC, fun b hb x =>
    norm_ccmRestrictedWeilForm_le_of_smooth _ _ (hbound b hb) x⟩

end

end RHTower
