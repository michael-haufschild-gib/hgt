import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionsHaveOnlyPresentationRadicals
import GaloisForLFunctions.BiScaleUncertainty.ProbeParsevalLaw
import GaloisForLFunctions.RHTower.WeilFullConeSpectralConsistency

/-!
# A locally bounded kernel for the complete mixed Weil form

Fixing one smooth compact test turns the full Weil pairing into integration
against a continuous source kernel. Its construction retains both pole moments,
the prime comb and the Gamma term. On a fixed support window the pairing is
therefore bounded by the other test's absolute mass, independently of its
derivatives or any coefficient presentation.
-/

open MeasureTheory Set
open Zeta23 RHTower RHTower.WeilSpectral

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri

/-- Reflection of an actual real test. -/
def reflectedRealTest (g : realTests) : realTests :=
  ⟨fun u => g.1 (-u), g.2.1.comp contDiff_neg,
    g.2.2.comp_homeomorph (Homeomorph.neg ℝ)⟩

/-- Compact real C² tests have the absolute Gamma integrability required by source averaging. -/
theorem admissible_cx_realTest (g : realTests) : Admissible (cx g.1) := by
  obtain ⟨R, hR⟩ := exists_abs_bound_of_hasCompactSupport (cx_hasCompactSupport g.2.2)
  refine ⟨(cx_contDiff g.2.1).continuous, cx_hasCompactSupport g.2.2, ?_⟩
  exact BiScaleUncertainty.ChebyshevGauge.integrable_paperFT_mul_gammaBracket g.2.1
    (fun u hu => by
      by_contra hne
      exact (not_le.mpr hu) (hR u (by simpa only [cx, ne_eq, Complex.ofReal_eq_zero] using hne)))

/-- The actual source kernel dual to one real test. -/
def weilSourceKernel (g : realTests) (u : ℝ) : ℂ :=
  weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
    (transl u (cx (reflectedRealTest g).1))

theorem continuous_weilSourceKernel (g : realTests) : Continuous (weilSourceKernel g) := by
  let k := cx (reflectedRealTest g).1
  have hk : Admissible k := admissible_cx_realTest (reflectedRealTest g)
  exact ((continuous_polePart_transl k).sub
    (continuous_primePart_transl _ hk.cont hk.supp)).add
    (continuous_archPart_transl hk)

/-- Exact source representation of the mixed completed pairing. -/
theorem realWeilForm_eq_sourceKernel (p g : realTests) :
    realWeilForm p g = (∫ u, (p.1 u : ℂ) * weilSourceKernel g u).re := by
  have hcorr : EF.weilTest (cx p.1) (cx g.1) =
      average (cx p.1) (cx (reflectedRealTest g).1) 0 := by
    funext x
    rw [WeilSpectral.weilTest_apply]
    change (∫ u, (p.1 u : ℂ) * (starRingEnd ℂ) (g.1 (u - x) : ℂ)) =
      ∫ u, (p.1 u : ℂ) * (g.1 (-(x - 0 - u)) : ℂ)
    apply integral_congr_ae
    filter_upwards [] with u
    simp only [sub_zero, neg_sub, Complex.conj_ofReal]
  change (weilFullFunctional _ (EF.weilTest (cx p.1) (cx g.1))).re = _
  rw [hcorr, weilFullFunctional_average _ (cx_contDiff p.2.1).continuous
    (cx_hasCompactSupport p.2.2) (admissible_cx_realTest (reflectedRealTest g))]
  simp only [zero_add, cx, weilSourceKernel]

/-- On a fixed window the full source pairing is uniformly bounded by absolute test mass. -/
theorem exists_sourceKernel_window_bound (g : realTests) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : realTests,
      (∀ u, R < |u| → p.1 u = 0) →
      |realWeilForm p g| ≤ C * ∫ u, |p.1 u| := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (-|R|) |R|)).exists_bound_of_continuousOn
    (continuous_weilSourceKernel g).continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp
  have hpi : Integrable p.1 := p.2.1.continuous.integrable_of_hasCompactSupport p.2.2
  have hki : Integrable (fun u => (p.1 u : ℂ) * weilSourceKernel g u) :=
    integrable_mul_of_continuous (cx_contDiff p.2.1).continuous
      (cx_hasCompactSupport p.2.2) (continuous_weilSourceKernel g)
  have hbound (u : ℝ) :
      ‖(p.1 u : ℂ) * weilSourceKernel g u‖ ≤ max C 0 * |p.1 u| := by
    by_cases hu : p.1 u = 0
    · simp only [hu, Complex.ofReal_zero, zero_mul, norm_zero, abs_zero, mul_zero, le_refl]
    · have huR : |u| ≤ |R| := (le_of_not_gt fun h => hu (hp u h)).trans (le_abs_self R)
      have hCu := (hC u (abs_le.mp huR)).trans (le_max_left C 0)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right hCu (abs_nonneg _)
  rw [realWeilForm_eq_sourceKernel]
  calc
    |(∫ u, (p.1 u : ℂ) * weilSourceKernel g u).re| ≤
        ‖∫ u, (p.1 u : ℂ) * weilSourceKernel g u‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ u, ‖(p.1 u : ℂ) * weilSourceKernel g u‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u, max C 0 * |p.1 u| := integral_mono hki.norm (hpi.abs.const_mul _) hbound
    _ = max C 0 * ∫ u, |p.1 u| := integral_const_mul _ _

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.realWeilForm_eq_sourceKernel
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.exists_sourceKernel_window_bound
