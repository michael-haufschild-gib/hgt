import GaloisForLFunctions.RHTower.CCMActualHeadCoherentQuantileGammaProducer

/-!
# Support projection of the coherent quantile field

The increment `U_r f - f` of an aperture-supported vector lies in the union of
the aperture and its translate. Cutting the complete coherent field to this
union preserves its pairing with the increment. Orthogonal decomposition
removes exactly the squared norm of the invisible part, after all prime and
terminal vectors have been added.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct

noncomputable section
namespace RHTower

/-- The union supporting an aperture vector and its translated copy. -/
def ccmIncrementSupport (a : SuzukiPositiveAperture) (r : ℝ) : Set ℝ :=
  centralInterval a.1 ∪ (fun x : ℝ => x + r) ⁻¹' centralInterval a.1

theorem measurableSet_ccmIncrementSupport (a : SuzukiPositiveAperture) (r : ℝ) :
    MeasurableSet (ccmIncrementSupport a r) :=
  (measurableSet_centralInterval a.1).union
    ((measurableSet_centralInterval a.1).preimage (measurable_id.add_const r))

/-- Physical support projection, applied only after the coherent sum is formed. -/
def ccmIncrementSupportProjection (a : SuzukiPositiveAperture) (r : ℝ) :
    SoninL2 →L[ℂ] SoninL2 :=
  indicatorCutoff (ccmIncrementSupport a r) (measurableSet_ccmIncrementSupport a r)

private theorem translation_ae (r : ℝ) (g : SoninL2) :
    (logTranslationCLM r g : ℝ → ℂ) =ᵐ[volume] fun x => g (x + r) :=
  (Lp.coeFn_compMeasurePreserving g
    (MellinL2.realTranslation_measurePreserving r)).trans
      (Eventually.of_forall fun _ => rfl)

private theorem translated_cutoff_ae (a : SuzukiPositiveAperture) (r : ℝ) (g : SoninL2) :
    (logTranslationCLM r (indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (logTranslationCLM (-r) g)) : ℝ → ℂ)
      =ᵐ[volume] ((fun x : ℝ => x + r) ⁻¹' centralInterval a.1).indicator g := by
  have ht := (MellinL2.realTranslation_measurePreserving r).quasiMeasurePreserving.tendsto_ae
  filter_upwards [translation_ae r (indicatorCutoff (centralInterval a.1)
      (measurableSet_centralInterval a.1) (logTranslationCLM (-r) g)),
    ht.eventually (indicatorCutoff_ae (centralInterval a.1)
      (measurableSet_centralInterval a.1) (logTranslationCLM (-r) g)),
    ht.eventually (translation_ae (-r) g)] with x h1 h2 h3
  rw [h1]
  change indicatorCutoff _ _ _ (x + r) = _ at h2
  rw [h2]
  change logTranslationCLM (-r) g (x + r) = g (x + r + -r) at h3
  change (centralInterval a.1).indicator (fun y => logTranslationCLM (-r) g y) (x+r) =
    ((fun y : ℝ => y+r) ⁻¹' centralInterval a.1).indicator (fun y => g y) x
  by_cases hx : x + r ∈ centralInterval a.1
  · rw [indicator_of_mem hx, indicator_of_mem (show x ∈
      ((fun y : ℝ => y+r) ⁻¹' centralInterval a.1) from hx), h3]
    congr 1
    ring
  · rw [indicator_of_notMem hx, indicator_of_notMem (show x ∉
      ((fun y : ℝ => y+r) ⁻¹' centralInterval a.1) from hx)]

private theorem projection_formula (a : SuzukiPositiveAperture) (r : ℝ) (g : SoninL2) :
    let P := indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
    let Q := logTranslationCLM r (P (logTranslationCLM (-r) g))
    ccmIncrementSupportProjection a r g = P g + Q - P Q := by
  let P := indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
  let Q := logTranslationCLM r (P (logTranslationCLM (-r) g))
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (ccmIncrementSupport a r)
      (measurableSet_ccmIncrementSupport a r) g,
    indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) g,
    translated_cutoff_ae a r g,
    indicatorCutoff_ae (centralInterval a.1) (measurableSet_centralInterval a.1) Q,
    Lp.coeFn_sub (P g + Q) (P Q), Lp.coeFn_add (P g) Q] with x hp h0 hq hpq hs ha
  change ccmIncrementSupportProjection a r g x = (P g + Q - P Q) x
  rw [hs]
  change _ = (P g + Q) x - (P Q) x
  rw [ha]
  change _ = (P g) x + Q x - (P Q) x
  change P Q x = _ at hpq
  change P g x = _ at h0
  change Q x = _ at hq
  change ccmIncrementSupportProjection a r g x = _ at hp
  rw [hp, hpq, h0]
  by_cases hx : x ∈ centralInterval a.1 <;>
    by_cases hy : x + r ∈ centralInterval a.1 <;>
    simp [ccmIncrementSupport, hx, hy, hq]

private theorem continuous_projection_expression {E : Type*}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    (U : ℝ × E → E) (P : E → E) (hU : Continuous U) (hP : Continuous P) :
    Continuous fun p : ℝ × E => P p.2 + U (p.1, P (U (-p.1, p.2))) -
      P (U (p.1, P (U (-p.1, p.2)))) := by
  have hback : Continuous fun p : ℝ × E => U (-p.1, p.2) :=
    hU.comp (continuous_fst.neg.prodMk continuous_snd)
  have hQ : Continuous fun p : ℝ × E => U (p.1, P (U (-p.1, p.2))) :=
    hU.comp (continuous_fst.prodMk (hP.comp hback))
  exact ((hP.comp continuous_snd).add hQ).sub (hP.comp hQ)

theorem continuous_ccmIncrementSupportProjection_joint (a : SuzukiPositiveAperture) :
    Continuous fun p : ℝ × SoninL2 => ccmIncrementSupportProjection a p.1 p.2 := by
  have h := continuous_projection_expression
    (fun p : ℝ × SoninL2 => logTranslationCLM p.1 p.2)
    (indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1))
    continuous_logTranslationCLM_joint
    (indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)).continuous
  exact h.congr (fun p => (projection_formula a p.1 p.2).symm)

theorem ccmIncrementSupportProjection_increment (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (r : ℝ) :
    ccmIncrementSupportProjection a r (logTranslationCLM r f.1 - f.1) =
      logTranslationCLM r f.1 - f.1 := by
  have hf := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hf
  have hft := (MellinL2.realTranslation_measurePreserving r).quasiMeasurePreserving.tendsto_ae.eventually hf
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (ccmIncrementSupport a r)
      (measurableSet_ccmIncrementSupport a r) (logTranslationCLM r f.1 - f.1),
    Lp.coeFn_sub (logTranslationCLM r f.1) f.1, translation_ae r f.1, hf, hft]
    with x hp hs ht hf hft
  change ccmIncrementSupportProjection a r _ x = _ at hp ⊢
  rw [hp]
  by_cases hx : x ∈ ccmIncrementSupport a r
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx, hs]
    change 0 = logTranslationCLM r f.1 x - f.1 x
    rw [ht]
    have h0 : x ∉ centralInterval a.1 := fun h => hx (Or.inl h)
    have h1 : x + r ∉ centralInterval a.1 := fun h => hx (Or.inr h)
    change f.1 (x + r) = (centralInterval a.1).indicator _ (x + r) at hft
    rw [hf, hft, indicator_of_notMem h0, indicator_of_notMem h1, sub_self]

theorem inner_increment_ccmIncrementSupportProjection (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (r : ℝ) (g : SoninL2) :
    inner ℂ (logTranslationCLM r f.1 - f.1) (ccmIncrementSupportProjection a r g) =
      inner ℂ (logTranslationCLM r f.1 - f.1) g := by
  have h := indicatorCutoff_symmetric (ccmIncrementSupport a r)
    (measurableSet_ccmIncrementSupport a r) (logTranslationCLM r f.1 - f.1) g
  change inner ℂ (ccmIncrementSupportProjection a r _) g = _ at h
  rw [ccmIncrementSupportProjection_increment] at h
  exact h.symm

theorem norm_sq_ccmIncrementSupportProjection (a : SuzukiPositiveAperture)
    (r : ℝ) (g : SoninL2) :
    ‖g‖ ^ 2 = ‖ccmIncrementSupportProjection a r g‖ ^ 2 +
      ‖g - ccmIncrementSupportProjection a r g‖ ^ 2 := by
  unfold ccmIncrementSupportProjection
  rw [indicatorCutoff_eq_physicalForbidden_starProjection]
  simpa only [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply] using
    (physicalForbidden (ccmIncrementSupport a r)
      (measurableSet_ccmIncrementSupport a r)).norm_sq_eq_add_norm_sq_starProjection g

/-- The terminal translation is invisible on the nonnegative displacement half-line. -/
theorem ccmIncrementSupportProjection_terminal_shift (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (r : ℝ) :
    ccmIncrementSupportProjection a (max r 0) (logTranslationCLM (-(2 * a.1)) f.1) = 0 := by
  have hf := indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) f.1
  rw [indicatorCutoff_suzukiApertureHilbert] at hf
  have hft := (MellinL2.realTranslation_measurePreserving (-(2*a.1))).quasiMeasurePreserving.tendsto_ae.eventually hf
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae (ccmIncrementSupport a (max r 0))
      (measurableSet_ccmIncrementSupport a (max r 0))
      (logTranslationCLM (-(2*a.1)) f.1),
    translation_ae (-(2*a.1)) f.1, hft,
    volume.ae_ne a.1,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := volume)] with x hp ht hf hx h0
  change ccmIncrementSupportProjection a (max r 0) _ x = _ at hp ⊢
  rw [hp, h0]
  change (ccmIncrementSupport a (max r 0)).indicator _ x = (0 : ℂ)
  by_cases hmem : x ∈ ccmIncrementSupport a (max r 0)
  · rw [indicator_of_mem hmem, ht]
    change f.1 (x + -(2*a.1)) =
      (centralInterval a.1).indicator _ (x + -(2*a.1)) at hf
    have hout : x + -(2*a.1) ∉ centralInterval a.1 := by
      intro hin
      have hlo : -a.1 ≤ x + -(2*a.1) := hin.1
      have hhi : x ≤ a.1 := by
        rcases hmem with hmem | hmem
        · exact hmem.2
        · have := le_max_right r (0 : ℝ)
          have := hmem.2
          linarith
      exact hx (by linarith)
    rw [hf, indicator_of_notMem hout]
  · rw [indicator_of_notMem hmem]

end RHTower
