import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormHasItsMixedJumpPairing
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicCutoffCommutatorHasABoundedKernel
import GaloisForLFunctions.HTGeometry.ReflectionSplitIntegral

/-!
# The exact logarithmic cutoff identity

The mixed jump pairing and a measure-preserving shear identify the bounded
Schur kernel with the commutator on the complete logarithmic form domain.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ENNReal InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

/-- The one-sided translation commutator of a physical cutoff. -/
def logarithmicCutoffTranslationCommutator {χ : ℝ → ℝ} (hm : Measurable χ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (t : ℝ) (f : RealLineL2) : RealLineL2 :=
  logarithmicCutoffMultiplier hm hM hb (logTranslationCLM t f) -
    logTranslationCLM t (logarithmicCutoffMultiplier hm hM hb f)

theorem logarithmicCutoffTranslationCommutator_coeFn {χ : ℝ → ℝ} (hm : Measurable χ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (t : ℝ) (f : RealLineL2) :
    (logarithmicCutoffTranslationCommutator hm hM hb t f : ℝ → ℂ) =ᵐ[volume]
      fun x => ((χ x - χ (x + t) : ℝ) : ℂ) * f (x + t) := by
  let P := logarithmicCutoffMultiplier hm hM hb
  have hshift := (logarithmicCutoffMultiplier_coeFn hm hM hb f).comp_tendsto
    (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae
  filter_upwards [Lp.coeFn_sub (P (logTranslationCLM t f)) (logTranslationCLM t (P f)),
    logarithmicCutoffMultiplier_coeFn hm hM hb (logTranslationCLM t f),
    logarithmicTranslation_coeFn t f, logarithmicTranslation_coeFn t (P f), hshift] with x hsub hP htf htP hPs
  change (P f) (x + t) = (χ (x + t) : ℂ) * f (x + t) at hPs
  change (P (logTranslationCLM t f) - logTranslationCLM t (P f)) x = _
  rw [hsub]
  simp only [Pi.sub_apply]
  rw [hP, htf, htP, hPs]
  push_cast
  ring

private theorem logarithmicCutoffKernel_translation_pair {χ : ℝ → ℝ} (hm : Measurable χ)
    {M : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (u v : RealLineL2) (t : ℝ) :
    (∫ x : ℝ, star (v x) * logarithmicCutoffKernel χ x (x + t) * u (x + t)) =
      (logReferenceLevyDensity |t| : ℂ) *
        inner ℂ v (logarithmicCutoffTranslationCommutator hm hM hb t u) := by
  rw [L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [logarithmicCutoffTranslationCommutator_coeFn hm hM hb t u] with x hx
  rw [hx, RCLike.inner_apply', starRingEnd_apply]
  unfold logarithmicCutoffKernel
  rw [show x - (x + t) = -t by ring, abs_neg]
  push_cast
  ring

/-- Shearing the absolutely integrable Schur pairing gives the full translation commutator. -/
private theorem logarithmicCutoffSchurKernel_pairing {χ : ℝ → ℝ} (hm : Measurable χ)
    {M Λ : ℝ} (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) (u v : RealLineL2) :
    Integrable (fun t : ℝ => (logReferenceLevyDensity |t| : ℂ) *
      inner ℂ v (logarithmicCutoffTranslationCommutator hm hM hb t u)) ∧
    inner ℂ v ((logarithmicCutoffSchurKernel hm hΛ hlip).op u) =
      ∫ t : ℝ, (logReferenceLevyDensity |t| : ℂ) *
        inner ℂ v (logarithmicCutoffTranslationCommutator hm hM hb t u) := by
  let k := logarithmicCutoffSchurKernel hm hΛ hlip
  have hj : Integrable (fun p : ℝ × ℝ =>
      star (v p.1) * logarithmicCutoffKernel χ p.1 (p.1 + p.2) * u (p.1 + p.2))
      ((volume : Measure ℝ).prod volume) :=
    (measurePreserving_prod_add volume volume).integrable_comp_of_integrable
      (k.integrable_triple u v)
  constructor
  · refine hj.integral_prod_right.congr (Eventually.of_forall fun t => ?_)
    exact logarithmicCutoffKernel_translation_pair hm hM hb u v t
  · rw [k.inner_op]
    calc
      _ = ∫ x : ℝ, ∫ t : ℝ, star (v x) * logarithmicCutoffKernel χ x (x + t) * u (x + t) := by
        apply integral_congr_ae
        filter_upwards with x
        exact (integral_add_left_eq_self
          (fun y : ℝ => star (v x) * logarithmicCutoffKernel χ x y * u y) x).symm
      _ = ∫ t : ℝ, ∫ x : ℝ, star (v x) * logarithmicCutoffKernel χ x (x + t) * u (x + t) :=
        integral_integral_swap hj
      _ = _ := integral_congr_ae (Eventually.of_forall fun t =>
        logarithmicCutoffKernel_translation_pair hm hM hb u v t)

private theorem inner_translationLoss_cutoff {χ : ℝ → ℝ} (hm : Measurable χ) {M : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (u v : RealLineL2) (t : ℝ) :
    inner ℂ (logTranslationCLM t v - v)
        (logTranslationCLM t (logarithmicCutoffMultiplier hm hM hb u) -
          logarithmicCutoffMultiplier hm hM hb u) -
      inner ℂ (logTranslationCLM t (logarithmicCutoffMultiplier hm hM hb v) -
          logarithmicCutoffMultiplier hm hM hb v) (logTranslationCLM t u - u) =
    inner ℂ v (logarithmicCutoffTranslationCommutator hm hM hb t u +
      logarithmicCutoffTranslationCommutator hm hM hb (-t) u) := by
  let P := logarithmicCutoffMultiplier hm hM hb
  change inner ℂ (logTranslationCLM t v - v) (logTranslationCLM t (P u) - P u) -
    inner ℂ (logTranslationCLM t (P v) - P v) (logTranslationCLM t u - u) =
      inner ℂ v ((P (logTranslationCLM t u) - logTranslationCLM t (P u)) +
        (P (logTranslationCLM (-t) u) - logTranslationCLM (-t) (P u)))
  have hiso (f g : RealLineL2) :
      inner ℂ (logTranslationCLM t f) (logTranslationCLM t g) = inner ℂ f g :=
    (MellinL2.additiveTranslationUnitary t).inner_map_map _ _
  simp only [inner_sub_left, inner_sub_right, inner_add_right]
  rw [hiso v (P u), hiso (P v) u,
    inner_logTranslationCLM t v (P u), inner_logTranslationCLM t (P v) u]
  rw [inner_logarithmicCutoffMultiplier hm hM hb v u,
    inner_logarithmicCutoffMultiplier hm hM hb v (logTranslationCLM t u),
    inner_logarithmicCutoffMultiplier hm hM hb v (logTranslationCLM (-t) u)]
  ring

/-- The bounded literal kernel is exactly the complete-domain logarithmic cutoff commutator. -/
theorem logarithmicFullForm_cutoff_identity {χ : ℝ → ℝ} (hm : Measurable χ) {M Λ : ℝ}
    (hM : 0 ≤ M) (hb : ∀ x, |χ x| ≤ M) (hΛ : 0 ≤ Λ)
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|) {u v : RealLineL2}
    (hu : HasLogarithmicEnergy u) (hv : HasLogarithmicEnergy v) :
    logarithmicFullForm v (logarithmicCutoffMultiplier hm hM hb u) -
      logarithmicFullForm (logarithmicCutoffMultiplier hm hM hb v) u =
        inner ℂ v ((logarithmicCutoffSchurKernel hm hΛ hlip).op u) := by
  let P := logarithmicCutoffMultiplier hm hM hb
  have hPu := hasLogarithmicEnergy_cutoff hm hM hb hΛ hlip hu
  have hPv := hasLogarithmicEnergy_cutoff hm hM hb hΛ hlip hv
  obtain ⟨hi, he⟩ := logarithmicCutoffSchurKernel_pairing hm hM hb hΛ hlip u v
  have hpair : inner ℂ v ((logarithmicCutoffSchurKernel hm hΛ hlip).op u) =
      ∫ t in Ioi (0 : ℝ), (logReferenceLevyDensity t : ℂ) *
        (inner ℂ (logTranslationCLM t v - v) (logTranslationCLM t (P u) - P u) -
          inner ℂ (logTranslationCLM t (P v) - P v) (logTranslationCLM t u - u)) := by
    rw [he, integral_eq_add_reflect hi,
      ← integral_add hi.integrableOn hi.comp_neg.integrableOn]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (0 : ℝ) < t at ht
    dsimp only
    rw [abs_neg, abs_of_pos ht, inner_translationLoss_cutoff hm hM hb u v t,
      inner_add_right]
    ring
  rw [logarithmicFullForm_eq_inner_add_jump hv hPu,
    logarithmicFullForm_eq_inner_add_jump hPv hu, hpair,
    inner_logarithmicCutoffMultiplier hm hM hb v u]
  have hsub := integral_sub (integrable_logarithmicJumpMixed hv hPu)
    (integrable_logarithmicJumpMixed hPv hu)
  simp_rw [mul_sub]
  rw [hsub]
  ring

#print axioms logarithmicFullForm_cutoff_identity
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
