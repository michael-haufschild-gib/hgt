import GaloisForLFunctions.SignedArithmeticHodgeTheory.BoundedWindowsAdmitSourceCompatibleScaleTransport
import GaloisForLFunctions.RHTower.CHMDFixedApertureQuotientLanding
import GaloisForLFunctions.RHTower.CHMDShiftedFourierReadout
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Literal scale transport on completed source apertures

Translation of compact arithmetic tests extends to the existing completed
aperture spaces. The extension uses the original graph norm and the actual
source map. Its bounds depend on the source aperture and translation range.
-/

noncomputable section

open Set
open scoped InnerProductSpace
open RHTower RHTower.CHMDDoobGraph RHTower.CHMDPolar
open GaloisForLFunctions.RHTower

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory

open ArithmeticCastelnuovoSeveri ArithmeticIndexDescent

/-- A smooth aperture source as a literal compact arithmetic test. -/
def apertureSourceTest {a : ℝ} (u : SuzukiRestrictedWeilCore a) : realTests :=
  ⟨u, u.smooth.of_le (WithTop.coe_le_coe.mpr le_top), u.hasCompactSupport⟩

private theorem apertureSourceTest_support {a : ℝ} (u : SuzukiRestrictedWeilCore a) :
    ∀ x, a < |x| → (apertureSourceTest u).1 x = 0 := by
  intro x hx
  by_contra h
  have hs := u.support_subset_aperture h
  exact (not_lt_of_ge (abs_lt.mpr hs).le) hx

private theorem translatedSourceGraph_add (f g : realTests) (t : ℝ) :
    translatedSourceGraph (f + g) t = translatedSourceGraph f t + translatedSourceGraph g t := by
  change realTestGraphLift (sourceTranslate t f + sourceTranslate t g) = _
  exact realTestGraphLift_add _ _

private theorem translatedSourceGraph_sub (f g : realTests) (t : ℝ) :
    translatedSourceGraph (f - g) t = translatedSourceGraph f t - translatedSourceGraph g t := by
  change realTestGraphLift (sourceTranslate t f - sourceTranslate t g) = _
  exact realTestGraphLift_sub _ _

private theorem translatedSourceGraph_smul (c : ℝ) (f : realTests) (t : ℝ) :
    translatedSourceGraph (c • f) t = c • translatedSourceGraph f t := by
  change realTestGraphLift (c • sourceTranslate t f) = _
  exact realTestGraphLift_smul _ _

private theorem translatedSourceGraph_congr_lift (R t : ℝ) (f g : realTests)
    (hf : ∀ u, R < |u| → f.1 u = 0) (hg : ∀ u, R < |u| → g.1 u = 0)
    (he : realTestGraphLift f = realTestGraphLift g) :
    translatedSourceGraph f t = translatedSourceGraph g t := by
  obtain ⟨C, _, hC⟩ := exists_boundedWindow_scaleTransport R |t|
  have hsupport : ∀ u, R < |u| → (f - g).1 u = 0 := by
    intro u hu
    change f.1 u - g.1 u = 0
    rw [hf u hu, hg u hu, sub_self]
  have h := hC (f - g) t hsupport le_rfl
  rw [translatedSourceGraph_sub, realTestGraphLift_sub, he, sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))))

private def apertureRepresentative (a : SuzukiPositiveAperture) (p : apertureGraphCore a) :
    realTests := apertureSourceTest (Classical.choose p.property)

private theorem apertureRepresentative_lift (a : SuzukiPositiveAperture)
    (p : apertureGraphCore a) : realTestGraphLift (apertureRepresentative a p) = p :=
  (Classical.choose_spec p.property).symm

private theorem apertureRepresentative_support (a : SuzukiPositiveAperture)
    (p : apertureGraphCore a) :
    ∀ u, a.1 < |u| → (apertureRepresentative a p).1 u = 0 :=
  apertureSourceTest_support _

private def apertureCoreScaleLinear (a : SuzukiPositiveAperture) (t : ℝ) :
    apertureGraphCore a →ₗ[ℝ] SourceGraph where
  toFun p := translatedSourceGraph (apertureRepresentative a p) t
  map_add' p q := by
    rw [← translatedSourceGraph_add]
    apply translatedSourceGraph_congr_lift a.1 t
      _ _ (apertureRepresentative_support a (p + q))
    · intro u hu
      change (apertureRepresentative a p).1 u + (apertureRepresentative a q).1 u = 0
      rw [apertureRepresentative_support a p u hu,
        apertureRepresentative_support a q u hu, add_zero]
    · simp only [realTestGraphLift_add, apertureRepresentative_lift]
  map_smul' c p := by
    change translatedSourceGraph (apertureRepresentative a (c • p)) t =
      c • translatedSourceGraph (apertureRepresentative a p) t
    rw [← translatedSourceGraph_smul]
    apply translatedSourceGraph_congr_lift a.1 t
      _ _ (apertureRepresentative_support a (c • p))
    · intro u hu
      change c * (apertureRepresentative a p).1 u = 0
      rw [apertureRepresentative_support a p u hu, mul_zero]
    · simp only [realTestGraphLift_smul, apertureRepresentative_lift]

private theorem apertureCoreScaleLinear_bound (a : SuzukiPositiveAperture) (t : ℝ) :
    ∃ C : ℝ, ∀ p : apertureGraphCore a, ‖apertureCoreScaleLinear a t p‖ ≤ C * ‖p‖ := by
  obtain ⟨C, hC, hbound⟩ := exists_boundedWindow_scaleTransport a.1 |t|
  refine ⟨Real.sqrt C, fun p => ?_⟩
  have h := hbound (apertureRepresentative a p) t (apertureRepresentative_support a p) le_rfl
  rw [apertureRepresentative_lift] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul hC.le, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at hs
  exact hs

private def apertureCoreScale (a : SuzukiPositiveAperture) (t : ℝ) :
    apertureGraphCore a →L[ℝ] SourceGraph :=
  (apertureCoreScaleLinear a t).mkContinuous
    (Classical.choose (apertureCoreScaleLinear_bound a t))
    (Classical.choose_spec (apertureCoreScaleLinear_bound a t))

private def apertureCoreEmbedding (a : SuzukiPositiveAperture) :
    apertureGraphCore a →L[ℝ] apertureGraphCompletion a :=
  (apertureGraphCoreInclusion a).mkContinuous 1 (fun p => by
    change ‖p‖ ≤ 1 * ‖p‖
    rw [one_mul])

private theorem apertureCoreEmbedding_isometry (a : SuzukiPositiveAperture) :
    Isometry (apertureCoreEmbedding a) := fun _ _ => rfl

/-- Translation on a completed aperture, with the original complete graph as target. -/
def apertureScaleTransport (a : SuzukiPositiveAperture) (t : ℝ) :
    apertureGraphCompletion a →L[ℝ] SourceGraph :=
  (apertureCoreScale a t).extend (apertureCoreEmbedding a)

private theorem apertureScaleTransport_core (a : SuzukiPositiveAperture) (t : ℝ)
    (p : apertureGraphCore a) :
    apertureScaleTransport a t (apertureGraphCoreInclusion a p) =
      translatedSourceGraph (apertureRepresentative a p) t :=
  ContinuousLinearMap.extend_eq (apertureCoreScale a t)
    (denseRange_apertureGraphCoreInclusion a)
    (apertureCoreEmbedding_isometry a).isUniformInducing p

/-- The extension is literal translation on every smooth source representative. -/
theorem apertureScaleTransport_test (a : SuzukiPositiveAperture) (t : ℝ)
    (u : SuzukiRestrictedWeilCore a.1) :
    apertureScaleTransport a t
      (apertureGraphCoreInclusion a ⟨suzukiCoreTestLift a u, ⟨u, rfl⟩⟩) =
      translatedSourceGraph (apertureSourceTest u) t := by
  rw [apertureScaleTransport_core]
  exact translatedSourceGraph_congr_lift a.1 t _ _
    (apertureRepresentative_support a _) (apertureSourceTest_support u)
    (apertureRepresentative_lift a _)

/-- Completing the source aperture preserves the full Weil translation identity. -/
theorem weilForm_apertureScaleTransport (a : SuzukiPositiveAperture) (t : ℝ)
    (p : apertureGraphCompletion a) :
    weilForm (apertureScaleTransport a t p) = weilForm p := by
  apply (denseRange_apertureGraphCoreInclusion a).induction_on p
  · exact isClosed_eq (continuous_weilForm.comp (apertureScaleTransport a t).continuous)
      (continuous_weilForm.comp continuous_subtype_val)
  · intro q
    rw [apertureScaleTransport_core, weilForm_translatedSourceGraph,
      ← weilForm_realTestGraphLift, apertureRepresentative_lift]

/-- One bound controls the completed aperture for every shift in a bounded range. -/
theorem exists_apertureScaleTransport_norm_bound (a : SuzukiPositiveAperture) (T : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, |t| ≤ T → ∀ p : apertureGraphCompletion a,
      ‖apertureScaleTransport a t p‖ ^ 2 ≤ C * ‖p‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_boundedWindow_scaleTransport a.1 T
  refine ⟨C, hC, fun t ht p => ?_⟩
  apply (denseRange_apertureGraphCoreInclusion a).induction_on p
  · exact isClosed_le ((apertureScaleTransport a t).continuous.norm.pow 2)
      ((continuous_norm.pow 2).const_mul C)
  · intro q
    rw [apertureScaleTransport_core]
    have h := hbound (apertureRepresentative a q) t
      (apertureRepresentative_support a q) ht
    rw [apertureRepresentative_lift] at h
    exact h

/-- Completed scale transport has a common upper and lower bound on bounded shift ranges. -/
theorem exists_apertureScaleTransport_two_sided_bound (a : SuzukiPositiveAperture) (T : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t : ℝ, |t| ≤ T → ∀ p : apertureGraphCompletion a,
      ‖apertureScaleTransport a t p‖ ^ 2 ≤ C * ‖p‖ ^ 2 ∧
        ‖p‖ ^ 2 ≤ C * ‖apertureScaleTransport a t p‖ ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_boundedWindow_two_sided_scaleTransport a.1 T
  refine ⟨C, hC, fun t ht p => ?_⟩
  apply (denseRange_apertureGraphCoreInclusion a).induction_on p
  · exact (isClosed_le ((apertureScaleTransport a t).continuous.norm.pow 2)
      ((continuous_norm.pow 2).const_mul C)).inter
      (isClosed_le (continuous_norm.pow 2)
        (((apertureScaleTransport a t).continuous.norm.pow 2).const_mul C))
  · intro q
    rw [apertureScaleTransport_core]
    have h := hbound (apertureRepresentative a q) t
      (apertureRepresentative_support a q) ht
    rw [apertureRepresentative_lift] at h
    exact h

/-- Translation loses no source information inside a completed aperture. -/
theorem apertureScaleTransport_injective (a : SuzukiPositiveAperture) (t : ℝ) :
    Function.Injective (apertureScaleTransport a t) := by
  obtain ⟨C, _, hC⟩ := exists_apertureScaleTransport_two_sided_bound a |t|
  intro p q hpq
  have h := (hC t le_rfl (p - q)).2
  rw [map_sub, hpq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at h
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (sq_eq_zero_iff.mp (le_antisymm h (sq_nonneg _))))

/-- Every mixed full-Weil pairing survives completed scale transport. -/
theorem weilBilin_apertureScaleTransport (a : SuzukiPositiveAperture) (t : ℝ)
    (p q : apertureGraphCompletion a) :
    weilBilin (apertureScaleTransport a t p) (apertureScaleTransport a t q) =
      weilBilin p q := by
  have hpair (x y : SourceGraph) :
      weilForm (x - y) = weilForm x - 2 * weilBilin x y + weilForm y := by
    rw [weilForm_eq_weilBilin, weilBilin_sub_left, weilBilin_sub_right,
      weilBilin_sub_right, weilBilin_comm y x, ← weilForm_eq_weilBilin,
      ← weilForm_eq_weilBilin]
    ring
  have h := weilForm_apertureScaleTransport a t (p - q)
  change weilForm (apertureScaleTransport a t (p - q)) =
    weilForm ((p : SourceGraph) - q) at h
  rw [map_sub, hpair, hpair, weilForm_apertureScaleTransport,
    weilForm_apertureScaleTransport] at h
  linarith only [h]

/-- The source aperture enlarged by the exact translation distance. -/
def scaleTargetAperture (a : SuzukiPositiveAperture) (t : ℝ) : SuzukiPositiveAperture :=
  ⟨a.1 + |t|, add_pos_of_pos_of_nonneg a.2 (abs_nonneg t)⟩

private def shiftedApertureCore (a : SuzukiPositiveAperture) (t : ℝ)
    (u : SuzukiRestrictedWeilCore a.1) :
    SuzukiRestrictedWeilCore (scaleTargetAperture a t).1 where
  toFun x := u (x - t)
  smooth := u.smooth.comp (contDiff_id.sub contDiff_const)
  supportRadius := u.supportRadius + |t|
  supportRadius_nonneg := add_nonneg u.supportRadius_nonneg (abs_nonneg t)
  supportRadius_lt_aperture := add_lt_add_right u.supportRadius_lt_aperture _
  support_subset := by
    intro x hx
    have hu := u.support_subset hx
    have htri : |x| ≤ |x - t| + |t| := by
      simpa only [sub_add_cancel] using abs_add_le (x - t) t
    exact abs_le.mp (htri.trans (add_le_add_right (abs_le.mpr hu) _))

/-- Completed translation lands in the corresponding enlarged source aperture. -/
theorem apertureScaleTransport_mem_target (a : SuzukiPositiveAperture) (t : ℝ)
    (p : apertureGraphCompletion a) :
    apertureScaleTransport a t p ∈ apertureGraphCompletion (scaleTargetAperture a t) := by
  apply (denseRange_apertureGraphCoreInclusion a).induction_on p
  · exact (isClosed_apertureGraphCompletion (scaleTargetAperture a t)).preimage
      (apertureScaleTransport a t).continuous
  · intro q
    obtain ⟨u, hu⟩ := q.property
    have hq : q = ⟨suzukiCoreTestLift a u, ⟨u, rfl⟩⟩ := Subtype.ext hu
    rw [hq, apertureScaleTransport_test]
    apply (apertureGraphCore (scaleTargetAperture a t)).le_topologicalClosure
    exact ⟨shiftedApertureCore a t u, rfl⟩

/-- Strip readouts, including both poles, retain their exact translation factors. -/
theorem graphFourierReadout_apertureScaleTransport (a : SuzukiPositiveAperture) (t : ℝ)
    (p : apertureGraphCompletion a) (z : ℂ) (hz : |z.im| ≤ 1 / 2) :
    graphFourierReadout (apertureScaleTransport a t p) z =
      Complex.exp (Complex.I * z * (t : ℂ)) * graphFourierReadout p z := by
  apply (denseRange_apertureGraphCoreInclusion a).induction_on p
  · exact isClosed_eq
      ((continuous_graphFourierReadout hz).comp (apertureScaleTransport a t).continuous)
      (continuous_const.mul ((continuous_graphFourierReadout hz).comp continuous_subtype_val))
  · intro q
    rw [apertureScaleTransport_core]
    change graphFourierReadout (translatedSourceGraph (apertureRepresentative a q) t) z =
      Complex.exp (Complex.I * z * (t : ℂ)) * graphFourierReadout (q : SourceGraph) z
    rw [← apertureRepresentative_lift a q]
    simp only [translatedSourceGraph, realTestGraphLift, graphFourierReadout_testLift]
    exact paperFT_translate_real (apertureRepresentative a q).1 t z

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.apertureScaleTransport_test
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.weilForm_apertureScaleTransport
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.weilBilin_apertureScaleTransport
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.apertureScaleTransport_mem_target
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.graphFourierReadout_apertureScaleTransport
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.apertureScaleTransport_injective
