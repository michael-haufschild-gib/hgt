import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.GrowingTheWeilWindowAddsAnOrthogonalKernel
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilFormHasBoundedExteriorCrossings
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilCollarProfilesHaveTheirExactBoundaryLimits

/-!
# The exact collar equation for the Weil kernel increment

Subtracting the old Riesz equation from the new one leaves an exterior
forcing. Its Gamma part is the actual boundary transfer; its regular part
is the evaluation exponential minus the full prime-polar remainder.
-/

open Complex MeasureTheory Set Filter Topology
open scoped InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy
namespace WeilHilbertBeforeContact

/-- The compact regular residual in the new aperture, before exterior restriction. -/
def evalVectorRegularResidual {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    suzukiApertureHilbert b.1 :=
  evaluationForcing b.1 z - ccmRestrictedWeilBoundedRemainder b.1
    (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a (evalVector a z))))

/-- The right exterior Riesz residual as an actual positive-half-line L² vector. -/
def evalVectorRightCollarResidual {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    SuzukiPositiveL2 :=
  soninHalfLine (logTranslationCLM a.1.1 (evalVectorRegularResidual hab z : SoninL2)) +
    ccmGammaRightBoundaryTransfer a.1.1 (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))

/-- The reflected left residual retains the same full regular source. -/
def evalVectorLeftCollarResidual {a b : PrecontactAperture} (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    SuzukiPositiveL2 :=
  soninHalfLine (logTranslationCLM a.1.1
    (l2Reflection (evalVectorRegularResidual hab z : SoninL2))) +
    ccmGammaLeftBoundaryTransfer a.1.1 (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))

private theorem inner_evalVector_eq_physical (b : PrecontactAperture)
    (u : WeilHilbertBeforeContact b) (z : ℂ) :
    inner ℂ u (evalVector b z) =
      inner ℂ (ccmArchimedeanFormToAperture b.1 (toForm b u)) (evaluationForcing b.1 z) := by
  have h := congrArg (starRingEnd ℂ)
    ((inner_evalVector b z u).trans (eval_eq_inner_evaluationForcing b z u))
  simpa only [inner_conj_symm (E := WeilHilbertBeforeContact b),
    inner_conj_symm (E := suzukiApertureHilbert b.1)] using h

/-- The actual kernel increment solves the full right collar equation. -/
theorem inner_evalVectorIncrement_rightCollar {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) (u : WeilHilbertBeforeContact b) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b.1 (toForm b u) =
      logTranslationCLM (-a.1.1) (suzukiPositiveZeroExtension g)) :
    inner ℂ u (evalVectorIncrement hab z) = inner ℂ g (evalVectorRightCollarResidual hab z) := by
  have hcross := ccmWeilForm_rightExterior_pair hab (toForm b u)
    (toForm a (evalVector a z)) g hu
  have hsym : inner ℂ
      (ccmRestrictedWeilBoundedRemainder b.1 (ccmArchimedeanFormToAperture b.1 (toForm b u)))
      (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a (evalVector a z)))) =
      inner ℂ (ccmArchimedeanFormToAperture b.1 (toForm b u))
        (ccmRestrictedWeilBoundedRemainder b.1
          (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a (evalVector a z))))) :=
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b.1).isSymmetric _ _
  rw [evalVectorIncrement, inner_sub_right (E := WeilHilbertBeforeContact b), inner_evalVector_eq_physical,
    inner_eq_weil, toForm_inclusion, hcross, hsym]
  calc
    _ = inner ℂ (ccmArchimedeanFormToAperture b.1 (toForm b u))
        (evalVectorRegularResidual hab z) +
        inner ℂ g (ccmGammaRightBoundaryTransfer a.1.1
          (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))) := by
      rw [evalVectorRegularResidual, inner_sub_right]
      ring
    _ = _ := by
      change inner ℂ (ccmArchimedeanFormEmbedding b.1 (toForm b u))
        (evalVectorRegularResidual hab z : SoninL2) + _ = _
      rw [hu, inner_rightExterior_halfLine, evalVectorRightCollarResidual, inner_add_right]

/-- The same exact equation holds in reflected left collar coordinates. -/
theorem inner_evalVectorIncrement_leftCollar {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) (u : WeilHilbertBeforeContact b) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b.1 (toForm b u) =
      l2Reflection (logTranslationCLM (-a.1.1) (suzukiPositiveZeroExtension g))) :
    inner ℂ u (evalVectorIncrement hab z) = inner ℂ g (evalVectorLeftCollarResidual hab z) := by
  have hcross := ccmWeilForm_leftExterior_pair hab (toForm b u)
    (toForm a (evalVector a z)) g hu
  have hsym : inner ℂ
      (ccmRestrictedWeilBoundedRemainder b.1 (ccmArchimedeanFormToAperture b.1 (toForm b u)))
      (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a (evalVector a z)))) =
      inner ℂ (ccmArchimedeanFormToAperture b.1 (toForm b u))
        (ccmRestrictedWeilBoundedRemainder b.1
          (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a (evalVector a z))))) :=
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint b.1).isSymmetric _ _
  rw [evalVectorIncrement, inner_sub_right (E := WeilHilbertBeforeContact b), inner_evalVector_eq_physical,
    inner_eq_weil, toForm_inclusion, hcross, hsym]
  calc
    _ = inner ℂ (ccmArchimedeanFormToAperture b.1 (toForm b u))
        (evalVectorRegularResidual hab z) +
        inner ℂ g (ccmGammaLeftBoundaryTransfer a.1.1
          (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))) := by
      rw [evalVectorRegularResidual, inner_sub_right]
      ring
    _ = _ := by
      change inner ℂ (ccmArchimedeanFormEmbedding b.1 (toForm b u))
        (evalVectorRegularResidual hab z : SoninL2) + _ = _
      rw [hu, inner_leftExterior_halfLine, evalVectorLeftCollarResidual, inner_add_right]

/-- The regular residual is the exact evaluation exponential minus the continuous full remainder. -/
theorem evalVectorRegularResidual_ae {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (evalVectorRegularResidual hab z : ℝ → ℂ) =ᵐ[volume.restrict (centralInterval b.1.1)]
      fun x => Complex.exp (-I*(starRingEnd ℂ z)*(x : ℂ)) -
        evalVectorRemainderProfile a b.1 hab z x := by
  let r := ccmRestrictedWeilBoundedRemainder b.1
    (ccmArchimedeanFormToAperture b.1 (apertureExt hab (toForm a (evalVector a z))))
  have hval : (evalVectorRegularResidual hab z : SoninL2) =
      (evaluationForcing b.1 z : SoninL2)-(r : SoninL2) := rfl
  change (evalVectorRegularResidual hab z : SoninL2) =ᵐ[
    volume.restrict (centralInterval b.1.1)] _
  rw [hval]
  filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub (evaluationForcing b.1 z : SoninL2) (r : SoninL2)),
    ae_restrict_of_ae (evaluationForcing_coeFn b.1 z), evalVectorRemainderProfile_ae a b.1 hab z,
    ae_restrict_mem (measurableSet_centralInterval b.1.1)] with x hs he hr hx
  change x ∈ Icc (-b.1.1) b.1.1 at hx
  rw [hs, Pi.sub_apply, he, hr, indicator_of_mem hx]
  rfl

/-- On the actual right collar, the operator residual is exactly its literal full profile. -/
theorem evalVectorRightCollarResidual_ae {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (evalVectorRightCollarResidual hab z : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (b.1.1-a.1.1))] evalVectorRightCollarProfile a b.1 hab z := by
  let r : SoninL2 := evalVectorRegularResidual hab z
  let T := ccmGammaRightBoundaryTransfer a.1.1
    (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))
  have ha := (ae_restrict_iff' measurableSet_Ioi).mp
    (Lp.coeFn_add (soninHalfLine (logTranslationCLM a.1.1 r)) T)
  have hh := (ae_restrict_iff' measurableSet_Ioi).mp
    (coeFn_soninHalfLine (logTranslationCLM a.1.1 r))
  have hr := (MellinL2.realTranslation_measurePreserving a.1.1).quasiMeasurePreserving.tendsto_ae.eventually
    ((ae_restrict_iff' (measurableSet_centralInterval b.1.1)).mp
      (evalVectorRegularResidual_ae hab z))
  have hT := (ae_restrict_iff' measurableSet_Ioi).mp
    (evalVectorRightExteriorResponse_eq_boundaryTransfer a z)
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae ha,
    ae_restrict_of_ae hh, ae_restrict_of_ae hr, ae_restrict_of_ae hT,
    ae_restrict_of_ae (logarithmicTranslation_coeFn a.1.1 r)] with d hd ha hh hr hT ht
  have hm : d+a.1.1 ∈ centralInterval b.1.1 := by
    constructor
    · linarith only [a.1.property, hab, hd.1]
    · linarith only [hd.2]
  change d+a.1.1 ∈ centralInterval b.1.1 → r (d+a.1.1) = _ at hr
  change (soninHalfLine (logTranslationCLM a.1.1 r)+T) d = _
  rw [ha hd.1, Pi.add_apply, hh hd.1, ht, hr hm]
  change Complex.exp (-I*(starRingEnd ℂ z)*((d+a.1.1 : ℝ) : ℂ)) -
    evalVectorRemainderProfile a b.1 hab z (d+a.1.1) + T d = _
  rw [add_comm d a.1.1]
  unfold evalVectorRightCollarProfile
  rw [hT hd.1, sub_neg_eq_add]

/-- On the reflected left collar, the same identification retains every prime and polar term. -/
theorem evalVectorLeftCollarResidual_ae {a b : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (z : ℂ) :
    (evalVectorLeftCollarResidual hab z : ℝ → ℂ) =ᵐ[
      volume.restrict (Ioc (0 : ℝ) (b.1.1-a.1.1))] evalVectorLeftCollarProfile a b.1 hab z := by
  let r : SoninL2 := evalVectorRegularResidual hab z
  let T := ccmGammaLeftBoundaryTransfer a.1.1
    (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z)))
  have ha := (ae_restrict_iff' measurableSet_Ioi).mp
    (Lp.coeFn_add (soninHalfLine (logTranslationCLM a.1.1 (l2Reflection r))) T)
  have hh := (ae_restrict_iff' measurableSet_Ioi).mp
    (coeFn_soninHalfLine (logTranslationCLM a.1.1 (l2Reflection r)))
  have hr := ((Measure.measurePreserving_neg (volume : Measure ℝ)).comp
    (MellinL2.realTranslation_measurePreserving a.1.1)).quasiMeasurePreserving.tendsto_ae.eventually
      ((ae_restrict_iff' (measurableSet_centralInterval b.1.1)).mp
        (evalVectorRegularResidual_ae hab z))
  have href := (l2Reflection_ae r).comp_tendsto
    (MellinL2.realTranslation_measurePreserving a.1.1).quasiMeasurePreserving.tendsto_ae
  have hT := (ae_restrict_iff' measurableSet_Ioi).mp
    (evalVectorLeftExteriorResponse_eq_boundaryTransfer a z)
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae ha,
    ae_restrict_of_ae hh, ae_restrict_of_ae hr, ae_restrict_of_ae href, ae_restrict_of_ae hT,
    ae_restrict_of_ae (logarithmicTranslation_coeFn a.1.1 (l2Reflection r))]
      with d hd ha hh hr href hT ht
  have hm : -(d+a.1.1) ∈ centralInterval b.1.1 := by
    constructor
    · linarith only [hd.2]
    · linarith only [a.1.property, hab, hd.1]
  change -(d+a.1.1) ∈ centralInterval b.1.1 → r (-(d+a.1.1)) = _ at hr
  change l2Reflection r (d+a.1.1) = r (-(d+a.1.1)) at href
  change (soninHalfLine (logTranslationCLM a.1.1 (l2Reflection r))+T) d = _
  rw [ha hd.1, Pi.add_apply, hh hd.1, ht, href, hr hm]
  change Complex.exp (-I*(starRingEnd ℂ z)*((-(d+a.1.1) : ℝ) : ℂ)) -
    evalVectorRemainderProfile a b.1 hab z (-(d+a.1.1)) + T d = _
  rw [show -(d+a.1.1) = -a.1.1-d by ring]
  unfold evalVectorLeftCollarProfile
  rw [hT hd.1, sub_neg_eq_add]

/-- Pairing an increment with an earlier source is independent of the enclosing aperture. -/
theorem inner_inclusion_evalVectorIncrement {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) (z : ℂ) (u : WeilHilbertBeforeContact b) :
    inner ℂ (inclusion hbc u) (evalVectorIncrement (hab.trans hbc) z) =
      inner ℂ u (evalVectorIncrement hab z) := by
  have he : inner ℂ (inclusion hbc u) (evalVector c z) = inner ℂ u (evalVector b z) := by
    have h := congrArg (starRingEnd ℂ) (fourier_inclusion hbc u z)
    change starRingEnd ℂ (eval c z (inclusion hbc u)) = starRingEnd ℂ (eval b z u) at h
    rw [← inner_evalVector c z (inclusion hbc u), ← inner_evalVector b z u,
      inner_conj_symm (E := WeilHilbertBeforeContact c),
      inner_conj_symm (E := WeilHilbertBeforeContact b)] at h
    exact h
  rw [evalVectorIncrement, inner_sub_right (E := WeilHilbertBeforeContact c), he,
    ← inclusion_trans hab hbc, (inclusion hbc).inner_map_map, evalVectorIncrement,
    inner_sub_right (E := WeilHilbertBeforeContact b)]

/-- A fixed enclosing aperture supplies the full right residual for every smaller growing window. -/
theorem inner_evalVectorIncrement_rightCollar_in_enclosure {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) (z : ℂ)
    (u : WeilHilbertBeforeContact b) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b.1 (toForm b u) =
      logTranslationCLM (-a.1.1) (suzukiPositiveZeroExtension g)) :
    inner ℂ u (evalVectorIncrement hab z) =
      inner ℂ g (evalVectorRightCollarResidual (hab.trans hbc) z) := by
  have he := ccmArchimedeanFormToAperture_coe_eq_of_val_eq
    (apertureExt_val hbc (toForm b u))
  have hu' : ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hbc u)) =
      logTranslationCLM (-a.1.1) (suzukiPositiveZeroExtension g) := by
    rw [toForm_inclusion]
    exact he.trans hu
  rw [← inner_inclusion_evalVectorIncrement hab hbc z u]
  exact inner_evalVectorIncrement_rightCollar (hab.trans hbc) z (inclusion hbc u) g hu'

/-- The left residual has the same fixed-enclosure compatibility. -/
theorem inner_evalVectorIncrement_leftCollar_in_enclosure {a b c : PrecontactAperture}
    (hab : a.1.1 ≤ b.1.1) (hbc : b.1.1 ≤ c.1.1) (z : ℂ)
    (u : WeilHilbertBeforeContact b) (g : SuzukiPositiveL2)
    (hu : ccmArchimedeanFormEmbedding b.1 (toForm b u) =
      l2Reflection (logTranslationCLM (-a.1.1) (suzukiPositiveZeroExtension g))) :
    inner ℂ u (evalVectorIncrement hab z) =
      inner ℂ g (evalVectorLeftCollarResidual (hab.trans hbc) z) := by
  have he := ccmArchimedeanFormToAperture_coe_eq_of_val_eq
    (apertureExt_val hbc (toForm b u))
  have hu' : ccmArchimedeanFormEmbedding c.1 (toForm c (inclusion hbc u)) =
      l2Reflection (logTranslationCLM (-a.1.1) (suzukiPositiveZeroExtension g)) := by
    rw [toForm_inclusion]
    exact he.trans hu
  rw [← inner_inclusion_evalVectorIncrement hab hbc z u]
  exact inner_evalVectorIncrement_leftCollar (hab.trans hbc) z (inclusion hbc u) g hu'

#print axioms inner_evalVectorIncrement_rightCollar_in_enclosure
#print axioms inner_evalVectorIncrement_leftCollar_in_enclosure
#print axioms evalVectorRightCollarResidual_ae
#print axioms evalVectorLeftCollarResidual_ae
#print axioms inner_evalVectorIncrement_rightCollar
#print axioms inner_evalVectorIncrement_leftCollar
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
