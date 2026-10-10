import GaloisForLFunctions.HTGeometry.PaperFiniteObservationEntropy
import GaloisForLFunctions.RHTower.ThetaCarrierHassePacket

/-! # Finite theta observations with their native reflection budget

The completed theta source supplies both reflected probability laws. Every
finite measurable observation inherits their exact source information budget
`2 a thetaTiltMean a`. Coarsening has the paper's exact conditional entropy
loss, and the paper Pinsker estimate bounds the surviving observed contrast.
-/

namespace RHTower
noncomputable section
open MeasureTheory InformationTheory
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.FourierLLogL
open scoped BigOperators ENNReal

/-- The closed interval of admissible native theta tilts. -/
abbrev PaperThetaTilt := {a : ℝ // |a| ≤ 1}

def paperThetaTiltReflection (a : PaperThetaTilt) : PaperThetaTilt :=
  ⟨-a, by simpa only [abs_neg] using a.property⟩

def paperThetaTiltProbability (a : PaperThetaTilt) : ProbabilityMeasure ℝ :=
  ⟨thetaTiltProb a, thetaTiltProb_isProbabilityMeasure a.property⟩

variable {α β : Type*}
  [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]
  [Fintype β] [MeasurableSpace β] [MeasurableSingletonClass β]

/-- The literal cell masses of an observation of the native theta probability. -/
def paperThetaObservationLaw (a : PaperThetaTilt) (f : SimpleFunc ℝ α) : Law α :=
  paperFiniteObservationLaw (paperThetaTiltProbability a) f

theorem paperThetaObservationLaw_apply (a : PaperThetaTilt) (f : SimpleFunc ℝ α) (i : α) :
    paperThetaObservationLaw a f i = (thetaTiltProb a).real (f ⁻¹' {i}) :=
  paperFiniteObservationLaw_apply (paperThetaTiltProbability a) f i

theorem paperThetaObservationLaw_Ex (a : PaperThetaTilt) (f : SimpleFunc ℝ α) (g : α → ℝ) :
    (paperThetaObservationLaw a f).Ex g = ∫ x, g (f x) ∂thetaTiltProb a :=
  paperFiniteObservationLaw_Ex (paperThetaTiltProbability a) f g

theorem paperThetaObservationLaw_send (a : PaperThetaTilt) (f : SimpleFunc ℝ α) (g : α → β) :
    paperThetaObservationLaw a (f.map g) = (paperThetaObservationLaw a f).send g :=
  paperFiniteObservationLaw_send (paperThetaTiltProbability a) f g

/-- Support domination is supplied by the actual reflected theta source. -/
theorem paperThetaObservationLaw_dominated (a : PaperThetaTilt) (f : SimpleFunc ℝ α) :
    (paperThetaObservationLaw a f).dominated
      (paperThetaObservationLaw (paperThetaTiltReflection a) f) :=
  (paperFiniteMeasureLaw_dominated_iff
    ((paperThetaTiltProbability a).map f.aemeasurable)
    ((paperThetaTiltProbability (paperThetaTiltReflection a)).map f.aemeasurable)).mpr
      ((thetaTiltProb_absolutelyContinuous a.property).map f.measurable)

private theorem reflection_kl_finite (a : PaperThetaTilt) :
    klDiv (thetaTiltProb a) (thetaTiltProb (-a)) ≠ ∞ := by
  haveI := thetaTiltProb_isProbabilityMeasure a.property
  haveI := thetaTiltProb_isProbabilityMeasure (paperThetaTiltReflection a).property
  have hac := thetaTiltProb_absolutelyContinuous a.property
  apply klDiv_ne_top hac
  have he : llr (thetaTiltProb a) (thetaTiltProb (-a)) =ᵐ[thetaTiltProb a]
      fun x => 2 * (a : ℝ) * x := hac.ae_le (llr_thetaTiltProb_reflection a.property)
  exact ((integrable_id_thetaTiltProb a.property).const_mul (2 * (a : ℝ))).congr
    he.symm

/-- The source-derived reflection cost bounds every finite observation, without a new estimate. -/
theorem paperThetaObservation_kl_budget (a : PaperThetaTilt) (f : SimpleFunc ℝ α) :
    (paperThetaObservationLaw a f).kl (paperThetaObservationLaw (paperThetaTiltReflection a) f) ≤
      2 * (a : ℝ) * thetaTiltMean a := by
  have h := paperFiniteObservationLaw_kl_le_native (paperThetaTiltProbability a)
    (paperThetaTiltProbability (paperThetaTiltReflection a)) f
  have hr := ENNReal.toReal_mono (reflection_kl_finite a) h
  change (ENNReal.ofReal ((paperThetaObservationLaw a f).kl
    (paperThetaObservationLaw (paperThetaTiltReflection a) f))).toReal ≤
      (klDiv (thetaTiltProb a) (thetaTiltProb (-a))).toReal at hr
  rw [ENNReal.toReal_ofReal (Law.kl_nonneg (paperThetaObservationLaw_dominated a f)),
    toReal_klDiv_thetaTiltProb_reflection a.property] at hr
  exact hr

theorem paperThetaObservation_tv_sq_budget (a : PaperThetaTilt) (f : SimpleFunc ℝ α) :
    ((paperThetaObservationLaw a f).tv
      (paperThetaObservationLaw (paperThetaTiltReflection a) f)) ^ 2 ≤
        2 * (a : ℝ) * thetaTiltMean a :=
  (Law.tv_sq_le_kl (paperThetaObservationLaw_dominated a f)).trans
    (paperThetaObservation_kl_budget a f)

theorem paperThetaObservation_tv_budget (a : PaperThetaTilt) (f : SimpleFunc ℝ α) :
    (paperThetaObservationLaw a f).tv
      (paperThetaObservationLaw (paperThetaTiltReflection a) f) ≤
        Real.sqrt (2 * (a : ℝ) * thetaTiltMean a) :=
  (Law.tv_le_sqrt_kl (paperThetaObservationLaw_dominated a f)).trans
    (Real.sqrt_le_sqrt (paperThetaObservation_kl_budget a f))

/-- Coarsening discards exactly the expected conditional relative entropy. -/
theorem paperThetaObservation_coarsen_kl_decomposition (a : PaperThetaTilt)
    (f : SimpleFunc ℝ α) (g : α → β) :
    (paperThetaObservationLaw a f).kl (paperThetaObservationLaw (paperThetaTiltReflection a) f) =
      (paperThetaObservationLaw a (f.map g)).kl
        (paperThetaObservationLaw (paperThetaTiltReflection a) (f.map g)) +
      (paperThetaObservationLaw a (f.map g)).Ex (fun b =>
        ((paperThetaObservationLaw a f).after g b).kl
          ((paperThetaObservationLaw (paperThetaTiltReflection a) f).after g b)) := by
  simpa only [paperThetaObservationLaw_send] using
    Law.kl_chain (paperThetaObservationLaw_dominated a f) g

theorem paperThetaObservation_coarsen_kl_le (a : PaperThetaTilt) (f : SimpleFunc ℝ α) (g : α → β) :
    (paperThetaObservationLaw a (f.map g)).kl
      (paperThetaObservationLaw (paperThetaTiltReflection a) (f.map g)) ≤
    (paperThetaObservationLaw a f).kl (paperThetaObservationLaw (paperThetaTiltReflection a) f) := by
  simpa only [paperThetaObservationLaw_send] using
    Law.kl_data_processing (paperThetaObservationLaw_dominated a f) g

theorem paperThetaObservation_coarsen_tv_le (a : PaperThetaTilt) (f : SimpleFunc ℝ α) (g : α → β) :
    (paperThetaObservationLaw a (f.map g)).tv
      (paperThetaObservationLaw (paperThetaTiltReflection a) (f.map g)) ≤
    (paperThetaObservationLaw a f).tv (paperThetaObservationLaw (paperThetaTiltReflection a) f) := by
  simpa only [paperThetaObservationLaw_send] using
    Law.tv_data_processing (paperThetaObservationLaw a f)
      (paperThetaObservationLaw (paperThetaTiltReflection a) f) g

/-- Discarded conditional information is itself paid for by the same native source budget. -/
theorem paperThetaObservation_conditional_kl_budget (a : PaperThetaTilt)
    (f : SimpleFunc ℝ α) (g : α → β) :
    (paperThetaObservationLaw a (f.map g)).Ex (fun b =>
      ((paperThetaObservationLaw a f).after g b).kl
        ((paperThetaObservationLaw (paperThetaTiltReflection a) f).after g b)) ≤
      2 * (a : ℝ) * thetaTiltMean a := by
  have he := paperThetaObservation_coarsen_kl_decomposition a f g
  have hb := paperThetaObservation_kl_budget a f
  have hn := Law.kl_nonneg (paperThetaObservationLaw_dominated a (f.map g))
  linarith

end
end RHTower
