import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.Lemmas
import GaloisForLFunctions.HTGeometry.ConstitutiveObserverFibreChirality

/-!
# Functional-equation action on split packet formation

This module formalizes the universal mechanism from the packet-formation card.

* a common Markov recovery kernel forms a joint observer-history law;
* projection recovers the observer and formation preserves KL divergence exactly;
* a measurable observer action lifts by discarding and regenerating latent history;
* the lift is natural, composes strictly on formed laws, and is an involution there when the
  observer action is involutive;
* measurable embeddings preserve both directed KL divergence and symmetric Jeffreys work after
  lifting;
* a reflection-odd tilt closes canonically only after adding a two-valued formation sheet.

The information-neutrality theorem is an isometry statement.  It does not assert that reflected
endpoint laws have zero information separation.
-/

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section SplitFormation

variable {X H : Type*} [MeasurableSpace X] [MeasurableSpace H]

/-- Extend an observer law by a parameter-independent latent recovery kernel. -/
def splitFormation (μ : Measure X) (κ : Kernel X H) : Measure (X × H) := μ ⊗ₘ κ

/-- Projection from a formed law recovers the observer exactly. -/
theorem splitFormation_recovers_observer
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X H) [IsMarkovKernel κ] :
    (splitFormation μ κ).fst = μ := by
  exact Measure.fst_compProd μ κ

/-- **Common-recovery information law.**  Adding the same latent conditional law to both
observers preserves extended KL divergence, including the value `∞`. -/
theorem klDiv_splitFormation
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] :
    klDiv (splitFormation μ κ) (splitFormation ν κ) = klDiv μ ν := by
  exact klDiv_compProd_left μ ν κ

/-- Lift an observer action by applying it to the recovered coordinate and then regenerating
latent history from the same kernel. -/
def formationLiftKernel (κ : Kernel X H) [IsMarkovKernel κ]
    (A : X → X) (hA : Measurable A) : Kernel (X × H) (X × H) :=
  (Kernel.id ×ₖ κ) ∘ₖ
    Kernel.deterministic (fun z : X × H => A z.1) (by fun_prop)

/-- **Formation-action naturality.**  The stochastic lift sends a formed law to the formation of
the pushed observer law. -/
theorem formationLiftKernel_naturality
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X H) [IsMarkovKernel κ]
    (A : X → X) (hA : Measurable A) :
    formationLiftKernel κ A hA ∘ₘ splitFormation μ κ =
      splitFormation (μ.map A) κ := by
  rw [formationLiftKernel, splitFormation, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map]
  have hfst : (μ ⊗ₘ κ).map Prod.fst = μ := by
    exact Measure.fst_compProd μ κ
  have hmap : (μ ⊗ₘ κ).map (fun z : X × H => A z.1) = μ.map A := by
    calc
      (μ ⊗ₘ κ).map (fun z : X × H => A z.1) =
          ((μ ⊗ₘ κ).map Prod.fst).map A := by
            rw [Measure.map_map hA measurable_fst]
            rfl
      _ = μ.map A := by rw [hfst]
  rw [hmap]
  change (Kernel.id ×ₖ κ) ∘ₘ μ.map A = μ.map A ⊗ₘ κ
  exact (Measure.compProd_eq_comp_prod (μ.map A) κ).symm

/-- Serial observer actions compose strictly after formation lifting. -/
theorem formationLiftKernel_comp_on_formation
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X H) [IsMarkovKernel κ]
    (A B : X → X) (hA : Measurable A) (hB : Measurable B) :
    formationLiftKernel κ B hB ∘ₘ
        (formationLiftKernel κ A hA ∘ₘ splitFormation μ κ) =
      formationLiftKernel κ (B ∘ A) (hB.comp hA) ∘ₘ splitFormation μ κ := by
  rw [formationLiftKernel_naturality μ κ A hA,
    formationLiftKernel_naturality (μ.map A) κ B hB,
    formationLiftKernel_naturality μ κ (B ∘ A) (hB.comp hA),
    Measure.map_map hB hA]

/-- An involutive observer action lifts to an involution on the image of packet formation. -/
theorem formationLiftKernel_involution_on_formation
    (μ : Measure X) [IsFiniteMeasure μ]
    (κ : Kernel X H) [IsMarkovKernel κ]
    (R : X → X) (hR : Measurable R) (hinv : ∀ x, R (R x) = x) :
    formationLiftKernel κ R hR ∘ₘ
        (formationLiftKernel κ R hR ∘ₘ splitFormation μ κ) =
      splitFormation μ κ := by
  rw [formationLiftKernel_naturality μ κ R hR,
    formationLiftKernel_naturality (μ.map R) κ R hR,
    Measure.map_map hR hR]
  have hcomp : R ∘ R = id := funext hinv
  rw [hcomp, Measure.map_id]

/-- **Information-neutral functional-equation lift.**  A measurable embedding of the observer
acts isometrically on KL divergence after common-kernel packet formation. -/
theorem formationLiftKernel_klDiv_isometry
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ]
    (A : X → X) (hA : MeasurableEmbedding A) :
    klDiv (formationLiftKernel κ A hA.measurable ∘ₘ splitFormation μ κ)
        (formationLiftKernel κ A hA.measurable ∘ₘ splitFormation ν κ) =
      klDiv (splitFormation μ κ) (splitFormation ν κ) := by
  rw [formationLiftKernel_naturality μ κ A hA.measurable,
    formationLiftKernel_naturality ν κ A hA.measurable,
    klDiv_splitFormation, klDiv_splitFormation,
    klDiv_map_measurableEmbedding hA]

/-- Symmetric information work of two finite observer or packet laws. -/
def formationJeffreys (μ ν : Measure X) : ℝ≥0∞ := klDiv μ ν + klDiv ν μ

/-- Split formation preserves symmetric information work exactly. -/
theorem formationJeffreys_splitFormation
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ] :
    formationJeffreys (splitFormation μ κ) (splitFormation ν κ) =
      formationJeffreys μ ν := by
  simp [formationJeffreys, klDiv_splitFormation]

/-- Reversible lifted action preserves symmetric information work; information neutrality does not
annihilate endpoint separation. -/
theorem formationJeffreys_lift_isometry
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ]
    (A : X → X) (hA : MeasurableEmbedding A) :
    formationJeffreys
        (formationLiftKernel κ A hA.measurable ∘ₘ splitFormation μ κ)
        (formationLiftKernel κ A hA.measurable ∘ₘ splitFormation ν κ) =
      formationJeffreys (splitFormation μ κ) (splitFormation ν κ) := by
  simp only [formationJeffreys]
  rw [formationLiftKernel_klDiv_isometry μ ν κ A hA,
    formationLiftKernel_klDiv_isometry ν μ κ A hA]

/-- **Functional-equation packet capstone.**  Every measurable involution lifts through a common
recovery kernel to an involution on formed laws that preserves both directed KL information and
symmetric Jeffreys work. -/
theorem involutiveFormationLift_informationNeutral
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (κ : Kernel X H) [IsMarkovKernel κ]
    (R : X → X) (hR : Measurable R) (hinv : ∀ x, R (R x) = x) :
    klDiv (formationLiftKernel κ R hR ∘ₘ splitFormation μ κ)
          (formationLiftKernel κ R hR ∘ₘ splitFormation ν κ) =
        klDiv (splitFormation μ κ) (splitFormation ν κ) ∧
      formationJeffreys
          (formationLiftKernel κ R hR ∘ₘ splitFormation μ κ)
          (formationLiftKernel κ R hR ∘ₘ splitFormation ν κ) =
        formationJeffreys (splitFormation μ κ) (splitFormation ν κ) ∧
      formationLiftKernel κ R hR ∘ₘ
          (formationLiftKernel κ R hR ∘ₘ splitFormation μ κ) =
        splitFormation μ κ := by
  let hEmb : MeasurableEmbedding R :=
    measurableEmbedding_of_measurable_involution hR hinv
  exact ⟨formationLiftKernel_klDiv_isometry μ ν κ R hEmb,
    formationJeffreys_lift_isometry μ ν κ R hEmb,
    formationLiftKernel_involution_on_formation μ κ R hR hinv⟩

end SplitFormation

section ReflectionSheet

variable {X : Type*}

/-- Unnormalized weight of a reflection-odd exponential tilt on one of two formation sheets.
`false` is the original base and `true` is its reflected base. -/
def reflectionSheetWeight (b : X → ℝ) (R : X → X) (T : X → ℝ)
    (a : ℝ) (sheet : Bool) (x : X) : ℝ :=
  Real.exp (a * T x) * if sheet then b (R x) else b x

/-- **Two-sheet reflection closure.**  Reflection negates the tilt and toggles the formation sheet.
This is the algebraic core of the Hellinger/modular formation double. -/
theorem reflectionSheetWeight_swap
    (b : X → ℝ) (R : X → X) (T : X → ℝ)
    (hinv : ∀ x, R (R x) = x) (hodd : ∀ x, T (R x) = -T x)
    (a : ℝ) (sheet : Bool) (x : X) :
    reflectionSheetWeight b R T (-a) (!sheet) (R x) =
      reflectionSheetWeight b R T a sheet x := by
  cases sheet <;> simp [reflectionSheetWeight, hinv, hodd]

/-- At zero tilt the two sheets coincide exactly when the base weight is reflection invariant. -/
theorem reflectionSheetWeight_sameSheet_zero_iff
    (b : X → ℝ) (R : X → X) (T : X → ℝ) :
    (∀ x, reflectionSheetWeight b R T 0 true x =
      reflectionSheetWeight b R T 0 false x) ↔
      ∀ x, b (R x) = b x := by
  simp [reflectionSheetWeight]

end ReflectionSheet

end

end GaloisForLFunctions.HTGeometry
