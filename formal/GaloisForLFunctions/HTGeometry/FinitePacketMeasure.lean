import GaloisForLFunctions.HTGeometry.SufficientMacroSaturation
import GaloisForLFunctions.HTGeometry.GaussianPacketTestingLaw
import GaloisForLFunctions.HTGeometry.CausalJordanDriftWord

/-!
# Finite packets as measures

The bridge from the finite experiment layer to mathlib's measure-theoretic relative entropy.

* `packetMeasure`  a finite packet as a measure, with `lintegral_packetMeasure`;
* `finiteKernel`  a `FiniteMarkovKernel` as a `Kernel`, with `finiteKernel_comp`;
* `packetMeasure_tensorPower`  independent formation is `Measure.pi`;
* **Corollary 2.2, `(FCAP.13)`** of the card `ULF-FRM-2`: `ExactFormation.klDiv_le` and
  `ExactFormation.jeffreys_le`, the directed-relative-entropy and Jeffreys forms of the
  fixed-source capital law, obtained from the randomized data-processing inequality
  `klDiv_comp_le`.
-/

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Bridge

variable {X : Type*} [Fintype X] [Nonempty X] [MeasurableSpace X]
  [MeasurableSingletonClass X]

/-- The probability measure attached to a finite packet. -/
def packetMeasure (p : X → ℝ) : Measure X := weightMeasure fun x => ENNReal.ofReal (p x)

@[simp] theorem packetMeasure_singleton (p : X → ℝ) (x : X) :
    packetMeasure p {x} = ENNReal.ofReal (p x) := weightMeasure_singleton _ x

theorem packetMeasure_univ {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1) :
    packetMeasure p Set.univ = 1 := by
  classical
  rw [packetMeasure, weightMeasure, Measure.sum_apply _ MeasurableSet.univ]
  have hterm : ∀ x : X, ((ENNReal.ofReal (p x)) • Measure.dirac x) Set.univ
      = ENNReal.ofReal (p x) := by
    intro x
    simp [Measure.smul_apply]
  rw [tsum_congr hterm, tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun x _ => hp x), hp1]
  simp

theorem isProbabilityMeasure_packetMeasure {p : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) : IsProbabilityMeasure (packetMeasure p) :=
  ⟨packetMeasure_univ hp hp1⟩

theorem lintegral_packetMeasure (p : X → ℝ) (f : X → ℝ≥0∞) :
    ∫⁻ x, f x ∂(packetMeasure p) = ∑ x, ENNReal.ofReal (p x) * f x := by
  rw [packetMeasure, weightMeasure, lintegral_sum_measure]
  rw [tsum_congr fun x => by rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]]
  exact tsum_fintype _

variable {Y : Type*} [Fintype Y] [Nonempty Y] [MeasurableSpace Y]
  [MeasurableSingletonClass Y]

/-- A finite Markov kernel as a probability kernel. -/
def finiteKernel (K : FiniteMarkovKernel X Y) : Kernel X Y :=
  Kernel.ofFunOfCountable fun x => packetMeasure (fun y => K.weight y x)

@[simp] theorem finiteKernel_apply (K : FiniteMarkovKernel X Y) (x : X) :
    finiteKernel K x = packetMeasure (fun y => K.weight y x) := rfl

instance isMarkovKernel_finiteKernel (K : FiniteMarkovKernel X Y) :
    IsMarkovKernel (finiteKernel K) :=
  ⟨fun x => isProbabilityMeasure_packetMeasure (fun y => K.nonneg y x) (K.column_sum x)⟩

theorem finiteKernel_comp (K : FiniteMarkovKernel X Y) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x) :
    (finiteKernel K) ∘ₘ (packetMeasure p)
      = packetMeasure (K.toFinitePositiveKernel.applyReal p) := by
  refine Measure.ext_iff_singleton.mpr fun y => ?_
  rw [Measure.bind_apply (measurableSet_singleton y) (Kernel.aemeasurable _)]
  rw [lintegral_packetMeasure]
  rw [packetMeasure_singleton]
  have hterm : ∀ x : X, ENNReal.ofReal (p x) * (finiteKernel K) x {y}
      = ENNReal.ofReal (K.weight y x * p x) := by
    intro x
    rw [finiteKernel_apply, packetMeasure_singleton,
      ← ENNReal.ofReal_mul (hp x), mul_comm]
  rw [Finset.sum_congr rfl fun x _ => hterm x,
    ← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (K.nonneg y x) (hp x))]
  rfl

theorem packetMeasure_tensorPower [DecidableEq X] (d : ℕ) {p : X → ℝ} (hp : ∀ x, 0 ≤ p x)
    (hp1 : ∑ x, p x = 1) :
    packetMeasure (tensorPower d p) = Measure.pi (fun _ : Fin d => packetMeasure p) := by
  haveI := isProbabilityMeasure_packetMeasure hp hp1
  refine Measure.ext_iff_singleton.mpr fun x => ?_
  have hsingleton : ({x} : Set (Fin d → X)) = Set.univ.pi fun j => ({x j} : Set X) := by
    ext y
    simp [funext_iff]
  rw [packetMeasure_singleton, hsingleton, Measure.pi_pi]
  rw [tensorPower, ENNReal.ofReal_prod_of_nonneg (fun j _ => hp (x j))]
  exact Finset.prod_congr rfl fun j _ => (packetMeasure_singleton p (x j)).symm

/-- **Corollary 2.2, `(FCAP.13)`.**  Directed relative entropy obeys the same fixed-source capital
law. -/
theorem ExactFormation.klDiv_le [DecidableEq X] {E : FiniteExperiment Y} {F : FiniteExperiment X}
    {d : ℕ} (A : ExactFormation E F d) :
    (d : ℝ≥0∞) * klDiv (packetMeasure F.law₀) (packetMeasure F.law₁)
      ≤ klDiv (packetMeasure E.law₀) (packetMeasure E.law₁) := by
  haveI := isProbabilityMeasure_packetMeasure E.nonneg₀ E.sum₀
  haveI := isProbabilityMeasure_packetMeasure E.nonneg₁ E.sum₁
  haveI := isProbabilityMeasure_packetMeasure F.nonneg₀ F.sum₀
  haveI := isProbabilityMeasure_packetMeasure F.nonneg₁ F.sum₁
  refine klDiv_comp_pi_le _ _ _ _ (finiteKernel A.kernel) ?_ ?_
  · rw [finiteKernel_comp _ E.nonneg₀, A.forms_zero]
    exact packetMeasure_tensorPower d F.nonneg₀ F.sum₀
  · rw [finiteKernel_comp _ E.nonneg₁, A.forms_one]
    exact packetMeasure_tensorPower d F.nonneg₁ F.sum₁

/-- **Corollary 2.2, `(FCAP.13)` Jeffreys form.** -/
theorem ExactFormation.jeffreys_le [DecidableEq X] {E : FiniteExperiment Y}
    {F : FiniteExperiment X} {d : ℕ} (A : ExactFormation E F d) :
    (d : ℝ≥0∞) * formationJeffreys (packetMeasure F.law₀) (packetMeasure F.law₁)
      ≤ formationJeffreys (packetMeasure E.law₀) (packetMeasure E.law₁) := by
  haveI := isProbabilityMeasure_packetMeasure E.nonneg₀ E.sum₀
  haveI := isProbabilityMeasure_packetMeasure E.nonneg₁ E.sum₁
  haveI := isProbabilityMeasure_packetMeasure F.nonneg₀ F.sum₀
  haveI := isProbabilityMeasure_packetMeasure F.nonneg₁ F.sum₁
  refine jeffreys_comp_pi_le _ _ _ _ (finiteKernel A.kernel) ?_ ?_
  · rw [finiteKernel_comp _ E.nonneg₀, A.forms_zero]
    exact packetMeasure_tensorPower d F.nonneg₀ F.sum₀
  · rw [finiteKernel_comp _ E.nonneg₁, A.forms_one]
    exact packetMeasure_tensorPower d F.nonneg₁ F.sum₁

end Bridge

end

end GaloisForLFunctions.HTGeometry
