import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingFZZParityLocalTemperedFEReflectionNoGo
import GaloisForLFunctions.HTGeometry.TwoSidedExponentialMoments
import GaloisForLFunctions.HTGeometry.WeightedDensityL2

/-!
# Singular weighted-Hilbert FZZ reflection is nonselective

The corpus-forced local FZZ gain becomes, in logarithmic energy x,

a(x) = g(x) / g(-x),  g(x) = exp(-x/2) F(exp x),

where F(t)=1/(exp t+1) is the literal parity-delay source. Therefore the weighted reflection
Tf(x)=a(x)f(-x) is unitary for a positive density rho exactly when

rho(x)=g(x)^(-2) h(x)

for an arbitrary positive even function h. The explicit choice h(x)=exp(-2|x|) admits the
literal Fermi source with energy density exp(x-2|x|), which is integrable.

Thus singular/non-Fock carrier existence, positive energy, reflection unitarity, and finite source
energy cannot select the missing FZZ phase/sign. The only surviving FZZ-P input is an independent
source-specific phase/sign law before the shared Ward endpoint.

[FZZ-P ROUTE-CLASS KILL] [SOURCE-PURE] [PAPER-PROVED] [LEAN-PROVED]
-/

open MeasureTheory Real Set

namespace RHTower

noncomputable section

def fzzCigarParityLogSource (x : ℝ) : ℝ :=
  fzzCigarParityDelay (Real.exp x)

def fzzCigarParityLogReflectionGauge (x : ℝ) : ℝ :=
  Real.exp (-x / 2) * fzzCigarParityLogSource x

def fzzCigarParityLogForcedGain (x : ℝ) : ℝ :=
  fzzCigarParityLogReflectionGauge x /
    fzzCigarParityLogReflectionGauge (-x)

theorem fzzCigarParityLogSource_pos (x : ℝ) :
    0 < fzzCigarParityLogSource x := by
  rw [fzzCigarParityLogSource,
    fzzCigarParityDelay_eq_fermi (Real.exp_pos x)]
  positivity

theorem fzzCigarParityLogSource_eq_fermi (x : ℝ) :
    fzzCigarParityLogSource x =
      (Real.exp (Real.exp x) + 1)⁻¹ := by
  exact fzzCigarParityDelay_eq_fermi (Real.exp_pos x)

theorem continuous_fzzCigarParityLogSource :
    Continuous fzzCigarParityLogSource := by
  have hfun : fzzCigarParityLogSource =
      fun x : ℝ => (Real.exp (Real.exp x) + 1)⁻¹ := by
    funext x
    exact fzzCigarParityLogSource_eq_fermi x
  rw [hfun]
  exact ((Real.continuous_exp.comp Real.continuous_exp).add continuous_const).inv₀
    (fun x => by
      change Real.exp (Real.exp x) + 1 ≠ 0
      positivity)

theorem fzzCigarParityLogReflectionGauge_pos (x : ℝ) :
    0 < fzzCigarParityLogReflectionGauge x := by
  rw [fzzCigarParityLogReflectionGauge]
  exact mul_pos (Real.exp_pos _) (fzzCigarParityLogSource_pos x)

theorem continuous_fzzCigarParityLogReflectionGauge :
    Continuous fzzCigarParityLogReflectionGauge := by
  unfold fzzCigarParityLogReflectionGauge
  have hfactor : Continuous (fun x : ℝ => Real.exp (-x / 2)) := by fun_prop
  exact hfactor.mul continuous_fzzCigarParityLogSource

theorem fzzCigarParityLogForcedGain_pos (x : ℝ) :
    0 < fzzCigarParityLogForcedGain x := by
  rw [fzzCigarParityLogForcedGain]
  exact div_pos (fzzCigarParityLogReflectionGauge_pos x)
    (fzzCigarParityLogReflectionGauge_pos (-x))

theorem fzzCigarParityLogForcedGain_neg (x : ℝ) :
    fzzCigarParityLogForcedGain (-x) =
      (fzzCigarParityLogForcedGain x)⁻¹ := by
  rw [fzzCigarParityLogForcedGain, fzzCigarParityLogForcedGain]
  simp only [neg_neg]
  field_simp [ne_of_gt (fzzCigarParityLogReflectionGauge_pos x),
    ne_of_gt (fzzCigarParityLogReflectionGauge_pos (-x))]

theorem FZZCigarParityLocalFEReflectionData.weight_exp_eq_logForcedGain
    (D : FZZCigarParityLocalFEReflectionData) (x : ℝ) :
    D.weight (Real.exp x) = fzzCigarParityLogForcedGain x := by
  rw [D.weight_eq (Real.exp_pos x), fzzCigarParityLogForcedGain,
    fzzCigarParityLogReflectionGauge, fzzCigarParityLogReflectionGauge,
    fzzCigarParityLogSource, fzzCigarParityLogSource,
    fzzCigarParityDelay_eq_fermi (Real.exp_pos x),
    fzzCigarParityDelay_eq_fermi (Real.exp_pos (-x))]
  rw [Real.exp_neg]
  field_simp [Real.exp_ne_zero]
  rw [← Real.exp_add]
  congr 1
  ring

def FZZCigarParityLogUnitaryDensityLaw (rho : ℝ → ℝ) : Prop :=
  ∀ x, rho (-x) = fzzCigarParityLogForcedGain x ^ 2 * rho x

def fzzCigarParityLogDensityCore (rho : ℝ → ℝ) (x : ℝ) : ℝ :=
  fzzCigarParityLogReflectionGauge x ^ 2 * rho x

theorem fzzCigarParityLogUnitaryDensityLaw_iff_even_core (rho : ℝ → ℝ) :
    FZZCigarParityLogUnitaryDensityLaw rho ↔
      Function.Even (fzzCigarParityLogDensityCore rho) := by
  constructor
  · intro hrho x
    rw [fzzCigarParityLogDensityCore, fzzCigarParityLogDensityCore,
      hrho x, fzzCigarParityLogForcedGain]
    field_simp [ne_of_gt (fzzCigarParityLogReflectionGauge_pos x),
      ne_of_gt (fzzCigarParityLogReflectionGauge_pos (-x))]
  · intro hcore x
    have hx := hcore x
    rw [fzzCigarParityLogDensityCore, fzzCigarParityLogDensityCore] at hx
    rw [fzzCigarParityLogForcedGain]
    have hgneg : fzzCigarParityLogReflectionGauge (-x) ≠ 0 :=
      ne_of_gt (fzzCigarParityLogReflectionGauge_pos (-x))
    calc
      rho (-x) = (fzzCigarParityLogReflectionGauge (-x) ^ 2)⁻¹ *
          (fzzCigarParityLogReflectionGauge (-x) ^ 2 * rho (-x)) := by
            field_simp [hgneg]
      _ = (fzzCigarParityLogReflectionGauge (-x) ^ 2)⁻¹ *
          (fzzCigarParityLogReflectionGauge x ^ 2 * rho x) := by rw [hx]
      _ = (fzzCigarParityLogReflectionGauge x /
          fzzCigarParityLogReflectionGauge (-x)) ^ 2 * rho x := by
            field_simp

theorem fzzCigarParityLogUnitaryDensity_classification (rho : ℝ → ℝ) :
    ((∀ x, 0 < rho x) ∧ FZZCigarParityLogUnitaryDensityLaw rho) ↔
      ∃ h : ℝ → ℝ, (∀ x, 0 < h x) ∧ Function.Even h ∧
        ∀ x, rho x = (fzzCigarParityLogReflectionGauge x ^ 2)⁻¹ * h x := by
  constructor
  · rintro ⟨hrhopos, hrholaw⟩
    refine ⟨fzzCigarParityLogDensityCore rho, ?_,
      (fzzCigarParityLogUnitaryDensityLaw_iff_even_core rho).mp hrholaw, ?_⟩
    · intro x
      exact mul_pos (sq_pos_of_pos (fzzCigarParityLogReflectionGauge_pos x))
        (hrhopos x)
    · intro x
      rw [fzzCigarParityLogDensityCore]
      field_simp [ne_of_gt (fzzCigarParityLogReflectionGauge_pos x)]
  · rintro ⟨h, hhpos, hheven, hrho⟩
    constructor
    · intro x
      rw [hrho]
      exact mul_pos (inv_pos.mpr (sq_pos_of_pos
        (fzzCigarParityLogReflectionGauge_pos x))) (hhpos x)
    · apply (fzzCigarParityLogUnitaryDensityLaw_iff_even_core rho).mpr
      intro x
      rw [fzzCigarParityLogDensityCore, fzzCigarParityLogDensityCore,
        hrho, hrho, hheven x]
      field_simp [ne_of_gt (fzzCigarParityLogReflectionGauge_pos x),
        ne_of_gt (fzzCigarParityLogReflectionGauge_pos (-x))]

theorem fzzCigarParityLogMeasurableUnitaryDensity_classification (rho : ℝ → ℝ) :
    ((∀ x, 0 < rho x) ∧ Measurable rho ∧
        FZZCigarParityLogUnitaryDensityLaw rho) ↔
      ∃ h : ℝ → ℝ, (∀ x, 0 < h x) ∧ Measurable h ∧ Function.Even h ∧
        ∀ x, rho x = (fzzCigarParityLogReflectionGauge x ^ 2)⁻¹ * h x := by
  constructor
  · rintro ⟨hrhopos, hrhomeas, hrholaw⟩
    refine ⟨fzzCigarParityLogDensityCore rho, ?_, ?_,
      (fzzCigarParityLogUnitaryDensityLaw_iff_even_core rho).mp hrholaw, ?_⟩
    · intro x
      exact mul_pos (sq_pos_of_pos (fzzCigarParityLogReflectionGauge_pos x))
        (hrhopos x)
    · exact (continuous_fzzCigarParityLogReflectionGauge.measurable.pow_const 2).mul
        hrhomeas
    · intro x
      rw [fzzCigarParityLogDensityCore]
      field_simp [ne_of_gt (fzzCigarParityLogReflectionGauge_pos x)]
  · rintro ⟨h, hhpos, hhmeas, hheven, hrho⟩
    have hbase :
        (∀ x, 0 < rho x) ∧ FZZCigarParityLogUnitaryDensityLaw rho :=
      (fzzCigarParityLogUnitaryDensity_classification rho).mpr
        ⟨h, hhpos, hheven, hrho⟩
    refine ⟨hbase.1, ?_, hbase.2⟩
    have hgmeas : Measurable (fun x : ℝ =>
        (fzzCigarParityLogReflectionGauge x ^ 2)⁻¹ * h x) :=
      (continuous_fzzCigarParityLogReflectionGauge.measurable.pow_const 2).inv.mul hhmeas
    have heq : rho = fun x : ℝ =>
        (fzzCigarParityLogReflectionGauge x ^ 2)⁻¹ * h x := by
      funext x
      exact hrho x
    rw [heq]
    exact hgmeas

def fzzCigarParityLogWeightedReflection (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  fzzCigarParityLogForcedGain x * f (-x)

def fzzCigarParityLogWeightedEnergyDensity
    (rho f : ℝ → ℝ) (x : ℝ) : ℝ :=
  rho x * f x ^ 2

theorem fzzCigarParityLogWeightedEnergyDensity_reflection_neg
    {rho : ℝ → ℝ} (hrho : FZZCigarParityLogUnitaryDensityLaw rho)
    (f : ℝ → ℝ) (x : ℝ) :
    fzzCigarParityLogWeightedEnergyDensity rho
        (fzzCigarParityLogWeightedReflection f) (-x) =
      fzzCigarParityLogWeightedEnergyDensity rho f x := by
  simp only [fzzCigarParityLogWeightedEnergyDensity,
    fzzCigarParityLogWeightedReflection, neg_neg]
  rw [hrho x, fzzCigarParityLogForcedGain_neg]
  field_simp [ne_of_gt (fzzCigarParityLogForcedGain_pos x)]

theorem fzzCigarParityLogWeightedReflection_integrable_energy_iff
    {rho : ℝ → ℝ} (hrho : FZZCigarParityLogUnitaryDensityLaw rho)
    (f : ℝ → ℝ) :
    Integrable (fzzCigarParityLogWeightedEnergyDensity rho
      (fzzCigarParityLogWeightedReflection f)) ↔
      Integrable (fzzCigarParityLogWeightedEnergyDensity rho f) := by
  have hcomp := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrable_comp_emb
    (measurableEmbedding_neg (α := ℝ))
    (g := fzzCigarParityLogWeightedEnergyDensity rho
      (fzzCigarParityLogWeightedReflection f))
  have hfun :
      fzzCigarParityLogWeightedEnergyDensity rho
          (fzzCigarParityLogWeightedReflection f) ∘ Neg.neg =
        fzzCigarParityLogWeightedEnergyDensity rho f := by
    funext x
    exact fzzCigarParityLogWeightedEnergyDensity_reflection_neg hrho f x
  rw [hfun] at hcomp
  exact hcomp.symm

theorem integral_fzzCigarParityLogWeightedEnergyDensity_reflection
    {rho : ℝ → ℝ} (hrho : FZZCigarParityLogUnitaryDensityLaw rho)
    (f : ℝ → ℝ) :
    ∫ x, fzzCigarParityLogWeightedEnergyDensity rho
        (fzzCigarParityLogWeightedReflection f) x =
      ∫ x, fzzCigarParityLogWeightedEnergyDensity rho f x := by
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).integral_comp
    (measurableEmbedding_neg (α := ℝ))
    (fzzCigarParityLogWeightedEnergyDensity rho
      (fzzCigarParityLogWeightedReflection f))
  calc
    _ = ∫ x, fzzCigarParityLogWeightedEnergyDensity rho
        (fzzCigarParityLogWeightedReflection f) (-x) := hneg.symm
    _ = _ := by
      refine integral_congr_ae ?_
      filter_upwards with x
      exact fzzCigarParityLogWeightedEnergyDensity_reflection_neg hrho f x

def fzzCigarParityLogExplicitEvenCore (x : ℝ) : ℝ :=
  Real.exp (-2 * |x|)

def fzzCigarParityLogExplicitDensity (x : ℝ) : ℝ :=
  (fzzCigarParityLogReflectionGauge x ^ 2)⁻¹ *
    fzzCigarParityLogExplicitEvenCore x

theorem fzzCigarParityLogExplicitEvenCore_pos (x : ℝ) :
    0 < fzzCigarParityLogExplicitEvenCore x := by
  rw [fzzCigarParityLogExplicitEvenCore]
  positivity

theorem fzzCigarParityLogExplicitEvenCore_even :
    Function.Even fzzCigarParityLogExplicitEvenCore := by
  intro x
  simp [fzzCigarParityLogExplicitEvenCore]

theorem measurable_fzzCigarParityLogExplicitEvenCore :
    Measurable fzzCigarParityLogExplicitEvenCore := by
  unfold fzzCigarParityLogExplicitEvenCore
  fun_prop

theorem measurable_fzzCigarParityLogExplicitDensity :
    Measurable fzzCigarParityLogExplicitDensity := by
  unfold fzzCigarParityLogExplicitDensity
  exact (continuous_fzzCigarParityLogReflectionGauge.measurable.pow_const 2).inv.mul
    measurable_fzzCigarParityLogExplicitEvenCore

theorem fzzCigarParityLogExplicitDensity_positive_unitary :
    (∀ x, 0 < fzzCigarParityLogExplicitDensity x) ∧
      FZZCigarParityLogUnitaryDensityLaw fzzCigarParityLogExplicitDensity := by
  apply (fzzCigarParityLogUnitaryDensity_classification
    fzzCigarParityLogExplicitDensity).mpr
  exact ⟨fzzCigarParityLogExplicitEvenCore,
    fzzCigarParityLogExplicitEvenCore_pos,
    fzzCigarParityLogExplicitEvenCore_even, fun x => rfl⟩

abbrev FZZCigarParityLogExplicitWeightedL2 : Type _ :=
  GaloisForLFunctions.HTGeometry.WeightedL2 (μ := volume)
    fzzCigarParityLogExplicitDensity

def fzzCigarParityLogExplicitDensityUnitary :
    FZZCigarParityLogExplicitWeightedL2 ≃ₗᵢ[ℂ]
      Lp ℂ 2 (volume : Measure ℝ) :=
  GaloisForLFunctions.HTGeometry.weightedDensityUnitary
    fzzCigarParityLogExplicitDensity
    measurable_fzzCigarParityLogExplicitDensity
    fzzCigarParityLogExplicitDensity_positive_unitary.1

theorem fzzCigarParityLogExplicit_source_energy_density (x : ℝ) :
    fzzCigarParityLogWeightedEnergyDensity fzzCigarParityLogExplicitDensity
        fzzCigarParityLogSource x =
      Real.exp (x - 2 * |x|) := by
  rw [fzzCigarParityLogWeightedEnergyDensity,
    fzzCigarParityLogExplicitDensity, fzzCigarParityLogExplicitEvenCore,
    fzzCigarParityLogReflectionGauge]
  have hsource : fzzCigarParityLogSource x ≠ 0 :=
    ne_of_gt (fzzCigarParityLogSource_pos x)
  field_simp [hsource, Real.exp_ne_zero]
  rw [pow_two, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

theorem integrable_fzzCigarParityLogExplicit_source_energy :
    Integrable (fzzCigarParityLogWeightedEnergyDensity
      fzzCigarParityLogExplicitDensity fzzCigarParityLogSource) := by
  rw [show fzzCigarParityLogWeightedEnergyDensity
      fzzCigarParityLogExplicitDensity fzzCigarParityLogSource =
        fun x => Real.exp (x - 2 * |x|) by
    funext x
    exact fzzCigarParityLogExplicit_source_energy_density x]
  have hmajor : Integrable (fun x : ℝ => Real.exp (-|x|)) := by
    have h := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0
      (r := 1) (by norm_num)
    simpa using h
  apply hmajor.mono'
  · exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (x - 2 * |x|))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith [le_abs_self x])

def FZZCigarParitySingularWeightedHilbertDensityNoGo : Prop :=
  (∀ D : FZZCigarParityLocalFEReflectionData, ∀ x,
    D.weight (Real.exp x) = fzzCigarParityLogForcedGain x) ∧
  (∀ rho : ℝ → ℝ,
    ((∀ x, 0 < rho x) ∧ Measurable rho ∧
        FZZCigarParityLogUnitaryDensityLaw rho) ↔
      ∃ h : ℝ → ℝ, (∀ x, 0 < h x) ∧ Measurable h ∧ Function.Even h ∧
        ∀ x, rho x = (fzzCigarParityLogReflectionGauge x ^ 2)⁻¹ * h x) ∧
  ((∀ x, 0 < fzzCigarParityLogExplicitDensity x) ∧
    Measurable fzzCigarParityLogExplicitDensity ∧
    FZZCigarParityLogUnitaryDensityLaw fzzCigarParityLogExplicitDensity) ∧
  Integrable (fzzCigarParityLogWeightedEnergyDensity
    fzzCigarParityLogExplicitDensity fzzCigarParityLogSource) ∧
  (∀ rho : ℝ → ℝ, FZZCigarParityLogUnitaryDensityLaw rho → ∀ f : ℝ → ℝ,
    Integrable (fzzCigarParityLogWeightedEnergyDensity rho
      (fzzCigarParityLogWeightedReflection f)) ↔
      Integrable (fzzCigarParityLogWeightedEnergyDensity rho f))

theorem fzzCigarParity_singularWeightedHilbertDensity_noGo :
    FZZCigarParitySingularWeightedHilbertDensityNoGo := by
  exact ⟨fun D x => D.weight_exp_eq_logForcedGain x,
    fzzCigarParityLogMeasurableUnitaryDensity_classification,
    ⟨fzzCigarParityLogExplicitDensity_positive_unitary.1,
      measurable_fzzCigarParityLogExplicitDensity,
      fzzCigarParityLogExplicitDensity_positive_unitary.2⟩,
    integrable_fzzCigarParityLogExplicit_source_energy,
    fun _ hrho f => fzzCigarParityLogWeightedReflection_integrable_energy_iff hrho f⟩

end

end RHTower
