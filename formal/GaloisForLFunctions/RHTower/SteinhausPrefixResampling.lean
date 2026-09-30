import GaloisForLFunctions.RHTower.SteinhausFrozenPrefixSecondMoment
import GaloisForLFunctions.HTGeometry.InfinitePiSumSplit
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Integral.MeanInequalities

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel

/-- Joint measurability of the literal operation retaining one prefix and resampling its exterior. -/
theorem measurable_freezeSteinhausPrefix_joint (S : Finset ℕ) :
    Measurable (fun z : Omega × Omega => freezeSteinhausPrefix S z.1 z.2) := by
  classical
  apply measurable_pi_lambda
  intro p
  by_cases hp : p ∈ S
  · simpa only [freezeSteinhausPrefix, if_pos hp, Function.comp_def] using
      (measurable_pi_apply p).comp measurable_fst
  · simpa only [freezeSteinhausPrefix, if_neg hp, Function.comp_def] using
      (measurable_pi_apply p).comp measurable_snd

/-- Retaining the prefix of one sample and the exterior of an independent sample preserves the law. -/
theorem map_freezeSteinhausPrefix (S : Finset ℕ) :
    Measure.map (fun z : Omega × Omega => freezeSteinhausPrefix S z.1 z.2)
      (steinhausMeasure.prod steinhausMeasure) = steinhausMeasure := by
  classical
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : ℕ ⊕ ℕ => ℝ)
  let sel : ℕ → ℕ ⊕ ℕ := fun p => if p ∈ S then Sum.inl p else Sum.inr p
  have hsel : Function.Injective sel := by
    intro p q hpq
    have h := congrArg (Sum.elim id id) hpq
    simpa only [sel, apply_ite, Sum.elim_inl, Sum.elim_inr, id_eq, ite_self] using h
  have hcomp : (fun z : Omega × Omega => freezeSteinhausPrefix S z.1 z.2) =
      (fun x : ℕ ⊕ ℕ → ℝ => fun p => x (sel p)) ∘ e.symm := by
    ext z p
    by_cases hp : p ∈ S <;> simp [freezeSteinhausPrefix, sel, hp, e] <;> rfl
  have hsplit := GaloisForLFunctions.HTGeometry.map_sumPiEquivProdPi_infinitePi
    (X := fun _ : ℕ ⊕ ℕ => ℝ)
    (fun _ => volume.restrict (Set.Icc (0 : ℝ) 1))
  rw [hcomp, ← Measure.map_map (by fun_prop) e.symm.measurable]
  change Measure.map _ (Measure.map e.symm
    ((Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))).prod
      (Measure.infinitePi (fun _ : ℕ => volume.restrict (Set.Icc (0 : ℝ) 1))))) = _
  rw [hsplit]
  exact Measure.map_infinitePi_infinitePi_of_inj hsel

/-- Every measurable nonnegative test has its original expectation after prefix resampling. -/
theorem lintegral_lintegral_freezeSteinhausPrefix (S : Finset ℕ)
    (f : Omega → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ η, f (freezeSteinhausPrefix S ω η) ∂steinhausMeasure ∂steinhausMeasure) =
      ∫⁻ ω, f ω ∂steinhausMeasure := by
  have hm : Measurable (fun z : Omega × Omega => f (freezeSteinhausPrefix S z.1 z.2)) := by
    simpa only [Function.comp_def] using hf.comp (measurable_freezeSteinhausPrefix_joint S)
  rw [← lintegral_prod _ hm.aemeasurable,
    ← lintegral_map hf (measurable_freezeSteinhausPrefix_joint S),
    map_freezeSteinhausPrefix]

/-- First moment bounded by the average square root of the literal frozen-prefix second moment. -/
theorem lintegral_le_frozenPrefix_secondMoment_sqrt (S : Finset ℕ)
    (f : Omega → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, f ω ∂steinhausMeasure) ≤
      ∫⁻ ω, (∫⁻ η, f (freezeSteinhausPrefix S ω η) ^ (2 : ℝ)
        ∂steinhausMeasure) ^ (1 / 2 : ℝ) ∂steinhausMeasure := by
  rw [← lintegral_lintegral_freezeSteinhausPrefix S f hf]
  apply lintegral_mono
  intro ω
  have hmeas := hf.comp (continuous_freezeSteinhausPrefix S ω).measurable
  have h := ENNReal.lintegral_mul_norm_pow_le (μ := steinhausMeasure)
    (hmeas.pow_const (2 : ℝ)).aemeasurable
    (measurable_const : Measurable (fun _ : Omega => (1 : ℝ≥0∞))).aemeasurable
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  simpa only [Function.comp_def, ← ENNReal.rpow_mul, mul_one_div_cancel (by norm_num : (2 : ℝ) ≠ 0),
    ENNReal.rpow_one, ENNReal.one_rpow, mul_one, lintegral_const,
    measure_univ, mul_one] using h

end RHTower
