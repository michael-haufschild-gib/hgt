import Mathlib

/-!
# The Gibbs variational principle on a probability space

Tilting a probability measure by a potential shifts its log-likelihood ratio by exactly the
potential and the logarithm of the partition function.  Integrating that shift against any
absolutely continuous probability measure exhibits the difference between its relative entropy and
its mean potential as a relative entropy against the tilted measure, hence nonnegative.

The tilted measure attains equality, so the negative logarithm of the partition function is the
least value of relative entropy minus mean potential.  This is the exact duality between source
rarity and action.
-/

open MeasureTheory Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section Gibbs

variable {α : Type*} [MeasurableSpace α]

/-- The action of a candidate law against a potential: relative entropy minus mean potential. -/
def gibbsAction (q ρ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, llr q ρ x ∂q) - ∫ x, f x ∂q

/-- The log-likelihood ratio against a tilted measure is shifted by the potential and the
logarithm of the partition function. -/
theorem llr_tilted_right (q ρ : Measure α) [SigmaFinite q] [IsProbabilityMeasure ρ] {f : α → ℝ}
    (hf : Integrable (fun x => Real.exp (f x)) ρ) (hq : q ≪ ρ) :
    llr q (ρ.tilted f) =ᵐ[q] fun x => llr q ρ x - f x + Real.log (∫ x, Real.exp (f x) ∂ρ) := by
  filter_upwards [_root_.MeasureTheory.llr_tilted_right hq hf] with x hx
  rw [hx]
  ring

/-- **Gibbs lower bound.**  Every absolutely continuous candidate law has action at least the
negative logarithm of the partition function. -/
theorem neg_log_integral_exp_le_gibbsAction (ρ : Measure α) [IsProbabilityMeasure ρ]
    {f : α → ℝ} (hf : Integrable (fun x => Real.exp (f x)) ρ)
    {q : Measure α} [IsProbabilityMeasure q] (hq : q ≪ ρ)
    (hllr : Integrable (llr q ρ) q) (hfq : Integrable f q)
    (hllr' : Integrable (llr q (ρ.tilted f)) q) :
    -Real.log (∫ x, Real.exp (f x) ∂ρ) ≤ gibbsAction q ρ f := by
  have hprob : IsProbabilityMeasure (ρ.tilted f) := isProbabilityMeasure_tilted hf
  have hac : q ≪ ρ.tilted f := hq.trans (absolutelyContinuous_tilted hf)
  have hkl : 0 ≤ ∫ x, llr q (ρ.tilted f) x ∂q := by
    have hbase := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hac hllr'
    have h1 : (ρ.tilted f).real Set.univ = 1 := by simp
    have h2 : q.real Set.univ = 1 := by simp
    rw [h1, h2] at hbase
    linarith
  have hshift := llr_tilted_right q ρ hf hq
  have hint : (∫ x, llr q (ρ.tilted f) x ∂q) =
      (∫ x, llr q ρ x ∂q) - (∫ x, f x ∂q) + Real.log (∫ x, Real.exp (f x) ∂ρ) := by
    rw [integral_congr_ae hshift]
    rw [integral_add (f := fun x => llr q ρ x - f x)
      (g := fun _ : α => Real.log (∫ x, Real.exp (f x) ∂ρ)) (hllr.sub hfq)
      (integrable_const _), integral_sub hllr hfq, integral_const]
    simp
  rw [hint] at hkl
  rw [gibbsAction]
  linarith

/-- The log-likelihood ratio of a tilted measure against its base is the potential shifted by the
logarithm of the partition function. -/
theorem llr_tilted_left_self (ρ : Measure α) [IsProbabilityMeasure ρ] {f : α → ℝ}
    (hf : Integrable (fun x => Real.exp (f x)) ρ) (hfmeas : AEMeasurable f ρ) :
    llr (ρ.tilted f) ρ =ᵐ[ρ.tilted f] fun x => f x - Real.log (∫ x, Real.exp (f x) ∂ρ) := by
  have hZ : 0 < ∫ x, Real.exp (f x) ∂ρ := integral_exp_pos hf
  have hbase := (tilted_absolutelyContinuous ρ f).ae_le (rnDeriv_tilted_left_self hfmeas)
  filter_upwards [hbase] with x hx
  rw [llr, hx, ENNReal.toReal_ofReal (by positivity),
    Real.log_div (ne_of_gt (Real.exp_pos _)) (ne_of_gt hZ), Real.log_exp]

/-- **Gibbs equality.**  The tilted measure attains the negative logarithm of the partition
function. -/
theorem gibbsAction_tilted (ρ : Measure α) [IsProbabilityMeasure ρ] {f : α → ℝ}
    (hf : Integrable (fun x => Real.exp (f x)) ρ) (hfmeas : AEMeasurable f ρ)
    (hfq : Integrable f (ρ.tilted f)) :
    gibbsAction (ρ.tilted f) ρ f = -Real.log (∫ x, Real.exp (f x) ∂ρ) := by
  have hprob : IsProbabilityMeasure (ρ.tilted f) := isProbabilityMeasure_tilted hf
  have hshift := llr_tilted_left_self ρ hf hfmeas
  rw [gibbsAction, integral_congr_ae hshift]
  rw [integral_sub hfq (integrable_const _), integral_const]
  simp

theorem integrable_llr_tilted_left_self (ρ : Measure α) [IsProbabilityMeasure ρ] {f : α → ℝ}
    (hf : Integrable (fun x => Real.exp (f x)) ρ) (hfmeas : AEMeasurable f ρ)
    (hfq : Integrable f (ρ.tilted f)) :
    Integrable (llr (ρ.tilted f) ρ) (ρ.tilted f) := by
  have hprob : IsProbabilityMeasure (ρ.tilted f) := isProbabilityMeasure_tilted hf
  refine (Integrable.congr (hfq.sub (integrable_const
    (Real.log (∫ x, Real.exp (f x) ∂ρ)))) ?_)
  exact (llr_tilted_left_self ρ hf hfmeas).symm

/-- **Gibbs variational principle.**  The negative logarithm of the partition function is the least
action over all absolutely continuous candidate laws. -/
theorem isLeast_gibbsAction (ρ : Measure α) [IsProbabilityMeasure ρ] {f : α → ℝ}
    (hf : Integrable (fun x => Real.exp (f x)) ρ) (hfmeas : AEMeasurable f ρ)
    (hfq : Integrable f (ρ.tilted f)) :
    IsLeast {a : ℝ | ∃ q : Measure α, ∃ _ : IsProbabilityMeasure q, q ≪ ρ ∧
        Integrable (llr q ρ) q ∧ Integrable f q ∧ Integrable (llr q (ρ.tilted f)) q ∧
        a = gibbsAction q ρ f}
      (-Real.log (∫ x, Real.exp (f x) ∂ρ)) := by
  have hprob : IsProbabilityMeasure (ρ.tilted f) := isProbabilityMeasure_tilted hf
  constructor
  · refine ⟨ρ.tilted f, hprob, tilted_absolutelyContinuous ρ f,
      integrable_llr_tilted_left_self ρ hf hfmeas hfq, hfq, ?_, ?_⟩
    · refine Integrable.congr (integrable_zero α ℝ (ρ.tilted f)) ?_
      exact (llr_self (ρ.tilted f)).symm
    · exact (gibbsAction_tilted ρ hf hfmeas hfq).symm
  · rintro a ⟨q, hqprob, hq, hllr, hfq', hllr', rfl⟩
    exact neg_log_integral_exp_le_gibbsAction ρ hf hq hllr hfq' hllr'

end Gibbs

end

end GaloisForLFunctions.HTGeometry
