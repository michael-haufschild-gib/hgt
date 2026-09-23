import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedCurrentCutoff
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalModeAction

/-!
# Original source-contact work on the physical left field

The fixed ingoing onset tensor is paired using the actual BM inverse metric and coordinate
volume density. All sixteen test entries remain free. Its self-pairing vanishes, whereas its
stream pairing retains the radial derivative at fixed ingoing time. The original physical
left-field specialization retains actual derivatives and an independent source occurrence.

The switched-source identity includes both the literal mixed Einstein source and this contact.
It does not identify the complete nonlinear source, prove boundary cancellation, or establish
fixed-clock extinction. No homogeneous mode equation outside its admitted band is asserted.
-/

set_option autoImplicit false
namespace RHTower.D4BMCurrentSourceAction
open GaloisForLFunctions.HTGeometry
open D4BMBackground D4BMModularCore D4BMMixedActionCurrent
open D4BMMetricReconstruction ScalarTwoJet
noncomputable section

/-- Original coordinate-volume Einstein pairing, with both inverse indices. -/
def sourceAction (p : ExteriorPoint) (M S : Matrix (Fin 4) (Fin 4) ℂ) : ℂ :=
  let G := D4BMBackground.metric (p.val 1) (p.val 3)
  (p.val 1 : ℂ)^(2 : ℕ) / (p.val 3 : ℂ)^(2 : ℕ) *
    ∑ i, ∑ j, (G⁻¹ * M * (G⁻¹).transpose) i j * S i j

private theorem mixed_action (p : ExteriorPoint) (M : Matrix (Fin 4) (Fin 4) ℂ)
    (T R : Fin 2 → ℂ) :
    sourceAction p M (mixedMatrix T R) =
      ∑ k : Fin 2,
        (-(M 0 (if k=0 then 2 else 3) + M (if k=0 then 2 else 3) 0) * T k /
            ((p.val 1 : ℂ)^(2 : ℕ)-1) +
        ((p.val 1 : ℂ)^(2 : ℕ)-1) *
          (M 1 (if k=0 then 2 else 3) + M (if k=0 then 2 else 3) 1) * R k) := by
  have hr : (p.val 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  dsimp only [sourceAction]
  rw [metric_inverse _ _ hr hy hf, Matrix.diagonal_transpose]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp [mixedMatrix, Fin.sum_univ_succ]
  field_simp
  ring

/-- The complete original onset tensor pairs with the ingoing radial part of every test.
No symmetry, scalar/vector restriction, or field equation is imposed on the test matrix. -/
theorem onset_action (q : XiZeroCopy) (b : Bool) (a : ℂ) (p : ExteriorPoint)
    (M : Matrix (Fin 4) (Fin 4) ℂ) :
    sourceAction p M (currentOnsetTensor q b a p.val) =
      currentCutoffSlope p.val / (p.val 1 : ℂ)^(2 : ℕ) *
        ∑ k : Fin 2, orbitCurrent q b a (angularPoint p.val) k p.val *
          (M 1 (if k=0 then 2 else 3) + M (if k=0 then 2 else 3) 1 -
            (M 0 (if k=0 then 2 else 3) + M (if k=0 then 2 else 3) 0) /
              ((p.val 1 : ℂ)^(2 : ℕ)-1)) := by
  let D : Fin 2 → ℂ := fun k => currentCutoffSlope p.val *
    orbitCurrent q b a (angularPoint p.val) k p.val
  have hN : currentOnsetTensor q b a p.val =
      mixedMatrix (fun k => D k / (p.val 1 : ℂ)^(2 : ℕ))
        (fun k => D k / ((p.val 1 : ℂ)^(2 : ℕ) * ((p.val 1 : ℂ)^(2 : ℕ)-1))) := rfl
  rw [hN, mixed_action]
  have hr : (p.val 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  simp only [Fin.sum_univ_succ]
  dsimp only [D]
  field_simp
  ring

/-- The characteristic contact is null under its original self-pairing. -/
theorem onset_self_action (q : XiZeroCopy) (b : Bool) (a : ℂ) (p : ExteriorPoint) :
    sourceAction p (currentOnsetTensor q b a p.val)
      (currentOnsetTensor q b a p.val) = 0 := by
  rw [onset_action]
  have hr : (p.val 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans zero_lt_one p.property.1))
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  apply mul_eq_zero.mpr
  right
  apply Finset.sum_eq_zero
  intro k _
  apply mul_eq_zero.mpr
  right
  fin_cases k <;> simp [currentOnsetTensor]
  all_goals field_simp
  all_goals ring

/-- An actual stream test retains the full fixed-ingoing-time derivative of the contact. -/
theorem onset_stream_action (q : XiZeroCopy) (b : Bool) (a : ℂ) (p : ExteriorPoint)
    (P : Fin 2 → ScalarTwoJet (Fin 4) ℂ) :
    sourceAction p (streamMetricJet (p.val 1) P).metric (currentOnsetTensor q b a p.val) =
      -2 * currentCutoffSlope p.val / (p.val 1 : ℂ)^(2 : ℕ) *
        ∑ k : Fin 2, orbitCurrent q b a (angularPoint p.val) k p.val *
          ((P k).first 1 - (P k).first 0 / ((p.val 1 : ℂ)^(2 : ℕ)-1)) := by
  rw [onset_action]
  have hf : (p.val 1 : ℂ)^(2 : ℕ)-1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1)^(2 : ℕ)-1 ≠ 0)
  simp [streamMetricJet, mixedJet, mixedMatrix, Fin.sum_univ_succ]
  field_simp
  ring

/-- Contact work on the original physical left-mode field, with its actual derivatives.
This identity does not assert a homogeneous mode equation outside its admitted band. -/
theorem physical_left_onset_action (q r : XiZeroCopy) (b outer : Bool) (a w : ℂ)
    (p : ExteriorPoint) :
    let Ψ := D4BMPhysicalModeAction.physicalLeftModeStream r w outer
    sourceAction p (streamMetricJet (p.val 1) (fun k => ofField (Ψ k) p.val)).metric
      (currentOnsetTensor q b a p.val) =
      -2 * currentCutoffSlope p.val / (p.val 1 : ℂ)^(2 : ℕ) *
        ∑ k : Fin 2, orbitCurrent q b a (angularPoint p.val) k p.val *
          (coordDeriv 1 (Ψ k) p.val - coordDeriv 0 (Ψ k) p.val /
            ((p.val 1 : ℂ)^(2 : ℕ)-1)) := by
  exact onset_stream_action q b a p _

/-- The actual switched tensor's left-field pairing includes both the literal source
and its characteristic contact. Source and reader occurrences stay independent. -/
theorem physical_left_switched_action (q r : XiZeroCopy) (b outer : Bool) (a w : ℂ)
    (p : ExteriorPoint) :
    let Ψ := D4BMPhysicalModeAction.physicalLeftModeStream r w outer
    let M := (streamMetricJet (p.val 1) (fun k => ofField (Ψ k) p.val)).metric
    sourceAction p M (switchedCurrentSource q b a p.val) =
      currentCutoff p.val * sourceAction p M
        (literalMixedSource q b (p.val 1)
          (D4BMFundamentalScalarMetric.envelope (physicalRate q b) a p.val)
          (angularPoint p.val)) -
      2 * currentCutoffSlope p.val / (p.val 1 : ℂ)^(2 : ℕ) *
        ∑ k : Fin 2, orbitCurrent q b a (angularPoint p.val) k p.val *
          (coordDeriv 1 (Ψ k) p.val - coordDeriv 0 (Ψ k) p.val /
            ((p.val 1 : ℂ)^(2 : ℕ)-1)) := by
  dsimp only
  let M := (streamMetricJet (p.val 1) (fun k =>
    ofField (D4BMPhysicalModeAction.physicalLeftModeStream r w outer k) p.val)).metric
  have hsplit : sourceAction p M (switchedCurrentSource q b a p.val) =
      currentCutoff p.val * sourceAction p M
        (literalMixedSource q b (p.val 1)
          (D4BMFundamentalScalarMetric.envelope (physicalRate q b) a p.val)
          (angularPoint p.val)) + sourceAction p M (currentOnsetTensor q b a p.val) := by
    dsimp only [sourceAction]
    simp_rw [switchedCurrentSource_eq]
    simp only [mul_add, Finset.sum_add_distrib]
    simp_rw [mul_left_comm _ (currentCutoff p.val), ← Finset.mul_sum]
    ring
  rw [hsplit, physical_left_onset_action]
  ring

end
end RHTower.D4BMCurrentSourceAction
