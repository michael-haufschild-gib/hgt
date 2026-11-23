import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.LineLoss
import GaloisForLFunctions.HTGeometry.HilbertSchmidtRankOne

/-! # Additivity of fourth-trace losses for separated line corrections

A rank-one change sees its input only on its generating direction.
Earlier corrections disappear there when the heated directions are orthogonal.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap InnerProductSpace

def lineCorrection (v : Gas) : GasOp := squareHeat.val-(projected (omitLine v))^2

theorem lineCorrection_eq (v : Gas) : lineCorrection v =
    ((‖v‖^2:ℝ):ℂ)⁻¹ • rankOne ℂ (criticalOperator v) (criticalOperator v) := by
  rw [lineCorrection,line_square,sub_sub_cancel]

private theorem correction_facts (v : Gas) :
    IsSelfAdjoint (lineCorrection v) ∧ (lineCorrection v).IsHilbertSchmidt := by
  refine ⟨squareHeat.property.1.sub ((projected_positive _).isSelfAdjoint.pow 2),?_⟩
  rw [lineCorrection_eq]
  exact (HTGeometry.isHilbertSchmidt_rankOne _ _).smul _

private theorem correction_vanishes {v w : Gas}
    (ho : inner ℂ (criticalOperator v) (criticalOperator w) = 0) :
    lineCorrection v (criticalOperator w) = 0 := by
  rw [lineCorrection_eq]
  change ((‖v‖^2:ℝ):ℂ)⁻¹ • (inner ℂ (criticalOperator v) (criticalOperator w) • criticalOperator v) = 0
  rw [ho,zero_smul,smul_zero]

/-- Finite orthogonal changes of squared heat contribute their individual trace losses additively. -/
theorem orthogonal_trace_sum {ι : Type*} (v : ι → Gas)
    (ho : ∀ i j, i ≠ j → inner ℂ (criticalOperator (v i)) (criticalOperator (v j)) = 0)
    (s : Finset ι) :
    opTrace ((squareHeat.val-∑ i ∈ s, lineCorrection (v i))^2) =
      opTrace (squareHeat.val^2)+∑ i ∈ s,
        (opTrace ((squareHeat.val-lineCorrection (v i))^2)-opTrace (squareHeat.val^2)) := by
  classical
  have h (t : Finset ι) : IsSelfAdjoint (∑ i ∈ t, lineCorrection (v i)) ∧
      (∑ i ∈ t, lineCorrection (v i)).IsHilbertSchmidt := by
    induction t using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using
        (show IsSelfAdjoint (0:GasOp) ∧ (0:GasOp).IsHilbertSchmidt from ⟨IsSelfAdjoint.zero _,isHilbertSchmidt_zero⟩)
    | @insert a t ha ih =>
      rw [Finset.sum_insert ha]
      exact ⟨(correction_facts _).1.add ih.1,(correction_facts _).2.add ih.2⟩
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    let B : HSObservable Gas := ⟨squareHeat.val-∑ i ∈ s, lineCorrection (v i),
      squareHeat.property.1.sub (h s).1,squareHeat.property.2.sub (h s).2⟩
    let x := criticalOperator (v a)
    have hz : (∑ i ∈ s, lineCorrection (v i)) x = 0 := by
      rw [sum_apply]
      exact Finset.sum_eq_zero (fun i hi => correction_vanishes (ho i a (fun eqn => ha (eqn ▸ hi))))
    have hBx : B.val x = squareHeat.val x := by
      change squareHeat.val x-(∑ i ∈ s, lineCorrection (v i)) x = squareHeat.val x
      rw [hz,sub_zero]
    have hupdate (T : HSObservable Gas) :
        opTrace ((T.val-lineCorrection (v a))^2) = opTrace (T.val^2)-
          2*((‖v a‖^2:ℝ):ℂ)⁻¹*inner ℂ x (T.val x)+(((‖v a‖^2:ℝ):ℂ)⁻¹)^2*(inner ℂ x x)^2 := by
      rw [lineCorrection_eq]
      exact rank_one_trace_square T x _
    rw [Finset.sum_insert ha,Finset.sum_insert ha,
      show squareHeat.val-(lineCorrection (v a)+∑ i ∈ s, lineCorrection (v i)) =
        B.val-lineCorrection (v a) from by dsimp only [B]; abel,hupdate B,hupdate squareHeat,hBx]
    change opTrace (B.val^2) = _ at ih
    rw [ih]
    ring

#print axioms orthogonal_trace_sum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
