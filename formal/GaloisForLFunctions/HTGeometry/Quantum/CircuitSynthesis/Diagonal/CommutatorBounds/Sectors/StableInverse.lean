import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.CommutatorBounds.Sectors.Inverse
import Mathlib.Topology.MetricSpace.Contracting

/-! # Stability of the opposite-sector commutator inverse -/

open Real Matrix
open scoped Matrix.Norms.L2Operator NNReal
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds.Sectors
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] {J : Type*} [DecidableEq J]

private theorem bracket_bound (E X : Matrix I I ℂ) :
    ‖E*X-X*E‖ ≤ 2*‖E‖*‖X‖ :=
  (norm_sub_le ..).trans ((add_le_add (norm_mul_le E X) (norm_mul_le X E)).trans_eq (by ring))

private theorem inverse_fixed_point (b : I → J) (d : I → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) (E V : Matrix I I ℂ)
    (hsmall : 2*(sqrt packConstant/g)*‖E‖ ≤ 1/2) :
    ∃ X : Matrix I I ℂ, inverse b d (V-(E*X-X*E))=X := by
  let R := sqrt packConstant/g
  have hR : 0 ≤ R := div_nonneg (sqrt_nonneg _) hg.le
  let q : ℝ≥0 := ⟨2*R*‖E‖,by positivity⟩
  have hq : (q:ℝ)<1 := hsmall.trans_lt (by norm_num)
  let F := fun X : Matrix I I ℂ => inverse b d (V-(E*X-X*E))
  have hF : ContractingWith q F := by
    refine ⟨(show q<1 from hq),LipschitzWith.of_dist_le_mul ?_⟩
    intro X Y
    rw [dist_eq_norm,dist_eq_norm]
    change ‖inverse b d _-inverse b d _‖ ≤ (2*R*‖E‖)*‖X-Y‖
    rw [←inverse_sub]
    have heq : (V-(E*X-X*E))-(V-(E*Y-Y*E))=E*(Y-X)-(Y-X)*E := by
      simp only [mul_sub,sub_mul]; abel
    rw [heq]
    calc
      _ ≤ R*‖E*(Y-X)-(Y-X)*E‖ := norm_inverse_le b d hg hsep _
      _ ≤ R*(2*‖E‖*‖Y-X‖) := mul_le_mul_of_nonneg_left (bracket_bound ..) hR
      _ = _ := by rw [norm_sub_rev Y X]; ring
  exact ⟨hF.fixedPoint F,hF.fixedPoint_isFixedPt⟩

/-- A sector-preserving perturbation smaller than the simple diagonal
spacing leaves an exact inverse on odd fields. The central field and
bath need no ordering in energy. -/
theorem stable_inverse (b : I → J) (d : I → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) (E V : Matrix I I ℂ)
    (he : Within b E) (hv : Across b V) (hsmall : 2*(sqrt packConstant/g)*‖E‖ ≤ 1/2) :
    let D := diagonal fun i => (d i:ℂ)
    ∃ X : Matrix I I ℂ, Across b X ∧ (D+E)*X-X*(D+E)=V ∧
      ‖X‖ ≤ 2*(sqrt packConstant/g)*‖V‖ := by
  intro D
  let R := sqrt packConstant/g
  have hR : 0 ≤ R := div_nonneg (sqrt_nonneg _) hg.le
  obtain ⟨X,hX⟩ := inverse_fixed_point b d hg hsep E V hsmall
  have hodd := inverse_across b d (V-(E*X-X*E))
  rw [hX] at hodd
  have hy : Across b (V-(E*X-X*E)) := by
    intro i j hij
    rw [Matrix.sub_apply,hv i j hij,across_bracket he hodd i j hij,sub_zero]
  have hinj : Function.Injective d := by
    intro i j h
    by_contra hn
    have hb := hsep i j hn
    rw [h,sub_self,abs_zero] at hb
    exact hg.not_ge hb
  have hsolve := commutator_inverse b d hinj _ hy
  -- The fixed point cancels the perturbation commutator exactly.
  have hc : D*X-X*D = V-(E*X-X*E) := by
    change D*inverse b d _-inverse b d _*D = _ at hsolve
    rwa [hX] at hsolve
  refine ⟨X,hodd,?_,?_⟩
  · rw [add_mul,mul_add]
    calc _ = (D*X-X*D)+(E*X-X*E) := by abel
         _ = _ := by rw [hc,sub_add_cancel]
  · have hb := norm_inverse_le b d hg hsep (V-(E*X-X*E))
    rw [hX] at hb
    change ‖X‖ ≤ R*‖V-(E*X-X*E)‖ at hb
    have hnorm := (norm_sub_le V (E*X-X*E)).trans (add_le_add le_rfl (bracket_bound E X))
    have h := hb.trans (mul_le_mul_of_nonneg_left hnorm hR)
    change 2*R*‖E‖ ≤ 1/2 at hsmall
    change ‖X‖ ≤ 2*R*‖V‖
    nlinarith only [h,mul_le_mul_of_nonneg_right hsmall (norm_nonneg X)]

#print axioms stable_inverse
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.CommutatorBounds.Sectors
