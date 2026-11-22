import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.MarkedLine
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.LocalAxes
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.ProjectorCommutator
import GaloisForLFunctions.HTGeometry.SiteSupportedEvolutionFactorization

/-! # A single eigenphase transmits between every ordered pair of sites -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenlineSignals
noncomputable section
open UntouchedSites
private abbrev Mat (N : ℕ) := SpinMatrix (Fin N)

private theorem axis_orthogonal (F : Fin 2→Fin 3→ℂ) (h : ∀ i a, ((F i a).re:ℂ)=F i a) :
    ∃ u : Fin 3→ℝ, u ⬝ᵥ u=1 ∧ ∀ i, (∑ a, (u a:ℂ)*F i a)=0 := by
  let M : Matrix (Fin 2) (Fin 3) ℝ := fun i a => (F i a).re
  obtain ⟨u,hu,hm⟩ := exists_unit_axis M
  refine ⟨u,hu,fun i => ?_⟩
  have hrow : (∑ a, u a*(F i a).re)=0 := by
    simpa only [Matrix.mulVec,dotProduct,M,Pi.zero_apply,mul_comm] using congrFun hm i
  have he := congrArg Complex.ofReal hrow
  simpa only [Complex.ofReal_sum,Complex.ofReal_mul,h,Complex.ofReal_zero] using he

private theorem choose_axis {N : ℕ} (V : Matrix.unitaryGroup (Fin N→Bool) ℂ)
    (r : Fin N→Bool) (i : Fin N) (K : Fin 2→Mat N) (hk : ∀ l, IsSelfAdjoint (K l))
    (hc : ∀ l a, Commute (K l) (spin i a)) :
    ∃ u : Fin 3→ℝ, u ⬝ᵥ u=1 ∧ ∀ l, expectation V r (K l*axis i u)=0 := by
  let F (l : Fin 2) (a : Fin 3) := expectation V r (K l*spin i a)
  have hr (l a) : ((F l a).re:ℂ)=F l a := by
    apply expectation_real
    change star (K l*spin i a)=_
    rw [star_mul,(hk l).star_eq,
      show star (spin i a)=spin i a from (finitePauliMatrix_isHermitian _).isSelfAdjoint.star_eq,
      (hc l a).symm.eq]
  obtain ⟨u,hu,h⟩ := axis_orthogonal F hr
  refine ⟨u,hu,fun l => ?_⟩
  simpa only [expectation,axis,Finset.mul_sum,Finset.sum_mul,Matrix.smul_mul,
    Matrix.mul_smul,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,F] using h l

/-- For any basis, changing just one eigenphase creates a signal of
at least its chord length between each two distinct qubits. -/
theorem marked_chord_signal {N : ℕ} (V : Matrix.unitaryGroup (Fin N→Bool) ℂ)
    (r : Fin N→Bool) (z : ℂ) {i j : Fin N} (hij : i ≠ j) :
    ∃ A B : Mat N, IsSiteSupported {i} A ∧ IsSiteSupported {j} B ∧
      A ∈ unitary _ ∧ B ∈ unitary _ ∧
      let R := twist z (marked V r)
      ‖1-z‖ ≤ ‖(star R*A*R)*B-B*(star R*A*R)‖ := by
  obtain ⟨u,hu,h⟩ := choose_axis V r i (fun _ => 1) (fun _ => star_one _)
    (fun _ _ => Commute.one_left _)
  let A := axis i u
  have ha : expectation V r A=0 := by simpa only [one_mul] using h 0
  have hd : Disjoint ({i}:Finset (Fin N)) {j} := Finset.disjoint_singleton.mpr hij
  let K : Fin 2→Mat N := ![1,A]
  obtain ⟨v,hv,h'⟩ := choose_axis V r j K (by
    intro l; fin_cases l
    · exact star_one _
    · exact axis_selfAdjoint i u) (by
    intro l a; fin_cases l
    · exact Commute.one_left _
    · exact commute_of_isSiteSupported_disjoint hd (axis_supported i u) (spin_supported j a))
  let B := axis j v
  have hb : expectation V r B=0 := by simpa only [K,Matrix.cons_val_zero,one_mul] using h' 0
  have hab : expectation V r (A*B)=0 := h' 1
  have hA := axis_unitary i u hu
  have hB := axis_unitary j v hv
  refine ⟨A,B,axis_supported i u,axis_supported j v,hA,hB,?_⟩
  exact chord_le_commutator z _ A B (marked_self V r) (marked_square V r) (marked_norm V r) hA hB
    (commute_of_isSiteSupported_disjoint hd (axis_supported i u) (axis_supported j v))
    (marked_sandwich_zero V r A ha) (marked_sandwich_zero V r B hb) (marked_sandwich_zero V r _ hab)

#print axioms marked_chord_signal
end
end GaloisForLFunctions.HTGeometry.EigenlineSignals
