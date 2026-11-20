import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnSpacing.PolynomialFloor
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline

/-! # First resolved return from a circuit approximation with error margin -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- Returning projectively near identity repeats any affordable circuit
with two percent initial error at ten percent error, within a deadline
measured from its own time origin. -/
theorem first_circuit_return_from_accurate_anchor {n s : ℕ} (H : selfAdjoint (Reg n)) (v : ℝ)
    (hv : HasProjectiveCircuitApproximation n (1/50:ℝ) s (unitaryEvolution H.val v)) :
    ∃ w : ℝ, IsLeast {t | v+1 ≤ t ∧ HasProjectiveCircuitApproximation n (1/10:ℝ) s
      (unitaryEvolution H.val t)} w ∧ w-v ≤ (100:ℝ)^(2^n-1) := by
  let d := 2^n-1
  let e : (Fin n → Bool) ≃ Fin (d+1) := (Fintype.equivFin _).trans
    (finCongr (by simp only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool]
                  have hp : 0 < (2:ℕ)^n := by positivity
                  dsimp [d]; omega))
  obtain ⟨t,ht,hid⟩ := projective_operator_zero_gate_return_after e H 0 99
  norm_num at ht hid
  have hnext : HasProjectiveCircuitApproximation n (1/10:ℝ) s (unitaryEvolution H.val (v+t)) := by
    by_contra hno
    have hfar : ProjectiveCircuitSeparated n (1/10:ℝ) s (unitaryEvolution H.val (v+t)) := by
      intro z hz C hC
      exact lt_of_not_ge fun h => hno ⟨z,hz,C,hC,h⟩
    have h := projectiveCircuitSeparated_unitaryEvolution_backward_cone H (Nat.zero_le s) hfar hid
      (show (1/50:ℝ)+_ ≤ 1/10 by linarith only [Real.pi_lt_four])
    rw [add_sub_cancel_right,Nat.sub_zero] at h
    obtain ⟨z,hz,C,hC,herr⟩ := hv
    exact (not_lt_of_ge herr) (h z hz C hC)
  obtain ⟨w,hw,hcheap,hfirst⟩ := projective_first_circuit_visit_deadline e H (v+1) s
  have hmin : IsLeast {t | v+1 ≤ t ∧ HasProjectiveCircuitApproximation n (1/10:ℝ) s
      (unitaryEvolution H.val t)} w := by
    refine ⟨⟨hw.1,hcheap⟩,?_⟩
    rintro u ⟨hu,z,hz,C,hC,herr⟩
    exact le_of_not_gt fun h => (not_lt_of_ge herr) (hfirst u ⟨hu,h⟩ z hz C hC)
  have hw' := hmin.2 (show v+t ∈ _ from ⟨(by linarith only [ht.1] : v+1 ≤ v+t),hnext⟩)
  refine ⟨w,hmin,?_⟩
  change w-v ≤ (100:ℝ)^d
  linarith only [hw',ht.2]

/-- On almost every Gaussian chain the first unit-resolved return from
every sufficiently accurate low-cost anchor lies strictly beyond N^(1/48)/4
and at most 100^(2^N−1) time units away. The same budget is used at both ends. -/
theorem gaussian_pauli_first_return_from_accurate_anchor :
    ∃ c : ℝ, 0 < c ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let H := pathHamiltonian (pathPauliDisorderShell ω n)
      ∀ (v : ℝ) (s : ℕ), (s:ℝ) < c*Real.sqrt (N:ℝ) →
        HasProjectiveCircuitApproximation N (1/50:ℝ) s (unitaryEvolution H v) →
        ∃ w : ℝ, IsLeast {t | v+1 ≤ t ∧ HasProjectiveCircuitApproximation N (1/10:ℝ) s
          (unitaryEvolution H t)} w ∧ (N:ℝ)^((48:ℝ)⁻¹)/4 < w-v ∧ w-v ≤ (100:ℝ)^(2^N-1) := by
  obtain ⟨A,c,hA,hc,hw⟩ := gaussian_pauli_polynomial_interval_cost_floor
  obtain ⟨m,hm⟩ := exists_nat_gt A
  refine ⟨c/2,half_pos hc,?_⟩
  filter_upwards [hw] with ω hω
  filter_upwards [hω,eventually_ge_atTop m] with n hn hsize
  let N := n+2
  let H : selfAdjoint (Reg N) := ⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩
  intro _ _ v s hcost hv
  obtain ⟨w,hmin,hdeadline⟩ := first_circuit_return_from_accurate_anchor H v hv
  refine ⟨w,hmin,?_,hdeadline⟩
  by_contra! hshort
  have hv' : HasProjectiveCircuitApproximation N (1/10:ℝ) s (unitaryEvolution H.val v) := by
    obtain ⟨z,hz,C,hC,he⟩ := hv
    exact ⟨z,hz,C,hC,he.trans (by norm_num)⟩
  have hstart : A/(N:ℝ) ≤ 1 := by
    apply (div_le_iff₀ (show 0 < (N:ℝ) by dsimp [N]; positivity)).mpr
    rw [one_mul]
    exact hm.le.trans (by exact_mod_cast (show m ≤ N by dsimp [N]; omega))
  have hlag : A/(N:ℝ) ≤ w-v := hstart.trans (by linarith only [hmin.1.1])
  have hl := (hn (w-v) hlag hshort).2 v s s hv'
  rw [show v+(w-v)=w by ring] at hl
  have hx := hl hmin.1.2
  change c*Real.sqrt (N:ℝ) ≤ _ at hx
  linarith only [hx,hcost]

#print axioms gaussian_pauli_first_return_from_accurate_anchor
end
end GaloisForLFunctions.HTGeometry
