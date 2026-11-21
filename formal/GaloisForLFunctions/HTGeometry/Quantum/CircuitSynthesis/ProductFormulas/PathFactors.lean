import GaloisForLFunctions.HTGeometry.PathHamiltonianSiteRestriction
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.OneGate

/-! # One-gate generators of the sparse Pauli path Hamiltonian -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
local instance pauliPathFactorCStarAlgebra (n : ℕ) : CStarAlgebra (Reg n) where

private def pathGateLabel {n : ℕ} (l : PathLabel n) : PauliTracelessLabel (n+2) 2 := by
  refine ⟨pathWord l,?_,pathWord_ne_identity l⟩
  rw [pauliWeight]
  rcases l with ⟨s,a⟩ | ⟨e,ab⟩
  · apply (Finset.card_le_card (t := {s}) ?_).trans (by simp)
    intro i hi
    by_contra hn
    have h : i ≠ s := by simpa using hn
    simpa [pathWord,onsiteWord,h] using (Finset.mem_filter.mp hi).2
  · apply (Finset.card_le_card (t := {e.castSucc,e.succ}) ?_).trans
      ((Finset.card_insert_le _ _).trans (by simp))
    intro i hi
    by_contra hn
    have h : i ≠ e.castSucc ∧ i ≠ e.succ := by simpa using hn
    simpa [pathWord,couplingWord,h.1,h.2] using (Finset.mem_filter.mp hi).2

/-- Concatenate a list of exact projective one-gate evolutions. -/
theorem compile_path_word_steps {n : ℕ} (z : List (Reg n)) (t : ℝ)
    (hz : ∀ x ∈ z, ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount = 1 ∧
      exp (t • x) = c • (C.eval : Reg n)) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit n, C.gateCount = z.length ∧
      (z.map fun x => exp (t • x)).prod = c • (C.eval : Reg n) := by
  induction z with
  | nil =>
    exact ⟨1,norm_one,TwoQubitCircuit.one n,rfl,by simp [TwoQubitCircuit.one_eval]⟩
  | cons x z ih =>
    obtain ⟨a,ha,C,hC,he⟩ := hz x List.mem_cons_self
    obtain ⟨b,hb,D,hD,hf⟩ := ih (fun y hy => hz y (List.mem_cons_of_mem _ hy))
    refine ⟨a*b,by rw [norm_mul,ha,hb,mul_one],C.mul D,by simp [TwoQubitCircuit.mul_gateCount,hD,hC],?_⟩
    simp only [List.map_cons,List.prod_cons,he,hf,TwoQubitCircuit.mul_eval]
    change (a • (C.eval : Reg n))*(b • (D.eval : Reg n)) = (a*b) • ((C.eval : Reg n)*(D.eval : Reg n))
    rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul]

/-- One skew-adjoint generator per path label, with exact total norm and
a one-gate implementation at every real time. -/
theorem exists_path_gate_generators {n : ℕ} (u : PathShell n) :
    ∃ Z : List (Reg (n+2)), Z.length = Fintype.card (PathLabel n) ∧
      Z.sum = (-Complex.I) • pathHamiltonian u ∧
      (Z.map norm).sum = ∑ l : PathLabel n, |u l| ∧
      (∀ x ∈ Z, x ∈ skewAdjoint (Reg (n+2))) ∧
      ∀ (h : ℝ) x, x ∈ Z → ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
        C.gateCount = 1 ∧ exp (h • x) = c • (C.eval : Reg (n+2)) := by
  classical
  let B := finitePauliSelfAdjointBasis (Fin (n+2))
  let H (l : PathLabel n) := u l • B (pathWord l)
  let X (l : PathLabel n) := twoLocalSkewGenerator (H l) (pathGateLabel l)
  let e := (Fintype.equivFin (PathLabel n)).symm
  let Z := List.ofFn (fun i => X (e i))
  have hc l : realPauliCoefficient (H l) (pathGateLabel l).val = u l := by
    change B.repr (u l • B (pathWord l)) (pathWord l) = u l
    simp
  have hsum : Z.sum = (-Complex.I) • pathHamiltonian u := by
    change (List.ofFn (fun i => X (e i))).sum = _
    rw [List.sum_ofFn,Equiv.sum_comp e X,pathHamiltonian_eq_sum,Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro l _
    change (-Complex.I) • ((realPauliCoefficient (H l) (pathGateLabel l).val : ℂ) • _) = _
    rw [hc]
    rfl
  have hmass : (Z.map norm).sum = ∑ l : PathLabel n, |u l| := by
    simp only [Z,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
    rw [Equiv.sum_comp e (fun l => ‖X l‖)]
    exact Finset.sum_congr rfl fun l _ => (twoLocalSkewGenerator_norm _ _).trans (congrArg abs (hc l))
  have hmem (x) (hx : x ∈ Z) : ∃ l, x = X l := by
    rw [List.mem_ofFn] at hx
    obtain ⟨i,rfl⟩ := hx
    exact ⟨_,rfl⟩
  have hz x (hx : x ∈ Z) : x ∈ skewAdjoint (Reg (n+2)) := by
    obtain ⟨l,rfl⟩ := hmem x hx
    exact twoLocalSkewGenerator_mem_skewAdjoint _ _
  have hs (h : ℝ) x (hx : x ∈ Z) : ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
      C.gateCount = 1 ∧ exp (h • x) = c • (C.eval : Reg (n+2)) := by
    obtain ⟨l,rfl⟩ := hmem x hx
    let P := pathGateLabel l
    have hn : 2 ≤ n+2 := by omega
    obtain ⟨c,hc,G,hG⟩ := exists_projective_twoQubitGate_eq_exp_twoLocalSkewGenerator hn (H l) P h
    refine ⟨c,hc,TwoQubitCircuit.singleOn _ _ (P.coveringPair_distinct hn) G,rfl,?_⟩
    rwa [TwoQubitCircuit.singleOn_eval]
  exact ⟨Z,by simp only [Z,List.length_ofFn],hsum,hmass,hz,hs⟩

#print axioms exists_path_gate_generators
end
end GaloisForLFunctions.HTGeometry
