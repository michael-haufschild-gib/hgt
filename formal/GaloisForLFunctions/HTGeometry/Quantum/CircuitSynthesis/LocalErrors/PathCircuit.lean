import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.Word
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PauliTerm

/-! # Nearest-neighbour Pauli simulation controlled by squared interaction mass -/
open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N → Bool) (Fin N → Bool) ℂ
local instance pathOverlapCStarAlgebra (N : ℕ) : CStarAlgebra (Reg N) where

open LocalPatches

private theorem pathTerm_commutator_mass {n : ℕ} (u : PathShell n) :
    let X := pathTermGenerator u
    (∑ l : PathLabel n, ∑ q : PathLabel n, ‖X l*X q-X q*X l‖) ≤ 84*‖u‖^2 := by
  classical
  let X := pathTermGenerator u
  change (∑ l : PathLabel n, ∑ q : PathLabel n, ‖X l*X q-X q*X l‖) ≤ _
  apply le_trans _ (path_sum_overlap_squares_le u)
  apply Finset.sum_le_sum
  intro l _
  have hzero (q : PathLabel n) (hq : q ∉ pathOverlaps l) : ‖X l*X q-X q*X l‖ = 0 := by
    have hd : Disjoint (labelSupport (pathWord l)) (labelSupport (pathWord q)) := by
      by_contra hn
      exact hq (mem_pathOverlaps.mpr hn)
    have hh := commute_finitePauliMatrix_of_disjoint hd
    have hh' : Commute (X l) (X q) :=
      (((hh.smul_left (u l : ℂ)).smul_left (-Complex.I)).smul_right (u q : ℂ)).smul_right (-Complex.I)
    rw [hh'.eq,sub_self,norm_zero]
  rw [← Finset.sum_subset (Finset.subset_univ (pathOverlaps l)) (fun q _ hq => hzero q hq)]
  apply Finset.sum_le_sum
  intro q _
  have hl := (pathTerm_properties u l).1
  have hq := (pathTerm_properties u q).1
  calc
    _ ≤ ‖X l‖*‖X q‖+‖X q‖*‖X l‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ _ := by
      change ‖pathTermGenerator u l‖*_+‖pathTermGenerator u q‖*_ ≤ _
      dsimp only [X]
      rw [hl,hq]
      nlinarith only [sq_nonneg (|u l|-|u q|),sq_abs (u l),sq_abs (u q)]

/-- Each sweep uses one physical gate per path label. The squared coefficient
norm bounds the overlap error uniformly in the chain length. -/
theorem exists_path_circuit_squared_mass_error {n : ℕ} (u : PathShell n)
    (t : ℝ) (ht : 0 ≤ t) (r : ℕ) (hr : 0 < r) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∃ C : TwoQubitCircuit (n+2),
      C.gateCount = r*Fintype.card (PathLabel n) ∧
      ‖unitaryEvolution (pathHamiltonian u) t-c • (C.eval : Reg (n+2))‖ ≤
        t^2/(r:ℝ)*(84*‖u‖^2) := by
  classical
  let X := pathTermGenerator u
  let e := (Fintype.equivFin (PathLabel n)).symm
  let Z := List.ofFn (fun i => X (e i))
  have hmem (x) (hx : x ∈ Z) : ∃ l, x = X l := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ⟨_,rfl⟩
  have hz x (hx : x ∈ Z) : x ∈ skewAdjoint (Reg (n+2)) := by
    obtain ⟨l,rfl⟩ := hmem x hx
    exact (pathTerm_properties u l).2.1
  have hs : Z.sum = (-Complex.I) • pathHamiltonian u := by
    change (List.ofFn (fun i => X (e i))).sum = _
    rw [List.sum_ofFn,Equiv.sum_comp e X,pathHamiltonian_eq_sum,Finset.smul_sum]
    rfl
  have hmap (f : Reg (n+2) → ℝ) : (Z.map f).sum = ∑ l : PathLabel n, f (X l) := by
    simp only [Z,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
    exact Equiv.sum_comp e (fun l => f (X l))
  let h := t/(r:ℝ)
  obtain ⟨c,hc,C,hC,hprod⟩ := compile_path_word_steps Z h (by
    intro x hx
    obtain ⟨l,rfl⟩ := hmem x hx
    exact (pathTerm_properties u l).2.2 h)
  refine ⟨c^r,by simp [norm_pow,hc],C.pow r,by rw [TwoQubitCircuit.pow_gateCount,hC]; simp only [Z,List.length_ofFn],?_⟩
  have herr := lie_word_repeated_commutator_error Z hz t ht r hr
  change ‖(Z.map fun x => exp (h • x)).prod^r-exp (t • Z.sum)‖ ≤ _ at herr
  rw [hprod,smul_pow,hs] at herr
  simp_rw [hmap] at herr
  rw [TwoQubitCircuit.pow_eval_coe,norm_sub_rev]
  exact herr.trans (mul_le_mul_of_nonneg_left (pathTerm_commutator_mass u) (by positivity))

#print axioms exists_path_circuit_squared_mass_error
end
end GaloisForLFunctions.HTGeometry

