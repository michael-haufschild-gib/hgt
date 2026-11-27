import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.ProductFormulas.BondMass
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # One physical gate per retained edge with arbitrary onsite assignments -/

open Matrix NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
open BondCoordinates LocalPatches
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ
local instance (N : ℕ) : CStarAlgebra (Reg N) where
variable {n m : ℕ}

private theorem supported_word_lift (l : PathLabel n) (e : Fin (n+1))
    (hs : ∀ i : Fin (n+2), i≠e.castSucc → i≠e.succ → pathWord l i=none) :
    finitePauliMatrix (pathWord l)=twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e)
      (boolTwoQubitPauli (pathWord l e.castSucc) (pathWord l e.succ)) := by
  let p := pathWord l
  let v := splitTwoQubitConfig e.castSucc e.succ (endpoints_ne e)
  have hrest : twoQubitRestPauliLabel p e.castSucc e.succ=(fun _ => none) := by
    funext j
    exact hs j.val j.2.1 j.2.2
  apply (Matrix.reindexAlgEquiv ℂ ℂ v).injective
  change Matrix.reindex v v (finitePauliMatrix p)=Matrix.reindex v v (twoQubitLiftMatrix _ _ _ _)
  rw [show Matrix.reindex v v (finitePauliMatrix p)=_ from
    reindex_splitTwoQubitConfig_finitePauliMatrix _ _ (endpoints_ne e) p,hrest,finitePauliMatrix_const_none]
  simp [twoQubitLiftMatrix,v,p]

private theorem assigned_blocks (u : PathShell n) (owner : PathLabel n→Fin m)
    (edge : Fin m→Fin (n+1)) (hs : ∀ l, u l≠0 → ∀ i : Fin (n+2),
      i≠(edge (owner l)).castSucc → i≠(edge (owner l)).succ → pathWord l i=none) :
    ∃ B : Fin m→selfAdjoint LocalMatrix, ∀ j, let e := edge j
      twoQubitLiftMatrix e.castSucc e.succ (endpoints_ne e) (B j).val =
        ∑ l : PathLabel n, if owner l=j then ((u l:ℝ):ℂ) • finitePauliMatrix (pathWord l) else 0 := by
  classical
  let term (j : Fin m) (l : PathLabel n) : LocalMatrix :=
    ((u l:ℝ):ℂ) • boolTwoQubitPauli (pathWord l (edge j).castSucc) (pathWord l (edge j).succ)
  let B (j : Fin m) := ∑ l : PathLabel n, if owner l=j then term j l else 0
  have herm (j : Fin m) : (B j).IsHermitian := by
    change (∑ l : PathLabel n, if owner l=j then term j l else 0)ᴴ=_
    rw [Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro l _
    split
    · simp only [term,Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,
        (boolTwoQubitPauli_isHermitian ..).eq]
    · exact Matrix.conjTranspose_zero
  refine ⟨fun j => ⟨B j,(herm j).isSelfAdjoint⟩,?_⟩
  let L (j : Fin m) := twoQubitLiftMatrixCLM (edge j).castSucc (edge j).succ (endpoints_ne _)
  intro j
  change L j (B j)=_
  dsimp only [B]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  by_cases hj : owner l=j
  · subst j
    simp only [if_true,term,map_smul]
    by_cases hl : u l=0
    · simp [hl]
    · exact congrArg (((u l:ℝ):ℂ) • ·) (supported_word_lift l _ (hs l hl)).symm
  · simp only [if_neg hj,map_zero]

/-- Nonzero Pauli terms can be assigned to any covering physical bonds.
The first-order error is independent of the assignment. The gate count
is exactly the number of chosen bonds, including if they overlap. -/
theorem assigned_sweep (u : PathShell n) (owner : PathLabel n→Fin m) (edge : Fin m→Fin (n+1))
    (hs : ∀ l, u l≠0 → ∀ i : Fin (n+2),
      i≠(edge (owner l)).castSucc → i≠(edge (owner l)).succ → pathWord l i=none)
    (t : ℝ) (ht : 0≤t) :
    HasProjectiveCircuitApproximation (n+2) (t^2*(84*‖u‖^2)) m
      (unitaryEvolution (pathHamiltonian u) t) := by
  classical
  obtain ⟨B,hB⟩ := assigned_blocks u owner edge hs
  let F (j : Fin m) := twoQubitLiftMatrix (edge j).castSucc (edge j).succ (endpoints_ne _) (B j).val
  let X (j : Fin m) := (-Complex.I) • F j
  let Z := List.ofFn X
  have hblock (j : Fin m) : X j=∑ l ∈ Finset.univ.filter (fun l => owner l=j), pathTermGenerator u l := by
    dsimp only [X,F]
    rw [hB,← Finset.sum_filter,Finset.smul_sum]
    rfl
  have hsk (x) (hx : x∈Z) : x∈skewAdjoint (Reg (n+2)) := by
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    rw [hblock]
    exact (skewAdjoint _).sum_mem fun l _ => (pathTerm_properties u l).2.1
  have hZ : Z.sum=(-Complex.I) • pathHamiltonian u := by
    change (List.ofFn X).sum=_
    rw [List.sum_ofFn,pathHamiltonian_eq_sum,Finset.smul_sum]
    simp only [hblock,Finset.sum_filter]
    rw [Finset.sum_comm]
    simp [pathTermGenerator]
  have hmass : (∑ i, ∑ j, ‖X i*X j-X j*X i‖)≤84*‖u‖^2 := by
    simp only [hblock]
    exact (LocalErrors.block_commutator_mass owner (pathTermGenerator u)).trans
      (LocalErrors.path_commutator_mass u)
  obtain ⟨z,hz,C,hC,hprod⟩ := compile_path_word_steps Z t (by
    intro x hx
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
    exact lifted_flow (edge j) (B j) t)
  refine ⟨z,hz,C,by simpa only [Z,List.length_ofFn] using hC.le,?_⟩
  have herr := lie_word_repeated_commutator_error Z hsk t ht 1 one_pos
  simp only [Nat.cast_one,div_one,pow_one] at herr
  change ‖(Z.map fun x => exp (t • x)).prod-exp (t • Z.sum)‖≤_ at herr
  rw [hprod,hZ] at herr
  simp only [Z,List.map_ofFn,Function.comp_apply,List.sum_ofFn] at herr
  rw [norm_sub_rev]
  exact herr.trans (mul_le_mul_of_nonneg_left hmass (sq_nonneg _))

#print axioms assigned_sweep
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
