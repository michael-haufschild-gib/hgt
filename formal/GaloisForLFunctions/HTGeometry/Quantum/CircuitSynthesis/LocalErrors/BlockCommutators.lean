import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalPatches.PauliTerm

/-! # Regrouping local interactions preserves the squared-mass commutator bound -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.LocalErrors
noncomputable section
open LocalPatches

/-- The norm of a commutator between two sums is bounded by their total
pairwise commutator mass. The two lists of labels may differ. -/
theorem norm_commutator_sums {ι κ A : Type*} [NormedRing A] (s : Finset ι) (t : Finset κ)
    (X : ι→A) (Y : κ→A) :
    ‖(∑ i ∈ s,X i)*(∑ j ∈ t,Y j)-(∑ j ∈ t,Y j)*(∑ i ∈ s,X i)‖ ≤
      ∑ i ∈ s, ∑ j ∈ t, ‖X i*Y j-Y j*X i‖ := by
  have h : (∑ i ∈ s,X i)*(∑ j ∈ t,Y j)-(∑ j ∈ t,Y j)*(∑ i ∈ s,X i)=
      ∑ i ∈ s, ∑ j ∈ t, (X i*Y j-Y j*X i) := by
    simp only [Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul]
  rw [h]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)

private theorem partition_sum {ι κ A : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommMonoid A] (b : ι→κ) (w : ι→A) :
    (∑ e : κ, ∑ i ∈ Finset.univ.filter (fun i => b i=e), w i)=∑ i, w i := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Assign every term to one block. Internal cancellations can only
decrease the sum of the norms of block commutators. -/
theorem block_commutator_mass {ι κ A : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [NormedRing A] (b : ι→κ) (X : ι→A) :
    let Z := fun e => ∑ i ∈ Finset.univ.filter (fun i => b i=e), X i
    (∑ e : κ, ∑ f : κ, ‖Z e*Z f-Z f*Z e‖) ≤ ∑ i : ι, ∑ j : ι, ‖X i*X j-X j*X i‖ := by
  intro Z
  let F (e : κ) := Finset.univ.filter fun i => b i=e
  let w (i j : ι) := ‖X i*X j-X j*X i‖
  calc _ ≤ ∑ e : κ, ∑ f : κ, ∑ i ∈ F e, ∑ j ∈ F f, w i j := by
              exact Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun f _ =>
                norm_commutator_sums (F e) (F f) X X
       _ = ∑ e : κ, ∑ i ∈ F e, ∑ j : ι, w i j := by
              apply Finset.sum_congr rfl
              intro e _
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun i _ => partition_sum b (w i)
       _ = _ := partition_sum b _

/-- Overlapping generators contribute at most the sum of their two
squared coefficients, and disjoint generators commute. -/
theorem path_commutator_mass {n : ℕ} (u : PathShell n) :
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
  calc
    _ ≤ ‖X l‖*‖X q‖+‖X q‖*‖X l‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ _ := by
      dsimp only [X]
      rw [(pathTerm_properties u l).1,(pathTerm_properties u q).1]
      nlinarith only [sq_nonneg (|u l|-|u q|),sq_abs (u l),sq_abs (u q)]

#print axioms block_commutator_mass
end
end GaloisForLFunctions.HTGeometry.LocalErrors
