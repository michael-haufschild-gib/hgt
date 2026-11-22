import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.LocalEcho.SparseMass
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.LocalErrors.BlockCommutators

/-! # Commutators of two Hamiltonians differing only near selected bonds -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
noncomputable section
open LocalPatches
variable {n : ℕ}
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

def nearBonds (Q : Finset (Fin (n+1))) := Q.biUnion fun e => ball (zz e)

theorem nearBonds_card (Q : Finset (Fin (n+1))) : (nearBonds Q).card ≤ 43*Q.card := calc
  _ ≤ ∑ e∈Q, (ball (zz e)).card := Finset.card_biUnion_le
  _ ≤ ∑ _e∈Q, 43 := Finset.sum_le_sum fun e _ => ball_card _
  _ = _ := by simp [mul_comm]

def weighted (u : PathShell n) (f : PathLabel n → ℝ) := ∑ l, f l • pathTermGenerator u l

private theorem weighted_sub (u : PathShell n) (f g : PathLabel n → ℝ) (Q : Finset (Fin (n+1)))
    (hfg : ∀ l ∉ nearBonds Q, f l=g l) :
    weighted u f-weighted u g=∑ i∈nearBonds Q,(f i-g i) • pathTermGenerator u i := by
  unfold weighted
  rw [←Finset.sum_sub_distrib]
  simp_rw [←sub_smul]
  exact (Finset.sum_subset (Finset.subset_univ _) fun l _ hl => by rw [hfg l hl,sub_self,zero_smul]).symm

private theorem pair_commute (u : PathShell n) (f g : ℝ) {i j : PathLabel n} (h : j ∉ ball i) :
    Commute (f • pathTermGenerator u i) (g • pathTermGenerator u j) := by
  have hd : Disjoint (labelSupport (pathWord i)) (labelSupport (pathWord j)) := by
    by_contra hn
    exact h (Finset.mem_insert_of_mem (mem_pathOverlaps.mpr hn))
  have hp := commute_finitePauliMatrix_of_disjoint hd
  have hleft := ((hp.smul_left (u i:ℂ)).smul_left (-Complex.I)).smul_left f
  exact ((hleft.smul_right (u j:ℂ)).smul_right (-Complex.I)).smul_right g

private theorem row_le (u : PathShell n) (i : PathLabel n) (a : ℝ) (ha : |a|≤2)
    (g : PathLabel n→ℝ) (hg : ∀ j, |g j|≤1) (M : ℝ) (hM : 0≤M)
    (hc : ∀ j∈ball i, (u j)^2≤M^2) :
    (∑ j, ‖(a • pathTermGenerator u i)*(g j • pathTermGenerator u j)-
      (g j • pathTermGenerator u j)*(a • pathTermGenerator u i)‖) ≤ 43*(4*M^2) := by
  let X := a • pathTermGenerator u i
  let Y (j) := g j • pathTermGenerator u j
  have hX : ‖X‖ ≤ 2*M := by
    rw [show ‖X‖=|a| *|u i| by rw [norm_smul,(pathTerm_properties u i).1,Real.norm_eq_abs]]
    exact mul_le_mul ha (le_of_sq_le_sq (by rw [sq_abs]; exact hc i (Finset.mem_insert_self ..)) hM) (abs_nonneg _) zero_le_two
  have hY (j) (hj : j∈ball i) : ‖Y j‖ ≤ M := by
    calc _ = |g j| *|u j| := by rw [Y,norm_smul,(pathTerm_properties u j).1,Real.norm_eq_abs]
         _ ≤ 1*M := mul_le_mul (hg j) (le_of_sq_le_sq (by rw [sq_abs]; exact hc j hj) hM) (abs_nonneg _) zero_le_one
         _ = M := one_mul _
  have hpair (j) (hj : j∈ball i) : ‖X*Y j-Y j*X‖ ≤ 4*M^2 := by
    calc _ ≤ ‖X‖*‖Y j‖+‖Y j‖*‖X‖ := (norm_sub_le ..).trans (add_le_add (norm_mul_le ..) (norm_mul_le ..))
         _ ≤ (2*M)*M+M*(2*M) := add_le_add (mul_le_mul hX (hY j hj) (norm_nonneg _) (by positivity))
           (mul_le_mul (hY j hj) hX (norm_nonneg _) hM)
         _ = _ := by ring
  change (∑ j, ‖X*Y j-Y j*X‖) ≤ _
  rw [←Finset.sum_subset (Finset.subset_univ (ball i)) (fun j _ hj => by
    rw [(show Commute X (Y j) from pair_commute u a (g j) hj).eq,sub_self,norm_zero])]
  apply (Finset.sum_le_sum hpair).trans
  rw [Finset.sum_const,nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast ball_card i) (by positivity)

/-- The common background cancels from the difference. Each remaining
row of the commutator has bounded degree and uniformly bounded entries. -/
theorem sparse_bracket (u : PathShell n) (Q : Finset (Fin (n+1))) (M : ℝ) (hM : 0≤M)
    (hm : ∀ e∈Q, localMass u e ≤ M^2) (f g : PathLabel n→ℝ)
    (hf : ∀ l, |f l|≤1) (hg : ∀ l, |g l|≤1) (hfg : ∀ l ∉ nearBonds Q, f l=g l) :
    ‖weighted u f*weighted u g-weighted u g*weighted u f‖ ≤ 4*43^2*Q.card*M^2 := by
  classical
  let X (i) := (f i-g i) • pathTermGenerator u i
  let Y (i) := g i • pathTermGenerator u i
  have he : weighted u f*weighted u g-weighted u g*weighted u f=
      (∑ i∈nearBonds Q,X i)*(∑ j,Y j)-(∑ j,Y j)*(∑ i∈nearBonds Q,X i) := by
    rw [←weighted_sub u f g Q hfg]; change _=(weighted u f-weighted u g)*weighted u g-weighted u g*(weighted u f-weighted u g)
    simp only [sub_mul,mul_sub]; abel
  have hr (i) (hi : i ∈ nearBonds Q) : (∑ j, ‖X i*Y j-Y j*X i‖) ≤ 43*(4*M^2) := by
    obtain ⟨e,he,hi⟩ := Finset.mem_biUnion.mp hi
    apply row_le u i _ ((abs_sub ..).trans ((add_le_add (hf i) (hg i)).trans_eq (by norm_num))) g hg M hM
    exact fun j hj => (coord_le_localMass u e hi hj).trans (hm e he)
  rw [he]
  apply (LocalErrors.norm_commutator_sums _ _ X Y).trans ((Finset.sum_le_sum hr).trans ?_)
  rw [Finset.sum_const,nsmul_eq_mul]
  have hcard : ((nearBonds Q).card:ℝ) ≤ 43*(Q.card:ℝ) := by exact_mod_cast nearBonds_card Q
  exact (mul_le_mul_of_nonneg_right hcard (by positivity : 0 ≤ 43*(4*M^2))).trans_eq (by ring)

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.LocalEcho
