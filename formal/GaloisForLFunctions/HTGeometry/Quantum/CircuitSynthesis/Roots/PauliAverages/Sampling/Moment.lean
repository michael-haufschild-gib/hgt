import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Sampling.WordCount
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Roots.PauliAverages.Sampling.Singleton
import GaloisForLFunctions.HTGeometry.CollectiveSpinOrderedInteractions
import GaloisForLFunctions.HTGeometry.FintypeSortedSpectrum
import GaloisForLFunctions.RHTower.SquarefreeShearKernelSpectrum
import GaloisForLFunctions.RHTower.InverseSquareChainCubicProjectiveFirstReturnLaw

/-! # Even moments of a sum of independent centered finite matrix samples -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
noncomputable section
variable {I J X : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
  [Fintype J] [DecidableEq J] [Nonempty J] [Fintype X] [Nonempty X]
private abbrev Mat (I : Type*) := Matrix I I ℂ

private theorem even_norm_trace {S : Mat I} (hs : S.IsHermitian) (k : ℕ) :
    ‖S‖^(2*k)≤(S^(2*k)).trace.re := by
  obtain ⟨i,_,hi⟩ := exists_max_image univ (fun j => |hs.eigenvalues j|) univ_nonempty
  have hn : ‖S‖≤|hs.eigenvalues i| := by
    rw [_root_.RHTower.l2_opNorm_eq_norm_eigenvalues hs]
    apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2
    intro j
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hi j (mem_univ j)
  rw [←sum_pow_eigenvalues_eq_trace_pow_re' hs]
  have he (j : I) : |hs.eigenvalues j|^(2*k)=hs.eigenvalues j^(2*k) := by
    rw [pow_mul,pow_mul,sq_abs]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn _).trans
    ((he i).le.trans (single_le_sum (f:=fun j => hs.eigenvalues j^(2*k))
      (fun j _ => he j ▸ pow_nonneg (abs_nonneg _) _) (mem_univ i)))

private theorem word_bound {R : ℝ} (hr : 0≤R) {n : ℕ} (A : Fin n → Mat I)
    (hA : ∀ i, ‖A i‖≤R) : ‖(List.ofFn A).prod‖≤R^n := by
  induction n with
  | zero => simp [List.ofFn_zero]
  | succ n ih =>
    rw [List.ofFn_succ,List.prod_cons,pow_succ']
    exact (norm_mul_le ..).trans (mul_le_mul (hA 0) (ih _ (fun i => hA i.succ))
      (norm_nonneg _) hr)

/-- Among all lists of independent samples, at least one has small
operator-norm sum. Singleton cancellation is before taking absolute values. -/
theorem exists_sample_moment (A : X → Mat I) (hA : ∑ x, A x=0) (hh : ∀ x, (A x).IsHermitian)
    {R : ℝ} (hr : 0≤R) (hb : ∀ x, ‖A x‖≤R) (k : ℕ) (hk : k≤Fintype.card J) :
    ∃ a : J → X, ‖∑ j, A (a j)‖^(2*k)≤
      Fintype.card I*(4*(Fintype.card J:ℝ)*k)^k*R^(2*k) := by
  classical
  let W (v : Fin (2*k) → J) (a : J → X) := (List.ofFn (fun j => A (a (v j)))).prod
  let F := univ.filter (fun v : Fin (2*k) → J => (univ.image v).card≤k)
  let N : ℝ := Fintype.card (J → X)
  let B : ℝ := Fintype.card I*R^(2*k)
  have hword (v : Fin (2*k) → J) (a : J → X) : (W v a).trace.re≤B :=
    (Complex.re_le_norm _).trans ((_root_.RHTower.norm_trace_le_card_mul_l2OpNorm _).trans
      (mul_le_mul_of_nonneg_left (word_bound hr _ (fun j => hb (a (v j)))) (by positivity)))
  have hzero (v : Fin (2*k) → J) (hv : v∉F) : (∑ a : J → X, (W v a).trace.re)=0 := by
    obtain ⟨i,hi⟩ := singleton_of_large_image v (lt_of_not_ge (fun hl =>
      hv (mem_filter.mpr ⟨mem_univ _,hl⟩)))
    have h := singleton_word_zero A hA v i hi
    change ∑ a, W v a=0 at h
    simpa only [Matrix.trace_sum,Complex.re_sum,Matrix.trace_zero,Complex.zero_re] using
      congrArg (fun M : Mat I => M.trace.re) h
  have htrace (a : J → X) : ((∑ j, A (a j))^(2*k)).trace.re=∑ v, (W v a).trace.re := by
    have h := finiteCollectiveObservable_pow_ordered_words (fun j => A (a j)) (2*k)
    simpa only [finiteCollectiveObservable,Matrix.trace_sum,Complex.re_sum,W] using
      congrArg (fun M : Mat I => M.trace.re) h
  have hherm (a : J → X) : (∑ j, A (a j)).IsHermitian := by
    change (∑ j, A (a j)).conjTranspose=_
    rw [Matrix.conjTranspose_sum]
    exact sum_congr rfl fun j _ => hh (a j)
  have ht : (∑ a : J → X, ‖∑ j, A (a j)‖^(2*k))≤F.card*(N*B) := calc
    _ ≤ ∑ a : J → X, ((∑ j, A (a j))^(2*k)).trace.re :=
      sum_le_sum fun a _ => even_norm_trace (hherm a) k
    _ = ∑ v ∈ F, ∑ a : J → X, (W v a).trace.re := by
      simp_rw [htrace]
      rw [Finset.sum_comm]
      exact (sum_subset (subset_univ F) fun v _ h => hzero v h).symm
    _ ≤ ∑ _v ∈ F, ∑ _a : J → X, B := sum_le_sum fun v _ => sum_le_sum fun a _ => hword v a
    _ = _ := by simp [N,nsmul_eq_mul]
  have hf : (F.card:ℝ)≤(4*(Fintype.card J:ℝ)*k)^k := by
    exact_mod_cast (small_image_count (J:=J) k hk)
  by_contra! h
  have hl := sum_lt_sum_of_nonempty (univ_nonempty (α:=J → X)) (fun a _ => h a)
  rw [sum_const,card_univ,nsmul_eq_mul] at hl
  have hp : 0≤N*B := mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hr _))
  have hu := ht.trans (mul_le_mul_of_nonneg_right hf hp)
  dsimp only [N,B] at hu
  linarith only [hu,hl]

#print axioms exists_sample_moment
end
end GaloisForLFunctions.HTGeometry.CircuitSynthesis.PauliAverages.Sampling
