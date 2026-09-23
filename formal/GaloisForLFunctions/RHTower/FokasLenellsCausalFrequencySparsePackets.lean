import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyAlmostEuclidean
import GaloisForLFunctions.RHTower.FokasLenellsCausalFrequencyBessel
import Mathlib.Analysis.SpecificLimits.Basic
open Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section
namespace RHTower.FokasLenells
set_option backward.isDefEq.respectTransparency false

private theorem weak_sequence_weighted_sparse_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℕ → H)
    (hw : ∀ y, Tendsto (fun n => inner ℂ y (v n)) atTop (𝓝 0))
    (ε : ℕ → ℕ → ℝ) (hε : ∀ i j, 0 < ε i j) :
    ∃ a : ℕ → ℕ, StrictMono a ∧
      ∀ i j, i < j → ‖inner ℂ (v (a i)) (v (a j))‖ < ε (a i) j := by
  classical
  have hthreshold (j m : ℕ) : ∃ M : ℕ, ∀ n ≥ M,
      ∀ i ∈ Finset.range (m + 1), ‖inner ℂ (v i) (v n)‖ < ε i j := by
    have he : ∀ᶠ n in atTop, ∀ i ∈ Finset.range (m + 1),
        ‖inner ℂ (v i) (v n)‖ < ε i j := by
      apply (eventually_all_finset (Finset.range (m + 1))).2
      intro i _
      simpa only [dist_zero_right] using
        (Metric.tendsto_nhds.1 (hw (v i))) (ε i j) (hε i j)
    exact eventually_atTop.1 he
  choose M hM using hthreshold
  let a : ℕ → ℕ := Nat.rec 0 (fun j prev => max (prev + 1) (M (j + 1) prev))
  have ha (j : ℕ) : a (j + 1) = max (a j + 1) (M (j + 1) (a j)) := rfl
  have hmono : StrictMono a := by
    apply strictMono_nat_of_lt_succ
    intro j
    rw [ha]
    exact (Nat.lt_succ_self (a j)).trans_le (le_max_left _ _)
  refine ⟨a, hmono, ?_⟩
  intro i j hij
  cases j with
  | zero => omega
  | succ j =>
    have hin : a i ∈ Finset.range (a j + 1) := by
      apply Finset.mem_range.2
      have hle : a i ≤ a j := hmono.monotone (by omega)
      omega
    apply hM (j + 1) (a j) (a (j + 1)) _ (a i) hin
    rw [ha]
    exact le_max_right _ _


private theorem geometric_weights_sum :
    HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
  simpa [pow_succ'] using hasSum_geometric_two.mul_left (1 / 2 : ℝ)

private theorem weak_sequence_geometric_subsequence
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℕ → H)
    (hw : ∀ y, Tendsto (fun n => inner ℂ y (v n)) atTop (𝓝 0))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ a : ℕ → ℕ, StrictMono a ∧ ∀ i j, i ≠ j →
      ‖inner ℂ (v (a i)) (v (a j))‖ ≤
        δ * (1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ (j + 1) := by
  obtain ⟨a, ha, hp⟩ := weak_sequence_weighted_sparse_subsequence v hw
    (fun i j => δ * (1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ (j + 1))
    (by intros; positivity)
  have hnat (i : ℕ) : i ≤ a i := by
    induction i with
    | zero => exact Nat.zero_le _
    | succ i ih => exact Nat.succ_le_of_lt (ih.trans_lt (ha (Nat.lt_succ_self i)))
  have hforward (i j : ℕ) (hij : i < j) :
      ‖inner ℂ (v (a i)) (v (a j))‖ ≤
        δ * (1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ (j + 1) := by
    apply (hp i j hij).le.trans
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_left _ hδ.le
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (Nat.add_le_add_right (hnat i) 1)
  refine ⟨a, ha, ?_⟩
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact hforward i j h
  · rw [RHTower.Sieve.norm_inner_symm]
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hforward j i h

private theorem geometric_unit_gram_row
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : ℕ → H) (hv : ∀ i, ‖v i‖ = 1)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (hp : ∀ i j, i ≠ j → ‖inner ℂ (v i) (v j)‖ ≤
      δ * (1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ (j + 1))
    (s : Finset ℕ) (i : ℕ) :
    ∑ j ∈ s, ‖inner ℂ (v i) (v j)‖ ≤ 1 + δ := by
  classical
  have hw (j : ℕ) : 0 ≤ (1 / 2 : ℝ) ^ (j + 1) := by positivity
  have hwi : (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := by
    simpa using pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) ≤ 1) (Nat.zero_le (i + 1))
  have hs : ∑ j ∈ s, (1 / 2 : ℝ) ^ (j + 1) ≤ 1 := by
    simpa only [geometric_weights_sum.tsum_eq] using
      geometric_weights_sum.summable.sum_le_tsum s (fun j _ => hw j)
  have hdiag : ∑ j ∈ s, (if i = j then (1 : ℝ) else 0) ≤ 1 := by
    by_cases hi : i ∈ s <;> simp [hi]
  calc
    _ ≤ ∑ j ∈ s, ((if i = j then (1 : ℝ) else 0) +
        δ * (1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ (j + 1)) := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · subst j
        simpa [inner_self_eq_norm_sq_to_K, hv] using
          (le_add_of_nonneg_right (mul_nonneg (mul_nonneg hδ (hw i)) (hw i)) :
            (1 : ℝ) ≤ 1 + δ * (1 / 2 : ℝ) ^ (i + 1) * (1 / 2 : ℝ) ^ (i + 1))
      · simpa only [if_neg hij, zero_add] using hp i j hij
    _ = (∑ j ∈ s, if i = j then (1 : ℝ) else 0) +
        (δ * (1 / 2 : ℝ) ^ (i + 1)) * ∑ j ∈ s, (1 / 2 : ℝ) ^ (j + 1) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 1 + (δ * (1 / 2 : ℝ) ^ (i + 1)) * ∑ j ∈ s, (1 / 2 : ℝ) ^ (j + 1) :=
      add_le_add hdiag le_rfl
    _ ≤ 1 + δ * (1 / 2 : ℝ) ^ (i + 1) := by
      have h := mul_le_mul_of_nonneg_left hs (mul_nonneg hδ (hw i))
      simpa only [mul_one] using add_le_add (le_refl (1 : ℝ)) h
    _ ≤ 1 + δ := by
      have h := mul_le_mul_of_nonneg_left hwi hδ
      simpa only [mul_one] using add_le_add (le_refl (1 : ℝ)) h

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
private theorem unimodular_gram_norm (v w : H) (z t : ℂ)
    (hz : ‖z‖ = 1) (ht : ‖t‖ = 1) (n : ℕ) :
    ‖inner ℂ (z ^ n • v) (t ^ n • w)‖ = ‖inner ℂ v w‖ := by
  simp [inner_smul_left, inner_smul_right, norm_pow, hz, ht]
end
section CoordinateEstimate
variable {I E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]

private theorem coordinate_gram_packet_bound
    (q : ℕ → E →L[ℂ] H) (v : I → E) (h : I → H) (z : I → ℂ)
    (hq : ∀ n i, q n (v i) = z i ^ n • h i)
    (hz : ∀ i, ‖z i‖ = 1)
    (hnorm : ∀ u C, 0 ≤ C → (∀ n, ‖q n u‖ ≤ C) → ‖u‖ ≤ C)
    (s : Finset I) (Δ : ℝ) (hΔ : 0 ≤ Δ)
    (hrow : ∀ i ∈ s, ∑ j ∈ s, ‖inner ℂ (h i) (h j)‖ ≤ Δ)
    (c : I → ℂ) :
    ‖∑ i ∈ s, c i • v i‖ ^ (2 : ℕ) ≤ Δ * ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) := by
  have hG : 0 ≤ Δ * ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) :=
    mul_nonneg hΔ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hcoord : ∀ n, ‖q n (∑ i ∈ s, c i • v i)‖ ^ (2 : ℕ) ≤
      Δ * ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) := by
    intro n
    simp only [map_sum, map_smul]
    apply RHTower.Sieve.norm_sum_smul_sq_le_of_schur
    intro i hi
    calc
      _ = ∑ j ∈ s, ‖inner ℂ (h i) (h j)‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hq, hq, unimodular_gram_norm _ _ _ _ (hz i) (hz j)]
      _ ≤ Δ := hrow i hi
  have hb := hnorm (∑ i ∈ s, c i • v i)
    (Real.sqrt (Δ * ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ))) (Real.sqrt_nonneg _)
    (fun n => Real.le_sqrt_of_sq_le (hcoord n))
  nlinarith [Real.sq_sqrt hG, norm_nonneg (∑ i ∈ s, c i • v i)]
end CoordinateEstimate

private theorem bounded_chain_norm_from_coordinates (u : causalBoundedChain) (C : ℝ)
    (hC : 0 ≤ C) (hc : ∀ n, ‖causalBoundedChainCoordinate n u‖ ≤ C) : ‖u‖ ≤ C := by
  change ‖u.val‖ ≤ C
  exact lp.norm_le_of_forall_le hC hc

private theorem actual_sparse_frequencies (b : ℝ) (k : ℕ) :
    ∃ ω : ℕ → ℝ, StrictMono ω ∧ ∀ s : Finset ℕ, ∀ i : ℕ,
      ∑ j ∈ s, ‖inner ℂ (causalUnitBoundaryEigenvector b (ω i)).val
        (causalUnitBoundaryEigenvector b (ω j)).val‖ ≤ 1 + 1 / ((k : ℝ) + 1) := by
  let v : ℕ → hardyL2ᗮ := fun n =>
    (causalUnitBoundaryEigenvector b (Real.exp (b + (n : ℝ)))).val
  have hw (y : hardyL2ᗮ) : Tendsto (fun n => inner ℂ y (v n)) atTop (𝓝 0) := by
    have hn : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    have he (n : ℕ) : v n = (causalUnitBoundaryEigenvector (-(n : ℝ)) 1).val := by
      simpa only [v, sub_neg_eq_add, mul_one] using
        congrArg Subtype.val (causalUnitBoundaryEigenvector_rescale (-(n : ℝ)) b 1)
    simpa only [Function.comp_def, he] using
      (causalUnitBoundaryEigenvector_weak_tendsto_pos y).comp hn
  obtain ⟨a, ha, hp⟩ := weak_sequence_geometric_subsequence v hw
    (1 / ((k : ℝ) + 1)) (by positivity)
  refine ⟨fun n => Real.exp (b + (a n : ℝ)), ?_, ?_⟩
  · intro i j hij
    apply Real.exp_lt_exp.2
    have hcast : (a i : ℝ) < a j := by exact_mod_cast ha hij
    linarith
  · intro s i
    exact geometric_unit_gram_row (fun n => v (a n))
      (fun n => norm_causalUnitBoundaryEigenvector b _) _ (by positivity) hp s i

/-- A selected strictly increasing sequence of actual frequencies. The precision
`k` controls every finite Gram row, independently of packet size. -/
def causalFrequencySparseFrequency (b : ℝ) (k : ℕ) : ℕ → ℝ :=
  (actual_sparse_frequencies b k).choose

/-- Sparse actual frequencies are distinct and retain their natural ordering. -/
theorem causalFrequencySparseFrequency_strictMono (b : ℝ) (k : ℕ) :
    StrictMono (causalFrequencySparseFrequency b k) :=
  (actual_sparse_frequencies b k).choose_spec.1

/-- Every finite Gram row of the selected boundary data has the same bound. -/
theorem causalFrequencySparseFrequency_gram_row_le (b : ℝ) (k : ℕ)
    (s : Finset ℕ) (i : ℕ) :
    ∑ j ∈ s,
      ‖inner ℂ (causalUnitBoundaryEigenvector b (causalFrequencySparseFrequency b k i)).val
        (causalUnitBoundaryEigenvector b (causalFrequencySparseFrequency b k j)).val‖ ≤
      1 + 1 / ((k : ℝ) + 1) :=
  (actual_sparse_frequencies b k).choose_spec.2 s i

private theorem subtype_packet_bound
    {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (D : Submodule ℂ E) (v : I → D) (w : I → E)
    (hv : ∀ i, (v i).val = w i) (s : Finset I) (c : I → ℂ) (C : ℝ)
    (h : ‖∑ i ∈ s, c i • w i‖ ^ (2 : ℕ) ≤ C) : ‖∑ i ∈ s, c i • v i‖ ^ (2 : ℕ) ≤ C := by
  have he : (∑ i ∈ s, c i • v i).val = ∑ i ∈ s, c i • w i := by
    change D.subtype (∑ i ∈ s, c i • v i) = _
    simp only [map_sum, map_smul]
    exact Finset.sum_congr rfl (fun i _ => congrArg (fun x => c i • x) (hv i))
  change ‖(∑ i ∈ s, c i • v i).val‖ ^ (2 : ℕ) ≤ C
  rw [he]
  exact h

/-- All finite packets from one infinite sparse family have a uniform quadratic
upper bound. The family is fixed before choosing the support or amplitudes. -/
theorem causalFrequencySparseFrequency_packet_norm_sq_le (b : ℝ) (k : ℕ)
    (s : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ i ∈ s, c i • causalFrequencyMode b (causalFrequencySparseFrequency b k i)‖ ^ (2 : ℕ) ≤
      (1 + 1 / ((k : ℝ) + 1)) * ∑ i ∈ s, ‖c i‖ ^ (2 : ℕ) := by
  apply subtype_packet_bound (causalFrequencySpace b)
    (fun i => causalFrequencyMode b (causalFrequencySparseFrequency b k i))
    (fun i => causalBoundedUnitEigenchain b (causalFrequencySparseFrequency b k i))
    (fun _ => rfl) s c
  apply coordinate_gram_packet_bound causalBoundedChainCoordinate
    (fun i => causalBoundedUnitEigenchain b (causalFrequencySparseFrequency b k i))
    (fun i => (causalUnitBoundaryEigenvector b (causalFrequencySparseFrequency b k i)).val)
    (fun i => (causalUnitBoundaryRate b (causalFrequencySparseFrequency b k i)).val)
    (fun _ _ => rfl) (fun i => norm_causalUnitBoundaryRate b _)
    bounded_chain_norm_from_coordinates s (1 + 1 / ((k : ℝ) + 1)) (by positivity)
  exact fun i hi => causalFrequencySparseFrequency_gram_row_le b k s i

end RHTower.FokasLenells
