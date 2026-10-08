import GaloisForLFunctions.RHTower.PrimeLogZetaAbelPole

/-!
# Abel damping preserves the upper logarithmic energy constant

The finite initial segment costs a term vanishing with the damping exponent.
The remaining logarithmic energy uses the existing positive Abel bound.
-/

open Filter Topology

noncomputable section
namespace RHTower.WeilSingularArithmetic

/-- A logarithmic energy limit supplies its exact upper Abel constant. -/
theorem exists_abel_energy_majorant {w : ℕ → ℝ} (hw0 : w 0 = 0)
    (hw : ∀ n, 0 ≤ w n) {V : ℝ} (hV0 : 0 ≤ V)
    (hV : Tendsto (fun N : ℕ => weightPartialSum w N / Real.log N) atTop (𝓝 V))
    {e : ℝ} (he : 0 < e) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ d : ℝ, 0 < d →
      Summable (fun n : ℕ => w n * (n : ℝ) ^ (-d)) ∧
      d * (∑' n : ℕ, w n * (n : ℝ) ^ (-d)) ≤ d * A + (V + e) * (1 + d) := by
  have hb := hV.eventually (gt_mem_nhds (show V < V + e by linarith))
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hb.and (eventually_ge_atTop (2 : ℕ)))
  let t : ℕ → ℝ := fun n => if M ≤ n then w n else 0
  let h : ℕ → ℝ := fun n => if n < M then w n else 0
  have ht0 : t 0 = 0 := by simp [t, hw0]
  have htn : ∀ n, 0 ≤ t n := fun n => by
    dsimp [t]; split_ifs
    · exact hw n
    · exact le_rfl
  have htw : ∀ n, t n ≤ w n := fun n => by
    dsimp [t]; split_ifs
    · exact le_rfl
    · exact hw n
  have htb : ∀ N, weightPartialSum t N ≤ (V + e) * (Real.log N + 1) := by
    intro N
    by_cases hMN : M ≤ N
    · have hN := hM N hMN
      have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
      have hbN : weightPartialSum w N ≤ (V + e) * Real.log N :=
        ((div_lt_iff₀ hl).mp hN.1).le
      have htN : weightPartialSum t N ≤ weightPartialSum w N :=
        Finset.sum_le_sum fun n _ => htw n
      nlinarith
    · have hz : weightPartialSum t N = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hnN := (Finset.mem_Icc.mp hn).2
        simp [t, show ¬ M ≤ n by omega]
      rw [hz]
      apply mul_nonneg (by linarith)
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · simp
      · have := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ N)
        linarith
  let A : ℝ := ∑ n ∈ Finset.range M, w n
  refine ⟨A, Finset.sum_nonneg (fun n _ => hw n), fun d hd => ?_⟩
  obtain ⟨hts, hte⟩ := summable_and_mul_tsum_weightedDirichlet_le ht0 htn
    (by linarith : 0 ≤ V + e) htb hd
  have hhs : Summable (fun n : ℕ => h n * (n : ℝ) ^ (-d)) := by
    apply summable_of_ne_finset_zero (s := Finset.range M)
    intro n hn
    simp [h, show ¬ n < M by simpa using hn]
  have heq (n : ℕ) : h n + t n = w n := by
    dsimp [h, t]
    by_cases hn : n < M
    · simp [hn, show ¬ M ≤ n by omega]
    · simp [hn, show M ≤ n by omega]
  have hsum : Summable (fun n : ℕ => w n * (n : ℝ) ^ (-d)) := by
    convert hhs.add hts using 1
    funext n
    simp only [← add_mul, heq]
  have hhead : (∑' n : ℕ, h n * (n : ℝ) ^ (-d)) ≤ A := by
    rw [tsum_eq_sum (s := Finset.range M) (fun n hn => by
      simp [h, show ¬ n < M by simpa using hn])]
    apply Finset.sum_le_sum
    intro n hn
    rw [show h n = w n by simp [h, Finset.mem_range.mp hn]]
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp [hw0]
    · exact mul_le_of_le_one_right (hw n) (Real.rpow_le_one_of_one_le_of_nonpos
        (by exact_mod_cast hn0) (by linarith))
  have hsplit : (∑' n : ℕ, w n * (n : ℝ) ^ (-d)) =
      (∑' n : ℕ, h n * (n : ℝ) ^ (-d)) + ∑' n : ℕ, t n * (n : ℝ) ^ (-d) := by
    rw [← hhs.tsum_add hts]
    apply tsum_congr
    intro n
    rw [← add_mul, heq]
  refine ⟨hsum, ?_⟩
  rw [hsplit, mul_add]
  exact add_le_add (mul_le_mul_of_nonneg_left hhead hd.le) hte

end RHTower.WeilSingularArithmetic
