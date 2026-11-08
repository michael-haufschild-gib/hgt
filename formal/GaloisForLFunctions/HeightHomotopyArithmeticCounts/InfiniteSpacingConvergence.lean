import GaloisForLFunctions.HeightHomotopyArithmeticCounts.WeightedSpacingConvergence

/-!
# Absolutely summable spacing errors on infinite probes

A positive conductor-weighted square norm controls the entire mixed error
series. Finite sets of pairs lie in square conductor windows; the finite
absolute estimate therefore passes to the infinite series with the same rate.
-/

noncomputable section
open Finset Filter Topology
namespace GaloisForLFunctions.HeightHomotopyArithmeticCounts
open ArithmeticEffectivityTheory ArithmeticIntersectionTheory

/-- Infinite probes of finite weighted square mass have absolutely summable spacing errors. -/
theorem spacingKernelError_infinite_absolute_rate (δ α : ℝ)
    (hα : 0 < α) (hα1 : α ≤ 1) (hgap : 2*α < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (x : ℕ → ℝ), 0 < ε → x 0=0 →
      Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2) →
      Summable (fun p : ℕ×ℕ => |x p.1*x p.2*spacingKernelError ε p.1 p.2|) ∧
      (∑' p : ℕ×ℕ, |x p.1*x p.2*spacingKernelError ε p.1 p.2|) ≤ 
        C*ε^α*(∑' n : ℕ, (n:ℝ)^δ*(x n)^2) := by
  classical
  obtain ⟨C, hC, hbound⟩ := spacingKernelError_weighted_absolute_rate δ α hα hα1 hgap
  refine ⟨C, hC, ?_⟩
  intro ε x hε hx0 hx
  have hfinite (u : Finset (ℕ×ℕ)) :
      (∑ p ∈ u, |x p.1*x p.2*spacingKernelError ε p.1 p.2|) ≤ 
        C*ε^α*(∑' n : ℕ, (n:ℝ)^δ*(x n)^2) := by
    let N := u.sup (fun p => max p.1 p.2)
    have hN (p : ℕ×ℕ) (hp : p∈u) : p.1 ≤ N ∧ p.2 ≤ N :=
      ⟨(le_max_left _ _).trans (Finset.le_sup (f := fun p => max p.1 p.2) hp),
       (le_max_right _ _).trans (Finset.le_sup (f := fun p => max p.1 p.2) hp)⟩
    let v := u.filter (fun p => 0 < p.1 ∧ 0 < p.2)
    have hremove : (∑ p ∈ v, |x p.1*x p.2*spacingKernelError ε p.1 p.2|) =
        ∑ p ∈ u, |x p.1*x p.2*spacingKernelError ε p.1 p.2| := by
      apply sum_subset (filter_subset _ _)
      intro p hp hnot
      have hbad : ¬(0 < p.1 ∧ 0 < p.2) := fun h => hnot (mem_filter.mpr ⟨hp, h⟩)
      have hzero : p.1=0 ∨ p.2=0 := by omega
      rcases hzero with h | h
      · rw [h, hx0, zero_mul, zero_mul, abs_zero]
      · rw [h, hx0, mul_zero, zero_mul, abs_zero]
    have hsub : v ⊆ Icc 1 N ×ˢ Icc 1 N := by
      intro p hp
      obtain ⟨hpu, hp1, hp2⟩ := mem_filter.mp hp
      exact mem_product.mpr ⟨mem_Icc.mpr ⟨hp1, (hN p hpu).1⟩,
        mem_Icc.mpr ⟨hp2, (hN p hpu).2⟩⟩
    calc (∑ p ∈ u, |x p.1*x p.2*spacingKernelError ε p.1 p.2|) =
          ∑ p ∈ v, |x p.1*x p.2*spacingKernelError ε p.1 p.2| := hremove.symm
         _ ≤ ∑ p ∈ Icc 1 N ×ˢ Icc 1 N,
          |x p.1*x p.2*spacingKernelError ε p.1 p.2| :=
          sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => abs_nonneg _)
         _ = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N,
          |x m*x n*spacingKernelError ε m n| := by rw [sum_product]
         _ ≤ C*ε^α*∑ n ∈ Icc 1 N, (n:ℝ)^δ*(x n)^2 :=
          hbound ε (Icc 1 N) x hε (fun n hn => (mem_Icc.mp hn).1)
         _ ≤ _ := mul_le_mul_of_nonneg_left
          (hx.sum_le_tsum _ (fun n _ => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (sq_nonneg _)))
          (mul_nonneg hC.le (Real.rpow_nonneg hε.le _))
  exact ⟨summable_of_sum_le (fun _ => abs_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun _ => abs_nonneg _) hfinite⟩

/-- Every positive conductor weight supplies a common power rate for all infinite probes. -/
theorem spacingKernelError_infinite_absolute_bound (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ε : ℝ) (x : ℕ → ℝ), 0 < ε → x 0=0 →
      Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2) →
      Summable (fun p : ℕ×ℕ => |x p.1*x p.2*spacingKernelError ε p.1 p.2|) ∧
      (∑' p : ℕ×ℕ, |x p.1*x p.2*spacingKernelError ε p.1 p.2|) ≤ 
        C*ε^(min (δ/8) 1)*(∑' n : ℕ, (n:ℝ)^δ*(x n)^2) := by
  apply spacingKernelError_infinite_absolute_rate δ (min (δ/8) 1)
    (lt_min (by positivity) zero_lt_one) (min_le_right _ _)
  have hmin := min_le_left (δ/8) (1:ℝ)
  linarith only [hmin, hδ]

/-- The entire absolute error tends to zero for every infinite positively weighted probe. -/
theorem tendsto_spacingKernelError_infinite_absolute (δ : ℝ) (hδ : 0 < δ)
    (x : ℕ → ℝ) (hx0 : x 0=0)
    (hx : Summable (fun n : ℕ => (n:ℝ)^δ*(x n)^2)) :
    Tendsto (fun ε : ℝ => ∑' p : ℕ×ℕ,
      |x p.1*x p.2*spacingKernelError ε p.1 p.2|) (𝓝[>] (0:ℝ)) (𝓝 0) := by
  obtain ⟨C, _hC, hbound⟩ := spacingKernelError_infinite_absolute_bound δ hδ
  have hα : 0 < min (δ/8) 1 := lt_min (by positivity) zero_lt_one
  have hcont : ContinuousAt (fun ε : ℝ => ε^(min (δ/8) 1)) 0 :=
    Real.continuousAt_rpow_const 0 _ (Or.inr hα.le)
  have hp := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  rw [Real.zero_rpow hα.ne'] at hp
  have hmajor := (hp.const_mul C).mul_const (∑' n : ℕ, (n:ℝ)^δ*(x n)^2)
  simp only [mul_zero, zero_mul] at hmajor
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => tsum_nonneg fun _ => abs_nonneg _) _ hmajor
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hbound ε x hε hx0 hx).2

#print axioms spacingKernelError_infinite_absolute_rate
#print axioms spacingKernelError_infinite_absolute_bound
#print axioms tendsto_spacingKernelError_infinite_absolute

end GaloisForLFunctions.HeightHomotopyArithmeticCounts
