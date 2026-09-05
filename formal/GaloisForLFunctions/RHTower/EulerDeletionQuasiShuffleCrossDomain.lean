import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleSecondConvergence

/-!
# A zero-independent domain for ordered Euler-deletion cross sums

Bounded deletion prefixes and finite variation of a weighted inner prefix give chronological
cross-level convergence when both real parts are positive and their sum exceeds one. No zeta-zero
assumption enters this domain theorem. This is convergence under the stated chronological cutoffs;
it does not assert unconditional summability or justify arbitrary rearrangements.
-/

noncomputable section
open Filter Topology
open scoped BigOperators

namespace RHTower.DeletionChronologicalLimit

/-- Abel summation with a vanishing test sequence of finite total variation. -/
theorem ordered_sum_of_finite_variation {a g : ℕ → ℂ} {C : ℝ}
    (ha : ∀ N, ‖∑ n ∈ Finset.range N, a n‖ ≤ C)
    (hg : Tendsto g atTop (nhds 0))
    (hdg : Summable (fun n => ‖g (n+1) - g n‖)) :
    ∃ L : ℂ, Tendsto (fun N => ∑ n ∈ Finset.range N, a n * g n) atTop (nhds L) := by
  let A (N : ℕ) : ℂ := ∑ n ∈ Finset.range N, a n
  have hd : Summable (fun n => (g (n+1) - g n) * A (n+1)) := by
    apply Summable.of_norm_bounded (hdg.mul_right C)
    intro n
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (ha (n+1)) (norm_nonneg _)
  obtain ⟨L, hL⟩ := hd
  refine ⟨-L, ?_⟩
  have hid : ∀ N,
      (∑ n ∈ Finset.range N, a n * g n) = g (N-1) * A N -
        ∑ n ∈ Finset.range (N-1), (g (n+1) - g n) * A (n+1) := by
    intro N
    have he := Finset.sum_range_by_parts g a N
    simp only [smul_eq_mul] at he
    rw [show (∑ n ∈ Finset.range N, a n * g n) =
      ∑ n ∈ Finset.range N, g n * a n from
        Finset.sum_congr rfl (fun n _ => mul_comm _ _)]
    exact he
  have hboundary : Tendsto (fun N => g (N-1) * A N) atTop (nhds 0) := by
    have hnorm := ((hg.comp (Filter.tendsto_sub_atTop_nat 1)).norm).mul_const C
    apply squeeze_zero_norm' ?_ (by simpa using hnorm)
    exact Filter.Eventually.of_forall (fun N => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (ha N) (norm_nonneg _))
  have hsum := hL.tendsto_sum_nat.comp (Filter.tendsto_sub_atTop_nat 1)
  convert (hboundary.sub hsum).congr (fun N => (hid N).symm) using 1
  simp

def kernel (s : ℂ) (n : ℕ) : ℂ := (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-s)
def innerPrefix (q : ℕ) (s : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, eulerDeletionWeightedJump q s n

theorem norm_kernel (s : ℂ) (n : ℕ) :
    ‖kernel s n‖ = ((n : ℝ)+1) ^ (-s.re) := by
  rw [kernel, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re]

theorem kernel_tendsto_zero (s : ℂ) (hs : 0 < s.re) :
    Tendsto (kernel s) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp_rw [norm_kernel]
  have he := (GaloisForLFunctions.RHTower.tendsto_rpow_neg_nat_atTop hs).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using he

theorem kernel_increment_summable (s : ℂ) (hs : 0 < s.re) :
    Summable (fun n => ‖kernel s (n+1) - kernel s n‖) := by
  refine (GaloisForLFunctions.RHTower.summable_norm_cpow_increment hs).congr ?_
  intro n
  simp only [kernel, Nat.cast_add, Nat.cast_one]
  rw [norm_sub_rev]
  congr 3
  ring_nf

theorem coefficient_norm_le (q n : ℕ) :
    ‖eulerDeletionDirichletCoefficient q n‖ ≤ q := by
  by_cases hq : 0 < q
  · exact norm_eulerDeletionDirichletCoefficient_le hq n
  · have hq0 : q = 0 := by omega
    simp [hq0, eulerDeletionDirichletCoefficient, blockDeletionCoefficient]

theorem innerPrefix_converges (q : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ∃ L : ℂ, Tendsto (innerPrefix q s) atTop (nhds L) := by
  exact tendsto_eulerDeletionDirichletCoefficient (q := q) hs

theorem innerPrefix_bounded (q : ℕ) (s : ℂ) (hs : 0 < s.re) :
    ∃ B : ℝ, ∀ N, ‖innerPrefix q s N‖ ≤ B := by
  obtain ⟨L, hL⟩ := innerPrefix_converges q s hs
  obtain ⟨B, hB⟩ := hL.norm.bddAbove_range
  exact ⟨B, fun N => hB ⟨N, rfl⟩⟩

def outerTest (q : ℕ) (s t : ℂ) (n : ℕ) : ℂ :=
  innerPrefix q s n * star (kernel t n)

theorem outerTest_tendsto_zero (q : ℕ) (s t : ℂ)
    (hs : 0 < s.re) (ht : 0 < t.re) :
    Tendsto (outerTest q s t) atTop (nhds 0) := by
  obtain ⟨L, hL⟩ := innerPrefix_converges q s hs
  have he := hL.mul (kernel_tendsto_zero t ht).star
  change Tendsto (fun n => innerPrefix q s n * star (kernel t n)) atTop (nhds 0)
  simpa using he

theorem outerTest_increment (q n : ℕ) (s t : ℂ) :
    outerTest q s t (n+1) - outerTest q s t n =
      eulerDeletionWeightedJump q s n * star (kernel t n) +
      innerPrefix q s (n+1) * star (kernel t (n+1) - kernel t n) := by
  have hi : innerPrefix q s (n+1) = innerPrefix q s n + eulerDeletionWeightedJump q s n := by
    exact Finset.sum_range_succ _ _
  rw [outerTest, outerTest, star_sub, hi]
  ring

theorem outerTest_increment_summable (q : ℕ) (s t : ℂ)
    (hs : 0 < s.re) (ht : 0 < t.re) (hst : 1 < s.re + t.re) :
    Summable (fun n => ‖outerTest q s t (n+1) - outerTest q s t n‖) := by
  obtain ⟨B, hB⟩ := innerPrefix_bounded q s hs
  have hr0 : Summable (fun n : ℕ => (n : ℝ) ^ (-(s.re+t.re))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hr : Summable (fun n : ℕ => ((n : ℝ)+1) ^ (-(s.re+t.re))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-(s.re+t.re))) 1).2 hr0
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
    (f := fun n : ℕ => (q : ℝ) * ((n : ℝ)+1) ^ (-(s.re+t.re)) +
      B * ‖kernel t (n+1) - kernel t n‖)
  · intro n
    rw [outerTest_increment]
    calc
      ‖eulerDeletionWeightedJump q s n * star (kernel t n) +
          innerPrefix q s (n+1) * star (kernel t (n+1) - kernel t n)‖ ≤
          ‖eulerDeletionWeightedJump q s n * star (kernel t n)‖ +
            ‖innerPrefix q s (n+1) * star (kernel t (n+1) - kernel t n)‖ := norm_add_le _ _
      _ ≤ (q : ℝ) * ((n : ℝ)+1) ^ (-(s.re+t.re)) +
          B * ‖kernel t (n+1) - kernel t n‖ := by
        apply add_le_add
        · change ‖(eulerDeletionDirichletCoefficient q n * kernel s n) * star (kernel t n)‖ ≤ _
          rw [norm_mul, norm_mul, norm_star, norm_kernel, norm_kernel, mul_assoc,
            ← Real.rpow_add (by positivity)]
          simpa only [neg_add] using mul_le_mul_of_nonneg_right (coefficient_norm_le q n)
            (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)+1)
              (-s.re + -t.re))
        · rw [norm_mul, norm_star]
          exact mul_le_mul_of_nonneg_right (hB (n+1)) (norm_nonneg _)
  · exact (hr.mul_left (q : ℝ)).add ((kernel_increment_summable t ht).mul_left B)

def crossPrefix (p q : ℕ) (s t : ℂ) (N : ℕ) : ℂ :=
  ∑ j ∈ Finset.range N, innerPrefix p s j * star (eulerDeletionWeightedJump q t j)

theorem crossPrefix_converges (p q : ℕ) (s t : ℂ)
    (hs : 0 < s.re) (ht : 0 < t.re) (hst : 1 < s.re+t.re) :
    ∃ L : ℂ, Tendsto (crossPrefix p q s t) atTop (nhds L) := by
  obtain ⟨L, hL⟩ := ordered_sum_of_finite_variation
    (eulerDeletionDirichletCoefficient_partialSum_norm_le q)
    (outerTest_tendsto_zero p s t hs ht) (outerTest_increment_summable p s t hs ht hst)
  refine ⟨L, ?_⟩
  convert hL using 1
  ext N
  apply Finset.sum_congr rfl
  intro j _
  simp only [outerTest, eulerDeletionWeightedJump, star_mul']
  have ha : star (eulerDeletionDirichletCoefficient q j) =
      eulerDeletionDirichletCoefficient q j := by simp [eulerDeletionDirichletCoefficient]
  rw [ha]
  change innerPrefix p s j * (eulerDeletionDirichletCoefficient q j * star (kernel t j)) = _
  ring

end RHTower.DeletionChronologicalLimit

namespace RHTower

/-- The ordered cross level exists on this entire domain, without a zeta-zero assumption. -/
theorem tendsto_chronologicalCrossPrefix_eulerDeletion_domain (p q : ℕ) (s t : ℂ)
    (hs : 0 < s.re) (ht : 0 < t.re) (hst : 1 < s.re + t.re) :
    ∃ L : ℂ, Tendsto
      (fun N => chronologicalCrossPrefix (eulerDeletionWeightedJump p s)
        (eulerDeletionWeightedJump q t) N) atTop (nhds L) := by
  exact DeletionChronologicalLimit.crossPrefix_converges p q s t hs ht hst

/-- Every deletion path has a chronological self limit right of the half-line, at arbitrary `s`. -/
theorem tendsto_chronologicalSecondPrefix_eulerDeletion_domain (q : ℕ) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    ∃ L : ℂ, Tendsto
      (fun N => chronologicalSecondPrefix (eulerDeletionWeightedJump q s) N)
      atTop (nhds L) := by
  have hs0 : 0 < s.re := by linarith
  exact tendsto_chronologicalCrossPrefix_eulerDeletion_domain q q s s hs0 hs0 (by linarith)

end RHTower

