import GaloisForLFunctions.HTGeometry.MittagLefflerConvergence

/-!
# The Mittag-Leffler construction

Given poles `a n` tending to infinity and principal parts `P n` holomorphic off `a n`, each `P n` is
holomorphic on the disc of radius `‖a n‖`, so a partial sum `Q n` of its expansion at the origin
approximates it within `2⁻ⁿ` on the disc of radius `‖a n‖/2`.  The corrected series

`f(z) = ∑ (P n z - Q n z)`

then converges at every point, and on any fixed disc all but finitely many terms are holomorphic
and dominated by `2⁻ⁿ`, so the sum splits there into a finite head carrying the poles and a
holomorphic tail.
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Filter

/-! ### Partial sums are entire -/

theorem differentiable_partialSum_apply (p : FormalMultilinearSeries ℂ ℂ ℂ) (i : ℕ) :
    Differentiable ℂ (fun z : ℂ => (p i) fun _ => z) := by
  have hdiag : Differentiable ℂ (fun z : ℂ => (fun _ : Fin i => z)) :=
    (ContinuousLinearMap.pi (fun _ : Fin i => ContinuousLinearMap.id ℂ ℂ)).differentiable
  exact (((p i).contDiff (n := (1 : ℕ))).differentiable (by norm_num)).comp hdiag

theorem differentiable_partialSum (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
    Differentiable ℂ (fun z : ℂ => p.partialSum n z) := by
  unfold FormalMultilinearSeries.partialSum
  exact Differentiable.fun_sum fun i _ => differentiable_partialSum_apply p i

/-! ### Approximation with real radii -/

/-- **Entire approximation on a smaller disc**, stated with real radii. -/
theorem exists_entire_approx {f : ℂ → ℂ} {R r ε : ℝ} (hR : 0 < R) (hrR : r < R) (hε : 0 < ε)
    (hf : DifferentiableOn ℂ f (closedBall (0 : ℂ) R)) :
    ∃ Q : ℂ → ℂ, Differentiable ℂ Q ∧ ∀ z ∈ ball (0 : ℂ) r, ‖f z - Q z‖ < ε := by
  set R' : NNReal := R.toNNReal with hR'
  set r' : NNReal := (max r 0).toNNReal with hr'
  have hR'coe : ((R' : ℝ)) = R := Real.coe_toNNReal R hR.le
  have hr'coe : ((r' : ℝ)) = max r 0 := Real.coe_toNNReal _ (le_max_right _ _)
  have hR'pos : 0 < R' := Real.toNNReal_pos.mpr hR
  have hr'R' : r' < R' := by
    rw [← NNReal.coe_lt_coe, hr'coe, hR'coe]
    exact max_lt hrR hR
  have hfR : DifferentiableOn ℂ f (closedBall (0 : ℂ) ((R' : ℝ))) := by
    rw [hR'coe]; exact hf
  obtain ⟨n, hn⟩ := exists_partialSum_approx hR'pos hfR hr'R' hε
  refine ⟨fun z => (cauchyPowerSeries f 0 ((R' : ℝ))).partialSum n z,
    differentiable_partialSum _ n, fun z hz => ?_⟩
  refine hn z ?_
  simp only [mem_ball, dist_zero_right] at hz ⊢
  calc ‖z‖ < r := hz
    _ ≤ (r' : ℝ) := by rw [hr'coe]; exact le_max_left _ _

/-! ### The corrected series -/

/-- **The Mittag-Leffler corrections exist.**  Each principal part is approximated to within `2⁻ⁿ`
on the disc of half the modulus of its pole by an entire function. -/
theorem exists_mittagLeffler_corrections {a : ℕ → ℂ} {P : ℕ → ℂ → ℂ}
    (hane : ∀ n, a n ≠ 0)
    (hP : ∀ n, DifferentiableOn ℂ (P n) {z : ℂ | z ≠ a n}) :
    ∃ Q : ℕ → ℂ → ℂ, (∀ n, Differentiable ℂ (Q n)) ∧
      ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (‖a n‖ / 2), ‖P n z - Q n z‖ ≤ (1 / 2 : ℝ) ^ n := by
  choose Q hQd hQb using fun n : ℕ => by
    have hpos : 0 < ‖a n‖ := norm_pos_iff.mpr (hane n)
    have hR : (0 : ℝ) < 3 * ‖a n‖ / 4 := by linarith
    have hrR : ‖a n‖ / 2 < 3 * ‖a n‖ / 4 := by linarith
    have hsub : closedBall (0 : ℂ) (3 * ‖a n‖ / 4) ⊆ {z : ℂ | z ≠ a n} := by
      intro z hz
      simp only [mem_closedBall, dist_zero_right] at hz
      simp only [Set.mem_setOf_eq]
      intro hzz
      rw [hzz] at hz
      linarith
    exact exists_entire_approx hR hrR (by positivity : (0 : ℝ) < (1 / 2 : ℝ) ^ n)
      ((hP n).mono hsub)
  exact ⟨Q, hQd, fun n z hz => (hQb n z hz).le⟩

/-- **The corrected series converges at every point.** -/
theorem summable_mittagLeffler {a : ℕ → ℂ} {P Q : ℕ → ℂ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hQb : ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (‖a n‖ / 2), ‖P n z - Q n z‖ ≤ (1 / 2 : ℝ) ^ n) (z : ℂ) :
    Summable fun n => P n z - Q n z := by
  have hu : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine summable_of_growing_radii (g := fun n z => P n z - Q n z) (R := fun n => ‖a n‖ / 2)
    (u := fun n : ℕ => (1 / 2 : ℝ) ^ n) hu ?_ ?_ z
  · exact Filter.Tendsto.atTop_div_const (by norm_num) ha
  · intro n w hw
    exact hQb n w (by simpa [mem_ball, dist_zero_right] using hw)

/-- **The head–tail structure on a disc.**  Beyond an index where every remaining pole is outside
the disc, the terms are holomorphic there and dominated by `2⁻ⁿ`, so the tail is holomorphic. -/
theorem differentiableOn_mittagLeffler_tail {a : ℕ → ℂ} {P Q : ℕ → ℂ → ℂ} {M : ℝ} {N : ℕ}
    (hQd : ∀ n, Differentiable ℂ (Q n))
    (hP : ∀ n, DifferentiableOn ℂ (P n) {z : ℂ | z ≠ a n})
    (hQb : ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (‖a n‖ / 2), ‖P n z - Q n z‖ ≤ (1 / 2 : ℝ) ^ n)
    (hN : ∀ k : ℕ, M < ‖a (k + N)‖ / 2) :
    DifferentiableOn ℂ (seriesTail (fun n z => P n z - Q n z) N) (ball (0 : ℂ) M) := by
  have hu : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine differentiableOn_seriesTail (u := fun n : ℕ => (1 / 2 : ℝ) ^ n) hu
    (fun k => ?_) (fun k z hz => ?_)
  · have hsub : ball (0 : ℂ) M ⊆ {z : ℂ | z ≠ a (k + N)} := by
      intro z hz
      simp only [mem_ball, dist_zero_right] at hz
      simp only [Set.mem_setOf_eq]
      intro hzz
      have hk := hN k
      have hnn : (0 : ℝ) ≤ ‖a (k + N)‖ := norm_nonneg _
      rw [hzz] at hz
      linarith
    exact ((hP (k + N)).mono hsub).sub (hQd (k + N)).differentiableOn
  · refine hQb (k + N) z ?_
    simp only [mem_ball, dist_zero_right] at hz ⊢
    exact lt_trans hz (hN k)

/-! ### The Mittag-Leffler function -/

/-- The Mittag-Leffler function attached to principal parts `P` and corrections `Q`. -/
noncomputable def mittagLeffler (P Q : ℕ → ℂ → ℂ) : ℂ → ℂ :=
  fun z => ∑' n : ℕ, (P n z - Q n z)

/-- **A cutoff index past every pole meeting a given disc**, chosen beyond a prescribed index. -/
theorem exists_mittagLeffler_cutoff {a : ℕ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop) (M : ℝ) (n₀ : ℕ) :
    ∃ N : ℕ, n₀ < N ∧ ∀ k : ℕ, M < ‖a (k + N)‖ / 2 := by
  have hdiv : Tendsto (fun n => ‖a n‖ / 2) atTop atTop :=
    Filter.Tendsto.atTop_div_const (by norm_num) ha
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp (hdiv.eventually_gt_atTop M)
  refine ⟨max (n₀ + 1) N₀, lt_of_lt_of_le (Nat.lt_succ_self n₀) (le_max_left _ _), fun k => ?_⟩
  exact hN₀ _ (le_trans (le_max_right _ _) (Nat.le_add_left _ k))

/-- **Head–tail decomposition of the Mittag-Leffler function.** -/
theorem mittagLeffler_eq_head_add_tail {a : ℕ → ℂ} {P Q : ℕ → ℂ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hQb : ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (‖a n‖ / 2), ‖P n z - Q n z‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) (z : ℂ) :
    mittagLeffler P Q z
      = (∑ n ∈ Finset.range N, (P n z - Q n z))
        + seriesTail (fun n z => P n z - Q n z) N z := by
  rw [mittagLeffler]
  exact tsum_eq_head_add_seriesTail (g := fun n z => P n z - Q n z) N
    (summable_mittagLeffler ha hQb z)

/-- **The Mittag-Leffler function is holomorphic off the poles inside any disc.**  On a disc, the
function differs from a holomorphic tail by the finitely many corrected principal parts that meet
it. -/
theorem differentiableOn_mittagLeffler_sub_head {a : ℕ → ℂ} {P Q : ℕ → ℂ → ℂ} {M : ℝ} {N : ℕ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hQd : ∀ n, Differentiable ℂ (Q n))
    (hP : ∀ n, DifferentiableOn ℂ (P n) {z : ℂ | z ≠ a n})
    (hQb : ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (‖a n‖ / 2), ‖P n z - Q n z‖ ≤ (1 / 2 : ℝ) ^ n)
    (hN : ∀ k : ℕ, M < ‖a (k + N)‖ / 2) :
    DifferentiableOn ℂ
      (fun z => mittagLeffler P Q z - ∑ n ∈ Finset.range N, (P n z - Q n z))
      (ball (0 : ℂ) M) := by
  have heq : Set.EqOn (fun z => mittagLeffler P Q z - ∑ n ∈ Finset.range N, (P n z - Q n z))
      (seriesTail (fun n z => P n z - Q n z) N) (ball (0 : ℂ) M) := by
    intro z _
    show mittagLeffler P Q z - ∑ n ∈ Finset.range N, (P n z - Q n z)
        = seriesTail (fun n z => P n z - Q n z) N z
    rw [mittagLeffler_eq_head_add_tail ha hQb N z]
    ring
  exact (differentiableOn_mittagLeffler_tail hQd hP hQb hN).congr heq

/-- **The Mittag-Leffler function has the prescribed principal part at every pole.**  At `a n₀` the
difference `f - P n₀` is holomorphic: the tail is holomorphic on a disc containing the pole, every
other corrected principal part is holomorphic there because the poles are distinct, and the
correction `Q n₀` is entire. -/
theorem differentiableAt_mittagLeffler_sub {a : ℕ → ℂ} {P Q : ℕ → ℂ → ℂ}
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hinj : Function.Injective a)
    (hQd : ∀ n, Differentiable ℂ (Q n))
    (hP : ∀ n, DifferentiableOn ℂ (P n) {z : ℂ | z ≠ a n})
    (hQb : ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (‖a n‖ / 2), ‖P n z - Q n z‖ ≤ (1 / 2 : ℝ) ^ n)
    (n₀ : ℕ) :
    DifferentiableAt ℂ (fun z => mittagLeffler P Q z - P n₀ z) (a n₀) := by
  classical
  obtain ⟨N, hn₀N, hN⟩ := exists_mittagLeffler_cutoff ha (‖a n₀‖ + 1) n₀
  have hmem : a n₀ ∈ ball (0 : ℂ) (‖a n₀‖ + 1) := by
    simp only [mem_ball, dist_zero_right]
    linarith
  have h1 : DifferentiableAt ℂ
      (fun z => mittagLeffler P Q z - ∑ n ∈ Finset.range N, (P n z - Q n z)) (a n₀) :=
    (differentiableOn_mittagLeffler_sub_head ha hQd hP hQb hN).differentiableAt
      (isOpen_ball.mem_nhds hmem)
  have h2 : DifferentiableAt ℂ
      (fun z => (∑ n ∈ Finset.range N, (P n z - Q n z)) - P n₀ z) (a n₀) := by
    have hsplit : (fun z => (∑ n ∈ Finset.range N, (P n z - Q n z)) - P n₀ z)
        = fun z => (∑ n ∈ (Finset.range N).erase n₀, (P n z - Q n z)) - Q n₀ z := by
      funext z
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hn₀N)]
      ring
    rw [hsplit]
    refine DifferentiableAt.sub ?_ (hQd n₀ (a n₀))
    refine DifferentiableAt.fun_sum fun n hn => ?_
    have hne : a n₀ ≠ a n := fun h => (Finset.mem_erase.mp hn).1 (hinj h).symm
    exact ((hP n).differentiableAt (isOpen_ne.mem_nhds hne)).sub (hQd n (a n₀))
  have hsum : (fun z => mittagLeffler P Q z - P n₀ z)
      = fun z => (mittagLeffler P Q z - ∑ n ∈ Finset.range N, (P n z - Q n z))
        + ((∑ n ∈ Finset.range N, (P n z - Q n z)) - P n₀ z) := by
    funext z
    ring
  rw [hsum]
  exact h1.add h2

end GaloisForLFunctions.HTGeometry
