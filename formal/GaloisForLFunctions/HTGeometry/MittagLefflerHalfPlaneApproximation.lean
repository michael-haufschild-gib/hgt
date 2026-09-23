import GaloisForLFunctions.HTGeometry.HalfPlaneGapApproximation
import GaloisForLFunctions.HTGeometry.MittagLefflerConstruction

/-!
# Entire approximation of a Mittag-Leffler series on a closed half plane

A Mittag-Leffler series with simple poles `a n` tending to infinity, all lying to the left of the
line `Re s = 1`, is approximated on the closed half plane `Re s ≥ 1`, after multiplication by `s²`,
by an entire function, to within any prescribed accuracy.

The mechanism is termwise.  Writing `s² = (s - a)(s + a) + a²`,

```text
s² (m/(s-a) - Q(s))  =  m a²/(s-a)  +  (m (s+a) - s² Q(s)) ,
```

the second bracket is entire and needs no approximation, while the single Cauchy kernel
`m a²/(s-a)` is approximated by a truncated Laplace kernel — pushed left first when its pole is not
already to the left of the disc used to control convergence.  Because the approximation of the
`n`-th kernel is good both on the half plane and on a disc of radius growing with `‖a n‖`, the
corrected series converges locally uniformly on the whole plane, so its sum is entire, while on the
half plane the accumulated error is a geometric series.

This is the analytic input that Arakelyan's theorem supplies in general; for a Mittag-Leffler datum
it is elementary.
-/

noncomputable section

open Metric Filter MeasureTheory

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 2000000 in
/-- **Entire approximation of `s² + κ s` times a Mittag-Leffler series on the closed half
plane.** -/
theorem exists_entire_approx_sq_mittagLeffler {a m : ℕ → ℂ} {Q : ℕ → ℂ → ℂ} {u : ℕ → ℝ} (κ : ℂ)
    (ha : Tendsto (fun n => ‖a n‖) atTop atTop)
    (hare : ∀ n, (a n).re < 1)
    (hQd : ∀ n, Differentiable ℂ (Q n))
    (hu : Summable u)
    (hQb : ∀ n : ℕ, ∀ z ∈ ball (0 : ℂ) (‖a n‖ / 2), ‖m n / (z - a n) - Q n z‖ ≤ u n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧
      ∀ s : ℂ, 1 ≤ s.re →
        ‖(s ^ (2 : ℕ) + κ * s) * (∑' n : ℕ, (m n / (s - a n) - Q n s)) - G s‖ ≤ ε := by
  set ε' : ℝ := ε / 4 with hε'def
  have hε' : 0 < ε' := by rw [hε'def]; linarith
  set ρ : ℕ → ℝ := fun n => (‖a n‖ - 16) / 8 with hρdef
  -- the termwise approximants
  have hchoice : ∀ n : ℕ, ∃ hn : ℂ → ℂ, Differentiable ℂ hn ∧
      (∀ s : ℂ, 1 ≤ s.re →
        ‖(m n * ((a n) ^ (2 : ℕ) + κ * a n)) * (s - a n)⁻¹ - hn s‖ ≤ ε' * (1 / 2 : ℝ) ^ n) ∧
      (∀ s : ℂ, ‖s‖ ≤ ρ n →
        ‖(m n * ((a n) ^ (2 : ℕ) + κ * a n)) * (s - a n)⁻¹ - hn s‖ ≤ ε' * (1 / 2 : ℝ) ^ n) := by
    intro n
    have hpos : 0 < ε' * (1 / 2 : ℝ) ^ n := by positivity
    by_cases hρn : 0 ≤ ρ n
    · have hbig : 8 * ρ n + 16 ≤ ‖a n‖ := by
        rw [hρdef]
        linarith
      obtain ⟨g, hgd, hgb⟩ :=
        exists_entire_approx_single_kernel (c := m n * ((a n) ^ (2 : ℕ) + κ * a n))
        (hare n) hρn hbig hpos
      exact ⟨g, hgd, fun s hs => hgb s (Or.inl hs), fun s hs => hgb s (Or.inr hs)⟩
    · rw [not_le] at hρn
      obtain ⟨g, hgd, hgb⟩ := exists_entire_approx_single_kernel_halfPlane
        (c := m n * ((a n) ^ (2 : ℕ) + κ * a n)) (hare n) hpos
      refine ⟨g, hgd, hgb, fun s hs => ?_⟩
      exact absurd hs (by linarith [norm_nonneg s])
  choose hker hkerd hkerE hkerB using hchoice
  set K : ℕ → ℂ → ℂ := fun n s => (m n * ((a n) ^ (2 : ℕ) + κ * a n)) * (s - a n)⁻¹ with hKdef
  set Ent : ℕ → ℂ → ℂ :=
    fun n s => m n * (s + a n + κ) - (s ^ (2 : ℕ) + κ * s) * Q n s with hEdef
  have hEd : ∀ n, Differentiable ℂ (Ent n) := by
    intro n
    rw [hEdef]
    exact ((differentiable_const _).mul
        ((differentiable_id.add (differentiable_const _)).add (differentiable_const _))).sub
      (((differentiable_id.pow 2).add ((differentiable_const _).mul differentiable_id)).mul
        (hQd n))
  have hgd : ∀ n, Differentiable ℂ (fun s => Ent n s + hker n s) := fun n => (hEd n).add (hkerd n)
  have hid : ∀ (n : ℕ) (s : ℂ), s ≠ a n →
      (s ^ (2 : ℕ) + κ * s) * (m n / (s - a n) - Q n s) = K n s + Ent n s := by
    intro n s hs
    have hne : s - a n ≠ 0 := sub_ne_zero.mpr hs
    rw [hKdef, hEdef]
    field_simp
    ring
  have hML : ∀ z : ℂ, Summable fun n => m n / (z - a n) - Q n z := by
    intro z
    refine summable_of_growing_radii (g := fun n z => m n / (z - a n) - Q n z)
      (R := fun n => ‖a n‖ / 2) hu (Filter.Tendsto.atTop_div_const (by norm_num) ha) ?_ z
    intro n w hw
    exact hQb n w (by simpa [mem_ball, dist_zero_right] using hw)
  -- a cutoff past which the point is inside every remaining approximation disc
  have hcut : ∀ z : ℂ, ∃ N : ℕ, ∀ k : ℕ,
      ‖z‖ < ‖a (k + N)‖ / 2 ∧ ‖z‖ ≤ ρ (k + N) := by
    intro z
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (ha.eventually_gt_atTop (max (2 * ‖z‖ + 1) (8 * ‖z‖ + 16)))
    refine ⟨N, fun k => ?_⟩
    have hk := hN (k + N) (Nat.le_add_left _ _)
    have h1 : 2 * ‖z‖ + 1 < ‖a (k + N)‖ := lt_of_le_of_lt (le_max_left _ _) hk
    have h2 : 8 * ‖z‖ + 16 < ‖a (k + N)‖ := lt_of_le_of_lt (le_max_right _ _) hk
    refine ⟨by linarith, ?_⟩
    rw [hρdef]
    dsimp only
    linarith
  -- summability of the corrected terms at every point
  have hsumK : ∀ z : ℂ, Summable fun n => K n z - hker n z := by
    intro z
    obtain ⟨N, hN⟩ := hcut z
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n : ℕ => ε' * (1 / 2 : ℝ) ^ n) ?_ ?_
    · exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ε'
    · filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hk : n = (n - N) + N := by omega
      rw [hk]
      exact hkerB _ z (hN (n - N)).2
  have hsumKE : ∀ z : ℂ, Summable fun n => K n z + Ent n z := by
    intro z
    obtain ⟨N, hN⟩ := hcut z
    have hz2 : Summable fun n => (z ^ (2 : ℕ) + κ * z) * (m n / (z - a n) - Q n z) := (hML z).mul_left _
    have htail : Summable fun k : ℕ => K (k + N) z + Ent (k + N) z := by
      have hz2t : Summable fun k : ℕ =>
          (z ^ (2 : ℕ) + κ * z) * (m (k + N) / (z - a (k + N)) - Q (k + N) z) :=
        (summable_nat_add_iff N).mpr hz2
      refine hz2t.congr fun k => ?_
      refine hid (k + N) z ?_
      intro hzz
      have := (hN k).1
      rw [← hzz] at this
      have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
      linarith
    exact (summable_nat_add_iff N).mp htail
  have hsumg : ∀ z : ℂ, Summable fun n => Ent n z + hker n z := by
    intro z
    have := (hsumKE z).sub (hsumK z)
    refine this.congr fun n => ?_
    ring
  refine ⟨fun s => ∑' n : ℕ, (Ent n s + hker n s), ?_, ?_⟩
  · -- entirety
    intro z₀
    set M : ℝ := ‖z₀‖ + 1 with hMdef
    have hM : 0 < M := by rw [hMdef]; positivity
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
      (ha.eventually_gt_atTop (max (2 * M + 1) (8 * M + 16)))
    have hNball : ∀ k : ℕ, M < ‖a (k + N)‖ / 2 := by
      intro k
      have hk := hN (k + N) (Nat.le_add_left _ _)
      have h1 : 2 * M + 1 < ‖a (k + N)‖ := lt_of_le_of_lt (le_max_left _ _) hk
      linarith
    have hNrho : ∀ k : ℕ, M ≤ ρ (k + N) := by
      intro k
      have hk := hN (k + N) (Nat.le_add_left _ _)
      have h2 : 8 * M + 16 < ‖a (k + N)‖ := lt_of_le_of_lt (le_max_right _ _) hk
      rw [hρdef]
      dsimp only
      linarith
    have htail : DifferentiableOn ℂ
        (seriesTail (fun n s => Ent n s + hker n s) N) (ball (0 : ℂ) M) := by
      refine differentiableOn_seriesTail
        (u := fun n : ℕ => (M ^ (2 : ℕ) + ‖κ‖ * M) * u n + ε' * (1 / 2 : ℝ) ^ n)
        ((hu.mul_left (M ^ (2 : ℕ) + ‖κ‖ * M)).add
          ((summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ε'))
        (fun k => (hgd (k + N)).differentiableOn) (fun k z hz => ?_)
      have hznorm : ‖z‖ < M := by simpa [mem_ball, dist_zero_right] using hz
      have hzne : z ≠ a (k + N) := by
        intro hzz
        have := hNball k
        rw [← hzz] at this
        have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
        linarith
      have hidk := hid (k + N) z hzne
      have hMLb : ‖m (k + N) / (z - a (k + N)) - Q (k + N) z‖ ≤ u (k + N) := by
        refine hQb (k + N) z ?_
        simp only [mem_ball, dist_zero_right]
        exact lt_trans hznorm (hNball k)
      have hu0 : 0 ≤ u (k + N) := le_trans (norm_nonneg _) hMLb
      have hznn : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
      have hcoef : ‖z ^ (2 : ℕ) + κ * z‖ ≤ M ^ (2 : ℕ) + ‖κ‖ * M := by
        refine le_trans (norm_add_le _ _) (add_le_add ?_ ?_)
        · rw [norm_pow]
          exact pow_le_pow_left₀ hznn hznorm.le 2
        · rw [norm_mul]
          exact mul_le_mul_of_nonneg_left hznorm.le (norm_nonneg κ)
      have hsq : ‖(z ^ (2 : ℕ) + κ * z) * (m (k + N) / (z - a (k + N)) - Q (k + N) z)‖
          ≤ (M ^ (2 : ℕ) + ‖κ‖ * M) * u (k + N) := by
        rw [norm_mul]
        refine mul_le_mul hcoef hMLb (norm_nonneg _) ?_
        have : (0:ℝ) ≤ M ^ (2 : ℕ) := by positivity
        have h2 : (0:ℝ) ≤ ‖κ‖ * M := by
          refine mul_nonneg (norm_nonneg κ) ?_
          linarith [hznn, hznorm]
        linarith
      have hKb : ‖K (k + N) z - hker (k + N) z‖ ≤ ε' * (1 / 2 : ℝ) ^ (k + N) :=
        hkerB (k + N) z (le_trans hznorm.le (hNrho k))
      have hsplit : Ent (k + N) z + hker (k + N) z
          = (z ^ (2 : ℕ) + κ * z) * (m (k + N) / (z - a (k + N)) - Q (k + N) z)
            - (K (k + N) z - hker (k + N) z) := by
        rw [hidk]
        ring
      rw [hsplit]
      calc ‖(z ^ (2 : ℕ) + κ * z) * (m (k + N) / (z - a (k + N)) - Q (k + N) z)
              - (K (k + N) z - hker (k + N) z)‖
          ≤ ‖(z ^ (2 : ℕ) + κ * z) * (m (k + N) / (z - a (k + N)) - Q (k + N) z)‖
            + ‖K (k + N) z - hker (k + N) z‖ := norm_sub_le _ _
        _ ≤ (M ^ (2 : ℕ) + ‖κ‖ * M) * u (k + N) + ε' * (1 / 2 : ℝ) ^ (k + N) := add_le_add hsq hKb
    have hhead : DifferentiableOn ℂ
        (fun s => ∑ n ∈ Finset.range N, (Ent n s + hker n s)) (ball (0 : ℂ) M) :=
      (Differentiable.fun_sum fun n _ => hgd n).differentiableOn
    have hdiff : DifferentiableOn ℂ (fun s => ∑' n : ℕ, (Ent n s + hker n s)) (ball (0 : ℂ) M) := by
      refine (hhead.add htail).congr fun z _ => ?_
      simp only [Pi.add_apply]
      exact tsum_eq_head_add_seriesTail (g := fun n s => Ent n s + hker n s) N (hsumg z)
    have hz₀ : z₀ ∈ ball (0 : ℂ) M := by
      simp only [mem_ball, dist_zero_right, hMdef]
      linarith
    exact hdiff.differentiableAt (isOpen_ball.mem_nhds hz₀)
  · -- the half-plane bound
    intro s hs
    have hne : ∀ n : ℕ, s ≠ a n := by
      intro n hsa
      have := hare n
      rw [← hsa] at this
      linarith
    have hsum1 : Summable fun n => (s ^ (2 : ℕ) + κ * s) * (m n / (s - a n) - Q n s) :=
      (hML s).mul_left _
    have hleft : (s ^ (2 : ℕ) + κ * s) * (∑' n : ℕ, (m n / (s - a n) - Q n s))
        = ∑' n : ℕ, (K n s + Ent n s) := by
      rw [← tsum_mul_left]
      exact tsum_congr fun n => hid n s (hne n)
    have hdiff : (∑' n : ℕ, (K n s + Ent n s)) - ∑' n : ℕ, (Ent n s + hker n s)
        = ∑' n : ℕ, (K n s - hker n s) := by
      rw [← (hsumKE s).tsum_sub (hsumg s)]
      exact tsum_congr fun n => by ring
    rw [hleft, hdiff]
    have hbound : ∀ n : ℕ, ‖K n s - hker n s‖ ≤ ε' * (1 / 2 : ℝ) ^ n := fun n =>
      hkerE n s hs
    have hgeom : Summable fun n : ℕ => ε' * (1 / 2 : ℝ) ^ n :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left ε'
    calc ‖∑' n : ℕ, (K n s - hker n s)‖
        ≤ ∑' n : ℕ, ‖K n s - hker n s‖ := norm_tsum_le_tsum_norm ((hsumK s).norm)
      _ ≤ ∑' n : ℕ, ε' * (1 / 2 : ℝ) ^ n := by
          exact Summable.tsum_le_tsum hbound (hsumK s).norm hgeom
      _ = ε' * 2 := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          norm_num
      _ ≤ ε := by rw [hε'def]; linarith

end GaloisForLFunctions.HTGeometry

end
