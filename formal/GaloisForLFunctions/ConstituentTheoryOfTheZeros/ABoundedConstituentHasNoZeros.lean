import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PrimeContractionOfBoundedDirichletSeries
import GaloisForLFunctions.ConstituentTheoryOfTheZeros.PureDivisorsAreConstantInADisc
import GaloisForLFunctions.InfiniteRankPurityTheory.AFactorWithADirichletSeriesIsPure

/-!
# A bounded Dirichlet constituent has no zeros

A bounded pure Dirichlet series has the same zero set as a projection onto
finitely many primes. Continuity of its prime-torus lift gives zero-free disc
anchors on both sides of the pure line. Simultaneous contraction then preserves
the zero set. The finite-prime constituent obstruction excludes every zero
shared with the completed zeta function.
-/

open Complex Filter Topology Set Metric
open _root_.RHTower

noncomputable section
namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

/-- Every bounded pure Dirichlet series has a finite-prime representative of its
zero set, retaining any prescribed finite set of prime coordinates. -/
theorem exists_smooth_zero_set_representative_of_bounded_pure
    {a : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ c M : ℝ} {n : ℕ}
    (hxu : x < u₀) (hxc : x < c) (hsum : LSeriesSummable a (u₀ : ℂ))
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hM : ∀ s, x < s.re → ‖F s‖ ≤ M)
    (hFL : ∀ s, u₀ < s.re → F s = LSeries a s) (hn : a (n + 1) ≠ 0)
    (hpure : ∀ s, x < s.re → F s = 0 → s.re = c) (N₀ : ℕ) :
    ∃ N ≥ N₀, ∃ K : ℂ → ℂ,
      DifferentiableOn ℂ K {s : ℂ | x < s.re} ∧
      (∀ s, x < s.re → ‖K s‖ ≤ M) ∧
      (∀ s, u₀ < s.re → K s = LSeries (fun m => if m ∈ Nat.smoothNumbers N then a m else 0) s) ∧
      (∀ s, x < s.re → (K s = 0 ↔ F s = 0)) := by
  obtain ⟨G, hG, hGM, hGL, hGp, hGc, hG1⟩ :=
    exists_bounded_pure_primeTorus_lift hxu hsum hF hM hFL hn hpure
  let α : ℂ := (((x + c) / 2 : ℝ) : ℂ)
  let β : ℂ := ((c + 1 : ℝ) : ℂ)
  have hαx : x < α.re := by dsimp only [α]; simp only [ofReal_re]; linarith
  have hαc : α.re < c := by dsimp only [α]; simp only [ofReal_re]; linarith
  have hβc : c < β.re := by dsimp only [β]; simp only [ofReal_re]; linarith
  have hβx : x < β.re := hxc.trans hβc
  have hα0 : F α ≠ 0 := fun hz => (ne_of_lt hαc) (hpure α hαx hz)
  have hβ0 : F β ≠ 0 := fun hz => (ne_of_gt hβc) (hpure β hβx hz)
  have heval (s : ℂ) (hs : x < s.re) : Continuous (fun ω => G ω s) := by
    rw [← continuousOn_univ]
    exact hGc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun ω _ => ⟨mem_univ ω, hs⟩)
  obtain ⟨A, hA, hAc⟩ := exists_prime_cutoff_of_continuousAt (heval α hαx).continuousAt
    (half_pos (norm_pos_iff.mpr hα0)) N₀
  obtain ⟨B, hB, hBc⟩ := exists_prime_cutoff_of_continuousAt (heval β hβx).continuousAt
    (half_pos (norm_pos_iff.mpr hβ0)) N₀
  let N := max A B
  obtain ⟨H, hHc, hHs, hHw, hHM, hHL, hHcircle⟩ :=
    exists_primeCutoff_family hsum hG hGM hGL hGc N
  have hU : IsOpen {s : ℂ | x < s.re} := isOpen_lt continuous_const continuous_re
  have hHa (s : ℂ) (hs : x < s.re) : AnalyticOnNhd ℂ (H s) (ball 0 1) :=
    (hHw s hs).analyticOnNhd isOpen_ball
  have hHas (w : ℂ) (hw : w ∈ closedBall (0 : ℂ) 1) :
      AnalyticOnNhd ℂ (fun s => H s w) {s : ℂ | x < s.re} :=
    (hHs w hw).analyticOnNhd hU
  have hHsc (s : ℂ) (hs : x < s.re) : ContinuousOn (H s) (closedBall 0 1) :=
    hHc.comp (continuous_const.prodMk continuous_id).continuousOn (fun w hw => ⟨hs, hw⟩)
  have hleft : ∀ w ∈ ball (0 : ℂ) 1, H α w ≠ 0 := by
    intro w hw
    apply unitDisc_ne_zero_of_boundary_close (hHa α hαx) (hHsc α hαx)
      (b := F α) (r := ‖F α‖ / 2) (half_lt_self (norm_pos_iff.mpr hα0))
      (hw := ball_subset_closedBall hw)
    intro z hz
    rw [hHcircle α ⟨z, hz⟩]
    have hh := hAc (retainedPrimePhase N ⟨z, hz⟩) (fun p hp =>
      if_pos (lt_of_lt_of_le hp (le_max_left A B)))
    rw [hG1 hαx] at hh
    exact hh.le
  have hright : ∀ w ∈ ball (0 : ℂ) 1, H β w ≠ 0 := by
    intro w hw
    apply unitDisc_ne_zero_of_boundary_close (hHa β hβx) (hHsc β hβx)
      (b := F β) (r := ‖F β‖ / 2) (half_lt_self (norm_pos_iff.mpr hβ0))
      (hw := ball_subset_closedBall hw)
    intro z hz
    rw [hHcircle β ⟨z, hz⟩]
    have hh := hBc (retainedPrimePhase N ⟨z, hz⟩) (fun p hp =>
      if_pos (lt_of_lt_of_le hp (le_max_right A B)))
    rw [hG1 hβx] at hh
    exact hh.le
  have hbd : ∀ s, x < s.re → ∀ w ∈ sphere (0 : ℂ) 1, H s w = 0 → s.re = c := by
    intro s hs w hw hz
    rw [hHcircle s ⟨w, hw⟩] at hz
    exact hGp (retainedPrimePhase N ⟨w, hw⟩) s hs hz
  have hzero : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := by simp only [mem_closedBall, dist_self]; norm_num
  refine ⟨N, hA.trans (le_max_left A B), (fun s => H s 0), hHs 0 hzero,
    (fun s hs => hHM s hs 0 hzero), ?_, ?_⟩
  · intro s hs
    exact (hHL s hs 0 hzero).trans (primeCutoffSeries_zero a N s)
  · intro s hs
    have h := unitDisc_zero_iff_center_of_boundary_and_anchors hxc hHc hHa hHas hbd
      hαx hαc hβc hleft hright hs
      (show (1 : ℂ) ∈ closedBall (0 : ℂ) 1 by simp only [mem_closedBall, dist_zero_right, norm_one, le_refl])
    have h1 : H s 1 = F s := by
      have hc := hHcircle s (1 : Circle)
      change H s 1 = G (retainedPrimePhase N (1 : Circle)) s at hc
      rw [retainedPrimePhase_one] at hc
      exact hc.trans (hG1 hs)
    rw [h1] at h
    exact h.symm

/-- A nonzero bounded Dirichlet series whose zeros are zeros of `ξ` has no zero
in its half-plane of bounded holomorphic continuation. -/
theorem bounded_dirichlet_constituent_ne_zero
    {a : ℕ → ℂ} {F : ℂ → ℂ} {x u₀ M : ℝ} {n : ℕ}
    (hsum : LSeriesSummable a (u₀ : ℂ))
    (hF : DifferentiableOn ℂ F {s : ℂ | x < s.re})
    (hM : ∀ s, x < s.re → ‖F s‖ ≤ M)
    (hFL : ∀ s, u₀ < s.re → F s = LSeries a s) (hn : a (n + 1) ≠ 0)
    (hzero : ∀ s, x < s.re → F s = 0 → xi s = 0)
    {s : ℂ} (hs : x < s.re) : F s ≠ 0 := by
  intro hFs
  have hFne : ∃ z : ℂ, x < z.re ∧ F z ≠ 0 := by
    apply exists_ne_zero_of_primePhaseTwist_coefficient hsum 1 hF (hn := hn)
    intro z hz
    simpa only [primePhaseTwist_one, mul_one] using hFL z hz
  have hpure : ∀ z, x < z.re → F z = 0 → z.re = (1 : ℝ) / 2 := by
    intro z hz hz0
    exact InfiniteRankPurityTheory.re_eq_half_of_zeros_subset_xi hsum hF hM hFL hFne hzero hz hz0
  have hxc : x < (1 : ℝ) / 2 := by rw [← hpure s hs hFs]; exact hs
  let u : ℝ := max x u₀ + 1
  have hxu : x < u := by dsimp only [u]; linarith [le_max_left x u₀]
  have hu₀ : u₀ < u := by dsimp only [u]; linarith [le_max_right x u₀]
  have hsumu : LSeriesSummable a (u : ℂ) :=
    hsum.of_re_le_re (by simpa only [ofReal_re] using hu₀.le)
  have hFLu : ∀ z, u < z.re → F z = LSeries a z := fun z hz => hFL z (hu₀.trans hz)
  obtain ⟨N, hN, K, hK, hKM, hKL, hKzero⟩ :=
    exists_smooth_zero_set_representative_of_bounded_pure hxu hxc hsumu hF hM hFLu hn hpure (n + 2)
  let b : ℕ → ℂ := fun m => if m ∈ Nat.smoothNumbers N then a m else 0
  have hb : b = fun m => a m * primeCutoffMultiplier N 0 m := by
    funext m
    rw [primeCutoffMultiplier_zero]
    dsimp only [b]
    split_ifs <;> simp only [mul_one, mul_zero]
  have hbsum : LSeriesSummable b (u : ℂ) := by
    rw [hb]
    exact lSeriesSummable_primeCutoffMultiplier N hsumu (by simp only [norm_zero, zero_le_one])
  have hsupport : ∀ m, b m ≠ 0 → m ∈ Nat.smoothNumbers N := by
    intro m hm
    by_contra h
    exact hm (if_neg h)
  have hnsm : n + 1 ∈ Nat.smoothNumbers N := by
    apply Nat.mem_smoothNumbers_iff_forall_le.mpr
    refine ⟨Nat.succ_ne_zero n, ?_⟩
    intro p hp _ _
    omega
  have hbn : b (n + 1) ≠ 0 := by simpa only [b, if_pos hnsm] using hn
  have hKxi : ∀ z, x < z.re → K z = 0 → xi z = 0 :=
    fun z hz hz0 => hzero z hz ((hKzero z hz).mp hz0)
  have hKn := ne_zero_of_bounded_of_smooth_of_zeros_subset_xi
    hbsum hK hKM hKL hsupport hbn hKxi hs
  exact hKn ((hKzero s hs).mpr hFs)

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
