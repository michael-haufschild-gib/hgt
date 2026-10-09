import GaloisForLFunctions.HTGeometry.LaguerrePolyaClass

/-!
# The Laguerre–Pólya class is closed under locally uniform limits

`LaguerrePolya.of_tendstoLocallyUniformly`: a locally uniform limit of Laguerre–Pólya functions is
Laguerre–Pólya. Choose for the `m`-th function a real-rooted polynomial within `1/(m+1)` of it on
the closed ball of radius `m`; the diagonal sequence converges locally uniformly to the limit.

`LaguerrePolya.const_mul`: real multiples of Laguerre–Pólya functions are Laguerre–Pólya.
-/

open Polynomial Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Closure under locally uniform limits.** -/
theorem LaguerrePolya.of_tendstoLocallyUniformly {f : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hf : ∀ m, LaguerrePolya (f m)) (hconv : TendstoLocallyUniformly f F atTop) :
    LaguerrePolya F := by
  choose p hsplit hp using hf
  -- the diagonal index: within `1/(m+1)` of `f m` on the ball of radius `m`
  have hk : ∀ m : ℕ, ∃ k : ℕ, ∀ z ∈ closedBall (0 : ℂ) m,
      dist (f m z) (polyEvalC (p m k) z) < 1 / ((m : ℝ) + 1) := by
    intro m
    have hu := (tendstoLocallyUniformly_iff_forall_isCompact.mp (hp m)) _
      (isCompact_closedBall (0 : ℂ) m)
    rw [Metric.tendstoUniformlyOn_iff] at hu
    exact (hu _ (by positivity)).exists
  choose k hk using hk
  refine ⟨fun m => p m (k m), fun m => hsplit m (k m), ?_⟩
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  have hFu := (tendstoLocallyUniformly_iff_forall_isCompact.mp hconv) K hK
  rw [Metric.tendstoUniformlyOn_iff] at hFu
  have h1 := hFu (ε / 2) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (max R (2 / ε))
  have h2 : ∀ᶠ m : ℕ in atTop, N ≤ m := eventually_ge_atTop N
  filter_upwards [h1, h2] with m hm1 hm2 z hz
  have hmR : R ≤ m := by
    have : (N : ℝ) ≤ m := by exact_mod_cast hm2
    linarith [le_max_left R (2 / ε)]
  have hzm : z ∈ closedBall (0 : ℂ) m := closedBall_subset_closedBall hmR (hR hz)
  have hd := hk m z hzm
  have hsmall : 1 / ((m : ℝ) + 1) < ε / 2 := by
    have hm : (2 / ε : ℝ) < m + 1 := by
      have : (N : ℝ) ≤ m := by exact_mod_cast hm2
      linarith [le_max_right R (2 / ε)]
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hm
    linarith
  calc dist (F z) (polyEvalC (p m (k m)) z)
      ≤ dist (F z) (f m z) + dist (f m z) (polyEvalC (p m (k m)) z) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add (hm1 z hz) (hd.trans hsmall)
    _ = ε := by ring

/-- **Real multiples.** -/
theorem LaguerrePolya.const_mul {F : ℂ → ℂ} (hF : LaguerrePolya F) (a : ℝ) :
    LaguerrePolya fun z => (a : ℂ) * F z := by
  obtain ⟨p, hsplit, hconv⟩ := hF
  refine ⟨fun m => C a * p m, fun m => (Splits.C a).mul (hsplit m), ?_⟩
  have hfun : (fun m => polyEvalC (C a * p m)) = fun m z => (a : ℂ) * polyEvalC (p m) z := by
    funext m z
    simp [polyEvalC]
  rw [hfun]
  have hU : UniformContinuous fun w : ℂ => (a : ℂ) * w :=
    (uniformContinuous_const_smul (a : ℂ))
  exact hU.comp_tendstoLocallyUniformly hconv

end

end GaloisForLFunctions.HTGeometry
