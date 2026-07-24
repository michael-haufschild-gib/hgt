import GaloisForLFunctions.HTGeometry.SampledSmallInterpolation
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Localized sampled-smallness: interval smoothness suffices

The sampled-smallness estimate `abs_le_of_sampled_small` requires global
smoothness only because its iterated-Rolle engine does; a smooth bump
supported inside the smoothness region converts interval smoothness into
the global hypothesis without changing the function — or any of its
derivatives — on the window.  Hence the estimate holds for functions
smooth merely on an open interval around the unit window, which is what
half-plane-analytic transforms provide.
-/

noncomputable section

namespace HTGeometry

open Set Metric

/-- **Localized sampled-smallness estimate**: smoothness on an open
interval `(c, d)` around the unit window suffices. -/
theorem abs_le_of_sampled_small_of_contDiffOn
    {N : ℕ} {f : ℝ → ℝ} {a c d : ℝ} (hca : c < a) (had : a + 1 < d)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Set.Ioo c d))
    {s : Finset ℝ} (hcard : s.card = N + 1)
    (hsub : ↑s ⊆ Set.Icc a (a + 1))
    {η : ℝ} (hη : 0 < η)
    (hsep : ∀ t ∈ s, ∀ u ∈ s, t ≠ u → η ≤ |t - u|)
    {M : ℝ} (hM : ∀ t ∈ Set.Icc a (a + 1), |iteratedDeriv (N + 1) f t| ≤ M)
    {ε₀ : ℝ} (hε₀ : ∀ t ∈ s, |f t| ≤ ε₀)
    {x : ℝ} (hx : x ∈ Set.Icc a (a + 1)) :
    |f x| ≤ (N + 1) * (2 ^ N / (η ^ N * N.factorial)) * ε₀
      + M / (N + 1).factorial := by
  set ε : ℝ := min (a - c) (d - (a + 1)) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hεc : ε ≤ a - c := min_le_left _ _
  have hεd : ε ≤ d - (a + 1) := min_le_right _ _
  -- the bump: `≡ 1` on `[a − ε/4, a+1+ε/4]`, supported inside `(c, d)`
  set bump : ContDiffBump (a + 1 / 2) :=
    ⟨1 / 2 + ε / 2, 1 / 2 + 3 * ε / 4, by linarith, by linarith⟩
    with hbumpdef
  have hrIn : bump.rIn = 1 / 2 + ε / 2 := rfl
  have hrOut : bump.rOut = 1 / 2 + 3 * ε / 4 := rfl
  set g : ℝ → ℝ := fun t => bump t * f t with hgdef
  -- global smoothness of the bumped function
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := by
    rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge (dist t (a + 1 / 2)) (1 / 2 + ε) with hin | hout
    · -- within the smoothness interval
      have htcd : t ∈ Set.Ioo c d := by
        rw [Real.dist_eq, abs_lt] at hin
        constructor <;> linarith
      exact (bump.contDiff.contDiffAt).mul
        (hf.contDiffAt (Ioo_mem_nhds htcd.1 htcd.2))
    · -- strictly outside the bump support: locally identically zero
      have hzero : ∀ᶠ u in nhds t, g u = 0 := by
        have hopen : {u : ℝ | 1 / 2 + 7 * ε / 8 < dist u (a + 1 / 2)}
            ∈ nhds t := by
          have h1 : IsOpen {u : ℝ | 1 / 2 + 7 * ε / 8
              < dist u (a + 1 / 2)} :=
            isOpen_lt continuous_const (continuous_id.dist continuous_const)
          apply h1.mem_nhds
          rw [Set.mem_setOf_eq]
          linarith
        filter_upwards [hopen] with u hu
        rw [hgdef]
        simp only
        rw [bump.zero_of_le_dist
          (by rw [hrOut]; linarith : bump.rOut ≤ dist u (a + 1 / 2)),
          zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  -- the bumped function agrees with `f` near the window
  have hone : ∀ u ∈ Set.Icc (a - ε / 4) (a + 1 + ε / 4), g u = f u := by
    intro u hu
    rw [Set.mem_Icc] at hu
    have h1 : u ∈ closedBall (a + 1 / 2) bump.rIn := by
      rw [mem_closedBall, hrIn, Real.dist_eq, abs_le]
      constructor <;> linarith
    rw [hgdef]
    simp only
    rw [bump.one_of_mem_closedBall h1, one_mul]
  have hnhds : ∀ t ∈ Set.Icc a (a + 1), g =ᶠ[nhds t] f := by
    intro t ht
    rw [Set.mem_Icc] at ht
    have hmem : Set.Ioo (a - ε / 4) (a + 1 + ε / 4) ∈ nhds t :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [hmem] with u hu
    exact hone u ⟨le_of_lt hu.1, le_of_lt hu.2⟩
  -- transport the estimate through the bump
  have hM' : ∀ t ∈ Set.Icc a (a + 1),
      |iteratedDeriv (N + 1) g t| ≤ M := by
    intro t ht
    rw [Filter.EventuallyEq.iteratedDeriv_eq (N + 1) (hnhds t ht)]
    exact hM t ht
  have hε₀' : ∀ t ∈ s, |g t| ≤ ε₀ := by
    intro t ht
    have h1 := hsub ht
    rw [Set.mem_Icc] at h1
    rw [hone t ⟨by linarith, by linarith⟩]
    exact hε₀ t ht
  have hmain := abs_le_of_sampled_small hg hcard hsub hη hsep hM' hε₀' hx
  rw [Set.mem_Icc] at hx
  rwa [hone x ⟨by linarith [hx.1], by linarith [hx.2]⟩] at hmain

end HTGeometry
