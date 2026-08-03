import GaloisForLFunctions.HTGeometry.BarnesConeProduct

/-!
# The cone poles are punctured-thin

The poles of the Barnes cone product are the negatives of the nonzero cone periods, and only
finitely many cone periods lie in any bounded region.  Hence every point of the plane has a
punctured neighbourhood free of poles, and a statement proved for every argument off the poles
holds eventually on the punctured neighbourhood of every point.

That is the form a pointwise identity must take before it can be transported into the meromorphic
field.
-/

open Filter Set Topology Metric

namespace GaloisForLFunctions

noncomputable section

variable {ι : Type} [Fintype ι] [Nonempty ι]

/-- A finite set is avoided on the punctured neighbourhood of every point. -/
theorem eventually_nhdsNE_notMem_finite {F : Set ℂ} (hF : F.Finite) (z₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] z₀, w ∉ F := by
  have hFd : (F \ {z₀}).Finite := hF.sdiff
  have hclosed : IsClosed (F \ {z₀}) := hFd.isClosed
  have hmem : (F \ {z₀})ᶜ ∈ 𝓝 z₀ := hclosed.compl_mem_nhds (by simp)
  filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with w hw hne
  intro hwF
  exact hw ⟨hwF, hne⟩

/-- **The cone poles are punctured-thin.**  Every point of the plane has a punctured
neighbourhood on which no nonzero cone period cancels the argument. -/
theorem eventually_nhdsNE_conePeriod_add_ne_zero (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im) (z₀ : ℂ) :
    ∀ᶠ w in 𝓝[≠] z₀, ∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + w ≠ 0 := by
  classical
  set R : ℝ := ‖z₀‖ + 1 with hR
  have hRpos : (0 : ℝ) < R := by
    have : (0 : ℝ) ≤ ‖z₀‖ := norm_nonneg _
    rw [hR]
    linarith
  set S : Set (ι → ℕ) := {n : ι → ℕ | ¬ (2 * R ≤ ‖conePeriod ω n‖)} with hSdef
  have hS : S.Finite := finite_conePeriod_lt ω hω R
  set F : Set ℂ := (fun n : ι → ℕ => -conePeriod ω n) '' S with hFdef
  have hF : F.Finite := hS.image _
  filter_upwards [eventually_nhdsNE_notMem_finite hF z₀,
    nhdsWithin_le_nhds (Metric.ball_mem_nhds z₀ one_pos)] with w hw hball
  intro n _ hcon
  have hwval : w = -conePeriod ω n := by linear_combination hcon
  have h1 : ‖w - z₀‖ < 1 := by
    rw [← dist_eq_norm]
    exact Metric.mem_ball.mp hball
  have h2 : ‖w‖ ≤ ‖z₀‖ + 1 := by
    have hsplit : w = (w - z₀) + z₀ := by ring
    calc ‖w‖ = ‖(w - z₀) + z₀‖ := by rw [← hsplit]
      _ ≤ ‖w - z₀‖ + ‖z₀‖ := norm_add_le _ _
      _ ≤ ‖z₀‖ + 1 := by linarith
  have hnorm : ‖conePeriod ω n‖ < 2 * R := by
    rw [hwval, norm_neg] at h2
    rw [hR]
    linarith
  exact hw ⟨n, by rw [hSdef]; exact not_le.mpr hnorm, hwval.symm⟩

/-- A pointwise statement valid off the cone poles holds eventually on the punctured neighbourhood
of every point. -/
theorem eventuallyEq_nhdsNE_of_forall_off_conePoles (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    {φ ψ : ℂ → ℂ}
    (h : ∀ w : ℂ, (∀ n : ι → ℕ, n ≠ 0 → conePeriod ω n + w ≠ 0) → φ w = ψ w) (z₀ : ℂ) :
    φ =ᶠ[𝓝[≠] z₀] ψ := by
  filter_upwards [eventually_nhdsNE_conePeriod_add_ne_zero ω hω z₀] with w hw
  exact h w hw

end

end GaloisForLFunctions
