import GaloisForLFunctions.HTGeometry.CoverSchwarz
import GaloisForLFunctions.HTGeometry.SelfImprovingBound

/-!
# Periodicity turns a Schwarz gain into vanishing

The step where compactness is load-bearing.  A periodic function is bounded on the whole space by
its bound on one fundamental domain, so the Schwarz estimate on a cover of that domain improves
*every* bound by the fixed factor `θ = (r/R)^N/(1−r/R)`.  When `θ < 1` the maximum on the compact
fundamental domain satisfies `M ≤ θ·M`, so the function vanishes identically.

Without periodicity the improvement is unavailable and the argument is false: the same counting
would otherwise make `z` and `exp z` algebraically dependent on `ℂ`.

* **`eqOn_zero_of_periodic_cover`**.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **A periodic function with enough jet vanishing on a cover of a fundamental domain
vanishes.** -/
theorem eqOn_zero_of_periodic_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E → ℂ} (hF : ContDiff ℂ (⊤ : ℕ∞) F)
    {P : AddSubgroup E} (hper : ∀ p ∈ P, ∀ z : E, F (z + p) = F z)
    {K : Set E} (hKcomp : IsCompact K) (hKne : K.Nonempty)
    (hfund : ∀ z : E, ∃ p ∈ P, z - p ∈ K)
    {ι : Type*} (c : ι → E) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R) (hR : 0 < R)
    {N : ℕ}
    (hvan : ∀ i, ∀ k, k < N → iteratedFDeriv ℂ k F (c i) = 0)
    (hcov : ∀ z ∈ K, ∃ i, ‖z - c i‖ ≤ r)
    (hθ : (r / R) ^ N / (1 - r / R) < 1) :
    ∀ z, F z = 0 := by
  have hcont : Continuous F := hF.continuous
  -- every value is a value on the fundamental domain
  have hglob : ∀ z : E, ∃ z' ∈ K, F z = F z' := by
    intro z
    obtain ⟨p, hp, hmem⟩ := hfund z
    refine ⟨z - p, hmem, ?_⟩
    have := hper p hp (z - p)
    rw [sub_add_cancel] at this
    exact this
  -- the vanishing on the fundamental domain
  have hzeroK : ∀ z ∈ K, F z = 0 := by
    refine eqOn_zero_of_le_mul_bound hKcomp hKne
      (hcont.norm.continuousOn) hθ ?_
    intro M hM z hzK
    have hMglob : ∀ w : E, ‖F w‖ ≤ M := by
      intro w
      obtain ⟨w', hw'K, hw'⟩ := hglob w
      rw [hw']
      exact hM w' hw'K
    have hbd : ∀ i, ∀ w : E, ‖w‖ ≤ R → ‖F (c i + w)‖ ≤ M := fun i w _ => hMglob _
    have hmain := norm_le_of_cover_schwarz hF c hr hrR hR hbd hvan hcov z hzK
    calc ‖F z‖ ≤ M * (r / R) ^ N / (1 - r / R) := hmain
      _ = (r / R) ^ N / (1 - r / R) * M := by ring
  intro z
  obtain ⟨z', hz'K, hz'⟩ := hglob z
  rw [hz']
  exact hzeroK z' hz'K

end GaloisForLFunctions.HTGeometry
