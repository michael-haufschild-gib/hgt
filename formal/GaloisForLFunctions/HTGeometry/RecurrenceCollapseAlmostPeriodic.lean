import GaloisForLFunctions.HTGeometry.BohrReturnSequence
import GaloisForLFunctions.HTGeometry.GammaFiniteProjectiveLaw

/-!
# The recurrence collapse with return times supplied by almost periodicity

The collapse of a finite differential relation to an autonomous one needs a sequence of vertical
translations along which every monomial returns to its value and the normalized coefficients
converge.  The second is a genuine limit as the imaginary part grows, so it holds along any sequence
tending to `+∞`; the first is exactly the common return sequence of a finite family of almost
periodic functions.  So the diagonal choice of return times is no longer a hypothesis.
-/

open Filter Topology

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **The recurrence collapse with the return times supplied by almost periodicity.** -/
theorem recurrence_collapse_of_bohr_return {n : ℕ} (F M : Fin n → ℂ → ℂ) (β : Fin n) (s₀ : ℂ)
    (d : Fin n → ℂ)
    (hrel : ∀ s : ℂ, ∑ α, F α s * M α s = 0)
    (hMcont : ∀ α, Continuous fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
    (hMap : ∀ α, IsBohrAlmostPeriodic fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I))
    (hFβ : ∀ᶠ t : ℝ in atTop, F β (s₀ + (t : ℂ) * Complex.I) ≠ 0)
    (hcoeff : ∀ α, Tendsto
      (fun t : ℝ => F α (s₀ + (t : ℂ) * Complex.I) / F β (s₀ + (t : ℂ) * Complex.I))
      atTop (nhds (d α))) :
    (∑ α, d α * M α s₀ = 0) ∧ d β = 1 := by
  classical
  obtain ⟨T, hT, hret⟩ := exists_bohr_return_sequence_tendsto
    (g := fun α => fun t : ℝ => M α (s₀ + (t : ℂ) * Complex.I)) hMcont hMap
  have hmon : ∀ α ∈ (Finset.univ : Finset (Fin n)), Tendsto
      (fun l => M α (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds (M α s₀)) := by
    intro α _
    have h := hret α 0
    have hzero : M α (s₀ + ((0 : ℝ) : ℂ) * Complex.I) = M α s₀ := by
      norm_num
    rw [hzero] at h
    refine h.congr fun l => ?_
    norm_num
  have hFβT : ∀ᶠ l in atTop, F β (s₀ + (T l : ℂ) * Complex.I) ≠ 0 := hT.eventually hFβ
  have hcoeffT : ∀ α ∈ (Finset.univ : Finset (Fin n)), Tendsto
      (fun l => F α (s₀ + (T l : ℂ) * Complex.I) / F β (s₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (d α)) := fun α _ => (hcoeff α).comp hT
  exact recurrence_collapse_to_autonomous_eventually Finset.univ F M β (Finset.mem_univ β) s₀ T d
    hrel hFβT hcoeffT hmon

end GaloisForLFunctions
