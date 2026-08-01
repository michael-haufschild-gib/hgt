import GaloisForLFunctions.HTGeometry.GammaFieldAbstractCollapse
import GaloisForLFunctions.HTGeometry.FinitePhaseLawFromRatios

/-!
# The finite phase law from a relation valid only far up the line

The collapse argument samples the relation along a Bohr return sequence, which tends to `+∞`, so the
relation is only ever used far up the vertical line.  Weakening the hypothesis from "the relation
holds at every point of `ℂ`" to "the relation holds eventually on the line" therefore costs nothing —
and it is the form in which a relation between germs at the upper end arrives.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Collapse from a relation sampled along the return sequence.** -/
theorem recurrence_collapse_to_autonomous_of_eventual {ι : Type*} (E : Finset ι)
    (F M : ι → ℂ → ℂ) (β : ι) (hβ : β ∈ E) (s₀ : ℂ) (T : ℕ → ℝ) (d : ι → ℂ)
    (hrel : ∀ᶠ l in atTop, ∑ α ∈ E, F α (s₀ + (T l : ℂ) * Complex.I)
      * M α (s₀ + (T l : ℂ) * Complex.I) = 0)
    (hFβ : ∀ᶠ l in atTop, F β (s₀ + (T l : ℂ) * Complex.I) ≠ 0)
    (hcoeff : ∀ α ∈ E, Tendsto
      (fun l => F α (s₀ + (T l : ℂ) * Complex.I) / F β (s₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (d α)))
    (hmon : ∀ α ∈ E, Tendsto
      (fun l => M α (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds (M α s₀))) :
    (∑ α ∈ E, d α * M α s₀ = 0) ∧ d β = 1 := by
  refine ⟨?_, ?_⟩
  · have hlim : Tendsto (fun l =>
        ∑ α ∈ E, (F α (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) *
          M α (s₀ + (T l : ℂ) * Complex.I))
        atTop (nhds (∑ α ∈ E, d α * M α s₀)) := by
      apply tendsto_finsetSum
      intro α hα
      exact (hcoeff α hα).mul (hmon α hα)
    have hzeroLim : Tendsto (fun l =>
        ∑ α ∈ E, (F α (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) *
          M α (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hFβ, hrel] with l hFβl hrell
      symm
      rw [show (∑ α ∈ E, (F α (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) *
          M α (s₀ + (T l : ℂ) * Complex.I)) =
        (∑ α ∈ E, F α (s₀ + (T l : ℂ) * Complex.I) *
          M α (s₀ + (T l : ℂ) * Complex.I)) /
          F β (s₀ + (T l : ℂ) * Complex.I) by
            rw [Finset.sum_div]
            exact Finset.sum_congr rfl (fun α _ => by ring)]
      rw [hrell, zero_div]
    exact tendsto_nhds_unique hlim hzeroLim
  · have hlim := hcoeff β hβ
    have hOne : Tendsto
        (fun l => F β (s₀ + (T l : ℂ) * Complex.I) /
          F β (s₀ + (T l : ℂ) * Complex.I)) atTop (nhds 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hFβ] with l hFβl
      exact (div_self hFβl).symm
    exact tendsto_nhds_unique hlim hOne

/-- **Collapse from a relation valid far up the line.** -/
theorem recurrence_collapse_of_bohr_return_eventual {n : ℕ} (F M : Fin n → ℂ → ℂ) (β : Fin n)
    (s₀ : ℂ) (d : Fin n → ℂ)
    (hrel : ∀ᶠ t : ℝ in atTop, ∑ α, F α (s₀ + (t : ℂ) * Complex.I)
      * M α (s₀ + (t : ℂ) * Complex.I) = 0)
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
  exact recurrence_collapse_to_autonomous_of_eventual Finset.univ F M β (Finset.mem_univ β) s₀ T d
    (hT.eventually hrel) (hT.eventually hFβ)
    (fun α _ => (hcoeff α).comp hT) hmon

end GaloisForLFunctions
