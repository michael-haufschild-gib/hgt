import GaloisForLFunctions.Bottcher.DendriteBoundary
import GaloisForLFunctions.U0.U0NaturalBoundary

open Complex Metric Topology Set Filter U0NaturalBoundary

namespace Bottcher

/-- A frontier point of `K_c` belongs to `K_c`. -/
theorem mem_filledJulia_of_frontier {c z₀ : ℂ}
    (hz : z₀ ∈ frontier (filledJulia c)) : z₀ ∈ filledJulia c := by
  rw [(isClosed_filledJulia c).frontier_eq] at hz
  exact hz.1

/-- A frontier point of `K_c` is accumulated by the basin side. -/
theorem nhdsWithin_compl_filledJulia_neBot_of_frontier {c z₀ : ℂ}
    (hz : z₀ ∈ frontier (filledJulia c)) : (𝓝[(filledJulia c)ᶜ] z₀).NeBot := by
  have hz' : z₀ ∈ closure (filledJulia c)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hz
    exact hz.2
  exact mem_closure_iff_nhdsWithin_neBot.mp hz'

/-- **Dendrite `ContinuesAcross` obstruction from the Böttcher modulus.** If the filled Julia set has
empty interior, then any basin-side branch carrying the Böttcher modulus cannot analytically continue
across a frontier point. -/
theorem not_continuesAcross_of_emptyInterior_modulus {c z₀ : ℂ} {β : ℂ → ℂ}
    (hempty : interior (filledJulia c) = ∅)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z))
    (hfront : z₀ ∈ frontier (filledJulia c)) :
    ¬ ContinuesAcross β (filledJulia c)ᶜ z₀ := by
  intro hcont
  obtain ⟨g, hgAt, hgEq⟩ := hcont
  obtain ⟨ε₁, hε₁, hgan1⟩ := Metric.eventually_nhds_iff.mp hgAt.eventually_analyticAt
  obtain ⟨W, hWopen, hz₀W, hWsub⟩ := mem_nhdsWithin.mp hgEq
  obtain ⟨ε₂, hε₂, hWball⟩ := Metric.isOpen_iff.mp hWopen z₀ hz₀W
  set r := min ε₁ ε₂ with hrdef
  have hr : 0 < r := lt_min hε₁ hε₂
  have hr₁ : r ≤ ε₁ := min_le_left _ _
  have hr₂ : r ≤ ε₂ := min_le_right _ _
  have hgan : AnalyticOnNhd ℂ g (ball z₀ r) := by
    intro z hz
    exact hgan1 (lt_of_lt_of_le (mem_ball.mp hz) hr₁)
  have hzK : z₀ ∈ filledJulia c := mem_filledJulia_of_frontier hfront
  have hemptyBall : ball z₀ r ∩ interior (filledJulia c) = ∅ := by
    rw [hempty, inter_empty]
  have hmod : ∀ z ∈ ball z₀ r, z ∉ filledJulia c →
      ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hzball hzKc
    have hzW' : z ∈ W := hWball (Metric.ball_subset_ball hr₂ hzball)
    have hgz : g z = β z := hWsub ⟨hzW', hzKc⟩
    rw [hgz]
    exact hβmod z hzKc
  have hNeBot : (𝓝[(filledJulia c)ᶜ] z₀).NeBot :=
    nhdsWithin_compl_filledJulia_neBot_of_frontier hfront
  have hbasin : ∃ z ∈ ball z₀ r, z ∉ filledJulia c := by
    obtain ⟨z, hz1, hz2⟩ := hNeBot.nonempty_of_mem
      (inter_mem_nhdsWithin _ (ball_mem_nhds z₀ hr))
    exact ⟨z, hz2, hz1⟩
  exact no_continuation_dendrite hr hgan hzK hemptyBall hmod hbasin

/-- Empty-interior filled Julia sets give the natural-boundary predicate at every frontier point for any
basin branch carrying the Böttcher modulus. -/
theorem hnb_of_emptyInterior_modulus {c : ℂ} {β : ℂ → ℂ}
    (hempty : interior (filledJulia c) = ∅)
    (hβmod : ∀ z ∈ (filledJulia c)ᶜ, ‖β z‖ = Real.exp (greenFunctionDyn c z)) :
    ∀ z₀ ∈ frontier (filledJulia c), ¬ ContinuesAcross β (filledJulia c)ᶜ z₀ := by
  intro z₀ hfront
  exact not_continuesAcross_of_emptyInterior_modulus hempty hβmod hfront

end Bottcher
