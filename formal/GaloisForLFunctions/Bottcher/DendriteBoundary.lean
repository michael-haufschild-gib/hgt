/-
# Böttcher tower — the Green-modulus natural boundary (dendrite case)

Assembling the natural-boundary engine (`NaturalBoundary.no_unit_min_of_analytic`) with the Green's
function `G_c = greenFunctionDyn`: **no analytic continuation of `φ_c` across a Julia point can
preserve the Böttcher modulus `‖φ_c‖ = exp(G_c)`.**

The reason is sharp and uses only `G_c ≥ 0` everywhere (`greenFunctionDyn_nonneg`) and `G_c = 0` on
`K_c` (`greenFunctionDyn_eq_zero_iff`): a modulus-preserving continuation `g` would have
`‖g‖ = exp(G_c) ≥ 1` on the whole ball, `‖g z₀‖ = exp(0) = 1` at the Julia point, yet `‖g‖ > 1` on the
basin side — exactly the configuration the minimum principle forbids. For an **empty-interior
(dendrite) Julia set** every continuation is forced to preserve the modulus (the basin is dense, and
`G_c` is continuous by `GreenContinuity`), so this is the full natural boundary there.

New file (hRigid connected lane); consumes `NaturalBoundary` + `GreenContinuity`.
-/
import GaloisForLFunctions.Bottcher.NaturalBoundary
import GaloisForLFunctions.Bottcher.GreenContinuity

open Complex Metric Topology Set Filter

namespace Bottcher

/-- **Green-modulus natural boundary.** No nonvanishing analytic `g` on a ball about a filled-Julia
point `z₀` can satisfy `‖g‖ = exp(G_c)` throughout while the ball meets the basin. Instantiated with
`g` = a hypothetical continuation of `φ_c` across `z₀ ∈ J_c` (which has `‖φ_c‖ = exp(G_c)` on the
basin, extended by continuity), this is the Julia natural boundary for any modulus-preserving
continuation — in particular the whole dendrite case. -/
theorem no_green_modulus_continuation {c z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r))
    (hz₀ : z₀ ∈ filledJulia c)
    (hmod : ∀ z ∈ ball z₀ r, ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hbasin : ∃ z ∈ ball z₀ r, z ∉ filledJulia c) :
    False := by
  refine no_unit_min_of_analytic hr hgan (fun z hz => ?_) (fun z hz => ?_) ?_ ?_
  · -- g ≠ 0
    refine norm_pos_iff.mp ?_
    rw [hmod z hz]; exact Real.exp_pos _
  · -- ‖g‖ ≥ 1  (since G_c ≥ 0)
    rw [hmod z hz]
    exact Real.one_le_exp (greenFunctionDyn_nonneg c z)
  · -- ‖g z₀‖ = 1  (since G_c z₀ = 0 on K_c)
    rw [hmod z₀ (mem_ball_self hr), (greenFunctionDyn_eq_zero_iff c z₀).mpr hz₀, Real.exp_zero]
  · -- ‖g‖ > 1 somewhere (basin point: G_c > 0)
    obtain ⟨z, hz, hzK⟩ := hbasin
    refine ⟨z, hz, ?_⟩
    have hgpos : 0 < greenFunctionDyn c z := by
      unfold greenFunctionDyn; rw [if_neg hzK]; exact greenLimit_pos_basin hzK
    rw [hmod z hz]
    exact Real.one_lt_exp_iff.mpr hgpos

/-- **Green-modulus natural boundary, dense form (uses Green continuity, D1).** It suffices that the
continuation preserves `‖φ_c‖ = exp(G_c)` only on the **basin part** of the ball, provided the basin
is dense there (empty-interior / dendrite condition). The modulus identity then extends to the whole
ball because both `‖g‖` and `exp(G_c)` are continuous (`continuous_greenFunctionDyn`), reducing to
`no_green_modulus_continuation`. This is the realistic dendrite natural boundary: a continuation only
sees the basin directly, yet is still ruled out. -/
theorem no_green_modulus_continuation_dense {c z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r)) (hz₀ : z₀ ∈ filledJulia c)
    (hdense : ball z₀ r ⊆ closure (ball z₀ r ∩ (filledJulia c)ᶜ))
    (hmod : ∀ z ∈ ball z₀ r, z ∉ filledJulia c → ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hbasin : ∃ z ∈ ball z₀ r, z ∉ filledJulia c) :
    False := by
  set s : Set ℂ := ball z₀ r ∩ (filledJulia c)ᶜ with hs
  have hsub : s ⊆ ball z₀ r := inter_subset_left
  have hcN : ContinuousOn (fun w => ‖g w‖) (ball z₀ r) := hgan.continuousOn.norm
  have hcE : ContinuousOn (fun w => Real.exp (greenFunctionDyn c w)) (ball z₀ r) :=
    (Real.continuous_exp.comp (continuous_greenFunctionDyn c)).continuousOn
  have hmod_all : ∀ z ∈ ball z₀ r, ‖g z‖ = Real.exp (greenFunctionDyn c z) := by
    intro z hz
    have hzcl : z ∈ closure s := hdense hz
    have hne : (𝓝[s] z).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hzcl
    have hf : Tendsto (fun w => ‖g w‖) (𝓝[s] z) (𝓝 (‖g z‖)) := (hcN z hz).mono hsub
    have hh0 : Tendsto (fun w => Real.exp (greenFunctionDyn c w)) (𝓝[s] z)
        (𝓝 (Real.exp (greenFunctionDyn c z))) := (hcE z hz).mono hsub
    have heqs : ∀ w ∈ s, Real.exp (greenFunctionDyn c w) = ‖g w‖ :=
      fun w hw => (hmod w hw.1 hw.2).symm
    have hh : Tendsto (fun w => ‖g w‖) (𝓝[s] z) (𝓝 (Real.exp (greenFunctionDyn c z))) :=
      hh0.congr' (Filter.eventuallyEq_of_mem self_mem_nhdsWithin heqs)
    exact tendsto_nhds_unique hf hh
  exact no_green_modulus_continuation hr hgan hz₀ hmod_all hbasin

/-- **General topology: complement of a nowhere-dense closed set is dense.** If an open `U` meets the
interior of `K` nowhere (`U ∩ interior K = ∅`), then `U ⊆ closure(U ∖ K)`. -/
theorem subset_closure_inter_compl {U K : Set ℂ} (hUo : IsOpen U)
    (hempty : U ∩ interior K = ∅) : U ⊆ closure (U ∩ Kᶜ) := by
  intro z hz
  rw [_root_.mem_closure_iff]
  intro V hVo hzV
  by_contra hcon
  rw [Set.not_nonempty_iff_eq_empty] at hcon
  have hsub : V ∩ U ⊆ K := by
    intro w hw
    by_contra hwK
    have hmem : w ∈ V ∩ (U ∩ Kᶜ) := ⟨hw.1, hw.2, hwK⟩
    rw [hcon] at hmem
    exact (Set.mem_empty_iff_false w).mp hmem
  have hint : V ∩ U ⊆ interior K := interior_maximal hsub (hVo.inter hUo)
  have hzmem : z ∈ U ∩ interior K := ⟨hz, hint ⟨hzV, hz⟩⟩
  rw [hempty] at hzmem
  exact hzmem

/-- **Density of the basin** under the empty-interior (dendrite) condition: if `K_c` has empty
interior in `ball z₀ r`, the basin `Ω_c` is dense there — discharging the density hypothesis of
`no_green_modulus_continuation_dense`. -/
theorem density_basin_of_empty_interior {c z₀ : ℂ} {r : ℝ}
    (hempty : ball z₀ r ∩ interior (filledJulia c) = ∅) :
    ball z₀ r ⊆ closure (ball z₀ r ∩ (filledJulia c)ᶜ) :=
  subset_closure_inter_compl isOpen_ball hempty

/-- **Dendrite natural boundary, fully assembled from the empty-interior condition.** For a Julia
point `z₀` where `K_c` has empty interior, no continuation of `φ_c` preserving the Böttcher modulus on
the basin can exist. The only remaining inputs are the empty-interior condition (the dendrite case
hypothesis) and the modulus identity `‖g‖ = exp(G_c)` on the basin part (supplied by `g` = the chain
branch `exp F`, `|exp F| = exp(G_c)`). -/
theorem no_continuation_dendrite {c z₀ : ℂ} {r : ℝ} {g : ℂ → ℂ}
    (hr : 0 < r) (hgan : AnalyticOnNhd ℂ g (ball z₀ r)) (hz₀ : z₀ ∈ filledJulia c)
    (hempty : ball z₀ r ∩ interior (filledJulia c) = ∅)
    (hmod : ∀ z ∈ ball z₀ r, z ∉ filledJulia c → ‖g z‖ = Real.exp (greenFunctionDyn c z))
    (hbasin : ∃ z ∈ ball z₀ r, z ∉ filledJulia c) :
    False :=
  no_green_modulus_continuation_dense hr hgan hz₀ (density_basin_of_empty_interior hempty) hmod hbasin

end Bottcher
