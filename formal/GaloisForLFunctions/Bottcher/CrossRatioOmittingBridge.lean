/-
# Cross-ratio omitting bridge for the Montel/periodic lane

This file connects the three-value lift mechanism to the frontier cross-ratio obstruction.  A family
of bounded disk lifts, pushed through a continuous sphere-valued target map, has a spherical locally
uniform subsequential limit.  For genuine iterate cross-ratios on a frontier ball, the obstruction in
`CrossRatioNormalBridge` forbids that limit.
-/
import GaloisForLFunctions.Bottcher.CrossRatioNormalBridge
import GaloisForLFunctions.Bottcher.ModularLambdaOmittingLift

open Complex Metric Set Filter Topology UpperHalfPlane
open scoped UpperHalfPlane

namespace Bottcher

noncomputable section

/-- Spherical normality from bounded omitting lifts.

This is the sphere-valued version of `normal_of_omitting_lift`: if each member of a family is the
push-forward of a bounded holomorphic disk-valued lift through a continuous sphere-valued map `μs`,
then a subsequence converges locally uniformly in the sphere model, with a continuous limit. -/
theorem spherical_normal_of_omitting_lift {f : ℕ → ℂ → ℂ} {c : ℂ} {R r : ℝ}
    {μs : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hr0 : 0 < r) (hrR : r < R / 2) (hμscont : Continuous μs)
    (hlift : ∀ n, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧
      (∀ z ∈ ball c R, ‖g z‖ ≤ 1) ∧ Set.EqOn (fun z => μs (g z))
        (fun z => stereo (f n z)) (ball c R)) :
    ∃ (φ : ℕ → ℕ) (G : ℂ → EuclideanSpace ℝ (Fin 3)), StrictMono φ ∧
      ContinuousOn G (closedBall c r) ∧
      TendstoUniformlyOn (fun k z => stereo (f (φ k) z)) G atTop (closedBall c r) := by
  choose g hg_diff hg_bd hg_eq using hlift
  obtain ⟨φ, gl, hφ, hgconv, -⟩ :=
    montel_subseq hr0 hrR hg_diff (fun n z hz => hg_bd n z hz)
  have hsubR : closedBall c r ⊆ ball c R := closedBall_subset_ball (by linarith)
  have hgk_mem : ∀ k (z : ℂ), z ∈ closedBall c r → g (φ k) z ∈ closedBall (0 : ℂ) 1 := by
    intro k z hz
    rw [mem_closedBall, dist_zero_right]
    exact hg_bd (φ k) z (hsubR hz)
  have hgl_mem : ∀ z ∈ closedBall c r, gl z ∈ closedBall (0 : ℂ) 1 := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    refine le_of_tendsto ((hgconv.tendsto_at hz).norm) ?_
    exact Eventually.of_forall (fun k => hg_bd (φ k) z (hsubR hz))
  have hUC : UniformContinuousOn μs (closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hμscont.continuousOn
  have hcomp : TendstoUniformlyOn (fun k z => μs (g (φ k) z)) (fun z => μs (gl z))
      atTop (closedBall c r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    rw [Metric.uniformContinuousOn_iff] at hUC
    obtain ⟨δ, hδ, hδμ⟩ := hUC ε hε
    rw [Metric.tendstoUniformlyOn_iff] at hgconv
    filter_upwards [hgconv δ hδ] with k hk
    intro z hz
    exact hδμ (gl z) (hgl_mem z hz) (g (φ k) z) (hgk_mem k z hz) (hk z hz)
  have hseqcont : ∀ k, ContinuousOn (fun z => μs (g (φ k) z)) (closedBall c r) := by
    intro k
    exact hμscont.comp_continuousOn ((hg_diff (φ k)).continuousOn.mono hsubR)
  have hGcont : ContinuousOn (fun z => μs (gl z)) (closedBall c r) :=
    hcomp.continuousOn (Frequently.of_forall hseqcont)
  have hconv : TendstoUniformlyOn (fun k z => stereo (f (φ k) z)) (fun z => μs (gl z))
      atTop (closedBall c r) := by
    refine hcomp.congr ?_
    filter_upwards with k z hz
    exact hg_eq (φ k) (hsubR hz)
  exact ⟨φ, fun z => μs (gl z), hφ, hGcont, hconv⟩

/-- A genuine frontier cross-ratio family cannot have bounded disk lifts through any continuous
sphere-valued target map.

The lift normality theorem produces a spherical locally uniform limit; the full cross-ratio obstruction
rules it out on the frontier closed ball. -/
theorem no_spherical_omitting_lift_crossRatio_of_frontier {c α β z₀ : ℂ} {ρ Rball : ℝ}
    {U : Set ℂ} {Rseq : ℕ → ℂ → ℂ} {μs : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ) (hρR : ρ < Rball / 2)
    (hU : closedBall z₀ ρ ⊆ U)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ U, z ≠ α)
    (hpreα : ∀ n z, z ∈ U → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ U, z ≠ β)
    (hRcont : ∀ n, ContinuousOn (Rseq n) (closedBall z₀ ρ))
    (hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) U)
    (hμscont : Continuous μs)
    (hlift : ∀ n, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₀ Rball) ∧
      (∀ z ∈ ball z₀ Rball, ‖g z‖ ≤ 1) ∧ Set.EqOn (fun z => μs (g z))
        (fun z => stereo (Rseq n z)) (ball z₀ Rball)) : False := by
  obtain ⟨φ, G, hφ, hGcont, hconv⟩ :=
    spherical_normal_of_omitting_lift (f := Rseq) hρ hρR hμscont hlift
  exact no_spherical_crossRatio_uniform_limit_of_frontier hzfront hρ hU hαβ hβ hα hpreα hzβ
    hRcont hR ⟨φ, G, hφ, hGcont, hconv⟩

/-- Memberwise spherical lift through a closed-disk sphere extension of the modular lambda target.

The extension `μs` only has to agree with `stereo (λ(cayleyInv z))` on the open unit disk. The lift
constructed from the upper-half-plane covering lands strictly inside that disk by `cayley_norm_lt_one`,
so no boundary value of the raw Cayley formula is used. -/
theorem omitting_lift_member_spherical_extension {c : ℂ} {R : ℝ}
    {μs : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hR : 0 < R)
    (hμs_eq : ∀ z : ℂ, ‖z‖ < 1 → μs z = stereo (modularLambda (cayleyInv z)))
    (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball c R))
    (homit : ∀ z ∈ ball c R, f z ∈ ({0, 1} : Set ℂ)ᶜ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ (∀ z ∈ ball c R, ‖g z‖ ≤ 1) ∧
      Set.EqOn (fun z => μs (g z)) (fun z => stereo (f z)) (ball c R) := by
  classical
  have hfcont : ContinuousOn f (ball c R) := hf.continuousOn
  let F : C(↥(ball c R), Punctured) :=
    ⟨fun z => ⟨f ↑z, homit ↑z z.2⟩,
      by
        apply Continuous.subtype_mk
        exact hfcont.comp_continuous continuous_subtype_val (fun z => z.2)⟩
  obtain ⟨G, hG⟩ := exists_continuous_lift_disk hR F
  let Gℂ : ℂ → ℂ := fun z => if h : z ∈ ball c R then ((G ⟨z, h⟩ : ℍ) : ℂ) else 0
  have hGℂval : ∀ z (hz : z ∈ ball c R), Gℂ z = ((G ⟨z, hz⟩ : ℍ) : ℂ) :=
    fun z hz => dif_pos hz
  have hGℂim : ∀ z (hz : z ∈ ball c R), 0 < (Gℂ z).im := by
    intro z hz
    rw [hGℂval z hz]
    exact (G ⟨z, hz⟩).2
  have hmodGℂ : ∀ z ∈ ball c R, modularLambda (Gℂ z) = f z := by
    intro z hz
    rw [hGℂval z hz, ← lambdaPunct_coe (G ⟨z, hz⟩)]
    have hlp : lambdaPunct (G ⟨z, hz⟩) = F ⟨z, hz⟩ := congrFun hG ⟨z, hz⟩
    rw [hlp]
    rfl
  have hGℂcont : ContinuousOn Gℂ (ball c R) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (ball c R).restrict Gℂ = fun τ => ((G τ : ℍ) : ℂ) := by
      funext τ
      show Gℂ ↑τ = _
      rw [hGℂval ↑τ τ.2]
    rw [heq]
    exact UpperHalfPlane.continuous_coe.comp G.continuous
  have hGℂdiff : DifferentiableOn ℂ Gℂ (ball c R) := by
    intro z₀ hz₀
    apply (differentiableAt_lift (h := modularLambda) ?_ ?_ ?_ ?_ ?_).differentiableWithinAt
    · exact hGℂcont.continuousAt (isOpen_ball.mem_nhds hz₀)
    · exact (analyticAt_modularLambda (hGℂim z₀ hz₀)).hasStrictDerivAt
    · exact modularLambda_deriv_ne_zero' (hGℂim z₀ hz₀)
    · exact analyticAt_modularLambda (hGℂim z₀ hz₀)
    · have : (fun z => modularLambda (Gℂ z)) =ᶠ[𝓝 z₀] f :=
        eventuallyEq_of_mem (isOpen_ball.mem_nhds hz₀) (fun z hz => hmodGℂ z hz)
      exact (hf.differentiableAt (isOpen_ball.mem_nhds hz₀)).congr_of_eventuallyEq this
  refine ⟨fun z => cayley (Gℂ z), ?_, ?_, ?_⟩
  · intro z₀ hz₀
    have hne : Gℂ z₀ + Complex.I ≠ 0 := by
      intro hc
      apply absurd (hGℂim z₀ hz₀)
      have : (Gℂ z₀).im = -1 := by
        rw [show Gℂ z₀ = -Complex.I by linear_combination hc]
        simp
      rw [this]
      norm_num
    exact ((cayley_differentiableAt hne).comp z₀
      ((hGℂdiff z₀ hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀))).differentiableWithinAt
  · intro z hz
    exact le_of_lt (cayley_norm_lt_one (hGℂim z hz))
  · intro z hz
    have hstrict : ‖cayley (Gℂ z)‖ < 1 := cayley_norm_lt_one (hGℂim z hz)
    change μs (cayley (Gℂ z)) = stereo (f z)
    rw [hμs_eq _ hstrict]
    show stereo (modularLambda (cayleyInv (cayley (Gℂ z)))) = stereo (f z)
    have hne : Gℂ z + Complex.I ≠ 0 := by
      intro hc
      apply absurd (hGℂim z hz)
      have : (Gℂ z).im = -1 := by
        rw [show Gℂ z = -Complex.I by linear_combination hc]
        simp
      rw [this]
      norm_num
    rw [cayleyInv_cayley hne, hmodGℂ z hz]

/-- Concrete three-value bridge for iterate cross-ratios.

On a frontier ball, suppose the cross-ratio denominator fibres, numerator fibres, anchor points, and
periodic points are all avoided.  Then `crossRatio_iterate_omits_zero_one_on` gives the modular-lambda
disk lifts memberwise.  If `μs` is a continuous closed-disk sphere extension of
`stereo ∘ modularLambda ∘ cayleyInv` on the open disk, the resulting spherical normality contradicts
the cross-ratio frontier obstruction. -/
theorem no_periodic_free_crossRatio_modularLiftExtension_of_frontier {c α β z₀ : ℂ} {ρ Rball : ℝ}
    {μs : ℂ → EuclideanSpace ℝ (Fin 3)}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ : 0 < ρ) (hρR : ρ < Rball / 2)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rball, z ≠ α)
    (hpreα : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rball, z ≠ β)
    (hnper : ∀ n z, z ∈ ball z₀ Rball → (quadratic c)^[n] z ≠ z)
    (hμscont : Continuous μs)
    (hμs_eq : ∀ z : ℂ, ‖z‖ < 1 → μs z = stereo (modularLambda (cayleyInv z))) : False := by
  let Rseq : ℕ → ℂ → ℂ := fun n z => ((quadratic c)^[n] z - α) * (z - β) /
    (((quadratic c)^[n] z - β) * (z - α))
  have hRball : 0 < Rball := by
    linarith
  have hsub : closedBall z₀ ρ ⊆ ball z₀ Rball := closedBall_subset_ball (by linarith)
  have hRcont : ∀ n, ContinuousOn (Rseq n) (closedBall z₀ ρ) := by
    intro n
    exact ((differentiableOn_crossRatio_iterate (hβ n) hα).continuousOn).mono hsub
  have hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) (ball z₀ Rball) := by
    intro n z hz
    rfl
  have hlift : ∀ n, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₀ Rball) ∧
      (∀ z ∈ ball z₀ Rball, ‖g z‖ ≤ 1) ∧
      Set.EqOn (fun z => μs (g z))
        (fun z => stereo (Rseq n z)) (ball z₀ Rball) := by
    intro n
    exact omitting_lift_member_spherical_extension hRball hμs_eq (Rseq n)
      (differentiableOn_crossRatio_iterate (hβ n) hα)
      (crossRatio_iterate_omits_zero_one_on hαβ (hβ n) hα (hpreα n) hzβ (hnper n))
  exact no_spherical_omitting_lift_crossRatio_of_frontier hzfront hρ hρR hsub hαβ hβ hα
    hpreα hzβ hRcont hR hμscont hlift

end

end Bottcher
