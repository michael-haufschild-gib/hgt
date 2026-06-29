/-
# Modular lambda omitting lifts for Marty bounds

This file connects the modular-lambda lift construction to `OmittingMartyBridge`.  The lift produced
from the upper-half-plane covering lands in the open unit disk, and the disk target
`ζ ↦ λ(cayleyInv ζ)` is differentiable there.  Thus the only remaining analytic datum for the
three-value/Marty close is a spherical-derivative bound for this fixed disk target.
-/
import GaloisForLFunctions.Bottcher.OmittingMartyBridge
import GaloisForLFunctions.Bottcher.ModularLambdaOmittingLift

open Complex Metric Set Filter Topology UpperHalfPlane
open scoped UpperHalfPlane

namespace Bottcher

noncomputable section

/-- The inverse Cayley transform is holomorphic away from its pole. -/
theorem cayleyInv_differentiableAt {z : ℂ} (hz : z ≠ 1) : DifferentiableAt ℂ cayleyInv z := by
  unfold cayleyInv
  exact (differentiableAt_const (c := Complex.I)).mul
    (((differentiableAt_const (c := (1 : ℂ))).add differentiableAt_id).div
      ((differentiableAt_const (c := (1 : ℂ))).sub differentiableAt_id)
      (sub_ne_zero.mpr (Ne.symm hz)))

/-- The inverse Cayley transform sends the open unit disk into the upper half-plane. -/
theorem cayleyInv_im_pos_of_norm_lt_one {θ : ℂ} (hθ : ‖θ‖ < 1) :
    0 < (cayleyInv θ).im := by
  have hne : θ ≠ 1 := by
    intro h
    rw [h, norm_one] at hθ
    linarith
  have hden : 0 < Complex.normSq (1 - θ) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  unfold cayleyInv
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul, zero_add, Complex.div_re,
      ← add_div]
  apply div_pos _ hden
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  have hsq : ‖θ‖ ^ 2 < 1 := by nlinarith [hθ, norm_nonneg θ]
  nlinarith [Complex.sq_norm θ, Complex.normSq_apply θ, hsq]

/-- The modular disk target `ζ ↦ λ(cayleyInv ζ)` is holomorphic on the open unit disk. -/
theorem modularDiskTarget_differentiableAt {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ (fun ζ => modularLambda (cayleyInv ζ)) z := by
  have hzne : z ≠ 1 := by
    intro h
    rw [h, norm_one] at hz
    linarith
  exact (analyticAt_modularLambda (cayleyInv_im_pos_of_norm_lt_one hz)).differentiableAt.comp z
    (cayleyInv_differentiableAt hzne)

/-- Memberwise modular-lambda lift with the strict disk bound exposed. -/
theorem omitting_lift_member_strict {c : ℂ} {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball c R))
    (homit : ∀ z ∈ ball c R, f z ∈ ({0, 1} : Set ℂ)ᶜ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ (∀ z ∈ ball c R, ‖g z‖ < 1) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) f (ball c R) := by
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
    exact cayley_norm_lt_one (hGℂim z hz)
  · intro z hz
    show modularLambda (cayleyInv (cayley (Gℂ z))) = f z
    have hne : Gℂ z + Complex.I ≠ 0 := by
      intro hc
      apply absurd (hGℂim z hz)
      have : (Gℂ z).im = -1 := by
        rw [show Gℂ z = -Complex.I by linear_combination hc]
        simp
      rw [this]
      norm_num
    rw [cayleyInv_cayley hne, hmodGℂ z hz]

/-- Concrete modular-lift/Marty contradiction for a periodic-free frontier cross-ratio family.

The remaining analytic datum is `hμbd`: a global spherical-derivative bound for the fixed modular disk
target on the open unit disk. -/
theorem no_periodic_free_crossRatio_modularTargetBound_of_frontier {c α β z₀ : ℂ}
    {ρ Rlift A : ℝ}
    (hzfront : z₀ ∈ frontier (filledJulia c)) (hρ0 : 0 < ρ) (hρR : ρ < Rlift / 2)
    (hαβ : α ≠ β)
    (hβ : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ β)
    (hα : ∀ z ∈ ball z₀ Rlift, z ≠ α)
    (hpreα : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ α)
    (hzβ : ∀ z ∈ ball z₀ Rlift, z ≠ β)
    (hnper : ∀ n z, z ∈ ball z₀ Rlift → (quadratic c)^[n] z ≠ z)
    (hμbd : ∀ w : ℂ, ‖w‖ < 1 →
      sphericalDeriv (fun ζ => modularLambda (cayleyInv ζ)) w ≤ A) : False := by
  let Rseq : ℕ → ℂ → ℂ := fun n z => ((quadratic c)^[n] z - α) * (z - β) /
    (((quadratic c)^[n] z - β) * (z - α))
  have hRlift : 0 < Rlift := by linarith
  have hsub : closedBall z₀ ρ ⊆ ball z₀ Rlift := closedBall_subset_ball (by linarith)
  have hR : ∀ n, Set.EqOn (Rseq n)
      (fun z => ((quadratic c)^[n] z - α) * (z - β) /
        (((quadratic c)^[n] z - β) * (z - α))) (ball z₀ Rlift) := by
    intro n z hz
    rfl
  have hlift : ∀ n, ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball z₀ Rlift) ∧
      (∀ z ∈ ball z₀ Rlift, ‖g z‖ < 1) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z)))
        (Rseq n) (ball z₀ Rlift) := by
    intro n
    exact omitting_lift_member_strict hRlift (Rseq n)
      (differentiableOn_crossRatio_iterate (hβ n) hα)
      (crossRatio_iterate_omits_zero_one_on hαβ (hβ n) hα (hpreα n) hzβ (hnper n))
  exact no_spherical_strict_omitting_lift_of_bounded_target_sphericalDeriv_crossRatio_of_frontier
    (μ := fun ζ => modularLambda (cayleyInv ζ)) hzfront hρ0 hρR hsub hαβ hβ hα hpreα hzβ
    hR (fun w hw => modularDiskTarget_differentiableAt hw) hμbd hlift

end

end Bottcher
