import Mathlib.Tactic
import GaloisForLFunctions.Bottcher.ModularLambdaLift
import GaloisForLFunctions.Bottcher.ModularLambdaCovering
import GaloisForLFunctions.Bottcher.ModularLambdaUnconditional
import GaloisForLFunctions.Bottcher.ThetaWronskian
open Complex Metric UpperHalfPlane Filter Topology
open scoped UpperHalfPlane
namespace Bottcher

/-! # The three-value Montel lift datum (`#30`), assembled from the covering of `λ`

With `λ : ℍ → ℂ∖{0,1}` a covering map (`isCoveringMap_lambdaPunct`) and the analytic toolkit
(`exists_continuous_lift_disk`, `differentiableAt_lift`, the `cayley`/`cayleyInv` bounded model), an
omitting holomorphic disk map `f : 𝔻 → ℂ∖{0,1}` is lifted to a **bounded holomorphic** `g : 𝔻 → 𝔻` with
`(λ ∘ cayleyInv) ∘ g = f` — exactly the per-member hypothesis `hlift` of
`OmittingNormal.normal_of_omitting_lift`. The `g` is `cayley ∘ Gℂ` where `Gℂ` is the (ℂ-valued, `dite`-
extended) continuous lift `G : 𝔻 → ℍ`, holomorphic by `differentiableAt_lift` (`λ` a local biholo),
bounded by `cayley_norm_lt_one`, with `EqOn` by `cayleyInv_cayley`. -/

theorem omitting_lift_member {c : ℂ} {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball c R)) (homit : ∀ z ∈ ball c R, f z ∈ ({0, 1} : Set ℂ)ᶜ) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ (∀ z ∈ ball c R, ‖g z‖ ≤ 1) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) f (ball c R) := by
  classical
  -- F : continuous map ↥ball → Punctured
  have hfcont : ContinuousOn f (ball c R) := hf.continuousOn
  let F : C(↥(ball c R), Punctured) :=
    ⟨fun z => ⟨f ↑z, homit ↑z z.2⟩,
      by apply Continuous.subtype_mk; exact hfcont.comp_continuous continuous_subtype_val (fun z => z.2)⟩
  obtain ⟨G, hG⟩ := exists_continuous_lift_disk hR F
  -- the lift as a ℂ-valued function on ball
  let Gℂ : ℂ → ℂ := fun z => if h : z ∈ ball c R then ((G ⟨z, h⟩ : ℍ) : ℂ) else 0
  -- on ball: Gℂ z = ↑(G ⟨z,_⟩), and modularLambda (Gℂ z) = f z, Im (Gℂ z) > 0
  have hGℂval : ∀ z (hz : z ∈ ball c R), Gℂ z = ((G ⟨z, hz⟩ : ℍ) : ℂ) := fun z hz => dif_pos hz
  have hGℂim : ∀ z (hz : z ∈ ball c R), 0 < (Gℂ z).im := by
    intro z hz; rw [hGℂval z hz]; exact (G ⟨z, hz⟩).2
  have hmodGℂ : ∀ z ∈ ball c R, modularLambda (Gℂ z) = f z := by
    intro z hz
    rw [hGℂval z hz, ← lambdaPunct_coe (G ⟨z, hz⟩)]
    have hlp : lambdaPunct (G ⟨z, hz⟩) = F ⟨z, hz⟩ := congrFun hG ⟨z, hz⟩
    rw [hlp]; rfl
  -- continuity of Gℂ on ball
  have hGℂcont : ContinuousOn Gℂ (ball c R) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (ball c R).restrict Gℂ = fun τ => ((G τ : ℍ) : ℂ) := by
      funext τ; show Gℂ ↑τ = _; rw [hGℂval ↑τ τ.2]
    rw [heq]
    exact UpperHalfPlane.continuous_coe.comp G.continuous
  -- Gℂ holomorphic on ball
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
  -- the bounded holomorphic disk map
  refine ⟨fun z => cayley (Gℂ z), ?_, ?_, ?_⟩
  · -- DifferentiableOn
    intro z₀ hz₀
    have hne : Gℂ z₀ + Complex.I ≠ 0 := by
      intro hc; apply absurd (hGℂim z₀ hz₀)
      have : (Gℂ z₀).im = -1 := by rw [show Gℂ z₀ = -Complex.I by linear_combination hc]; simp
      rw [this]; norm_num
    exact ((cayley_differentiableAt hne).comp z₀
      ((hGℂdiff z₀ hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀))).differentiableWithinAt
  · -- bound
    intro z hz
    exact le_of_lt (cayley_norm_lt_one (hGℂim z hz))
  · -- EqOn
    intro z hz
    show modularLambda (cayleyInv (cayley (Gℂ z))) = f z
    have hne : Gℂ z + Complex.I ≠ 0 := by
      intro hc; apply absurd (hGℂim z hz)
      have : (Gℂ z).im = -1 := by rw [show Gℂ z = -Complex.I by linear_combination hc]; simp
      rw [this]; norm_num
    rw [cayleyInv_cayley hne, hmodGℂ z hz]

/-- **Based memberwise modular lift.** If the chosen basepoint value `f c` is represented by
`τ₀ ∈ ℍ`, the lifted disk map can be chosen with center value `cayley τ₀`.  This is the memberwise
producer consumed by the deck-normalized Montel extraction. -/
theorem omitting_lift_member_based {c : ℂ} {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball c R))
    (homit : ∀ z ∈ ball c R, f z ∈ ({0, 1} : Set ℂ)ᶜ)
    (τ₀ : ℍ) (hτ₀ : modularLambda (τ₀ : ℂ) = f c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ (∀ z ∈ ball c R, ‖g z‖ ≤ 1) ∧
      g c = cayley (τ₀ : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) f (ball c R) := by
  classical
  have hc_mem : c ∈ ball c R := mem_ball_self hR
  have hfcont : ContinuousOn f (ball c R) := hf.continuousOn
  let F : C(↥(ball c R), Punctured) :=
    ⟨fun z => ⟨f ↑z, homit ↑z z.2⟩,
      by apply Continuous.subtype_mk; exact hfcont.comp_continuous continuous_subtype_val (fun z => z.2)⟩
  let a₀ : ↥(ball c R) := ⟨c, hc_mem⟩
  have he₀ : lambdaPunct τ₀ = F a₀ := by
    apply Subtype.ext
    exact hτ₀
  obtain ⟨G, hGbase, hG⟩ := exists_continuous_lift_disk_based hR F a₀ τ₀ he₀
  let Gℂ : ℂ → ℂ := fun z => if h : z ∈ ball c R then ((G ⟨z, h⟩ : ℍ) : ℂ) else 0
  have hGℂval : ∀ z (hz : z ∈ ball c R), Gℂ z = ((G ⟨z, hz⟩ : ℍ) : ℂ) := fun z hz => dif_pos hz
  have hGℂbase : Gℂ c = (τ₀ : ℂ) := by
    rw [hGℂval c hc_mem]
    exact congrArg (fun x : ℍ => (x : ℂ)) hGbase
  have hGℂim : ∀ z (hz : z ∈ ball c R), 0 < (Gℂ z).im := by
    intro z hz; rw [hGℂval z hz]; exact (G ⟨z, hz⟩).2
  have hmodGℂ : ∀ z ∈ ball c R, modularLambda (Gℂ z) = f z := by
    intro z hz
    rw [hGℂval z hz, ← lambdaPunct_coe (G ⟨z, hz⟩)]
    have hlp : lambdaPunct (G ⟨z, hz⟩) = F ⟨z, hz⟩ := congrFun hG ⟨z, hz⟩
    rw [hlp]; rfl
  have hGℂcont : ContinuousOn Gℂ (ball c R) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (ball c R).restrict Gℂ = fun τ => ((G τ : ℍ) : ℂ) := by
      funext τ; show Gℂ ↑τ = _; rw [hGℂval ↑τ τ.2]
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
  refine ⟨fun z => cayley (Gℂ z), ?_, ?_, ?_, ?_⟩
  · intro z₀ hz₀
    have hne : Gℂ z₀ + Complex.I ≠ 0 := by
      intro hc; apply absurd (hGℂim z₀ hz₀)
      have : (Gℂ z₀).im = -1 := by rw [show Gℂ z₀ = -Complex.I by linear_combination hc]; simp
      rw [this]; norm_num
    exact ((cayley_differentiableAt hne).comp z₀
      ((hGℂdiff z₀ hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀))).differentiableWithinAt
  · intro z hz
    exact le_of_lt (cayley_norm_lt_one (hGℂim z hz))
  · change cayley (Gℂ c) = cayley (τ₀ : ℂ)
    rw [hGℂbase]
  · intro z hz
    show modularLambda (cayleyInv (cayley (Gℂ z))) = f z
    have hne : Gℂ z + Complex.I ≠ 0 := by
      intro hc; apply absurd (hGℂim z hz)
      have : (Gℂ z).im = -1 := by rw [show Gℂ z = -Complex.I by linear_combination hc]; simp
      rw [this]; norm_num
    rw [cayleyInv_cayley hne, hmodGℂ z hz]

end Bottcher

namespace Bottcher

/-- **Based memberwise modular lift with strict disk image.**  This is the based version needed by
cusp-normalized Schwarz-Pick/Harnack arguments: once the caller chooses a base preimage `τ₀`, the
covering lift can be chosen through that sheet and its Cayley coordinate is strictly disk-valued. -/
theorem omitting_lift_member_based_strict {c : ℂ} {R : ℝ} (hR : 0 < R) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f (ball c R))
    (homit : ∀ z ∈ ball c R, f z ∈ ({0, 1} : Set ℂ)ᶜ)
    (τ₀ : ℍ) (hτ₀ : modularLambda (τ₀ : ℂ) = f c) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball c R) ∧ (∀ z ∈ ball c R, ‖g z‖ < 1) ∧
      g c = cayley (τ₀ : ℂ) ∧
      Set.EqOn (fun z => modularLambda (cayleyInv (g z))) f (ball c R) := by
  classical
  have hc_mem : c ∈ ball c R := mem_ball_self hR
  have hfcont : ContinuousOn f (ball c R) := hf.continuousOn
  let F : C(↥(ball c R), Punctured) :=
    ⟨fun z => ⟨f ↑z, homit ↑z z.2⟩,
      by apply Continuous.subtype_mk; exact hfcont.comp_continuous continuous_subtype_val (fun z => z.2)⟩
  let a₀ : ↥(ball c R) := ⟨c, hc_mem⟩
  have he₀ : lambdaPunct τ₀ = F a₀ := by
    apply Subtype.ext
    exact hτ₀
  obtain ⟨G, hGbase, hG⟩ := exists_continuous_lift_disk_based hR F a₀ τ₀ he₀
  let Gℂ : ℂ → ℂ := fun z => if h : z ∈ ball c R then ((G ⟨z, h⟩ : ℍ) : ℂ) else 0
  have hGℂval : ∀ z (hz : z ∈ ball c R), Gℂ z = ((G ⟨z, hz⟩ : ℍ) : ℂ) := fun z hz => dif_pos hz
  have hGℂbase : Gℂ c = (τ₀ : ℂ) := by
    rw [hGℂval c hc_mem]
    exact congrArg (fun x : ℍ => (x : ℂ)) hGbase
  have hGℂim : ∀ z (hz : z ∈ ball c R), 0 < (Gℂ z).im := by
    intro z hz; rw [hGℂval z hz]; exact (G ⟨z, hz⟩).2
  have hmodGℂ : ∀ z ∈ ball c R, modularLambda (Gℂ z) = f z := by
    intro z hz
    rw [hGℂval z hz, ← lambdaPunct_coe (G ⟨z, hz⟩)]
    have hlp : lambdaPunct (G ⟨z, hz⟩) = F ⟨z, hz⟩ := congrFun hG ⟨z, hz⟩
    rw [hlp]; rfl
  have hGℂcont : ContinuousOn Gℂ (ball c R) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : (ball c R).restrict Gℂ = fun τ => ((G τ : ℍ) : ℂ) := by
      funext τ; show Gℂ ↑τ = _; rw [hGℂval ↑τ τ.2]
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
  refine ⟨fun z => cayley (Gℂ z), ?_, ?_, ?_, ?_⟩
  · intro z₀ hz₀
    have hne : Gℂ z₀ + Complex.I ≠ 0 := by
      intro hc; apply absurd (hGℂim z₀ hz₀)
      have : (Gℂ z₀).im = -1 := by rw [show Gℂ z₀ = -Complex.I by linear_combination hc]; simp
      rw [this]; norm_num
    exact ((cayley_differentiableAt hne).comp z₀
      ((hGℂdiff z₀ hz₀).differentiableAt (isOpen_ball.mem_nhds hz₀))).differentiableWithinAt
  · intro z hz
    exact cayley_norm_lt_one (hGℂim z hz)
  · change cayley (Gℂ c) = cayley (τ₀ : ℂ)
    rw [hGℂbase]
  · intro z hz
    show modularLambda (cayleyInv (cayley (Gℂ z))) = f z
    have hne : Gℂ z + Complex.I ≠ 0 := by
      intro hc; apply absurd (hGℂim z hz)
      have : (Gℂ z).im = -1 := by rw [show Gℂ z = -Complex.I by linear_combination hc]; simp
      rw [this]; norm_num
    rw [cayleyInv_cayley hne, hmodGℂ z hz]

end Bottcher
