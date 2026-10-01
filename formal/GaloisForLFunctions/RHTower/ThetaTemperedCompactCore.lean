import GaloisForLFunctions.RHTower.ThetaTemperedFourierKernel
import Mathlib.Analysis.LocallyConvex.HahnBanach

/-!
# Compact Schwartz tests determine tempered functionals

The actual compact-support submodule is dense in the original complex Schwartz topology.
A complex linear functional on this submodule extends uniquely to an original tempered
distribution exactly when its joint value is controlled by finitely many original Schwartz
seminorms. The extension retains the same bound on every original test. No norm on the
pointwise-convergence weak dual or separate coefficient growth envelope is used.
-/

open Filter Topology
open scoped SchwartzMap

noncomputable section

namespace RHTower

/-- The actual compactly supported original complex Schwartz tests. -/
def thetaSchwartzCompactCore : Submodule ℂ 𝓢(ℝ, ℂ) where
  carrier := {φ | HasCompactSupport (φ : ℝ → ℂ)}
  zero_mem' := by
    change HasCompactSupport (fun _ : ℝ => (0 : ℂ))
    simp [HasCompactSupport]
  add_mem' := by
    intro φ ψ hφ hψ
    change HasCompactSupport (fun x : ℝ => φ x + ψ x)
    exact hφ.add hψ
  smul_mem' := by
    intro a φ hφ
    change HasCompactSupport (fun x : ℝ => a * φ x)
    exact hφ.comp_left (g := fun z : ℂ => a * z) (by simp)

theorem thetaSchwartzCompactCore_mem_iff (φ : 𝓢(ℝ, ℂ)) :
    φ ∈ thetaSchwartzCompactCore ↔ HasCompactSupport (φ : ℝ → ℂ) := Iff.rfl

/-- Expanding actual compact cutoffs converge in every original Schwartz seminorm. -/
theorem thetaSchwartzCompactCore_dense :
    Dense (thetaSchwartzCompactCore : Set 𝓢(ℝ, ℂ)) := by
  intro φ
  exact mem_closure_of_tendsto (SchwartzMap.tendsto_compactSupportApproximation φ)
    (Filter.Eventually.of_forall fun n =>
      SchwartzMap.compactSupportApproximation_hasCompactSupport n φ)

/-- Agreement on all actual compact tests determines the original weak-dual functional. -/
theorem thetaTempered_eq_of_compact_eq (Q₁ Q₂ : 𝓢'(ℝ, ℂ))
    (h : ∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) → Q₁ φ = Q₂ φ) :
    Q₁ = Q₂ := by
  apply ContinuousLinearMap.ext
  intro φ
  have h₁ := (Q₁.continuous.tendsto φ).comp
    (SchwartzMap.tendsto_compactSupportApproximation φ)
  have h₂ : Tendsto (fun n : ℕ => Q₁ (SchwartzMap.compactSupportApproximation n φ))
      atTop (𝓝 (Q₂ φ)) :=
    ((Q₂.continuous.tendsto φ).comp
      (SchwartzMap.tendsto_compactSupportApproximation φ)).congr
        (fun n => (h _ (SchwartzMap.compactSupportApproximation_hasCompactSupport n φ)).symm)
  exact tendsto_nhds_unique h₁ h₂

theorem thetaTempered_eq_zero_iff_compact (Q : 𝓢'(ℝ, ℂ)) :
    Q = 0 ↔ ∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) → Q φ = 0 := by
  constructor
  · intro h φ _
    rw [h]
    rfl
  · intro h
    exact thetaTempered_eq_of_compact_eq Q 0 h

/-- One joint bound by a finite family of the original defining Schwartz seminorms. -/
def thetaSchwartzCompactCoreJointBound (L : thetaSchwartzCompactCore →ₗ[ℂ] ℂ) : Prop :=
  ∃ s : Finset (ℕ × ℕ), ∃ C : NNReal, ∀ φ : thetaSchwartzCompactCore,
    ‖L φ‖ ≤ (C : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (φ : 𝓢(ℝ, ℂ))

/-- Genuine original tempered continuity forces a joint finite seminorm bound. -/
theorem thetaSchwartzCompactCoreJointBound_of_tempered
    (L : thetaSchwartzCompactCore →ₗ[ℂ] ℂ) (Q : 𝓢'(ℝ, ℂ))
    (hQ : ∀ φ : thetaSchwartzCompactCore, Q (φ : 𝓢(ℝ, ℂ)) = L φ) :
    thetaSchwartzCompactCoreJointBound L := by
  let T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := Q
  let q : Seminorm ℂ 𝓢(ℝ, ℂ) := (normSeminorm ℂ ℂ).comp T.toLinearMap
  have hq : Continuous q := continuous_norm.comp T.continuous
  obtain ⟨s, C, _hC, hbound⟩ :=
    Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ) q hq
  refine ⟨s, C, fun φ => ?_⟩
  have hb := hbound (φ : 𝓢(ℝ, ℂ))
  change ‖Q (φ : 𝓢(ℝ, ℂ))‖ ≤
    (C : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (φ : 𝓢(ℝ, ℂ)) at hb
  rw [hQ φ] at hb
  exact hb

/-- The actual tempered extension retains exactly the supplied joint bound on all tests. -/
theorem thetaSchwartzCompactCore_exists_tempered_extension_of_bound
    (L : thetaSchwartzCompactCore →ₗ[ℂ] ℂ) (s : Finset (ℕ × ℕ)) (C : NNReal)
    (hbound : ∀ φ : thetaSchwartzCompactCore, ‖L φ‖ ≤
      (C : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) (φ : 𝓢(ℝ, ℂ))) :
    ∃ Q : 𝓢'(ℝ, ℂ),
      (∀ φ : thetaSchwartzCompactCore, Q (φ : 𝓢(ℝ, ℂ)) = L φ) ∧
      ∀ φ : 𝓢(ℝ, ℂ), ‖Q φ‖ ≤ (C : ℝ) * s.sup (schwartzSeminormFamily ℂ ℝ ℂ) φ := by
  have hp : ∀ φ : thetaSchwartzCompactCore, ‖L φ‖ ≤
      (C • s.sup (schwartzSeminormFamily ℂ ℝ ℂ)) (φ : 𝓢(ℝ, ℂ)) := by
    intro φ
    exact hbound φ
  obtain ⟨g, hg, hgBound⟩ :=
    Module.Dual.exists_extension_of_le_seminorm thetaSchwartzCompactCore L hp
  have hgCont : Continuous g :=
    (schwartz_withSeminorms ℂ ℝ ℂ).continuous_normedSpace_rng ℂ g ⟨s, C, hgBound⟩
  let T : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := ⟨g, hgCont⟩
  let Q : 𝓢'(ℝ, ℂ) :=
    ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) 𝓢(ℝ, ℂ) ℂ T
  exact ⟨Q, hg, hgBound⟩

/-- The exact joint original seminorm criterion, including existence and uniqueness. -/
theorem thetaSchwartzCompactCoreJointBound_iff_existsUnique_tempered_extension
    (L : thetaSchwartzCompactCore →ₗ[ℂ] ℂ) :
    thetaSchwartzCompactCoreJointBound L ↔
      ∃! Q : 𝓢'(ℝ, ℂ), ∀ φ : thetaSchwartzCompactCore, Q (φ : 𝓢(ℝ, ℂ)) = L φ := by
  constructor
  · rintro ⟨s, C, hbound⟩
    obtain ⟨Q, hQ, _hBound⟩ :=
      thetaSchwartzCompactCore_exists_tempered_extension_of_bound L s C hbound
    refine ⟨Q, hQ, fun Q' hQ' => ?_⟩
    apply thetaTempered_eq_of_compact_eq Q' Q
    intro φ hφ
    exact (hQ' ⟨φ, hφ⟩).trans (hQ ⟨φ, hφ⟩).symm
  · intro h
    obtain ⟨Q, hQ⟩ := h.exists
    exact thetaSchwartzCompactCoreJointBound_of_tempered L Q hQ

end RHTower
