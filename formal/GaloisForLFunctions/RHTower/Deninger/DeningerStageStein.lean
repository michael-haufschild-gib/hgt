import GaloisForLFunctions.RHTower.Deninger.DeningerStageDeRham

/-!
# The finite character stages are Stein

A finite character stage is holomorphically convex and holomorphically separable, which is the
Stein property for a domain in `ℂ^r`.  Convexity is witnessed by the coordinates and their inverses:
on the holomorphically convex hull of a compact set the coordinates stay bounded and bounded away
from zero, so the hull is a closed subset of a compact polyannulus inside the stage.  Separability
is witnessed by the coordinates alone.

* `deningerHolHull` : the holomorphically convex hull of a set inside a domain.
* `deningerStageTorus_holomorphicallyConvex` : the stage is holomorphically convex.
* `deningerStageTorus_holomorphicallySeparable` : the stage is holomorphically separable.
* `deningerStageTorus_isStein` : the stage is Stein.
-/

namespace RHTower

open Filter Topology

section Stein

variable {r : ℕ}

/-- **The holomorphically convex hull** of a set inside a domain: the points at which every function
holomorphic on the domain is bounded by its bounds on the set. -/
def deningerHolHull (Ω K : Set (Fin r → ℂ)) : Set (Fin r → ℂ) :=
  {z | z ∈ Ω ∧ ∀ f : (Fin r → ℂ) → ℂ, AnalyticOnNhd ℂ f Ω → ∀ C : ℝ,
    (∀ w ∈ K, ‖f w‖ ≤ C) → ‖f z‖ ≤ C}

theorem deningerHolHull_subset (Ω K : Set (Fin r → ℂ)) : deningerHolHull Ω K ⊆ Ω :=
  fun _ hz => hz.1

/-- **Holomorphic convexity** of a domain: the hull of a compact set is compact. -/
def DeningerIsHolomorphicallyConvex (Ω : Set (Fin r → ℂ)) : Prop :=
  ∀ K ⊆ Ω, IsCompact K → IsCompact (deningerHolHull Ω K)

/-- **Holomorphic separability** of a domain: holomorphic functions separate its points. -/
def DeningerIsHolomorphicallySeparable (Ω : Set (Fin r → ℂ)) : Prop :=
  ∀ z ∈ Ω, ∀ w ∈ Ω, z ≠ w → ∃ f : (Fin r → ℂ) → ℂ, AnalyticOnNhd ℂ f Ω ∧ f z ≠ f w

/-- **A Stein domain**: holomorphically convex and holomorphically separable. -/
def DeningerIsStein (Ω : Set (Fin r → ℂ)) : Prop :=
  DeningerIsHolomorphicallyConvex Ω ∧ DeningerIsHolomorphicallySeparable Ω

/-- The coordinates are holomorphic on any domain. -/
theorem deningerCoord_analyticOnNhd (Ω : Set (Fin r → ℂ)) (i : Fin r) :
    AnalyticOnNhd ℂ (fun z : Fin r → ℂ => z i) Ω := fun z _ =>
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i).analyticAt z

/-- The inverse coordinates are holomorphic on the stage. -/
theorem deningerCoordInv_analyticOnNhd (i : Fin r) :
    AnalyticOnNhd ℂ (fun z : Fin r → ℂ => (z i)⁻¹) (deningerStageTorus r) := fun z hz =>
  ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin r => ℂ) i).analyticAt z).inv (hz i)

/-- **The finite character stage is holomorphically convex.** -/
theorem deningerStageTorus_holomorphicallyConvex (r : ℕ) :
    DeningerIsHolomorphicallyConvex (deningerStageTorus r) := by
  intro K hKΩ hK
  obtain ⟨b, hb⟩ : ∃ b : ℝ, ∀ z ∈ K, ‖z‖ ≤ b :=
    hK.exists_bound_of_continuousOn continuousOn_id
  have hCex : ∀ i : Fin r, ∃ C : ℝ, ∀ z ∈ K, ‖(z i)⁻¹‖ ≤ C := by
    intro i
    refine hK.exists_bound_of_continuousOn ?_
    exact ContinuousOn.inv₀ (Continuous.continuousOn (continuous_apply i))
      fun z hz => hKΩ hz i
  choose C hC using hCex
  set B : ℝ := max b 1 with hB
  set D : Fin r → ℝ := fun i => max (C i) 1 with hD
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hDpos : ∀ i, (0 : ℝ) < D i := fun i => lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  set A : Set (Fin r → ℂ) := {z | (∀ i, (D i)⁻¹ ≤ ‖z i‖) ∧ ‖z‖ ≤ B} with hA
  have hAclosed : IsClosed A := by
    have h1 : IsClosed {z : Fin r → ℂ | ∀ i, (D i)⁻¹ ≤ ‖z i‖} := by
      have : {z : Fin r → ℂ | ∀ i, (D i)⁻¹ ≤ ‖z i‖} =
          ⋂ i, {z : Fin r → ℂ | (D i)⁻¹ ≤ ‖z i‖} := by
        ext z
        simp [Set.mem_iInter]
      rw [this]
      exact isClosed_iInter fun i =>
        isClosed_le continuous_const ((continuous_apply i).norm)
    have h2 : IsClosed {z : Fin r → ℂ | ‖z‖ ≤ B} := isClosed_le continuous_norm continuous_const
    exact h1.inter h2
  have hAcompact : IsCompact A := by
    refine Metric.isCompact_of_isClosed_isBounded hAclosed ?_
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨B, fun z hz => ?_⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hz.2
  have hAΩ : A ⊆ deningerStageTorus r := by
    intro z hz i hzero
    have := hz.1 i
    rw [hzero] at this
    simp only [norm_zero] at this
    exact absurd this (not_le.2 (inv_pos.2 (hDpos i)))
  have hhullA : deningerHolHull (deningerStageTorus r) K ⊆ A := by
    intro z hz
    have hupper : ∀ i, ‖z i‖ ≤ B := by
      intro i
      refine hz.2 (fun w : Fin r → ℂ => w i) (deningerCoord_analyticOnNhd _ i) B ?_
      intro w hw
      exact le_trans (norm_le_pi_norm w i) (le_trans (hb w hw) (le_max_left _ _))
    refine ⟨fun i => ?_, ?_⟩
    · have hinv : ‖(z i)⁻¹‖ ≤ D i := by
        refine hz.2 (fun w : Fin r → ℂ => (w i)⁻¹) (deningerCoordInv_analyticOnNhd i) (D i) ?_
        intro w hw
        exact le_trans (hC i w hw) (le_max_left _ _)
      have hzi : z i ≠ 0 := hz.1 i
      rw [norm_inv] at hinv
      have hnpos : (0 : ℝ) < ‖z i‖ := norm_pos_iff.2 hzi
      exact (inv_le_comm₀ hnpos (hDpos i)).1 hinv
    · exact (pi_norm_le_iff_of_nonneg (le_of_lt hBpos)).2 hupper
  have hhullclosed : IsClosed (deningerHolHull (deningerStageTorus r) K) := by
    rw [← closure_subset_iff_isClosed]
    intro z hzc
    have hzA : z ∈ A := hAclosed.closure_subset_iff.2 hhullA hzc
    have hzΩ : z ∈ deningerStageTorus r := hAΩ hzA
    refine ⟨hzΩ, fun f hf Cf hCf => ?_⟩
    haveI : (𝓝[deningerHolHull (deningerStageTorus r) K] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.1 hzc
    have hcont : ContinuousAt (fun y => ‖f y‖) z := ((hf z hzΩ).continuousAt).norm
    refine le_of_tendsto
      (hcont.continuousWithinAt (s := deningerHolHull (deningerStageTorus r) K)).tendsto ?_
    exact eventually_nhdsWithin_of_forall fun y hy => hy.2 f hf Cf hCf
  exact hAcompact.of_isClosed_subset hhullclosed hhullA

/-- **The finite character stage is holomorphically separable**: the coordinates separate its
points. -/
theorem deningerStageTorus_holomorphicallySeparable (r : ℕ) :
    DeningerIsHolomorphicallySeparable (deningerStageTorus r) := by
  intro z _ w _ hzw
  obtain ⟨i, hi⟩ : ∃ i, z i ≠ w i := Function.ne_iff.1 hzw
  exact ⟨fun y : Fin r → ℂ => y i, deningerCoord_analyticOnNhd _ i, hi⟩

/-- **The finite character stages `(ℂ^×)^r` are Stein.** -/
theorem deningerStageTorus_isStein (r : ℕ) : DeningerIsStein (deningerStageTorus r) :=
  ⟨deningerStageTorus_holomorphicallyConvex r, deningerStageTorus_holomorphicallySeparable r⟩

end Stein

end RHTower
