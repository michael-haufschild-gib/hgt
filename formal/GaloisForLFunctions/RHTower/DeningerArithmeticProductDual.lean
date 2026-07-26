import GaloisForLFunctions.RHTower.DeningerArithmeticCompactOpen
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Continuous dual of the product jet carrier

The compact-open quotient is expected to identify with a product of finite local jet algebras.
The continuous dual of such a product must have finite coordinate support.  This file proves the
required topological-vector-space fact directly for an arbitrary product `ι → ℂ`.

No Xi divisor or spectral enumeration occurs here.  The theorem becomes arithmetic only after a
source jet-interpolation equivalence is constructed.
-/

open Filter Metric Set Topology

namespace RHTower

noncomputable section

/--
Every continuous complex-linear functional on a product of complex lines kills the subspace of
vectors vanishing on some finite coordinate set.
-/
theorem deningerContinuousDual_pi_hasFiniteSupport
    {ι : Type*} (L : (ι → ℂ) →L[ℂ] ℂ) :
    ∃ s : Finset ι,
      ∀ x : ι → ℂ, (∀ i ∈ s, x i = 0) → L x = 0 := by
  classical
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (L 0) := by
    simpa using Metric.ball_mem_nhds (0 : ℂ) zero_lt_one
  have hpre : L ⁻¹' Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ι → ℂ) :=
    L.continuous.continuousAt hball
  rw [nhds_pi, Filter.mem_pi, exists_finite_iff_finset] at hpre
  obtain ⟨s, U, hU, hsub⟩ := hpre
  refine ⟨s, fun x hx => ?_⟩
  by_contra hLx
  let c : ℂ := (L x)⁻¹
  have hcx : c • x ∈ Set.pi (s : Set ι) U := by
    intro i hi
    have hzero : (0 : ℂ) ∈ U i :=
      mem_of_mem_nhds (hU i)
    simpa [Pi.smul_apply, hx i hi] using hzero
  have hcball :
      L (c • x) ∈ Metric.ball (0 : ℂ) 1 :=
    hsub hcx
  have hnorm : ‖L (c • x)‖ < 1 := by
    simpa [Metric.mem_ball] using hcball
  rw [L.map_smul] at hnorm
  change ‖c * L x‖ < 1 at hnorm
  rw [show c * L x = 1 by
    exact inv_mul_cancel₀ hLx] at hnorm
  norm_num at hnorm

/--
Equivalent finite-coordinate dependence statement: two product vectors agreeing on a finite
support selected by the functional have the same value.
-/
theorem deningerContinuousDual_pi_dependsOnFinset
    {ι : Type*} (L : (ι → ℂ) →L[ℂ] ℂ) :
    ∃ s : Finset ι,
      ∀ x y : ι → ℂ,
        (∀ i ∈ s, x i = y i) →
          L x = L y := by
  obtain ⟨s, hs⟩ :=
    deningerContinuousDual_pi_hasFiniteSupport L
  refine ⟨s, fun x y hxy => ?_⟩
  have hzero : L (x - y) = 0 :=
    hs (x - y) (fun i hi => by
      simp [hxy i hi])
  have hsub : L x - L y = 0 := by
    simpa using hzero
  exact sub_eq_zero.mp hsub

end

end RHTower
