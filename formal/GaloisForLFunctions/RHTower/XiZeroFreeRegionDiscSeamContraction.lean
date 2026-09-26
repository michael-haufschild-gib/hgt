import GaloisForLFunctions.RHTower.CircleHolomorphicPhaseSeamContraction
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros

/-!
# The adjoint seam contracts on every disc inside the zero-free region

The Riemann hypothesis is equivalent to the adjoint Hankel seam `(1 − P) U† P` of the `xi`
boundary phase being a strict contraction on every closed disc right of the critical line
(`riemannHypothesis_iff_forall_xiRightDisc_adjointSeam_lt_one`).  This module proves that
contraction unconditionally on every closed disc contained in the explicit zero-free region

`|Im z| < 4`  or  `Re z > 1 − 1/(58 log |Im z|)`  (or `Re z ≥ 1`)

(`xiDisc_adjointSeam_lt_one_of_zeroFreeRegion`).  The inputs are the corpus zero-free region
(`four_le_abs_im_of_zeta_zero`, `re_le_one_sub_of_zeta_zero`) and the general implication
"no zero in the closed disc ⇒ relative index `0` ⇒ strict contraction"
(`xiDisc_adjointSeam_lt_one_of_ne_zero`), which holds for any disc.
-/

noncomputable section

open Complex Metric

namespace RHTower

/-- If `xi` has no zero in the closed disc, the Hardy relative index vanishes. -/
theorem xiDiscRelativeIndex_eq_zero_of_ne_zero (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) (hzero : ∀ z ∈ closedBall c t, xi z ≠ 0) :
    xiDiscRelativeIndex c t ht hne = 0 := by
  obtain ⟨Z, hZball, hZzero, hidx⟩ := (xiDiscDatum c t ht hne).relativeIndex_eq_zeroCount
  have hZ : Z = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro ρ hρ
    have hball := hZball ρ hρ
    exact hzero ρ (ball_subset_closedBall hball) ((hZzero ρ hball).mpr hρ)
  unfold xiDiscRelativeIndex
  rw [hidx, hZ, Finset.sum_empty]

/-- **Zero-free discs have contracting adjoint seam.**  If `xi` has no zero in the closed disc,
the adjoint Hankel seam of its boundary phase is a strict contraction. -/
theorem xiDisc_adjointSeam_lt_one_of_ne_zero (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0) (hzero : ∀ z ∈ closedBall c t, xi z ≠ 0) :
    ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ < 1 := by
  set D := (xiDiscDatum c t ht hne).circlePhase.datum with hD
  apply D.norm_adjointHankelSeam_lt_one
  intro y hRy hPy
  have hidx := xiDiscRelativeIndex_eq_zero_of_ne_zero c t ht hne hzero
  unfold xiDiscRelativeIndex at hidx
  rw [← hD, D.relativeIndex_eq_intersection_finrank_sub] at hidx
  have hbot : LinearMap.range (D.projection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) ⊓
      LinearMap.ker (D.conjugateProjection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) = ⊥ := by
    rw [eq_bot_iff]
    intro f hf
    rw [Submodule.mem_inf, mem_range_restrictedProjection_iff_apply_eq _
      D.projection_idempotent, LinearMap.mem_ker] at hf
    rw [Submodule.mem_bot]
    exact (xiDiscDatum c t ht hne).ker_conjugate_inf_range_projection_trivial f hf.1 hf.2
  rw [hbot, finrank_bot, Nat.cast_zero, sub_zero, Nat.cast_eq_zero] at hidx
  have hfin : FiniteDimensional ℂ ↥(LinearMap.range
      (D.conjugateProjection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) ⊓
        LinearMap.ker (D.projection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2)) := by
    rw [← eigenspace_restrictedProjectionDisplacement_one_eq_range_inf_ker _ _
      D.conjugateProjection_idempotent D.projection_idempotent
      D.conjugateProjection_adjoint D.projection_adjoint]
    exact ContinuousLinearMap.finite_dimensional_eigenspace
      D.displacement_isHilbertSchmidt.isCompactOperator 1 one_ne_zero
  have hbot' := Submodule.finrank_eq_zero.mp hidx
  have hmem : y ∈ LinearMap.range (D.conjugateProjection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) ⊓
      LinearMap.ker (D.projection : CCMCircleL2 →ₗ[ℂ] CCMCircleL2) := by
    rw [Submodule.mem_inf, mem_range_restrictedProjection_iff_apply_eq _
      D.conjugateProjection_idempotent, LinearMap.mem_ker]
    exact ⟨hRy, hPy⟩
  rw [hbot', Submodule.mem_bot] at hmem
  exact hmem

/-- The explicit zero-free region for `xi`. -/
def XiZeroFreePoint (z : ℂ) : Prop :=
  1 ≤ z.re ∨ |z.im| < 4 ∨ 1 - 1 / 58 / Real.log |z.im| < z.re

/-- `xi` has no zero at a point of the explicit zero-free region. -/
theorem xi_ne_zero_of_zeroFreePoint {z : ℂ} (hz : XiZeroFreePoint z) : xi z ≠ 0 := by
  rcases hz with h1 | h1 | h1
  · exact xi_ne_zero_of_one_le_re h1
  · intro hxi
    by_cases hre : 0 < z.re
    · by_cases hlt : z.re < 1
      · have hz1 : z ≠ 1 := fun h => by rw [h] at hlt; simp at hlt
        have hzeta : riemannZeta z = 0 := (xi_eq_zero_iff hre hz1).mp hxi
        have := four_le_abs_im_of_zeta_zero hre hlt hzeta
        linarith
      · push Not at hlt
        exact xi_ne_zero_of_one_le_re hlt hxi
    · push Not at hre
      have h1z : 1 ≤ (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      exact xi_ne_zero_of_one_le_re h1z (by rw [xi_one_sub]; exact hxi)
  · intro hxi
    by_cases hre : 0 < z.re
    · by_cases hlt : z.re < 1
      · have hz1 : z ≠ 1 := fun h => by rw [h] at hlt; simp at hlt
        have hzeta : riemannZeta z = 0 := (xi_eq_zero_iff hre hz1).mp hxi
        have := re_le_one_sub_of_zeta_zero hre hlt hzeta
        linarith
      · push Not at hlt
        exact xi_ne_zero_of_one_le_re hlt hxi
    · push Not at hre
      have h1z : 1 ≤ (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
      exact xi_ne_zero_of_one_le_re h1z (by rw [xi_one_sub]; exact hxi)

/-- **Unconditional seam contraction on the zero-free region.**  On every closed disc contained
in the explicit zero-free region, the adjoint Hankel seam of the `xi` boundary phase is a strict
contraction. -/
theorem xiDisc_adjointSeam_lt_one_of_zeroFreeRegion (c : ℂ) (t : ℝ) (ht : 0 < t)
    (hregion : ∀ z ∈ closedBall c t, XiZeroFreePoint z) :
    ∃ hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0,
      ‖(xiDiscDatum c t ht hne).circlePhase.datum.adjointHankelSeam‖ < 1 := by
  have hzero : ∀ z ∈ closedBall c t, xi z ≠ 0 := fun z hz =>
    xi_ne_zero_of_zeroFreePoint (hregion z hz)
  have hne : ∀ ζ ∈ sphere c t, xi ζ ≠ 0 := fun ζ hζ =>
    hzero ζ (sphere_subset_closedBall hζ)
  exact ⟨hne, xiDisc_adjointSeam_lt_one_of_ne_zero c t ht hne hzero⟩

end RHTower
