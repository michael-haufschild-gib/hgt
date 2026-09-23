import GaloisForLFunctions.HTGeometry.PolynomialVanishingOrderBound
import GaloisForLFunctions.HTGeometry.TruncatedInverseSeries

/-!
# Polynomials evaluated at `1/s`

The truncations of a series in `1/s` are polynomial evaluations at `s⁻¹`.  This file records their
derivative, their analyticity away from the origin, their limit along a horizontal ray, and the
uniform bound they satisfy outside the unit disc.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology Polynomial

noncomputable section

theorem hasDerivAt_polyEval_inv (P : ℂ[X]) {s : ℂ} (hs : s ≠ 0) :
    HasDerivAt (fun z : ℂ => P.eval z⁻¹)
      ((derivative P).eval s⁻¹ * (-(s ^ (2 : ℕ))⁻¹)) s := by
  have h1 : HasDerivAt (fun y : ℂ => y⁻¹) (-(s ^ (2 : ℕ))⁻¹) s := hasDerivAt_inv hs
  have h2 : HasDerivAt (fun x : ℂ => P.eval x) ((derivative P).eval s⁻¹) s⁻¹ := P.hasDerivAt s⁻¹
  have hcomp := h2.comp s h1
  have hrw : ((fun x : ℂ => P.eval x) ∘ fun y : ℂ => y⁻¹) = fun z : ℂ => P.eval z⁻¹ := by
    funext z; rfl
  rwa [hrw] at hcomp

theorem differentiableAt_polyEval_inv (P : ℂ[X]) {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (fun z : ℂ => P.eval z⁻¹) s :=
  (hasDerivAt_polyEval_inv P hs).differentiableAt

theorem analyticAt_polyEval_inv (P : ℂ[X]) {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (fun z : ℂ => P.eval z⁻¹) s := by
  have hopen : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne
  have hdiff : DifferentiableOn ℂ (fun z : ℂ => P.eval z⁻¹) {z : ℂ | z ≠ 0} := fun z hz =>
    (differentiableAt_polyEval_inv P hz).differentiableWithinAt
  exact hdiff.analyticAt (hopen.mem_nhds hs)

theorem tendsto_polyEval_inv_ray (P : ℂ[X]) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => P.eval (s + (x : ℂ))⁻¹) atTop (nhds (P.eval 0)) := by
  have hnorm : Tendsto (fun x : ℝ => ‖s + (x : ℂ)‖) atTop atTop :=
    tendsto_norm_shift_ray (le_of_lt hs)
  have hinv : Tendsto (fun x : ℝ => (s + (x : ℂ))⁻¹) atTop (nhds 0) := by
    refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
    have := hnorm.inv_tendsto_atTop
    refine this.congr fun x => ?_
    rw [Pi.inv_apply, norm_inv]
  have hcont : ContinuousAt (fun w : ℂ => P.eval w) 0 := P.continuous_aeval.continuousAt
  exact hcont.tendsto.comp hinv

theorem norm_polyEval_inv_le (P : ℂ[X]) {s : ℂ} (hs : 1 ≤ ‖s‖) :
    ‖P.eval s⁻¹‖ ≤ ∑ j ∈ Finset.range (P.natDegree + 1), ‖P.coeff j‖ := by
  refine norm_polyEval_le_of_norm_le_one P ?_
  rw [norm_inv]
  rw [inv_le_one_iff₀]
  exact Or.inr hs

end

end GaloisForLFunctions.HTGeometry
