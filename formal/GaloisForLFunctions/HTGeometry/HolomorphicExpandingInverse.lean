import GaloisForLFunctions.Bottcher.Univalence
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

/-!
# Inverse disks for holomorphic maps with expanding real derivative

Noshiro-Warschawski applied to every linear perturbation of slope less than
one gives a quantitative lower bound on image distances. The open mapping
estimate then gives inverse disks, whose inverse is holomorphic.
-/

open Complex Set Metric Filter
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

/-- A real derivative lower bound of one expands every distance on a convex domain. -/
theorem norm_sub_le_norm_sub_of_one_le_re_deriv {f : ℂ → ℂ} {U : Set ℂ}
    (hU : Convex ℝ U) (hf : ∀ z ∈ U, HasDerivAt f (deriv f z) z)
    (hcont : ContinuousOn (deriv f) U) (hbound : ∀ z ∈ U, 1 ≤ (deriv f z).re)
    {x y : ℂ} (hx : x ∈ U) (hy : y ∈ U) :
    ‖y - x‖ ≤ ‖f y - f x‖ := by
  by_contra h
  have hnorm : ‖f y - f x‖ < ‖y - x‖ := lt_of_not_ge h
  have hne : y - x ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hnorm)
  let c : ℂ := (f y - f x) / (y - x)
  have hc : ‖c‖ < 1 := by
    rw [show ‖c‖ = ‖f y - f x‖ / ‖y - x‖ by exact norm_div _ _]
    exact (div_lt_one (norm_pos_iff.mpr hne)).mpr hnorm
  let g : ℂ → ℂ := fun z => f z - c * z
  have hgd : ∀ z ∈ U, HasDerivAt g (deriv f z - c) z := by
    intro z hz
    convert (hf z hz).sub ((hasDerivAt_id z).const_mul c) using 1 <;>
      first | rfl | simp
  have hdg : ∀ z ∈ U, deriv g z = deriv f z - c := fun z hz => (hgd z hz).deriv
  have hginj : InjOn g U := Bottcher.injOn_of_re_deriv_pos hU
    (fun z hz => (hdg z hz).symm ▸ hgd z hz)
    ((hcont.sub continuousOn_const).congr hdg) (by
      intro z hz
      rw [hdg z hz, Complex.sub_re]
      have := Complex.re_le_norm c
      have := hbound z hz
      linarith)
  have hgeq : g y = g x := by
    dsimp [g, c]
    field_simp
    ring
  exact hne (sub_eq_zero.mpr (hginj hy hx hgeq))

/-- A quantitative inverse disk inside an open convex domain. -/
theorem exists_holomorphic_inverse_disk {f : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hUc : Convex ℝ U) (hf : DifferentiableOn ℂ f U)
    (hbound : ∀ z ∈ U, 1 ≤ (deriv f z).re)
    {b : ℂ} {r : ℝ} (hr : 0 < r) (hball : closedBall b r ⊆ U) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball (f b) (r / 2)) ∧
      ∀ w ∈ ball (f b) (r / 2), g w ∈ U ∧ f (g w) = w := by
  have hb : b ∈ U := hball (mem_closedBall_self hr.le)
  have hfd : ∀ z ∈ U, HasDerivAt f (deriv f z) z :=
    fun z hz => (hf.differentiableAt (hUo.mem_nhds hz)).hasDerivAt
  have hcont : ContinuousOn (deriv f) U := (hf.deriv hUo).continuousOn
  have hinj : InjOn f U := Bottcher.injOn_of_re_deriv_pos hUc hfd hcont
    (fun z hz => lt_of_lt_of_le zero_lt_one (hbound z hz))
  have hne : ∀ z ∈ U, deriv f z ≠ 0 := by
    intro z hz he
    have := hbound z hz
    norm_num [he] at this
  have hfreq : ∃ᶠ z in 𝓝 b, f z ≠ f b := by
    by_contra hn
    have he : f =ᶠ[𝓝 b] fun _ => f b := by
      filter_upwards [not_frequently.mp hn] with z hz
      exact not_not.mp hz
    have hh := (hfd b hb).congr_of_eventuallyEq he.symm
    exact hne b hb (hh.unique (hasDerivAt_const b (f b)))
  have himage : ball (f b) (r / 2) ⊆ f '' closedBall b r :=
    (hf.diffContOnCl_ball hball).ball_subset_image_closedBall hr (by
      intro z hz
      have hzball : z ∈ closedBall b r := sphere_subset_closedBall hz
      have hnorm := norm_sub_le_norm_sub_of_one_le_re_deriv hUc hfd hcont hbound hb
        (hball hzball)
      have hdist : ‖z - b‖ = r := mem_sphere_iff_norm.mp hz
      rwa [hdist] at hnorm) hfreq
  let g : ℂ → ℂ := Function.invFunOn f U
  have hleft : ∀ z ∈ U, g (f z) = z := hinj.leftInvOn_invFunOn
  have hright : ∀ w ∈ ball (f b) (r / 2), g w ∈ U ∧ f (g w) = w := by
    intro w hw
    obtain ⟨z, hz, he⟩ := himage hw
    exact Function.invFunOn_pos ⟨z, hball hz, he⟩
  refine ⟨g, ?_, hright⟩
  intro w hw
  obtain ⟨hgw, he⟩ := hright w hw
  have hlocal : ∀ᶠ z in 𝓝 (g w), g (f z) = z := by
    filter_upwards [hUo.mem_nhds hgw] with z hz
    exact hleft z hz
  have hstrict := (hf.analyticAt (hUo.mem_nhds hgw)).hasStrictDerivAt.to_local_left_inverse
    (hne (g w) hgw) hlocal
  rw [he] at hstrict
  exact hstrict.hasDerivAt.differentiableAt.differentiableWithinAt

end GaloisForLFunctions.HTGeometry
