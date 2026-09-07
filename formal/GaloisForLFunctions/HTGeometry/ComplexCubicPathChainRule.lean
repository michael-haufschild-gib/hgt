import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace GaloisForLFunctions.HTGeometry.ComplexCubicPath
open Filter Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A cubic field path with independent first, second and third coefficient vectors. -/
def path (q h k l : E) (t : ℂ) : E := q+t • h+t^2 • k+t^3 • l

/-- Actual first derivative of the cubic path. -/
def velocity (h k l : E) (t : ℂ) : E := h+(2*t) • k+(3*t^2) • l

/-- Actual second derivative of the cubic path. -/
def acceleration (k l : E) (t : ℂ) : E := (2 : ℂ) • k+(6*t) • l

/-- The cubic path has the displayed actual first derivative. -/
theorem path_hasDerivAt (q h k l : E) (t : ℂ) :
    HasDerivAt (path q h k l) (velocity h k l t) t := by
  have hd := ((((hasDerivAt_id t).smul_const h).const_add q).add
    (((hasDerivAt_id t).pow 2).smul_const k)).add (((hasDerivAt_id t).pow 3).smul_const l)
  convert! hd using 1
  simp [velocity]

/-- The velocity has the displayed actual derivative. -/
theorem velocity_hasDerivAt (h k l : E) (t : ℂ) :
    HasDerivAt (velocity h k l) (acceleration k l t) t := by
  have hd := ((((hasDerivAt_id t).const_mul 2).smul_const k).const_add h).add
    ((((hasDerivAt_id t).pow 2).const_mul 3).smul_const l)
  convert! hd using 1
  dsimp [acceleration]
  module

/-- The acceleration differentiates to six times the cubic coefficient. -/
theorem acceleration_hasDerivAt (k l : E) (t : ℂ) :
    HasDerivAt (acceleration k l) ((6 : ℂ) • l) t := by
  unfold acceleration
  simpa only [id_eq, mul_one] using (((hasDerivAt_id t).const_mul 6).smul_const l).const_add ((2 : ℂ) • k)

private def firstAlong (f : E → ℂ) (q h k l : E) (t : ℂ) : ℂ :=
  fderiv ℂ f (path q h k l t) (velocity h k l t)

private def secondAlong (f : E → ℂ) (q h k l : E) (t : ℂ) : ℂ :=
  fderiv ℂ (fderiv ℂ f) (path q h k l t) (velocity h k l t) (velocity h k l t) +
    fderiv ℂ f (path q h k l t) (acceleration k l t)

private def thirdAlong (f : E → ℂ) (q h k l : E) (t : ℂ) : ℂ :=
  fderiv ℂ (fderiv ℂ (fderiv ℂ f)) (path q h k l t)
      (velocity h k l t) (velocity h k l t) (velocity h k l t) +
    3 * fderiv ℂ (fderiv ℂ f) (path q h k l t) (velocity h k l t) (acceleration k l t) +
    fderiv ℂ f (path q h k l t) ((6 : ℂ) • l)

private theorem comp_hasDerivAt (f : E → ℂ) (q h k l : E) (t : ℂ)
    (hf : ContDiffAt ℂ 3 f (path q h k l t)) :
    HasDerivAt (fun u => f (path q h k l u)) (firstAlong f q h k l t) t := by
  exact (hf.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt t (path_hasDerivAt q h k l t)

private theorem firstAlong_hasDerivAt (f : E → ℂ) (q h k l : E) (t : ℂ)
    (hf : ContDiffAt ℂ 3 f (path q h k l t)) :
    HasDerivAt (firstAlong f q h k l) (secondAlong f q h k l t) t := by
  have hdf := ((hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hd := (hdf.comp_hasDerivAt t (path_hasDerivAt q h k l t)).clm_apply (velocity_hasDerivAt h k l t)
  exact hd

private theorem secondAlong_hasDerivAt (f : E → ℂ) (q h k l : E) (t : ℂ)
    (hf : ContDiffAt ℂ 3 f (path q h k l t)) :
    HasDerivAt (secondAlong f q h k l) (thirdAlong f q h k l t) t := by
  have hdf := ((hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hB := (((hf.fderiv_right (m := 2) (by norm_num)).fderiv_right (m := 1)
    (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  have hv := velocity_hasDerivAt h k l t
  have hBB := ((hB.comp_hasDerivAt t (path_hasDerivAt q h k l t)).clm_apply hv).clm_apply hv
  have hD := (hdf.comp_hasDerivAt t (path_hasDerivAt q h k l t)).clm_apply (acceleration_hasDerivAt k l t)
  have hs := hf.isSymmSndFDerivAt (by norm_num)
  convert! hBB.add hD using 1
  simp only [thirdAlong, add_apply, Function.comp_apply]
  rw [hs (acceleration k l t) (velocity h k l t)]
  ring

private theorem secondAlong_eq_iteratedDeriv (f : E → ℂ) (q h k l : E) (t : ℂ)
    (hf : ContDiffAt ℂ 3 f (path q h k l t)) :
    iteratedDeriv 2 (fun u => f (path q h k l u)) t = secondAlong f q h k l t := by
  have hn := (path_hasDerivAt q h k l t).continuousAt.tendsto.eventually (hf.eventually (by simp))
  have he : deriv (fun u => f (path q h k l u)) =ᶠ[nhds t] firstAlong f q h k l := by
    filter_upwards [hn] with u hu
    exact (comp_hasDerivAt f q h k l u hu).deriv
  rw [show 2 = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
    he.deriv_eq, (firstAlong_hasDerivAt f q h k l t hf).deriv]

/-- The actual first derivative depends on the linear coefficient of the corrected path. -/
theorem linear_coefficient (f : E → ℂ) (q h k l : E) (hf : ContDiffAt ℂ 3 f q) :
    deriv (fun t => f (path q h k l t)) 0 = fderiv ℂ f q h := by
  have hf0 : ContDiffAt ℂ 3 f (path q h k l 0) := by simpa [path] using hf
  simpa [firstAlong, path, velocity] using (comp_hasDerivAt f q h k l 0 hf0).deriv

/-- Full quadratic coefficient of an actual smooth function along a corrected cubic path. -/
theorem quadratic_coefficient (f : E → ℂ) (q h k l : E) (hf : ContDiffAt ℂ 3 f q) :
    iteratedDeriv 2 (fun t => f (path q h k l t)) 0 / 2 =
      fderiv ℂ f q k + fderiv ℂ (fderiv ℂ f) q h h / 2 := by
  have hf0 : ContDiffAt ℂ 3 f (path q h k l 0) := by simpa [path] using hf
  rw [secondAlong_eq_iteratedDeriv f q h k l 0 hf0]
  simp [secondAlong, path, velocity, acceleration, smul_eq_mul]
  ring

/-- Full cubic coefficient, including the Hessian term with the quadratic field correction. -/
theorem cubic_coefficient (f : E → ℂ) (q h k l : E) (hf : ContDiffAt ℂ 3 f q) :
    iteratedDeriv 3 (fun t => f (path q h k l t)) 0 / 6 =
      fderiv ℂ f q l + fderiv ℂ (fderiv ℂ f) q h k +
        fderiv ℂ (fderiv ℂ (fderiv ℂ f)) q h h h / 6 := by
  have hf0 : ContDiffAt ℂ 3 f (path q h k l 0) := by simpa [path] using hf
  have hn := (path_hasDerivAt q h k l 0).continuousAt.tendsto.eventually (hf0.eventually (by simp))
  have he : iteratedDeriv 2 (fun t => f (path q h k l t)) =ᶠ[nhds (0 : ℂ)]
      secondAlong f q h k l := by
    filter_upwards [hn] with u hu
    exact secondAlong_eq_iteratedDeriv f q h k l u hu
  rw [show 3 = 2+1 from rfl, iteratedDeriv_succ, he.deriv_eq,
    (secondAlong_hasDerivAt f q h k l 0 hf0).deriv]
  simp [thirdAlong, path, velocity, acceleration, smul_eq_mul]
  ring

end
end GaloisForLFunctions.HTGeometry.ComplexCubicPath
