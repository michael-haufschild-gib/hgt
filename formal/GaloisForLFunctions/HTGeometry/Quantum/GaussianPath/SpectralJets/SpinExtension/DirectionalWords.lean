import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Rank.CoordinateCalculus
import GaloisForLFunctions.HTGeometry.DirectionalMeromorphicField

/-! # Ordered responses along physical matrix perturbations -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
noncomputable section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The first direction is differentiated last, as for coordinate words. -/
def response : List E → (E → ℂ) → E → ℂ
  | [], f => f
  | v::w, f => fun x => deriv (fun t : ℂ => response w f (x+t • v)) 0

theorem response_append (v w : List E) (f : E → ℂ) :
    response (v++w) f = response v (response w f) := by
  induction v with
  | nil => rfl
  | cons i v ih => simp only [List.cons_append,response,ih]

private theorem line_deriv (x v : E) : HasDerivAt (fun t : ℂ => x+t • v) v 0 := by
  simpa using ((hasDerivAt_id (0:ℂ)).smul_const v).const_add x

theorem response_germ (w : List E) {f g : E → ℂ} {x : E} (h : f =ᶠ[𝓝 x] g) :
    response w f =ᶠ[𝓝 x] response w g := by
  induction w with
  | nil => exact h
  | cons v w ih =>
    filter_upwards [ih.eventuallyEq_nhds] with y hy
    have ht : Tendsto (fun t : ℂ => y+t • v) (𝓝 0) (𝓝 y) := by
      simpa using (line_deriv y v).continuousAt.tendsto
    exact (ht.eventually hy).deriv_eq

theorem response_analytic (w : List E) {f : E → ℂ} {x : E} (hf : AnalyticAt ℂ f x) :
    AnalyticAt ℂ (response w f) x := by
  induction w with
  | nil => exact hf
  | cons v w ih =>
    have ha := ((ContinuousLinearMap.apply ℂ ℂ v).analyticAt _).comp ih.fderiv
    apply ha.congr
    filter_upwards [ih.eventually_analyticAt] with y hy
    have hd : HasFDerivAt (response w f) (fderiv ℂ (response w f) y) (y+(0:ℂ) • v) := by
      simpa using hy.differentiableAt.hasFDerivAt
    exact (hd.comp_hasDerivAt 0 (line_deriv y v)).deriv.symm

/-- Restriction to an affine family takes words to their physical perturbations. -/
theorem response_affine (L : E → F) (d : E → F)
    (h : ∀ x v (t : ℂ), L (x+t • v) = L x + t • d v) (w : List E) (f : F → ℂ) (x : E) :
    response w (f ∘ L) x = response (w.map d) f (L x) := by
  induction w generalizing x with
  | nil => rfl
  | cons v w ih => simp only [List.map_cons,response,ih,h]

theorem response_const_mul (c : ℂ) (w : List E) (f : E → ℂ) (x : E) :
    response w (fun y => c*f y) x = c*response w f x := by
  induction w generalizing x with
  | nil => rfl
  | cons v w ih => simp only [response,ih,deriv_const_mul_field]

theorem response_coordinate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : List ι) (f : (ι → ℂ) → ℂ) (x : ι → ℂ) :
    response (w.map (fun i => Pi.single i (1:ℂ))) f x = mixed w f x := by
  have h (i : ι) (z : ι → ℂ) (t : ℂ) : z+t • Pi.single i (1:ℂ)=coordLine z i t := by
    funext j
    by_cases hj : j=i <;> simp [coordLine,Pi.single_apply,hj]
  induction w generalizing x with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons,response,mixed,h,ih]

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension
