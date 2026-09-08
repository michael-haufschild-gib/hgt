import GaloisForLFunctions.HTGeometry.HilbertFiniteProjectionCompact
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support

/-! Smooth finite tensor coefficients approximate a compact Hilbert-valued radial family and its derivative. -/
open Filter Topology Set
open scoped ContDiff
namespace GaloisForLFunctions.HTGeometry
noncomputable section
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
  (b : HilbertBasis ι ℂ E)

theorem hilbertFiniteProjection_deriv (s : Finset ι) (F : ℝ → E)
    (hF : Differentiable ℝ F) (t : ℝ) :
    deriv (fun r => hilbertFiniteProjection b s (F r)) t =
      hilbertFiniteProjection b s (deriv F t) :=
  (((hilbertFiniteProjection b s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hF t).hasDerivAt).deriv

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem hilbertFiniteProjection_family_uniform (F : ℝ → E) (hF : Continuous F)
    (hK : HasCompactSupport F) :
    TendstoUniformly (fun s : Finset ι => fun t => hilbertFiniteProjection b s (F t)) F atTop := by
  rw [← tendstoUniformlyOn_univ]
  apply ((hilbertFiniteProjection_uniformOn_compact b (range F)
    (hK.isCompact_range hF)).comp F).mono
  intro t _
  exact ⟨t,rfl⟩

theorem hilbertFiniteProjection_family_deriv_uniform (F : ℝ → E)
    (hF : ContDiff ℝ ∞ F) (hK : HasCompactSupport F) :
    TendstoUniformly (fun s : Finset ι => deriv (fun t => hilbertFiniteProjection b s (F t)))
      (deriv F) atTop := by
  have he (s : Finset ι) : deriv (fun t => hilbertFiniteProjection b s (F t)) =
      fun t => hilbertFiniteProjection b s (deriv F t) :=
    funext (hilbertFiniteProjection_deriv b s F (hF.differentiable (by simp)))
  simp_rw [he]
  exact hilbertFiniteProjection_family_uniform b (deriv F)
    (hF.continuous_deriv (by simp)) hK.deriv

def hilbertRadialCoefficient (F : ℝ → E) (i : ι) : ℝ → ℂ :=
  fun t => inner ℂ (b i) (F t)

theorem hilbertRadialCoefficient_smooth (F : ℝ → E) (hF : ContDiff ℝ ∞ F) (i : ι) :
    ContDiff ℝ ∞ (hilbertRadialCoefficient b F i) :=
  ((innerSL ℂ (b i)).restrictScalars ℝ).contDiff.comp hF

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem hilbertRadialCoefficient_support (F : ℝ → E) (i : ι) :
    tsupport (hilbertRadialCoefficient b F i) ⊆ tsupport F := by
  apply closure_mono
  intro t ht he
  exact ht (by simp [hilbertRadialCoefficient,he])

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem hilbertRadialCoefficient_compact (F : ℝ → E) (hK : HasCompactSupport F) (i : ι) :
    HasCompactSupport (hilbertRadialCoefficient b F i) :=
  hK.of_isClosed_subset isClosed_closure (hilbertRadialCoefficient_support b F i)

theorem hilbertRadialCoefficient_deriv (F : ℝ → E) (hF : Differentiable ℝ F) (i : ι) (t : ℝ) :
    deriv (hilbertRadialCoefficient b F i) t = inner ℂ (b i) (deriv F t) :=
  (((innerSL ℂ (b i)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hF t).hasDerivAt).deriv

end
end GaloisForLFunctions.HTGeometry
