/-
Coordinate Laplacian identities adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicDirichletForm
import GaloisForLFunctions.MetaplecticMobiusDescent.Sobolev.ComplexWeakGradientGraph

/-!
# Axis and Euclidean descriptions of the hyperbolic Laplacian

Differentiate affine coordinate lines to identify iterated axis derivatives
with the Fréchet differential expression on positive-height half-space.
The positive Laplacian is minus the axis expression.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def axisSlice (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) (j : Fin 3) : ℝ → ℂ :=
  fun t => f (Function.update p j t)

def axisLaplacian (f : SpatialCoordinates → ℂ) (p : SpatialCoordinates) : ℂ :=
  (p 2:ℂ)^2 * (∑ j : Fin 3, deriv (deriv (axisSlice f p j)) (p j)) -
    (p 2:ℂ)*deriv (axisSlice f p 2) (p 2)

def euclideanAxisPath (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) : EuclideanSpatial :=
  WithLp.toLp 2 (Function.update p.ofLp j t)

lemma euclideanAxisPath_affine (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    euclideanAxisPath p j t=p+(t-p j)•euclideanCoordinateVector j := by
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext k
  by_cases hk : k=j
  · subst k
    simp [euclideanAxisPath,euclideanCoordinateVector]
  · simp [euclideanAxisPath,euclideanCoordinateVector,Function.update,hk]

lemma euclideanAxisPath_self (p : EuclideanSpatial) (j : Fin 3) :
    euclideanAxisPath p j (p j)=p := by
  rw [euclideanAxisPath_affine,sub_self,zero_smul,add_zero]

lemma euclideanAxisPath_hasDerivAt (p : EuclideanSpatial) (j : Fin 3) (t : ℝ) :
    HasDerivAt (euclideanAxisPath p j) (euclideanCoordinateVector j) t := by
  have he : euclideanAxisPath p j=(fun t => p+(t-p j)•euclideanCoordinateVector j) :=
    funext (euclideanAxisPath_affine p j)
  rw [he]
  simpa only [sub_zero,one_smul,zero_add,Pi.add_apply,id_eq] using!
    (hasDerivAt_const t p).add (((hasDerivAt_id t).sub_const (p j)).smul_const (euclideanCoordinateVector j))

lemma euclideanAxisSlice_deriv (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (j : Fin 3) (t : ℝ) (hf : DifferentiableAt ℝ f (euclideanAxisPath p j t)) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) t=
      fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j) :=
  (hf.hasFDerivAt.comp_hasDerivAt t (euclideanAxisPath_hasDerivAt p j t)).deriv

lemma euclideanAxisSlice_derivatives (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) (j : Fin 3) :
    deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j) (p j)=
      fderiv ℝ f p (euclideanCoordinateVector j) ∧
    deriv (deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)) (p j)=
      fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p (euclideanCoordinateVector j) := by
  constructor
  · simpa only [euclideanAxisPath_self] using euclideanAxisSlice_deriv f p j (p j)
      (by simpa only [euclideanAxisPath_self] using (hf p hp).differentiableAt (by simp))
  · have hc : ContinuousAt (fun t => euclideanAxisPath p j t 2) (p j) :=
      (by fun_prop : Continuous (fun q : EuclideanSpatial => q 2)).continuousAt.comp
        (euclideanAxisPath_hasDerivAt p j (p j)).continuousAt
    have hpos : 0<euclideanAxisPath p j (p j) 2 := by rw [euclideanAxisPath_self]; exact hp
    have he : deriv (axisSlice (fun q => f (WithLp.toLp 2 q)) p.ofLp j)=ᶠ[𝓝 (p j)]
        (fun t => fderiv ℝ f (euclideanAxisPath p j t) (euclideanCoordinateVector j)) := by
      filter_upwards [hc.eventually_const_lt hpos] with t ht
      exact euclideanAxisSlice_deriv f p j t ((hf _ ht).differentiableAt (by simp))
    rw [he.deriv_eq]
    have hd : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p :=
      (((hf p hp).fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt (by simp)
    have hd' : DifferentiableAt ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j))
        (euclideanAxisPath p j (p j)) := by rwa [euclideanAxisPath_self]
    have hh := hd'.hasFDerivAt.comp_hasDerivAt (p j) (euclideanAxisPath_hasDerivAt p j (p j))
    simpa only [euclideanAxisPath_self,Function.comp_def] using! hh.deriv

def positiveEuclideanLaplacian (f : EuclideanSpatial→ℂ) (p : EuclideanSpatial) : ℂ :=
  -(p 2:ℂ)^2*(∑j : Fin 3,fderiv ℝ (fun q => fderiv ℝ f q (euclideanCoordinateVector j)) p
    (euclideanCoordinateVector j))+(p 2:ℂ)*fderiv ℝ f p (euclideanCoordinateVector 2)

lemma positiveEuclideanLaplacian_eq_axis (f : EuclideanSpatial→ℂ)
    (hf : ∀p,0<p 2→ContDiffAt ℝ ∞ f p) (p : EuclideanSpatial) (hp : 0<p 2) :
    positiveEuclideanLaplacian f p=-axisLaplacian (fun q => f (WithLp.toLp 2 q)) p.ofLp := by
  unfold positiveEuclideanLaplacian axisLaplacian
  simp only [(euclideanAxisSlice_derivatives f hf p hp _).1,(euclideanAxisSlice_derivatives f hf p hp _).2]
  ring

lemma positiveEuclideanLaplacian_congr (f g : EuclideanSpatial→ℂ) (p : EuclideanSpatial)
    (he : f=ᶠ[𝓝 p]g) : positiveEuclideanLaplacian f p=positiveEuclideanLaplacian g p := by
  have hd (j : Fin 3) : (fun q => fderiv ℝ f q (euclideanCoordinateVector j))=ᶠ[𝓝 p]
      (fun q => fderiv ℝ g q (euclideanCoordinateVector j)) :=
    (he.fderiv (𝕜 := ℝ)).mono (fun q hq => congrArg (fun d => d (euclideanCoordinateVector j)) hq)
  simp only [positiveEuclideanLaplacian,he.fderiv_eq,(hd _).fderiv_eq]

#print axioms positiveEuclideanLaplacian_eq_axis
#print axioms positiveEuclideanLaplacian_congr
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
