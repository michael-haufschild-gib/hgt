import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Higher Fréchet jets under affine automorphisms

Mathlib supplies the higher chain rule for precomposition by a continuous linear map and the
translation law for iterated Fréchet derivatives.  This module combines those two results for a
continuous affine automorphism.  Its linear part acts by a continuous linear equivalence on every
homogeneous jet space, so affine precomposition changes jet coordinates invertibly.
-/

open Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The continuous linear part of a continuous affine equivalence between complex normed spaces. -/
def continuousLinearEquivOfContinuousAffineEquiv (e : E ≃ᴬ[ℂ] E) : E ≃L[ℂ] E where
  toLinearEquiv := e.linear
  continuous_toFun := e.toContinuousAffineMap.contLinear.continuous
  continuous_invFun := by
    simpa using! e.symm.toContinuousAffineMap.contLinear.continuous

@[simp]
theorem coe_continuousLinearEquivOfContinuousAffineEquiv (e : E ≃ᴬ[ℂ] E) :
    ((continuousLinearEquivOfContinuousAffineEquiv e : E ≃L[ℂ] E) : E → E) =
      e.toContinuousAffineMap.contLinear := by
  rfl

@[simp]
theorem continuousLinearEquivOfContinuousAffineEquiv_toContinuousLinearMap
    (e : E ≃ᴬ[ℂ] E) :
    (continuousLinearEquivOfContinuousAffineEquiv e : E →L[ℂ] E) =
      e.toContinuousAffineMap.contLinear := by
  rfl

/-- The invertible change of an order-`i` Fréchet jet induced by the linear part of an affine
automorphism. -/
def continuousAffineJetEquiv (e : E ≃ᴬ[ℂ] E) (i : ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin i ↦ E) F ≃L[ℂ]
      ContinuousMultilinearMap ℂ (fun _ : Fin i ↦ E) F :=
  ContinuousLinearEquiv.continuousMultilinearMapCongrLeft F
    (fun _ ↦ continuousLinearEquivOfContinuousAffineEquiv e)

/-- The iterated Fréchet derivative of `f ∘ e` is the derivative of `f` at `e x`, precomposed in
every tangent argument with the linear part of `e`. -/
theorem iteratedFDeriv_comp_continuousAffineEquiv
    (e : E ≃ᴬ[ℂ] E) {f : E → F} {n : ℕ} (hf : ContDiff ℂ n f)
    (x : E) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℂ i (f ∘ e) x =
      (iteratedFDeriv ℂ i f (e x)).compContinuousLinearMap
        (fun _ ↦ (continuousLinearEquivOfContinuousAffineEquiv e : E ≃L[ℂ] E)) := by
  let L : E →L[ℂ] E := e.toContinuousAffineMap.contLinear
  let a : E := e 0
  have he (y : E) : e y = L y + a := by
    have h := congrFun (ContinuousAffineMap.decomp e.toContinuousAffineMap) y
    simpa [L, a] using h
  have hfun : f ∘ e = (fun z ↦ f (a + z)) ∘ L := by
    funext y
    simp only [Function.comp_apply, he]
    rw [add_comm]
  have hi' : (i : WithTop ℕ∞) ≤ (n : WithTop ℕ∞) := by
    exact_mod_cast hi
  have hfShift : ContDiff ℂ n (fun z ↦ f (a + z)) := by
    simpa only [Function.comp_apply, id_eq] using!
      hf.comp (contDiff_const.add contDiff_id)
  rw [hfun, L.iteratedFDeriv_comp_right (f := fun z ↦ f (a + z)) hfShift x hi']
  rw [iteratedFDeriv_comp_add_left]
  simp only [L, continuousLinearEquivOfContinuousAffineEquiv_toContinuousLinearMap]
  rw [add_comm a, ← he x]

/-- The affine chain rule as an invertible change of higher Fréchet-jet coordinates. -/
theorem iteratedFDeriv_comp_continuousAffineEquiv_eq_jetEquiv
    (e : E ≃ᴬ[ℂ] E) {f : E → F} {n : ℕ} (hf : ContDiff ℂ n f)
    (x : E) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv ℂ i (f ∘ e) x =
      continuousAffineJetEquiv (F := F) e i (iteratedFDeriv ℂ i f (e x)) := by
  simpa [continuousAffineJetEquiv] using
    iteratedFDeriv_comp_continuousAffineEquiv e hf x hi

/-- In particular, affine precomposition never loses an order-`i` jet. -/
theorem continuousAffineJetEquiv_injective (e : E ≃ᴬ[ℂ] E) (i : ℕ) :
    Function.Injective (continuousAffineJetEquiv (F := F) e i) :=
  (continuousAffineJetEquiv (F := F) e i).injective

end

end GaloisForLFunctions.HTGeometry
