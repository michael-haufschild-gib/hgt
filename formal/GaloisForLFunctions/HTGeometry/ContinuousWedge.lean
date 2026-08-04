import GaloisForLFunctions.HTGeometry.MultilinearFiniteDimensional
import Mathlib.LinearAlgebra.Alternating.DomCoprod

/-!
# The wedge product of continuous alternating forms

The exterior product of two alternating forms on a finite coordinate space is again a continuous
alternating form: mathlib builds the algebraic exterior product as the alternating coproduct into a
tensor product, and on a finite coordinate space every alternating map is continuous.  The product is
bilinear.

* `continuousWedge` : the exterior product of two continuous alternating forms.
* `continuousWedge_add_left`, `continuousWedge_smul_left` : bilinearity.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct

section Wedge

variable {r p q : ℕ}

/-- **The exterior product of two continuous alternating forms** on a finite coordinate space. -/
noncomputable def continuousWedge (α : (Fin r → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (β : (Fin r → ℂ) [⋀^Fin q]→L[ℂ] ℂ) : (Fin r → ℂ) [⋀^Fin (p + q)]→L[ℂ] ℂ :=
  alternatingMapToContinuous
    (AlternatingMap.domDomCongr finSumFinEquiv
      (LinearMap.compAlternatingMap (TensorProduct.lid ℂ ℂ).toLinearMap
        (α.toAlternatingMap.domCoprod β.toAlternatingMap)))

theorem continuousWedge_apply (α : (Fin r → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (β : (Fin r → ℂ) [⋀^Fin q]→L[ℂ] ℂ) (v : Fin (p + q) → (Fin r → ℂ)) :
    continuousWedge α β v =
      (TensorProduct.lid ℂ ℂ)
        ((α.toAlternatingMap.domCoprod β.toAlternatingMap) fun i => v (finSumFinEquiv i)) := rfl

theorem continuousWedge_add_left (α₁ α₂ : (Fin r → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (β : (Fin r → ℂ) [⋀^Fin q]→L[ℂ] ℂ) :
    continuousWedge (α₁ + α₂) β = continuousWedge α₁ β + continuousWedge α₂ β := by
  ext v
  rw [continuousWedge_apply]
  show _ = continuousWedge α₁ β v + continuousWedge α₂ β v
  rw [continuousWedge_apply, continuousWedge_apply]
  have hcoe : (α₁ + α₂).toAlternatingMap = α₁.toAlternatingMap + α₂.toAlternatingMap := rfl
  have hbil : (α₁.toAlternatingMap + α₂.toAlternatingMap).domCoprod β.toAlternatingMap =
      α₁.toAlternatingMap.domCoprod β.toAlternatingMap +
        α₂.toAlternatingMap.domCoprod β.toAlternatingMap := by
    rw [← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply,
      ← AlternatingMap.domCoprod'_apply, ← map_add, TensorProduct.add_tmul]
  rw [hcoe, hbil]
  show (TensorProduct.lid ℂ ℂ) (_ + _) = _
  rw [map_add]
  rfl

theorem continuousWedge_smul_left (c : ℂ) (α : (Fin r → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (β : (Fin r → ℂ) [⋀^Fin q]→L[ℂ] ℂ) :
    continuousWedge (c • α) β = c • continuousWedge α β := by
  ext v
  rw [continuousWedge_apply]
  show _ = c • continuousWedge α β v
  rw [continuousWedge_apply]
  have hcoe : (c • α).toAlternatingMap = c • α.toAlternatingMap := rfl
  have hbil : (c • α.toAlternatingMap).domCoprod β.toAlternatingMap =
      c • (α.toAlternatingMap.domCoprod β.toAlternatingMap) := by
    rw [← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply, ← map_smul,
      TensorProduct.smul_tmul']
  rw [hcoe, hbil]
  show (TensorProduct.lid ℂ ℂ) (c • _) = _
  rw [map_smul]
  rfl

theorem continuousWedge_add_right (α : (Fin r → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (β₁ β₂ : (Fin r → ℂ) [⋀^Fin q]→L[ℂ] ℂ) :
    continuousWedge α (β₁ + β₂) = continuousWedge α β₁ + continuousWedge α β₂ := by
  ext v
  rw [continuousWedge_apply]
  show _ = continuousWedge α β₁ v + continuousWedge α β₂ v
  rw [continuousWedge_apply, continuousWedge_apply]
  have hcoe : (β₁ + β₂).toAlternatingMap = β₁.toAlternatingMap + β₂.toAlternatingMap := rfl
  have hbil : α.toAlternatingMap.domCoprod (β₁.toAlternatingMap + β₂.toAlternatingMap) =
      α.toAlternatingMap.domCoprod β₁.toAlternatingMap +
        α.toAlternatingMap.domCoprod β₂.toAlternatingMap := by
    rw [← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply,
      ← AlternatingMap.domCoprod'_apply, ← map_add, TensorProduct.tmul_add]
  rw [hcoe, hbil]
  show (TensorProduct.lid ℂ ℂ) (_ + _) = _
  rw [map_add]
  rfl

theorem continuousWedge_smul_right (c : ℂ) (α : (Fin r → ℂ) [⋀^Fin p]→L[ℂ] ℂ)
    (β : (Fin r → ℂ) [⋀^Fin q]→L[ℂ] ℂ) :
    continuousWedge α (c • β) = c • continuousWedge α β := by
  ext v
  rw [continuousWedge_apply]
  show _ = c • continuousWedge α β v
  rw [continuousWedge_apply]
  have hcoe : (c • β).toAlternatingMap = c • β.toAlternatingMap := rfl
  have hbil : α.toAlternatingMap.domCoprod (c • β.toAlternatingMap) =
      c • (α.toAlternatingMap.domCoprod β.toAlternatingMap) := by
    rw [← AlternatingMap.domCoprod'_apply, ← AlternatingMap.domCoprod'_apply, ← map_smul,
      TensorProduct.tmul_smul]
  rw [hcoe, hbil]
  show (TensorProduct.lid ℂ ℂ) (c • _) = _
  rw [map_smul]
  rfl

end Wedge

end GaloisForLFunctions.HTGeometry
