import GaloisForLFunctions.RHTower.WeightedEulerCarrierBlocks
import GaloisForLFunctions.HTGeometry.ReflectedCarrierFunctional

/-!
# The doubled and reflected functionals of a rectangular quadrant carrier

The complex functional of a rectangular carrier is doubled across the real axis by its Schwarz
reflection, pulled back across the critical line by the functional equation, and the difference of
the two is a functional on the total carrier.  Its Cauchy transform is the sum of the doubled
transform and its reflection.

* `RHTower.QuadrantCarrierData.doubled`, `.reflected`, `.total`;
* `RHTower.QuadrantCarrierData.cauchyTransform_total`.
-/

noncomputable section

open Complex Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

namespace QuadrantCarrierData

variable {f₂ : holoQuadrant →L[ℝ] ℝ} (D : QuadrantCarrierData f₂)

/-- The carrier functional, on the upper block. -/
def Lc : C(D.Kc, ℂ) →L[ℂ] ℂ := D.L

/-- The functional doubled across the real axis. -/
def doubled : C(D.Kt, ℂ) →L[ℂ] ℂ :=
  doubledFunctional D.Kc_subset_Kt (fun _ hz => D.conj_mem_Kt hz) D.Lc

/-- The doubled functional pulled back across the critical line. -/
def reflected : C(D.Kt', ℂ) →L[ℂ] ℂ :=
  feReflFunctional (fun _ hz => D.one_sub_mem_Kt' hz) D.doubled

/-- The difference of the two, a functional on the total carrier. -/
def total : C(D.Ktot, ℂ) →L[ℂ] ℂ :=
  D.doubled.comp (precompCLM (inclMap D.Kt_subset_Ktot))
    - D.reflected.comp (precompCLM (inclMap D.Kt'_subset_Ktot))

theorem cauchyTransform_doubled {v : ℂ} (hv : v ∉ D.Kt) :
    cauchyTransform D.doubled v
      = cauchyTransform D.Lc v + (starRingEnd ℂ) (cauchyTransform D.Lc ((starRingEnd ℂ) v)) :=
  cauchyTransform_doubledFunctional D.Kc_subset_Kt (fun _ hz => D.conj_mem_Kt hz) D.Lc hv

theorem cauchyTransform_reflected {v : ℂ} (hv : v ∉ D.Kt') :
    cauchyTransform D.reflected v = -cauchyTransform D.doubled (1 - v) :=
  cauchyTransform_feReflFunctional (fun _ hz => D.one_sub_mem_Kt' hz) D.doubled hv

theorem cauchyTransform_total {v : ℂ} (hv : v ∉ D.Ktot) :
    cauchyTransform D.total v
      = cauchyTransform D.doubled v + cauchyTransform D.doubled (1 - v) := by
  have hvt : v ∉ D.Kt := fun hc => hv (D.Kt_subset_Ktot hc)
  have hvt' : v ∉ D.Kt' := fun hc => hv (D.Kt'_subset_Ktot hc)
  have hker : cauchyTransform D.total v
      = cauchyTransform (D.doubled.comp (precompCLM (inclMap D.Kt_subset_Ktot))) v
        - cauchyTransform (D.reflected.comp (precompCLM (inclMap D.Kt'_subset_Ktot))) v := by
    rw [cauchyTransform_eq _ hv, cauchyTransform_eq _ hv, cauchyTransform_eq _ hv, total]
    rfl
  rw [hker, cauchyTransform_comp_precompCLM D.Kt_subset_Ktot D.doubled hv,
    cauchyTransform_comp_precompCLM D.Kt'_subset_Ktot D.reflected hv,
    D.cauchyTransform_reflected hvt', sub_neg_eq_add]

end QuadrantCarrierData

end RHTower
