import GaloisForLFunctions.HTGeometry.NevLeafInfinityCauchyMoebius
import GaloisForLFunctions.HTGeometry.NevExtremalFamily
import GaloisForLFunctions.HTGeometry.AnalyticNevanlinnaCarrierBridge

/-!
# The classical analytic Nevanlinna carrier family, constructed

The four limiting entries `A, B, C, D` are entire, restrict on the real axis to the entries of the
classical Nevanlinna matrix, and satisfy `A D − B C = 1`.  The Weyl-disc closed form evaluates the
Cauchy transform of every leaf as the Möbius image of its parameter.  In the carrier convention
`(a, b, c, d) = (−A, C, B, −D)` these are exactly the fields of
`ClassicalAnalyticNevanlinnaCarrierFamily`, so an indeterminate moment problem carries one with no
analytic input left outstanding.
-/

open scoped BigOperators
open MeasureTheory OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- **The classical analytic Nevanlinna carrier family of an indeterminate moment problem.** -/
noncomputable def analyticNevCarrierFamily (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    GaloisForLFunctions.HTGeometry.ClassicalAnalyticNevanlinnaCarrierFamily s where
  base := nevExtremalFamily h h0b h0
  a := fun z => -nevAinf s z
  b := nevCinf s
  c := nevBinf s
  d := fun z => -nevDinf s z
  differentiable_a := (nevanlinna_entire_unimodular h h0b).1.neg
  differentiable_b := (nevanlinna_entire_unimodular h h0b).2.2.1
  differentiable_c := (nevanlinna_entire_unimodular h h0b).2.1
  differentiable_d := (nevanlinna_entire_unimodular h h0b).2.2.2.1.neg
  det_one := by
    intro z
    have hdet := (nevanlinna_entire_unimodular h h0b).2.2.2.2 z
    linear_combination hdet
  a_real := by
    intro x
    show -nevAinf s ((x : ℝ) : ℂ) = ((-nevArealInf s x : ℝ) : ℂ)
    rw [nevAinf_ofReal]
    push_cast
    ring
  b_real := by
    intro x
    show nevCinf s ((x : ℝ) : ℂ) = ((nevCrealInf s x : ℝ) : ℂ)
    rw [nevCinf_ofReal]
  c_real := by
    intro x
    show nevBinf s ((x : ℝ) : ℂ) = ((nevBrealInf s x : ℝ) : ℂ)
    rw [nevBinf_ofReal]
  d_real := by
    intro x
    show -nevDinf s ((x : ℝ) : ℂ) = ((-nevDrealInf s x : ℝ) : ℂ)
    rw [nevDinf_ofReal]
    push_cast
    ring
  finite_cauchy := by
    intro tau z hz
    have hz' : z.im ≠ 0 := hz
    have hkey := cauchyTransform_nevLeaf_eq_moebius h h0b h0 tau hz'
    have hden := nevInf_denominator_ne_zero h h0b h0 tau hz'
    have hshape : -nevAinf s z * (tau : ℂ) + nevCinf s z
        = -(nevAinf s z * (tau : ℂ) - nevCinf s z) := by ring
    have hshape' : nevBinf s z * (tau : ℂ) + -nevDinf s z
        = nevBinf s z * (tau : ℂ) - nevDinf s z := by ring
    show (∫ x, ((x : ℂ) - z)⁻¹
        ∂((nevExtremalFamily h h0b h0).leaf (tau : OnePoint ℝ) : Measure ℝ)) = _
    rw [nevExtremalFamily_leaf, hkey, hshape, hshape']
  infinity_cauchy := by
    intro z hz _
    have hz' : z.im ≠ 0 := hz
    show (∫ x, ((x : ℂ) - z)⁻¹
        ∂((nevExtremalFamily h h0b h0).leaf ∞ : Measure ℝ)) = _
    rw [nevExtremalFamily_leaf]
    exact cauchyTransform_nevLeafInf_eq_ratio h h0b h0 hz'

/-- **Existence of the classical analytic carrier family.**  A positive definite normalised moment
sequence whose kernel is bounded at a point carries a classical analytic Nevanlinna carrier
family. -/
theorem exists_classicalAnalyticNevanlinnaCarrierFamily (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    Nonempty (GaloisForLFunctions.HTGeometry.ClassicalAnalyticNevanlinnaCarrierFamily s) :=
  ⟨analyticNevCarrierFamily h h0b h0⟩

@[simp] theorem analyticNevCarrierFamily_base (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (analyticNevCarrierFamily h h0b h0).base = nevExtremalFamily h h0b h0 := rfl

@[simp] theorem analyticNevCarrierFamily_a (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (analyticNevCarrierFamily h h0b h0).a = fun z => -nevAinf s z := rfl

@[simp] theorem analyticNevCarrierFamily_b (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (analyticNevCarrierFamily h h0b h0).b = nevCinf s := rfl

@[simp] theorem analyticNevCarrierFamily_c (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (analyticNevCarrierFamily h h0b h0).c = nevBinf s := rfl

@[simp] theorem analyticNevCarrierFamily_d (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (analyticNevCarrierFamily h h0b h0).d = fun z => -nevDinf s z := rfl

end HTGeometry
