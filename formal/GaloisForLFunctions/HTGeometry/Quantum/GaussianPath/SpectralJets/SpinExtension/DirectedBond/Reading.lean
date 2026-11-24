import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.SpinExtension.DirectedBond.WordLimits
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # The two response matrices associated to a terminal Pauli control -/
open Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The anchor row is constant. Every other row ends with one or two derivatives
in the last field, after the derivatives in its prefix word. -/
def readings (k : I) (w : I → List E) (j : Bool) (f : I → E × ℂ → ℂ) : Matrix I I ℂ :=
  of fun i l => if i=k then 1 else response (extendWord j (w i)) (f l) 0

/-- Even rows lift with equal signs, odd rows with opposite signs.
The old anchor in the odd half becomes the new endpoint alone. -/
def nextWords (k : I) (w : I → List E) : I⊕I → List (E × ℂ) :=
  Sum.elim (fun i => if i=k then [] else extendWord true (w i))
    (fun i => if i=k then [] else extendWord false (w i))

/-- A nonzero multiplier for every row preserves the determinant test. -/
theorem weighted_det_ne (A : Matrix I I ℂ) (hA : A.det≠0) (c : I→ℂ) (hc : ∀ i, c i≠0) :
    (of fun i j => c i*A i j).det≠0 := by
  have he : (of fun i j => c i*A i j)=diagonal c*A := by
    ext i j
    simp only [of_apply,diagonal_mul]
  rw [he,det_mul,det_diagonal]
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => hc i) hA

/-- The finite rank test is unchanged when the terminal field is read
in physical units instead of units of the spin splitting. -/
theorem readings_scaled_ne (k : I) (w : I→List E) (j : Bool) (F : I→E × ℂ → ℂ)
    {u : ℂ} (hu : u≠0) (hd : (readings k w j F).det≠0) :
    (readings k w j (fun l p => F l (p.1,u*p.2))).det≠0 := by
  let c (i : I) : ℂ := if i=k then 1 else u^order j
  have hc (i : I) : c i≠0 := by
    by_cases h : i=k <;> simp [c,h,hu]
  have he : readings k w j (fun l p => F l (p.1,u*p.2)) =
      of (fun i l => c i*readings k w j F i l) := by
    ext i l
    by_cases h : i=k <;> simp [readings,c,h,read_scaled]
  rw [he]
  exact weighted_det_ne _ hd c hc

end
end GaloisForLFunctions.HTGeometry.SpectralJets.SpinExtension.DirectedBond
