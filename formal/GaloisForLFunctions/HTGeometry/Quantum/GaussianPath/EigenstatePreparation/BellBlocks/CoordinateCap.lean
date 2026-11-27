import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass

/-! # A small spin expectation bounds every component in its measurement basis -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
open SpectralApproximation.MarkedReflections
open private diagonal_sum from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.MarkedMass
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The component at j belongs to one of the two sign sectors, whose
larger mass is half of one plus the absolute reflection expectation. -/
theorem component_cap (V : unitaryGroup I ℂ) (M : Finset I) (i j : I) :
    2*‖V.val i j‖^2 ≤ 1+‖reflection V M i i‖ := by
  let p (k : I) := ‖V.val i k‖^2
  have h := congrArg Complex.re (diagonal_sum V (fun _ => 1) i)
  simp only [diagonal_one,mul_one,(Unitary.mem_iff.mp V.property).2,Matrix.one_apply_eq,
    Complex.one_re,Complex.re_sum,Complex.ofReal_re] at h
  have hsum : (∑ k∈M,p k)+(∑ k∈Mᶜ,p k)=1 := (sum_add_sum_compl M p).trans h.symm
  have hd := reflection_diagonal V M i
  rw [hd,Complex.norm_real,Real.norm_eq_abs]
  change 2*p j≤1+|1-2*∑ k∈M,p k|
  by_cases hj : j∈M
  · have hsub := single_le_sum (f:=p) (fun k _ => sq_nonneg _) hj
    have habs := neg_abs_le (1-2*∑ k∈M,p k)
    linarith only [hsub,habs]
  · have hsub := single_le_sum (f:=p) (fun k _ => sq_nonneg _) (mem_compl.mpr hj)
    have habs := le_abs_self (1-2*∑ k∈M,p k)
    linarith only [hsub,hsum,habs]

#print axioms component_cap
end
end GaloisForLFunctions.HTGeometry.EigenstatePreparation.BellBlocks
