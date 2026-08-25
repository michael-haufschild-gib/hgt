import GaloisForLFunctions.HTGeometry.RegularizedDeterminantAlgebraicMultiplicity
import GaloisForLFunctions.HTGeometry.CompactHyperplanePerturbation
import GaloisForLFunctions.RHTower.TraceClassOperatorTrace

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt

variable {ι : Type*} [DecidableEq ι]

noncomputable def kernelFredholmOperator (K : ι × ι → ℂ) (hK : IsHS K) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  1 + toOperator hK

noncomputable def kernelFredholmDeterminant (K : ι × ι → ℂ) (hK : IsHS K) : ℂ :=
  entireDet2 (-K) 1 * Complex.exp
    (ContinuousLinearMap.opTrace (toOperator hK))

/-- Exact Fredholm alternative for the ordinary determinant of `I + K`. The exponential trace
correction is zero-free, while the global Hilbert--Carleman determinant detects precisely failure
of invertibility of the compact perturbation. -/
theorem kernelFredholmDeterminant_eq_zero_iff_not_isUnit
    (K : ι × ι → ℂ) (hK : IsHS K) :
    kernelFredholmDeterminant K hK = 0 ↔
      ¬ IsUnit (kernelFredholmOperator K hK) := by
  let hKn : IsHS (-K) := isHS_neg hK
  have hneg : toOperator hKn = -(toOperator hK) := by
    simpa [hKn] using toOperator_neg hK
  rw [kernelFredholmDeterminant, mul_eq_zero]
  simp only [Complex.exp_ne_zero, or_false]
  rw [entireDet2_eq_zero_iff_exists_eigenvector hKn one_ne_zero]
  constructor
  · rintro ⟨w, hw0, hw⟩ hunit
    have hinj : Function.Injective (kernelFredholmOperator K hK) :=
      (ContinuousLinearMap.isUnit_iff_bijective.mp hunit).1
    apply hw0
    apply hinj
    have hTw : toOperator hK w = -w := by
      rw [hneg, ContinuousLinearMap.neg_apply] at hw
      simpa using congrArg Neg.neg hw
    simp [kernelFredholmOperator, hTw]
  · intro hnotunit
    have hnotinj : ¬ Function.Injective (kernelFredholmOperator K hK) := by
      intro hinj
      have hcompact : IsCompactOperator (toOperator hK) :=
        (isHilbertSchmidt_toOperator hK).isCompactOperator
      have hsurj : Function.Surjective (kernelFredholmOperator K hK) := by
        simpa [kernelFredholmOperator] using
          compactPerturbation_one_surjective_of_injective (toOperator hK) hcompact
            (by simpa [kernelFredholmOperator] using hinj)
      exact hnotunit (ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hinj, hsurj⟩)
    rw [injective_iff_map_eq_zero] at hnotinj
    push_neg at hnotinj
    obtain ⟨w, hFw, hw0⟩ := hnotinj
    refine ⟨w, hw0, ?_⟩
    have hTw : toOperator hK w = -w := by
      change w + toOperator hK w = 0 at hFw
      exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hFw)
    rw [hneg, ContinuousLinearMap.neg_apply, hTw]
    simp

end GaloisForLFunctions.HTGeometry
