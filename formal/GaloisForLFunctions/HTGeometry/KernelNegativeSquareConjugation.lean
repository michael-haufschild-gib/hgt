import GaloisForLFunctions.HTGeometry.KernelNegativeSquareCongruence

open Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*}

/-- Coefficientwise complex conjugation of a finitely supported packet. -/
def finsuppConjugate (f : X →₀ ℂ) : X →₀ ℂ where
  support := f.support
  toFun := fun x => (starRingEnd ℂ) (f x)
  mem_support_toFun := by
    intro x
    simp

@[simp]
theorem finsuppConjugate_apply (f : X →₀ ℂ) (x : X) :
    finsuppConjugate f x = (starRingEnd ℂ) (f x) := rfl

theorem finsuppConjugate_sum_conj_smul {r : ℕ}
    (c : Fin r → ℂ) (d : Fin r → X →₀ ℂ) :
    finsuppConjugate (∑ i, (starRingEnd ℂ) (c i) • d i) =
      ∑ i, c i • finsuppConjugate (d i) := by
  ext x
  simp [finsuppConjugate_apply]

theorem kernelForm_conjugate_congruence
    (K : X → X → ℂ) (f g : X →₀ ℂ) :
    kernelForm (fun x y => (starRingEnd ℂ) (K x y))
        (finsuppConjugate f) (finsuppConjugate g) =
      (starRingEnd ℂ) (kernelForm K f g) := by
  classical
  rw [kernelForm, kernelForm]
  change f.sum (fun y dy => g.sum fun x dx =>
      (starRingEnd ℂ) ((starRingEnd ℂ) dy) *
        (starRingEnd ℂ) dx * (starRingEnd ℂ) (K x y)) =
    (starRingEnd ℂ) (f.sum fun y dy => g.sum fun x dx =>
      (starRingEnd ℂ) dy * dx * K x y)
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro y _
  rw [map_finsuppSum]
  apply Finsupp.sum_congr
  intro x _
  simp only [map_mul]

theorem hasFiniteKernelNegativeDimension_conjugate
    (K : X → X → ℂ) (r : ℕ) :
    HasFiniteKernelNegativeDimension K r →
      HasFiniteKernelNegativeDimension
        (fun x y => (starRingEnd ℂ) (K x y)) r := by
  intro hneg
  obtain ⟨d, hd⟩ := hneg
  let dstar : Fin r → X →₀ ℂ := fun i => finsuppConjugate (d i)
  refine ⟨dstar, ?_⟩
  intro c hc
  let cstar : Fin r → ℂ := fun i => (starRingEnd ℂ) (c i)
  have hcstar : cstar ≠ 0 := by
    intro hzero
    apply hc
    funext i
    have hi := congrFun hzero i
    have histar := congrArg (starRingEnd ℂ) hi
    simpa [cstar] using histar
  have hsum : ∑ i, c i • dstar i =
      finsuppConjugate (∑ i, cstar i • d i) := by
    exact (finsuppConjugate_sum_conj_smul c d).symm
  rw [hsum, kernelForm_conjugate_congruence]
  change (kernelForm K (∑ i, cstar i • d i)
    (∑ i, cstar i • d i)).re < 0
  exact hd cstar hcstar

theorem hasFiniteKernelNegativeDimension_conjugate_iff
    (K : X → X → ℂ) (r : ℕ) :
    HasFiniteKernelNegativeDimension
        (fun x y => (starRingEnd ℂ) (K x y)) r ↔
      HasFiniteKernelNegativeDimension K r := by
  constructor
  · intro hneg
    have h := hasFiniteKernelNegativeDimension_conjugate
      (fun x y => (starRingEnd ℂ) (K x y)) r hneg
    simpa using h
  · exact hasFiniteKernelNegativeDimension_conjugate K r

end

end GaloisForLFunctions.HTGeometry
