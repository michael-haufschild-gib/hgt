import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.SpectralCoordinates.PhaseFunctions
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.MatrixLevels
import Mathlib.Analysis.Complex.Basic

/-! # Rational entry equations as functions of the relative phases -/

open Matrix MvPolynomial
open scoped ComplexConjugate Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates
noncomputable section
variable {F : Type*} [Field F] [Algebra F ℂ]
variable {I T : Type*} (K : IntermediateField F ℂ) (z : T → I → ℂ)

/-- Real coordinates split into a matrix entry and its conjugate. -/
theorem real_imaginary_mem (hI : Complex.I∈K) (f : T → ℂ) (hf : f∈phaseFunctionRing K z)
    (hc : (fun t => conj (f t))∈phaseFunctionRing K z) :
    (fun t => ((f t).re:ℂ))∈phaseFunctionRing K z ∧ (fun t => ((f t).im:ℂ))∈phaseFunctionRing K z := by
  let S := phaseFunctionRing K z
  let c : T → ℂ := fun t => conj (f t)
  have h2 : (fun _ : T => (2:ℂ)⁻¹)∈S := constant_mem_phaseFunctionRing K z ⟨_,K.inv_mem (K.natCast_mem 2)⟩
  have hi : (fun _ : T => -Complex.I)∈S := constant_mem_phaseFunctionRing K z ⟨_,K.neg_mem hI⟩
  constructor
  · have he : (fun t => ((f t).re:ℂ))=(f+c)*(fun _ => (2:ℂ)⁻¹) := by
      funext t
      change _=(f t+conj (f t))*_
      rw [Complex.add_conj,Complex.ofReal_mul,Complex.ofReal_ofNat]
      ring
    rw [he]
    exact S.mul_mem (S.add_mem hf hc) h2
  · have he : (fun t => ((f t).im:ℂ))=((f-c)*(fun _ => (2:ℂ)⁻¹))*(fun _ => -Complex.I) := by
      funext t
      change _=((f t-conj (f t))*_)*_
      rw [Complex.sub_conj,Complex.ofReal_mul,Complex.ofReal_ofNat]
      linear_combination ((f t).im:ℂ)*Complex.I_sq
    rw [he]
    exact S.mul_mem (S.mul_mem (S.sub_mem hf hc) h2) hi

/-- Every entry polynomial with real coefficients in the phase field is a rational phase function when
the complex entries and their conjugates are such functions. -/
theorem polynomial_mem {R : Type*} [CommRing R] (κ : R →+* ℝ) (hκ : ∀ r, (κ r:ℂ)∈K) {N : ℕ} (U : T → Square (Bits N)) (hI : Complex.I∈K)
    (hU : ∀ i j, (fun t => U t i j)∈phaseFunctionRing K z ∧
      (fun t => conj (U t i j))∈phaseFunctionRing K z) (p : EntryPolynomial N R) :
    (fun t => (entryEval κ (U t) p:ℂ))∈phaseFunctionRing K z := by
  let S := phaseFunctionRing K z
  have hX (i : Bits N × Bits N × Bool) :
      (fun t => (entryEval κ (U t) (MvPolynomial.X i):ℂ))∈S := by
    obtain ⟨i,j,b⟩ := i
    have h := real_imaginary_mem K z hI _ (hU i j).1 (hU i j).2
    cases b
    · simpa only [entryEval,MvPolynomial.eval₂Hom_X',Bool.false_eq_true,if_false] using h.1
    · simpa only [entryEval,MvPolynomial.eval₂Hom_X',if_true] using h.2
  induction p using MvPolynomial.induction_on with
  | C r =>
    simpa only [entryEval,MvPolynomial.eval₂Hom_C] using
      constant_mem_phaseFunctionRing K z ⟨_,hκ r⟩
  | add p q hp hq =>
    simpa only [map_add,Complex.ofReal_add,Pi.add_def] using S.add_mem hp hq
  | mul_X p i hp =>
    simpa only [map_mul,Complex.ofReal_mul,Pi.mul_def] using S.mul_mem hp (hX i)

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates.SpectralCoordinates
