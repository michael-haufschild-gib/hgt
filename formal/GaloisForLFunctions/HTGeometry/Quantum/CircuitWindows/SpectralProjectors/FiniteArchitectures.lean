import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralProjectors.PolynomialMasks

/-! # Counting fixed-rank Boolean masks across circuit architectures -/

open Finset MvPolynomial
namespace GaloisForLFunctions.HTGeometry.SpectralProjectors
noncomputable section

/-- A finite choice of architectures costs only its cardinality. Each
mask may be realized in the algebraic closure of a different chart. -/
theorem card_masks_in_charts {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    {k d : ℕ} (F : J→I→MvPolynomial (Fin k) ℂ)
    (hd : ∀ j i, F j i∈degreesLE ℂ (Fin k) (multilinearDegreeBound k d))
    (T : Finset (Finset I)) (h : ℕ) (hsize : ∀ A∈T, A.card=h)
    (hit : ∀ A∈T, ∃ j, inImageClosure (F j) (mask A)) :
    T.card≤Fintype.card J*(h*d+1)^k := by
  classical
  let S (j : J) := T.filter fun A => inImageClosure (F j) (mask A)
  have hs (j : J) := card_masks_le (F j) (hd j) (S j) h
    (fun A ha => hsize A (mem_filter.mp ha).1) (fun _ ha => (mem_filter.mp ha).2)
  have hc : T⊆univ.biUnion S := by
    intro A ha
    obtain ⟨j,hj⟩ := hit A ha
    exact mem_biUnion.mpr ⟨j,mem_univ _,mem_filter.mpr ⟨ha,hj⟩⟩
  exact (card_le_card hc).trans ((card_biUnion_le ..).trans (by
    simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum (fun j (_ : j∈univ) => hs j)))

#print axioms card_masks_in_charts
end
end GaloisForLFunctions.HTGeometry.SpectralProjectors
