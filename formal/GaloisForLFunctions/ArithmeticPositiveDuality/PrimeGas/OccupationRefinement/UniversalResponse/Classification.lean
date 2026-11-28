import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.Phase
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse.UnitPhase

/-! # Classification of continuous probability responses by quantum composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse

open Set ModeCapacities CoherentRay

private theorem norm_power (s : Conserving) {x : ℝ} (hx : 0<x) : ‖power s.val x‖^2=x := by
  rw [power,Complex.norm_exp,sq,←Real.exp_add,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero,s.property]
  rw [show (1/2:ℝ)*Real.log x+1/2*Real.log x=Real.log x by ring,Real.exp_log hx]

private theorem continuous_power (z : ℂ) : ContinuousOn (power z) Shares := by
  have l : ContinuousOn Real.log Shares := fun x hx => (Real.continuousAt_log hx.1.ne').continuousWithinAt
  exact (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn l)).cexp

private theorem from_power {A : ℝ → ℂ} {s : Conserving} (h : ∀ x ∈ Shares, A x=power s.val x) :
    ContinuousOn A Shares ∧ sequential A ∧ born A := by
  refine ⟨(continuous_power s.val).congr h,?_,fun x hx =>
    (congrArg (fun z : ℂ => ‖z‖^2) (h x hx)).trans (norm_power s hx.1)⟩
  intro x hx y hy
  have product : x*y∈Shares := ⟨mul_pos hx.1 hy.1,(mul_le_of_le_one_right hx.1.le hy.2).trans hx.2⟩
  rw [h _ product,h x hx,h y hy,power_mul s.val hx.1 hy.1]

/-- The critical-line powers are exactly the continuous sequential responses
that give isometries for all positive prime capacities. -/
theorem classification (A : ℝ → ℂ) :
    ContinuousOn A Shares ∧ sequential A ∧ conserving A ↔
      ∃! s : Conserving, ∀ x ∈ Shares, A x=power s.val x := by
  constructor
  · rintro ⟨hc,seq,con⟩
    obtain ⟨s,hs⟩ := critical_power hc seq ((conserving_iff_born A seq).mp con)
    exact ⟨s,hs,fun w hw => Subtype.ext (unique_power fun x hx => (hw x hx).symm.trans (hs x hx))⟩
  · rintro ⟨s,hs,_⟩
    obtain ⟨hc,seq,b⟩ := from_power hs
    exact ⟨hc,seq,conserving_of_born b⟩

/-- A single balanced reading suffices for a bounded sequential response. -/
theorem balanced_classification (A : ℝ → ℂ) :
    ContinuousOn A Shares ∧ sequential A ∧ bounded A ∧ balanced A ↔
      ∃! s : Conserving, ∀ x ∈ Shares, A x=power s.val x := by
  rw [←classification,born_iff]
  constructor
  · exact fun ⟨hc,seq,h⟩ => ⟨hc,seq,conserving_of_born h⟩
  · exact fun ⟨hc,seq,h⟩ => ⟨hc,seq,(conserving_iff_born A seq).mp h⟩

#print axioms classification
#print axioms balanced_classification

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.UniversalResponse
