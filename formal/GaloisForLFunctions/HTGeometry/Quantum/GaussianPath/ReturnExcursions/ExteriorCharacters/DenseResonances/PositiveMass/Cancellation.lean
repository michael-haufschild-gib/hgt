import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass.Bins
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.ExteriorCharacters.ElapsedWindow.Kernel

/-! # Negative real mass needed to cancel positive near-resonances -/

open Finset Complex
open scoped ComplexConjugate symmDiff
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
open ElapsedWindow
noncomputable section
variable {I : Type*} [DecidableEq I]

private def signedTerm (a : Finset I → ℂ) (x : Finset I → ℝ) (w : ℝ) (S T : Finset I) : ℝ :=
  (a S*conj (a T)).re*Real.sinc (w*(x S-x T)/2)

/-- Total magnitude of the negative real terms on macroscopic supports,
including all detunings. -/
def negativeWindow (F : Finset (Finset I)) (a : Finset I → ℂ) (x : Finset I → ℝ) (r : ℕ) (w : ℝ) : ℝ :=
  ∑ S ∈ F, ∑ T ∈ F.filter (fun T => r<(S ∆ T).card), max 0 (-signedTerm a x w S T)

/-- The uncompensated positive mass is a lower bound for the signed sum
on the original window, with exactly the same midpoint and sinc factors. -/
theorem cancellation_bound (F : Finset (Finset I)) (m : Finset I → ℂ) (E : I → ℝ)
    (r : ℕ) (σ w : ℝ) :
    let x (S : Finset I) := ∑ i ∈ S, E i
    let a (S : Finset I) := m S*wave (-(σ+w/2)*x S)
    positiveWindow F a x r w ≤ windowSum F m E r σ w + negativeWindow F a x r w := by
  intro x a
  have he (S T : Finset I) : a S*conj (a T)=
      m S*conj (m T)*wave ((σ+w/2)*(x T-x S)) := by
    unfold a wave
    rw [map_mul,←Complex.exp_conj]
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I]
    rw [show (σ+w/2)*(x T-x S)= (-(σ+w/2)*x S)- (-(σ+w/2)*x T) by ring,
      Complex.ofReal_sub,sub_mul,Complex.exp_sub]
    rw [show ((-(σ+w/2)*x T:ℝ):ℂ)*(-Complex.I)= -(((-(σ+w/2)*x T:ℝ):ℂ)*Complex.I) by ring,
      Complex.exp_neg,div_eq_mul_inv]
    ring
  have hs (S T : Finset I) : signedTerm a x w S T=
      (m S*conj (m T)*wave ((σ+w/2)*(x T-x S))).re*Real.sinc (w*(x T-x S)/2) := by
    rw [signedTerm,he,show w*(x S-x T)/2= -(w*(x T-x S)/2) by ring,Real.sinc_neg]
  have ht : windowSum F m E r σ w=
      ∑ S ∈ F, ∑ T ∈ F.filter (fun T => r<(S ∆ T).card), signedTerm a x w S T := by
    unfold windowSum
    simp only [hs,x]
  rw [ht,negativeWindow,←sum_add_distrib]
  apply sum_le_sum
  intro S _
  rw [←sum_add_distrib]
  let V := F.filter fun T => r<(S ∆ T).card
  let U := F.filter fun T => r<(S ∆ T).card ∧ |w*(x S-x T)|≤1
  have hsub : U⊆V := fun _ hT => mem_filter.mpr ⟨(mem_filter.mp hT).1,(mem_filter.mp hT).2.1⟩
  change (∑ T ∈ U, max 0 (signedTerm a x w S T))≤_
  apply (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => le_max_left ..)).trans
  apply sum_le_sum
  intro T _
  rcases le_total 0 (signedTerm a x w S T) with h|h
  · rw [max_eq_right h,max_eq_left (neg_nonpos.mpr h),add_zero]
  · rw [max_eq_left h,max_eq_right (neg_nonneg.mpr h),add_neg_cancel]

#print axioms cancellation_bound
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.ExteriorCharacters.DenseResonances.PositiveMass
