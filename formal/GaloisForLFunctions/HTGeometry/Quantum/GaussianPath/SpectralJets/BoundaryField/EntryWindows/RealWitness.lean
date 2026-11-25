module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! # Real polynomial witnesses for real-valued spectral evaluations -/

public section
open Polynomial
namespace GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows

/-- On a real-valued polynomial curve, the real parts of the coefficients
give a real polynomial with the same absolute values and no larger degree. -/
theorem real_evaluation_witness (P : ℂ[X]) (h : ∀ x : ℝ, (P.eval (x:ℂ)).im=0) :
    ∃ Q : ℝ[X], Q.natDegree≤P.natDegree ∧ ∀ x : ℝ, |Q.eval x|=‖P.eval (x:ℂ)‖ := by
  let Q : ℝ[X] := Polynomial.ofFinsupp ⟨P.toFinsupp.coeff.mapRange Complex.re (by simp)⟩
  have hc (n : ℕ) : Q.coeff n=(P.coeff n).re := by
    dsimp only [Q]
    rw [Polynomial.coeff_ofFinsupp]
    simp [Polynomial.toFinsupp_apply]
  have hd : Q.natDegree≤P.natDegree := Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
    (fun n hn => by rw [hc,Polynomial.coeff_eq_zero_of_natDegree_lt hn,Complex.zero_re])
  refine ⟨Q,hd,fun x => ?_⟩
  have hv : Q.eval x=(P.eval (x:ℂ)).re := by
    rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd),Polynomial.eval_eq_sum_range,Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => by simp [hc,←Complex.ofReal_pow]
  rw [hv]
  have he : ((P.eval (x:ℂ)).re:ℂ)=P.eval (x:ℂ) := Complex.ext rfl (by simp only [Complex.ofReal_im,h x])
  calc
    _ = ‖(((P.eval (x:ℂ)).re:ℝ):ℂ)‖ := by rw [Complex.norm_real,Real.norm_eq_abs]
    _ = _ := congrArg norm he

end GaloisForLFunctions.HTGeometry.SpectralJets.BoundaryField.EntryWindows
