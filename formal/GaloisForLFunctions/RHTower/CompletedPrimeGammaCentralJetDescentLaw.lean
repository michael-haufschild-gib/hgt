import GaloisForLFunctions.RHTower.CompletedPrimeGammaMovingComplexHankel

/-!
# Real-even central jet law for the completed prime--Gamma Hankel determinant

The explicit completed odd-logarithmic-derivative Hankel determinant carries two independent
involutions: functional-equation reflection and Schwarz conjugation.  Joining them at their common
fixed point shows that its entire central jet is real and supported only in even degrees.

This is stronger than evenness of the central vanishing order: it constrains every Taylor
coefficient, including when the determinant does not vanish.
-/

open Complex

namespace RHTower

noncomputable section

/-- Schwarz equivariance propagates through every derivative of the explicit completed-source
Hankel determinant. -/
theorem completedOddLogDerivHankelDet_iteratedDeriv_conj
    (n m : ℕ) (sigma : ℂ) :
    iteratedDeriv m (completedOddLogDerivHankelDet n) ((starRingEnd ℂ) sigma) =
      (starRingEnd ℂ)
        (iteratedDeriv m (completedOddLogDerivHankelDet n) sigma) := by
  have hfun :
      (starRingEnd ℂ) ∘ completedOddLogDerivHankelDet n ∘ (starRingEnd ℂ) =
        completedOddLogDerivHankelDet n := by
    funext z
    simp only [Function.comp_apply]
    rw [completedOddLogDerivHankelDet_conj, Complex.conj_conj]
  have hd := iteratedDeriv_conj_conj (completedOddLogDerivHankelDet n) m
  rw [hfun] at hd
  have hval := congrFun hd ((starRingEnd ℂ) sigma)
  simpa only [Function.comp_apply, Complex.conj_conj] using hval

/-- Every central Taylor coefficient of the explicit completed-source Hankel determinant is real. -/
theorem completedOddLogDerivHankelDet_centralJet_im
    (n m : ℕ) :
    (iteratedDeriv m (completedOddLogDerivHankelDet n) (1 / 2 : ℂ)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  have h := completedOddLogDerivHankelDet_iteratedDeriv_conj n m (1 / 2 : ℂ)
  have hc : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    have hcast : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by norm_num
    rw [hcast]
    exact Complex.conj_ofReal _
  rw [hc] at h
  exact h.symm

/-- Every odd central Taylor coefficient vanishes by functional-equation reflection. -/
theorem completedOddLogDerivHankelDet_centralJet_eq_zero_of_odd
    (n m : ℕ) (hm : Odd m) :
    iteratedDeriv m (completedOddLogDerivHankelDet n) (1 / 2 : ℂ) = 0 := by
  have hfun :
      (fun sigma : ℂ => completedOddLogDerivHankelDet n (1 - sigma)) =
        completedOddLogDerivHankelDet n := by
    funext sigma
    exact completedOddLogDerivHankelDet_one_sub n sigma
  have hd := congrArg (fun f : ℂ → ℂ =>
      iteratedDeriv m f (1 / 2 : ℂ)) hfun
  change iteratedDeriv m
      (fun sigma : ℂ => completedOddLogDerivHankelDet n (1 - sigma)) (1 / 2 : ℂ) =
    iteratedDeriv m (completedOddLogDerivHankelDet n) (1 / 2 : ℂ) at hd
  rw [congrFun
    (iteratedDeriv_comp_const_sub m (completedOddLogDerivHankelDet n) 1)
      (1 / 2 : ℂ)] at hd
  rw [show (1 - (1 / 2 : ℂ)) = 1 / 2 by norm_num, hm.neg_one_pow] at hd
  linear_combination (-1 / 2 : ℂ) * hd

/-- **Universal central-jet law.**  The completed prime--Gamma Hankel determinant has a real-even
central jet: every coefficient is real, and every odd coefficient is zero. -/
theorem completedOddLogDerivHankelDet_centralJet_real_even_law
    (n m : ℕ) :
    (iteratedDeriv m (completedOddLogDerivHankelDet n) (1 / 2 : ℂ)).im = 0 ∧
      (Odd m →
        iteratedDeriv m (completedOddLogDerivHankelDet n) (1 / 2 : ℂ) = 0) := by
  exact ⟨completedOddLogDerivHankelDet_centralJet_im n m,
    completedOddLogDerivHankelDet_centralJet_eq_zero_of_odd n m⟩

end

end RHTower
