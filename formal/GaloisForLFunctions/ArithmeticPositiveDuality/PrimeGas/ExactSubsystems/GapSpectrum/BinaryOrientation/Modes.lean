import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.MarkedIdealSeries

/-! # Common prime occupations, unpaired quanta, and a binary orientation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation

abbrev Bose := Nat.Primes →₀ ℕ
abbrev Binary := Nat.Primes →₀ Fin 2

/-- The binary quantum is present precisely when the second copy has excess occupation.
After removing that quantum, the excess is an unconstrained bosonic occupation. -/
def mode : (ℕ × ℕ) ≃ ℕ × ℕ × Fin 2 where
  toFun q := if q.1 < q.2 then (q.1,q.2-q.1-1,1) else (q.2,q.1-q.2,0)
  invFun v := if v.2.2 = 0 then (v.1+v.2.1,v.1) else (v.1,v.1+v.2.1+1)
  left_inv := by
    rintro ⟨a,b⟩
    by_cases hab : a < b
    · simp only [if_pos hab,one_ne_zero,if_false,Prod.mk.injEq,true_and]
      omega
    · simp only [if_neg hab,if_true,Prod.mk.injEq,and_true]
      omega
  right_inv := by
    rintro ⟨c,r,b⟩
    fin_cases b
    · simp [show ¬c+r<c by omega]
    · simp [show c<c+r+1 by omega]
      omega

private theorem mode_zero : mode 0 = 0 := rfl

theorem common_mode (a b : ℕ) : (mode (a,b)).1 = min a b := by
  by_cases h : a < b
  · simp [mode,h,min_eq_left h.le]
  · simp [mode,h,min_eq_right (le_of_not_gt h)]

theorem orientation_iff (a b : ℕ) : (mode (a,b)).2.2 = 1 ↔ a < b := by
  by_cases h : a < b <;> simp [mode,h]

theorem mode_total (a b : ℕ) :
    a+b = (mode (a,b)).1+(mode (a,b)).1+(mode (a,b)).2.1+(mode (a,b)).2.2.val := by
  by_cases h : a < b <;> simp [mode,h] <;> omega

open MetaplecticMobiusDescent.CubicEisenstein.ProbePhysical in
/-- The independently chosen normal coordinates have finite prime support in both directions. -/
def occupations : (Bose × Bose) ≃ Bose × Bose × Binary :=
  finsuppPairEquiv.trans
    ((Finsupp.mapRange.equiv mode mode_zero).trans
      (finsuppPairEquiv.symm.trans
        (Equiv.prodCongr (Equiv.refl _) finsuppPairEquiv.symm)))

theorem occupations_at (q : Bose × Bose) (p : Nat.Primes) :
    ((occupations q).1 p,(occupations q).2.1 p,(occupations q).2.2 p) = mode (q.1 p,q.2 p) := rfl

/-- Binary occupations embedded in the ordinary number basis. -/
def binaryOccupations (b : Binary) : Bose := b.mapRange Fin.val rfl

theorem total_occupations (q : Bose × Bose) :
    q.1+q.2 = (occupations q).1+(occupations q).1+(occupations q).2.1+binaryOccupations (occupations q).2.2 := by
  ext p
  exact mode_total (q.1 p) (q.2 p)

theorem diagonal_occupations (a : Bose) : occupations (a,a) = (a,0,0) := by
  apply Prod.ext
  · ext p
    change (mode (a p,a p)).1 = a p
    rw [common_mode,min_self]
  · apply Prod.ext
    · ext p
      change (mode (a p,a p)).2.1 = 0
      simp [mode]
    · apply Finsupp.ext
      intro p
      change (mode (a p,a p)).2.2 = 0
      simp [mode]

#print axioms common_mode
#print axioms orientation_iff
#print axioms mode_total
#print axioms occupations_at
#print axioms total_occupations
#print axioms diagonal_occupations

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.BinaryOrientation
