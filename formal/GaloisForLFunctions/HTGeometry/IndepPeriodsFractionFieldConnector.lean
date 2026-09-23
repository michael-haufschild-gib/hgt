import GaloisForLFunctions.HTGeometry.EllipticGammaConeDivisor
import GaloisForLFunctions.HTGeometry.RankThreeMinorWitnesses

/-!
# Integral period independence is rational source-period independence

The cone-divisor hypothesis asks for integral independence of the three periods, while the rank-three
source interface asks for rational independence of the same three numbers.  Both are the finite
independence criterion for the family `1, a, b`, and rational scalars are the fraction field of the
integers, so the two interfaces agree for every pair of complex periods.

Every concrete rational independence witness therefore discharges the integral hypothesis with no
analytic or arithmetic input.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

section PeriodConnector

theorem indepPeriods_iff_linearIndependent_int (a b : ℂ) :
    IndepPeriods a b ↔ LinearIndependent ℤ (ellipticGammaSourcePeriods a b) := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h g hg
    have hexpand : (g 0 : ℂ) + (g 1 : ℂ) * a + (g 2 : ℂ) * b = 0 := by
      simpa [ellipticGammaSourcePeriods, Fin.sum_univ_three, zsmul_eq_mul] using hg
    obtain ⟨h0, h1, h2⟩ := h (g 0) (g 1) (g 2) hexpand
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro h p q r hpqr
    have hg : ∑ i : Fin 3, (![p, q, r] : Fin 3 → ℤ) i • ellipticGammaSourcePeriods a b i = 0 := by
      simpa [ellipticGammaSourcePeriods, Fin.sum_univ_three, zsmul_eq_mul] using hpqr
    have h0 := h ![p, q, r] hg 0
    have h1 := h ![p, q, r] hg 1
    have h2 := h ![p, q, r] hg 2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
    exact ⟨h0, h1, h2⟩

/-- **Period interface identification.**  Integral independence of the three periods is exactly
rational independence of the source-period family. -/
theorem indepPeriods_iff_linearIndependent_ellipticGammaSourcePeriods_indepPeriodsFractionFieldConnector (a b : ℂ) :
    IndepPeriods a b ↔ LinearIndependent ℚ (ellipticGammaSourcePeriods a b) := by
  rw [indepPeriods_iff_linearIndependent_int]
  exact LinearIndependent.iff_fractionRing ℤ ℚ

/-- The unconditional rational witness discharges the integral period hypothesis. -/
theorem indepPeriods_I_I_sqrtTwo_indepPeriodsFractionFieldConnector :
    IndepPeriods Complex.I (Complex.I * (Real.sqrt 2 : ℂ)) :=
  (indepPeriods_iff_linearIndependent_ellipticGammaSourcePeriods_indepPeriodsFractionFieldConnector _ _).mpr
    GaloisForLFunctions.linearIndependent_ellipticGammaSourcePeriods_I_I_sqrtTwo

end PeriodConnector

end GaloisForLFunctions.HTGeometry
