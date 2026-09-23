import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomOddProfiles
import GaloisForLFunctions.RHTower.ThetaCuspTwoAtomExponentialAdmission
import GaloisForLFunctions.HTGeometry.TwoAtomOddHighReserve

/-!
# Literal two-atom determinant reserves throughout the remaining middle regime

These are the retained source's exact determinants at its actual parameters.
The complete deep-tail transfer is a separate remaining comparison.
-/
namespace RHTower
noncomputable section

/-- Normalized signed odd determinant of the literal two-atom source. -/
def thetaCuspTwoAtomOddDetNormalized (x : ℝ) : ℝ :=
  HilbertMetric.signedEvenHankelThreeDet (thetaCuspTwoAtomScaledEvenJet 1 x)
    (thetaCuspTwoAtomScaledEvenJet 2 x) (thetaCuspTwoAtomScaledEvenJet 3 x)
    (thetaCuspTwoAtomScaledEvenJet 4 x) (thetaCuspTwoAtomScaledEvenJet 5 x)

/-- Normalized leading odd minor of the same literal retained source. -/
def thetaCuspTwoAtomOddHeadNormalized (x : ℝ) : ℝ :=
  thetaCuspTwoAtomScaledEvenJet 1 x*thetaCuspTwoAtomScaledEvenJet 3 x-
    thetaCuspTwoAtomScaledEvenJet 2 x^(2 : ℕ)

/-- Exact polynomial incidence of the retained determinant. -/
theorem thetaCuspTwoAtomOddDetNormalized_eq {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomOddDetNormalized x =
      HTGeometry.twoAtomOddDet (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  unfold thetaCuspTwoAtomOddDetNormalized HTGeometry.twoAtomOddDet
  rw [thetaCuspTwoAtomScaledEvenJet_1_eq_profile hx, thetaCuspTwoAtomScaledEvenJet_2_eq_profile hx,
    thetaCuspTwoAtomScaledEvenJet_3_eq_profile hx, thetaCuspTwoAtomScaledEvenJet_4_eq_profile hx,
    thetaCuspTwoAtomScaledEvenJet_5_eq_profile hx]

/-- Exact polynomial incidence of the retained leading minor. -/
theorem thetaCuspTwoAtomOddHeadNormalized_eq {x : ℝ} (hx : 0 < x) :
    thetaCuspTwoAtomOddHeadNormalized x =
      HTGeometry.twoAtomOddHead (thetaCuspSingleAtomReflectionScale 1 x)
        (Real.exp (-3*thetaCuspSingleAtomReflectionScale 1 x)) := by
  unfold thetaCuspTwoAtomOddHeadNormalized HTGeometry.twoAtomOddHead
  rw [thetaCuspTwoAtomScaledEvenJet_1_eq_profile hx, thetaCuspTwoAtomScaledEvenJet_2_eq_profile hx,
    thetaCuspTwoAtomScaledEvenJet_3_eq_profile hx]

/-- Fifteen billion of actual retained determinant reserve below physical scale five. -/
theorem thetaCuspTwoAtomOddDetNormalized_lower_middle {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 5) :
    15000000000 ≤ thetaCuspTwoAtomOddDetNormalized x := by
  rw [thetaCuspTwoAtomOddDetNormalized_eq (thetaCusp_pos_of_thirtySevenTenths_le hq)]
  exact HTGeometry.twoAtomOddDet_lower_middle hq hqu (Real.exp_pos _).le
    (thetaCuspTwoAtom_lower_envelope_admission hq)

/-- Eighty-five billion of actual retained determinant reserve from scale five through seven. -/
theorem thetaCuspTwoAtomOddDetNormalized_upper_middle {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    85000000000 ≤ thetaCuspTwoAtomOddDetNormalized x := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (x := x) (by linarith)
  rw [thetaCuspTwoAtomOddDetNormalized_eq hx]
  exact HTGeometry.twoAtomOddDet_high_lower hq hqu (Real.exp_pos _).le
    (thetaCuspTwoAtom_high_envelope_admission hq)

/-- The retained leading minor stays below thirty-three thousand on the upper middle interval. -/
theorem thetaCuspTwoAtomOddHeadNormalized_upper_middle {x : ℝ}
    (hq : 5 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    thetaCuspTwoAtomOddHeadNormalized x ≤ 33000 := by
  have hx := thetaCusp_pos_of_thirtySevenTenths_le (x := x) (by linarith)
  rw [thetaCuspTwoAtomOddHeadNormalized_eq hx]
  exact HTGeometry.twoAtomOddHead_high_upper hq hqu (Real.exp_pos _).le
    (thetaCuspTwoAtom_high_envelope_admission hq)

/-- Uniform retained determinant positivity across the full physical middle interval. -/
theorem thetaCuspTwoAtomOddDetNormalized_middle_lower {x : ℝ}
    (hq : 37/10 ≤ thetaCuspSingleAtomReflectionScale 1 x)
    (hqu : thetaCuspSingleAtomReflectionScale 1 x ≤ 7) :
    15000000000 ≤ thetaCuspTwoAtomOddDetNormalized x := by
  by_cases h5 : thetaCuspSingleAtomReflectionScale 1 x ≤ 5
  · exact thetaCuspTwoAtomOddDetNormalized_lower_middle hq h5
  · have ht := thetaCuspTwoAtomOddDetNormalized_upper_middle (le_of_not_ge h5) hqu
    linarith only [ht]

end
end RHTower
