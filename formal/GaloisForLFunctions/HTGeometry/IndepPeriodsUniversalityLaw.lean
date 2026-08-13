import GaloisForLFunctions.HTGeometry.EllipticGammaConeDivisor
import GaloisForLFunctions.HTGeometry.RankThreeMinorWitnesses

/-!
# Integral and rational period independence are the same interface

The cone-divisor API asks for integral independence of `1, a, b`, while the rank-three source API
uses rational linear independence of the same ordered period family.  Fraction-field base change
identifies these hypotheses exactly.  Consequently every source-period witness can discharge the
cone-divisor premise, including the existing explicit pair `i, i√2`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- **Universal period-interface law.**  Integral independence of `1, a, b` is equivalent to
rational linear independence of the elliptic-gamma source-period family. -/
theorem indepPeriods_iff_linearIndependent_ellipticGammaSourcePeriods (a b : ℂ) :
    IndepPeriods a b ↔ LinearIndependent ℚ (ellipticGammaSourcePeriods a b) := by
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
  constructor
  · intro hindep
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hrel : (g 0 : ℂ) + g 1 * a + g 2 * b = 0 := by
      simpa [Fin.sum_univ_three, ellipticGammaSourcePeriods, zsmul_eq_mul] using hg
    obtain ⟨h0, h1, h2⟩ := hindep (g 0) (g 1) (g 2) hrel
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · intro hlinear p q r hrel
    rw [Fintype.linearIndependent_iff] at hlinear
    let g : Fin 3 → ℤ := ![p, q, r]
    have hg : ∑ i, g i • ellipticGammaSourcePeriods a b i = 0 := by
      simpa [g, Fin.sum_univ_three, ellipticGammaSourcePeriods, zsmul_eq_mul] using hrel
    have hzero := hlinear g hg
    exact ⟨hzero 0, hzero 1, hzero 2⟩

/-- The explicit rank-three source pair `i, i√2` unconditionally realizes `IndepPeriods`. -/
theorem indepPeriods_I_I_sqrtTwo :
    IndepPeriods Complex.I (Complex.I * (Real.sqrt 2 : ℂ)) :=
  (indepPeriods_iff_linearIndependent_ellipticGammaSourcePeriods _ _).2
    GaloisForLFunctions.linearIndependent_ellipticGammaSourcePeriods_I_I_sqrtTwo

end GaloisForLFunctions.HTGeometry
