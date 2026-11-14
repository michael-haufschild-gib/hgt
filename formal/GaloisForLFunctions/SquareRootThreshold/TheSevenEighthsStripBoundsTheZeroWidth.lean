import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.QuasiRiemannHypothesis

/-!
# The zero width is at most three eighths

The seven-eighths zero-free half-plane and functional reflection bound the
symmetric width of the actual zeta divisor by `3/8`.
-/

namespace GaloisForLFunctions.SquareRootThreshold

/-- The seven-eighths zero-free half-plane bounds the symmetric zero width by `3/8`. -/
theorem zetaZeroWidth_le_three_eighths : zetaZeroWidth ≤ 3 / 8 := by
  refine (zetaZeroWidth_le_iff_re_le (by norm_num : (0 : ℝ) ≤ 3 / 8)).2 ?_
  intro ρ hρ
  obtain ⟨hz, hpos, -⟩ := (show Zeta23.IsNontrivialZero ρ from hρ)
  have hstrip := MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_zero_mem_quasiRH_strip
    hpos hz
  linarith only [hstrip.2]

#print axioms zetaZeroWidth_le_three_eighths

end GaloisForLFunctions.SquareRootThreshold
