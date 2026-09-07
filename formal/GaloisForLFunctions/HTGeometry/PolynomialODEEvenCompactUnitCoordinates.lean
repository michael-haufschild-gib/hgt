import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactModel

/-! # Exact coupled unit coordinates for the compact even comparison -/
namespace HTGeometry
noncomputable section

/-- Gap coordinate retains both physical drift bounds. -/
def evenCompactUnitGap (r t : ℝ) : ℝ := 191/10-(12/5)*r+t*(1/10+(16/15)*r)

/-- The exact mass-normalized source value in the coupled coordinates. -/
def evenCompactUnitSourceZero (r t : ℝ) : ℝ := r/24+evenCompactUnitGap r t/16-3/8

/-- The proved full-source correction lower comparison is even in the drift. -/
def evenCompactUnitCorrection (r t : ℝ) : ℝ :=
  evenCompactUnitSourceZero r t*(3*evenCompactUnitSourceZero r t-6/19)

end
end HTGeometry
