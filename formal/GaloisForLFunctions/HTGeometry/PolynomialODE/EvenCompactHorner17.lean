import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade17
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactHorner18
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactUnitCoordinates

/-! # A single linear-factor Horner step for the compact determinant -/
namespace HTGeometry
noncomputable section
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Drift-degree 0 in this exact Horner remainder. -/
def evenCompactHorner17Coeff0 (t _v : ℝ) : ℝ :=
  (((6900366629758689/2814749767106560000000000000000000000000 : ℝ) +
    (-73782354646251/2814749767106560000000000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ) +
    ((-70362754569/562949953421312000000000000000000000000 : ℝ)*t^(2 : ℕ) +
    (-913113/4503599627370496000000000000000000000 : ℝ)*t^(3 : ℕ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner17Coeff0_eq (t v : ℝ) :
    evenCompactHorner17Coeff0 t v = (evenCompactRelativeGapGrade17Coeff0 v)+
      (191/10+t/10)*(evenCompactHorner18Coeff0 t v)+(-12/5+(16/15)*t)*((0 : ℝ)) := by
  unfold evenCompactHorner17Coeff0 evenCompactRelativeGapGrade17Coeff0 evenCompactHorner18Coeff0
  ring1

/-- Drift-degree 1 in this exact Horner remainder. -/
def evenCompactHorner17Coeff1 (t v : ℝ) : ℝ :=
  ((((-17106825582273/70368744177664000000000000000000000000 : ℝ) +
    (13336127238231/43980465111040000000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((903719687643963/5629499534213120000000000000000000000000 : ℝ)*v^(2 : ℕ) +
    ((-51520348753473/175921860444160000000000000000000000000 : ℝ)*t^(1 : ℕ) +
    (-299945587743/87960930222080000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((601048547559/2814749767106560000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (-190546152753/70368744177664000000000000000000000000 : ℝ)*t^(2 : ℕ) : ℝ) +
    ((-234003879/17592186044416000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) +
    ((-579868821/1125899906842624000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) +
    (-913113/140737488355328000000000000000000000 : ℝ)*t^(3 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner17Coeff1_eq (t v : ℝ) :
    evenCompactHorner17Coeff1 t v = (evenCompactRelativeGapGrade17Coeff1 v)+
      (191/10+t/10)*(evenCompactHorner18Coeff1 t v)+(-12/5+(16/15)*t)*(evenCompactHorner18Coeff0 t v) := by
  unfold evenCompactHorner17Coeff1 evenCompactRelativeGapGrade17Coeff1 evenCompactHorner18Coeff1 evenCompactHorner18Coeff0
  ring1

/-- Drift-degree 2 in this exact Horner remainder. -/
def evenCompactHorner17Coeff2 (t v : ℝ) : ℝ :=
  ((((-17003907940643/87960930222080000000000000000000000000 : ℝ) +
    ((1666598440443/10995116277760000000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (222106345851723/1407374883553280000000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ) +
    (((1528696837269/43980465111040000000000000000000000000 : ℝ)*v^(3 : ℕ) +
    (90889255631403/45035996273704960000000000000000000000000 : ℝ)*v^(4 : ℕ) : ℝ) +
    ((-38497386653927/263882790666240000000000000000000000000 : ℝ)*t^(1 : ℕ) +
    (-85418721627/2199023255552000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((2607660606069/1407374883553280000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
    ((-2126961279/175921860444160000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) +
    (83499748533/45035996273704960000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ) : ℝ) : ℝ) +
    (((-3321376241/219902325555200000000000000000000000 : ℝ)*t^(2 : ℕ) +
    (-78001293/274877906944000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) : ℝ) +
    ((-193289607/17592186044416000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) +
    (-304371/4398046511104000000000000000000000 : ℝ)*t^(3 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner17Coeff2_eq (t v : ℝ) :
    evenCompactHorner17Coeff2 t v = (evenCompactRelativeGapGrade17Coeff2 v)+
      (191/10+t/10)*(evenCompactHorner18Coeff2 t v)+(-12/5+(16/15)*t)*(evenCompactHorner18Coeff1 t v) := by
  unfold evenCompactHorner17Coeff2 evenCompactRelativeGapGrade17Coeff2 evenCompactHorner18Coeff2 evenCompactHorner18Coeff1
  ring1

/-- Drift-degree 3 in this exact Horner remainder. -/
def evenCompactHorner17Coeff3 (t v : ℝ) : ℝ :=
  (((((-109926876528139/296868139499520000000000000000000000000 : ℝ) +
    (-53028925939693/197912092999680000000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((-38683134975799/527765581332480000000000000000000000000 : ℝ)*v^(2 : ℕ) +
    (-161435922413/21990232555520000000000000000000000000 : ℝ)*v^(3 : ℕ) : ℝ) : ℝ) +
    (((2263659684681/5629499534213120000000000000000000000000 : ℝ)*v^(4 : ℕ) +
    (14182604343/112589990684262400000000000000000000000 : ℝ)*v^(5 : ℕ) : ℝ) +
    ((2998431459/562949953421312000000000000000000000000 : ℝ)*v^(6 : ℕ) +
    (-1183589491703/24739011624960000000000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ) : ℝ) : ℝ) +
    ((((-9055385937/343597383680000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
    (-199310549193/43980465111040000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) : ℝ) +
    ((-708987093/5497558138880000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) +
    (27833249511/1407374883553280000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ) : ℝ) : ℝ) +
    (((-970713523/206158430208000000000000000000000000 : ℝ)*t^(2 : ℕ) +
    (-26000431/17179869184000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) : ℝ) +
    ((-64429869/1099511627776000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) +
    (-33819/137438953472000000000000000000000 : ℝ)*t^(3 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner17Coeff3_eq (t v : ℝ) :
    evenCompactHorner17Coeff3 t v = (evenCompactRelativeGapGrade17Coeff3 v)+
      (191/10+t/10)*((0 : ℝ))+(-12/5+(16/15)*t)*(evenCompactHorner18Coeff2 t v) := by
  unfold evenCompactHorner17Coeff3 evenCompactRelativeGapGrade17Coeff3 evenCompactHorner18Coeff2
  ring1

/-- The exact Horner polynomial retains its drift grading. -/
def evenCompactHorner17 (r t v : ℝ) : ℝ :=
  ((evenCompactHorner17Coeff0 t v +
    (r^(1 : ℕ)*evenCompactHorner17Coeff1 t v) : ℝ) +
    ((r^(2 : ℕ)*evenCompactHorner17Coeff2 t v) +
    (r^(3 : ℕ)*evenCompactHorner17Coeff3 t v) : ℝ) : ℝ)

/-- Assemble the checked coefficient identities without expanding their polynomials. -/
theorem evenCompactHorner17_step (r t v : ℝ) :
    evenCompactHorner17 r t v = evenCompactRelativeGapGrade17 r v+
      evenCompactUnitGap r t*evenCompactHorner18 r t v := by
  unfold evenCompactHorner17 evenCompactHorner18
  rw [evenCompactHorner17Coeff0_eq, evenCompactHorner17Coeff1_eq, evenCompactHorner17Coeff2_eq, evenCompactHorner17Coeff3_eq]
  unfold evenCompactRelativeGapGrade17 evenCompactUnitGap
  ring1

end
end HTGeometry
