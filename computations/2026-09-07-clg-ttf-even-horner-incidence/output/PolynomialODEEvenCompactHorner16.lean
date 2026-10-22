import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactGapGrade16
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactHorner17
import GaloisForLFunctions.HTGeometry.PolynomialODE.EvenCompactUnitCoordinates

/-! # A single linear-factor Horner step for the compact determinant -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option pp.deepTerms false
set_option pp.maxSteps 1000

/-- Drift-degree 0 in this exact Horner remainder. -/
def evenCompactHorner16Coeff0 (t _v : ℝ) : ℝ :=
  (((-902376566152416801/28147497671065600000000000000000000000000 : ℝ) +
    (-1798015776918813/7036874417766400000000000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ) +
    ((-70489392629823/14073748835532800000000000000000000000000 : ℝ)*t^(2 : ℕ) +
    ((-23040831861/1407374883553280000000000000000000000000 : ℝ)*t^(3 : ℕ) +
    (-913113/45035996273704960000000000000000000000 : ℝ)*t^(4 : ℕ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner16Coeff0_eq (t v : ℝ) :
    evenCompactHorner16Coeff0 t v = (evenCompactRelativeGapGrade16Coeff0 v)+
      (191/10+t/10)*(evenCompactHorner17Coeff0 t v)+(-12/5+(16/15)*t)*((0 : ℝ)) := by
  unfold evenCompactHorner16Coeff0 evenCompactRelativeGapGrade16Coeff0 evenCompactHorner17Coeff0
  ring1

/-- Drift-degree 1 in this exact Horner remainder. -/
def evenCompactHorner16Coeff1 (t v : ℝ) : ℝ :=
  ((((88561762269551409/1759218604441600000000000000000000000000 : ℝ) +
    ((4213001659762521/439804651110400000000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (131493997919907333/56294995342131200000000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ) +
    ((-5172235724060523/1759218604441600000000000000000000000000 : ℝ)*t^(1 : ℕ) +
    ((-30617352782451/879609302220800000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
    (1133320232811501/56294995342131200000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((-191166652464597/1759218604441600000000000000000000000000 : ℝ)*t^(2 : ℕ) +
    ((-130854823047/219902325555200000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) +
    (648322371063/56294995342131200000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) : ℝ) : ℝ) +
    (((-37122303297/70368744177664000000000000000000000000 : ℝ)*t^(3 : ℕ) +
    (-234003879/175921860444160000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) : ℝ) +
    ((-579868821/11258999068426240000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ) +
    (-304371/351843720888320000000000000000000000 : ℝ)*t^(4 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner16Coeff1_eq (t v : ℝ) :
    evenCompactHorner16Coeff1 t v = (evenCompactRelativeGapGrade16Coeff1 v)+
      (191/10+t/10)*(evenCompactHorner17Coeff1 t v)+(-12/5+(16/15)*t)*(evenCompactHorner17Coeff0 t v) := by
  unfold evenCompactHorner16Coeff1 evenCompactRelativeGapGrade16Coeff1 evenCompactHorner17Coeff1 evenCompactHorner17Coeff0
  ring1

/-- Drift-degree 2 in this exact Horner remainder. -/
def evenCompactHorner16Coeff2 (t v : ℝ) : ℝ :=
  (((((10588607985256577/879609302220800000000000000000000000000 : ℝ) +
    (1309433434953027/109951162777600000000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((13712324074340343/2814749767106560000000000000000000000000 : ℝ)*v^(2 : ℕ) +
    (37503161165763/54975581388800000000000000000000000000 : ℝ)*v^(3 : ℕ) : ℝ) : ℝ) +
    (((1565269458461973/450359962737049600000000000000000000000000 : ℝ)*v^(4 : ℕ) +
    (-3116776521443939/1319413953331200000000000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ) +
    ((-43445437981497/109951162777600000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
    ((1561438053045381/7036874417766400000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (5708537744787/1759218604441600000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) +
    ((((53418853800603/225179981368524800000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ) +
    (-64277329895957/105553116266496000000000000000000000000 : ℝ)*t^(2 : ℕ) : ℝ) +
    ((-709720439397/54975581388800000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) +
    ((2877183729387/14073748835532800000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) +
    (-2126961279/1759218604441600000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(3 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((83499748533/450359962737049600000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(4 : ℕ) +
    (-62727079893/10995116277760000000000000000000000000 : ℝ)*t^(3 : ℕ) : ℝ) +
    ((-234003879/5497558138880000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) +
    ((-579868821/351843720888320000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ) +
    (-304371/21990232555520000000000000000000000 : ℝ)*t^(4 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner16Coeff2_eq (t v : ℝ) :
    evenCompactHorner16Coeff2 t v = (evenCompactRelativeGapGrade16Coeff2 v)+
      (191/10+t/10)*(evenCompactHorner17Coeff2 t v)+(-12/5+(16/15)*t)*(evenCompactHorner17Coeff1 t v) := by
  unfold evenCompactHorner16Coeff2 evenCompactRelativeGapGrade16Coeff2 evenCompactHorner17Coeff2 evenCompactHorner17Coeff1
  ring1

/-- Drift-degree 3 in this exact Horner remainder. -/
def evenCompactHorner16Coeff3 (t v : ℝ) : ℝ :=
  (((((3050866068392467/1484340697497600000000000000000000000000 : ℝ) +
    (9055823646782261/1979120929996800000000000000000000000000 : ℝ)*v^(1 : ℕ) : ℝ) +
    ((4294335697281671/1319413953331200000000000000000000000000 : ℝ)*v^(2 : ℕ) +
    ((114048818522057/109951162777600000000000000000000000000 : ℝ)*v^(3 : ℕ) +
    (4442139447711531/28147497671065600000000000000000000000000 : ℝ)*v^(4 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((10928081239209/1125899906842624000000000000000000000000 : ℝ)*v^(5 : ℕ) +
    ((118163592369/5629499534213120000000000000000000000000 : ℝ)*v^(6 : ℕ) +
    (-1197712618859267/1484340697497600000000000000000000000000 : ℝ)*t^(1 : ℕ) : ℝ) : ℝ) +
    ((-544774925905309/1979120929996800000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
    ((92363381056529/1319413953331200000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) +
    (372816431057/10995116277760000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) +
    ((((14446343724069/5629499534213120000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ) +
    ((14182604343/1125899906842624000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(5 : ℕ) +
    (2998431459/5629499534213120000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(6 : ℕ) : ℝ) : ℝ) +
    ((-5296201424209/24739011624960000000000000000000000000 : ℝ)*t^(2 : ℕ) +
    ((-62100382403/858993459200000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) +
    (18926283009/43980465111040000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((-708987093/27487790694400000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(3 : ℕ) +
    ((27833249511/7036874417766400000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(4 : ℕ) +
    (-7255200343/343597383680000000000000000000000000 : ℝ)*t^(3 : ℕ) : ℝ) : ℝ) +
    ((-78001293/171798691840000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) +
    ((-193289607/10995116277760000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ) +
    (-33819/343597383680000000000000000000000 : ℝ)*t^(4 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner16Coeff3_eq (t v : ℝ) :
    evenCompactHorner16Coeff3 t v = (evenCompactRelativeGapGrade16Coeff3 v)+
      (191/10+t/10)*(evenCompactHorner17Coeff3 t v)+(-12/5+(16/15)*t)*(evenCompactHorner17Coeff2 t v) := by
  unfold evenCompactHorner16Coeff3 evenCompactRelativeGapGrade16Coeff3 evenCompactHorner17Coeff3 evenCompactHorner17Coeff2
  ring1

/-- Drift-degree 4 in this exact Horner remainder. -/
def evenCompactHorner16Coeff4 (t v : ℝ) : ℝ :=
  (((((-5609252697535997/3339766569369600000000000000000000000000 : ℝ) +
    ((-42561025912469/27487790694400000000000000000000000000 : ℝ)*v^(1 : ℕ) +
    (-1710416710544051/2968681394995200000000000000000000000000 : ℝ)*v^(2 : ℕ) : ℝ) : ℝ) +
    ((-118103514151453/1319413953331200000000000000000000000000 : ℝ)*v^(3 : ℕ) +
    ((75010245305671/21110623253299200000000000000000000000000 : ℝ)*v^(4 : ℕ) +
    (497073078367/140737488355328000000000000000000000000 : ℝ)*v^(5 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((181019589459/351843720888320000000000000000000000000 : ℝ)*v^(6 : ℕ) +
    ((15935110407/562949953421312000000000000000000000000 : ℝ)*v^(7 : ℕ) +
    (97069833/281474976710656000000000000000000000000 : ℝ)*v^(8 : ℕ) : ℝ) : ℝ) +
    ((-38984980126079/139156940390400000000000000000000000000 : ℝ)*t^(1 : ℕ) +
    ((-41293145765341/185542587187200000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(1 : ℕ) +
    (-8325437536897/123695058124800000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(2 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) +
    ((((-9690939911/1288490188800000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(3 : ℕ) +
    ((335526739847/879609302220800000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(4 : ℕ) +
    (4727534781/35184372088832000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(5 : ℕ) : ℝ) : ℝ) +
    ((999477153/175921860444160000000000000000000000000 : ℝ)*t^(1 : ℕ)*v^(6 : ℕ) +
    ((-921496840493/23192823398400000000000000000000000000 : ℝ)*t^(2 : ℕ) +
    (-1314227757/53687091200000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(1 : ℕ) : ℝ) : ℝ) : ℝ) +
    (((-64503953661/13743895347200000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(2 : ℕ) +
    ((-236329031/1717986918400000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(3 : ℕ) +
    (9277749837/439804651110400000000000000000000000000 : ℝ)*t^(2 : ℕ)*v^(4 : ℕ) : ℝ) : ℝ) +
    (((-428287199/96636764160000000000000000000000000 : ℝ)*t^(3 : ℕ) +
    (-26000431/16106127360000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(1 : ℕ) : ℝ) +
    ((-21476623/343597383680000000000000000000000000 : ℝ)*t^(3 : ℕ)*v^(2 : ℕ) +
    (-11273/42949672960000000000000000000000 : ℝ)*t^(4 : ℕ) : ℝ) : ℝ) : ℝ) : ℝ) : ℝ)

/-- This coefficient step is an exact identity with only a linear multiplier. -/
theorem evenCompactHorner16Coeff4_eq (t v : ℝ) :
    evenCompactHorner16Coeff4 t v = (evenCompactRelativeGapGrade16Coeff4 v)+
      (191/10+t/10)*((0 : ℝ))+(-12/5+(16/15)*t)*(evenCompactHorner17Coeff3 t v) := by
  unfold evenCompactHorner16Coeff4 evenCompactRelativeGapGrade16Coeff4 evenCompactHorner17Coeff3
  ring1

/-- The exact Horner polynomial retains its drift grading. -/
def evenCompactHorner16 (r t v : ℝ) : ℝ :=
  ((evenCompactHorner16Coeff0 t v +
    (r^(1 : ℕ)*evenCompactHorner16Coeff1 t v) : ℝ) +
    ((r^(2 : ℕ)*evenCompactHorner16Coeff2 t v) +
    ((r^(3 : ℕ)*evenCompactHorner16Coeff3 t v) +
    (r^(4 : ℕ)*evenCompactHorner16Coeff4 t v) : ℝ) : ℝ) : ℝ)

/-- Assemble the checked coefficient identities without expanding their polynomials. -/
theorem evenCompactHorner16_step (r t v : ℝ) :
    evenCompactHorner16 r t v = evenCompactRelativeGapGrade16 r v+
      evenCompactUnitGap r t*evenCompactHorner17 r t v := by
  unfold evenCompactHorner16 evenCompactHorner17
  rw [evenCompactHorner16Coeff0_eq, evenCompactHorner16Coeff1_eq, evenCompactHorner16Coeff2_eq, evenCompactHorner16Coeff3_eq, evenCompactHorner16Coeff4_eq]
  unfold evenCompactRelativeGapGrade16 evenCompactUnitGap
  ring1

end
end HTGeometry
