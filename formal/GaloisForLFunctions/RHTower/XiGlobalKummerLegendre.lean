import GaloisForLFunctions.RHTower.XiGlobalKummerMarkedTower
import GaloisForLFunctions.HTGeometry.LegendreDoublingSquare

/-!
# The actual Xi Legendre section and its global Kummer unit

On the joint marked extension, put `d=beta²*xi` and `u²=xi*(1-d)`. The Legendre curve with
parameter `1+d` carries the nonsingular point `(d,beta*u)`. It is not a double: its
x-coordinate has the surviving square class of Xi. The marking `q=beta*u/(1-d)` satisfies
the original source equation and recovers `u` rationally.

The same class has the explicit unit representative `1-2*d+2*i*beta*u`, with inverse
`1-2*d-2*i*beta*u`. A polynomial square identity identifies this unit's class with Xi.
-/

noncomputable section
open Complex Filter Topology
open GaloisForLFunctions.HTGeometry
namespace RHTower.XiGlobalKummer

/-- The entire square root of the integer-labelled exponential source character. -/
def beta (n : ℕ) (s : ℂ) : ℂ :=
  Complex.exp (-s * (Real.log (n + 2 : ℕ) : ℂ) / 2)

theorem beta_differentiable (n : ℕ) : Differentiable ℂ (beta n) :=
  ((differentiable_id.neg.mul_const (Real.log (n + 2 : ℕ) : ℂ)).div_const 2).cexp

theorem beta_sq (n : ℕ) (s : ℂ) :
    beta n s ^ 2 = Complex.exp (-s * (Real.log (n + 2 : ℕ) : ℂ)) := by
  rw [beta, pow_two, ← Complex.exp_add]
  congr 1
  ring

/-- The exponential square root in the global meromorphic plane field. -/
def betaElement (n : ℕ) : MeromorphicPlane :=
  ofMeromorphic (beta n) (fun z => ((beta_differentiable n).analyticAt z).meromorphicAt)

theorem betaElement_ne_zero (n : ℕ) : betaElement n ≠ 0 := by
  intro h
  have he := congrArg MeromorphicPlane.germ h
  change (beta n : Germ planeCodiscrete ℂ) = ((fun _ : ℂ => (0 : ℂ)) : Germ planeCodiscrete ℂ) at he
  have he0 := (eventuallyEq_planeCodiscrete_iff.mp (Germ.coe_eq.mp he)) 0
  obtain ⟨z, hz⟩ := he0.exists
  exact Complex.exp_ne_zero _ hz

/-- The actual Xi pullback relation for the source parameter. -/
theorem betaElement_sq_mul_xi (n : ℕ) :
    betaElement n ^ 2 * xiElement = 1 - factorElement (n + 2) := by
  apply eq_sub_iff_add_eq.mpr
  rw [pow_two]
  apply MeromorphicPlane.germ_injective
  simp only [germ_add, germ_mul, betaElement, xiElement,
    factorElement, germ_ofMeromorphic, germ_one]
  rw [← Germ.coe_mul, ← Germ.coe_mul, ← Germ.coe_add]
  apply Germ.coe_eq.mpr
  filter_upwards with s
  change beta n s * beta n s * xi s + deletionFactor (n + 2) s = 1
  rw [← pow_two, beta_sq, deletionFactor]
  ring

abbrev Marked := ↥markedExtension

local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
local instance : DecidableEq Marked := Classical.decEq Marked

def xiMarked : Marked := algebraMap K Marked xiElement

def betaMarked (n : ℕ) : Marked := algebraMap K Marked (betaElement n)

def factorMarked (n : ℕ) : Marked := algebraMap K Marked (factorElement (n + 2))

/-- The actual parameter `(n+2)^(-s)*xi(s)` on the joint marked extension. -/
def sourceParameter (n : ℕ) : Marked := betaMarked n ^ 2 * xiMarked

def sourceY (n : ℕ) : Marked := betaMarked n * markedRoot n

theorem betaMarked_ne_zero (n : ℕ) : betaMarked n ≠ 0 :=
  (map_ne_zero (algebraMap K Marked)).mpr (betaElement_ne_zero n)

theorem factorMarked_ne_zero (n : ℕ) : factorMarked n ≠ 0 :=
  (map_ne_zero (algebraMap K Marked)).mpr (factorElement_ne_zero (by omega))

theorem sourceParameter_add_factor (n : ℕ) : sourceParameter n + factorMarked n = 1 := by
  have h := congrArg (algebraMap K Marked) (betaElement_sq_mul_xi n)
  simp only [map_mul, map_pow, map_sub, map_one] at h
  exact eq_sub_iff_add_eq.mp h

/-- The source parameter retains the nonzero global Xi square class. -/
theorem sourceParameter_not_isSquare (n : ℕ) : ¬ IsSquare (sourceParameter n) := by
  rintro ⟨r, hr⟩
  apply xi_not_isSquare_markedExtension
  refine ⟨r / betaMarked n, ?_⟩
  have hb := betaMarked_ne_zero n
  change betaMarked n ^ 2 * xiMarked = r * r at hr
  change xiMarked = r / betaMarked n * (r / betaMarked n)
  field_simp [hb]
  linear_combination hr

theorem sourceParameter_ne_zero (n : ℕ) : sourceParameter n ≠ 0 := by
  intro h
  exact sourceParameter_not_isSquare n (h ▸ IsSquare.zero)

theorem sourceY_sq (n : ℕ) : sourceY n ^ 2 = sourceParameter n * factorMarked n := by
  have hu := markedRoot_sq n
  rw [radicand, map_mul] at hu
  change markedRoot n * markedRoot n = xiMarked * factorMarked n at hu
  dsimp [sourceY, sourceParameter]
  linear_combination betaMarked n ^ 2 * hu

theorem sourceY_ne_zero (n : ℕ) : sourceY n ≠ 0 := by
  intro h
  have hy := sourceY_sq n
  rw [h, zero_pow (by decide : 2 ≠ 0)] at hy
  exact (mul_ne_zero (sourceParameter_ne_zero n) (factorMarked_ne_zero n)) hy.symm

def sourceCurve (n : ℕ) : WeierstrassCurve.Affine Marked :=
  LegendreDoubling.curve (1 + sourceParameter n)

theorem sourceSection_equation (n : ℕ) :
    (sourceCurve n).Equation (sourceParameter n) (sourceY n) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  dsimp [sourceCurve, LegendreDoubling.curve]
  have hy := sourceY_sq n
  have hf := sourceParameter_add_factor n
  linear_combination hy + sourceParameter n * hf

theorem sourceSection_nonsingular (n : ℕ) :
    (sourceCurve n).Nonsingular (sourceParameter n) (sourceY n) := by
  rw [WeierstrassCurve.Affine.nonsingular_iff']
  refine ⟨sourceSection_equation n, Or.inr ?_⟩
  simpa [sourceCurve, LegendreDoubling.curve] using
    mul_ne_zero (show (2 : Marked) ≠ 0 by norm_num) (sourceY_ne_zero n)

/-- The original nonsingular marked Legendre section after the actual Xi pullback. -/
def sourceSection (n : ℕ) : (sourceCurve n).Point :=
  WeierstrassCurve.Affine.Point.some (sourceParameter n) (sourceY n) (sourceSection_nonsingular n)

/-- The actual source section has no half on the full joint marked extension. -/
theorem sourceSection_not_double (n : ℕ) (R : (sourceCurve n).Point) :
    R + R ≠ sourceSection n :=
  LegendreDoubling.point_not_double_of_x_not_square (sourceSection_nonsingular n)
    (sourceParameter_not_isSquare n) R

/-- The original marking coordinate, recovered from the entire marked root. -/
def markingCoordinate (n : ℕ) : Marked := sourceY n / factorMarked n

/-- The marking satisfies the prescribed quadratic pullback equation. -/
theorem markingCoordinate_sq (n : ℕ) :
    markingCoordinate n ^ 2 = sourceParameter n / factorMarked n := by
  rw [markingCoordinate, div_pow, sourceY_sq]
  field_simp [factorMarked_ne_zero n]

/-- The original marking and the entire marked root generate the same extension. -/
theorem markedRoot_recovered (n : ℕ) :
    markedRoot n = markingCoordinate n * factorMarked n / betaMarked n := by
  dsimp [markingCoordinate, sourceY]
  field_simp [factorMarked_ne_zero n, betaMarked_ne_zero n]


def markedI : Marked := algebraMap K Marked (constPlane Complex.I)

theorem markedI_sq : markedI ^ 2 = -1 := by
  simp only [markedI, ← map_pow, Complex.I_sq, map_neg, map_one]

/-- An explicit unit representing the surviving global Xi square class. -/
def unitRepresentative (n : ℕ) : Marked :=
  1 - 2 * sourceParameter n + 2 * markedI * sourceY n

/-- The polynomial inverse of the global Kummer representative. -/
def unitRepresentativeInverse (n : ℕ) : Marked :=
  1 - 2 * sourceParameter n - 2 * markedI * sourceY n

theorem unitRepresentative_mul_inverse (n : ℕ) :
    unitRepresentative n * unitRepresentativeInverse n = 1 := by
  dsimp [unitRepresentative, unitRepresentativeInverse]
  linear_combination -4 * sourceY n ^ 2 * markedI_sq +
    4 * sourceY_sq n + 4 * sourceParameter n * sourceParameter_add_factor n

/-- The explicit global Kummer representative as a unit. -/
def sourceKummerUnit (n : ℕ) : Markedˣ where
  val := unitRepresentative n
  inv := unitRepresentativeInverse n
  val_inv := unitRepresentative_mul_inverse n
  inv_val := by rw [mul_comm]; exact unitRepresentative_mul_inverse n

/-- The unit representative has exactly the square class of Xi. -/
theorem unitRepresentative_mul_square (n : ℕ) :
    unitRepresentative n * (markedRoot n - markedI * betaMarked n * xiMarked) ^ 2 = xiMarked := by
  have hu := markedRoot_sq n
  rw [radicand, map_mul] at hu
  change markedRoot n * markedRoot n = xiMarked * factorMarked n at hu
  have hf := sourceParameter_add_factor n
  dsimp [sourceParameter] at hf
  have hprod : (markedRoot n - markedI * betaMarked n * xiMarked) *
      (markedRoot n + markedI * betaMarked n * xiMarked) = xiMarked := by
    linear_combination -betaMarked n ^ 2 * xiMarked ^ 2 * markedI_sq + hu + xiMarked * hf
  have hmul : unitRepresentative n * (markedRoot n - markedI * betaMarked n * xiMarked) =
      markedRoot n + markedI * betaMarked n * xiMarked := by
    dsimp [unitRepresentative, sourceParameter, sourceY]
    linear_combination 2 * markedI * betaMarked n * hu +
      2 * markedI * betaMarked n * xiMarked * hf -
      2 * betaMarked n ^ 2 * markedRoot n * xiMarked * markedI_sq
  calc
    _ = (unitRepresentative n * (markedRoot n - markedI * betaMarked n * xiMarked)) *
        (markedRoot n - markedI * betaMarked n * xiMarked) := by ring
    _ = (markedRoot n + markedI * betaMarked n * xiMarked) *
        (markedRoot n - markedI * betaMarked n * xiMarked) := by rw [hmul]
    _ = xiMarked := by rw [mul_comm]; exact hprod

/-- The explicit source unit has no square root on the joint marked extension. -/
theorem unitRepresentative_not_isSquare (n : ℕ) : ¬ IsSquare (unitRepresentative n) := by
  intro h
  apply xi_not_isSquare_markedExtension
  change IsSquare xiMarked
  rw [← unitRepresentative_mul_square n]
  exact h.mul (IsSquare.sq _)

end RHTower.XiGlobalKummer
