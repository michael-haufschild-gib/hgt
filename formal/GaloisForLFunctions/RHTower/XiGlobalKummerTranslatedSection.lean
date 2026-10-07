import GaloisForLFunctions.RHTower.XiGlobalKummerLegendre

/-!
# The translated Xi section remains globally non-divisible

The source section translated by the rational two-torsion point `(0,0)` is
`Q=((1+d)/d, -(1+d)*y/d²)`. This is an equality in the actual affine group, after
adjoining every integer-labelled marked root. Since `x(Q)-1=1/d` is nonsquare,
`Q` has no half in this extension. Its full halves field may also carry the
additional square class of `1+d`; it is not identified with that of the original section.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry
open WeierstrassCurve.Affine
namespace RHTower.XiGlobalKummer
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
local instance : DecidableEq Marked := Classical.decEq Marked

/-- The actual Legendre parameter differs from zero. -/
theorem sourceLambda_ne_zero (n : ℕ) : 1 + sourceParameter n ≠ 0 := by
  intro h
  apply sourceParameter_not_isSquare n
  refine ⟨markedI, ?_⟩
  have hi := markedI_sq
  linear_combination h - hi

def translatedX (n : ℕ) : Marked := (1 + sourceParameter n) / sourceParameter n

def translatedY (n : ℕ) : Marked :=
  -(1 + sourceParameter n) * sourceY n / sourceParameter n ^ 2

theorem translatedSection_equation (n : ℕ) :
    (sourceCurve n).Equation (translatedX n) (translatedY n) := by
  have hp : sourceY n ^ 2 = sourceParameter n * (1 - sourceParameter n) := by
    linear_combination sourceY_sq n + sourceParameter n * sourceParameter_add_factor n
  rw [equation_iff]
  dsimp [sourceCurve, LegendreDoubling.curve, translatedX, translatedY]
  field_simp [sourceParameter_ne_zero n]
  linear_combination (1 + sourceParameter n) ^ 2 * hp

theorem translatedY_ne_zero (n : ℕ) : translatedY n ≠ 0 :=
  div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (sourceLambda_ne_zero n)) (sourceY_ne_zero n))
    (pow_ne_zero 2 (sourceParameter_ne_zero n))

theorem translatedSection_nonsingular (n : ℕ) :
    (sourceCurve n).Nonsingular (translatedX n) (translatedY n) := by
  rw [nonsingular_iff']
  refine ⟨translatedSection_equation n, Or.inr ?_⟩
  simpa [sourceCurve, LegendreDoubling.curve] using
    mul_ne_zero (show (2 : Marked) ≠ 0 by norm_num) (translatedY_ne_zero n)

/-- The actual translated source section. -/
def translatedSection (n : ℕ) : (sourceCurve n).Point :=
  Point.some (translatedX n) (translatedY n) (translatedSection_nonsingular n)

theorem translatedX_sub_one_not_isSquare (n : ℕ) : ¬ IsSquare (translatedX n - 1) := by
  have h : sourceParameter n * (translatedX n - 1) = 1 := by
    dsimp [translatedX]
    field_simp [sourceParameter_ne_zero n]
    ring
  rintro ⟨r, hr⟩
  apply sourceParameter_not_isSquare n
  refine ⟨sourceParameter n * r, ?_⟩
  rw [hr] at h
  linear_combination -sourceParameter n * h

/-- The translated source section has no half on the full joint marked extension. -/
theorem translatedSection_not_double (n : ℕ) (R : (sourceCurve n).Point) :
    R + R ≠ translatedSection n :=
  LegendreDoubling.point_not_double_of_x_sub_one_not_square (translatedSection_nonsingular n)
    (translatedX_sub_one_not_isSquare n) R


theorem torsionSection_nonsingular (n : ℕ) : (sourceCurve n).Nonsingular 0 0 := by
  rw [nonsingular_iff']
  refine ⟨?_, Or.inl ?_⟩
  · simp [equation_iff, sourceCurve, LegendreDoubling.curve]
  · simpa [sourceCurve, LegendreDoubling.curve] using neg_ne_zero.mpr (sourceLambda_ne_zero n)

/-- The rational two-torsion section at `(0,0)`. -/
def torsionSection (n : ℕ) : (sourceCurve n).Point :=
  Point.some 0 0 (torsionSection_nonsingular n)

theorem torsionSection_double (n : ℕ) : torsionSection n + torsionSection n = 0 := by
  apply Point.add_self_of_Y_eq
  simp [sourceCurve, LegendreDoubling.curve, negY]

/-- The explicit translated coordinates agree with translation in the affine group. -/
theorem translatedSection_eq_add_torsion (n : ℕ) :
    translatedSection n = sourceSection n + torsionSection n := by
  have hs : (sourceCurve n).slope (sourceParameter n) 0 (sourceY n) 0 =
      sourceY n / sourceParameter n := by
    rw [slope_of_X_ne (sourceParameter_ne_zero n)]
    simp
  have hp : sourceY n ^ 2 = sourceParameter n * (1 - sourceParameter n) := by
    linear_combination sourceY_sq n + sourceParameter n * sourceParameter_add_factor n
  have hx : (sourceCurve n).addX (sourceParameter n) 0 (sourceY n / sourceParameter n) =
      translatedX n := by
    dsimp [sourceCurve, LegendreDoubling.curve, addX, translatedX]
    field_simp [sourceParameter_ne_zero n]
    linear_combination hp
  have hy : (sourceCurve n).addY (sourceParameter n) 0 (sourceY n)
      (sourceY n / sourceParameter n) = translatedY n := by
    rw [addY, negAddY, hx]
    dsimp [sourceCurve, LegendreDoubling.curve, negY, translatedX, translatedY]
    field_simp [sourceParameter_ne_zero n]
    ring
  symm
  dsimp [sourceSection, torsionSection, translatedSection]
  rw [Point.add_of_X_ne (sourceParameter_ne_zero n)]
  rw [Point.some.injEq]
  constructor
  · simpa only [hs] using hx
  · simpa only [hs] using hy

end RHTower.XiGlobalKummer
