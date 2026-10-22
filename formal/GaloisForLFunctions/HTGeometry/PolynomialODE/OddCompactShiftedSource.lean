import GaloisForLFunctions.HTGeometry.PolynomialODE.OddCompactScalarPolynomials

/-!
# Lower source in the box chart

The compact box uses `a = 17+3t` with `0 ≤ t ≤ 1`. Substituting it into the
lower source correction gives one explicit polynomial in `u, t, w`.
-/

namespace HTGeometry
noncomputable section
set_option maxRecDepth 4000

/-- The lower source correction after the box substitution `a = 17+3t`. -/
def oddCompactShiftedLowerSource (u t w : ℝ) : ℝ :=
  ((1089000 : ℝ) +
    (594000 : ℝ)*t^(1 : ℕ) +
    (-153714 : ℝ)*w^(1 : ℕ) +
    (-22605 : ℝ)*u^(1 : ℕ) +
    (81000 : ℝ)*t^(2 : ℕ) +
    (-69048 : ℝ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (-6165 : ℝ)*u^(1 : ℕ)*t^(1 : ℕ) +
    (132000 : ℝ)*u^(2 : ℕ) +
    (-7398 : ℝ)*w^(1 : ℕ)*t^(2 : ℕ) +
    (36000 : ℝ)*u^(2 : ℕ)*t^(1 : ℕ) +
    (-9316 : ℝ)*u^(2 : ℕ)*w^(1 : ℕ) +
    (-1370 : ℝ)*u^(3 : ℕ) +
    (-1644 : ℝ)*u^(2 : ℕ)*w^(1 : ℕ)*t^(1 : ℕ) +
    (4000 : ℝ)*u^(4 : ℕ)) / (768000 : ℝ)

/-- The substituted lower source is the displayed polynomial in the box chart. -/
theorem oddCompactShiftedLowerSource_eq (u t w : ℝ) :
    oddCompactLowerSource u (17+3*t) w = oddCompactShiftedLowerSource u t w := by
  unfold oddCompactLowerSource oddCompactSourceZero oddCompactShiftedLowerSource
  ring

end
end HTGeometry
