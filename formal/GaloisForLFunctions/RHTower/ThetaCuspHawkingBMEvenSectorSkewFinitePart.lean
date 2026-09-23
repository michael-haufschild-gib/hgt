import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEvenSectorSkewTrace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Hadamard finite part of the elementary skew cut

The radial integral of the dressed two-rate density `z^{−3}·r²·(current)` over the exterior, in
the boundary variable `w = (1−z)^{1/2} = 1/r`, is the integral of the rational function
`skewBulkIntegrand s w = 2w·skewLaurentSS s w/(1−w²)⁴` over `0 < w < 1`. Its partial fractions
(`skewBulkIntegrand_eq`) have a double pole at `w = 0` (the AdS boundary), poles of order up to
four at `w = 1` (the horizon) and at `w = −1`, and no logarithmic term at the boundary. The
primitive `skewBulkPrimitive` is explicit (`hasDerivAt_skewBulkPrimitive`), so the integral over
`[a, b]` is a difference of primitive values (`skewBulk_integral`). With the horizon cutoff `z = ε`,
i.e. `w = √(1−ε)`, the primitive splits exactly into the pure divergences `skewBulkDivergence s ε`
(`2/ε`, `4/ε² − 2/ε`, `8/ε³ − 6/ε²` and `−b₁·log ε`, from the identities
`1/(1−w) + 1/(1+w) = 2/(1−w²)` and their squares and cubes) and a part `skewBulkRegular`
continuous at `w = 1` (`skewBulkPrimitive_split`); at the boundary end the primitive is the pure
divergence `−a₂/w` plus a part continuous at `w = 0`. The finite part is therefore the explicit
value `skewBulkFinitePart s = skewBulkRegular s 1 − skewBulkBoundaryRegular s 0`
(`skewBulkFinitePart_eq`, `skewBulk_finitePart_limit`): a rational function of `s` plus
`(b₁ + d₁)·log 2`, where `3·b₁ = −skewLogCoeff s` and `b₁ + d₁ = −(2/3)·skewLogCoeff s`
(`skewBulk_log_coefficients`), so the logarithm of two combines with the cutoff into `log(4/ε)`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace RHTower.D4BMScalarStream

/-- The rational integrand in the boundary variable `w = 1/r`. -/
noncomputable def skewBulkIntegrand (s : ℂ) (w : ℝ) : ℂ :=
  2 * (w : ℂ) * skewLaurentSS s (w : ℂ) / (1 - (w : ℂ) ^ (2 : ℕ)) ^ (4 : ℕ)

/-- Partial-fraction coefficient of the double pole at the boundary. -/
noncomputable def skewPfA (s : ℂ) : ℂ := (((3 : ℂ) + (-5 / 2 : ℂ) * s + (-9 / 2 : ℂ) * s ^ (2 : ℕ) + (-1 : ℂ) * s ^ (3 : ℕ)) / (s * (s + 3)))
/-- Partial-fraction coefficient of `(1−w)^{−1}`. -/
noncomputable def skewPfB1 (s : ℂ) : ℂ := (((63 / 32 : ℂ) + (-177 / 64 : ℂ) * s + (1395 / 128 : ℂ) * s ^ (2 : ℕ) + (9659 / 256 : ℂ) * s ^ (3 : ℕ) + (102873 / 2048 : ℂ) * s ^ (4 : ℕ) + (187685 / 4096 : ℂ) * s ^ (5 : ℕ) + (131145 / 4096 : ℂ) * s ^ (6 : ℕ) + (17149 / 1024 : ℂ) * s ^ (7 : ℕ) + (6291 / 1024 : ℂ) * s ^ (8 : ℕ) + (5989 / 4096 : ℂ) * s ^ (9 : ℕ) + (825 / 4096 : ℂ) * s ^ (10 : ℕ) + (25 / 2048 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))
/-- Partial-fraction coefficient of `(1−w)^{−2}`. -/
noncomputable def skewPfB2 (s : ℂ) : ℂ := (((15 / 32 : ℂ) + (-241 / 64 : ℂ) * s + (-1089 / 128 : ℂ) * s ^ (2 : ℕ) + (-9601 / 256 : ℂ) * s ^ (3 : ℕ) + (-184887 / 2048 : ℂ) * s ^ (4 : ℕ) + (-467499 / 4096 : ℂ) * s ^ (5 : ℕ) + (-359751 / 4096 : ℂ) * s ^ (6 : ℕ) + (-45299 / 1024 : ℂ) * s ^ (7 : ℕ) + (-15309 / 1024 : ℂ) * s ^ (8 : ℕ) + (-13611 / 4096 : ℂ) * s ^ (9 : ℕ) + (-1815 / 4096 : ℂ) * s ^ (10 : ℕ) + (-55 / 2048 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))
/-- Partial-fraction coefficient of `(1−w)^{−3}`. -/
noncomputable def skewPfB3 (s : ℂ) : ℂ := (((-3 / 16 : ℂ) + (-301 / 32 : ℂ) * s + (-2511 / 128 : ℂ) * s ^ (2 : ℕ) + (2829 / 256 : ℂ) * s ^ (3 : ℕ) + (20211 / 256 : ℂ) * s ^ (4 : ℕ) + (57847 / 512 : ℂ) * s ^ (5 : ℕ) + (43827 / 512 : ℂ) * s ^ (6 : ℕ) + (2567 / 64 : ℂ) * s ^ (7 : ℕ) + (3159 / 256 : ℂ) * s ^ (8 : ℕ) + (1293 / 512 : ℂ) * s ^ (9 : ℕ) + (165 / 512 : ℂ) * s ^ (10 : ℕ) + (5 / 256 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))
/-- Partial-fraction coefficient of `(1−w)^{−4}`. -/
noncomputable def skewPfB4 (s : ℂ) : ℂ := ((-27 / 16 : ℂ) + (-585 / 128 : ℂ) * s + (-2151 / 256 : ℂ) * s ^ (2 : ℕ) + (-12331 / 1024 : ℂ) * s ^ (3 : ℕ) + (-22785 / 2048 : ℂ) * s ^ (4 : ℕ) + (-3185 / 512 : ℂ) * s ^ (5 : ℕ) + (-273 / 128 : ℂ) * s ^ (6 : ℕ) + (-239 / 512 : ℂ) * s ^ (7 : ℕ) + (-135 / 2048 : ℂ) * s ^ (8 : ℕ) + (-5 / 1024 : ℂ) * s ^ (9 : ℕ))
/-- Partial-fraction coefficient of `(1+w)^{−1}`. -/
noncomputable def skewPfD1 (s : ℂ) : ℂ := (((63 / 32 : ℂ) + (-177 / 64 : ℂ) * s + (1395 / 128 : ℂ) * s ^ (2 : ℕ) + (9659 / 256 : ℂ) * s ^ (3 : ℕ) + (102873 / 2048 : ℂ) * s ^ (4 : ℕ) + (187685 / 4096 : ℂ) * s ^ (5 : ℕ) + (131145 / 4096 : ℂ) * s ^ (6 : ℕ) + (17149 / 1024 : ℂ) * s ^ (7 : ℕ) + (6291 / 1024 : ℂ) * s ^ (8 : ℕ) + (5989 / 4096 : ℂ) * s ^ (9 : ℕ) + (825 / 4096 : ℂ) * s ^ (10 : ℕ) + (25 / 2048 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))
/-- Partial-fraction coefficient of `(1+w)^{−2}`. -/
noncomputable def skewPfD2 (s : ℂ) : ℂ := (((15 / 32 : ℂ) + (-241 / 64 : ℂ) * s + (-1089 / 128 : ℂ) * s ^ (2 : ℕ) + (-9601 / 256 : ℂ) * s ^ (3 : ℕ) + (-184887 / 2048 : ℂ) * s ^ (4 : ℕ) + (-467499 / 4096 : ℂ) * s ^ (5 : ℕ) + (-359751 / 4096 : ℂ) * s ^ (6 : ℕ) + (-45299 / 1024 : ℂ) * s ^ (7 : ℕ) + (-15309 / 1024 : ℂ) * s ^ (8 : ℕ) + (-13611 / 4096 : ℂ) * s ^ (9 : ℕ) + (-1815 / 4096 : ℂ) * s ^ (10 : ℕ) + (-55 / 2048 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))
/-- Partial-fraction coefficient of `(1+w)^{−3}`. -/
noncomputable def skewPfD3 (s : ℂ) : ℂ := (((-3 / 16 : ℂ) + (-301 / 32 : ℂ) * s + (-2511 / 128 : ℂ) * s ^ (2 : ℕ) + (2829 / 256 : ℂ) * s ^ (3 : ℕ) + (20211 / 256 : ℂ) * s ^ (4 : ℕ) + (57847 / 512 : ℂ) * s ^ (5 : ℕ) + (43827 / 512 : ℂ) * s ^ (6 : ℕ) + (2567 / 64 : ℂ) * s ^ (7 : ℕ) + (3159 / 256 : ℂ) * s ^ (8 : ℕ) + (1293 / 512 : ℂ) * s ^ (9 : ℕ) + (165 / 512 : ℂ) * s ^ (10 : ℕ) + (5 / 256 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3)))
/-- Partial-fraction coefficient of `(1+w)^{−4}`. -/
noncomputable def skewPfD4 (s : ℂ) : ℂ := ((-27 / 16 : ℂ) + (-585 / 128 : ℂ) * s + (-2151 / 256 : ℂ) * s ^ (2 : ℕ) + (-12331 / 1024 : ℂ) * s ^ (3 : ℕ) + (-22785 / 2048 : ℂ) * s ^ (4 : ℕ) + (-3185 / 512 : ℂ) * s ^ (5 : ℕ) + (-273 / 128 : ℂ) * s ^ (6 : ℕ) + (-239 / 512 : ℂ) * s ^ (7 : ℕ) + (-135 / 2048 : ℂ) * s ^ (8 : ℕ) + (-5 / 1024 : ℂ) * s ^ (9 : ℕ))

theorem skewBulkIntegrand_eq (s : ℂ) (w : ℝ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw : (w : ℂ) ≠ 0)
    (hw1 : (1 : ℂ) - w ≠ 0) (hw2 : (1 : ℂ) + w ≠ 0) :
    skewBulkIntegrand s w = skewPfA s * ((w ^ (2 : ℕ))⁻¹ : ℝ) +
      (skewPfB1 s * ((1 - w)⁻¹ : ℝ) + skewPfB2 s * (((1 - w) ^ (2 : ℕ))⁻¹ : ℝ) + skewPfB3 s * (((1 - w) ^ (3 : ℕ))⁻¹ : ℝ) + skewPfB4 s * (((1 - w) ^ (4 : ℕ))⁻¹ : ℝ)) +
      (skewPfD1 s * ((1 + w)⁻¹ : ℝ) + skewPfD2 s * (((1 + w) ^ (2 : ℕ))⁻¹ : ℝ) + skewPfD3 s * (((1 + w) ^ (3 : ℕ))⁻¹ : ℝ) + skewPfD4 s * (((1 + w) ^ (4 : ℕ))⁻¹ : ℝ)) := by
  have hf : ((1 : ℂ) - (w : ℂ) ^ (2 : ℕ)) ≠ 0 := by
    rw [show (1 : ℂ) - (w : ℂ) ^ (2 : ℕ) = (1 - w) * (1 + w) by ring]; exact mul_ne_zero hw1 hw2
  unfold skewBulkIntegrand skewLaurentSS skewPfA skewPfB1 skewPfB2 skewPfB3 skewPfB4 skewPfD1 skewPfD2 skewPfD3 skewPfD4
  push_cast
  field_simp
  ring

/-- The logarithmic coefficients of the partial fractions are the horizon logarithm coefficient. -/
theorem skewBulk_log_coefficients (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    3 * skewPfB1 s = -skewLogCoeff s ∧ skewPfB1 s + skewPfD1 s = -(2 / 3) * skewLogCoeff s := by
  unfold skewPfB1 skewPfD1 skewLogCoeff
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- The primitive of the integrand on `0 < w < 1`. -/
noncomputable def skewBulkPrimitive (s : ℂ) (w : ℝ) : ℂ :=
  (-skewPfA s) * ((w⁻¹ : ℝ) : ℂ) +
    (skewPfB2 s * (((1 - w)⁻¹ : ℝ) : ℂ) + (skewPfB3 s / 2) * ((((1 - w) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) + (skewPfB4 s / 3) * ((((1 - w) ^ (3 : ℕ))⁻¹ : ℝ) : ℂ)) +
    (-skewPfB1 s) * ((Real.log (1 - w) : ℝ) : ℂ) + skewPfD1 s * ((Real.log (1 + w) : ℝ) : ℂ) +
    ((-skewPfD2 s) * (((1 + w)⁻¹ : ℝ) : ℂ) + (-skewPfD3 s / 2) * ((((1 + w) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) + (-skewPfD4 s / 3) * ((((1 + w) ^ (3 : ℕ))⁻¹ : ℝ) : ℂ))

theorem hasDerivAt_skewBulkPrimitive (s : ℂ) (w : ℝ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (hw0 : 0 < w) (hw1 : w < 1) :
    HasDerivAt (skewBulkPrimitive s) (skewBulkIntegrand s w) w := by
  have hwr : w ≠ 0 := hw0.ne'
  have h1r : (1 : ℝ) - w ≠ 0 := by linarith
  have h2r : (1 : ℝ) + w ≠ 0 := by linarith
  have hw : (w : ℂ) ≠ 0 := by exact_mod_cast hwr
  have hw1c : (1 : ℂ) - w ≠ 0 := by exact_mod_cast h1r
  have hw2c : (1 : ℂ) + w ≠ 0 := by exact_mod_cast h2r
  have dm : HasDerivAt (fun x : ℝ => 1 - x) (-1) w := by simpa using (hasDerivAt_id w).const_sub 1
  have dp : HasDerivAt (fun x : ℝ => 1 + x) 1 w := by simpa using (hasDerivAt_id w).const_add 1
  have e0 : HasDerivAt (fun x : ℝ => x⁻¹) (-(w ^ (2 : ℕ))⁻¹) w := by simpa using hasDerivAt_inv hwr
  have e1 : HasDerivAt (fun x : ℝ => (1 - x)⁻¹) (-(-1) / (1 - w) ^ (2 : ℕ)) w := dm.inv h1r
  have e2 : HasDerivAt (fun x : ℝ => ((1 - x) ^ (2 : ℕ))⁻¹) (-(2 * (1 - w) ^ (1 : ℕ) * (-1)) / ((1 - w) ^ (2 : ℕ)) ^ (2 : ℕ)) w :=
    (dm.pow 2).inv (pow_ne_zero 2 h1r)
  have e3 : HasDerivAt (fun x : ℝ => ((1 - x) ^ (3 : ℕ))⁻¹) (-(3 * (1 - w) ^ (2 : ℕ) * (-1)) / ((1 - w) ^ (3 : ℕ)) ^ (2 : ℕ)) w :=
    (dm.pow 3).inv (pow_ne_zero 3 h1r)
  have l1 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-1 / (1 - w)) w := dm.log h1r
  have l2 : HasDerivAt (fun x : ℝ => Real.log (1 + x)) (1 / (1 + w)) w := dp.log h2r
  have f1 : HasDerivAt (fun x : ℝ => (1 + x)⁻¹) (-1 / (1 + w) ^ (2 : ℕ)) w := dp.inv h2r
  have f2 : HasDerivAt (fun x : ℝ => ((1 + x) ^ (2 : ℕ))⁻¹) (-(2 * (1 + w) ^ (1 : ℕ) * 1) / ((1 + w) ^ (2 : ℕ)) ^ (2 : ℕ)) w :=
    (dp.pow 2).inv (pow_ne_zero 2 h2r)
  have f3 : HasDerivAt (fun x : ℝ => ((1 + x) ^ (3 : ℕ))⁻¹) (-(3 * (1 + w) ^ (2 : ℕ) * 1) / ((1 + w) ^ (3 : ℕ)) ^ (2 : ℕ)) w :=
    (dp.pow 3).inv (pow_ne_zero 3 h2r)
  have total := ((((e0.ofReal_comp.const_mul (-skewPfA s)).add
    (((e1.ofReal_comp.const_mul (skewPfB2 s)).add (e2.ofReal_comp.const_mul (skewPfB3 s / 2))).add
      (e3.ofReal_comp.const_mul (skewPfB4 s / 3)))).add
    (l1.ofReal_comp.const_mul (-skewPfB1 s))).add (l2.ofReal_comp.const_mul (skewPfD1 s))).add
    (((f1.ofReal_comp.const_mul (-skewPfD2 s)).add (f2.ofReal_comp.const_mul (-skewPfD3 s / 2))).add
      (f3.ofReal_comp.const_mul (-skewPfD4 s / 3)))
  have hval : skewBulkIntegrand s w = (-skewPfA s) * ((-(w ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) +
      (skewPfB2 s * (((-(-1) / (1 - w) ^ (2 : ℕ)) : ℝ) : ℂ) + (skewPfB3 s / 2) * (((-(2 * (1 - w) ^ (1 : ℕ) * (-1)) / ((1 - w) ^ (2 : ℕ)) ^ (2 : ℕ)) : ℝ) : ℂ) +
        (skewPfB4 s / 3) * (((-(3 * (1 - w) ^ (2 : ℕ) * (-1)) / ((1 - w) ^ (3 : ℕ)) ^ (2 : ℕ)) : ℝ) : ℂ)) +
      (-skewPfB1 s) * (((-1 / (1 - w)) : ℝ) : ℂ) + skewPfD1 s * (((1 / (1 + w)) : ℝ) : ℂ) +
      ((-skewPfD2 s) * (((-1 / (1 + w) ^ (2 : ℕ)) : ℝ) : ℂ) + (-skewPfD3 s / 2) * (((-(2 * (1 + w) ^ (1 : ℕ) * 1) / ((1 + w) ^ (2 : ℕ)) ^ (2 : ℕ)) : ℝ) : ℂ) +
        (-skewPfD4 s / 3) * (((-(3 * (1 + w) ^ (2 : ℕ) * 1) / ((1 + w) ^ (3 : ℕ)) ^ (2 : ℕ)) : ℝ) : ℂ)) := by
    rw [skewBulkIntegrand_eq s w hs hs3 hw hw1c hw2c]
    push_cast
    field_simp
    ring
  rw [hval]
  exact total

/-- The integrand is continuous on compact subintervals of `(0,1)`. -/
theorem skewBulkIntegrand_continuousOn (s : ℂ) (a b : ℝ) (ha : 0 < a) (hb : b < 1) :
    ContinuousOn (fun w => skewBulkIntegrand s w) (Set.Icc a b) := by
  intro x hx
  have hx0 : 0 < x := lt_of_lt_of_le ha hx.1
  have hx1 : x < 1 := lt_of_le_of_lt hx.2 hb
  apply ContinuousAt.continuousWithinAt
  have hxc : (x : ℂ) ≠ 0 := by exact_mod_cast hx0.ne'
  have hx3 : (x : ℂ) ^ (3 : ℕ) ≠ 0 := pow_ne_zero 3 hxc
  have hf : ((1 : ℂ) - (x : ℂ) ^ (2 : ℕ)) ^ (4 : ℕ) ≠ 0 := by
    apply pow_ne_zero
    rw [show (1 : ℂ) - (x : ℂ) ^ (2 : ℕ) = ((1 - x ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    exact_mod_cast (show (1 : ℝ) - x ^ (2 : ℕ) ≠ 0 by nlinarith)
  unfold skewBulkIntegrand skewLaurentSS
  fun_prop (disch := assumption)

/-- The integral over a compact subinterval of `(0,1)` is a difference of primitive values. -/
theorem skewBulk_integral (s : ℂ) (a b : ℝ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    ∫ w in a..b, skewBulkIntegrand s w = skewBulkPrimitive s b - skewBulkPrimitive s a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro w hw
    rw [Set.uIcc_of_le hab] at hw
    exact hasDerivAt_skewBulkPrimitive s w hs hs3 (lt_of_lt_of_le ha hw.1) (lt_of_le_of_lt hw.2 hb)
  · rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (skewBulkIntegrand_continuousOn s a b ha hb).integrableOn_compact isCompact_Icc

/-- Pure divergences of the primitive at the horizon cutoff `z = ε`, `w = √(1−ε)`. -/
noncomputable def skewBulkDivergence (s : ℂ) (ε : ℝ) : ℂ :=
  skewPfB2 s * (2 / (ε : ℂ)) + (skewPfB3 s / 2) * (4 / (ε : ℂ) ^ (2 : ℕ) - 2 / (ε : ℂ)) +
    (skewPfB4 s / 3) * (8 / (ε : ℂ) ^ (3 : ℕ) - 6 / (ε : ℂ) ^ (2 : ℕ)) + (-skewPfB1 s) * ((Real.log ε : ℝ) : ℂ)

/-- The part of the primitive that is continuous at the horizon `w = 1`. -/
noncomputable def skewBulkRegular (s : ℂ) (w : ℝ) : ℂ :=
  (-skewPfA s) * ((w⁻¹ : ℝ) : ℂ) -
    (skewPfB2 s * (((1 + w)⁻¹ : ℝ) : ℂ) + (skewPfB3 s / 2) * ((((1 + w) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) + (skewPfB4 s / 3) * ((((1 + w) ^ (3 : ℕ))⁻¹ : ℝ) : ℂ)) +
    (skewPfB1 s + skewPfD1 s) * ((Real.log (1 + w) : ℝ) : ℂ) +
    ((-skewPfD2 s) * (((1 + w)⁻¹ : ℝ) : ℂ) + (-skewPfD3 s / 2) * ((((1 + w) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) + (-skewPfD4 s / 3) * ((((1 + w) ^ (3 : ℕ))⁻¹ : ℝ) : ℂ))

/-- Exact split of the primitive at `w = √(1−ε)`: from `1/(1−w) + 1/(1+w) = 2/(1−w²)` and its powers,
and `log(1−w) = log ε − log(1+w)`. -/
theorem skewBulkPrimitive_split (s : ℂ) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    skewBulkPrimitive s (Real.sqrt (1 - ε)) = skewBulkDivergence s ε + skewBulkRegular s (Real.sqrt (1 - ε)) := by
  have hw2 : Real.sqrt (1 - ε) ^ (2 : ℕ) = 1 - ε := Real.sq_sqrt (by linarith)
  have hw0 : 0 < Real.sqrt (1 - ε) := Real.sqrt_pos.mpr (by linarith)
  have hwlt : Real.sqrt (1 - ε) < 1 := by rw [Real.sqrt_lt' one_pos]; linarith
  generalize hw : Real.sqrt (1 - ε) = w at hw2 hw0 hwlt ⊢
  have h1r : (0 : ℝ) < 1 - w := by linarith
  have h2r : (0 : ℝ) < 1 + w := by linarith
  have hlog : Real.log (1 - w) = Real.log ε - Real.log (1 + w) := by
    rw [← Real.log_div hε.ne' h2r.ne']
    congr 1
    field_simp
    nlinarith [hw2]
  have hεc : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have h1 : (1 : ℂ) - (w : ℂ) ≠ 0 := by exact_mod_cast h1r.ne'
  have h2 : (1 : ℂ) + (w : ℂ) ≠ 0 := by exact_mod_cast h2r.ne'
  have hwc : (w : ℂ) ≠ 0 := by exact_mod_cast hw0.ne'
  have hε' : (ε : ℂ) = 1 - (w : ℂ) ^ (2 : ℕ) := by exact_mod_cast (by linarith [hw2] : ε = 1 - w ^ (2 : ℕ))
  have hf : (1 : ℂ) - (w : ℂ) ^ (2 : ℕ) ≠ 0 := by
    rw [show (1 : ℂ) - (w : ℂ) ^ (2 : ℕ) = (1 - w) * (1 + w) by ring]; exact mul_ne_zero h1 h2
  unfold skewBulkPrimitive skewBulkDivergence skewBulkRegular
  rw [hlog]
  push_cast
  rw [hε']
  field_simp
  ring

/-- The part of the primitive that is continuous at the boundary `w = 0`. -/
noncomputable def skewBulkBoundaryRegular (s : ℂ) (w : ℝ) : ℂ :=
  (skewPfB2 s * (((1 - w)⁻¹ : ℝ) : ℂ) + (skewPfB3 s / 2) * ((((1 - w) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) + (skewPfB4 s / 3) * ((((1 - w) ^ (3 : ℕ))⁻¹ : ℝ) : ℂ)) +
    (-skewPfB1 s) * ((Real.log (1 - w) : ℝ) : ℂ) + skewPfD1 s * ((Real.log (1 + w) : ℝ) : ℂ) +
    ((-skewPfD2 s) * (((1 + w)⁻¹ : ℝ) : ℂ) + (-skewPfD3 s / 2) * ((((1 + w) ^ (2 : ℕ))⁻¹ : ℝ) : ℂ) + (-skewPfD4 s / 3) * ((((1 + w) ^ (3 : ℕ))⁻¹ : ℝ) : ℂ))

theorem skewBulkPrimitive_boundary (s : ℂ) (w : ℝ) :
    skewBulkPrimitive s w = (-skewPfA s) * ((w⁻¹ : ℝ) : ℂ) + skewBulkBoundaryRegular s w := by
  unfold skewBulkPrimitive skewBulkBoundaryRegular; ring

/-- The finite part: regular value at the horizon minus regular value at the boundary. -/
noncomputable def skewBulkFinitePart (s : ℂ) : ℂ := skewBulkRegular s 1 - skewBulkBoundaryRegular s 0

theorem skewBulkFinitePart_eq (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    skewBulkFinitePart s = (((-219 / 64 : ℂ) + (1157 / 128 : ℂ) * s + (2457 / 128 : ℂ) * s ^ (2 : ℕ) + (9785 / 256 : ℂ) * s ^ (3 : ℕ) + (304129 / 4096 : ℂ) * s ^ (4 : ℕ) + (2203847 / 24576 : ℂ) * s ^ (5 : ℕ) + (564529 / 8192 : ℂ) * s ^ (6 : ℕ) + (216647 / 6144 : ℂ) * s ^ (7 : ℕ) + (24903 / 2048 : ℂ) * s ^ (8 : ℕ) + (67511 / 24576 : ℂ) * s ^ (9 : ℕ) + (3025 / 8192 : ℂ) * s ^ (10 : ℕ) + (275 / 12288 : ℂ) * s ^ (11 : ℕ)) / (s * (s + 3))) + (skewPfB1 s + skewPfD1 s) * ((Real.log 2 : ℝ) : ℂ) := by
  unfold skewBulkFinitePart skewBulkRegular skewBulkBoundaryRegular
  simp only [sub_zero, add_zero, Real.log_one, Complex.ofReal_zero, mul_zero, inv_one, one_pow, Complex.ofReal_one, mul_one]
  rw [show ((1 : ℝ) + 1) = 2 by norm_num]
  unfold skewPfA skewPfB1 skewPfB2 skewPfB3 skewPfB4 skewPfD1 skewPfD2 skewPfD3 skewPfD4
  push_cast
  field_simp
  ring

theorem skewBulkRegular_continuousAt_one (s : ℂ) : ContinuousAt (skewBulkRegular s) 1 := by
  unfold skewBulkRegular
  have hl : ContinuousAt (fun w : ℝ => Real.log (1 + w)) 1 :=
    (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
  have h1 : (1 : ℝ) ≠ 0 := one_ne_zero
  have h2 : (1 : ℝ) + 1 ≠ 0 := by norm_num
  fun_prop (disch := first | assumption | norm_num)

theorem skewBulkBoundaryRegular_continuousAt_zero (s : ℂ) : ContinuousAt (skewBulkBoundaryRegular s) 0 := by
  unfold skewBulkBoundaryRegular
  have hl1 : ContinuousAt (fun w : ℝ => Real.log (1 - w)) 0 :=
    (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
  have hl2 : ContinuousAt (fun w : ℝ => Real.log (1 + w)) 0 :=
    (Real.continuousAt_log (by norm_num)).comp (by fun_prop)
  have h1 : (1 : ℝ) - 0 ≠ 0 := by norm_num
  have h2 : (1 : ℝ) + 0 ≠ 0 := by norm_num
  fun_prop (disch := first | assumption | norm_num)

/-- The cutoff integral minus its pure divergences tends to the finite part as both cutoffs are removed. -/
theorem skewBulk_finitePart_limit (s : ℂ) (hs : s ≠ 0) (hs3 : s + 3 ≠ 0) :
    Filter.Tendsto (fun p : ℝ × ℝ => (∫ w in p.2..Real.sqrt (1 - p.1), skewBulkIntegrand s w) -
        skewBulkDivergence s p.1 - skewPfA s * ((p.2⁻¹ : ℝ) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (nhds (skewBulkFinitePart s)) := by
  have h1 : Set.Ioo (0 : ℝ) (1 / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) := Ioo_mem_nhdsGT (by norm_num)
  have hev : ∀ᶠ p : ℝ × ℝ in nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0),
      (∫ w in p.2..Real.sqrt (1 - p.1), skewBulkIntegrand s w) - skewBulkDivergence s p.1 - skewPfA s * ((p.2⁻¹ : ℝ) : ℂ) =
        skewBulkRegular s (Real.sqrt (1 - p.1)) - skewBulkBoundaryRegular s p.2 := by
    filter_upwards [Filter.prod_mem_prod h1 h1] with p hp
    obtain ⟨⟨hε, hε1⟩, ⟨ha, ha1⟩⟩ := hp
    have hsq1 : Real.sqrt (1 - p.1) < 1 := by rw [Real.sqrt_lt' one_pos]; linarith
    have hsq_ge : 1 / 2 ≤ Real.sqrt (1 - p.1) := by
      rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
    rw [skewBulk_integral s p.2 (Real.sqrt (1 - p.1)) hs hs3 ha (by linarith) hsq1,
      skewBulkPrimitive_split s p.1 hε (by linarith), skewBulkPrimitive_boundary s p.2]
    ring
  rw [Filter.tendsto_congr' hev]
  unfold skewBulkFinitePart
  apply Filter.Tendsto.sub
  · have hfst : Filter.Tendsto (fun p : ℝ × ℝ => p.1) (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Filter.tendsto_fst.mono_right nhdsWithin_le_nhds
    have hsq : Filter.Tendsto (fun p : ℝ × ℝ => Real.sqrt (1 - p.1)) (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
      have hc : Continuous (fun x : ℝ => Real.sqrt (1 - x)) := (continuous_const.sub continuous_id).sqrt
      have h := (hc.continuousAt (x := (0 : ℝ))).tendsto.comp hfst
      simp only [sub_zero, Real.sqrt_one] at h
      exact h
    exact (skewBulkRegular_continuousAt_one s).tendsto.comp hsq
  · have hsnd : Filter.Tendsto (fun p : ℝ × ℝ => p.2) (nhdsWithin 0 (Set.Ioi 0) ×ˢ nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      Filter.tendsto_snd.mono_right nhdsWithin_le_nhds
    exact (skewBulkBoundaryRegular_continuousAt_zero s).tendsto.comp hsnd

end RHTower.D4BMScalarStream
