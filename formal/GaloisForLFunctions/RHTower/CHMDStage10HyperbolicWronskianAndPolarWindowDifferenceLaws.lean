import GaloisForLFunctions.RHTower.CHMDStage9OddTwoBumpConcavityAndJointParityElimination

/-!
# CHMD Stage 10: Hyperbolic Wronskian Identities, Pure Even Scale-Doubling, and Polar Window Subadditivity Laws

This module establishes the **Stage 10** exact algebraic and analytic closure of the two-bump
pole-free inequalities from Stages 8 and 9:

1. **Support Vanishing of `farSum` on `(-∞, 0]` and Pure Even Scale-Doubling on `WeilPositiveEvenPolar`
   (`farSum_eq_zero_of_nonpos`, `farSum_zero`,
   `farSum_two_mul_div_cosh_sq_le_of_weilPositiveEvenPolar`,
   `farSum_two_mul_le_cosh_mul_of_weilPositiveEvenPolar`)**:
   Because `2 * (nodeBump 2).rOut < Real.log 2`, `farKernel (Real.log n - 2 * a) = 0` for all
   `n ≥ 2` and `a ≤ 0`, so `farSum lam a = 0` on `(-∞, 0]` (in particular `farSum lam 0 = 0`).
   Evaluating the Stage 8 even two-bump midpoint inequality at `b = 0` and `a = 2 * x` (`x ≥ 1`)
   yields a **pure even-sector scale-doubling law** on `WeilPositiveEvenPolar lam` alone (without
   any odd-sector assumption):
   `farSum lam (2 * x) - 4 * Real.cosh x * farSum lam x ≤ Real.cosh x ^ 2 * (2 / π * farBumpArchMass)`.

2. **Hyperbolic Addition, Double-Angle, and Wronskian Identities for Two-Scale Pole-Free Ratios
   (`cosh_mul_sinh_sub_sinh_mul_cosh`, `cosh_mul_sinh_add_sinh_mul_cosh`,
   `two_mul_cosh_mul_sinh`, `two_mul_cosh_half_mul_sinh_half`, `cosh_half_mul_sinh_half`,
   `cosh_div_cosh_sub_sinh_div_sinh_eq`, `cosh_div_cosh_add_sinh_div_sinh_eq`,
   `cosh_div_cosh_mul_sinh_div_sinh_eq`, `sq_cosh_div_cosh_sub_sq_sinh_div_sinh_eq`,
   `sq_cosh_div_cosh_add_sq_sinh_div_sinh_eq`)**:
   For `c = cosh(b/2) / cosh(a/2)` and `s = sinh(b/2) / sinh(a/2)` (`a ≠ 0`):
   - `c - s = 2 * sinh((a - b) / 2) / sinh a`;
   - `c + s = 2 * sinh((a + b) / 2) / sinh a`;
   - `c * s = sinh b / sinh a`;
   - `c ^ 2 - s ^ 2 = 4 * sinh((a - b) / 2) * sinh((a + b) / 2) / sinh a ^ 2`;
   - `c ^ 2 + s ^ 2 = 2 * (sinh((a + b) / 2) ^ 2 + sinh((a - b) / 2) ^ 2) / sinh a ^ 2`.

3. **Wronskian-Cleared Joint Parity Elimination Laws (`wronskian_eliminate_lower_endpoint`,
   `wronskian_eliminate_midpoint`, `wronskian_eliminate_upper_endpoint`,
   `normalized_two_scale_difference_le`)**:
   Substituting the hyperbolic Wronskian identities into the three Joint Parity Elimination Laws
   of Stage 9 and clearing the positive common `sinh a` factors yields:
   - **Lower-Endpoint Elimination**:
     `(sinh((a - b) / 2) * sinh((a + b) / 2) / sinh a) * farSum lam a - sinh((a - b) / 2) * farSum lam ((a + b) / 2) - sinh((a + b) / 2) * farSum lam ((a - b) / 2) ≤ sinh a * (1 / π * farBumpArchMass)`;
   - **Midpoint Elimination**:
     `(sinh b * sinh((a - b) / 2) / sinh a) * farSum lam a - sinh((a - b) / 2) * farSum lam b - 2 * sinh b * farSum lam ((a - b) / 2) ≤ sinh((a + b) / 2) * (2 / π * farBumpArchMass)`;
   - **Upper-Endpoint Elimination (Completely Independent of `a`!)**:
     `sinh b * sinh((a - b) / 2) * farSum lam ((a + b) / 2) - sinh((a - b) / 2) * sinh((a + b) / 2) * farSum lam b - sinh b * sinh((a + b) / 2) * farSum lam ((a - b) / 2) ≤ (sinh((a + b) / 2) ^ 2 + sinh((a - b) / 2) ^ 2) * (1 / π * farBumpArchMass)`.

4. **Hyperbolic-Sine-Normalized Subadditivity and Scale-Tripling Laws
   (`farSum_add_subadditivity_mul_le`, `farSum_div_sinh_add_le`,
   `farSum_div_sinh_add_two_mul_le`, `farSum_three_mul_le_of_joint_polar`)**:
   Reparameterizing Upper-Endpoint Elimination by `u = (a - b) / 2 ≥ 1` and `v = b ≥ 0` (`a = v + 2 * u`)
   eliminates `a` completely and establishes **subadditivity** of the hyperbolic-sine-normalized
   prime window sum `Φ(x) = farSum lam x / Real.sinh x`:
   `farSum lam (u + v) / sinh(u + v) - farSum lam v / sinh v - farSum lam u / sinh u ≤ (sinh(u + v) ^ 2 + sinh u ^ 2) / (sinh u * sinh v * sinh(u + v)) * (1 / π * farBumpArchMass)`.
   Setting `a = 3 * b` (`b ≥ 1`) in Midpoint Elimination collapses `(a - b) / 2 = b` and yields the
   direct two-scale tripling inequality between `farSum lam (3 * b)` and `farSum lam b`:
   `(sinh b / sinh(3 * b)) * farSum lam (3 * b) - 3 * farSum lam b ≤ 2 * cosh b * (2 / π * farBumpArchMass)`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.CHMDStage10

open EvenSector OddSector WeilOneSided WeilPoleWeight WeilSpectral WeilMeanSquare ResonatorProfile
open CHMDStage6 CHMDStage7 CHMDStage8 CHMDStage9

/-! ## Section 1: Vanishing of `farSum` on `(-∞, 0]` and Pure Even Scale-Doubling on `WeilPositiveEvenPolar` -/

/-- **Support Vanishing of `farSum` on `(-∞, 0]`**:
because `2 * (nodeBump 2).rOut < Real.log 2`, for every `a ≤ 0` and every `n ≥ 2` we have
`Real.log n - 2 * a ≥ Real.log 2 > 2 * (nodeBump 2).rOut`, so `farKernel (Real.log n - 2 * a) = 0`
and `farSum lam a = 0`. -/
theorem farSum_eq_zero_of_nonpos (lam : ℕ → ℝ) {a : ℝ} (ha : a ≤ 0) :
    farSum lam a = 0 := by
  unfold farSum
  have h0 : (fun n : ℕ => (if 2 ≤ n then lam n / Real.sqrt n else 0) *
      farKernel (Real.log n - 2 * a)) = fun _ => 0 := by
    funext n
    split_ifs with hn
    · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos (by exact_mod_cast hn)
      have hr := two_mul_rOut_lt_log_two
      have hr0 := (nodeBump 2).rOut_pos
      rw [farKernel_eq_zero (by rw [abs_of_nonneg (by linarith)]; linarith), mul_zero]
    · ring
  rw [h0, tsum_zero]

/-- At `a = 0`, `farSum lam 0 = 0` identically for every arithmetic weight `lam : ℕ → ℝ`. -/
theorem farSum_zero (lam : ℕ → ℝ) : farSum lam 0 = 0 :=
  farSum_eq_zero_of_nonpos lam (le_refl 0)

/-- **Pure Even-Sector Scale-Doubling Inequality (Normalized Form)**:
evaluating the Stage 8 even two-bump midpoint inequality at `b = 0` and `a = 2 * x` (`1 ≤ x`)
uses `farSum lam 0 = 0` and coalesces both cross-terms at `x`:
`2 / cosh(x)^2 * farSum lam (2 * x) - 8 / cosh(x) * farSum lam x ≤ (4 / π) * farBumpArchMass`. -/
theorem farSum_two_mul_div_cosh_sq_le_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) {x : ℝ} (hx : 1 ≤ x) :
    2 / Real.cosh x ^ 2 * farSum lam (2 * x) -
      8 / Real.cosh x * farSum lam x ≤
      4 / Real.pi * farBumpArchMass := by
  have h := two_bump_cosh_normalized_midpoint_le_of_weilPositiveEvenPolar hpfe
    (b := 0) (a := 2 * x) (le_refl 0) (by linarith)
  rw [farSum_zero lam, show (0 : ℝ) / 2 = 0 by ring, Real.cosh_zero,
    show 2 * x / 2 = x by ring, show (2 * x + 0) / 2 = x by ring,
    show (2 * x - 0) / 2 = x by ring] at h
  have heq : 2 / Real.cosh x ^ 2 * farSum lam (2 * x) - 8 / Real.cosh x * farSum lam x =
      2 * 0 + 2 * (1 / Real.cosh x) ^ 2 * farSum lam (2 * x) -
        4 * (1 / Real.cosh x) * (farSum lam x + farSum lam x) := by ring
  linarith

/-- **Pure Even-Sector Scale-Doubling Inequality (Cleared-Denominator Form)**:
for every `lam` satisfying `WeilPositiveEvenPolar lam` and every `x ≥ 1`,
`farSum lam (2 * x) - 4 * Real.cosh x * farSum lam x ≤ Real.cosh x ^ 2 * (2 / π * farBumpArchMass)`. -/
theorem farSum_two_mul_le_cosh_mul_of_weilPositiveEvenPolar {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) {x : ℝ} (hx : 1 ≤ x) :
    farSum lam (2 * x) - 4 * Real.cosh x * farSum lam x ≤
      Real.cosh x ^ 2 * (2 / Real.pi * farBumpArchMass) := by
  have hc : 0 < Real.cosh x := Real.cosh_pos x
  have hne : Real.cosh x ≠ 0 := hc.ne'
  have h := mul_le_mul_of_nonneg_left
    (farSum_two_mul_div_cosh_sq_le_of_weilPositiveEvenPolar hpfe hx)
    (show 0 ≤ Real.cosh x ^ 2 / 2 by positivity)
  have hlhs : Real.cosh x ^ 2 / 2 *
      (2 / Real.cosh x ^ 2 * farSum lam (2 * x) - 8 / Real.cosh x * farSum lam x) =
      farSum lam (2 * x) - 4 * Real.cosh x * farSum lam x := by
    field_simp
    ring
  have hrhs : Real.cosh x ^ 2 / 2 * (4 / Real.pi * farBumpArchMass) =
      Real.cosh x ^ 2 * (2 / Real.pi * farBumpArchMass) := by ring
  linarith

/-! ## Section 2: Hyperbolic Addition, Double-Angle, and Wronskian Identities -/

/-- Hyperbolic sine subtraction identity:
`Real.cosh y * Real.sinh x - Real.sinh y * Real.cosh x = Real.sinh (x - y)`. -/
theorem cosh_mul_sinh_sub_sinh_mul_cosh (x y : ℝ) :
    Real.cosh y * Real.sinh x - Real.sinh y * Real.cosh x = Real.sinh (x - y) := by
  rw [Real.cosh_eq y, Real.sinh_eq x, Real.sinh_eq y, Real.cosh_eq x, Real.sinh_eq (x - y),
    show x - y = x + -y by ring, show -(x + -y) = y + -x by ring,
    Real.exp_add x (-y), Real.exp_add y (-x)]
  ring

/-- Hyperbolic sine addition identity:
`Real.cosh y * Real.sinh x + Real.sinh y * Real.cosh x = Real.sinh (x + y)`. -/
theorem cosh_mul_sinh_add_sinh_mul_cosh (x y : ℝ) :
    Real.cosh y * Real.sinh x + Real.sinh y * Real.cosh x = Real.sinh (x + y) := by
  rw [Real.cosh_eq y, Real.sinh_eq x, Real.sinh_eq y, Real.cosh_eq x, Real.sinh_eq (x + y),
    show -(x + y) = -x + -y by ring, Real.exp_add x y, Real.exp_add (-x) (-y)]
  ring

/-- Hyperbolic sine double-angle identity:
`2 * Real.cosh x * Real.sinh x = Real.sinh (2 * x)`. -/
theorem two_mul_cosh_mul_sinh (x : ℝ) :
    2 * Real.cosh x * Real.sinh x = Real.sinh (2 * x) := by
  have h := cosh_mul_sinh_add_sinh_mul_cosh x x
  rw [show x + x = 2 * x by ring] at h
  linarith

/-- Half-angle hyperbolic sine product identity:
`2 * Real.cosh (a / 2) * Real.sinh (a / 2) = Real.sinh a`. -/
theorem two_mul_cosh_half_mul_sinh_half (a : ℝ) :
    2 * Real.cosh (a / 2) * Real.sinh (a / 2) = Real.sinh a := by
  rw [two_mul_cosh_mul_sinh (a / 2), show 2 * (a / 2) = a by ring]

/-- Half-angle hyperbolic sine product:
`Real.cosh (a / 2) * Real.sinh (a / 2) = Real.sinh a / 2`. -/
theorem cosh_half_mul_sinh_half (a : ℝ) :
    Real.cosh (a / 2) * Real.sinh (a / 2) = Real.sinh a / 2 := by
  linarith [two_mul_cosh_half_mul_sinh_half a]

/-- **Hyperbolic Wronskian Difference Identity (`c - s`)**:
for `a ≠ 0`,
`Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2) = 2 * Real.sinh ((a - b) / 2) / Real.sinh a`. -/
theorem cosh_div_cosh_sub_sinh_div_sinh_eq {b a : ℝ} (ha : a ≠ 0) :
    Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2) =
      2 * Real.sinh ((a - b) / 2) / Real.sinh a := by
  have hca : Real.cosh (a / 2) ≠ 0 := (Real.cosh_pos (a / 2)).ne'
  have hsa : Real.sinh (a / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero ha two_ne_zero)
  rw [div_sub_div _ _ hca hsa, cosh_half_mul_sinh_half a,
    show Real.cosh (b / 2) * Real.sinh (a / 2) - Real.cosh (a / 2) * Real.sinh (b / 2) =
      Real.cosh (b / 2) * Real.sinh (a / 2) - Real.sinh (b / 2) * Real.cosh (a / 2) by ring,
    cosh_mul_sinh_sub_sinh_mul_cosh (a / 2) (b / 2),
    show a / 2 - b / 2 = (a - b) / 2 by ring]
  ring

/-- **Hyperbolic Wronskian Sum Identity (`c + s`)**:
for `a ≠ 0`,
`Real.cosh (b / 2) / Real.cosh (a / 2) + Real.sinh (b / 2) / Real.sinh (a / 2) = 2 * Real.sinh ((a + b) / 2) / Real.sinh a`. -/
theorem cosh_div_cosh_add_sinh_div_sinh_eq {b a : ℝ} (ha : a ≠ 0) :
    Real.cosh (b / 2) / Real.cosh (a / 2) + Real.sinh (b / 2) / Real.sinh (a / 2) =
      2 * Real.sinh ((a + b) / 2) / Real.sinh a := by
  have hca : Real.cosh (a / 2) ≠ 0 := (Real.cosh_pos (a / 2)).ne'
  have hsa : Real.sinh (a / 2) ≠ 0 := Real.sinh_ne_zero.mpr (div_ne_zero ha two_ne_zero)
  rw [div_add_div _ _ hca hsa, cosh_half_mul_sinh_half a,
    show Real.cosh (b / 2) * Real.sinh (a / 2) + Real.cosh (a / 2) * Real.sinh (b / 2) =
      Real.cosh (b / 2) * Real.sinh (a / 2) + Real.sinh (b / 2) * Real.cosh (a / 2) by ring,
    cosh_mul_sinh_add_sinh_mul_cosh (a / 2) (b / 2),
    show a / 2 + b / 2 = (a + b) / 2 by ring]
  ring

/-- **Hyperbolic Wronskian Product Identity (`c * s`)**:
`(Real.cosh (b / 2) / Real.cosh (a / 2)) * (Real.sinh (b / 2) / Real.sinh (a / 2)) = Real.sinh b / Real.sinh a`. -/
theorem cosh_div_cosh_mul_sinh_div_sinh_eq (b a : ℝ) :
    (Real.cosh (b / 2) / Real.cosh (a / 2)) * (Real.sinh (b / 2) / Real.sinh (a / 2)) =
      Real.sinh b / Real.sinh a := by
  rw [div_mul_div_comm, cosh_half_mul_sinh_half b, cosh_half_mul_sinh_half a]
  ring

/-- **Hyperbolic Wronskian Difference-of-Squares Identity (`c ^ 2 - s ^ 2`)**:
for `a ≠ 0`,
`(Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 - (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 = 4 * Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) / Real.sinh a ^ 2`. -/
theorem sq_cosh_div_cosh_sub_sq_sinh_div_sinh_eq {b a : ℝ} (ha : a ≠ 0) :
    (Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 -
      (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 =
      4 * Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) / Real.sinh a ^ 2 := by
  rw [sq_sub_sq, cosh_div_cosh_add_sinh_div_sinh_eq ha, cosh_div_cosh_sub_sinh_div_sinh_eq ha]
  ring

/-- **Hyperbolic Wronskian Sum-of-Squares Identity (`c ^ 2 + s ^ 2`)**:
for `a ≠ 0`,
`(Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 + (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 = 2 * (Real.sinh ((a + b) / 2) ^ 2 + Real.sinh ((a - b) / 2) ^ 2) / Real.sinh a ^ 2`. -/
theorem sq_cosh_div_cosh_add_sq_sinh_div_sinh_eq {b a : ℝ} (ha : a ≠ 0) :
    (Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 +
      (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 =
      2 * (Real.sinh ((a + b) / 2) ^ 2 + Real.sinh ((a - b) / 2) ^ 2) / Real.sinh a ^ 2 := by
  have h : (Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 +
      (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 =
      ((Real.cosh (b / 2) / Real.cosh (a / 2) + Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2 +
        (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2) / 2 := by
    ring
  rw [h, cosh_div_cosh_add_sinh_div_sinh_eq ha, cosh_div_cosh_sub_sinh_div_sinh_eq ha]
  ring

/-! ## Section 3: Wronskian-Cleared Joint Parity Elimination Laws -/

/-- **Wronskian Lower-Endpoint Elimination Law**:
substituting the hyperbolic Wronskian identities into `joint_two_bump_eliminate_lower_endpoint`
and multiplying by `Real.sinh a / 8 > 0` yields:
`(sinh((a - b) / 2) * sinh((a + b) / 2) / sinh a) * farSum lam a - sinh((a - b) / 2) * farSum lam ((a + b) / 2) - sinh((a + b) / 2) * farSum lam ((a - b) / 2) ≤ sinh a * (1 / π * farBumpArchMass)`. -/
theorem wronskian_eliminate_lower_endpoint {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    (Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) / Real.sinh a) * farSum lam a -
      Real.sinh ((a - b) / 2) * farSum lam ((a + b) / 2) -
      Real.sinh ((a + b) / 2) * farSum lam ((a - b) / 2) ≤
      Real.sinh a * (1 / Real.pi * farBumpArchMass) := by
  have ha : 0 < a := by linarith
  have hsa : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hsane : Real.sinh a ≠ 0 := hsa.ne'
  have h1 := joint_two_bump_eliminate_lower_endpoint hpfe hpfo hb hba
  dsimp only at h1
  rw [sq_cosh_div_cosh_sub_sq_sinh_div_sinh_eq ha.ne',
    cosh_div_cosh_sub_sinh_div_sinh_eq ha.ne',
    cosh_div_cosh_add_sinh_div_sinh_eq ha.ne'] at h1
  have hm := mul_le_mul_of_nonneg_left h1 (show 0 ≤ Real.sinh a / 8 by positivity)
  have hlhs : Real.sinh a / 8 *
      (2 * (4 * Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) / Real.sinh a ^ 2) *
          farSum lam a -
        4 * (2 * Real.sinh ((a - b) / 2) / Real.sinh a) * farSum lam ((a + b) / 2) -
        4 * (2 * Real.sinh ((a + b) / 2) / Real.sinh a) * farSum lam ((a - b) / 2)) =
      (Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) / Real.sinh a) * farSum lam a -
        Real.sinh ((a - b) / 2) * farSum lam ((a + b) / 2) -
        Real.sinh ((a + b) / 2) * farSum lam ((a - b) / 2) := by
    field_simp
    ring
  have hrhs : Real.sinh a / 8 * (8 / Real.pi * farBumpArchMass) =
      Real.sinh a * (1 / Real.pi * farBumpArchMass) := by ring
  linarith

/-- **Wronskian Midpoint Elimination Law**:
substituting the hyperbolic Wronskian identities into `joint_two_bump_eliminate_midpoint`
and multiplying by `Real.sinh a / 4 > 0` yields:
`(sinh b * sinh((a - b) / 2) / sinh a) * farSum lam a - sinh((a - b) / 2) * farSum lam b - 2 * sinh b * farSum lam ((a - b) / 2) ≤ sinh((a + b) / 2) * (2 / π * farBumpArchMass)`. -/
theorem wronskian_eliminate_midpoint {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    (Real.sinh b * Real.sinh ((a - b) / 2) / Real.sinh a) * farSum lam a -
      Real.sinh ((a - b) / 2) * farSum lam b -
      2 * Real.sinh b * farSum lam ((a - b) / 2) ≤
      Real.sinh ((a + b) / 2) * (2 / Real.pi * farBumpArchMass) := by
  have ha : 0 < a := by linarith
  have hsa : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hsane : Real.sinh a ≠ 0 := hsa.ne'
  have h2 := joint_two_bump_eliminate_midpoint hpfe hpfo hb hba
  dsimp only at h2
  have hcs := cosh_div_cosh_mul_sinh_div_sinh_eq b a
  have hsub := cosh_div_cosh_sub_sinh_div_sinh_eq (b := b) ha.ne'
  have hadd := cosh_div_cosh_add_sinh_div_sinh_eq (b := b) ha.ne'
  have hrew : 2 * (Real.cosh (b / 2) / Real.cosh (a / 2)) *
        (Real.sinh (b / 2) / Real.sinh (a / 2)) *
        (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
        farSum lam a -
      2 * (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
        farSum lam b -
      8 * (Real.cosh (b / 2) / Real.cosh (a / 2)) * (Real.sinh (b / 2) / Real.sinh (a / 2)) *
        farSum lam ((a - b) / 2) =
      2 * (Real.sinh b / Real.sinh a) * (2 * Real.sinh ((a - b) / 2) / Real.sinh a) *
        farSum lam a -
      2 * (2 * Real.sinh ((a - b) / 2) / Real.sinh a) * farSum lam b -
      8 * (Real.sinh b / Real.sinh a) * farSum lam ((a - b) / 2) := by
    calc 2 * (Real.cosh (b / 2) / Real.cosh (a / 2)) *
          (Real.sinh (b / 2) / Real.sinh (a / 2)) *
          (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam a -
        2 * (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam b -
        8 * (Real.cosh (b / 2) / Real.cosh (a / 2)) * (Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam ((a - b) / 2)
        = 2 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) *
            (Real.sinh (b / 2) / Real.sinh (a / 2))) *
          (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam a -
        2 * (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam b -
        8 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) *
          (Real.sinh (b / 2) / Real.sinh (a / 2))) * farSum lam ((a - b) / 2) := by ring
      _ = _ := by rw [hcs, hsub]
  rw [hrew, hadd] at h2
  have hm := mul_le_mul_of_nonneg_left h2 (show 0 ≤ Real.sinh a / 4 by positivity)
  have hlhs : Real.sinh a / 4 *
      (2 * (Real.sinh b / Real.sinh a) * (2 * Real.sinh ((a - b) / 2) / Real.sinh a) *
          farSum lam a -
        2 * (2 * Real.sinh ((a - b) / 2) / Real.sinh a) * farSum lam b -
        8 * (Real.sinh b / Real.sinh a) * farSum lam ((a - b) / 2)) =
      (Real.sinh b * Real.sinh ((a - b) / 2) / Real.sinh a) * farSum lam a -
        Real.sinh ((a - b) / 2) * farSum lam b -
        2 * Real.sinh b * farSum lam ((a - b) / 2) := by
    field_simp
    ring
  have hrhs : Real.sinh a / 4 *
      (2 * Real.sinh ((a + b) / 2) / Real.sinh a * (4 / Real.pi * farBumpArchMass)) =
      Real.sinh ((a + b) / 2) * (2 / Real.pi * farBumpArchMass) := by
    field_simp
  linarith

/-- **Normalized Two-Scale Window Difference Law**:
dividing `wronskian_eliminate_midpoint` by `Real.sinh ((a - b) / 2) > 0` yields:
`(sinh b / sinh a) * farSum lam a - farSum lam b - (2 * sinh b / sinh((a - b) / 2)) * farSum lam ((a - b) / 2) ≤ (sinh((a + b) / 2) / sinh((a - b) / 2)) * (2 / π * farBumpArchMass)`. -/
theorem normalized_two_scale_difference_le {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    (Real.sinh b / Real.sinh a) * farSum lam a -
      farSum lam b -
      (2 * Real.sinh b / Real.sinh ((a - b) / 2)) * farSum lam ((a - b) / 2) ≤
      (Real.sinh ((a + b) / 2) / Real.sinh ((a - b) / 2)) *
        (2 / Real.pi * farBumpArchMass) := by
  have ha : 0 < a := by linarith
  have hsa : (Real.sinh a : ℝ) ≠ 0 := (Real.sinh_pos_iff.mpr ha).ne'
  have hsab : 0 < Real.sinh ((a - b) / 2) := Real.sinh_pos_iff.mpr (by linarith)
  have hsabne : Real.sinh ((a - b) / 2) ≠ 0 := hsab.ne'
  have hm := mul_le_mul_of_nonneg_left
    (wronskian_eliminate_midpoint hpfe hpfo hb hba)
    (show 0 ≤ 1 / Real.sinh ((a - b) / 2) by positivity)
  have hlhs : 1 / Real.sinh ((a - b) / 2) *
      ((Real.sinh b * Real.sinh ((a - b) / 2) / Real.sinh a) * farSum lam a -
        Real.sinh ((a - b) / 2) * farSum lam b -
        2 * Real.sinh b * farSum lam ((a - b) / 2)) =
      (Real.sinh b / Real.sinh a) * farSum lam a -
        farSum lam b -
        (2 * Real.sinh b / Real.sinh ((a - b) / 2)) * farSum lam ((a - b) / 2) := by
    field_simp
  have hrhs : 1 / Real.sinh ((a - b) / 2) *
      (Real.sinh ((a + b) / 2) * (2 / Real.pi * farBumpArchMass)) =
      (Real.sinh ((a + b) / 2) / Real.sinh ((a - b) / 2)) *
        (2 / Real.pi * farBumpArchMass) := by ring
  linarith

/-- **Wronskian Upper-Endpoint Elimination Law (Denominator-Free & Independent of `a`!)**:
substituting the hyperbolic Wronskian identities into `joint_two_bump_eliminate_upper_endpoint`
and multiplying by `Real.sinh a ^ 2 / 8 > 0` clears `Real.sinh a` completely:
`sinh b * sinh((a - b) / 2) * farSum lam ((a + b) / 2) - sinh((a - b) / 2) * sinh((a + b) / 2) * farSum lam b - sinh b * sinh((a + b) / 2) * farSum lam ((a - b) / 2) ≤ (sinh((a + b) / 2) ^ 2 + sinh((a - b) / 2) ^ 2) * (1 / π * farBumpArchMass)`. -/
theorem wronskian_eliminate_upper_endpoint {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {b a : ℝ} (hb : 0 ≤ b) (hba : b + 2 ≤ a) :
    Real.sinh b * Real.sinh ((a - b) / 2) * farSum lam ((a + b) / 2) -
      Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) * farSum lam b -
      Real.sinh b * Real.sinh ((a + b) / 2) * farSum lam ((a - b) / 2) ≤
      (Real.sinh ((a + b) / 2) ^ 2 + Real.sinh ((a - b) / 2) ^ 2) *
        (1 / Real.pi * farBumpArchMass) := by
  have ha : 0 < a := by linarith
  have hsa : 0 < Real.sinh a := Real.sinh_pos_iff.mpr ha
  have hsane : Real.sinh a ≠ 0 := hsa.ne'
  have h3 := joint_two_bump_eliminate_upper_endpoint hpfe hpfo hb hba
  dsimp only at h3
  have hcs := cosh_div_cosh_mul_sinh_div_sinh_eq b a
  have hsub := cosh_div_cosh_sub_sinh_div_sinh_eq (b := b) ha.ne'
  have hadd := cosh_div_cosh_add_sinh_div_sinh_eq (b := b) ha.ne'
  have hsqsub := sq_cosh_div_cosh_sub_sq_sinh_div_sinh_eq (b := b) ha.ne'
  have hsqadd := sq_cosh_div_cosh_add_sq_sinh_div_sinh_eq (b := b) ha.ne'
  have hrew : 4 * (Real.cosh (b / 2) / Real.cosh (a / 2)) *
        (Real.sinh (b / 2) / Real.sinh (a / 2)) *
        (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
        farSum lam ((a + b) / 2) -
      2 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 -
        (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2) * farSum lam b -
      4 * (Real.cosh (b / 2) / Real.cosh (a / 2)) * (Real.sinh (b / 2) / Real.sinh (a / 2)) *
        (Real.cosh (b / 2) / Real.cosh (a / 2) + Real.sinh (b / 2) / Real.sinh (a / 2)) *
        farSum lam ((a - b) / 2) =
      4 * (Real.sinh b / Real.sinh a) * (2 * Real.sinh ((a - b) / 2) / Real.sinh a) *
        farSum lam ((a + b) / 2) -
      2 * (4 * Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) / Real.sinh a ^ 2) *
        farSum lam b -
      4 * (Real.sinh b / Real.sinh a) * (2 * Real.sinh ((a + b) / 2) / Real.sinh a) *
        farSum lam ((a - b) / 2) := by
    calc 4 * (Real.cosh (b / 2) / Real.cosh (a / 2)) *
          (Real.sinh (b / 2) / Real.sinh (a / 2)) *
          (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam ((a + b) / 2) -
        2 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 -
          (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2) * farSum lam b -
        4 * (Real.cosh (b / 2) / Real.cosh (a / 2)) * (Real.sinh (b / 2) / Real.sinh (a / 2)) *
          (Real.cosh (b / 2) / Real.cosh (a / 2) + Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam ((a - b) / 2)
        = 4 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) *
            (Real.sinh (b / 2) / Real.sinh (a / 2))) *
          (Real.cosh (b / 2) / Real.cosh (a / 2) - Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam ((a + b) / 2) -
        2 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) ^ 2 -
          (Real.sinh (b / 2) / Real.sinh (a / 2)) ^ 2) * farSum lam b -
        4 * ((Real.cosh (b / 2) / Real.cosh (a / 2)) *
          (Real.sinh (b / 2) / Real.sinh (a / 2))) *
          (Real.cosh (b / 2) / Real.cosh (a / 2) + Real.sinh (b / 2) / Real.sinh (a / 2)) *
          farSum lam ((a - b) / 2) := by ring
      _ = _ := by rw [hcs, hsub, hsqsub, hadd]
  rw [hrew, hsqadd] at h3
  have hm := mul_le_mul_of_nonneg_left h3 (show 0 ≤ Real.sinh a ^ 2 / 8 by positivity)
  have hlhs : Real.sinh a ^ 2 / 8 *
      (4 * (Real.sinh b / Real.sinh a) * (2 * Real.sinh ((a - b) / 2) / Real.sinh a) *
          farSum lam ((a + b) / 2) -
        2 * (4 * Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) / Real.sinh a ^ 2) *
          farSum lam b -
        4 * (Real.sinh b / Real.sinh a) * (2 * Real.sinh ((a + b) / 2) / Real.sinh a) *
          farSum lam ((a - b) / 2)) =
      Real.sinh b * Real.sinh ((a - b) / 2) * farSum lam ((a + b) / 2) -
        Real.sinh ((a - b) / 2) * Real.sinh ((a + b) / 2) * farSum lam b -
        Real.sinh b * Real.sinh ((a + b) / 2) * farSum lam ((a - b) / 2) := by
    field_simp
    ring
  have hrhs : Real.sinh a ^ 2 / 8 *
      (2 * (Real.sinh ((a + b) / 2) ^ 2 + Real.sinh ((a - b) / 2) ^ 2) / Real.sinh a ^ 2 *
        (4 / Real.pi * farBumpArchMass)) =
      (Real.sinh ((a + b) / 2) ^ 2 + Real.sinh ((a - b) / 2) ^ 2) *
        (1 / Real.pi * farBumpArchMass) := by
    field_simp
    ring
  linarith

/-! ## Section 4: Hyperbolic-Sine-Normalized Subadditivity and Scale-Tripling Laws -/

/-- **Additive Reparameterization of Upper-Endpoint Elimination (`u ≥ 1`, `v ≥ 0`)**:
setting `b = v ≥ 0` and `a = v + 2 * u` (`1 ≤ u`) in `wronskian_eliminate_upper_endpoint`
gives `(a - b) / 2 = u` and `(a + b) / 2 = u + v`:
`sinh v * sinh u * farSum lam (u + v) - sinh u * sinh (u + v) * farSum lam v - sinh v * sinh (u + v) * farSum lam u ≤ (sinh (u + v) ^ 2 + sinh u ^ 2) * (1 / π * farBumpArchMass)`. -/
theorem farSum_add_subadditivity_mul_le {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {u v : ℝ} (hu : 1 ≤ u) (hv : 0 ≤ v) :
    Real.sinh v * Real.sinh u * farSum lam (u + v) -
      Real.sinh u * Real.sinh (u + v) * farSum lam v -
      Real.sinh v * Real.sinh (u + v) * farSum lam u ≤
      (Real.sinh (u + v) ^ 2 + Real.sinh u ^ 2) * (1 / Real.pi * farBumpArchMass) := by
  have h := wronskian_eliminate_upper_endpoint hpfe hpfo (b := v) (a := v + 2 * u)
    hv (by linarith)
  rw [show (v + 2 * u - v) / 2 = u by ring, show (v + 2 * u + v) / 2 = u + v by ring] at h
  exact h

/-- **Hyperbolic-Sine-Normalized Subadditivity Law (`Φ(u + v) ≤ Φ(v) + Φ(u) + ...`)**:
for every `1 ≤ u` and `0 < v`, dividing `farSum_add_subadditivity_mul_le` by
`Real.sinh u * Real.sinh v * Real.sinh (u + v) > 0` yields:
`farSum lam (u + v) / sinh (u + v) - farSum lam v / sinh v - farSum lam u / sinh u ≤ (sinh (u + v) ^ 2 + sinh u ^ 2) / (sinh u * sinh v * sinh (u + v)) * (1 / π * farBumpArchMass)`. -/
theorem farSum_div_sinh_add_le {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {u v : ℝ} (hu : 1 ≤ u) (hv : 0 < v) :
    farSum lam (u + v) / Real.sinh (u + v) -
      farSum lam v / Real.sinh v -
      farSum lam u / Real.sinh u ≤
      (Real.sinh (u + v) ^ 2 + Real.sinh u ^ 2) /
        (Real.sinh u * Real.sinh v * Real.sinh (u + v)) *
        (1 / Real.pi * farBumpArchMass) := by
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr (by linarith)
  have hsv : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have hsuv : 0 < Real.sinh (u + v) := Real.sinh_pos_iff.mpr (by linarith)
  have hsune : Real.sinh u ≠ 0 := hsu.ne'
  have hsvne : Real.sinh v ≠ 0 := hsv.ne'
  have hsuvne : Real.sinh (u + v) ≠ 0 := hsuv.ne'
  have hm := mul_le_mul_of_nonneg_left
    (farSum_add_subadditivity_mul_le hpfe hpfo hu hv.le)
    (show 0 ≤ 1 / (Real.sinh u * Real.sinh v * Real.sinh (u + v)) by positivity)
  have hlhs : 1 / (Real.sinh u * Real.sinh v * Real.sinh (u + v)) *
      (Real.sinh v * Real.sinh u * farSum lam (u + v) -
        Real.sinh u * Real.sinh (u + v) * farSum lam v -
        Real.sinh v * Real.sinh (u + v) * farSum lam u) =
      farSum lam (u + v) / Real.sinh (u + v) -
        farSum lam v / Real.sinh v -
        farSum lam u / Real.sinh u := by
    field_simp
  have hrhs : 1 / (Real.sinh u * Real.sinh v * Real.sinh (u + v)) *
      ((Real.sinh (u + v) ^ 2 + Real.sinh u ^ 2) * (1 / Real.pi * farBumpArchMass)) =
      (Real.sinh (u + v) ^ 2 + Real.sinh u ^ 2) /
        (Real.sinh u * Real.sinh v * Real.sinh (u + v)) *
        (1 / Real.pi * farBumpArchMass) := by ring
  linarith

/-- **Hyperbolic-Sine-Normalized Two-Step Subadditivity Law (`Φ(v + 2u) ≤ Φ(v) + 2 Φ(u) + ...`)**:
setting `b = v > 0` and `a = v + 2 * u` (`1 ≤ u`) in `normalized_two_scale_difference_le`
and dividing by `Real.sinh v > 0` yields:
`farSum lam (v + 2 * u) / sinh (v + 2 * u) - farSum lam v / sinh v - 2 * (farSum lam u / sinh u) ≤ (sinh (v + u) / (sinh u * sinh v)) * (2 / π * farBumpArchMass)`. -/
theorem farSum_div_sinh_add_two_mul_le {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {u v : ℝ} (hu : 1 ≤ u) (hv : 0 < v) :
    farSum lam (v + 2 * u) / Real.sinh (v + 2 * u) -
      farSum lam v / Real.sinh v -
      2 * (farSum lam u / Real.sinh u) ≤
      (Real.sinh (v + u) / (Real.sinh u * Real.sinh v)) *
        (2 / Real.pi * farBumpArchMass) := by
  have hsu : 0 < Real.sinh u := Real.sinh_pos_iff.mpr (by linarith)
  have hsv : 0 < Real.sinh v := Real.sinh_pos_iff.mpr hv
  have hsv2u : 0 < Real.sinh (v + 2 * u) := Real.sinh_pos_iff.mpr (by linarith)
  have hsune : Real.sinh u ≠ 0 := hsu.ne'
  have hsvne : Real.sinh v ≠ 0 := hsv.ne'
  have hsv2une : Real.sinh (v + 2 * u) ≠ 0 := hsv2u.ne'
  have h := normalized_two_scale_difference_le hpfe hpfo (b := v) (a := v + 2 * u)
    hv.le (by linarith)
  rw [show (v + 2 * u - v) / 2 = u by ring, show (v + 2 * u + v) / 2 = v + u by ring] at h
  have hm := mul_le_mul_of_nonneg_left h (show 0 ≤ 1 / Real.sinh v by positivity)
  have hlhs : 1 / Real.sinh v *
      ((Real.sinh v / Real.sinh (v + 2 * u)) * farSum lam (v + 2 * u) -
        farSum lam v -
        (2 * Real.sinh v / Real.sinh u) * farSum lam u) =
      farSum lam (v + 2 * u) / Real.sinh (v + 2 * u) -
        farSum lam v / Real.sinh v -
        2 * (farSum lam u / Real.sinh u) := by
    field_simp
  have hrhs : 1 / Real.sinh v *
      ((Real.sinh (v + u) / Real.sinh u) * (2 / Real.pi * farBumpArchMass)) =
      (Real.sinh (v + u) / (Real.sinh u * Real.sinh v)) *
        (2 / Real.pi * farBumpArchMass) := by ring
  linarith

/-- **Two-Scale Tripling Inequality (`a = 3 * b`, `b ≥ 1`)**:
at `a = 3 * b` (`b ≥ 1`), the same-side cross-scale `(a - b) / 2` equals `b`, so
`normalized_two_scale_difference_le` collapses to a direct two-scale relation between
`farSum lam (3 * b)` and `farSum lam b`:
`(sinh b / sinh (3 * b)) * farSum lam (3 * b) - 3 * farSum lam b ≤ 2 * cosh b * (2 / π * farBumpArchMass)`. -/
theorem farSum_three_mul_le_of_joint_polar {lam : ℕ → ℝ}
    (hpfe : WeilPositiveEvenPolar lam) (hpfo : CHMDStage9.WeilPositiveOddPolar lam)
    {b : ℝ} (hb : 1 ≤ b) :
    (Real.sinh b / Real.sinh (3 * b)) * farSum lam (3 * b) -
      3 * farSum lam b ≤
      2 * Real.cosh b * (2 / Real.pi * farBumpArchMass) := by
  have hsb : 0 < Real.sinh b := Real.sinh_pos_iff.mpr (by linarith)
  have hsbne : Real.sinh b ≠ 0 := hsb.ne'
  have h := normalized_two_scale_difference_le hpfe hpfo (b := b) (a := 3 * b)
    (by linarith) (by linarith)
  rw [show (3 * b - b) / 2 = b by ring, show (3 * b + b) / 2 = 2 * b by ring,
    ← two_mul_cosh_mul_sinh b] at h
  have hlhs : (Real.sinh b / Real.sinh (3 * b)) * farSum lam (3 * b) -
      farSum lam b -
      (2 * Real.sinh b / Real.sinh b) * farSum lam b =
      (Real.sinh b / Real.sinh (3 * b)) * farSum lam (3 * b) - 3 * farSum lam b := by
    field_simp
    ring
  have hrhs : (2 * Real.cosh b * Real.sinh b / Real.sinh b) *
      (2 / Real.pi * farBumpArchMass) =
      2 * Real.cosh b * (2 / Real.pi * farBumpArchMass) := by
    field_simp
  linarith

end RHTower.CHMDStage10

end
