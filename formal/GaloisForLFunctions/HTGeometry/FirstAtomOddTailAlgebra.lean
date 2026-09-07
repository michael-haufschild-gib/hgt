import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Explicit first-atom odd determinant reserve at inverse scale at most 1/30

The five signed Gaussian-scale reflection moments are rational functions with
one common positive denominator. Exact polynomial identities give both a
fixed determinant floor and entry bounds for quantitative source perturbation.
-/

namespace HTGeometry
noncomputable section

/-- Common first-atom Gaussian-scale denominator. -/
def firstAtomOddTailDenominator (u : ℝ) : ℝ := (4-6*u)^2

/-- Numerator of signed first-atom Gaussian moment 1. -/
def firstAtomOddTailNumerator1 (u : ℝ) : ℝ :=
  (128 : ℝ) +
    (-384 : ℝ)*u^1 +
    (480 : ℝ)*u^2

/-- Signed first-atom Gaussian moment 1, in inverse scale. -/
def firstAtomOddTailProfile1 (u : ℝ) : ℝ :=
  firstAtomOddTailNumerator1 u / firstAtomOddTailDenominator u

/-- Numerator of signed first-atom Gaussian moment 2. -/
def firstAtomOddTailNumerator2 (u : ℝ) : ℝ :=
  (3072 : ℝ) +
    (-9728 : ℝ)*u^1 +
    (17664 : ℝ)*u^2 +
    (-1920 : ℝ)*u^3

/-- Signed first-atom Gaussian moment 2, in inverse scale. -/
def firstAtomOddTailProfile2 (u : ℝ) : ℝ :=
  firstAtomOddTailNumerator2 u / firstAtomOddTailDenominator u

/-- Numerator of signed first-atom Gaussian moment 3. -/
def firstAtomOddTailNumerator3 (u : ℝ) : ℝ :=
  (122880 : ℝ) +
    (-430080 : ℝ)*u^1 +
    (1015808 : ℝ)*u^2 +
    (-328704 : ℝ)*u^3 +
    (7680 : ℝ)*u^4

/-- Signed first-atom Gaussian moment 3, in inverse scale. -/
def firstAtomOddTailProfile3 (u : ℝ) : ℝ :=
  firstAtomOddTailNumerator3 u / firstAtomOddTailDenominator u

/-- Numerator of signed first-atom Gaussian moment 4. -/
def firstAtomOddTailNumerator4 (u : ℝ) : ℝ :=
  (6881280 : ℝ) +
    (-27525120 : ℝ)*u^1 +
    (78446592 : ℝ)*u^2 +
    (-49553408 : ℝ)*u^3 +
    (5443584 : ℝ)*u^4 +
    (-30720 : ℝ)*u^5

/-- Signed first-atom Gaussian moment 4, in inverse scale. -/
def firstAtomOddTailProfile4 (u : ℝ) : ℝ :=
  firstAtomOddTailNumerator4 u / firstAtomOddTailDenominator u

/-- Numerator of signed first-atom Gaussian moment 5. -/
def firstAtomOddTailNumerator5 (u : ℝ) : ℝ :=
  (495452160 : ℝ) +
    (-2312110080 : ℝ)*u^1 +
    (7596933120 : ℝ)*u^2 +
    (-7696220160 : ℝ)*u^3 +
    (2001010688 : ℝ)*u^4 +
    (-87834624 : ℝ)*u^5 +
    (122880 : ℝ)*u^6

/-- Signed first-atom Gaussian moment 5, in inverse scale. -/
def firstAtomOddTailProfile5 (u : ℝ) : ℝ :=
  firstAtomOddTailNumerator5 u / firstAtomOddTailDenominator u

/-- Odd rank-three determinant of the five signed Gaussian-scale moments. -/
def firstAtomOddTailDet (u : ℝ) : ℝ :=
  let a := firstAtomOddTailProfile1 u
  let b := firstAtomOddTailProfile2 u
  let c := firstAtomOddTailProfile3 u
  let d := firstAtomOddTailProfile4 u
  let e := firstAtomOddTailProfile5 u
  a*c*e-a*d^2-b^2*e+2*b*c*d-c^3

/-- Exact numerator after cancellation of the three highest formal degrees. -/
def firstAtomOddTailDetNumerator (u : ℝ) : ℝ :=
  (395824185999360 : ℝ) +
    (-4848846278492160 : ℝ)*u^1 +
    (31393805752074240 : ℝ)*u^2 +
    (-128024385159168000 : ℝ)*u^3 +
    (348949943722967040 : ℝ)*u^4 +
    (-645131575649894400 : ℝ)*u^5 +
    (783383995927756800 : ℝ)*u^6 +
    (-587172709977292800 : ℝ)*u^7 +
    (246568703754240000 : ℝ)*u^8 +
    (-49313740750848000 : ℝ)*u^9

/-- The complete first-atom odd determinant retains the common denominator cubed. -/
theorem firstAtomOddTailDet_eq_ratio (u : ℝ) (hD : firstAtomOddTailDenominator u ≠ 0) :
    firstAtomOddTailDet u = firstAtomOddTailDetNumerator u / firstAtomOddTailDenominator u^3 := by
  unfold firstAtomOddTailDet
  dsimp only
  unfold firstAtomOddTailProfile1 firstAtomOddTailProfile2 firstAtomOddTailProfile3 firstAtomOddTailProfile4 firstAtomOddTailProfile5
    firstAtomOddTailNumerator1 firstAtomOddTailNumerator2 firstAtomOddTailNumerator3 firstAtomOddTailNumerator4 firstAtomOddTailNumerator5 firstAtomOddTailDetNumerator
  field_simp [hD]
  ring

/-- The common denominator has a fixed positive margin throughout the explicit inverse-scale interval. -/
theorem firstAtomOddTailDenominator_lower {u : ℝ} (_hu0 : 0 ≤ u) (hu1 : u ≤ 1/30) :
    9 ≤ firstAtomOddTailDenominator u := by
  have h : 3 ≤ 4-6*u := by linarith
  unfold firstAtomOddTailDenominator
  nlinarith [sq_nonneg (4-6*u-3)]

/-- The first-atom determinant has a uniform explicit positive reserve. -/
theorem firstAtomOddTailDet_lower {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/30) :
    50000000000 ≤ firstAtomOddTailDet u := by
  have hD : 0 < firstAtomOddTailDenominator u := by
    have h := firstAtomOddTailDenominator_lower hu0 hu1
    linarith
  rw [firstAtomOddTailDet_eq_ratio u hD.ne']
  apply (le_div_iff₀ (pow_pos hD 3)).mpr
  have hn2 : 0 ≤ u^2 := pow_nonneg hu0 2
  have hn3 : 0 ≤ u^3 := pow_nonneg hu0 3
  have hn4 : 0 ≤ u^4 := pow_nonneg hu0 4
  have hn5 : 0 ≤ u^5 := pow_nonneg hu0 5
  have hn6 : 0 ≤ u^6 := pow_nonneg hu0 6
  have hn7 : 0 ≤ u^7 := pow_nonneg hu0 7
  have hn8 : 0 ≤ u^8 := pow_nonneg hu0 8
  have hn9 : 0 ≤ u^9 := pow_nonneg hu0 9
  have hu3 := pow_le_pow_left₀ hu0 hu1 3
  have hu5 := pow_le_pow_left₀ hu0 hu1 5
  have hu7 := pow_le_pow_left₀ hu0 hu1 7
  have hu9 := pow_le_pow_left₀ hu0 hu1 9
  unfold firstAtomOddTailDetNumerator firstAtomOddTailDenominator
  norm_num at hu3 hu5 hu7 hu9
  nlinarith

/-- All five numerators have positive sign and one uniform arithmetic ceiling. -/
theorem firstAtomOddTailNumerators_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/30) :
    (0 ≤ firstAtomOddTailNumerator1 u ∧ firstAtomOddTailNumerator1 u ≤ 900000000) ∧
    (0 ≤ firstAtomOddTailNumerator2 u ∧ firstAtomOddTailNumerator2 u ≤ 900000000) ∧
    (0 ≤ firstAtomOddTailNumerator3 u ∧ firstAtomOddTailNumerator3 u ≤ 900000000) ∧
    (0 ≤ firstAtomOddTailNumerator4 u ∧ firstAtomOddTailNumerator4 u ≤ 900000000) ∧
    (0 ≤ firstAtomOddTailNumerator5 u ∧ firstAtomOddTailNumerator5 u ≤ 900000000) := by
  have hn2 : 0 ≤ u^2 := pow_nonneg hu0 2
  have hu2 := pow_le_pow_left₀ hu0 hu1 2
  have hn3 : 0 ≤ u^3 := pow_nonneg hu0 3
  have hu3 := pow_le_pow_left₀ hu0 hu1 3
  have hn4 : 0 ≤ u^4 := pow_nonneg hu0 4
  have hu4 := pow_le_pow_left₀ hu0 hu1 4
  have hn5 : 0 ≤ u^5 := pow_nonneg hu0 5
  have hu5 := pow_le_pow_left₀ hu0 hu1 5
  have hn6 : 0 ≤ u^6 := pow_nonneg hu0 6
  have hu6 := pow_le_pow_left₀ hu0 hu1 6
  norm_num at hu2 hu3 hu4 hu5 hu6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor <;> unfold firstAtomOddTailNumerator1 <;> nlinarith
  · constructor <;> unfold firstAtomOddTailNumerator2 <;> nlinarith
  · constructor <;> unfold firstAtomOddTailNumerator3 <;> nlinarith
  · constructor <;> unfold firstAtomOddTailNumerator4 <;> nlinarith
  · constructor <;> unfold firstAtomOddTailNumerator5 <;> nlinarith

/-- Quantitative entry bounds needed for the complete-source determinant comparison. -/
theorem firstAtomOddTailProfiles_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1/30) :
    |firstAtomOddTailProfile1 u| ≤ 100000000 ∧
    |firstAtomOddTailProfile2 u| ≤ 100000000 ∧
    |firstAtomOddTailProfile3 u| ≤ 100000000 ∧
    |firstAtomOddTailProfile4 u| ≤ 100000000 ∧
    |firstAtomOddTailProfile5 u| ≤ 100000000 ∧
    firstAtomOddTailProfile1 u ≤ 9 ∧ firstAtomOddTailProfile3 u ≤ 9000 := by
  have hD9 := firstAtomOddTailDenominator_lower hu0 hu1
  have hD : 0 < firstAtomOddTailDenominator u := by linarith
  obtain ⟨h1,h2,h3,h4,h5⟩ := firstAtomOddTailNumerators_bounds hu0 hu1
  have hb (N : ℝ) (hN : 0 ≤ N ∧ N ≤ 900000000) :
      |N/firstAtomOddTailDenominator u| ≤ 100000000 := by
    rw [abs_of_nonneg (div_nonneg hN.1 hD.le)]
    apply (div_le_iff₀ hD).mpr
    nlinarith [hN.2]
  refine ⟨hb _ h1, hb _ h2, hb _ h3, hb _ h4, hb _ h5, ?_, ?_⟩
  · unfold firstAtomOddTailProfile1
    apply (div_le_iff₀ hD).mpr
    have h2 := pow_le_pow_left₀ hu0 hu1 2
    norm_num at h2
    unfold firstAtomOddTailNumerator1 firstAtomOddTailDenominator
    nlinarith
  · unfold firstAtomOddTailProfile3
    apply (div_le_iff₀ hD).mpr
    have hn3 : 0 ≤ u^3 := pow_nonneg hu0 3
    have hu2 := pow_le_pow_left₀ hu0 hu1 2
    have hu4 := pow_le_pow_left₀ hu0 hu1 4
    norm_num at hu2 hu4
    unfold firstAtomOddTailNumerator3 firstAtomOddTailDenominator
    nlinarith

end
end HTGeometry
