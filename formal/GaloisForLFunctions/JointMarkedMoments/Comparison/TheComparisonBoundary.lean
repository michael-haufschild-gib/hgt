import GaloisForLFunctions.JointMarkedMoments.LimitingRange.TheLimitingImprovement
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Order.IntermediateValue

/-!
# The comparison boundary `B∗`

The optimizing point `r∗` of the limiting comparison is a root in
`(0.7523220538, 0.7523220539)` of
`(19(3r − 2)(9r + 2)/(3(45r − 14)))⁵ = 7r⁴(r − 2/3)` (eq. (33)), equivalently of the degree-nine
polynomial `19⁵(3r − 2)⁴(9r + 2)⁵ − 567 r⁴(45r − 14)⁵` obtained by removing the factor `3r − 2`.

* `limitCore_boundaryPoint`: at `r∗` the fifth-root core is rational in `r∗`,
  `H(r∗) = 19(3r∗ − 2)(9r∗ + 2)/(3(45r∗ − 14))`, hence
  `G(r∗) = (24 + 2r∗ − 45r∗²)/(2(45r∗ − 14))`.
* `tangentSlope_eq`, `tangentIntercept_eq`: the line `g₀ − g₁r` of (36),
  `g₀ = (17 − 18r∗)/(3(45r∗ − 14))`, `g₁ = (135r∗² − 42r∗ − 38)/(6r∗(45r∗ − 14))`, is the tangent
  to `G` at `r∗`.
* `relativeBoundary_eq`: `B_rel = (14 + 25δ∗)/(18 + 24δ∗) = B∗ = (99r∗ − 14)/(12(9r∗ − 1))`,
  `δ∗ = (45r∗ − 14)/(6 + 54r∗)`.
* `one_sub_delta_mul_limitTotal`: `1 − δ∗F_G(r∗) = 1/6 + (5/6 − δ∗)(3r∗/2) = (10 + 3δ∗)/18 = R∗`.
* `lowerBoundPlane_identity`, `le_relativeBoundary_of_planes` (Proposition 6.5): the planes
  `L₀ = 5/6 + M/12 − ℓ/6`, `L_K = 1/3 + 7M/12 + ℓ/3` and
  `H = 1 + 3δ/4 − (1/2 + δ/4)M + 3δℓ/4` have a positive convex combination equal to
  `(14 + 25δ)/(18 + 24δ)`.
* `comparisonBoundary_bounds` and the comparisons `B∗ < B₁₃₇ < B₂ < (1 + κ₁)/2 < 20999/24000`.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Real Set

noncomputable section

/-- The degree-nine polynomial whose root in `(0.7523220538, 0.7523220539)` is `r∗`. -/
def boundaryPolynomial (r : ℝ) : ℝ :=
  19 ^ 5 * (3 * r - 2) ^ 4 * (9 * r + 2) ^ 5 - 567 * r ^ 4 * (45 * r - 14) ^ 5

theorem exists_boundaryPolynomial_root :
    ∃ r ∈ Ioo (7523220538 / 10000000000 : ℝ) (7523220539 / 10000000000),
      boundaryPolynomial r = 0 := by
  have hc : ContinuousOn boundaryPolynomial
      (Icc (7523220538 / 10000000000 : ℝ) (7523220539 / 10000000000)) := by
    unfold boundaryPolynomial; fun_prop
  have h := intermediate_value_Ioo (by norm_num) hc
  have hmem : (0 : ℝ) ∈ Ioo (boundaryPolynomial (7523220538 / 10000000000))
      (boundaryPolynomial (7523220539 / 10000000000)) := by
    unfold boundaryPolynomial; constructor <;> norm_num
  obtain ⟨r, hr, hr0⟩ := h hmem
  exact ⟨r, hr, hr0⟩

/-- The optimizing point `r∗`. -/
def boundaryPoint : ℝ := Classical.choose exists_boundaryPolynomial_root

theorem boundaryPoint_mem :
    boundaryPoint ∈ Ioo (7523220538 / 10000000000 : ℝ) (7523220539 / 10000000000) :=
  (Classical.choose_spec exists_boundaryPolynomial_root).1

theorem boundaryPolynomial_boundaryPoint : boundaryPolynomial boundaryPoint = 0 :=
  (Classical.choose_spec exists_boundaryPolynomial_root).2

/-- The rational expression `19(3r − 2)(9r + 2)/(3(45r − 14))` inside the fifth power of (33). -/
def boundaryCore (r : ℝ) : ℝ := 19 * (3 * r - 2) * (9 * r + 2) / (3 * (45 * r - 14))

/-- Equation (33) at `r∗`. -/
theorem boundaryCore_pow_five :
    boundaryCore boundaryPoint ^ 5 = 7 * boundaryPoint ^ 4 * (boundaryPoint - 2 / 3) := by
  have h := boundaryPolynomial_boundaryPoint
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  unfold boundaryPolynomial at h
  unfold boundaryCore
  generalize boundaryPoint = r at h h1 h2 ⊢
  have hd : 45 * r - 14 ≠ 0 := by linarith
  rw [div_pow, div_eq_iff (by positivity)]
  linear_combination (3 * r - 2) * h

/-- `H(r∗) = 19(3r∗ − 2)(9r∗ + 2)/(3(45r∗ − 14))`. -/
theorem limitCore_boundaryPoint : limitCore boundaryPoint = boundaryCore boundaryPoint := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  have hpos : 0 ≤ boundaryCore boundaryPoint := by
    unfold boundaryCore
    apply div_nonneg
    · apply mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by linarith)
    · linarith
  unfold limitCore
  rw [← boundaryCore_pow_five, show (1 / 5 : ℝ) = ((5 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast hpos (by norm_num)

/-- `G(r∗) = (24 + 2r∗ − 45r∗²)/(2(45r∗ − 14))`. -/
theorem limitImprovement_boundaryPoint :
    limitImprovement boundaryPoint =
      (24 + 2 * boundaryPoint - 45 * boundaryPoint ^ 2) / (2 * (45 * boundaryPoint - 14)) := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  unfold limitImprovement
  rw [limitCore_boundaryPoint]
  unfold boundaryCore
  generalize boundaryPoint = r at h1 h2 ⊢
  generalize hd : 45 * r - 14 = d
  have hd0 : d ≠ 0 := by rw [← hd]; linarith
  field_simp
  rw [← hd]
  ring

/-- The parameter `δ∗ = (45r∗ − 14)/(6 + 54r∗)`. -/
def comparisonDelta : ℝ := (45 * boundaryPoint - 14) / (6 + 54 * boundaryPoint)

/-- The comparison infimum `B∗ = (99r∗ − 14)/(12(9r∗ − 1))`. -/
def comparisonBoundary : ℝ := (99 * boundaryPoint - 14) / (12 * (9 * boundaryPoint - 1))

/-- `B_rel = (14 + 25δ∗)/(18 + 24δ∗)`. -/
def relativeBoundary : ℝ := (14 + 25 * comparisonDelta) / (18 + 24 * comparisonDelta)

/-- The count `R∗ = (10 + 3δ∗)/18` at the critical splits. -/
def criticalCount : ℝ := (10 + 3 * comparisonDelta) / 18

theorem relativeBoundary_eq : relativeBoundary = comparisonBoundary := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  unfold relativeBoundary comparisonBoundary comparisonDelta
  generalize boundaryPoint = r at h1 h2 ⊢
  generalize ha : 6 + 54 * r = a
  generalize hb : 9 * r - 1 = b
  have ha0 : a ≠ 0 := by rw [← ha]; linarith
  have hb0 : b ≠ 0 := by rw [← hb]; linarith
  have hc : 18 + 24 * ((45 * r - 14) / a) = 228 * b / a := by
    rw [← ha, ← hb]; field_simp; ring
  rw [hc]
  field_simp
  ring

theorem comparisonDelta_bounds : (27 / 64 : ℝ) < comparisonDelta ∧ comparisonDelta < 57 / 128 := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  unfold comparisonDelta
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- `B∗ ∈ (0.8733458561, 0.8733458562)`. -/
theorem comparisonBoundary_bounds :
    (8733458561 / 10000000000 : ℝ) < comparisonBoundary ∧
      comparisonBoundary < 8733458562 / 10000000000 := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  unfold comparisonBoundary
  constructor
  · rw [lt_div_iff₀ (by linarith)]; linarith
  · rw [div_lt_iff₀ (by linarith)]; linarith

/-- `1 − δ∗F_G(r∗) = R∗`. -/
theorem one_sub_delta_mul_limitTotal :
    1 - comparisonDelta * ((1 + boundaryPoint) / 2 + limitImprovement boundaryPoint) =
      criticalCount := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  rw [limitImprovement_boundaryPoint]
  unfold criticalCount comparisonDelta
  generalize boundaryPoint = r at h1 h2 ⊢
  generalize ha : 6 + 54 * r = a
  generalize hd : 45 * r - 14 = d
  have ha0 : a ≠ 0 := by rw [← ha]; linarith
  have hd0 : d ≠ 0 := by rw [← hd]; linarith
  field_simp
  (try rw [← ha]); (try rw [← hd])
  ring

/-- The long inverse branch at `t∗ = 3r∗/2` meets the same count: `1/6 + (5/6 − δ∗)t∗ = R∗`. -/
theorem long_branch_eq_criticalCount :
    1 / 6 + (5 / 6 - comparisonDelta) * (3 * boundaryPoint / 2) = criticalCount := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  unfold criticalCount comparisonDelta
  generalize boundaryPoint = r at h1 h2 ⊢
  generalize ha : 6 + 54 * r = a
  have ha0 : a ≠ 0 := by rw [← ha]; linarith
  field_simp
  (try rw [← ha])
  ring

/-- At `R∗` the endpoint comparison loses its dependence on `h`: `5/12 + δ∗/8 − 3R∗/4 = 0`. -/
theorem endpoint_amplitude_balance : 5 / 12 + comparisonDelta / 8 - 3 * criticalCount / 4 = 0 := by
  unfold criticalCount; ring

/-- `R∗ = 1 − δ∗(1/2 + c∗)` with `c∗ = r∗/2 + G(r∗)`. -/
theorem criticalCount_eq :
    criticalCount = 1 - comparisonDelta * (1 / 2 + (boundaryPoint / 2 +
      limitImprovement boundaryPoint)) := by
  rw [← one_sub_delta_mul_limitTotal]; ring

/-- The slope `g₁ = (135r∗² − 42r∗ − 38)/(6r∗(45r∗ − 14))` of the tangent (36). -/
def tangentSlope : ℝ :=
  (135 * boundaryPoint ^ 2 - 42 * boundaryPoint - 38) / (6 * boundaryPoint * (45 * boundaryPoint - 14))

/-- The intercept `g₀ = (17 − 18r∗)/(3(45r∗ − 14))` of the tangent (36). -/
def tangentIntercept : ℝ := (17 - 18 * boundaryPoint) / (3 * (45 * boundaryPoint - 14))

/-- `g₁ = −G′(r∗)`. -/
theorem tangentSlope_eq : tangentSlope = -limitSlope boundaryPoint := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  rw [limitSlope_eq_recursionSlope (by linarith), limitImprovement_boundaryPoint]
  unfold tangentSlope recursionSlope
  generalize boundaryPoint = r at h1 h2 ⊢
  have hr : r ≠ 0 := by linarith
  generalize hd : 45 * r - 14 = d
  generalize hU : 45 * r - 30 = U
  have hd0 : d ≠ 0 := by rw [← hd]; linarith
  have hU0 : U ≠ 0 := by rw [← hU]; linarith
  field_simp
  rw [← hd, ← hU]
  ring

/-- `g₀ = G(r∗) + g₁ r∗`: the line `g₀ − g₁r` touches `G` at `r∗`. -/
theorem tangentIntercept_eq :
    tangentIntercept = limitImprovement boundaryPoint + tangentSlope * boundaryPoint := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  rw [limitImprovement_boundaryPoint]
  unfold tangentIntercept tangentSlope
  generalize boundaryPoint = r at h1 h2 ⊢
  have hr : r ≠ 0 := by linarith
  generalize hd : 45 * r - 14 = d
  have hd0 : d ≠ 0 := by rw [← hd]; linarith
  field_simp
  (try rw [← hd])
  ring

/-- The tangent at `r∗` is a global minorant of `G` on `[2/3, ∞)`. -/
theorem tangent_le_limitImprovement {r : ℝ} (hr : 2 / 3 ≤ r) :
    tangentIntercept - tangentSlope * r ≤ limitImprovement r := by
  obtain ⟨h1, _⟩ := boundaryPoint_mem
  have h := limitImprovement_tangent_le (R := boundaryPoint) (by linarith) hr
  rw [tangentIntercept_eq, tangentSlope_eq]
  linarith

/-- The planes of Proposition 6.5. -/
def directPlane (M ℓ : ℝ) : ℝ := 5 / 6 + M / 12 - ℓ / 6

/-- The plane `L_K = 1/3 + 7M/12 + ℓ/3`. -/
def countPlane (M ℓ : ℝ) : ℝ := 1 / 3 + 7 * M / 12 + ℓ / 3

/-- The numerator plane `1 + 3δ/4 − (1/2 + δ/4)M + 3δℓ/4`. -/
def numeratorPlane (δ M ℓ : ℝ) : ℝ := 1 + 3 * δ / 4 - (1 / 2 + δ / 4) * M + 3 * δ * ℓ / 4

/-- Proposition 6.5: `uL₀ + vL_K + wH = (14 + 25δ)/(18 + 24δ)` with
`u = (25δ + 8)/(6(4δ + 3))`, `v = (4 − δ)/(6(4δ + 3))`, `w = 1/(4δ + 3)`, `u + v + w = 1`. -/
theorem lowerBoundPlane_identity {δ : ℝ} (hδ : 4 * δ + 3 ≠ 0) (M ℓ : ℝ) :
    (25 * δ + 8) / (6 * (4 * δ + 3)) + (4 - δ) / (6 * (4 * δ + 3)) + 1 / (4 * δ + 3) = 1 ∧
      (25 * δ + 8) / (6 * (4 * δ + 3)) * directPlane M ℓ +
        (4 - δ) / (6 * (4 * δ + 3)) * countPlane M ℓ +
          1 / (4 * δ + 3) * numeratorPlane δ M ℓ = (14 + 25 * δ) / (18 + 24 * δ) := by
  have h2 : 18 + 24 * δ ≠ 0 := by intro h; apply hδ; linarith
  unfold directPlane countPlane numeratorPlane
  generalize he : 4 * δ + 3 = e at hδ
  have hδe : δ = (e - 3) / 4 := by rw [← he]; ring
  subst hδe
  constructor
  · field_simp; ring
  · have h3 : 18 + 24 * ((e - 3) / 4) = 6 * e := by ring
    rw [h3]
    field_simp
    ring

/-- Proposition 6.5: a comparison requiring `B ≥ L₀, L_K, H` at `δ = δ∗` forces
`B ≥ B_rel = B∗`. -/
theorem le_relativeBoundary_of_planes {B M ℓ : ℝ} (h0 : directPlane M ℓ ≤ B)
    (hK : countPlane M ℓ ≤ B) (hH : numeratorPlane comparisonDelta M ℓ ≤ B) :
    comparisonBoundary ≤ B := by
  obtain ⟨hd1, hd2⟩ := comparisonDelta_bounds
  have he : 4 * comparisonDelta + 3 ≠ 0 := by linarith
  obtain ⟨hsum, hid⟩ := lowerBoundPlane_identity he M ℓ
  have hu : 0 ≤ (25 * comparisonDelta + 8) / (6 * (4 * comparisonDelta + 3)) :=
    div_nonneg (by linarith) (by linarith)
  have hv : 0 ≤ (4 - comparisonDelta) / (6 * (4 * comparisonDelta + 3)) :=
    div_nonneg (by linarith) (by linarith)
  have hw : 0 ≤ 1 / (4 * comparisonDelta + 3) := div_nonneg (by norm_num) (by linarith)
  have hB := congrArg (· * B) hsum
  simp only [one_mul] at hB
  rw [← relativeBoundary_eq]
  unfold relativeBoundary
  rw [← hid]
  nlinarith [mul_le_mul_of_nonneg_left h0 hu, mul_le_mul_of_nonneg_left hK hv,
    mul_le_mul_of_nonneg_left hH hw]

/-- On the edge `M = 1 − ℓ` the direct planes agree: `L₀ = L_K = 11/12 − ℓ/4`. -/
theorem directPlane_eq_countPlane (ℓ : ℝ) :
    directPlane (1 - ℓ) ℓ = 11 / 12 - ℓ / 4 ∧ countPlane (1 - ℓ) ℓ = 11 / 12 - ℓ / 4 := by
  unfold directPlane countPlane; constructor <;> ring

/-- `B₁₃₇ = 2183367/2500000`, the earlier marked-induction value. -/
def markedInductionBoundary : ℝ := 2183367 / 2500000

/-- `B₂ = (777 − √1081)/852`, the earlier selected-moment value. -/
def selectedMomentBoundary : ℝ := (777 - √1081) / 852

theorem comparisonBoundary_lt_markedInductionBoundary :
    comparisonBoundary < markedInductionBoundary := by
  unfold markedInductionBoundary; linarith [comparisonBoundary_bounds.2]

theorem markedInductionBoundary_lt_selectedMomentBoundary :
    markedInductionBoundary < selectedMomentBoundary := by
  have h : √1081 < 328786 / 10000 := (Real.sqrt_lt' (by norm_num)).2 (by norm_num)
  unfold markedInductionBoundary selectedMomentBoundary
  linarith

theorem selectedMomentBoundary_lt :
    selectedMomentBoundary < (1 + 374887 / 500000) / 2 := by
  have h : (328785 / 10000 : ℝ) < √1081 := (Real.lt_sqrt (by norm_num)).2 (by norm_num)
  unfold selectedMomentBoundary
  linarith

/-- `B∗` lies strictly below the corpus half-plane `20999/24000` and above `51/100`. -/
theorem comparisonBoundary_lt_sub_seven_eighths :
    51 / 100 < comparisonBoundary ∧ comparisonBoundary < 20999 / 24000 := by
  obtain ⟨h1, h2⟩ := comparisonBoundary_bounds
  constructor <;> linarith

end

end GaloisForLFunctions.JointMarkedMoments
