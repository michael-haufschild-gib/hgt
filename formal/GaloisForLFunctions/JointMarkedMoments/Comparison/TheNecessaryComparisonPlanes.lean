import GaloisForLFunctions.JointMarkedMoments.Comparison.TheComparisonBoundary
import GaloisForLFunctions.JointMarkedMoments.LimitingRange.TheCeilingOfEarlierMomentRanges

/-!
# The necessary comparison planes

The lower bound `B ≥ B∗` of Theorem 7.2 rests on exact linear identities between the direct,
count and numerator planes of the comparison, in the lengths `lx, ly > 0`, `ℓ ≥ 0` with
`M = lx + ly`, `b = ly − lx` and numerator length `h = 1 − lx + ℓ`.

* `directPlane_identity`, `numerator_gap_of_planes`: for every `μ`,
  `h − ly − μh = 11(4 − 3μ)/6 − (22/3 − 25μ/4)L₀ − (2/3 + μ/4)L_K − (3μ/4)(L₀ + G₀)`,
  `G₀ = 2b/3 − M/4`; at `μ = 37/100` and `B ≤ 0.8741` this gives `h − ly − μh ≥ 41671/12000000`.
* `halfEndpoint_identity`, `le_of_halfEndpoint_planes`: the dual identity
  `B − v = u(B − L_K) + v(B − H_{1/2}) + w(h − 2ly) + zb` with positive weights for
  `21/50 < δ < 1/2`, hence `B ≥ 13/(19 − 21δ/2)`, which exceeds `0.89` at `δ∗`.
* `shortNumerator_identity`, `le_of_shortNumerator_planes`: at `δ₀ = 37/100`, `q = 7/18` the
  numerator plane `H_c` gives `B ≥ 72703411/83204812 > B∗`.
* `criticalCount_short_split`, `criticalCount_long_split`: the amplitude model of §7.2 meets both
  critical splits with equality at `r∗`; `balancedModel_identities` does the same for the rational
  model `(r₀, δ₀, R₀) = (24257/33000, 37/100, 4471723/6600000)`.
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Real Set

noncomputable section

/-- The numerator length `h = 1 − (M − b)/2 + ℓ = 1 − lx + ℓ`. -/
def numeratorLength (lx ℓ : ℝ) : ℝ := 1 - lx + ℓ

/-- The direct correction `G₀ = 2b/3 − M/4`. -/
def directCorrection (lx ly : ℝ) : ℝ := 2 * (ly - lx) / 3 - (lx + ly) / 4

/-- The direct-plane identity, valid for every `μ`. -/
theorem directPlane_identity (μ lx ly ℓ : ℝ) :
    numeratorLength lx ℓ - ly - μ * numeratorLength lx ℓ =
      11 * (4 - 3 * μ) / 6 - (22 / 3 - 25 * μ / 4) * directPlane (lx + ly) ℓ -
        (2 / 3 + μ / 4) * countPlane (lx + ly) ℓ -
          3 * μ / 4 * (directPlane (lx + ly) ℓ + directCorrection lx ly) := by
  unfold numeratorLength directPlane countPlane directCorrection; ring

/-- Below `B = 0.8741` the three direct planes force `h − ly − (37/100)h ≥ 41671/12000000`. -/
theorem numerator_gap_of_planes {B lx ly ℓ : ℝ} (hB : B ≤ 8741 / 10000)
    (h0 : directPlane (lx + ly) ℓ ≤ B) (hK : countPlane (lx + ly) ℓ ≤ B)
    (hG : directPlane (lx + ly) ℓ + directCorrection lx ly ≤ B) :
    41671 / 12000000 ≤ numeratorLength lx ℓ - ly - 37 / 100 * numeratorLength lx ℓ := by
  rw [directPlane_identity]
  nlinarith

/-- `M ≤ (12/7)(B − 1/3) < 1` and `h > 0` below `B = 0.8741`. -/
theorem total_length_lt_one {B lx ly ℓ : ℝ} (hB : B ≤ 8741 / 10000) (hly : 0 ≤ ly) (hℓ : 0 ≤ ℓ)
    (hK : countPlane (lx + ly) ℓ ≤ B) :
    lx + ly ≤ 12 / 7 * (B - 1 / 3) ∧ lx + ly < 1 ∧ 0 < numeratorLength lx ℓ := by
  unfold countPlane at hK
  unfold numeratorLength
  refine ⟨by linarith, by linarith, by linarith⟩

/-- The endpoint plane `H_{1/2} = 1 + 5δ/8 − (1/2 + δ/16)M + δb/16 + 5δℓ/8`. -/
def halfEndpointPlane (δ lx ly ℓ : ℝ) : ℝ :=
  1 + 5 * δ / 8 - (1 / 2 + δ / 16) * (lx + ly) + δ * (ly - lx) / 16 + 5 * δ * ℓ / 8

/-- The dual identity of the unmarked endpoint, with `q = 19 − 21δ/2`, `v = 13/q`,
`u = (6 − 21δ/2)/q`, `w = u/3 + 5δv/8`, `z = δv/16 + w/2`. -/
theorem halfEndpoint_identity {δ : ℝ} (hq : 19 - 21 * δ / 2 ≠ 0) (B lx ly ℓ : ℝ) :
    B - 13 / (19 - 21 * δ / 2) =
      (6 - 21 * δ / 2) / (19 - 21 * δ / 2) * (B - countPlane (lx + ly) ℓ) +
        13 / (19 - 21 * δ / 2) * (B - halfEndpointPlane δ lx ly ℓ) +
          ((6 - 21 * δ / 2) / (19 - 21 * δ / 2) / 3 + 5 * δ * (13 / (19 - 21 * δ / 2)) / 8) *
            (numeratorLength lx ℓ - 2 * ly) +
          (δ * (13 / (19 - 21 * δ / 2)) / 16 +
            ((6 - 21 * δ / 2) / (19 - 21 * δ / 2) / 3 +
              5 * δ * (13 / (19 - 21 * δ / 2)) / 8) / 2) * (ly - lx) := by
  unfold countPlane halfEndpointPlane numeratorLength
  generalize hQ : 19 - 21 * δ / 2 = Q at hq
  have hδ : δ = (19 - Q) * 2 / 21 := by rw [← hQ]; ring
  subst hδ
  field_simp
  ring

/-- The unmarked endpoint obstruction: `B ≥ 13/(19 − 21δ/2)` for `21/50 < δ < 1/2`. -/
theorem le_of_halfEndpoint_planes {δ B lx ly ℓ : ℝ} (hδ1 : 21 / 50 < δ) (hδ2 : δ < 1 / 2)
    (hK : countPlane (lx + ly) ℓ ≤ B) (hH : halfEndpointPlane δ lx ly ℓ ≤ B)
    (hD : 2 * ly ≤ numeratorLength lx ℓ) (hb : lx ≤ ly) :
    13 / (19 - 21 * δ / 2) ≤ B := by
  have hq : 0 < 19 - 21 * δ / 2 := by linarith
  have hid := halfEndpoint_identity hq.ne' B lx ly ℓ
  have hu : 0 ≤ (6 - 21 * δ / 2) / (19 - 21 * δ / 2) := div_nonneg (by linarith) hq.le
  have hv : 0 ≤ 13 / (19 - 21 * δ / 2) := div_nonneg (by norm_num) hq.le
  have hw : 0 ≤ (6 - 21 * δ / 2) / (19 - 21 * δ / 2) / 3 + 5 * δ * (13 / (19 - 21 * δ / 2)) / 8 := by
    have : 0 ≤ 5 * δ * (13 / (19 - 21 * δ / 2)) / 8 := by
      have : 0 ≤ δ := by linarith
      positivity
    linarith [div_nonneg hu (by norm_num : (0 : ℝ) ≤ 3)]
  have hz : 0 ≤ δ * (13 / (19 - 21 * δ / 2)) / 16 +
      ((6 - 21 * δ / 2) / (19 - 21 * δ / 2) / 3 + 5 * δ * (13 / (19 - 21 * δ / 2)) / 8) / 2 := by
    have : 0 ≤ δ * (13 / (19 - 21 * δ / 2)) / 16 := by
      have : 0 ≤ δ := by linarith
      positivity
    linarith
  have t1 := mul_nonneg hu (sub_nonneg.2 hK)
  have t2 := mul_nonneg hv (sub_nonneg.2 hH)
  have t3 := mul_nonneg hw (sub_nonneg.2 hD)
  have t4 := mul_nonneg hz (sub_nonneg.2 hb)
  linarith

/-- At `δ∗` the unmarked endpoint obstruction exceeds `0.89`. -/
theorem halfEndpoint_bound_at_comparisonDelta : 89 / 100 < 13 / (19 - 21 * comparisonDelta / 2) := by
  obtain ⟨h1, h2⟩ := comparisonDelta_bounds
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- The shorter-numerator plane `H_c` at `δ₀ = 37/100`, `R₀ = 4471723/6600000`, `c = 1/250`. -/
def shortNumeratorPlane (lx ly ℓ : ℝ) : ℝ :=
  (1 + 37 / 100) / 2 - ly / 2 +
    numeratorLength lx ℓ * ((3 * (4471723 / 6600000) + 1) / 4 - 1 / 6) +
      (37 / 100 - 1) / 2 * ℓ - 37 / 100 * (2 * ly - numeratorLength lx ℓ) / 8 -
        numeratorLength lx ℓ * (37 / 100) * (1 / 250) / 4

/-- The exact coefficient comparison on `0.37 < n < 7/18`, with `D = (7/18)h − (h − ly)`. -/
theorem shortNumerator_identity (B lx ly ℓ : ℝ) :
    B - 72703411 / 83204812 =
      57303411 / 83204812 * (B - directPlane (lx + ly) ℓ) +
        10501401 / 83204812 * (B - countPlane (lx + ly) ℓ) +
          3850000 / 20801203 * (B - shortNumeratorPlane lx ly ℓ) +
            3553203 / 166409624 * (7 / 18 * numeratorLength lx ℓ - (numeratorLength lx ℓ - ly)) := by
  unfold directPlane countPlane shortNumeratorPlane numeratorLength; ring

/-- The planes `L₀, L_K, H_c` and `n ≤ 7/18` force `B ≥ 72703411/83204812`. -/
theorem le_of_shortNumerator_planes {B lx ly ℓ : ℝ} (h0 : directPlane (lx + ly) ℓ ≤ B)
    (hK : countPlane (lx + ly) ℓ ≤ B) (hc : shortNumeratorPlane lx ly ℓ ≤ B)
    (hn : numeratorLength lx ℓ - ly ≤ 7 / 18 * numeratorLength lx ℓ) :
    72703411 / 83204812 ≤ B := by
  have := shortNumerator_identity B lx ly ℓ
  nlinarith

theorem comparisonBoundary_lt_shortNumerator : comparisonBoundary < 72703411 / 83204812 := by
  linarith [comparisonBoundary_bounds.2]

/-- The rational model `(r₀, δ₀, R₀)` meets both critical splits exactly. -/
theorem balancedModel_identities :
    (4471723 / 6600000 : ℝ) + 37 / 100 * (24257 / 33000 + (1 - 24257 / 33000) / 2 + 1 / 250) = 1 ∧
      (4471723 / 6600000 : ℝ) + 37 / 100 * (3 * (24257 / 33000) / 2) =
        (1 + 5 * (3 * (24257 / 33000) / 2)) / 6 ∧
      (24257 / 33000 : ℝ) / 2 < 37 / 100 := by
  norm_num

/-- `r∗` lies in the critical interval where the ceiling is the limiting range. -/
theorem markCeiling_boundaryPoint :
    markCeiling boundaryPoint = (1 - boundaryPoint) / 2 + limitImprovement boundaryPoint := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  exact markCeiling_eq_limit (by linarith) (by linarith)

/-- The short critical split: `R∗ + δ∗r∗ + δ∗Ŝ(r∗) = 1`. -/
theorem criticalCount_short_split :
    criticalCount + comparisonDelta * boundaryPoint +
      comparisonDelta * markCeiling boundaryPoint = 1 := by
  rw [markCeiling_boundaryPoint, ← one_sub_delta_mul_limitTotal]; ring

/-- The long critical split: `R∗ + δ∗(3r∗/2) = (1 + 5(3r∗/2))/6`. -/
theorem criticalCount_long_split :
    criticalCount + comparisonDelta * (3 * boundaryPoint / 2) =
      (1 + 5 * (3 * boundaryPoint / 2)) / 6 := by
  rw [← long_branch_eq_criticalCount]; ring

/-- `c∗ = r∗/2 + G(r∗) < 19/50 < 7/18`. -/
theorem criticalLength_lt : boundaryPoint / 2 + limitImprovement boundaryPoint < 19 / 50 ∧
    (19 / 50 : ℝ) < 7 / 18 := by
  obtain ⟨h1, h2⟩ := boundaryPoint_mem
  refine ⟨?_, by norm_num⟩
  rw [limitImprovement_boundaryPoint]
  have hd : 39 < 2 * (45 * boundaryPoint - 14) := by linarith
  have hn : 24 + 2 * boundaryPoint - 45 * boundaryPoint ^ 2 ≤ 1 / 20 := by nlinarith
  have : (24 + 2 * boundaryPoint - 45 * boundaryPoint ^ 2) / (2 * (45 * boundaryPoint - 14)) ≤
      1 / 780 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  linarith

/-- On numerator lengths `7/18 ≤ n < 1/2` the model amplitude reproduces the fourth-moment value:
`R∗ + δ∗(n + c∗)/4 = (3R∗ + 1 − δ∗(1 − 2n)/2)/4`; at `n = 1/2` it is the unmarked value. -/
theorem criticalCount_numerator_identity (n : ℝ) :
    criticalCount + comparisonDelta * (n + (boundaryPoint / 2 + limitImprovement boundaryPoint)) / 4 =
      (3 * criticalCount + 1 - comparisonDelta * ((1 - 2 * n) / 2)) / 4 ∧
    criticalCount + comparisonDelta * (1 / 2 + (boundaryPoint / 2 + limitImprovement boundaryPoint)) = 1 := by
  have h := criticalCount_eq
  constructor <;> linarith

end

end GaloisForLFunctions.JointMarkedMoments
