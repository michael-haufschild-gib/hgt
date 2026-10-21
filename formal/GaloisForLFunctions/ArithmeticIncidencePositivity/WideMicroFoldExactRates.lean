import GaloisForLFunctions.ArithmeticIncidencePositivity.SharpMicroFoldHarnack
import GaloisForLFunctions.RHTower.ArchimedeanAnomalyConstantLaws

/-!
# The micro-fold on a wide strip, with a band of pairs removed

The sharp micro-fold (`SharpMicroFoldHarnack`) bounds every pair kernel of the strip
`S = [L − r, r]` below by `k₀(t) = ω(t) − ω(2p)`, `p = L − r`, which is nonnegative only for
distances `t ≤ 2p`; it therefore needs the half-width `η = r − L/2` to stay below `p`. Here each
group of two pairs is read at its exact smaller kernel. In folded coordinates `u = |x − L/2|`,
`v = |y − L/2|` the group at distance `|u − v|` has rate `ω(|u − v|) − ω(L − u − v)`
(`wideSameRate`) and the group at distance `u + v` has rate `ω(u + v) − ω(L − |u − v|)`
(`wideCrossRate`). Both are nonnegative on every strip with `p > 0`, and their difference is
nonnegative because `ω = Σ_k e^{−(2k+½)t}` is completely monotone (`archLevyDensity_sub_shift_le`):
the drop of `ω` over an interval decreases when the interval moves away from `0`.
`wideQuadruple_ge` is the quadruple inequality with these rates, valid for strips of any width.

A band of pairs can be withheld from the fold (`wideBandQuadruple_ge`): the pairs with both points
in `[c, r]`, `c > L/2`, carry the kernel `withheldKernel c = 0`, and the folded weight vanishes on the
corresponding band `u, v ≥ c − L/2`. Every quadruple meets the band in at most one pair, its upper
same-distance pair, so off the band nothing changes. The withheld pairs are those of a second,
nested strip, which pay a second prime atom.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ### Complete monotonicity -/

/-- **The drop of `ω` decreases away from the origin.** For `0 < a ≤ c` and `Δ ≥ 0`:
`ω(c) − ω(c + Δ) ≤ ω(a) − ω(a + Δ)`, term by term in `ω(t) = Σ_k e^{−(2k+½)t}`. -/
theorem archLevyDensity_sub_shift_le {a c Δ : ℝ} (ha : 0 < a) (hac : a ≤ c) (hΔ : 0 ≤ Δ) :
    archLevyDensity c - archLevyDensity (c + Δ) ≤ archLevyDensity a - archLevyDensity (a + Δ) := by
  have h1 := RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity (show 0 < c by linarith)
  have h2 := RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity (show 0 < c + Δ by linarith)
  have h3 := RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity ha
  have h4 := RHTower.ArchimedeanAnomaly.hasSum_archLevyDensity (show 0 < a + Δ by linarith)
  refine hasSum_le (fun k => ?_) (h1.sub h2) (h3.sub h4)
  have hl : 0 < 2 * (k : ℝ) + 1 / 2 := by positivity
  have e1 : Real.exp (-(2 * (k : ℝ) + 1 / 2) * (c + Δ)) =
      Real.exp (-(2 * (k : ℝ) + 1 / 2) * c) * Real.exp (-(2 * (k : ℝ) + 1 / 2) * Δ) := by
    rw [← Real.exp_add]; ring_nf
  have e2 : Real.exp (-(2 * (k : ℝ) + 1 / 2) * (a + Δ)) =
      Real.exp (-(2 * (k : ℝ) + 1 / 2) * a) * Real.exp (-(2 * (k : ℝ) + 1 / 2) * Δ) := by
    rw [← Real.exp_add]; ring_nf
  have hca : Real.exp (-(2 * (k : ℝ) + 1 / 2) * c) ≤ Real.exp (-(2 * (k : ℝ) + 1 / 2) * a) :=
    Real.exp_le_exp.mpr (by nlinarith)
  have hd : Real.exp (-(2 * (k : ℝ) + 1 / 2) * Δ) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  show Real.exp (-(2 * (k : ℝ) + 1 / 2) * c) - Real.exp (-(2 * (k : ℝ) + 1 / 2) * (c + Δ)) ≤
    Real.exp (-(2 * (k : ℝ) + 1 / 2) * a) - Real.exp (-(2 * (k : ℝ) + 1 / 2) * (a + Δ))
  rw [e1, e2]
  nlinarith [Real.exp_pos (-(2 * (k : ℝ) + 1 / 2) * c), Real.exp_pos (-(2 * (k : ℝ) + 1 / 2) * Δ)]

/-! ### The exact rates of the fold -/

/-- The rate of the pair group at folded distance `|u − v|`: its smaller kernel
`ω(|u − v|) − ω(L − u − v)`. -/
def wideSameRate (L u v : ℝ) : ℝ := archLevyDensity |u - v| - archLevyDensity (L - (u + v))

/-- The rate of the pair group at folded distance `u + v`: its smaller kernel
`ω(u + v) − ω(L − |u − v|)`. -/
def wideCrossRate (L u v : ℝ) : ℝ := archLevyDensity (u + v) - archLevyDensity (L - |u - v|)

/-- The ground-state weight of the wide fold in the gauge `β + t`:
`W(u, v) = 2 (R₋ − R₊)(1 − (β + v)/(β + u)) + 4 R₊`. -/
def wideFoldWeight (L β u v : ℝ) : ℝ :=
  2 * ((wideSameRate L u v - wideCrossRate L u v) * (1 - (β + v) / (β + u))) +
    4 * wideCrossRate L u v

theorem wideSameRate_comm (L u v : ℝ) : wideSameRate L v u = wideSameRate L u v := by
  unfold wideSameRate; rw [abs_sub_comm, add_comm]

theorem wideCrossRate_comm (L u v : ℝ) : wideCrossRate L v u = wideCrossRate L u v := by
  unfold wideCrossRate; rw [abs_sub_comm, add_comm]

/-- **The fold surplus is nonnegative**: `ω(|u − v|) − ω(u + v) ≥ ω(L − u − v) − ω(L − |u − v|)`
whenever `u + v + |u − v| ≤ L`. -/
theorem wideSameRate_sub_crossRate_nonneg {L u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u ≠ v)
    (hL : u + v + |u - v| ≤ L) : 0 ≤ wideSameRate L u v - wideCrossRate L u v := by
  have hd : 0 < |u - v| := abs_pos.mpr (sub_ne_zero.mpr huv)
  have hle : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith, by linarith⟩
  have h := archLevyDensity_sub_shift_le hd (show |u - v| ≤ L - (u + v) by linarith)
    (show 0 ≤ u + v - |u - v| by linarith)
  rw [show L - (u + v) + (u + v - |u - v|) = L - |u - v| by ring,
    show |u - v| + (u + v - |u - v|) = u + v by ring] at h
  unfold wideSameRate wideCrossRate
  linarith

/-- **The folded pair in the gauge `β + t`, with the exact rates.** -/
theorem wideFold_folded {L β u v a b : ℝ} (hβ : 0 < β) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hL : u + v + |u - v| ≤ L) (hdeg : u = v → a = b) :
    a ^ 2 * wideFoldWeight L β u v + b ^ 2 * wideFoldWeight L β v u ≤
      2 * wideSameRate L u v * (a - b) ^ 2 + 2 * wideCrossRate L u v * (a + b) ^ 2 := by
  have hβu : 0 < β + u := by positivity
  have hβv : 0 < β + v := by positivity
  have hq : 0 < (β + v) / (β + u) := div_pos hβv hβu
  have hqinv : (β + u) / (β + v) = 1 / ((β + v) / (β + u)) := by field_simp
  unfold wideFoldWeight
  rw [wideSameRate_comm L u v, wideCrossRate_comm L u v, hqinv]
  refine sharpFold_core (m₁ := wideSameRate L u v) (m₂ := wideCrossRate L u v) hq rfl ?_
  by_cases huv : u = v
  · exact Or.inr ⟨hdeg huv, by rw [huv, div_self hβv.ne']⟩
  · exact Or.inl (wideSameRate_sub_crossRate_nonneg hu hv huv hL)

/-- A surplus pair dominates the rate `ω(|x − y|) − ω(L − |x + y − L|)`: `x + y ≥ L − |x + y − L| > 0`. -/
theorem wideRate_mul_le {L x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxyL : |x + y - L| < L)
    (F : ℝ → ℝ) :
    (archLevyDensity |x - y| - archLevyDensity (L - |x + y - L|)) * (F x - F y) ^ 2 ≤
      surplusKernel x y * (F x - F y) ^ 2 := by
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  unfold surplusKernel
  have h1 : L - |x + y - L| ≤ x + y := by linarith [neg_abs_le (x + y - L)]
  have hpos : 0 < L - |x + y - L| := by linarith
  have := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr hpos)
    (mem_Ioi.mpr (by linarith : (0 : ℝ) < x + y)) h1
  linarith

/-- **The wide quadruple inequality.** For `x, y` in the strip `[p, r]`, `p + r = L`, `p > 0`, of any
width, the four surplus terms of `x, L − x, y, L − y` dominate
`α(x)² W(u, v) + α(y)² W(v, u)` with the exact rates. -/
theorem wideQuadruple_ge {p r L β x y : ℝ} (hp : 0 < p) (hL : p + r = L) (hβ : 0 < β)
    (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) (F : ℝ → ℝ) :
    reflectedOddPart F L x ^ 2 * wideFoldWeight L β |x - L / 2| |y - L / 2| +
        reflectedOddPart F L y ^ 2 * wideFoldWeight L β |y - L / 2| |x - L / 2| ≤
      surplusKernel x y * (F x - F y) ^ 2 +
        surplusKernel (L - x) (L - y) * (F (L - x) - F (L - y)) ^ 2 +
        surplusKernel x (L - y) * (F x - F (L - y)) ^ 2 +
        surplusKernel (L - x) y * (F (L - x) - F y) ^ 2 := by
  have hxL : L - x ∈ Icc p r := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hyL : L - y ∈ Icc p r := ⟨by linarith [hy.2], by linarith [hy.1]⟩
  set U := x - L / 2 with hU
  set V := y - L / 2 with hV
  have hU1 : -((r - p) / 2) ≤ U := by rw [hU]; linarith [hx.1]
  have hU2 : U ≤ (r - p) / 2 := by rw [hU]; linarith [hx.2]
  have hV1 : -((r - p) / 2) ≤ V := by rw [hV]; linarith [hy.1]
  have hV2 : V ≤ (r - p) / 2 := by rw [hV]; linarith [hy.2]
  -- the two folded distances fit: `|U − V| + |U + V| = 2 max(|U|, |V|) < L`
  have hsum : |U - V| + |U + V| < L := by
    rcases le_total 0 (U - V) with h1 | h1 <;> rcases le_total 0 (U + V) with h2 | h2
    · rw [abs_of_nonneg h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonneg h1, abs_of_nonpos h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonneg h2]; linarith
    · rw [abs_of_nonpos h1, abs_of_nonpos h2]; linarith
  have hUV : |U - V| ≥ 0 := abs_nonneg _
  have hUV' : |U + V| ≥ 0 := abs_nonneg _
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hxL0 : 0 < L - x := by linarith [hxL.1]
  have hyL0 : 0 < L - y := by linarith [hyL.1]
  -- the four pairs at their group rates
  have k1 := wideRate_mul_le hx0 hy0 (by rw [show x + y - L = U + V by rw [hU, hV]; ring]; linarith) F
  have k2 := wideRate_mul_le hxL0 hyL0
    (by rw [show L - x + (L - y) - L = -(U + V) by rw [hU, hV]; ring, abs_neg]; linarith) F
  have k3 := wideRate_mul_le hx0 hyL0
    (by rw [show x + (L - y) - L = U - V by rw [hU, hV]; ring]; linarith) F
  have k4 := wideRate_mul_le hxL0 hy0
    (by rw [show L - x + y - L = -(U - V) by rw [hU, hV]; ring, abs_neg]; linarith) F
  rw [show x - y = U - V by rw [hU, hV]; ring, show x + y - L = U + V by rw [hU, hV]; ring] at k1
  rw [show L - x - (L - y) = -(U - V) by rw [hU, hV]; ring, abs_neg,
    show L - x + (L - y) - L = -(U + V) by rw [hU, hV]; ring, abs_neg] at k2
  rw [show x - (L - y) = U + V by rw [hU, hV]; ring,
    show x + (L - y) - L = U - V by rw [hU, hV]; ring] at k3
  rw [show L - x - y = -(U + V) by rw [hU, hV]; ring, abs_neg,
    show L - x + y - L = -(U - V) by rw [hU, hV]; ring, abs_neg] at k4
  -- the same-distance group and the crossing group
  have g12 := sharpFold_group k1 k2 (by
    by_cases hxy : U = V
    · right
      have : x = y := by linarith
      rw [this]; exact ⟨rfl, rfl⟩
    · left
      have hd : 0 < |U - V| := abs_pos.mpr (sub_ne_zero.mpr hxy)
      have := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr hd)
        (mem_Ioi.mpr (by linarith : (0 : ℝ) < L - |U + V|)) (by linarith)
      linarith)
  have g34 := sharpFold_group k3 k4 (by
    by_cases hxy : U + V = 0
    · right
      have : y = L - x := by linarith
      rw [this, sub_sub_cancel]; exact ⟨rfl, rfl⟩
    · left
      have hd : 0 < |U + V| := abs_pos.mpr hxy
      have := strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr hd)
        (mem_Ioi.mpr (by linarith : (0 : ℝ) < L - |U - V|)) (by linarith)
      linarith)
  unfold reflectedOddPart
  set a := (F x - F (L - x)) / 2 with ha
  set b := (F y - F (L - y)) / 2 with hb
  have g34' : 2 * (archLevyDensity |U + V| - archLevyDensity (L - |U - V|)) * (a + b) ^ 2 ≤
      surplusKernel x (L - y) * (F x - F (L - y)) ^ 2 +
        surplusKernel (L - x) y * (F (L - x) - F y) ^ 2 := by
    have e : a - (F (L - y) - F y) / 2 = a + b := by rw [hb]; ring
    rw [e] at g34; exact g34
  rcases le_total 0 U with hU0 | hU0 <;> rcases le_total 0 V with hV0 | hV0
  · -- both on the right
    have hf := wideFold_folded (L := L) (a := a) (b := b) hβ (abs_nonneg U) (abs_nonneg V)
      (by rw [abs_of_nonneg hU0, abs_of_nonneg hV0]
          rw [abs_of_nonneg (by linarith : 0 ≤ U + V)] at hsum; linarith)
      (fun h => by
        rw [abs_of_nonneg hU0, abs_of_nonneg hV0] at h
        have : x = y := by linarith
        rw [ha, hb, this])
    have e1 : wideSameRate L |U| |V| = archLevyDensity |U - V| - archLevyDensity (L - |U + V|) := by
      unfold wideSameRate
      rw [abs_of_nonneg hU0, abs_of_nonneg hV0, abs_of_nonneg (by linarith : 0 ≤ U + V)]
    have e2 : wideCrossRate L |U| |V| = archLevyDensity |U + V| - archLevyDensity (L - |U - V|) := by
      unfold wideCrossRate
      rw [abs_of_nonneg hU0, abs_of_nonneg hV0, abs_of_nonneg (by linarith : 0 ≤ U + V)]
    rw [e1, e2] at hf
    linarith only [hf, g12, g34']
  · -- `x` right, `y` left: the two groups exchange their distances
    have hf := wideFold_folded (L := L) (a := a) (b := -b) hβ (abs_nonneg U) (abs_nonneg V)
      (by rw [abs_of_nonneg hU0, abs_of_nonpos hV0]
          rw [abs_of_nonneg (by linarith : 0 ≤ U - V)] at hsum
          rcases le_total 0 (U + V) with h | h
          · rw [abs_of_nonneg h] at hsum
            rw [abs_of_nonneg (by linarith : 0 ≤ U - -V)]; linarith
          · rw [abs_of_nonpos h] at hsum
            rw [abs_of_nonpos (by linarith : U - -V ≤ 0)]; linarith)
      (fun h => by
        rw [abs_of_nonneg hU0, abs_of_nonpos hV0] at h
        have : y = L - x := by linarith
        rw [ha, hb, this, sub_sub_cancel]; ring)
    have e1 : wideSameRate L |U| |V| = archLevyDensity |U + V| - archLevyDensity (L - |U - V|) := by
      unfold wideSameRate
      rw [abs_of_nonneg hU0, abs_of_nonpos hV0, abs_of_nonneg (by linarith : 0 ≤ U - V),
        show U - -V = U + V by ring, show U + -V = U - V by ring]
    have e2 : wideCrossRate L |U| |V| = archLevyDensity |U - V| - archLevyDensity (L - |U + V|) := by
      unfold wideCrossRate
      rw [abs_of_nonneg hU0, abs_of_nonpos hV0, abs_of_nonneg (by linarith : 0 ≤ U - V),
        show U - -V = U + V by ring, show U + -V = U - V by ring]
    rw [e1, e2, neg_sq, sub_neg_eq_add, ← sub_eq_add_neg] at hf
    linarith only [hf, g12, g34']
  · -- `x` left, `y` right
    have hf := wideFold_folded (L := L) (a := a) (b := -b) hβ (abs_nonneg U) (abs_nonneg V)
      (by rw [abs_of_nonpos hU0, abs_of_nonneg hV0]
          rw [abs_of_nonpos (by linarith : U - V ≤ 0)] at hsum
          rcases le_total 0 (U + V) with h | h
          · rw [abs_of_nonneg h] at hsum
            rw [abs_of_nonpos (by linarith : -U - V ≤ 0)]; linarith
          · rw [abs_of_nonpos h] at hsum
            rw [abs_of_nonneg (by linarith : 0 ≤ -U - V)]; linarith)
      (fun h => by
        rw [abs_of_nonpos hU0, abs_of_nonneg hV0] at h
        have : y = L - x := by linarith
        rw [ha, hb, this, sub_sub_cancel]; ring)
    have e1 : wideSameRate L |U| |V| = archLevyDensity |U + V| - archLevyDensity (L - |U - V|) := by
      unfold wideSameRate
      rw [abs_of_nonpos hU0, abs_of_nonneg hV0, abs_of_nonpos (by linarith : U - V ≤ 0),
        show -U - V = -(U + V) by ring, abs_neg, show -U + V = -(U - V) by ring]
    have e2 : wideCrossRate L |U| |V| = archLevyDensity |U - V| - archLevyDensity (L - |U + V|) := by
      unfold wideCrossRate
      rw [abs_of_nonpos hU0, abs_of_nonneg hV0, abs_of_nonpos (by linarith : U - V ≤ 0),
        show -U - V = -(U + V) by ring, abs_neg, show -U + V = -(U - V) by ring]
    rw [e1, e2, neg_sq, sub_neg_eq_add, ← sub_eq_add_neg] at hf
    linarith only [hf, g12, g34']
  · -- both on the left
    have hf := wideFold_folded (L := L) (a := a) (b := b) hβ (abs_nonneg U) (abs_nonneg V)
      (by rw [abs_of_nonpos hU0, abs_of_nonpos hV0]
          rw [abs_of_nonpos (by linarith : U + V ≤ 0)] at hsum
          rcases le_total 0 (U - V) with h | h
          · rw [abs_of_nonneg h] at hsum
            rw [abs_of_nonpos (by linarith : -U - -V ≤ 0)]; linarith
          · rw [abs_of_nonpos h] at hsum
            rw [abs_of_nonneg (by linarith : 0 ≤ -U - -V)]; linarith)
      (fun h => by
        rw [abs_of_nonpos hU0, abs_of_nonpos hV0] at h
        have : x = y := by linarith
        rw [ha, hb, this])
    have e1 : wideSameRate L |U| |V| = archLevyDensity |U - V| - archLevyDensity (L - |U + V|) := by
      unfold wideSameRate
      rw [abs_of_nonpos hU0, abs_of_nonpos hV0, abs_of_nonpos (by linarith : U + V ≤ 0),
        show -U - -V = -(U - V) by ring, abs_neg, show -U + -V = -(U + V) by ring]
    have e2 : wideCrossRate L |U| |V| = archLevyDensity |U + V| - archLevyDensity (L - |U - V|) := by
      unfold wideCrossRate
      rw [abs_of_nonpos hU0, abs_of_nonpos hV0, abs_of_nonpos (by linarith : U + V ≤ 0),
        show -U - -V = -(U - V) by ring, abs_neg, show -U + -V = -(U + V) by ring]
    rw [e1, e2] at hf
    linarith only [hf, g12, g34']

/-! ### A band of pairs withheld -/

/-- The surplus kernel with the pairs of `[c, ∞)²` withheld. -/
def withheldKernel (c x y : ℝ) : ℝ := if c ≤ x ∧ c ≤ y then 0 else surplusKernel x y

/-- The wide folded weight with the band `u, v ≥ b` withheld. -/
def wideFoldWeightBand (L β b u v : ℝ) : ℝ :=
  if b ≤ u ∧ b ≤ v then 0 else wideFoldWeight L β u v

theorem withheldKernel_mul_sq_nonneg {c x y : ℝ} (hx : 0 < x) (hy : 0 < y) (F : ℝ → ℝ) :
    0 ≤ withheldKernel c x y * (F x - F y) ^ 2 := by
  unfold withheldKernel
  split_ifs
  · simp
  · by_cases hxy : x = y
    · rw [hxy, sub_self]; simp
    · exact mul_nonneg (surplusKernel_nonneg hx hy hxy) (sq_nonneg _)

/-- **The wide quadruple inequality with a band withheld.** The pairs with both points in `[c, ∞)`
are withheld; the folded weight vanishes on the band `u, v ≥ c − L/2`. -/
theorem wideBandQuadruple_ge {p r L β c x y : ℝ} (hp : 0 < p) (hL : p + r = L) (hβ : 0 < β)
    (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) (F : ℝ → ℝ) :
    reflectedOddPart F L x ^ 2 * wideFoldWeightBand L β (c - L / 2) |x - L / 2| |y - L / 2| +
        reflectedOddPart F L y ^ 2 * wideFoldWeightBand L β (c - L / 2) |y - L / 2| |x - L / 2| ≤
      withheldKernel c x y * (F x - F y) ^ 2 +
        withheldKernel c (L - x) (L - y) * (F (L - x) - F (L - y)) ^ 2 +
        withheldKernel c x (L - y) * (F x - F (L - y)) ^ 2 +
        withheldKernel c (L - x) y * (F (L - x) - F y) ^ 2 := by
  have hx0 : 0 < x := by linarith [hx.1]
  have hy0 : 0 < y := by linarith [hy.1]
  have hxL0 : 0 < L - x := by linarith [hx.2]
  have hyL0 : 0 < L - y := by linarith [hy.2]
  by_cases hB : c - L / 2 ≤ |x - L / 2| ∧ c - L / 2 ≤ |y - L / 2|
  · -- the band: the weight vanishes
    unfold wideFoldWeightBand
    rw [if_pos hB, if_pos ⟨hB.2, hB.1⟩, mul_zero, mul_zero, add_zero]
    linarith [withheldKernel_mul_sq_nonneg (c := c) hx0 hy0 F,
      withheldKernel_mul_sq_nonneg (c := c) hxL0 hyL0 F, withheldKernel_mul_sq_nonneg (c := c) hx0 hyL0 F,
      withheldKernel_mul_sq_nonneg (c := c) hxL0 hy0 F]
  -- off the band one of `x, y` has both reflections below `c`, so no pair is withheld
  unfold wideFoldWeightBand
  rw [if_neg hB, if_neg (fun h => hB ⟨h.2, h.1⟩)]
  have hside : (x < c ∧ L - x < c) ∨ (y < c ∧ L - y < c) := by
    rcases not_and_or.mp hB with h | h
    · left
      rw [not_le] at h
      exact ⟨by linarith [le_abs_self (x - L / 2)], by linarith [neg_abs_le (x - L / 2)]⟩
    · right
      rw [not_le] at h
      exact ⟨by linarith [le_abs_self (y - L / 2)], by linarith [neg_abs_le (y - L / 2)]⟩
  have hk : ∀ z w, (z < c ∨ w < c) → withheldKernel c z w = surplusKernel z w := fun z w h => by
    unfold withheldKernel
    rw [if_neg (fun h' => by rcases h with h | h <;> linarith [h'.1, h'.2])]
  rcases hside with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hk x y (Or.inl h1), hk (L - x) (L - y) (Or.inl h2), hk x (L - y) (Or.inl h1),
      hk (L - x) y (Or.inl h2)]
    exact wideQuadruple_ge hp hL hβ hx hy F
  · rw [hk x y (Or.inr h1), hk (L - x) (L - y) (Or.inr h2), hk x (L - y) (Or.inr h2),
      hk (L - x) y (Or.inr h1)]
    exact wideQuadruple_ge hp hL hβ hx hy F


/-! ### The integrated wide fold -/

theorem measurable_wideFoldWeightBand (L β b : ℝ) :
    Measurable (Function.uncurry (wideFoldWeightBand L β b)) := by
  unfold wideFoldWeightBand wideFoldWeight wideSameRate wideCrossRate
  have h1 : Measurable fun z : ℝ × ℝ => archLevyDensity |z.1 - z.2| :=
    measurable_archLevyDensity.comp (measurable_fst.sub measurable_snd).abs
  have h2 : Measurable fun z : ℝ × ℝ => archLevyDensity (L - (z.1 + z.2)) :=
    measurable_archLevyDensity.comp (measurable_const.sub (measurable_fst.add measurable_snd))
  have h3 : Measurable fun z : ℝ × ℝ => archLevyDensity (z.1 + z.2) :=
    measurable_archLevyDensity.comp (measurable_fst.add measurable_snd)
  have h4 : Measurable fun z : ℝ × ℝ => archLevyDensity (L - |z.1 - z.2|) :=
    measurable_archLevyDensity.comp (measurable_const.sub (measurable_fst.sub measurable_snd).abs)
  refine Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
    (measurableSet_le measurable_const measurable_snd)) measurable_const ?_
  exact ((((h1.sub h2).sub (h3.sub h4)).mul (measurable_const.sub ((measurable_const.add measurable_snd).div
    (measurable_const.add measurable_fst)))).const_mul 2).add ((h3.sub h4).const_mul 4)

/-- **The wide weight is bounded on the half-window.** For `0 < u ≤ η`, `0 ≤ v ≤ η`, `η ≤ 1/2`,
`2p ≤ L − 2η`: `|W(u, v)| ≤ 3/β + 2ω(2p)η/β + 4(ω(u + v) + ω(2p))`. -/
theorem abs_wideFoldWeight_le {L β p η u v : ℝ} (hβ : 0 < β) (hp : 0 < p) (hu0 : 0 < u) (hv0 : 0 ≤ v)
    (hu : u ≤ η) (hv : v ≤ η) (hη1 : η ≤ 1 / 2) (hLη : 2 * p ≤ L - 2 * η) :
    |wideFoldWeight L β u v| ≤
      3 / β + 2 * archLevyDensity (2 * p) * η / β + 4 * (archLevyDensity (u + v) + archLevyDensity (2 * p)) := by
  have hω2p := archLevyDensity_pos (show 0 < 2 * p by linarith)
  have hqb : |1 - (β + v) / (β + u)| ≤ η / β := by
    have e : 1 - (β + v) / (β + u) = (u - v) / (β + u) := by field_simp; ring
    rw [e, abs_div, abs_of_pos (by linarith : 0 < β + u), div_le_div_iff₀ (by linarith) hβ]
    have : |u - v| ≤ η := abs_le.mpr ⟨by linarith, by linarith⟩
    nlinarith
  have hk : |surplusKernel u v * (1 - (β + v) / (β + u))| ≤ 3 / 2 / β := by
    rcases eq_or_lt_of_le hv0 with hv' | hv'
    · rw [← hv', surplusKernel_comm, surplusKernel_zero_left hu0.le, zero_mul, abs_zero]
      positivity
    have := abs_surplusKernel_mul_le (h := fun t => β + t) (L := 1) hu0 hv'
      (by rw [abs_le]; constructor <;> linarith) hβ (by linarith)
      (by simp only [one_mul]; rw [show β + u - (β + v) = u - v by ring])
    rw [abs_one, mul_one] at this
    exact this
  have hab : |u - v| ≤ u + v := abs_le.mpr ⟨by linarith, by linarith⟩
  have hLuv : 2 * p ≤ L - (u + v) := by linarith
  have hD0 : 0 ≤ archLevyDensity (L - |u - v|) := (archLevyDensity_pos (by linarith)).le
  have hD2 : archLevyDensity (L - |u - v|) ≤ archLevyDensity (2 * p) :=
    strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith))
      (by linarith)
  have hD1 : archLevyDensity (L - (u + v)) ≤ archLevyDensity (2 * p) :=
    strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) hLuv
  have hD3 : archLevyDensity (L - |u - v|) ≤ archLevyDensity (L - (u + v)) :=
    strictAntiOn_archLevyDensity.antitoneOn (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith))
      (by linarith)
  have hω := archLevyDensity_pos (show 0 < u + v by linarith)
  set D := archLevyDensity (L - (u + v)) - archLevyDensity (L - |u - v|) with hDdef
  set q := 1 - (β + v) / (β + u) with hqdef
  have hDq : |D * q| ≤ archLevyDensity (2 * p) * (η / β) := by
    rw [abs_mul, abs_of_nonneg (by rw [hDdef]; linarith)]
    exact mul_le_mul (by rw [hDdef]; linarith) hqb (abs_nonneg _) hω2p.le
  have hR : |archLevyDensity (u + v) - archLevyDensity (L - |u - v|)| ≤
      archLevyDensity (u + v) + archLevyDensity (2 * p) := by
    rw [abs_le]; constructor <;> linarith
  have e : wideFoldWeight L β u v =
      2 * (surplusKernel u v * q - D * q) + 4 * (archLevyDensity (u + v) - archLevyDensity (L - |u - v|)) := by
    unfold wideFoldWeight wideSameRate wideCrossRate surplusKernel
    rw [hqdef, hDdef]; ring
  rw [e]
  have t1 := abs_add_le (2 * (surplusKernel u v * q - D * q))
    (4 * (archLevyDensity (u + v) - archLevyDensity (L - |u - v|)))
  have t2 := abs_sub (surplusKernel u v * q) (D * q)
  rw [abs_mul, abs_mul (4 : ℝ), abs_two, show |(4 : ℝ)| = 4 by norm_num] at t1
  have e2 : 2 * archLevyDensity (2 * p) * η / β = 2 * (archLevyDensity (2 * p) * (η / β)) := by ring
  have e3 : 3 / β = 2 * (3 / 2 / β) := by ring
  rw [e2, e3]
  linarith

/-- **The wide folded weight is bounded on the strip.** For `x, y ∈ [p, r]`, `η = (r − p)/2 ≤ 1/2`:
`|α(x)² W_band| ≤ K²η²(3/β + 2ω(2p)η/β + 4ω(2p)) + K²(2η + η²)`. -/
theorem abs_bandFoldedWeight_le {F : ℝ → ℝ} {K p r L β c x y : ℝ}
    (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|) (hp : 0 < p) (hL : p + r = L) (hr1 : r - p ≤ 1)
    (hβ : 0 < β) (hx : x ∈ Icc p r) (hy : y ∈ Icc p r) :
    abs (reflectedOddPart F L x ^ 2 * wideFoldWeightBand L β (c - L / 2) |x - L / 2| |y - L / 2|) ≤
      K ^ 2 * ((r - p) / 2) ^ 2 * (3 / β + 2 * archLevyDensity (2 * p) * ((r - p) / 2) / β +
          4 * archLevyDensity (2 * p)) + K ^ 2 * (2 * ((r - p) / 2) + ((r - p) / 2) ^ 2) := by
  have hα := abs_reflectedOddPart_le (L := L) hFL x
  have hK0 : 0 ≤ K := by
    have := hFL 1 0; norm_num at this; linarith [abs_nonneg (F 1 - F 0)]
  have hω2p := archLevyDensity_pos (show 0 < 2 * p by linarith)
  have hu : |x - L / 2| ≤ (r - p) / 2 := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
  have hv : |y - L / 2| ≤ (r - p) / 2 := by rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
  set η := (r - p) / 2 with hη
  set u := |x - L / 2| with hudef
  set v := |y - L / 2| with hvdef
  have hη0 : 0 ≤ η := le_trans (abs_nonneg _) hu
  set C : ℝ := 3 / β + 2 * archLevyDensity (2 * p) * η / β + 4 * archLevyDensity (2 * p) with hCdef
  have hC : 0 ≤ C := by rw [hCdef]; positivity
  have hu0 : 0 ≤ u := abs_nonneg _
  have hv0 : 0 ≤ v := abs_nonneg _
  have hα2 : reflectedOddPart F L x ^ 2 ≤ K ^ 2 * u ^ 2 := by
    rw [← sq_abs]
    have := mul_le_mul hα hα (abs_nonneg _) (mul_nonneg hK0 hu0)
    nlinarith [abs_nonneg (reflectedOddPart F L x)]
  have hR0 : 0 ≤ K ^ 2 * η ^ 2 * C + K ^ 2 * (2 * η + η ^ 2) := by
    have : 0 ≤ η := le_trans hu0 hu
    positivity
  rcases eq_or_lt_of_le hu0 with h0 | h0
  · have : reflectedOddPart F L x = 0 := by
      have := hα; rw [← h0, mul_zero] at this; exact abs_nonpos_iff.mp this
    rw [this, zero_pow two_ne_zero, zero_mul, abs_zero]; exact hR0
  have hWb : |wideFoldWeightBand L β (c - L / 2) u v| ≤ |wideFoldWeight L β u v| := by
    unfold wideFoldWeightBand; split_ifs
    · rw [abs_zero]; exact abs_nonneg _
    · exact le_rfl
  have hW := abs_wideFoldWeight_le (L := L) (p := p) hβ hp h0 hv0 hu hv (by linarith) (by linarith)
  have hωu := archLevyDensity_le_inv (show 0 < u + v by linarith)
  have h1 : u ^ 2 * archLevyDensity (u + v) ≤ u / 2 + u ^ 2 / 4 := by
    have h2 := mul_le_mul_of_nonneg_left hωu (sq_nonneg u)
    have h3 : u ^ 2 * (1 / (2 * (u + v))) ≤ u / 2 := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    nlinarith
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hu2 : u ^ 2 ≤ η ^ 2 := pow_le_pow_left₀ hu0 hu 2
  have hW' : |wideFoldWeightBand L β (c - L / 2) u v| ≤ C + 4 * archLevyDensity (u + v) := by
    rw [hCdef]; linarith
  have hm := mul_le_mul hα2 hW' (abs_nonneg _) (mul_nonneg (sq_nonneg K) (sq_nonneg u))
  have h4 : K ^ 2 * (u ^ 2 * archLevyDensity (u + v)) ≤ K ^ 2 * (u / 2 + u ^ 2 / 4) :=
    mul_le_mul_of_nonneg_left h1 (sq_nonneg K)
  have h5 : K ^ 2 * (u / 2 + u ^ 2 / 4) ≤ K ^ 2 * ((2 * η + η ^ 2) / 4) :=
    mul_le_mul_of_nonneg_left (by nlinarith) (sq_nonneg K)
  have h6 : K ^ 2 * u ^ 2 * C ≤ K ^ 2 * η ^ 2 * C :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hu2 (sq_nonneg K)) hC
  have e : K ^ 2 * u ^ 2 * (C + 4 * archLevyDensity (u + v)) =
      K ^ 2 * u ^ 2 * C + 4 * (K ^ 2 * (u ^ 2 * archLevyDensity (u + v))) := by ring
  rw [e] at hm
  linarith

section WideStrip

variable {F : ℝ → ℝ} {K p r L : ℝ} (hF : Continuous F) (hFL : ∀ a b, |F a - F b| ≤ K * |a - b|)
  (hp : 0 < p) (hpr : p < r) (hL : p + r = L) (hr1 : r - p ≤ 1)

include hF hFL hp hpr hL hr1 in
/-- **The wide micro-fold of the strip with a band withheld.** If the folded weight integrates to at
least `2λ` over the strip at every folded point `u ∈ (0, η]`, `η = (r − p)/2`, then the surplus of the
pairs of `[p, r]²` outside `[c, r]²` is at least `λ ∫_p^r α²`, `α` the odd part about `L/2`. -/
theorem wideBandMicroFold_strip_ge {β c lam : ℝ} (hβ : 0 < β)
    (hpot : ∀ u, 0 < u → u ≤ (r - p) / 2 →
      2 * lam ≤ ∫ y in p..r, wideFoldWeightBand L β (c - L / 2) u |y - L / 2|) :
    lam * (∫ x in p..r, reflectedOddPart F L x ^ 2) ≤
      ∫ x in p..r, ∫ y in p..r, withheldKernel c x y * (F x - F y) ^ 2 := by
  set C : ℝ := 3 / 2 * K ^ 2 * (r - p) with hC
  have hmg : Measurable (Function.uncurry fun x y => withheldKernel c x y * (F x - F y) ^ 2) := by
    unfold withheldKernel
    refine Measurable.mul (Measurable.ite ((measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_const measurable_snd)) measurable_const measurable_surplusKernel) ?_
    exact ((hF.measurable.comp measurable_fst).sub (hF.measurable.comp measurable_snd)).pow_const 2
  have hrefl : ∀ x, x ∈ Icc p r → L - x ∈ Icc p r := fun x hx =>
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hbd : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r, |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y| ≤ C :=
    fun x hx y hy => by
      have h := abs_strip_integrand_le hFL hp hr1 hx hy
      simp only
      unfold withheldKernel
      split_ifs
      · rw [zero_mul, abs_zero]; exact (abs_nonneg _).trans h
      · exact h
  obtain ⟨hi0, ho0⟩ := intervalIntegrable_iterated hpr.le hmg hbd
  have hm1 := measurable_uncurry_reflect_both hmg L
  have hm2 := measurable_uncurry_reflect_snd hmg L
  have hm3 := measurable_uncurry_reflect_fst hmg L
  obtain ⟨hi1, ho1⟩ := intervalIntegrable_iterated hpr.le hm1 fun x hx y hy =>
    hbd _ (hrefl x hx) _ (hrefl y hy)
  obtain ⟨hi2, ho2⟩ := intervalIntegrable_iterated hpr.le hm2 fun x hx y hy =>
    hbd _ hx _ (hrefl y hy)
  obtain ⟨hi3, ho3⟩ := intervalIntegrable_iterated hpr.le hm3 fun x hx y hy =>
    hbd _ (hrefl x hx) _ hy
  set T := ∫ x in p..r, ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y with hT
  -- the three reflected copies equal `T`
  have hT1 : (∫ x in p..r, ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y)) = fun x => ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y :=
      funext fun x => integral_strip_reflect hL ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x))
    rw [e]
    exact integral_strip_reflect hL (fun x => ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y)
  have hT2 : (∫ x in p..r, ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y)) = T := by
    have e : (fun x => ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y)) = fun x => ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y :=
      funext fun x => integral_strip_reflect hL ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x)
    rw [e]
  have hT3 : (∫ x in p..r, ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y) = T :=
    integral_strip_reflect hL (fun x => ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y)
  -- the sum of the four copies, as one iterated integral
  have hsum : (∫ x in p..r, ∫ y in p..r, ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y)) =
      4 * T := by
    have hin : ∀ x ∈ uIcc p r, (∫ y in p..r, ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y)) =
        (∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y) + (∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y)) + (∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y)) +
          ∫ y in p..r, (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y := fun x hx => by
      rw [uIcc_of_le hpr.le] at hx
      rw [intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx) |>.add (hi2 x hx)) (hi3 x hx),
        intervalIntegral.integral_add ((hi0 x hx).add (hi1 x hx)) (hi2 x hx),
        intervalIntegral.integral_add (hi0 x hx) (hi1 x hx)]
    rw [intervalIntegral.integral_congr hin, intervalIntegral.integral_add ((ho0.add ho1).add ho2) ho3,
      intervalIntegral.integral_add (ho0.add ho1) ho2, intervalIntegral.integral_add ho0 ho1,
      hT1, hT2, hT3]
    ring
  -- integrability of the summed integrand
  have hms : Measurable (Function.uncurry fun x y => (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y +
      (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y) := by
    have := ((hmg.add hm1).add hm2).add hm3
    exact this
  obtain ⟨his, hos⟩ := intervalIntegrable_iterated (C := 4 * C) hpr.le hms fun x hx y hy => by
    have h0 := hbd x hx y hy
    have h1 := hbd _ (hrefl x hx) _ (hrefl y hy)
    have h2 := hbd _ hx _ (hrefl y hy)
    have h3 := hbd _ (hrefl x hx) _ hy
    calc |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y) +
          (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y|
        ≤ |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y| + |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y)| + |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y)| +
          |(fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y| := by
          have := abs_add_le ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y) +
            (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y)) ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y)
          have := abs_add_le ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y))
            ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y))
          have := abs_add_le ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y) ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y))
          linarith
      _ ≤ 4 * C := by linarith
  -- the folded weight
  set η := (r - p) / 2 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  have hαc : Continuous fun x => reflectedOddPart F L x ^ 2 := by
    unfold reflectedOddPart; fun_prop
  have hΦm : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L x ^ 2 * wideFoldWeightBand L β (c - L / 2) |x - L / 2| |y - L / 2|) :=
    ((hαc.measurable.comp measurable_fst).mul
      (measurable_uncurry_abs_sub (measurable_wideFoldWeightBand L β (c - L / 2)) (L / 2)))
  have hΦb : ∀ x ∈ Icc p r, ∀ y ∈ Icc p r,
      abs (reflectedOddPart F L x ^ 2 * wideFoldWeightBand L β (c - L / 2) |x - L / 2| |y - L / 2|) ≤
        K ^ 2 * η ^ 2 * (3 / β + 2 * archLevyDensity (2 * p) * η / β + 4 * archLevyDensity (2 * p)) +
          K ^ 2 * (2 * η + η ^ 2) :=
    fun x hx y hy => abs_bandFoldedWeight_le hFL hp hL hr1 hβ hx hy
  obtain ⟨hiΦ, hoΦ⟩ := intervalIntegrable_iterated hpr.le hΦm hΦb
  have hΦm' : Measurable (Function.uncurry fun x y =>
      reflectedOddPart F L y ^ 2 * wideFoldWeightBand L β (c - L / 2) |y - L / 2| |x - L / 2|) :=
    hΦm.comp measurable_swap
  obtain ⟨hiΦ', hoΦ'⟩ := intervalIntegrable_iterated hpr.le hΦm' fun x hx y hy => hΦb y hy x hx
  -- the pointwise inequality, integrated
  have hinner1 : ∀ x ∈ Icc p r,
      (∫ y in p..r, reflectedOddPart F L x ^ 2 * wideFoldWeightBand L β (c - L / 2) |x - L / 2| |y - L / 2|) +
        (∫ y in p..r, reflectedOddPart F L y ^ 2 * wideFoldWeightBand L β (c - L / 2) |y - L / 2| |x - L / 2|) ≤
      ∫ y in p..r, ((fun x y => withheldKernel c x y * (F x - F y) ^ 2) x y + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) (L - y) +
        (fun x y => withheldKernel c x y * (F x - F y) ^ 2) x (L - y) + (fun x y => withheldKernel c x y * (F x - F y) ^ 2) (L - x) y) := fun x hx => by
    rw [← intervalIntegral.integral_add (hiΦ x hx) (hiΦ' x hx)]
    refine intervalIntegral.integral_mono_on hpr.le ((hiΦ x hx).add (hiΦ' x hx)) (his x hx)
      fun y hy => ?_
    exact wideBandQuadruple_ge hp hL hβ hx hy F
  have hint1 :
      (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L x ^ 2 * wideFoldWeightBand L β (c - L / 2) |x - L / 2| |y - L / 2|) +
        (∫ x in p..r, ∫ y in p..r,
          reflectedOddPart F L y ^ 2 * wideFoldWeightBand L β (c - L / 2) |y - L / 2| |x - L / 2|) ≤
        4 * T := by
    rw [← intervalIntegral.integral_add hoΦ hoΦ', ← hsum]
    exact intervalIntegral.integral_mono_on hpr.le (hoΦ.add hoΦ') hos fun x hx => hinner1 x hx
  have hswap := integral_integral_swap_box hpr.le hΦm hΦb
  -- the inner integral is the potential of the folded odd part
  have hinner : ∀ x ∈ Icc p r, 2 * lam * reflectedOddPart F L x ^ 2 ≤
      ∫ y in p..r, reflectedOddPart F L x ^ 2 * wideFoldWeightBand L β (c - L / 2) |x - L / 2| |y - L / 2| := by
    intro x hx
    have hu : |x - L / 2| ≤ η := by rw [abs_le]; constructor <;> linarith [hx.1, hx.2]
    rcases eq_or_lt_of_le (abs_nonneg (x - L / 2)) with h0 | h0
    · have hα := abs_reflectedOddPart_le (L := L) hFL x
      have : reflectedOddPart F L x = 0 := by
        rw [← h0, mul_zero] at hα; exact abs_nonpos_iff.mp hα
      rw [this]; simp
    rw [intervalIntegral.integral_const_mul, mul_comm (2 * lam)]
    exact mul_le_mul_of_nonneg_left (hpot _ h0 hu) (sq_nonneg _)
  have hmono := intervalIntegral.integral_mono_on hpr.le ((hαc.intervalIntegrable p r).const_mul
    (2 * lam)) hoΦ fun x hx => hinner x hx
  rw [intervalIntegral.integral_const_mul] at hmono
  rw [hswap] at hint1
  linarith

end WideStrip

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
