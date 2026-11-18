import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The exponent algebra of the joint moment induction

The scalar content of the inverse and ordinary halves of the joint moment induction.

* `selected_exponents`: complete-factor selection of width `u′` gives `N′ − z′ = N − z`,
  `H₀ = 2(N′ + V) − K′ = 1 − 6u′` at the parameter cap `M = 2F₀ − 1`, the normalization
  `(K′ − N′ − V) + (H_c + u′) = F₀ + κ_P`, and `K′ ≤ F₀` when `F₀ + 4u′ ≤ 1` (eq. (47)).
* `largeValue_gap`, `largeValue_shortRemainder`: with `s = H((1 − R)/2 + z_R) + u/k` and
  `g(ν) = (r + s − H/2 − Ha₀ − u/ν)/D`, `D = 1/2 − a₁`, one has
  `D(g − r) = H(z_R − λ(R)) + u(1/k − 1/ν)` and `s − (H − g)/2 − Ha₀ + a₁g = g − r + u/ν`.
* `shortClass_bound` (Proposition 8.9, short sums): `C_s + νr + es < H + u − Hkω/20`.
* `longClass_value`, `longClass_increment`, `longClass_bound` (Proposition 8.9, long sums):
  `G(k) = H F_high`, the increment formula for `G(ν) − G(k)`, and
  `C_l + νr + es ≤ H + u − H F_high/2`.
* `smallValue_exponent`: the small-value pointwise exponent is exactly `u`.
* `excess_slope_short`, `excess_slope_long`, `excess_slope_core`, `slope_bound_max`,
  `slope_bound_ciInf`, `slope_bound_ciSup`, `sixthPower_cofactor`: every excess exponent has
  `M`-slope at least `−5/6`, the bound passes to maxima, infima and suprema (eq. (49)), and a
  sixth-power cofactor of norm `Z^x` lowers `d + p(d)` by `x`.
* `cutoff_condition_of_condition13`: condition 13 bounds `νw + eσ(w) < 5/6` on the cutoff
  interval.
* `referenceKernel_exponents`: the local exponents `E(k, m) = 1 − (k + m)/2 + r₀(k − 49m/20)`,
  `r₀ = 15/98`, of the compensated cubic kernel (table of §8.8), and `3(1/2 − r₀) = 51/49`.
* `reflected_reference_face`, `ordinary_side_normalization`: the reflected reference face (50)
  and the exact side normalization `2a − k_C + q_C = 1 + t − 6u_C` of the ordinary induction (52).
-/

namespace GaloisForLFunctions.JointMarkedMoments

open Set

noncomputable section

/-! ### Complete-factor selection -/

/-- The selection identities (47). -/
theorem selected_exponents (N V z u κ : ℝ) :
    let F₀ := N + V
    let M := 2 * F₀ - 1
    let N' := N - u
    let K' := M + 4 * u
    let H₀ := 2 * (N' + V) - K'
    N' - (z - u) = N - z ∧ H₀ = 1 - 6 * u ∧
      (K' - N' - V) + (H₀ + κ + u) = F₀ + κ ∧ (F₀ + 4 * u ≤ 1 → K' ≤ F₀) := by
  intro F₀ M N' K' H₀
  refine ⟨by ring, by simp only [H₀, N', K', M, F₀]; ring, by simp only [H₀, N', K', M, F₀]; ring,
    fun h => by simp only [K', M, F₀] at h ⊢; linarith⟩

/-! ### The estimate for large values -/

/-- The cutoff length function `g(ν) = (r + s − H/2 − Ha₀ − u/ν)/D`. -/
def cutoffLength (r s H a₀ u D ν : ℝ) : ℝ := (r + s - H / 2 - H * a₀ - u / ν) / D

/-- The marked length `s = H((1 − R)/2 + z_R) + u/k` of a stage. -/
def stageMarkedLength (H R zR u k : ℝ) : ℝ := H * ((1 - R) / 2 + zR) + u / k

theorem largeValue_gap {H R zR u k ν a₀ a₁ : ℝ} (hD : 1 / 2 - a₁ ≠ 0) :
    (1 / 2 - a₁) * (cutoffLength (H * R) (stageMarkedLength H R zR u k) H a₀ u (1 / 2 - a₁) ν -
      H * R) = H * (zR - (a₀ - a₁ * R)) + u * (1 / k - 1 / ν) := by
  unfold cutoffLength stageMarkedLength
  rw [mul_sub, mul_div_cancel₀ _ hD]
  ring

theorem largeValue_shortRemainder {r s H a₀ a₁ u ν : ℝ} (hD : 1 / 2 - a₁ ≠ 0) :
    s - (H - cutoffLength r s H a₀ u (1 / 2 - a₁) ν) / 2 - H * a₀ +
        a₁ * cutoffLength r s H a₀ u (1 / 2 - a₁) ν =
      cutoffLength r s H a₀ u (1 / 2 - a₁) ν - r + u / ν := by
  have h : (1 / 2 - a₁) * cutoffLength r s H a₀ u (1 / 2 - a₁) ν =
      r + s - H / 2 - H * a₀ - u / ν := by
    unfold cutoffLength; rw [mul_div_cancel₀ _ hD]
  linear_combination (-1 : ℝ) * h

/-- The reference marked length `σ(w) = max(0, (1 − w)/2 + a₀ − a₁w − π)`. -/
def referenceLength (a₀ a₁ π w : ℝ) : ℝ := max 0 ((1 - w) / 2 + a₀ - a₁ * w - π)

/-- Proposition 8.9, short sums: at the cutoff `w = g/H + ω` the short count of every amplitude
class `(ν, e)`, `k ≤ ν`, `0 ≤ e ≤ ν`, saves `Hkω/20` (padding `ω > 0`, `0 < π < ω/20`). -/
theorem shortClass_bound {H r s g a₀ a₁ u ν e k ω π : ℝ} (hH : 0 < H) (hk : 0 < k)
    (hkν : k ≤ ν) (he0 : 0 ≤ e) (heν : e ≤ ν) (ha0 : 0 ≤ a₁) (ha1 : a₁ ≤ 2 / 5) (hω : 0 < ω)
    (hπ0 : 0 < π) (hπ : π < ω / 20) (hg : 0 ≤ g - r + u / ν)
    (hrem : s - (H - g) / 2 - H * a₀ + a₁ * g = g - r + u / ν) :
    H - ν * H * (g / H + ω) - e * min s (H * referenceLength a₀ a₁ π (g / H + ω)) + ν * r + e * s <
      H + u - H * k * ω / 20 := by
  have hν : 0 < ν := lt_of_lt_of_le hk hkν
  have hHw : H * (g / H + ω) = g + H * ω := by field_simp
  -- `Hσ(w) ≥ (H − g)/2 + Ha₀ − a₁g − H((1/2 + a₁)ω + π)`
  have hσ : (H - g) / 2 + H * a₀ - a₁ * g - H * ((1 / 2 + a₁) * ω + π) ≤
      H * referenceLength a₀ a₁ π (g / H + ω) := by
    have h1 := le_max_right 0 ((1 - (g / H + ω)) / 2 + a₀ - a₁ * (g / H + ω) - π)
    have h2 := mul_le_mul_of_nonneg_left h1 hH.le
    unfold referenceLength
    nlinarith [hHw]
  have hbr0 : 0 ≤ H * ((1 / 2 + a₁) * ω + π) := by positivity
  set X := g - r + u / ν + H * ((1 / 2 + a₁) * ω + π) with hX
  -- `[s − Hσ]₊ ≤ X`
  have hpos : s - min s (H * referenceLength a₀ a₁ π (g / H + ω)) ≤ X := by
    rcases le_total s (H * referenceLength a₀ a₁ π (g / H + ω)) with h | h
    · rw [min_eq_left h, sub_self]; linarith
    · rw [min_eq_right h]; linarith
  have hX0 : 0 ≤ X := by linarith
  have e1 : ν * H * (g / H + ω) = ν * g + ν * H * ω := by rw [mul_assoc, hHw]; ring
  have e2 : ν * X = ν * g - ν * r + u + ν * H * ((1 / 2 + a₁) * ω + π) := by
    rw [hX]; field_simp
  have t1 := mul_le_mul_of_nonneg_left hpos he0
  have t2 := mul_le_mul_of_nonneg_right heν hX0
  have t5 : ν * H * ((1 / 2 + a₁) * ω + π) - ν * H * ω ≤ -(H * ν * (ω / 10 - π)) := by
    have : 0 ≤ ν * H * ω := by positivity
    nlinarith
  have t3 : H * k * ω / 20 < H * ν * (ω / 10 - π) := by
    have h1 : k * ω / 20 < ν * (ω / 10 - π) := by nlinarith
    nlinarith
  nlinarith

/-- The high-cutoff margin `F_high = 5/6 − (5/4 − 3k/2)ŵ − k(1 + R)/2 − k z_R`. -/
def highMargin (k R zR ŵ : ℝ) : ℝ := 5 / 6 - (5 / 4 - 3 * k / 2) * ŵ - k * (1 + R) / 2 - k * zR

/-- The long-branch function `G(ν) = H + u − H/6 − (5/6 − ν)·3g(ν)/2 − ν(r + s)`. -/
def longBranch (H u r s g ν : ℝ) : ℝ := H + u - H / 6 - (5 / 6 - ν) * (3 * g / 2) - ν * (r + s)

/-- `G(k) = H F_high` with `ŵ = (R/2 + z_R − a₀)/D`. -/
theorem longClass_value {H R zR u k a₀ a₁ : ℝ} (hk : k ≠ 0) :
    longBranch H u (H * R) (stageMarkedLength H R zR u k)
        (cutoffLength (H * R) (stageMarkedLength H R zR u k) H a₀ u (1 / 2 - a₁) k) k =
      H * highMargin k R zR ((R / 2 + zR - a₀) / (1 / 2 - a₁)) := by
  unfold longBranch cutoffLength stageMarkedLength highMargin
  field_simp
  ring

/-- `G(ν) − G(k) = (ν − k)(3g(ν)/2 − (3/2)(5/6 − k)u/(kνD) − (r + s))`. -/
theorem longClass_increment {H u r s a₀ D k ν : ℝ} (hD : D ≠ 0) (hk : k ≠ 0) (hν : ν ≠ 0) :
    longBranch H u r s (cutoffLength r s H a₀ u D ν) ν -
        longBranch H u r s (cutoffLength r s H a₀ u D k) k =
      (ν - k) * (3 * cutoffLength r s H a₀ u D ν / 2 - 3 / 2 * (5 / 6 - k) * u / (k * ν * D) -
        (r + s)) := by
  unfold longBranch cutoffLength
  field_simp
  ring

/-- Proposition 8.9, long sums: `C_l + νr + es ≤ H + u − H F_high/2` once
`(5/6 − k)H(3ω/2 + τ) < H F_high/2` and `G(ν) ≥ G(k) = H F_high`. -/
theorem longClass_bound {H u r s g ν e k ω τ Fh : ℝ} (hkν : k ≤ ν) (hν : ν ≤ 5 / 6)
    (heν : e ≤ ν) (hs : 0 ≤ s) (hH : 0 < H) (hωτ : 0 ≤ 3 * ω / 2 + τ)
    (hG : H * Fh ≤ longBranch H u r s g ν)
    (hpad : (5 / 6 - k) * H * (3 * ω / 2 + τ) < H * Fh / 2) :
    H / 6 + (5 / 6 - ν) * H * (3 * ((g + H * ω) / H) / 2 + τ) + ν * r + e * s ≤
      H + u - H * Fh / 2 := by
  have hHg : H * ((g + H * ω) / H) = g + H * ω := by field_simp
  have h1 : (5 / 6 - ν) * H * (3 * ω / 2 + τ) ≤ (5 / 6 - k) * H * (3 * ω / 2 + τ) := by
    have : 0 ≤ H * (3 * ω / 2 + τ) := by positivity
    nlinarith
  have h2 := mul_le_mul_of_nonneg_right heν hs
  unfold longBranch at hG
  nlinarith [hHg]

/-- The small-value pointwise exponent `k(s − H((1 − R)/2 + z_R)) = u`. -/
theorem smallValue_exponent {H R zR u k : ℝ} (hk : k ≠ 0) :
    k * (stageMarkedLength H R zR u k - H * ((1 - R) / 2 + zR)) = u := by
  unfold stageMarkedLength; field_simp; ring

/-! ### The sixth-power factors -/

/-- The short excess `A_s(M) = νP + es − νMw − e min(s, Mσ)` has `M`-slope at least `−5/6`
when `νw + eσ ≤ 5/6`. -/
theorem excess_slope_short {ν e P s w σ M₁ M₂ : ℝ} (he : 0 ≤ e) (hσ : 0 ≤ σ) (hM : M₁ ≤ M₂)
    (h13 : ν * w + e * σ ≤ 5 / 6) :
    ν * P + e * s - ν * M₁ * w - e * min s (M₁ * σ) ≤
      ν * P + e * s - ν * M₂ * w - e * min s (M₂ * σ) + 5 / 6 * (M₂ - M₁) := by
  have hmin : min s (M₂ * σ) ≤ min s (M₁ * σ) + (M₂ - M₁) * σ := by
    rcases le_total s (M₁ * σ) with h | h
    · rw [min_eq_left h]
      have : 0 ≤ (M₂ - M₁) * σ := mul_nonneg (by linarith) hσ
      linarith [min_le_left s (M₂ * σ)]
    · rw [min_eq_right h]
      have := min_le_right s (M₂ * σ)
      nlinarith
  have := mul_le_mul_of_nonneg_left hmin he
  nlinarith [mul_le_mul_of_nonneg_left h13 (sub_nonneg.2 hM)]

/-- The long excess `A_l(M) = −5M/6 + (5/6 − ν)Mt + νP + es` has `M`-slope at least `−5/6`. -/
theorem excess_slope_long {ν e P s t M₁ M₂ : ℝ} (hνt : 0 ≤ (5 / 6 - ν) * t) (hM : M₁ ≤ M₂) :
    -(5 * M₁ / 6) + (5 / 6 - ν) * M₁ * t + ν * P + e * s ≤
      -(5 * M₂ / 6) + (5 / 6 - ν) * M₂ * t + ν * P + e * s + 5 / 6 * (M₂ - M₁) := by
  nlinarith [mul_nonneg hνt (sub_nonneg.2 hM)]

/-- The small-core excess `A₀(M) = −5M/6 + 1/15 + 3P/4 + s` has `M`-slope exactly `−5/6`. -/
theorem excess_slope_core (P s M₁ M₂ : ℝ) :
    -(5 * M₁ / 6) + 1 / 15 + 3 * P / 4 + s =
      -(5 * M₂ / 6) + 1 / 15 + 3 * P / 4 + s + 5 / 6 * (M₂ - M₁) := by ring

/-- A slope bound `f(M₁) ≤ f(M₂) + c` passes to maxima. -/
theorem slope_bound_max {a₁ a₂ b₁ b₂ c : ℝ} (ha : a₁ ≤ a₂ + c) (hb : b₁ ≤ b₂ + c) :
    max a₁ b₁ ≤ max a₂ b₂ + c :=
  max_le (ha.trans (by linarith [le_max_left a₂ b₂]))
    (hb.trans (by linarith [le_max_right a₂ b₂]))

/-- A slope bound passes to infima over a nonempty index set. -/
theorem slope_bound_ciInf {ι : Type*} [Nonempty ι] {f g : ι → ℝ} {c : ℝ}
    (hf : BddBelow (range f)) (h : ∀ i, f i ≤ g i + c) : ⨅ i, f i ≤ (⨅ i, g i) + c := by
  have : (⨅ i, f i) - c ≤ ⨅ i, g i := le_ciInf fun i => by linarith [ciInf_le hf i, h i]
  linarith

/-- A slope bound passes to suprema over a nonempty index set. -/
theorem slope_bound_ciSup {ι : Type*} [Nonempty ι] {f g : ι → ℝ} {c : ℝ}
    (hg : BddAbove (range g)) (h : ∀ i, f i ≤ g i + c) : ⨆ i, f i ≤ (⨆ i, g i) + c :=
  ciSup_le fun i => (h i).trans (by linarith [le_ciSup hg i])

/-- Removing a sixth-power cofactor of norm `Z^x` from a parameter of length `M` lowers
`d + p(d)`, `d = M − 6x`, by `x` whenever `p` has `M`-slope at least `−5/6`. -/
theorem sixthPower_cofactor {p : ℝ → ℝ} {M x : ℝ}
    (hp : p (M - 6 * x) ≤ p M + 5 / 6 * (M - (M - 6 * x))) :
    (M - 6 * x) + p (M - 6 * x) ≤ M + p M - x := by
  linarith

/-- Condition 13 controls every class on the cutoff interval: `w + σ(w)` is nondecreasing for
`a₁ ≤ 1/2`, so `νw + eσ(w) < 5/6` for `0 ≤ w ≤ w₊`, `e ≤ ν ≤ 3/4`. -/
theorem cutoff_condition_of_condition13 {a₀ a₁ π w wp ν e : ℝ} (ha1 : a₁ ≤ 1 / 2) (hπ : 0 ≤ π)
    (hw0 : 0 ≤ w) (hw : w ≤ wp) (hν : ν ≤ 3 / 4) (heν : e ≤ ν)
    (h13 : 0 < 5 / 6 - 3 / 4 * wp - 3 / 4 * max 0 ((1 - wp) / 2 + (a₀ - a₁ * wp))) :
    ν * w + e * referenceLength a₀ a₁ π w < 5 / 6 := by
  have hσ0 : 0 ≤ referenceLength a₀ a₁ π w := le_max_left _ _
  have hmono : w + referenceLength a₀ a₁ π w ≤ wp + max 0 ((1 - wp) / 2 + (a₀ - a₁ * wp)) := by
    unfold referenceLength
    have hY0 := le_max_left 0 ((1 - wp) / 2 + (a₀ - a₁ * wp))
    have hY1 := le_max_right 0 ((1 - wp) / 2 + (a₀ - a₁ * wp))
    rcases le_total 0 ((1 - w) / 2 + a₀ - a₁ * w - π) with h | h
    · rw [max_eq_right h]
      have : (1 - w) / 2 + a₀ - a₁ * w - π + w ≤ (1 - wp) / 2 + (a₀ - a₁ * wp) + wp := by
        nlinarith
      linarith
    · rw [max_eq_left h]; linarith
  have h1 : e * referenceLength a₀ a₁ π w ≤ ν * referenceLength a₀ a₁ π w :=
    mul_le_mul_of_nonneg_right heν hσ0
  have h2 : ν * (w + referenceLength a₀ a₁ π w) ≤
      3 / 4 * (wp + max 0 ((1 - wp) / 2 + (a₀ - a₁ * wp))) := by
    have : 0 ≤ w + referenceLength a₀ a₁ π w := by linarith
    nlinarith
  nlinarith

/-! ### The reference ordinary moment -/

/-- The local exponent `E(k, m) = 1 − (k + m)/2 + r₀(k − 49m/20)`, `r₀ = 15/98`, of an exterior
prime with ordinary kernel degree `k` and `m` marked positions. -/
def referenceKernelExponent (k m : ℝ) : ℝ := 1 - (k + m) / 2 + 15 / 98 * (k - 49 / 20 * m)

/-- The table of §8.8 and the convergence exponent `3(1/2 − r₀) = 51/49`. -/
theorem referenceKernel_exponents :
    (3 / 4 : ℝ) / (2 * (49 / 20)) = 15 / 98 ∧ 3 * (1 / 2 - 15 / 98 : ℝ) = 51 / 49 ∧
      (∀ k : ℝ, 3 ≤ k → referenceKernelExponent k 0 ≤ -2 / 49) ∧
      (∀ k : ℝ, 1 ≤ k → referenceKernelExponent k 1 ≤ -87 / 392) ∧
      (∀ k m : ℝ, 0 ≤ k → 2 ≤ m → referenceKernelExponent k m ≤ -3 / 4) ∧
      (∀ k : ℝ, 3 ≤ k → 1 - (k + 0) / 2 ≤ -1 / 2) ∧
      (∀ k m : ℝ, 1 ≤ k + m → 2 ≤ k + m ∨ m = 1 → 1 - (k + m) / 2 ≤ 1 / 2) := by
  refine ⟨by norm_num, by norm_num, fun k hk => ?_, fun k hk => ?_, fun k m hk hm => ?_,
    fun k hk => by linarith, fun k m h1 _ => by linarith⟩ <;>
  · unfold referenceKernelExponent; linarith

/-- The reflected reference face (50): widths `x ≤ 7/50` and `1 − P + x`, `P ≥ 2/3`,
`S < 137/1000`, stay strictly inside the face `P + 49S/20 ≤ 99/100` with margin `1/25`; the direct
term satisfies `7/50 + 1/2 + (49/20)(137/1000) < 99/100`. -/
theorem reflected_reference_face {x P S : ℝ} (hx : x ≤ 7 / 50) (hP : 2 / 3 ≤ P)
    (hS : S < 137 / 1000) :
    x + (1 - P + x) + 49 / 20 * S < 99 / 100 - 1 / 25 ∧
      (7 / 50 : ℝ) + 1 / 2 + 49 / 20 * (137 / 1000) < 99 / 100 := by
  constructor
  · linarith
  · norm_num

/-- The side normalization of the ordinary induction (52) and the paired-side cancellation. -/
theorem ordinary_side_normalization (A c d q t uC : ℝ) :
    2 * (A - c - uC) - ((2 * A - c - d + q - 1 - t) + 4 * uC) + (q + c - d) = 1 + t - 6 * uC ∧
      (A - c + (q + c - d)) + (A - d + (q + d - c)) = 2 * (A + q) - c - d := by
  constructor <;> ring

end

end GaloisForLFunctions.JointMarkedMoments
