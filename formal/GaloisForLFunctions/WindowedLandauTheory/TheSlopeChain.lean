import Mathlib

/-!
# The slope chain

A finite nonempty family of words `u` carries lattices `N_u`, `M_u` with ranks `d_u > 0`, minimal and
maximal slopes `μ_N(u) ≤ μ_N^max(u)`, `μ_M(u)`, `μ_M^max(u)`, heights `h_u`, exponents `E_u`, levels
`log T_u` and losses `Lo_u`, and a dual lattice with slope `μ*`. The *gain* `G` measures how far the
slopes of `N` exceed those of `M`:

```text
μ_M(u) + G + F - E_u - Lo_u ≤ μ_N(u),    μ_N^max(u) ≤ μ_M^max(u) + G + F - E_u + B.
```

If the dual slope is bounded above by an archimedean term (`μ* + h_u - F ≤ S - A log T_u + E_div`,
with `log T_u ≥ Λ`), and below by the rank-weighted mean slope `s = mean_d (μ_N - h)` through the
mean-slope inequality

```text
s - log |W| - (1-δ)⁻¹ (4 u log(1 + H/u) + (η + 4√e) H) ≤ μ*,   u = max (μ_N^max - h) - s,
```

then `μ*` cancels and the gain is bounded by the archimedean term (`gain_le_of_slopeChain`):

```text
G ≤ S - AΛ + Sl + E⁺ + E_div + mean_d Lo + log |W|
      + (1-δ)⁻¹ (4 log(1+X) (Sl⁺ + Sl + V + B + mean_d Lo + b) + (η + 4√e) X b).
```

The spread `u` of the slopes is controlled by the two gain bounds (`spread_le`), and
`u log(1 + H/u) ≤ log(1+X)(U + b)` for `u ≤ U`, `H ≤ Xb` (`mul_log_one_add_div_le`).
-/

open Finset

namespace WindowedLandauTheory

noncomputable section

section RankMean

variable {ι : Type*} [Fintype ι]

/-- The rank-weighted mean `Σ d X / Σ d`. -/
def rankMean (d X : ι → ℝ) : ℝ := (∑ i, d i * X i) / ∑ i, d i

theorem sum_rank_pos [Nonempty ι] {d : ι → ℝ} (hd : ∀ i, 0 < d i) : 0 < ∑ i, d i :=
  Finset.sum_pos (fun i _ => hd i) Finset.univ_nonempty

/-- A pointwise lower bound `c - Y ≤ X` passes to the means. -/
theorem sub_rankMean_le [Nonempty ι] {d X Y : ι → ℝ} (hd : ∀ i, 0 < d i) {c : ℝ}
    (h : ∀ i, c - Y i ≤ X i) : c - rankMean d Y ≤ rankMean d X := by
  have hS := sum_rank_pos hd
  unfold rankMean
  rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hS, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := mul_le_mul_of_nonneg_left (h i) (hd i).le
  nlinarith

theorem rankMean_le_const [Nonempty ι] {d X : ι → ℝ} (hd : ∀ i, 0 < d i) {c : ℝ}
    (h : ∀ i, X i ≤ c) : rankMean d X ≤ c := by
  have hS := sum_rank_pos hd
  unfold rankMean
  rw [div_le_iff₀ hS, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    have := mul_le_mul_of_nonneg_left (h i) (hd i).le
    linarith

end RankMean

/-- `u log(1 + H/u) ≤ log(1+X)(U + b)` for `0 ≤ u ≤ U` and `0 < H ≤ Xb`. -/
theorem mul_log_one_add_div_le {u H X b U : ℝ} (hu : 0 ≤ u) (hH : 0 < H) (hHX : H ≤ X * b)
    (hb : 0 < b) (hX : 0 < X) (huU : u ≤ U) :
    u * Real.log (1 + H / u) ≤ Real.log (1 + X) * (U + b) := by
  have hX1 : 0 < 1 + X := by linarith
  have hL : 0 ≤ Real.log (1 + X) := Real.log_nonneg (by linarith)
  -- `1 - 1/(1+X) ≤ log(1+X)`
  have hb0 : X / (1 + X) ≤ Real.log (1 + X) := by
    have h := Real.one_sub_inv_le_log_of_pos hX1
    have e : 1 - (1 + X)⁻¹ = X / (1 + X) := by field_simp; ring
    linarith
  have hbX : H / (1 + X) ≤ b * Real.log (1 + X) := by
    calc H / (1 + X) ≤ X * b / (1 + X) := div_le_div_of_nonneg_right hHX hX1.le
      _ = b * (X / (1 + X)) := by ring
      _ ≤ b * Real.log (1 + X) := mul_le_mul_of_nonneg_left hb0 hb.le
  rcases hu.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]
    have : 0 ≤ U + b := by linarith
    positivity
  · have h1 : 0 < 1 + H / u := by positivity
    -- `log y ≤ log(1+X) + y/(1+X) - 1`
    have ha : Real.log (1 + H / u) ≤ Real.log (1 + X) + ((1 + H / u) / (1 + X) - 1) := by
      have h := Real.log_le_sub_one_of_pos (div_pos h1 hX1)
      rw [Real.log_div h1.ne' hX1.ne'] at h
      linarith
    have e : u * (Real.log (1 + X) + ((1 + H / u) / (1 + X) - 1)) =
        u * Real.log (1 + X) - u * (X / (1 + X)) + H / (1 + X) := by
      field_simp
      ring
    have i1 := mul_le_mul_of_nonneg_left ha hu
    have i2 := mul_le_mul_of_nonneg_right huU hL
    have i3 : 0 ≤ u * (X / (1 + X)) := by positivity
    rw [e] at i1
    nlinarith

/-- Slope data on a finite family of words. -/
structure SlopeChain (W : Type*) where
  rank : W → ℝ
  muN : W → ℝ
  muMaxN : W → ℝ
  ht : W → ℝ
  muM : W → ℝ
  muMaxM : W → ℝ
  logT : W → ℝ
  expo : W → ℝ
  loss : W → ℝ
  muDual : ℝ
  gain : ℝ
  F : ℝ

namespace SlopeChain

variable {W : Type*} [Fintype W] [Nonempty W] (S : SlopeChain W)

/-- The rank-weighted mean slope `s = mean_d (μ_N - h)`. -/
def meanSlope : ℝ := rankMean S.rank fun u => S.muN u - S.ht u

/-- The spread `max (μ_N^max - h) - s` of the slopes above their mean. -/
def spread : ℝ :=
  (Finset.univ.sup' Finset.univ_nonempty fun u => S.muMaxN u - S.ht u) - S.meanSlope

theorem spread_nonneg (hrank : ∀ u, 0 < S.rank u) (hN : ∀ u, S.muN u ≤ S.muMaxN u) :
    0 ≤ S.spread := by
  have h : S.meanSlope ≤ Finset.univ.sup' Finset.univ_nonempty fun u => S.muMaxN u - S.ht u :=
    rankMean_le_const hrank fun u => (sub_le_sub_right (hN u) _).trans
      (Finset.le_sup' (fun u => S.muMaxN u - S.ht u) (Finset.mem_univ u))
  unfold spread
  linarith

/-- **The spread is controlled by the gain bounds.** -/
theorem spread_le (hrank : ∀ u, 0 < S.rank u) {B Sl SlU V : ℝ}
    (hlow : ∀ u, S.muM u + S.gain + S.F - S.expo u - S.loss u ≤ S.muN u)
    (hup : ∀ u, S.muMaxN u ≤ S.muMaxM u + S.gain + S.F - S.expo u + B)
    (hM : ∀ u, -Sl ≤ S.muM u ∧ S.muMaxM u ≤ SlU)
    (hV : ∀ u u', (S.expo u' + S.ht u') - (S.expo u + S.ht u) ≤ V) :
    S.spread ≤ SlU + Sl + V + B + rankMean S.rank S.loss := by
  have hs : ∀ u, S.muMaxN u - S.ht u - (SlU + Sl + V + B) - rankMean S.rank S.loss ≤
      S.meanSlope := by
    intro u
    refine sub_rankMean_le hrank fun u' => ?_
    have h1 := hup u
    have h2 := hlow u'
    have h3 := (hM u).2
    have h4 := (hM u').1
    have h5 := hV u u'
    linarith
  have hsup := Finset.sup'_le (Finset.univ_nonempty (α := W)) (fun u => S.muMaxN u - S.ht u)
    (a := S.meanSlope + (SlU + Sl + V + B + rankMean S.rank S.loss))
    (fun u _ => by have := hs u; linarith)
  unfold spread
  linarith

/-- **The gain bound.** The dual slope cancels between the archimedean upper bound and the
mean-slope inequality. -/
theorem gain_le_of_slopeChain (hrank : ∀ u, 0 < S.rank u) (hN : ∀ u, S.muN u ≤ S.muMaxN u)
    {A S₀ Λ EDiv Sl SlU Eplus B V δ η e HH X b : ℝ}
    (hlow : ∀ u, S.muM u + S.gain + S.F - S.expo u - S.loss u ≤ S.muN u)
    (hup : ∀ u, S.muMaxN u ≤ S.muMaxM u + S.gain + S.F - S.expo u + B)
    (hdiv : ∀ u, S.muDual + S.ht u - S.F ≤ S₀ - A * S.logT u + EDiv)
    (hA : 0 ≤ A) (hcount : ∀ u, Λ ≤ S.logT u)
    (hM : ∀ u, -Sl ≤ S.muM u ∧ S.muMaxM u ≤ SlU) (hE : ∀ u, S.expo u ≤ Eplus)
    (hV : ∀ u u', (S.expo u' + S.ht u') - (S.expo u + S.ht u) ≤ V)
    (hδ : δ < 1) (hη : 0 ≤ η) (hHH : 0 < HH) (hHHX : HH ≤ X * b) (hX : 0 < X)
    (hb : 0 < b)
    (hineq : S.meanSlope - Real.log (Fintype.card W) - (1 - δ)⁻¹ *
      (4 * S.spread * Real.log (1 + HH / S.spread) + (η + 4 * Real.sqrt e) * HH) ≤ S.muDual) :
    S.gain ≤ S₀ - A * Λ + Sl + Eplus + EDiv + rankMean S.rank S.loss +
      Real.log (Fintype.card W) + (1 - δ)⁻¹ *
        (4 * Real.log (1 + X) * (SlU + Sl + V + B + rankMean S.rank S.loss + b) +
          (η + 4 * Real.sqrt e) * (X * b)) := by
  -- the mean slope from below
  have hsl : S.gain + S.muDual - (Sl + Eplus + S₀ - A * Λ + EDiv) - rankMean S.rank S.loss ≤
      S.meanSlope := by
    refine sub_rankMean_le hrank fun u => ?_
    have h1 := hlow u
    have h2 := hdiv u
    have h3 := mul_le_mul_of_nonneg_left (hcount u) hA
    have h4 := (hM u).1
    have h5 := hE u
    linarith
  -- the loss term of the mean-slope inequality
  have hu0 := S.spread_nonneg hrank hN
  have hu := S.spread_le hrank hlow hup hM hV
  have hphi := mul_log_one_add_div_le hu0 hHH hHHX hb hX hu
  have hc : 0 ≤ η + 4 * Real.sqrt e := by positivity
  have hB : (η + 4 * Real.sqrt e) * HH ≤ (η + 4 * Real.sqrt e) * (X * b) :=
    mul_le_mul_of_nonneg_left hHHX hc
  have hinv : 0 ≤ (1 - δ)⁻¹ := inv_nonneg.2 (by linarith)
  have hloss : (1 - δ)⁻¹ * (4 * S.spread * Real.log (1 + HH / S.spread) +
        (η + 4 * Real.sqrt e) * HH) ≤
      (1 - δ)⁻¹ * (4 * Real.log (1 + X) * (SlU + Sl + V + B + rankMean S.rank S.loss + b) +
        (η + 4 * Real.sqrt e) * (X * b)) := by
    refine mul_le_mul_of_nonneg_left ?_ hinv
    have e4 : 4 * S.spread * Real.log (1 + HH / S.spread) =
        4 * (S.spread * Real.log (1 + HH / S.spread)) := by ring
    have e5 : 4 * Real.log (1 + X) * (SlU + Sl + V + B + rankMean S.rank S.loss + b) =
        4 * (Real.log (1 + X) * (SlU + Sl + V + B + rankMean S.rank S.loss + b)) := by ring
    rw [e4, e5]
    linarith
  linarith

end SlopeChain

end

end WindowedLandauTheory
