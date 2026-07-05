/-
The dyadic assembly's scalar core (doc 87 App B, the (L3) base case).

Five facts the dyadic sum consumes, each banked separately:

* `radial_band_empty_of_norm_large` / `_of_norm_small` / `_of_B_large` —
  the reachable window: outside `ρ − r ≤ ‖c'‖ + ‖B‖`, `‖c'‖ ≤ ρ + r + ‖B‖`,
  `‖B‖ ≤ ρ + r + ‖c'‖` the radial band is EMPTY (triangle inequality; no
  band machinery needed).
* `exists_dyadic_cover` — every `t ∈ [1, 2^J)` lands in a dyadic window
  `[2^j, 2^{j+1})` with `j < J`: the shell index exists.
* `one_sub_abs_bandCenter_of_dist` — the MARGIN INVERSION: squared
  center-modulus at distance `≥ σ` from BOTH caustic values
  `y₊ = (ρ+‖B‖)²`, `y₋ = (ρ−‖B‖)²` (and `2σ ≤ y₊ − y₋`) forces
  `1 − |bandCenter| ≥ σ·(y₊−y₋)/(16·y₊·‖B‖²)` — the input to the
  transversal law on each dyadic shell, via the caustic factorization
  `one_sub_bandCenter_sq` and `one_sub_abs_ge`.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBShellBounds

namespace RHTower
namespace Sublevel

/-- Outer emptiness: a center too far out cannot reach the annulus. -/
theorem radial_band_empty_of_norm_large {B c' : ℂ} {ρ r : ℝ}
    (h : ρ + r + ‖B‖ < ‖c'‖) :
    {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c' + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r} = ∅ := by
  ext φ
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hband⟩
  have htri := abs_norm_sub_norm_le
    (c' + B * Complex.exp ((φ : ℂ) * Complex.I)) c'
  rw [add_sub_cancel_left, norm_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one] at htri
  have h1 := abs_le.mp htri
  have h2 := abs_le.mp hband
  linarith [h1.1, h2.2]

/-- Inner emptiness, small center: `‖c'‖ + ‖B‖ < ρ − r` cannot reach the
annulus from below. -/
theorem radial_band_empty_of_norm_small {B c' : ℂ} {ρ r : ℝ}
    (h : ‖c'‖ + ‖B‖ < ρ - r) :
    {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c' + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r} = ∅ := by
  ext φ
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hband⟩
  have htri := norm_add_le c' (B * Complex.exp ((φ : ℂ) * Complex.I))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at htri
  have h2 := abs_le.mp hband
  linarith [h2.1]

/-- Inner emptiness, large arm: `ρ + r + ‖c'‖ < ‖B‖` overshoots the
annulus for every angle. -/
theorem radial_band_empty_of_B_large {B c' : ℂ} {ρ r : ℝ}
    (h : ρ + r + ‖c'‖ < ‖B‖) :
    {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c' + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r} = ∅ := by
  ext φ
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨_, hband⟩
  have htri := abs_norm_sub_norm_le
    (c' + B * Complex.exp ((φ : ℂ) * Complex.I))
    (B * Complex.exp ((φ : ℂ) * Complex.I))
  rw [add_sub_cancel_right, norm_mul, Complex.norm_exp_ofReal_mul_I,
    mul_one] at htri
  have h1 := abs_le.mp htri
  have h2 := abs_le.mp hband
  linarith [h1.1, h2.2]

/-- **Dyadic cover**: every `t ∈ [1, 2^J)` lies in some window
`[2^j, 2^{j+1})`, `j < J`. -/
theorem exists_dyadic_cover {t : ℝ} {J : ℕ} (h1 : 1 ≤ t)
    (h2 : t < 2 ^ J) :
    ∃ j < J, (2 : ℝ) ^ j ≤ t ∧ t < 2 ^ (j + 1) := by
  induction J with
  | zero =>
      norm_num at h2
      linarith
  | succ J ih =>
      rcases lt_or_ge t (2 ^ J) with h | h
      · obtain ⟨j, hj, hle, hlt⟩ := ih h
        exact ⟨j, Nat.lt_succ_of_lt hj, hle, hlt⟩
      · exact ⟨J, Nat.lt_succ_self J, h, h2⟩

/-- **The margin inversion.**  If the squared center modulus keeps distance
`≥ σ` from both caustic values `y₊ = (ρ+‖B‖)²`, `y₋ = (ρ−‖B‖)²`, and
`2σ ≤ y₊ − y₋`, then the band center keeps tangency margin
`σ·(y₊−y₋)/(16·y₊·‖B‖²)` — the transversal law's input on a dyadic shell. -/
theorem one_sub_abs_bandCenter_of_dist {c' B : ℂ} {ρ σ : ℝ} (hc' : c' ≠ 0)
    (hB : B ≠ 0) (hσ : 0 < σ)
    (hdp : σ ≤ (ρ + ‖B‖) ^ 2 - ‖c'‖ ^ 2)
    (hdm : σ ≤ ‖c'‖ ^ 2 - (ρ - ‖B‖) ^ 2)
    (hσG : 2 * σ ≤ (ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) :
    σ * ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2)
        / (16 * ((ρ + ‖B‖) ^ 2 * ‖B‖ ^ 2))
      ≤ 1 - |bandCenter c' B ρ| := by
  have hx0 : (0 : ℝ) < ‖c'‖ := norm_pos_iff.mpr hc'
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hyP0 : (0 : ℝ) < (ρ + ‖B‖) ^ 2 := by
    nlinarith [hdp, hdm, sq_nonneg (ρ - ‖B‖), sq_nonneg ‖c'‖]
  have hG : (0 : ℝ) < (ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2 :=
    lt_of_lt_of_le (by linarith : (0 : ℝ) < 2 * σ) hσG
  have hfac := one_sub_bandCenter_sq (c := c') (B := B) ρ hc' hB
  -- product lower bound: d₊·d₋ ≥ σ(G − σ) ≥ σ·G/2
  have hprod : σ * (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 2)
      ≤ ((ρ + ‖B‖) ^ 2 - ‖c'‖ ^ 2) * (‖c'‖ ^ 2 - (ρ - ‖B‖) ^ 2) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdp) (sub_nonneg.mpr hdm),
      mul_nonneg hσ.le (sub_nonneg.mpr hσG)]
  -- x² ≤ y₊
  have hxy : ‖c'‖ ^ 2 ≤ (ρ + ‖B‖) ^ 2 := by nlinarith [hdp, hσ]
  have hdd0 : (0 : ℝ)
      ≤ ((ρ + ‖B‖) ^ 2 - ‖c'‖ ^ 2) * (‖c'‖ ^ 2 - (ρ - ‖B‖) ^ 2) :=
    mul_nonneg (by linarith) (by linarith)
  -- 1 − U₀² ≥ σ·(G/2)/(4·y₊·b²)
  have hU2 : σ * (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 2)
        / (4 * ((ρ + ‖B‖) ^ 2 * ‖B‖ ^ 2))
      ≤ 1 - bandCenter c' B ρ ^ 2 := by
    rw [hfac, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right hprod
        (by positivity : (0 : ℝ) ≤ 4 * (‖c'‖ ^ 2 * ‖B‖ ^ 2)),
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hxy
          (by positivity : (0 : ℝ) ≤ 4 * ‖B‖ ^ 2)) hdd0]
  -- |U₀| ≤ 1 from 1 − U₀² > 0
  have hU2pos : (0 : ℝ) < 1 - bandCenter c' B ρ ^ 2 := by
    refine lt_of_lt_of_le ?_ hU2
    exact div_pos (mul_pos hσ (by linarith)) (by positivity)
  have habs1 : |bandCenter c' B ρ| ≤ 1 := by
    nlinarith [sq_abs (bandCenter c' B ρ), abs_nonneg (bandCenter c' B ρ)]
  have hhalf := one_sub_abs_ge habs1
  have hgoal : σ * ((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2)
        / (16 * ((ρ + ‖B‖) ^ 2 * ‖B‖ ^ 2))
      = (σ * (((ρ + ‖B‖) ^ 2 - (ρ - ‖B‖) ^ 2) / 2)
          / (4 * ((ρ + ‖B‖) ^ 2 * ‖B‖ ^ 2))) / 2 := by
    field_simp
    ring
  rw [hgoal]
  linarith [hU2, hhalf]

end Sublevel
end RHTower

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- **Pointwise transversal arm with a center-modulus floor**: margin `m`
plus half-width fitting under the tangency gap gives the linear law with
`xmin` in the denominator. -/
theorem vol_K_le_of_margin {B c' : ℂ} {ρ r m xmin : ℝ} (hB : B ≠ 0)
    (hρ : 0 ≤ ρ) (hr : 0 ≤ r) (hm : 0 < m) (hm1 : m ≤ 1) (hx0 : 0 < xmin)
    (hxm : xmin ≤ ‖c'‖)
    (hmarg : m + bandHalf c' B ρ r ≤ 1 - |bandCenter c' B ρ|) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c' + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ ENNReal.ofReal (2 * Real.pi * (r * (2 * ρ + r))
          / (Real.sqrt m * (xmin * ‖B‖))) := by
  have hc' : c' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxm
    linarith
  have htrans : |bandCenter c' B ρ| + bandHalf c' B ρ r ≤ 1 - m := by
    linarith
  refine le_trans
    (radial_band_measure_transversal hc' hB hρ hr hm hm1 htrans)
    (ENNReal.ofReal_le_ofReal ?_)
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hsm : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.mpr hm
  refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
  gcongr

/-- **Pointwise √-law arm with a center-modulus floor.** -/
theorem vol_K_le_sqrt {B c' : ℂ} {ρ r xmin : ℝ} (hB : B ≠ 0) (hρ : 0 ≤ ρ)
    (hr : 0 ≤ r) (hx0 : 0 < xmin) (hxm : xmin ≤ ‖c'‖) :
    volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
        |‖c' + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r}
      ≤ ENNReal.ofReal (2 * Real.pi
          * Real.sqrt (2 * (r * (2 * ρ + r) / (xmin * ‖B‖)))) := by
  have hc' : c' ≠ 0 := by
    intro h
    rw [h, norm_zero] at hxm
    linarith
  refine le_trans (radial_band_measure hc' hB hρ hr)
    (ENNReal.ofReal_le_ofReal ?_)
  have hb0 : (0 : ℝ) < ‖B‖ := norm_pos_iff.mpr hB
  have hdiv : r * (2 * ρ + r) / (‖c'‖ * ‖B‖)
      ≤ r * (2 * ρ + r) / (xmin * ‖B‖) :=
    div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_right hxm (norm_nonneg B))
  have hs : Real.sqrt (2 * (r * (2 * ρ + r) / (‖c'‖ * ‖B‖)))
      ≤ Real.sqrt (2 * (r * (2 * ρ + r) / (xmin * ‖B‖))) :=
    Real.sqrt_le_sqrt (by linarith)
  exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- The dyadic cancellation `√(t·s/d)/√(t·h) = √(s/(h·d))`: the shell scale
`t = 2^j` drops out of the (shell measure) × (linear arm) product. -/
theorem sqrt_div_sqrt_cancel {t s h d : ℝ} (ht : 0 < t) (hs : 0 ≤ s)
    (hh : 0 < h) (hd : 0 < d) :
    Real.sqrt (t * s / d) / Real.sqrt (t * h) = Real.sqrt (s / (h * d)) := by
  rw [← Real.sqrt_div (by positivity) (t * h)]
  congr 1
  field_simp

end Sublevel
end RHTower
