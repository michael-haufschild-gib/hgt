import GaloisForLFunctions.GaloisTheoryOfZeros.ALoopOfSaddlesTurnsTheSquaredRatioOfTheTwoTermsAroundOne
import GaloisForLFunctions.GaloisTheoryOfZeros.OnlyACollisionOffTheCentreMovesAPair
import GaloisForLFunctions.RigidArithmeticOfCuts.ZerosOfADirichletPolynomialRecurEffectively
import GaloisForLFunctions.HTGeometry.DerivSignMonotone

/-!
# A collision away from the centre exists at a forward time

**Theorem** (`exists_forward_multipleZero_ne_zero`). For every `T` there are a time `τ` with
`Re τ > max T 0` and a place `ζ ≠ 0` with `H_τ(ζ) = 0` and `H_τ'(ζ) = 0`.

Hence the forward monodromy group does not preserve the pairs `{z, −z}`
(`not_forwardMonodromy_preserves_pairs`): at every base time it contains an element that carries
some zero `z` to a zero other than `±z`. No hypothesis on the zeros of `ξ` is used.

Proof. On a loop of saddles `a(s)` the heat family at the time `τ(a(s))` is the model
`B₀ + 2S₀ cos ζ` in the variable `ζ = a(s)z`, up to `|B₀|/8192`, and
`(2S₀)² cos² ξ₀(s) = (1 + e)B₀²`, `|e| ≤ 1/4096`, `ξ₀(s) = e^{iπs}/4` (`IsModelLoop`).

* The continuous function `2S₀ cos ξ₀/B₀` has its square near `1`, so its sign is constant
  (`norm_sub_le_or_norm_add_le`): with `θ = π` or `θ = 2π`,
  `|2S₀ cos θ cos ξ₀(s) + B₀| ≤ |B₀|/4096` for all `s` (`IsModelLoop.exists_turn`).
* Then `(B₀ + 2S₀ cos(θ + ξ)) cos ξ₀ = B₀(cos ξ₀ − cos ξ) + (2S₀ cos θ cos ξ₀ + B₀) cos ξ`: the
  family has no zero on the circle `|a(s)z − θ − ξ₀(s)| = 1/16` (`le_norm_of_mem_annulus`), is
  small at its centre (`norm_le_at_turnPoint`), and does not vanish at `z = 0`
  (`ne_zero_at_centre`).
* If a time of the loop is a branch time, its multiple zero is not the centre. Otherwise the
  loop is a forward loop; the zero in the first disc follows the centres `θ + ξ₀(s)` and arrives
  near `θ − 1/4`, having started near `θ + 1/4`: it is carried to a zero outside its pair, and
  the detector `exists_multipleZero_ne_zero_of_transports` gives the collision.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Sine and cosine on the unit disc -/

/-- `|sin w| ≥ |w|/2` on the unit disc. -/
theorem half_norm_le_norm_sin {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖w‖ / 2 ≤ ‖Complex.sin w‖ := by
  have h := Complex.sin_bound hw
  have h0 := norm_nonneg w
  have h1 : ‖w‖ - ‖w‖ ^ 3 / 6 ≤ ‖w - w ^ 3 / 6‖ := by
    have h2 := norm_sub_norm_le w (w ^ 3 / 6)
    have h3 : ‖w ^ 3 / 6‖ = ‖w‖ ^ 3 / 6 := by rw [norm_div, norm_pow, Complex.norm_ofNat]
    rw [h3] at h2
    exact h2
  have h4 : ‖w - w ^ 3 / 6‖ - ‖Complex.sin w‖ ≤ ‖w‖ ^ 5 / 100 := by
    have h5 := norm_sub_norm_le (w - w ^ 3 / 6) (Complex.sin w)
    rw [norm_sub_rev (w - w ^ 3 / 6) (Complex.sin w)] at h5
    linarith
  have h3 : ‖w‖ ^ 3 ≤ ‖w‖ := by
    calc ‖w‖ ^ 3 = ‖w‖ * ‖w‖ ^ 2 := by ring
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 hw) h0
      _ = ‖w‖ := mul_one _
  have h5 : ‖w‖ ^ 5 ≤ ‖w‖ := by
    calc ‖w‖ ^ 5 = ‖w‖ * ‖w‖ ^ 4 := by ring
      _ ≤ ‖w‖ * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0 hw) h0
      _ = ‖w‖ := mul_one _
  linarith

theorem norm_cos_le_two {w : ℂ} (hw : ‖w‖ ≤ 1) : ‖Complex.cos w‖ ≤ 2 := by
  have h := norm_cos_sub_one_le hw
  have h1 := norm_sub_norm_le (Complex.cos w) 1
  rw [norm_one] at h1
  have h2 : ‖w‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg w) hw
  linarith

/-! ## The model near its two zeros -/

/-- **No zero on the annulus.** Let `sin θ = 0`, `|ξ₀| = 1/4` and
`|2S cos θ cos ξ₀ + B| ≤ |B|/4096`. If `H` is within `|B|/8192` of `B + 2S cos(θ + ξ)` and
`1/16 ≤ |ξ − ξ₀| ≤ 1/8`, then `|H| ≥ (9/8192)|B|`. -/
theorem le_norm_of_mem_annulus {B S θ ξ₀ ξ H : ℂ} (hsin : Complex.sin θ = 0)
    (hξ₀ : ‖ξ₀‖ = 1 / 4)
    (hE : ‖2 * S * Complex.cos θ * Complex.cos ξ₀ + B‖ ≤ ‖B‖ / 4096)
    (hH : ‖H - B - 2 * S * Complex.cos (θ + ξ)‖ ≤ ‖B‖ / 8192)
    (h1 : 1 / 16 ≤ ‖ξ - ξ₀‖) (h2 : ‖ξ - ξ₀‖ ≤ 1 / 8) :
    ‖B‖ * (9 / 8192) ≤ ‖H‖ := by
  have hB := norm_nonneg B
  have hcosadd : Complex.cos (θ + ξ) = Complex.cos θ * Complex.cos ξ := by
    rw [Complex.cos_add, hsin, zero_mul, sub_zero]
  have hξn : ‖ξ‖ ≤ 3 / 8 := by
    have h3 := norm_add_le (ξ - ξ₀) ξ₀
    rw [sub_add_cancel] at h3
    linarith
  have hsum_lo : 3 / 8 ≤ ‖ξ₀ + ξ‖ := by
    have e : ξ₀ + ξ = 2 * ξ₀ + (ξ - ξ₀) := by ring
    have h3 := norm_sub_norm_le (2 * ξ₀) (-(ξ - ξ₀))
    rw [sub_neg_eq_add, norm_neg, norm_mul, Complex.norm_ofNat, hξ₀] at h3
    rw [e]
    linarith
  have hsum_hi : ‖ξ₀ + ξ‖ ≤ 5 / 8 := by
    have h3 := norm_add_le ξ₀ ξ
    linarith
  have hs1 : 3 / 32 ≤ ‖Complex.sin ((ξ₀ + ξ) / 2)‖ := by
    have hn : ‖(ξ₀ + ξ) / 2‖ = ‖ξ₀ + ξ‖ / 2 := by rw [norm_div, Complex.norm_ofNat]
    have h3 := half_norm_le_norm_sin (w := (ξ₀ + ξ) / 2) (by rw [hn]; linarith)
    rw [hn] at h3
    linarith
  have hs2 : 1 / 64 ≤ ‖Complex.sin ((ξ₀ - ξ) / 2)‖ := by
    have hn : ‖(ξ₀ - ξ) / 2‖ = ‖ξ - ξ₀‖ / 2 := by
      rw [norm_div, Complex.norm_ofNat, norm_sub_rev]
    have h3 := half_norm_le_norm_sin (w := (ξ₀ - ξ) / 2) (by rw [hn]; linarith)
    rw [hn] at h3
    linarith
  have hdiff : 3 / 1024 ≤ ‖Complex.cos ξ₀ - Complex.cos ξ‖ := by
    rw [Complex.cos_sub_cos, norm_mul, norm_mul, norm_neg, Complex.norm_ofNat]
    nlinarith [mul_le_mul hs1 hs2 (by norm_num) (norm_nonneg (Complex.sin ((ξ₀ + ξ) / 2)))]
  have hcξ : ‖Complex.cos ξ‖ ≤ 2 := norm_cos_le_two (by linarith)
  have hcξ₀ : ‖Complex.cos ξ₀‖ ≤ 2 := norm_cos_le_two (by rw [hξ₀]; norm_num)
  -- the model times `cos ξ₀`
  have hid : (B + 2 * S * Complex.cos (θ + ξ)) * Complex.cos ξ₀ =
      B * (Complex.cos ξ₀ - Complex.cos ξ) +
        (2 * S * Complex.cos θ * Complex.cos ξ₀ + B) * Complex.cos ξ := by
    rw [hcosadd]
    ring
  have hlow : ‖B‖ * (10 / 4096) ≤ ‖(B + 2 * S * Complex.cos (θ + ξ)) * Complex.cos ξ₀‖ := by
    rw [hid]
    have h3 := norm_sub_norm_le (B * (Complex.cos ξ₀ - Complex.cos ξ))
      (-((2 * S * Complex.cos θ * Complex.cos ξ₀ + B) * Complex.cos ξ))
    rw [sub_neg_eq_add, norm_neg, norm_mul, norm_mul] at h3
    have h4 : ‖B‖ * (3 / 1024) ≤ ‖B‖ * ‖Complex.cos ξ₀ - Complex.cos ξ‖ :=
      mul_le_mul_of_nonneg_left hdiff hB
    have h5 : ‖2 * S * Complex.cos θ * Complex.cos ξ₀ + B‖ * ‖Complex.cos ξ‖ ≤
        ‖B‖ / 4096 * 2 := mul_le_mul hE hcξ (norm_nonneg _) (by positivity)
    linarith
  have hmodel : ‖B‖ * (10 / 8192) ≤ ‖B + 2 * S * Complex.cos (θ + ξ)‖ := by
    rw [norm_mul] at hlow
    have h3 : ‖B + 2 * S * Complex.cos (θ + ξ)‖ * ‖Complex.cos ξ₀‖ ≤
        ‖B + 2 * S * Complex.cos (θ + ξ)‖ * 2 := mul_le_mul_of_nonneg_left hcξ₀ (norm_nonneg _)
    linarith
  have h3 := norm_sub_norm_le (B + 2 * S * Complex.cos (θ + ξ))
    (-(H - B - 2 * S * Complex.cos (θ + ξ)))
  rw [sub_neg_eq_add, norm_neg] at h3
  have e : B + 2 * S * Complex.cos (θ + ξ) + (H - B - 2 * S * Complex.cos (θ + ξ)) = H := by
    ring
  rw [e] at h3
  linarith

/-- **Small at the centre of the disc.** At `ξ = ξ₀` the model is `2S cos θ cos ξ₀ + B`. -/
theorem norm_le_at_turnPoint {B S θ ξ₀ H : ℂ} (hsin : Complex.sin θ = 0)
    (hE : ‖2 * S * Complex.cos θ * Complex.cos ξ₀ + B‖ ≤ ‖B‖ / 4096)
    (hH : ‖H - B - 2 * S * Complex.cos (θ + ξ₀)‖ ≤ ‖B‖ / 8192) :
    ‖H‖ ≤ ‖B‖ * (3 / 8192) := by
  have hcosadd : Complex.cos (θ + ξ₀) = Complex.cos θ * Complex.cos ξ₀ := by
    rw [Complex.cos_add, hsin, zero_mul, sub_zero]
  have e : (H - B - 2 * S * Complex.cos (θ + ξ₀)) +
      (2 * S * Complex.cos θ * Complex.cos ξ₀ + B) = H := by
    rw [hcosadd]
    ring
  have h := norm_add_le (H - B - 2 * S * Complex.cos (θ + ξ₀))
    (2 * S * Complex.cos θ * Complex.cos ξ₀ + B)
  rw [e] at h
  linarith

/-- From `(2S)² = QB²` and `Q cos² ξ₀` near `1`: `|S| ≤ |B|`. -/
theorem norm_saddle_le_norm_bulk {B S Q ξ₀ : ℂ} (hc : 15 / 16 ≤ ‖Complex.cos ξ₀‖)
    (hQ : ‖Q * Complex.cos ξ₀ ^ 2 - 1‖ ≤ 1 / 4096) (hSQ : (2 * S) ^ 2 = Q * B ^ 2) :
    ‖S‖ ≤ ‖B‖ := by
  have h1 : ‖Q * Complex.cos ξ₀ ^ 2‖ ≤ 1 + 1 / 4096 := by
    have h2 := norm_sub_norm_le (Q * Complex.cos ξ₀ ^ 2) 1
    rw [norm_one] at h2
    linarith
  rw [norm_mul, norm_pow] at h1
  have h2 : (225 / 256 : ℝ) ≤ ‖Complex.cos ξ₀‖ ^ 2 := by
    calc (225 / 256 : ℝ) = (15 / 16) ^ 2 := by norm_num
      _ ≤ ‖Complex.cos ξ₀‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hc 2
  have hQn : ‖Q‖ ≤ 4 := by
    have h3 := mul_le_mul_of_nonneg_left h2 (norm_nonneg Q)
    linarith
  have h3 : ‖2 * S‖ ^ 2 = ‖Q‖ * ‖B‖ ^ 2 := by rw [← norm_pow, hSQ, norm_mul, norm_pow]
  rw [norm_mul, Complex.norm_ofNat] at h3
  have h4 : ‖Q‖ * ‖B‖ ^ 2 ≤ 4 * ‖B‖ ^ 2 := mul_le_mul_of_nonneg_right hQn (sq_nonneg _)
  by_contra hcon
  push Not at hcon
  have h5 := mul_self_lt_mul_self (norm_nonneg B) hcon
  nlinarith

/-- **No zero at the centre `z = 0`.** `(B + 2S)(B − 2S) = B²(1 − Q)` and
`(1 − Q)cos² ξ₀ = −sin² ξ₀ − (Q cos² ξ₀ − 1)`. -/
theorem ne_zero_at_centre {B S Q ξ₀ H : ℂ} (hB : B ≠ 0) (hξ₀ : ‖ξ₀‖ = 1 / 4)
    (hQ : ‖Q * Complex.cos ξ₀ ^ 2 - 1‖ ≤ 1 / 4096) (hSQ : (2 * S) ^ 2 = Q * B ^ 2)
    (hH : ‖H - B - 2 * S‖ ≤ ‖B‖ / 8192) : H ≠ 0 := by
  have hBn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have hc1 : ‖Complex.cos ξ₀ - 1‖ ≤ 1 / 16 := by
    calc ‖Complex.cos ξ₀ - 1‖ ≤ ‖ξ₀‖ ^ 2 := norm_cos_sub_one_le (by rw [hξ₀]; norm_num)
      _ = 1 / 16 := by rw [hξ₀]; norm_num
  have hc_lo : 15 / 16 ≤ ‖Complex.cos ξ₀‖ := by
    have h1 := norm_sub_norm_le (1 : ℂ) (Complex.cos ξ₀)
    rw [norm_one, norm_sub_rev] at h1
    linarith
  have hc_hi : ‖Complex.cos ξ₀‖ ≤ 17 / 16 := by
    have h1 := norm_sub_norm_le (Complex.cos ξ₀) 1
    rw [norm_one] at h1
    linarith
  have hSB := norm_saddle_le_norm_bulk hc_lo hQ hSQ
  have hid : (1 - Q) * Complex.cos ξ₀ ^ 2 =
      -(Complex.sin ξ₀ ^ 2) - (Q * Complex.cos ξ₀ ^ 2 - 1) := by
    linear_combination Complex.sin_sq_add_cos_sq ξ₀
  have hsin : 1 / 8 ≤ ‖Complex.sin ξ₀‖ := by
    have h1 := half_norm_le_norm_sin (w := ξ₀) (by rw [hξ₀]; norm_num)
    rw [hξ₀] at h1
    linarith
  have h1Q : 63 / 8192 ≤ ‖1 - Q‖ := by
    have h1 : 63 / 4096 ≤ ‖(1 - Q) * Complex.cos ξ₀ ^ 2‖ := by
      rw [hid]
      have h2 := norm_sub_norm_le (-(Complex.sin ξ₀ ^ 2)) (Q * Complex.cos ξ₀ ^ 2 - 1)
      rw [norm_neg, norm_pow] at h2
      have h3 : (1 / 64 : ℝ) ≤ ‖Complex.sin ξ₀‖ ^ 2 := by
        calc (1 / 64 : ℝ) = (1 / 8) ^ 2 := by norm_num
          _ ≤ ‖Complex.sin ξ₀‖ ^ 2 := pow_le_pow_left₀ (by norm_num) hsin 2
      linarith
    rw [norm_mul, norm_pow] at h1
    have h4 : ‖Complex.cos ξ₀‖ ^ 2 ≤ 2 := by nlinarith [norm_nonneg (Complex.cos ξ₀)]
    have h5 : ‖1 - Q‖ * ‖Complex.cos ξ₀‖ ^ 2 ≤ ‖1 - Q‖ * 2 :=
      mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    linarith
  have hprod : (B + 2 * S) * (B - 2 * S) = B ^ 2 * (1 - Q) := by linear_combination -hSQ
  have h6 : ‖B‖ ^ 2 * (63 / 8192) ≤ ‖B + 2 * S‖ * (3 * ‖B‖) := by
    have h7 : ‖B + 2 * S‖ * ‖B - 2 * S‖ = ‖B‖ ^ 2 * ‖1 - Q‖ := by
      rw [← norm_mul, hprod, norm_mul, norm_pow]
    have h8 : ‖B - 2 * S‖ ≤ 3 * ‖B‖ := by
      have h9 := norm_sub_le B (2 * S)
      rw [norm_mul, Complex.norm_ofNat] at h9
      linarith
    have h9 : ‖B + 2 * S‖ * ‖B - 2 * S‖ ≤ ‖B + 2 * S‖ * (3 * ‖B‖) :=
      mul_le_mul_of_nonneg_left h8 (norm_nonneg _)
    have h10 : ‖B‖ ^ 2 * (63 / 8192) ≤ ‖B‖ ^ 2 * ‖1 - Q‖ :=
      mul_le_mul_of_nonneg_left h1Q (sq_nonneg _)
    linarith
  have h11 : ‖B‖ * (21 / 8192) ≤ ‖B + 2 * S‖ := by
    by_contra hcon
    push Not at hcon
    have h12 := mul_lt_mul_of_pos_right hcon (by positivity : 0 < 3 * ‖B‖)
    nlinarith
  intro h0
  have e : (0 : ℂ) - B - 2 * S = -(B + 2 * S) := by ring
  rw [h0, e, norm_neg] at hH
  linarith

/-! ## The sign of a continuous square root -/

/-- If `|A² − B²| ≤ ε|B|²` and `Re(A/B) > 0`, then `|A − B| ≤ ε|B|`. -/
theorem norm_sub_le_of_sq {A B : ℂ} {ε : ℝ} (hB : B ≠ 0) (h : ‖A ^ 2 - B ^ 2‖ ≤ ε * ‖B‖ ^ 2)
    (hre : 0 < (A / B).re) : ‖A - B‖ ≤ ε * ‖B‖ := by
  have hBn : 0 < ‖B‖ := norm_pos_iff.mpr hB
  have h1 : ‖B‖ ≤ ‖A + B‖ := by
    have e : A + B = B * (A / B + 1) := by rw [mul_add, mul_div_cancel₀ _ hB, mul_one]
    have h2 : 1 ≤ ‖A / B + 1‖ := by
      have h3 := Complex.re_le_norm (A / B + 1)
      rw [Complex.add_re, Complex.one_re] at h3
      linarith
    rw [e, norm_mul]
    nlinarith
  have h3 : ‖A - B‖ * ‖A + B‖ = ‖A ^ 2 - B ^ 2‖ := by
    rw [← norm_mul]
    congr 1
    ring
  by_contra hcon
  push Not at hcon
  have h4 : ε * ‖B‖ * ‖B‖ < ‖A - B‖ * ‖A + B‖ :=
    calc ε * ‖B‖ * ‖B‖ < ‖A - B‖ * ‖B‖ := mul_lt_mul_of_pos_right hcon hBn
      _ ≤ ‖A - B‖ * ‖A + B‖ := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
  rw [h3] at h4
  nlinarith

/-- **The sign of a continuous square root is constant.** If `A² = (1 + e)B²` along a path with
`|e| ≤ ε ≤ 1/2`, then `A` is near `B` on the whole path or near `−B` on the whole path: the real
part of `A/B` never vanishes. -/
theorem norm_sub_le_or_norm_add_le {A B : ℝ → ℂ} {ε : ℝ} (hA : ContinuousOn A (Icc 0 1))
    (hB : ContinuousOn B (Icc 0 1)) (hB0 : ∀ s ∈ Icc (0 : ℝ) 1, B s ≠ 0) (hε : ε ≤ 1 / 2)
    (h : ∀ s ∈ Icc (0 : ℝ) 1, ‖A s ^ 2 - B s ^ 2‖ ≤ ε * ‖B s‖ ^ 2) :
    (∀ s ∈ Icc (0 : ℝ) 1, ‖A s - B s‖ ≤ ε * ‖B s‖) ∨
      (∀ s ∈ Icc (0 : ℝ) 1, ‖A s + B s‖ ≤ ε * ‖B s‖) := by
  have hg : ContinuousOn (fun s => (A s / B s).re) (Icc 0 1) :=
    Complex.continuous_re.comp_continuousOn (hA.div hB hB0)
  have hne : ∀ s ∈ Icc (0 : ℝ) 1, (A s / B s).re ≠ 0 := by
    intro s hs h0
    have hBn : 0 < ‖B s‖ := norm_pos_iff.mpr (hB0 s hs)
    have hu : ‖(A s / B s) ^ 2 - 1‖ ≤ ε := by
      have e : (A s / B s) ^ 2 - 1 = (A s ^ 2 - B s ^ 2) / B s ^ 2 := by
        rw [div_pow, sub_div, div_self (pow_ne_zero 2 (hB0 s hs))]
      rw [e, norm_div, norm_pow, div_le_iff₀ (by positivity)]
      exact h s hs
    have hre : ((A s / B s) ^ 2 - 1).re = -((A s / B s).im) ^ 2 - 1 := by
      rw [Complex.sub_re, Complex.one_re, sq, Complex.mul_re, h0]
      ring
    have h1 := (abs_le.mp ((Complex.abs_re_le_norm _).trans hu)).1
    rw [hre] at h1
    nlinarith [sq_nonneg (A s / B s).im]
  rcases HTGeometry.sign_const_of_continuousOn_ne_zero zero_le_one hg hne with hpos | hneg
  · exact Or.inl fun s hs => norm_sub_le_of_sq (hB0 s hs) (h s hs) (hpos s hs)
  · refine Or.inr fun s hs => ?_
    have h1 : ‖(-A s) ^ 2 - B s ^ 2‖ ≤ ε * ‖B s‖ ^ 2 := by
      rw [neg_sq]
      exact h s hs
    have h2 : 0 < (-A s / B s).re := by
      rw [neg_div, Complex.neg_re]
      linarith [hneg s hs]
    have h3 := norm_sub_le_of_sq (hB0 s hs) h1 h2
    have e : -A s - B s = -(A s + B s) := by ring
    rwa [e, norm_neg] at h3

/-- A continuous function on `[0, 1]` that starts below `r` and never takes the value `r` ends
below `r`. -/
theorem lt_of_continuousOn_avoid {d : ℝ → ℝ} {r : ℝ} (hd : ContinuousOn d (Icc 0 1))
    (h0 : d 0 < r) (havoid : ∀ s ∈ Icc (0 : ℝ) 1, d s ≠ r) : d 1 < r := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs, hsd⟩ := intermediate_value_Icc zero_le_one hd ⟨h0.le, hcon⟩
  exact havoid s hs hsd

/-! ## Continuity of the two terms along a path of saddles -/

theorem pi_div_mem_slitPlane {w : ℂ} (hw : 0 < w.re) : (π : ℂ) / w ∈ slitPlane := by
  refine Complex.mem_slitPlane_iff.2 (Or.inl ?_)
  have hw0 : w ≠ 0 := fun h => by
    rw [h, Complex.zero_re] at hw
    exact lt_irrefl _ hw
  have hN : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw0
  rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, zero_div, add_zero]
  exact div_pos (mul_pos Real.pi_pos hw) hN

theorem continuous_saddleTime_comp {a : ℝ → ℂ} (ha : Continuous a)
    (hR : ∀ s, SaddleRegion (a s)) : Continuous fun s => saddleTime (a s) := by
  have hP : Continuous fun s => saddleP (a s) :=
    continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul ha))
  exact hP.div ha fun s => (hR s).ne_zero

theorem continuous_bulkTerm_comp {a : ℝ → ℂ} (ha : Continuous a)
    (hR : ∀ s, SaddleRegion (a s)) : Continuous fun s => bulkTerm (a s) := by
  have hτ := continuous_saddleTime_comp ha hR
  have hτ0 : ∀ s, saddleTime (a s) ≠ 0 := fun s h0 => by
    have h1 := (hR s).time_re_pos
    rw [h0, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  have h1 : Continuous fun s => ((π : ℂ) / saddleTime (a s)) ^ (1 / 2 : ℂ) :=
    (continuous_const.div hτ hτ0).cpow continuous_const
      fun s => pi_div_mem_slitPlane (hR s).time_re_pos
  exact continuous_const.mul h1

theorem continuous_saddleTerm_comp {a : ℝ → ℂ} (ha : Continuous a)
    (hR : ∀ s, SaddleRegion (a s)) : Continuous fun s => saddleTerm (a s) := by
  have hP : Continuous fun s => saddleP (a s) :=
    continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul ha))
  have hτ := continuous_saddleTime_comp ha hR
  have hf : Continuous fun s => saddlePhaseValue (a s) := hP.mul (ha.sub continuous_const)
  have hlam : ∀ s, 0 < (2 * saddleP (a s) - saddleTime (a s)).re := by
    intro s
    have e : (2 * saddleP (a s) - saddleTime (a s)).re =
        2 * (saddleP (a s)).re - (saddleTime (a s)).re := by simp
    rw [e]
    linarith [(hR s).time_re_le, (hR s).P_re_ge]
  have hlam0 : ∀ s, 2 * saddleP (a s) - saddleTime (a s) ≠ 0 := fun s h0 => by
    have h1 := hlam s
    rw [h0, Complex.zero_re] at h1
    exact lt_irrefl _ h1
  have h1 : Continuous fun s =>
      ((π : ℂ) / (2 * saddleP (a s) - saddleTime (a s))) ^ (1 / 2 : ℂ) :=
    (continuous_const.div ((continuous_const.mul hP).sub hτ) hlam0).cpow continuous_const
      fun s => pi_div_mem_slitPlane (hlam s)
  have h2 : Continuous fun s => cexp (9 * a s / 2 + saddlePhaseValue (a s)) :=
    Complex.continuous_exp.comp (((continuous_const.mul ha).div_const _).add hf)
  exact (continuous_const.mul h2).mul h1

/-- On the saddle region the time has real part at least `Re a`. -/
theorem re_le_saddleTime_re {a : ℂ} (h : SaddleRegion a) : a.re ≤ (saddleTime a).re := by
  have hσ := h.re_pos
  have h1 := h.le_time_re
  have h2 := two_thirds_pow_le_exp hσ.le
  have hπ := Real.pi_gt_three
  refine le_trans ?_ h1
  rw [le_div_iff₀ (by positivity)]
  have h3 : 8 * a.re ^ 3 ≤ 2 * a.re ^ 4 := by
    nlinarith [mul_nonneg (pow_pos hσ 3).le (by linarith [h.1] : (0 : ℝ) ≤ a.re - 4)]
  have h4 := mul_le_mul_of_nonneg_right hπ.le (Real.exp_pos (2 * a.re)).le
  have e : a.re * (8 * a.re ^ 2) = 8 * a.re ^ 3 := by ring
  rw [e]
  linarith

/-! ## Loops of saddles on which the model holds -/

/-- A closed loop of saddles `a(s)` in the saddle region, with times of real part beyond `T`, on
which the heat family is the model up to the relative error `1/16384` and the squared ratio of
the two terms follows `1/cos² ξ₀(s)`. -/
structure IsModelLoop (T : ℝ) (a : ℝ → ℂ) : Prop where
  continuous : Continuous a
  closed : a 1 = a 0
  region : ∀ s, SaddleRegion (a s)
  far : ∀ s, T < (saddleTime (a s)).re
  ratio : ∀ s, ‖saddleRatioSq (a s) * Complex.cos (turnPoint s) ^ 2 - 1‖ ≤ 1 / 4096
  model : ∀ s (ζ : ℂ), ‖ζ‖ ≤ 8 →
    ‖complexHeat (saddleTime (a s)) (ζ / a s) - bulkTerm (a s) -
        2 * saddleTerm (a s) * Complex.cos ζ‖ ≤
      1 / 16384 * (‖bulkTerm (a s)‖ + ‖saddleTerm (a s)‖)

/-- **Model loops exist** with times of arbitrarily large real part. -/
theorem exists_isModelLoop (T : ℝ) : ∃ a : ℝ → ℂ, IsModelLoop T a := by
  obtain ⟨σ₀, hmodel⟩ :=
    exists_forall_norm_complexHeat_sub_model_le (ε := 1 / 16384) (by norm_num)
  obtain ⟨a₁, hloop⟩ := exists_loopSaddle (max σ₀ (T + 1))
  refine ⟨loopSaddle a₁, continuous_loopSaddle a₁, loopSaddle_one a₁, fun s => (hloop s).1,
    fun s => ?_, fun s => (hloop s).2.2,
    fun s ζ hζ => hmodel _ (hloop s).1 ((le_max_left _ _).trans (hloop s).2.1) ζ hζ⟩
  have h1 := re_le_saddleTime_re (hloop s).1
  have h2 := (le_max_right σ₀ (T + 1)).trans (hloop s).2.1
  linarith

namespace IsModelLoop

variable {T : ℝ} {a : ℝ → ℂ}

theorem sq_eq (h : IsModelLoop T a) (s : ℝ) :
    (2 * saddleTerm (a s)) ^ 2 = saddleRatioSq (a s) * bulkTerm (a s) ^ 2 := by
  refine two_mul_saddleTerm_sq (h.region s).ne_zero fun h0 => ?_
  have hre : (2 * a s - 1).re = 2 * (a s).re - 1 := by simp
  rw [h0, Complex.zero_re] at hre
  linarith [(h.region s).1]

theorem bulkTerm_ne_zero (h : IsModelLoop T a) (s : ℝ) : bulkTerm (a s) ≠ 0 := by
  have h1 := (h.region s).le_norm_bulkTerm
  have h2 : 0 < ‖kernelC 0‖ * Real.exp (-(a s).re) :=
    mul_pos (norm_pos_iff.mpr kernelC_zero_ne_zero) (Real.exp_pos _)
  exact norm_pos_iff.mp (lt_of_lt_of_le h2 h1)

theorem norm_saddleTerm_le (h : IsModelLoop T a) (s : ℝ) :
    ‖saddleTerm (a s)‖ ≤ ‖bulkTerm (a s)‖ :=
  norm_saddle_le_norm_bulk (norm_cos_turnPoint_bounds s).1 (h.ratio s) (h.sq_eq s)

/-- The model with the error `|B₀|/8192`. -/
theorem model' (h : IsModelLoop T a) (s : ℝ) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 8) :
    ‖complexHeat (saddleTime (a s)) (ζ / a s) - bulkTerm (a s) -
        2 * saddleTerm (a s) * Complex.cos ζ‖ ≤ ‖bulkTerm (a s)‖ / 8192 := by
  have h1 := h.model s ζ hζ
  have h2 := h.norm_saddleTerm_le s
  linarith

/-- The centre is not a zero at any time of the loop. -/
theorem centre_ne_zero (h : IsModelLoop T a) (s : ℝ) : complexHeat (saddleTime (a s)) 0 ≠ 0 := by
  have h1 := h.model' s (ζ := 0) (by rw [norm_zero]; norm_num)
  rw [zero_div, Complex.cos_zero, mul_one] at h1
  exact ne_zero_at_centre (h.bulkTerm_ne_zero s) (norm_turnPoint s) (h.ratio s) (h.sq_eq s) h1

/-- **The centre of the turn.** With `θ = π` or `θ = 2π`, the model `B₀ + 2S₀ cos ζ` nearly
vanishes at `ζ = θ + ξ₀(s)` for every `s`: the sign of `2S₀ cos ξ₀/B₀` is constant on the loop. -/
theorem exists_turn (h : IsModelLoop T a) :
    ∃ θ : ℂ, Complex.sin θ = 0 ∧ π ≤ ‖θ‖ ∧ ‖θ‖ ≤ 2 * π ∧ ∀ s ∈ Icc (0 : ℝ) 1,
      ‖2 * saddleTerm (a s) * Complex.cos θ * Complex.cos (turnPoint s) + bulkTerm (a s)‖ ≤
        ‖bulkTerm (a s)‖ / 4096 := by
  have hπ := Real.pi_pos
  have hAc : ContinuousOn (fun s => 2 * saddleTerm (a s) * Complex.cos (turnPoint s))
      (Icc 0 1) :=
    ((continuous_const.mul (continuous_saddleTerm_comp h.continuous h.region)).mul
      (Complex.continuous_cos.comp continuous_turnPoint)).continuousOn
  have hBc : ContinuousOn (fun s => bulkTerm (a s)) (Icc 0 1) :=
    (continuous_bulkTerm_comp h.continuous h.region).continuousOn
  have hsq : ∀ s ∈ Icc (0 : ℝ) 1,
      ‖(2 * saddleTerm (a s) * Complex.cos (turnPoint s)) ^ 2 - bulkTerm (a s) ^ 2‖ ≤
        1 / 4096 * ‖bulkTerm (a s)‖ ^ 2 := by
    intro s _
    have e : (2 * saddleTerm (a s) * Complex.cos (turnPoint s)) ^ 2 - bulkTerm (a s) ^ 2 =
        bulkTerm (a s) ^ 2 * (saddleRatioSq (a s) * Complex.cos (turnPoint s) ^ 2 - 1) := by
      rw [mul_pow, h.sq_eq s]
      ring
    rw [e, norm_mul, norm_pow]
    calc ‖bulkTerm (a s)‖ ^ 2 * ‖saddleRatioSq (a s) * Complex.cos (turnPoint s) ^ 2 - 1‖
        ≤ ‖bulkTerm (a s)‖ ^ 2 * (1 / 4096) :=
          mul_le_mul_of_nonneg_left (h.ratio s) (sq_nonneg _)
      _ = 1 / 4096 * ‖bulkTerm (a s)‖ ^ 2 := mul_comm _ _
  have hnπ : ‖(π : ℂ)‖ = π := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hπ]
  rcases norm_sub_le_or_norm_add_le hAc hBc (fun s _ => h.bulkTerm_ne_zero s) (by norm_num) hsq
    with hc | hc
  · refine ⟨π, Complex.sin_pi, hnπ.ge, by rw [hnπ]; linarith, fun s hs => ?_⟩
    have h1 : ‖2 * saddleTerm (a s) * Complex.cos (turnPoint s) - bulkTerm (a s)‖ ≤
        1 / 4096 * ‖bulkTerm (a s)‖ := hc s hs
    have e : 2 * saddleTerm (a s) * Complex.cos π * Complex.cos (turnPoint s) + bulkTerm (a s) =
        -(2 * saddleTerm (a s) * Complex.cos (turnPoint s) - bulkTerm (a s)) := by
      rw [Complex.cos_pi]
      ring
    rw [e, norm_neg]
    linarith
  · refine ⟨2 * π, Complex.sin_two_pi, ?_, ?_, fun s hs => ?_⟩
    · rw [norm_mul, Complex.norm_ofNat, hnπ]
      linarith
    · rw [norm_mul, Complex.norm_ofNat, hnπ]
    · have h1 : ‖2 * saddleTerm (a s) * Complex.cos (turnPoint s) + bulkTerm (a s)‖ ≤
          1 / 4096 * ‖bulkTerm (a s)‖ := hc s hs
      rw [Complex.cos_two_pi, mul_one]
      linarith

/-- **A model loop gives a collision away from the centre**, at a time of real part beyond
`max T 0`. -/
theorem exists_multipleZero (h : IsModelLoop T a) :
    ∃ τ ζ : ℂ, max T 0 < τ.re ∧ ζ ≠ 0 ∧ complexHeat τ ζ = 0 ∧
      deriv (complexHeat τ) ζ = 0 := by
  have hfar : ∀ s, max T 0 < (saddleTime (a s)).re := fun s =>
    max_lt (h.far s) (h.region s).time_re_pos
  by_cases hbr : ∃ s ∈ Icc (0 : ℝ) 1, saddleTime (a s) ∈ branchTimes
  · -- a branch time on the loop: its multiple zero is not the centre
    obtain ⟨s, -, ⟨τ', ζ⟩, ⟨h0, hd⟩, hτ'⟩ := hbr
    have hτ'' : τ' = saddleTime (a s) := hτ'
    subst hτ''
    refine ⟨saddleTime (a s), ζ, hfar s, ?_, h0, hd⟩
    rintro rfl
    exact h.centre_ne_zero s h0
  · -- a forward loop
    push Not at hbr
    have hγ : IsForwardPath fun s => saddleTime (a s) :=
      ⟨(continuous_saddleTime_comp h.continuous h.region).continuousOn,
        fun s _ => (h.region s).time_re_pos, hbr⟩
    have hclosed : (fun s => saddleTime (a s)) 1 = (fun s => saddleTime (a s)) 0 := by
      show saddleTime (a 1) = saddleTime (a 0)
      rw [h.closed]
    obtain ⟨θ, hsinθ, hθlo, hθhi, hE⟩ := h.exists_turn
    have hπ4 := Real.pi_lt_d2
    -- no zero on the circles around `θ + ξ₀(s)`
    have hcircle : ∀ s ∈ Icc (0 : ℝ) 1, ∀ ξ : ℂ, ‖ξ - turnPoint s‖ = 1 / 16 →
        ‖bulkTerm (a s)‖ * (9 / 8192) ≤ ‖complexHeat (saddleTime (a s)) ((θ + ξ) / a s)‖ := by
      intro s hs ξ hξ
      have hζ : ‖θ + ξ‖ ≤ 8 := by
        have h1 := norm_add_le θ ξ
        have h2 := norm_add_le (ξ - turnPoint s) (turnPoint s)
        rw [sub_add_cancel, norm_turnPoint, hξ] at h2
        linarith
      exact le_norm_of_mem_annulus hsinθ (norm_turnPoint s) (hE s hs) (h.model' s hζ) hξ.ge
        (hξ.le.trans (by norm_num))
    -- a zero in the first disc
    have ha0 := (h.region 0).ne_zero
    have han : 0 < ‖a 0‖ := norm_pos_iff.mpr ha0
    have hBn : 0 < ‖bulkTerm (a 0)‖ := norm_pos_iff.mpr (h.bulkTerm_ne_zero 0)
    have h01 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
    obtain ⟨z₀, hz₀d, hz₀⟩ : ∃ z₀ : ℂ, ‖a 0 * z₀ - θ - turnPoint 0‖ < 1 / 16 ∧
        complexHeat (saddleTime (a 0)) z₀ = 0 := by
      have hζ0 : ‖θ + turnPoint 0‖ ≤ 8 := by
        have h1 := norm_add_le θ (turnPoint 0)
        rw [norm_turnPoint] at h1
        linarith
      have hcen : ‖complexHeat (saddleTime (a 0)) ((θ + turnPoint 0) / a 0)‖ <
          ‖bulkTerm (a 0)‖ * (9 / 8192) := by
        have h1 := norm_le_at_turnPoint hsinθ (hE 0 h01) (h.model' 0 hζ0)
        linarith
      have hshift : ∀ z : ℂ, a 0 * z - θ - turnPoint 0 =
          a 0 * (z - (θ + turnPoint 0) / a 0) := by
        intro z
        rw [mul_sub, mul_div_cancel₀ _ ha0]
        ring
      obtain ⟨z₀, hz₀r, hz₀⟩ := RigidArithmeticOfCuts.exists_zero_of_norm_center_lt
        (differentiable_complexHeat (saddleTime (a 0))) (c := (θ + turnPoint 0) / a 0)
        (r := 1 / 16 / ‖a 0‖) (μ := ‖bulkTerm (a 0)‖ * (9 / 8192))
        (div_pos (by norm_num) han) (mul_pos hBn (by norm_num)) hcen (by
          intro z hz
          have hξ : ‖a 0 * z - θ - turnPoint 0‖ = 1 / 16 := by
            rw [hshift, norm_mul, hz, mul_div_cancel₀ _ han.ne']
          have e : (θ + (a 0 * z - θ)) / a 0 = z := by
            rw [add_sub_cancel, mul_div_cancel_left₀ _ ha0]
          have h1 := hcircle 0 h01 (a 0 * z - θ) hξ
          rwa [e] at h1)
      refine ⟨z₀, ?_, hz₀⟩
      rw [hshift, norm_mul]
      rw [lt_div_iff₀ han] at hz₀r
      linarith [mul_comm ‖a 0‖ ‖z₀ - (θ + turnPoint 0) / a 0‖]
    -- its lift follows the centres of the discs
    obtain ⟨z, hz, hz0⟩ := exists_isZeroLift_of_re_pos (γ := fun s => saddleTime (a s))
      hγ.continuousOn hγ.re_pos hγ.simple (z₀ := z₀) hz₀
    have hmc : ContinuousOn (fun s => ‖a s * z s - θ - turnPoint s‖) (Icc 0 1) :=
      (((h.continuous.continuousOn.mul hz.continuousOn).sub continuousOn_const).sub
        continuous_turnPoint.continuousOn).norm
    have havoid : ∀ s ∈ Icc (0 : ℝ) 1, ‖a s * z s - θ - turnPoint s‖ ≠ 1 / 16 := by
      intro s hs hd
      have has := (h.region s).ne_zero
      have e : (θ + (a s * z s - θ)) / a s = z s := by
        rw [add_sub_cancel, mul_div_cancel_left₀ _ has]
      have h1 := hcircle s hs (a s * z s - θ) hd
      rw [e] at h1
      have h2 : complexHeat (saddleTime (a s)) (z s) = 0 := hz.zero s hs
      rw [h2, norm_zero] at h1
      have h3 : 0 < ‖bulkTerm (a s)‖ := norm_pos_iff.mpr (h.bulkTerm_ne_zero s)
      linarith
    have hd1 : ‖a 1 * z 1 - θ - turnPoint 1‖ < 1 / 16 :=
      lt_of_continuousOn_avoid hmc (by
        show ‖a 0 * z 0 - θ - turnPoint 0‖ < 1 / 16
        rw [hz0]
        exact hz₀d) havoid
    rw [h.closed, turnPoint_one] at hd1
    rw [turnPoint_zero] at hz₀d
    -- the zero is carried outside its pair
    have hT : Transports (fun s => saddleTime (a s)) z₀ (z 1) := ⟨z, hz, hz0, rfl⟩
    have hne1 : z 1 ≠ z₀ := by
      intro he
      rw [he] at hd1
      have h1 := norm_sub_le (a 0 * z₀ - θ - -(1 / 4)) (a 0 * z₀ - θ - 1 / 4)
      have e : a 0 * z₀ - θ - -(1 / 4) - (a 0 * z₀ - θ - 1 / 4) = (1 / 2 : ℂ) := by ring
      have h2 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by
        rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (by norm_num)]
      rw [e, h2] at h1
      linarith
    have hne2 : z 1 ≠ -z₀ := by
      intro he
      rw [he] at hd1
      have h1 := norm_add_le (a 0 * -z₀ - θ - -(1 / 4)) (a 0 * z₀ - θ - 1 / 4)
      have e : a 0 * -z₀ - θ - -(1 / 4) + (a 0 * z₀ - θ - 1 / 4) = -(2 * θ) := by ring
      rw [e, norm_neg, norm_mul, Complex.norm_ofNat] at h1
      linarith [Real.pi_gt_three]
    obtain ⟨τ, hτ, ζ, hζ, h0, hd⟩ := exists_multipleZero_ne_zero_of_transports
      (convex_halfSpace_re_gt (max T 0)) (isOpen_lt continuous_const Complex.continuous_re)
      (fun _ hτ => lt_of_le_of_lt (le_max_right T 0) hτ) hγ hclosed (fun s _ => hfar s) hT
      hne1 hne2
    exact ⟨τ, ζ, hτ, hζ, h0, hd⟩

end IsModelLoop

/-! ## The collision and the forward monodromy group -/

/-- **A collision away from the centre exists at forward times of arbitrarily large real
part.** For every `T` there are `τ` with `Re τ > max T 0` and `ζ ≠ 0` such that `ζ` is a multiple
zero of `H_τ`. -/
theorem exists_forward_multipleZero_ne_zero (T : ℝ) :
    ∃ τ ζ : ℂ, max T 0 < τ.re ∧ ζ ≠ 0 ∧ complexHeat τ ζ = 0 ∧
      deriv (complexHeat τ) ζ = 0 := by
  obtain ⟨a, ha⟩ := exists_isModelLoop T
  exact ha.exists_multipleZero

/-- **The forward monodromy group moves a zero outside its pair.** At every forward base time
off the branch times the group has an element `σ` and the fibre a zero `p` with `σp ≠ p` and
`σp ≠ −p`. -/
theorem exists_mem_forwardMonodromy_moving_a_pair {b : ℂ} (hb₀ : 0 < b.re)
    (hb : b ∉ branchTimes) :
    ∃ σ ∈ forwardMonodromy b hb₀ hb, ∃ p : {w : ℂ // complexHeat b w = 0},
      σ p ≠ p ∧ σ p ≠ fibreNeg b p := by
  obtain ⟨τ, ζ, hτ, hζ, h0, hd⟩ := exists_forward_multipleZero_ne_zero 0
  exact exists_mem_forwardMonodromy_moving_pair (lt_of_le_of_lt (le_max_right 0 0) hτ) h0 hd hζ
    hb₀ hb

/-- **The forward monodromy group is not a group of sign changes.** -/
theorem not_forwardMonodromy_preserves_pairs {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes) :
    ¬ ∀ σ ∈ forwardMonodromy b hb₀ hb, ∀ q, σ q = q ∨ σ q = fibreNeg b q := by
  intro h
  obtain ⟨σ, hσ, p, h1, h2⟩ := exists_mem_forwardMonodromy_moving_a_pair hb₀ hb
  rcases h σ hσ p with h3 | h3
  · exact h1 h3
  · exact h2 h3

end

end GaloisForLFunctions.GaloisTheoryOfZeros
