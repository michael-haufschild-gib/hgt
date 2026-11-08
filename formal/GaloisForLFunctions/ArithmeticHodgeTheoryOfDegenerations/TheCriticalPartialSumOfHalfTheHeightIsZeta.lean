import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePartialZetaSumIsQuietBelowItsGrid

/-!
# The critical partial sum of half the height is `ζ` on the line

On the critical line, below the grid `|b| ≤ πM`, the partial sum `S_M(b) = Σ_{k≤M} k^{−½−ib}` is
`ζ(½ + ib)` up to `9 M^{−½} + M^{½}/|b|` (`norm_criticalPartialSum_sub_zeta_le`, from the strip
error bound `norm_zetaStripError_le_grid`). For the adaptive length `M(b) = ⌈|b|/2⌉ + B` of the
theta head, a partial sum of half the height, the error is `(9√2 + √(1 + 2(B+1))) |b|^{−½}` for
`|b| ≥ 1` (`norm_adaptivePartialSum_sub_zeta_le`), and the squares differ by the same error times
`2|ζ(½ + ib)| + error` (`abs_normSq_adaptivePartialSum_sub_le`).

So the leading term of the adaptive head is `|ζ(½ + ib)|²` up to `O(|ζ(½ + ib)| |b|^{−½} + |b|^{−1})`.
-/

noncomputable section

open Finset Complex

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

/-- The critical partial sum `Σ_{k≤M} k^{−½−ib}`. -/
def criticalPartialSum (M : ℕ) (b : ℝ) : ℂ :=
  ∑ k ∈ Icc 1 M, ((k : ℝ) : ℂ) ^ (-((1 / 2 : ℂ) + (b : ℂ) * I))

/-- **Below the grid the critical partial sum is `ζ` on the line.** -/
theorem norm_criticalPartialSum_sub_zeta_le {b : ℝ} (hb : b ≠ 0) {M : ℕ} (hM : 1 ≤ M)
    (hbM : |b| ≤ Real.pi * M) :
    ‖criticalPartialSum M b - riemannZeta ((1 / 2 : ℂ) + (b : ℂ) * I)‖ ≤
      9 * (M : ℝ) ^ (-(1 / 2 : ℝ)) + (M : ℝ) ^ (1 / 2 : ℝ) / |b| := by
  set w : ℂ := (1 / 2 : ℂ) + (b : ℂ) * I with hw
  have hwre : w.re = 1 / 2 := by simp [hw]
  have hwim : w.im = b := by simp [hw]
  have hw1 : w ≠ 1 := fun h => by
    have := congrArg Complex.im h
    rw [hwim, one_im] at this
    exact hb this
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hE := norm_zetaStripError_le_grid (w := w) (by rw [hwre]; norm_num) hw1 hM
    (by rw [hwim]; exact hbM)
  rw [hwre] at hE
  have hsplit : criticalPartialSum M b - riemannZeta w =
      ((M : ℝ) : ℂ) ^ (1 - w) / (1 - w) + RHTower.zetaStripError w M := by
    rw [criticalPartialSum, ← hw, RHTower.sum_cpow_eq_zetaStripError]; ring
  rw [hsplit]
  -- the pole term: `|M^{1−w}| = M^{½}`, `|1 − w| ≥ |b|`
  have hnum : ‖((M : ℝ) : ℂ) ^ (1 - w)‖ = (M : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hM0]
    congr 1
    simp [hw]; norm_num
  have hden : |b| ≤ ‖1 - w‖ := by
    have := Complex.abs_im_le_norm (1 - w)
    simpa [hw] using this
  have hb0 : 0 < |b| := abs_pos.mpr hb
  have hpole : ‖((M : ℝ) : ℂ) ^ (1 - w) / (1 - w)‖ ≤ (M : ℝ) ^ (1 / 2 : ℝ) / |b| := by
    rw [norm_div, hnum]
    exact div_le_div_of_nonneg_left (by positivity) hb0 hden
  calc ‖((M : ℝ) : ℂ) ^ (1 - w) / (1 - w) + RHTower.zetaStripError w M‖
      ≤ ‖((M : ℝ) : ℂ) ^ (1 - w) / (1 - w)‖ + ‖RHTower.zetaStripError w M‖ := norm_add_le _ _
    _ ≤ (M : ℝ) ^ (1 / 2 : ℝ) / |b| + 9 * (M : ℝ) ^ (-(1 / 2 : ℝ)) := add_le_add hpole hE
    _ = _ := add_comm _ _

/-- The adaptive length `M(b) = ⌈|b|/2⌉ + B`. -/
def adaptiveLength (B : ℕ) (b : ℝ) : ℕ := ⌈|b| / 2⌉₊ + B

/-- **The adaptive partial sum is `ζ` on the line up to `O(|b|^{−½})`.** -/
theorem norm_adaptivePartialSum_sub_zeta_le (B : ℕ) {b : ℝ} (hb : 1 ≤ |b|) :
    ‖criticalPartialSum (adaptiveLength B b) b - riemannZeta ((1 / 2 : ℂ) + (b : ℂ) * I)‖ ≤
      (9 * Real.sqrt 2 + Real.sqrt (1 + 2 * ((B : ℝ) + 1))) * |b| ^ (-(1 / 2 : ℝ)) := by
  set M := adaptiveLength B b with hMdef
  have hb0 : 0 < |b| := by linarith
  have hbne : b ≠ 0 := abs_pos.mp hb0
  have hMlow : |b| / 2 ≤ (M : ℝ) := by
    rw [hMdef, adaptiveLength]; push_cast
    linarith [Nat.le_ceil (|b| / 2), (Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hMup : (M : ℝ) ≤ |b| / 2 + (B + 1) := by
    rw [hMdef, adaptiveLength]; push_cast
    linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ |b| / 2)]
  have hM1 : 1 ≤ M := by
    have : (0 : ℝ) < M := by linarith
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro h; rw [h] at this; simp at this)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  have hgrid : |b| ≤ Real.pi * M := by nlinarith [Real.pi_gt_three]
  refine (norm_criticalPartialSum_sub_zeta_le hbne hM1 hgrid).trans ?_
  -- `M^{−½} ≤ √2 |b|^{−½}` and `M^{½}/|b| ≤ √(1 + 2(B+1)) |b|^{−½}`
  have h1 : (M : ℝ) ^ (-(1 / 2 : ℝ)) ≤ Real.sqrt 2 * |b| ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hM0.le, Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    rw [← div_eq_mul_inv, le_div_iff₀ (Real.sqrt_pos.mpr hb0), inv_mul_eq_div,
      div_le_iff₀ (Real.sqrt_pos.mpr hM0), ← Real.sqrt_mul (by norm_num)]
    calc Real.sqrt |b| ≤ Real.sqrt (2 * M) := Real.sqrt_le_sqrt (by linarith)
      _ = 1 * Real.sqrt (2 * M) := (one_mul _).symm
  have h2 : (M : ℝ) ^ (1 / 2 : ℝ) / |b| ≤
      Real.sqrt (1 + 2 * ((B : ℝ) + 1)) * |b| ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hb0.le, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← div_eq_mul_inv,
      div_le_div_iff₀ hb0 (Real.sqrt_pos.mpr hb0)]
    have hsb : Real.sqrt |b| * Real.sqrt |b| = |b| := Real.mul_self_sqrt hb0.le
    rw [← Real.sqrt_mul hM0.le, ← Real.sqrt_mul (by positivity), ← hsb, ← Real.sqrt_mul hb0.le,
      ← Real.sqrt_mul (by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have hb1 : (1 : ℝ) ≤ |b| := hb
    nlinarith [mul_le_mul_of_nonneg_left hMup hb0.le]
  nlinarith [h1, h2]

/-- **The squares agree to the same error.** -/
theorem abs_normSq_adaptivePartialSum_sub_le (B : ℕ) {b : ℝ} (hb : 1 ≤ |b|) :
    |‖criticalPartialSum (adaptiveLength B b) b‖ ^ 2 - ‖riemannZeta ((1 / 2 : ℂ) + (b : ℂ) * I)‖ ^ 2| ≤
      (9 * Real.sqrt 2 + Real.sqrt (1 + 2 * ((B : ℝ) + 1))) * |b| ^ (-(1 / 2 : ℝ)) *
        (2 * ‖riemannZeta ((1 / 2 : ℂ) + (b : ℂ) * I)‖ +
          (9 * Real.sqrt 2 + Real.sqrt (1 + 2 * ((B : ℝ) + 1))) * |b| ^ (-(1 / 2 : ℝ))) := by
  set S := criticalPartialSum (adaptiveLength B b) b
  set Z := riemannZeta ((1 / 2 : ℂ) + (b : ℂ) * I)
  set E := (9 * Real.sqrt 2 + Real.sqrt (1 + 2 * ((B : ℝ) + 1))) * |b| ^ (-(1 / 2 : ℝ))
  have hSZ : ‖S - Z‖ ≤ E := norm_adaptivePartialSum_sub_zeta_le B hb
  have hdiff : |‖S‖ - ‖Z‖| ≤ E := (abs_norm_sub_norm_le S Z).trans hSZ
  have hsum : ‖S‖ + ‖Z‖ ≤ 2 * ‖Z‖ + E := by
    have := (abs_le.mp hdiff).2
    linarith
  rw [show ‖S‖ ^ 2 - ‖Z‖ ^ 2 = (‖S‖ - ‖Z‖) * (‖S‖ + ‖Z‖) by ring, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ ‖S‖ + ‖Z‖)]
  exact mul_le_mul hdiff hsum (by positivity) ((abs_nonneg _).trans hdiff)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
