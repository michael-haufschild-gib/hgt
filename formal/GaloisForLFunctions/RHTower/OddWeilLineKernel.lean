import GaloisForLFunctions.RHTower.SquareRootNevanlinnaTransfer

/-!
# The Nevanlinna kernel of the odd Weil function on the line `Re w = 5/4`

For a circle point `ζ` and `w = ½ + a` put `K_ζ(w) = i K(½ − i a², ζ)/a`, where `K` is the
Herglotz–Riesz kernel of the half-plane chart (`oddLineKernel`).  On the line `w = 5/4 + it`
(`linePt`), `a = ¾ + it` (`lineA`), and for `ζ ≠ 1` with ordinate `γ = circleOrd ζ`,
`K_ζ(w) = ((γ a² − 1)/(a² + γ))/a` (`oddLineKernel_eq`), while `K_1(w) = a`.

The kernel has real coefficients, `K_ζ(w̄) = conj K_ζ(w)` (`oddLineKernel_neg`), and on the
support `{ζ = 1} ∪ {γ ≥ −¼}` it is bounded by `44 (1 + t²)` (`norm_oddLineKernel_le`): the
denominator satisfies `|a² + γ| ≥ 3|t|/2`, and `|a² + γ| ≥ 1/16` when `|t| ≤ ½`, while
`γ a² − 1 = (a² + γ) a² − a⁴ − 1`.
-/

open Complex Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower.OddResolvent

open RHTower.AtomDomination

/-! ## The line -/

/-- The point `5/4 + it` of the line `Re w = 5/4`. -/
def linePt (t : ℝ) : ℂ := (5 / 4 : ℂ) + t * I

/-- `a = w − ½ = ¾ + it`. -/
def lineA (t : ℝ) : ℂ := (3 / 4 : ℂ) + t * I

theorem linePt_sub_half (t : ℝ) : linePt t - 1 / 2 = lineA t := by
  unfold linePt lineA; ring

theorem linePt_neg (t : ℝ) : linePt (-t) = conj (linePt t) := by
  unfold linePt
  apply Complex.ext <;> simp [map_ofNat]

theorem lineA_neg (t : ℝ) : lineA (-t) = conj (lineA t) := by
  unfold lineA
  apply Complex.ext <;> simp [map_ofNat]

theorem lineA_re (t : ℝ) : (lineA t).re = 3 / 4 := by simp [lineA]

theorem lineA_im (t : ℝ) : (lineA t).im = t := by simp [lineA]

theorem lineA_sq_re (t : ℝ) : (lineA t ^ 2).re = 9 / 16 - t ^ 2 := by
  simp [lineA, pow_two, Complex.mul_re]; ring

theorem lineA_sq_im (t : ℝ) : (lineA t ^ 2).im = 3 / 2 * t := by
  simp [lineA, pow_two, Complex.mul_im]; ring

theorem lineA_ne_zero (t : ℝ) : lineA t ≠ 0 := by
  intro h
  have := congrArg Complex.re h
  rw [lineA_re] at this
  norm_num at this

theorem normSq_lineA (t : ℝ) : Complex.normSq (lineA t) = 9 / 16 + t ^ 2 := by
  rw [Complex.normSq_apply, lineA_re, lineA_im]; ring

theorem norm_lineA_sq (t : ℝ) : ‖lineA t‖ ^ 2 = 9 / 16 + t ^ 2 := by
  rw [Complex.sq_norm, normSq_lineA]

theorem norm_lineA_ge (t : ℝ) : 3 / 4 ≤ ‖lineA t‖ := by
  have := Complex.abs_re_le_norm (lineA t)
  rw [lineA_re, abs_of_pos (by norm_num)] at this
  exact this

theorem abs_le_norm_lineA (t : ℝ) : |t| ≤ ‖lineA t‖ := by
  have := Complex.abs_im_le_norm (lineA t)
  rwa [lineA_im] at this

theorem norm_lineA_le (t : ℝ) : ‖lineA t‖ ≤ 1 + |t| := by
  unfold lineA
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have : ‖(3 / 4 : ℂ)‖ ≤ 1 := by norm_num
  linarith

/-- The chart point `½ − i a²` of a line point has `2s + 1 ≠ 0`. -/
theorem two_mul_chart_add_one_ne_zero (t : ℝ) : 2 * (1 / 2 - I * lineA t ^ 2) + 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.I_re, Complex.I_im,
    Complex.add_im, Complex.mul_im, Complex.sub_im, lineA_sq_re, lineA_sq_im] at hre him
  norm_num at hre him
  nlinarith [sq_nonneg t]

/-- `a² + γ ≠ 0` on the line off `t = 0`. -/
theorem lineA_sq_add_ne_zero {t : ℝ} (ht : t ≠ 0) (γ : ℝ) : lineA t ^ 2 + (γ : ℂ) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, lineA_sq_im, Complex.ofReal_im, add_zero, Complex.zero_im] at him
  exact ht (by linarith)

theorem norm_lineA_sq_add_ge_im (t γ : ℝ) : 3 / 2 * |t| ≤ ‖lineA t ^ 2 + (γ : ℂ)‖ := by
  have := Complex.abs_im_le_norm (lineA t ^ 2 + (γ : ℂ))
  rw [Complex.add_im, lineA_sq_im, Complex.ofReal_im, add_zero, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)] at this
  exact this

theorem norm_lineA_sq_add_ge_re {t γ : ℝ} (ht : |t| ≤ 1 / 2) (hγ : -(1 / 4) ≤ γ) :
    1 / 16 ≤ ‖lineA t ^ 2 + (γ : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (lineA t ^ 2 + (γ : ℂ))
  rw [Complex.add_re, lineA_sq_re, Complex.ofReal_re] at h
  have ht2 : t ^ 2 ≤ 1 / 4 := by
    have := abs_le.mp ht
    nlinarith
  have : 1 / 16 ≤ 9 / 16 - t ^ 2 + γ := by linarith
  exact this.trans ((le_abs_self _).trans h)

/-! ## The kernel -/

/-- `K_ζ(w) = i K(½ − i(w − ½)², ζ)/(w − ½)`. -/
def oddLineKernel (ζ w : ℂ) : ℂ := I * hrKernel (1 / 2 - I * (w - 1 / 2) ^ 2) ζ / (w - 1 / 2)

theorem oddLineKernel_one (t : ℝ) : oddLineKernel 1 (linePt t) = lineA t := by
  unfold oddLineKernel
  rw [linePt_sub_half, I_mul_hrKernel_one (two_mul_chart_add_one_ne_zero t), pow_two]
  exact mul_div_cancel_right₀ _ (lineA_ne_zero t)

/-- The rational form `K_ζ(w) = ((γ a² − 1)/(a² + γ))/a` for `ζ ≠ 1` and `t ≠ 0`. -/
theorem oddLineKernel_eq {t : ℝ} (ht : t ≠ 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (h1 : ζ ≠ 1) :
    oddLineKernel ζ (linePt t) =
      (((circleOrd ζ : ℂ) * lineA t ^ 2 - 1) / (lineA t ^ 2 + circleOrd ζ)) / lineA t := by
  unfold oddLineKernel
  rw [linePt_sub_half, I_mul_hrKernel_eq (two_mul_chart_add_one_ne_zero t) hζ h1
    (lineA_sq_add_ne_zero ht _)]

/-- Real coefficients: `K_ζ(w̄) = conj K_ζ(w)` on the line off `t = 0`. -/
theorem oddLineKernel_neg {t : ℝ} (ht : t ≠ 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    oddLineKernel ζ (linePt (-t)) = conj (oddLineKernel ζ (linePt t)) := by
  have ht' : -t ≠ 0 := neg_ne_zero.mpr ht
  by_cases h1 : ζ = 1
  · rw [h1, oddLineKernel_one, oddLineKernel_one, lineA_neg]
  · rw [oddLineKernel_eq ht' hζ h1, oddLineKernel_eq ht hζ h1, lineA_neg]
    simp only [map_div₀, map_sub, map_mul, map_pow, map_one, Complex.conj_ofReal, map_add]

/-- **The uniform bound on the support.**  For `t ≠ 0` and `ζ = 1` or `γ ≥ −¼`,
`‖K_ζ(5/4 + it)‖ ≤ 44 (1 + t²)`. -/
theorem norm_oddLineKernel_le {t : ℝ} (ht : t ≠ 0) {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hs : ζ = 1 ∨ -(1 / 4) ≤ circleOrd ζ) :
    ‖oddLineKernel ζ (linePt t)‖ ≤ 44 * (1 + t ^ 2) := by
  have hna := norm_lineA_le t
  have hta := abs_le_norm_lineA t
  have h34 := norm_lineA_ge t
  have hsq := norm_lineA_sq t
  have hnorm0 : 0 < ‖lineA t‖ := lt_of_lt_of_le (by norm_num) h34
  have habs : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  by_cases h1 : ζ = 1
  · rw [h1, oddLineKernel_one]
    nlinarith
  · have hγ : -(1 / 4) ≤ circleOrd ζ := hs.resolve_left h1
    set γ := circleOrd ζ
    set a := lineA t
    set u := a ^ 2 + (γ : ℂ) with hu
    have hu0 : u ≠ 0 := lineA_sq_add_ne_zero ht γ
    rw [oddLineKernel_eq ht hζ h1]
    -- `(γ a² − 1)/u = a² − (a⁴ + 1)/u`
    have hk : ((γ : ℂ) * a ^ 2 - 1) / u = a ^ 2 - (a ^ 4 + 1) / u := by
      rw [eq_sub_iff_add_eq, ← add_div, div_eq_iff hu0, hu]
      ring
    rw [hk, norm_div]
    have hnum : ‖a ^ 2 - (a ^ 4 + 1) / u‖ ≤ ‖a‖ ^ 2 + (‖a‖ ^ 4 + 1) / ‖u‖ := by
      have h4 : ‖a ^ 4 + 1‖ ≤ ‖a‖ ^ 4 + 1 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_pow, norm_one]
      calc ‖a ^ 2 - (a ^ 4 + 1) / u‖ ≤ ‖a ^ 2‖ + ‖(a ^ 4 + 1) / u‖ := norm_sub_le _ _
        _ = ‖a‖ ^ 2 + ‖a ^ 4 + 1‖ / ‖u‖ := by rw [norm_pow, norm_div]
        _ ≤ ‖a‖ ^ 2 + (‖a‖ ^ 4 + 1) / ‖u‖ := by gcongr
    have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    rw [div_le_iff₀ hnorm0]
    refine hnum.trans ?_
    rcases le_or_gt |t| (1 / 2) with hsmall | hlarge
    · -- small `t`: `|u| ≥ 1/16`
      have hu16 := norm_lineA_sq_add_ge_re hsmall hγ
      have ht2 : t ^ 2 ≤ 1 / 4 := by
        have := abs_le.mp hsmall
        nlinarith
      have ha2 : ‖a‖ ^ 2 ≤ 1 := by rw [hsq]; linarith
      have ha4 : ‖a‖ ^ 4 ≤ 1 := by
        have : ‖a‖ ^ 4 = (‖a‖ ^ 2) ^ 2 := by ring
        rw [this]
        nlinarith [sq_nonneg (‖a‖ ^ 2)]
      have hdiv : (‖a‖ ^ 4 + 1) / ‖u‖ ≤ 32 := by
        rw [div_le_iff₀ hu_pos]
        nlinarith
      nlinarith
    · -- large `t`: `|u| ≥ 3|t|/2` and `|a| ≥ |t|`
      have hu32 := norm_lineA_sq_add_ge_im t γ
      have ht2 : 1 / 4 < t ^ 2 := by nlinarith [sq_abs t, abs_nonneg t]
      have hu' : 3 / 2 * |t| ≤ ‖u‖ := hu32
      have hprod : 3 / 2 * t ^ 2 ≤ ‖a‖ * ‖u‖ := by
        have h1' : 0 ≤ |t| := abs_nonneg t
        calc 3 / 2 * t ^ 2 = |t| * (3 / 2 * |t|) := by rw [← sq_abs t]; ring
          _ ≤ ‖a‖ * ‖u‖ := mul_le_mul hta hu' (by positivity) (norm_nonneg _)
      have ha4 : ‖a‖ ^ 4 = (9 / 16 + t ^ 2) ^ 2 := by
        have : ‖a‖ ^ 4 = (‖a‖ ^ 2) ^ 2 := by ring
        rw [this, hsq]
      -- `(|a|⁴ + 1)/(|a||u|) ≤ (|a|⁴ + 1)/(3t²/2) ≤ 6(1 + t²)`
      have hdiv : (‖a‖ ^ 4 + 1) / ‖u‖ ≤ 6 * (1 + t ^ 2) * ‖a‖ := by
        rw [div_le_iff₀ hu_pos]
        have hkey : ‖a‖ ^ 4 + 1 ≤ 6 * (1 + t ^ 2) * (3 / 2 * t ^ 2) := by
          rw [ha4]
          nlinarith [sq_nonneg t, sq_nonneg (t ^ 2 - 1 / 4)]
        calc ‖a‖ ^ 4 + 1 ≤ 6 * (1 + t ^ 2) * (3 / 2 * t ^ 2) := hkey
          _ ≤ 6 * (1 + t ^ 2) * (‖a‖ * ‖u‖) := by gcongr
          _ = 6 * (1 + t ^ 2) * ‖a‖ * ‖u‖ := by ring
      have ha2' : ‖a‖ ^ 2 ≤ 1 + t ^ 2 := by rw [hsq]; linarith
      have ha1 : ‖a‖ ≤ 2 * (1 + t ^ 2) := by nlinarith
      nlinarith [norm_nonneg a]

end RHTower.OddResolvent
