import GaloisForLFunctions.GaloisTheoryOfZeros.AZeroAloneInAMovingRegionIsFollowedThroughSimpleZeros
import GaloisForLFunctions.GaloisTheoryOfZeros.ACollisionAwayFromTheCentreExistsAtAForwardTime
import GaloisForLFunctions.Bottcher.Univalence

/-!
# A zero of a strip stays in its strip where the cosine term dominates

At a saddle time `τ(a)` the heat family is `B₀ + 2S₀ cos ζ` in the scaled variable `ζ = az`, up to
a small error on a window `|ζ| ≤ R`. Where the cosine term dominates, `|B₀| ≤ (97/100)|2S₀|`, the
zeros of the model solve `cos ζ = −B₀/(2S₀)`: one in each strip `θ + 1/8 ≤ Re ζ ≤ θ + π − 1/8`,
`|Im ζ| ≤ 1`, `θ ∈ πℤ`.

**Theorem** (`exists_stripFacts`). Far out in the wide region, on the cosine side:
* a zero of the window has `|cos ζ| < 127/128`, so it is not within `1/8` of a line
  `Re ζ = θ`, `θ ∈ πℤ`, and `|Im ζ| < 1`;
* on each strip of the window `ζ ↦ H_{τ(a)}(ζ/a)` is injective and its derivative does not vanish.

**Theorem** (`exists_simplyJoined_of_stripFacts`). Along a path of such saddles the zero of a strip
is joined through simple zeros to the zero of the same strip at the end of the path.

Proof. The derivative of the error is bounded by Cauchy's estimate on circles of radius `1`. On
the strip `Re(cos θ · sin ζ) = sin(Re ζ − θ) cosh(Im ζ) ≥ sin(1/8)`, so a constant multiple of the
function has a derivative of positive real part on the convex strip and is injective there. For the
zeros, `|cos ζ| ≥ |cos Re ζ|` and `|cos ζ| ≥ sinh |Im ζ|`.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower RHTower.DeBruijn RHTower.KernelStrip
open scoped Real

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## Cosine and sine at a complex point -/

theorem re_cos_eq_mul (ζ : ℂ) : (Complex.cos ζ).re = Real.cos ζ.re * Real.cosh ζ.im := by
  rw [Complex.cos_eq ζ]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]

theorem im_cos_eq_mul (ζ : ℂ) : (Complex.cos ζ).im = -(Real.sin ζ.re * Real.sinh ζ.im) := by
  rw [Complex.cos_eq ζ]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]

theorem re_sin_eq_mul (ζ : ℂ) : (Complex.sin ζ).re = Real.sin ζ.re * Real.cosh ζ.im := by
  rw [Complex.sin_eq ζ]
  simp [← Complex.ofReal_cos, ← Complex.ofReal_cosh, ← Complex.ofReal_sin, ← Complex.ofReal_sinh]

/-- `|cos Re ζ| ≤ |cos ζ|`. -/
theorem abs_cos_re_le_norm_cos (ζ : ℂ) : |Real.cos ζ.re| ≤ ‖Complex.cos ζ‖ := by
  have h := Complex.abs_re_le_norm (Complex.cos ζ)
  rw [re_cos_eq_mul, abs_mul, abs_of_pos (Real.cosh_pos _)] at h
  have h1 : |Real.cos ζ.re| * 1 ≤ |Real.cos ζ.re| * Real.cosh ζ.im :=
    mul_le_mul_of_nonneg_left (Real.one_le_cosh _) (abs_nonneg _)
  linarith

/-- `|sinh Im ζ| ≤ |cos ζ|`: `|cos ζ|² = cos²(Re ζ) + sinh²(Im ζ)`. -/
theorem abs_sinh_im_le_norm_cos (ζ : ℂ) : |Real.sinh ζ.im| ≤ ‖Complex.cos ζ‖ := by
  have hc := Real.cosh_sq ζ.im
  have hs := Real.cos_sq_add_sin_sq ζ.re
  have e : Real.cos ζ.re * Real.cosh ζ.im * (Real.cos ζ.re * Real.cosh ζ.im) +
      -(Real.sin ζ.re * Real.sinh ζ.im) * -(Real.sin ζ.re * Real.sinh ζ.im) =
      Real.sinh ζ.im ^ 2 + Real.cos ζ.re ^ 2 := by
    linear_combination Real.cos ζ.re ^ 2 * hc + Real.sinh ζ.im ^ 2 * hs
  have h : Real.sinh ζ.im ^ 2 ≤ ‖Complex.cos ζ‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, re_cos_eq_mul, im_cos_eq_mul, e]
    linarith [sq_nonneg (Real.cos ζ.re)]
  exact abs_le_of_sq_le_sq h (norm_nonneg _)

/-- A point with `|cos ζ| < 127/128` has `|Im ζ| < 1`. -/
theorem abs_im_lt_one_of_norm_cos_lt {ζ : ℂ} (h : ‖Complex.cos ζ‖ < 127 / 128) : |ζ.im| < 1 := by
  by_contra hcon
  push Not at hcon
  have h1 := abs_sinh_im_le_norm_cos ζ
  have h3 : (1 : ℝ) ≤ Real.sinh 1 := Real.self_le_sinh_iff.mpr zero_le_one
  have h2 : 1 ≤ |Real.sinh ζ.im| := by
    rcases le_total 0 ζ.im with hy | hy
    · rw [abs_of_nonneg hy] at hcon
      exact (h3.trans (Real.sinh_le_sinh.mpr hcon)).trans (le_abs_self _)
    · rw [abs_of_nonpos hy] at hcon
      have h4 := Real.sinh_le_sinh.mpr hcon
      rw [Real.sinh_neg] at h4
      exact (h3.trans h4).trans (neg_le_abs _)
  linarith

/-- A point with `|cos ζ| < 127/128` is not within `1/8` of a line `Re ζ = θ`, `θ ∈ πℤ`. -/
theorem lt_abs_re_sub_of_norm_cos_lt {ζ : ℂ} (h : ‖Complex.cos ζ‖ < 127 / 128) {θ : ℝ}
    (hθ : Real.sin θ = 0) : 1 / 8 < |ζ.re - θ| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hlo, hhi⟩ := abs_le.mp hcon
  have h1 := abs_cos_re_le_norm_cos ζ
  have hcos : Real.cos ζ.re = Real.cos (ζ.re - θ) * Real.cos θ := by
    have e : ζ.re = ζ.re - θ + θ := by ring
    conv_lhs => rw [e]
    rw [Real.cos_add, hθ, mul_zero, sub_zero]
  have habs : |Real.cos θ| = 1 := by
    rcases Real.sin_eq_zero_iff_cos_eq.mp hθ with h | h <;> rw [h] <;> norm_num
  have h2 : 127 / 128 ≤ Real.cos (ζ.re - θ) := by
    have h3 := Real.one_sub_sq_div_two_le_cos (x := ζ.re - θ)
    nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (by linarith : (0 : ℝ) ≤ ζ.re - θ + 1 / 8)]
  rw [hcos, abs_mul, habs, mul_one, abs_of_nonneg (by linarith)] at h1
  linarith

/-! ## Strips -/

/-- The strip of `θ`: `θ + 1/8 ≤ Re ζ ≤ θ + π − 1/8`, `|Im ζ| ≤ 1`. -/
def cosStrip (θ : ℝ) : Set ℂ :=
  {ζ | θ + 1 / 8 ≤ ζ.re ∧ ζ.re ≤ θ + π - 1 / 8 ∧ -1 ≤ ζ.im ∧ ζ.im ≤ 1}

/-- The open strip of `θ`. -/
def openCosStrip (θ : ℝ) : Set ℂ :=
  {ζ | θ + 1 / 8 < ζ.re ∧ ζ.re < θ + π - 1 / 8 ∧ -1 < ζ.im ∧ ζ.im < 1}

theorem openCosStrip_subset (θ : ℝ) : openCosStrip θ ⊆ cosStrip θ := fun _ h =>
  ⟨h.1.le, h.2.1.le, h.2.2.1.le, h.2.2.2.le⟩

theorem convex_cosStrip (θ : ℝ) : Convex ℝ (cosStrip θ) := by
  have h := ((convex_halfSpace_re_ge (θ + 1 / 8)).inter
    (convex_halfSpace_re_le (θ + π - 1 / 8))).inter
    ((convex_halfSpace_im_ge (-1)).inter (convex_halfSpace_im_le 1))
  have e : cosStrip θ = ({c : ℂ | θ + 1 / 8 ≤ c.re} ∩ {c : ℂ | c.re ≤ θ + π - 1 / 8}) ∩
      ({c : ℂ | -1 ≤ c.im} ∩ {c : ℂ | c.im ≤ 1}) := by
    ext ζ
    simp only [cosStrip, mem_setOf_eq, mem_inter_iff]
    tauto
  rw [e]
  exact h

theorem norm_le_of_mem_cosStrip {θ : ℝ} {ζ : ℂ} (h : ζ ∈ cosStrip θ) : ‖ζ‖ ≤ |θ| + π + 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hπ := Real.pi_pos
  have hre : |ζ.re| ≤ |θ| + π :=
    abs_le.mpr ⟨by linarith [neg_abs_le θ], by linarith [le_abs_self θ]⟩
  have him : |ζ.im| ≤ 1 := abs_le.mpr ⟨h3, h4⟩
  linarith [Complex.norm_le_abs_re_add_abs_im ζ]

/-- The strip function: nonpositive on the strip, negative on the open strip. -/
def cosStripFn (θ : ℝ) (ζ : ℂ) : ℝ :=
  max (|ζ.re - (θ + π / 2)| - (π / 2 - 1 / 8)) (|ζ.im| - 1)

theorem cosStripFn_nonpos_iff {θ : ℝ} {ζ : ℂ} : cosStripFn θ ζ ≤ 0 ↔ ζ ∈ cosStrip θ := by
  rw [cosStripFn, max_le_iff, sub_nonpos, sub_nonpos, abs_le, abs_le]
  simp only [cosStrip, mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by linarith, by linarith, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩

theorem cosStripFn_neg_iff {θ : ℝ} {ζ : ℂ} : cosStripFn θ ζ < 0 ↔ ζ ∈ openCosStrip θ := by
  rw [cosStripFn, max_lt_iff, sub_neg, sub_neg, abs_lt, abs_lt]
  simp only [openCosStrip, mem_setOf_eq]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    exact ⟨by linarith, by linarith, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨by linarith, by linarith⟩, h3, h4⟩

theorem continuous_cosStripFn (θ : ℝ) : Continuous (cosStripFn θ) := by
  unfold cosStripFn
  exact ((continuous_abs.comp (Complex.continuous_re.sub continuous_const)).sub
    continuous_const).max ((continuous_abs.comp Complex.continuous_im).sub continuous_const)

/-- A point of a strip with `|cos ζ| < 127/128` is in the open strip. -/
theorem mem_openCosStrip_of_norm_cos_lt {θ : ℝ} (hθ : Real.sin θ = 0) {ζ : ℂ}
    (hζ : ζ ∈ cosStrip θ) (h : ‖Complex.cos ζ‖ < 127 / 128) : ζ ∈ openCosStrip θ := by
  obtain ⟨h1, h2, -, -⟩ := hζ
  have ha := lt_abs_re_sub_of_norm_cos_lt h hθ
  have hθ' : Real.sin (θ + π) = 0 := by rw [Real.sin_add_pi, hθ, neg_zero]
  have hb := lt_abs_re_sub_of_norm_cos_lt h hθ'
  obtain ⟨h5, h6⟩ := abs_lt.mp (abs_im_lt_one_of_norm_cos_lt h)
  rw [abs_of_nonneg (by linarith)] at ha
  rw [abs_of_nonpos (by linarith)] at hb
  exact ⟨by linarith, by linarith, h5, h6⟩

/-- A point with `|cos ζ| < 127/128` is in the open strip of `π⌊Re ζ/π⌋`. -/
theorem mem_openCosStrip_floor {ζ : ℂ} (h : ‖Complex.cos ζ‖ < 127 / 128) :
    ζ ∈ openCosStrip (π * ⌊ζ.re / π⌋) := by
  have hπ := Real.pi_pos
  have hθ : Real.sin (π * ⌊ζ.re / π⌋) = 0 := by
    rw [mul_comm]
    exact Real.sin_int_mul_pi _
  have hθ' : Real.sin (π * ⌊ζ.re / π⌋ + π) = 0 := by rw [Real.sin_add_pi, hθ, neg_zero]
  have hlo : π * ⌊ζ.re / π⌋ ≤ ζ.re := by
    have h1 := Int.floor_le (ζ.re / π)
    rw [le_div_iff₀ hπ] at h1
    linarith
  have hhi : ζ.re < π * ⌊ζ.re / π⌋ + π := by
    have h1 := Int.lt_floor_add_one (ζ.re / π)
    rw [div_lt_iff₀ hπ] at h1
    linarith
  have ha := lt_abs_re_sub_of_norm_cos_lt h hθ
  have hb := lt_abs_re_sub_of_norm_cos_lt h hθ'
  obtain ⟨h5, h6⟩ := abs_lt.mp (abs_im_lt_one_of_norm_cos_lt h)
  rw [abs_of_nonneg (by linarith)] at ha
  rw [abs_of_nonpos (by linarith)] at hb
  exact ⟨by linarith, by linarith, h5, h6⟩

/-- On the strip of `θ ∈ πℤ`: `Re(cos θ · sin ζ) = sin(Re ζ − θ) cosh(Im ζ) ≥ 1/9`. -/
theorem le_re_cos_mul_sin {θ : ℝ} (hθ : Real.sin θ = 0) {ζ : ℂ} (h : ζ ∈ cosStrip θ) :
    1 / 9 ≤ ((Real.cos θ : ℂ) * Complex.sin ζ).re := by
  obtain ⟨h1, h2, -, -⟩ := h
  have hπ := Real.pi_gt_three
  rw [Complex.re_ofReal_mul, re_sin_eq_mul]
  have hsub : Real.sin (ζ.re - θ) = Real.sin ζ.re * Real.cos θ := by
    rw [Real.sin_sub, hθ, mul_zero, sub_zero]
  have hs8 : 1 / 9 ≤ Real.sin (1 / 8) := by
    have h3 := Real.sin_gt_sub_cube (x := 1 / 8) (by norm_num)
    have e : (1 / 8 : ℝ) - (1 / 8) ^ 3 / 6 = 383 / 3072 := by norm_num
    rw [e] at h3
    linarith
  have hsin : Real.sin (1 / 8) ≤ Real.sin (ζ.re - θ) := by
    rcases le_total (ζ.re - θ) (π / 2) with hle | hge
    · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hle (by linarith)
    · rw [← Real.sin_pi_sub (ζ.re - θ)]
      exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
  have h0 : 0 ≤ Real.sin (ζ.re - θ) := by linarith
  calc (1 : ℝ) / 9 ≤ Real.sin (ζ.re - θ) * 1 := by linarith
    _ ≤ Real.sin (ζ.re - θ) * Real.cosh ζ.im :=
        mul_le_mul_of_nonneg_left (Real.one_le_cosh _) h0
    _ = Real.cos θ * (Real.sin ζ.re * Real.cosh ζ.im) := by rw [hsub]; ring

theorem norm_ofReal_cos_eq_one {θ : ℝ} (hθ : Real.sin θ = 0) : ‖(Real.cos θ : ℂ)‖ = 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases Real.sin_eq_zero_iff_cos_eq.mp hθ with h | h <;> rw [h] <;> norm_num

/-! ## A function near a constant plus a cosine -/

/-- **Univalence where the sine has a direction.** Let `F` be entire with `|F' + 2S sin ζ| ≤ δ` on
a convex set `U` on which `Re(c sin ζ) ≥ m`, `|c| = 1`, and let `δ < 2|S|m`. Then `F` is injective
on `U` and `F'` does not vanish on `U`: the function `−cF/(2S)` has a derivative of positive real
part. -/
theorem injOn_and_deriv_ne_zero {F : ℂ → ℂ} (hF : Differentiable ℂ F) {U : Set ℂ}
    (hU : Convex ℝ U) {S c : ℂ} {m δ : ℝ} (hc : ‖c‖ = 1)
    (hm : ∀ ζ ∈ U, m ≤ (c * Complex.sin ζ).re) (hδ : δ < 2 * ‖S‖ * m)
    (hD : ∀ ζ ∈ U, ‖deriv F ζ + 2 * S * Complex.sin ζ‖ ≤ δ) :
    InjOn F U ∧ ∀ ζ ∈ U, deriv F ζ ≠ 0 := by
  rcases U.eq_empty_or_nonempty with rfl | ⟨ζ₁, hζ₁⟩
  · exact ⟨injOn_empty F, fun ζ h => (notMem_empty ζ h).elim⟩
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans (hD ζ₁ hζ₁)
  have hS : 0 < ‖S‖ := by
    by_contra hcon
    push Not at hcon
    have h0 : ‖S‖ = 0 := le_antisymm hcon (norm_nonneg _)
    rw [h0] at hδ
    linarith
  have hS0 : S ≠ 0 := norm_pos_iff.mp hS
  have hc0 : c ≠ 0 := norm_pos_iff.mp (by rw [hc]; exact one_pos)
  have hκn : ‖-c / (2 * S)‖ = 1 / (2 * ‖S‖) := by
    rw [norm_div, norm_neg, hc, norm_mul, Complex.norm_ofNat]
  have hg : Differentiable ℂ fun ζ => -c / (2 * S) * F ζ := hF.const_mul _
  have hderiv : ∀ ζ, deriv (fun ζ => -c / (2 * S) * F ζ) ζ = -c / (2 * S) * deriv F ζ :=
    fun ζ => deriv_const_mul _ (hF ζ)
  have hpos : ∀ ζ ∈ U, 0 < (deriv (fun ζ => -c / (2 * S) * F ζ) ζ).re := by
    intro ζ hζ
    have e : -c / (2 * S) * deriv F ζ =
        c * Complex.sin ζ + -c / (2 * S) * (deriv F ζ + 2 * S * Complex.sin ζ) := by
      field_simp
      ring
    rw [hderiv, e, Complex.add_re]
    have h1 := hm ζ hζ
    have h2 : ‖-c / (2 * S) * (deriv F ζ + 2 * S * Complex.sin ζ)‖ ≤ 1 / (2 * ‖S‖) * δ := by
      rw [norm_mul, hκn]
      exact mul_le_mul_of_nonneg_left (hD ζ hζ) (by positivity)
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm _).trans h2)).1
    have h4 : 1 / (2 * ‖S‖) * δ < m := by
      rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
      linarith
    linarith
  have hinj := Bottcher.injOn_of_re_deriv_pos hU (fun z _ => (hg z).hasDerivAt)
    ((hg.contDiff (n := 1)).continuous_deriv le_rfl).continuousOn hpos
  have hκ0 : -c / (2 * S) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr hc0) (mul_ne_zero two_ne_zero hS0)
  refine ⟨fun x hx y hy hxy => hinj hx hy ?_, fun ζ hζ h0 => ?_⟩
  · show -c / (2 * S) * F x = -c / (2 * S) * F y
    rw [hxy]
  · have h1 := hpos ζ hζ
    rw [hderiv, h0, mul_zero, Complex.zero_re] at h1
    exact lt_irrefl _ h1

/-- **The derivative of the model.** If `|F − B − 2S cos ζ| ≤ δ` for `|ζ| ≤ R`, then
`|F' + 2S sin ζ| ≤ δ` for `|ζ| ≤ R − 1`: Cauchy's estimate on the circle of radius `1`. -/
theorem norm_deriv_add_sin_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) {B S : ℂ} {R δ : ℝ}
    (hmodel : ∀ ζ : ℂ, ‖ζ‖ ≤ R → ‖F ζ - B - 2 * S * Complex.cos ζ‖ ≤ δ) {ζ : ℂ}
    (hζ : ‖ζ‖ ≤ R - 1) : ‖deriv F ζ + 2 * S * Complex.sin ζ‖ ≤ δ := by
  have hE : Differentiable ℂ fun w => F w - B - 2 * S * Complex.cos w :=
    (hF.sub_const B).sub (Complex.differentiable_cos.const_mul (2 * S))
  have hd : HasDerivAt (fun w => F w - B - 2 * S * Complex.cos w)
      (deriv F ζ - 2 * S * -Complex.sin ζ) ζ :=
    ((hF ζ).hasDerivAt.sub_const B).sub ((Complex.hasDerivAt_cos ζ).const_mul (2 * S))
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := ζ) (R := 1) (C := δ) one_pos
    hE.diffContOnCl (fun w hw => hmodel w (by
      rw [mem_sphere_iff_norm] at hw
      have h1 := norm_add_le (w - ζ) ζ
      rw [sub_add_cancel] at h1
      linarith))
  rw [hd.deriv, div_one] at h
  have e : deriv F ζ - 2 * S * -Complex.sin ζ = deriv F ζ + 2 * S * Complex.sin ζ := by ring
  rwa [e] at h

/-- **The zeros on the cosine side.** If `|B| ≤ (97/100)|2S|` and the value `0` is within
`δ < (71/3200)|2S|` of `B + 2S cos ζ`, then `|cos ζ| < 127/128`. -/
theorem norm_cos_lt_of_zero {B S ζ : ℂ} {δ : ℝ} (hside : ‖B‖ ≤ 97 / 100 * ‖2 * S‖)
    (hδ : δ < 71 / 3200 * ‖2 * S‖) (hmodel : ‖(0 : ℂ) - B - 2 * S * Complex.cos ζ‖ ≤ δ) :
    ‖Complex.cos ζ‖ < 127 / 128 := by
  have e : (0 : ℂ) - B - 2 * S * Complex.cos ζ = -(B + 2 * S * Complex.cos ζ) := by ring
  rw [e, norm_neg] at hmodel
  have h1 := norm_sub_norm_le (2 * S * Complex.cos ζ) (-B)
  rw [sub_neg_eq_add, norm_neg, norm_mul, add_comm (2 * S * Complex.cos ζ) B] at h1
  by_contra hcon
  push Not at hcon
  have h2 : ‖2 * S‖ * (127 / 128) ≤ ‖2 * S‖ * ‖Complex.cos ζ‖ :=
    mul_le_mul_of_nonneg_left hcon (norm_nonneg _)
  linarith

/-! ## The heat family at a saddle of the cosine side -/

/-- The side of the saddles on which the cosine term dominates: `|B₀| ≤ (97/100)|2S₀|`. -/
def CosineSide (a : ℂ) : Prop := ‖bulkTerm a‖ ≤ 97 / 100 * ‖2 * saddleTerm a‖

/-- The zeros of `H_{τ(a)}` in the window `|az| ≤ R`: they stay off the lines between the strips,
and on each strip of the window the function is injective with nonvanishing derivative. -/
structure StripFacts (R : ℝ) (a : ℂ) : Prop where
  collar : ∀ z : ℂ, complexHeat (saddleTime a) z = 0 → ‖a * z‖ ≤ R →
    ‖Complex.cos (a * z)‖ < 127 / 128
  injOn : ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R → ∀ z z' : ℂ, a * z ∈ cosStrip θ →
    a * z' ∈ cosStrip θ → complexHeat (saddleTime a) z = complexHeat (saddleTime a) z' → z = z'
  simple : ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R → ∀ z : ℂ, a * z ∈ cosStrip θ →
    deriv (complexHeat (saddleTime a)) z ≠ 0

theorem differentiable_scaledHeat (a : ℂ) :
    Differentiable ℂ fun ζ : ℂ => complexHeat (saddleTime a) (ζ / a) :=
  (differentiable_complexHeat (saddleTime a)).comp (differentiable_id.div_const a)

theorem deriv_scaledHeat (a ζ : ℂ) :
    deriv (fun ζ : ℂ => complexHeat (saddleTime a) (ζ / a)) ζ =
      deriv (complexHeat (saddleTime a)) (ζ / a) / a := by
  have h1 : HasDerivAt (fun ζ : ℂ => ζ / a) (1 / a) ζ := (hasDerivAt_id ζ).div_const a
  have h2 := ((differentiable_complexHeat (saddleTime a)) (ζ / a)).hasDerivAt
  have h3 := h2.comp ζ h1
  rw [show (fun ζ : ℂ => complexHeat (saddleTime a) (ζ / a)) =
    complexHeat (saddleTime a) ∘ fun ζ : ℂ => ζ / a from rfl, h3.deriv, mul_one_div]

/-- **The strips at a saddle of the cosine side**, far out in the wide region. -/
theorem exists_stripFacts (R : ℝ) : ∃ σ₀ : ℝ, ∀ a : ℂ, WideRegion a → σ₀ ≤ a.re →
    CosineSide a → StripFacts R a := by
  obtain ⟨σ₀, hσ₀⟩ := exists_forall_norm_complexHeat_sub_wide_model_le R (ε := 1 / 100)
    (by norm_num)
  refine ⟨σ₀, fun a ha hσ hside => ?_⟩
  have ha0 := ha.ne_zero
  have hBpos : 0 < ‖bulkTerm a‖ :=
    lt_of_lt_of_le (mul_pos (norm_pos_iff.mpr kernelC_zero_ne_zero) (Real.exp_pos _))
      ha.le_norm_bulkTerm
  have h2S : ‖2 * saddleTerm a‖ = 2 * ‖saddleTerm a‖ := by rw [norm_mul, Complex.norm_ofNat]
  have hside' : ‖bulkTerm a‖ ≤ 97 / 100 * (2 * ‖saddleTerm a‖) := by
    rw [← h2S]
    exact hside
  have hmodel : ∀ ζ : ℂ, ‖ζ‖ ≤ R →
      ‖complexHeat (saddleTime a) (ζ / a) - bulkTerm a - 2 * saddleTerm a * Complex.cos ζ‖ ≤
        1 / 100 * (‖bulkTerm a‖ + ‖saddleTerm a‖) := hσ₀ a ha hσ
  have hscale : ∀ z : ℂ, a * z / a = z := fun z => mul_div_cancel_left₀ z ha0
  have hstrip : ∀ θ : ℝ, Real.sin θ = 0 → |θ| + π + 2 ≤ R →
      InjOn (fun ζ : ℂ => complexHeat (saddleTime a) (ζ / a)) (cosStrip θ) ∧
        ∀ ζ ∈ cosStrip θ, deriv (fun ζ : ℂ => complexHeat (saddleTime a) (ζ / a)) ζ ≠ 0 :=
    fun θ hθ hθR =>
      injOn_and_deriv_ne_zero (differentiable_scaledHeat a) (convex_cosStrip θ)
        (norm_ofReal_cos_eq_one hθ) (fun ζ hζ => le_re_cos_mul_sin hθ hζ)
        (by linarith : 1 / 100 * (‖bulkTerm a‖ + ‖saddleTerm a‖) < 2 * ‖saddleTerm a‖ * (1 / 9))
        (fun ζ hζ => norm_deriv_add_sin_le (differentiable_scaledHeat a) hmodel
          (by linarith [norm_le_of_mem_cosStrip hζ]))
  refine ⟨fun z hz hzR => ?_, fun θ hθ hθR z z' hz hz' heq => ?_, fun θ hθ hθR z hz h0 => ?_⟩
  · have h1 := hmodel (a * z) hzR
    rw [hscale, hz] at h1
    exact norm_cos_lt_of_zero hside (by rw [h2S]; linarith) h1
  · refine mul_left_cancel₀ ha0 ((hstrip θ hθ hθR).1 hz hz' ?_)
    show complexHeat (saddleTime a) (a * z / a) = complexHeat (saddleTime a) (a * z' / a)
    rw [hscale, hscale, heq]
  · refine (hstrip θ hθ hθR).2 (a * z) hz ?_
    rw [deriv_scaledHeat, hscale, h0, zero_div]

/-! ## A path of saddles of the cosine side -/

theorem continuous_saddleTime_comp_wide {a : ℝ → ℂ} (ha : Continuous a)
    (hW : ∀ s, WideRegion (a s)) : Continuous fun s => saddleTime (a s) := by
  have hP : Continuous fun s => saddleP (a s) :=
    continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul ha))
  exact hP.div ha fun s => (hW s).ne_zero

/-- **The zero of a strip as a continuous family.** Along a path of saddles with the strip facts,
a zero of `H_{τ(a(0))}` in the strip of `θ` is followed by a continuous family of simple zeros in
the open strip of `θ`. -/
theorem exists_isZeroLift_of_stripFacts {R : ℝ} {a : ℝ → ℂ} (ha : Continuous a)
    (hW : ∀ s, WideRegion (a s)) (hfacts : ∀ s, StripFacts R (a s)) {θ : ℝ}
    (hθ : Real.sin θ = 0) (hθR : |θ| + π + 2 ≤ R) {z₀ : ℂ}
    (h0 : complexHeat (saddleTime (a 0)) z₀ = 0) (hz₀ : a 0 * z₀ ∈ cosStrip θ) :
    ∃ w : ℝ → ℂ, IsZeroLift (fun s => saddleTime (a s)) 1 w ∧ w 0 = z₀ ∧
      ∀ s ∈ Icc (0 : ℝ) 1, a s * w s ∈ openCosStrip θ ∧
        deriv (complexHeat (saddleTime (a s))) (w s) ≠ 0 := by
  have hd : Continuous fun p : ℝ × ℂ => cosStripFn θ (a p.1 * p.2) :=
    (continuous_cosStripFn θ).comp ((ha.comp continuous_fst).mul continuous_snd)
  have hnorm : ∀ s, 1 ≤ ‖a s‖ := fun s => by
    have h1 := (le_abs_self _).trans (Complex.abs_re_le_norm (a s))
    linarith [(hW s).1]
  have hwin : ∀ s z, a s * z ∈ cosStrip θ → ‖a s * z‖ ≤ R := fun s z hz => by
    linarith [norm_le_of_mem_cosStrip hz]
  obtain ⟨w, hw, hw0, hprop⟩ := exists_isZeroLift_of_alone (γ := fun s => saddleTime (a s))
    (d := fun s z => cosStripFn θ (a s * z)) (M := |θ| + π + 1)
    (continuous_saddleTime_comp_wide ha hW).continuousOn hd.continuousOn
    (fun s _ z hz => by
      have h1 := norm_le_of_mem_cosStrip (cosStripFn_nonpos_iff.mp hz)
      rw [norm_mul] at h1
      have h2 : 1 * ‖z‖ ≤ ‖a s‖ * ‖z‖ := mul_le_mul_of_nonneg_right (hnorm s) (norm_nonneg z)
      linarith)
    (fun s _ z hz hd => cosStripFn_neg_iff.mpr (mem_openCosStrip_of_norm_cos_lt hθ
      (cosStripFn_nonpos_iff.mp hd)
      ((hfacts s).collar z hz (hwin s z (cosStripFn_nonpos_iff.mp hd)))))
    (fun s _ z z' hz hd hz' hd' => (hfacts s).injOn θ hθ hθR z z'
      (cosStripFn_nonpos_iff.mp hd) (cosStripFn_nonpos_iff.mp hd') (by rw [hz, hz']))
    (fun s _ z _ hd => (hfacts s).simple θ hθ hθR z (cosStripFn_nonpos_iff.mp hd))
    h0 (cosStripFn_nonpos_iff.mpr hz₀)
  exact ⟨w, hw, hw0, fun s hs => ⟨cosStripFn_neg_iff.mp (hprop s hs).1, (hprop s hs).2⟩⟩

/-- **A zero of a strip stays in its strip.** Along a path of saddles with the strip facts, a zero
of `H_{τ(a(0))}` in the strip of `θ` is joined through simple zeros to a zero of `H_{τ(a(1))}` in
the open strip of `θ`. -/
theorem exists_simplyJoined_of_stripFacts {R : ℝ} {a : ℝ → ℂ} (ha : Continuous a)
    (hW : ∀ s, WideRegion (a s)) (hfacts : ∀ s, StripFacts R (a s)) {θ : ℝ}
    (hθ : Real.sin θ = 0) (hθR : |θ| + π + 2 ≤ R) {z₀ : ℂ}
    (h0 : complexHeat (saddleTime (a 0)) z₀ = 0) (hz₀ : a 0 * z₀ ∈ cosStrip θ) :
    ∃ z₁, SimplyJoined (saddleTime (a 0)) z₀ (saddleTime (a 1)) z₁ ∧
      complexHeat (saddleTime (a 1)) z₁ = 0 ∧ a 1 * z₁ ∈ openCosStrip θ := by
  obtain ⟨w, hw, hw0, hprop⟩ := exists_isZeroLift_of_stripFacts ha hW hfacts hθ hθR h0 hz₀
  have h11 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  exact ⟨w 1, ⟨fun s => saddleTime (a s), w,
    (continuous_saddleTime_comp_wide ha hW).continuousOn, fun s _ => (hW s).time_re_pos, hw,
    fun s hs => (hprop s hs).2, rfl, rfl, hw0, rfl⟩, hw.zero 1 h11, (hprop 1 h11).1⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
