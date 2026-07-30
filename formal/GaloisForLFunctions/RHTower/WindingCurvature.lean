/-
Curvature of the archimedean winding, and the all-explicit resonance bound.

Differentiating the rational-plus-digamma form of the winding datum identifies its derivative
as `(ratDeriv + ψ′(s/2)/4)·i` along the line; on the line the rational derivative has real
numerator `2u² − ½` over `(¼+u²)²`, and the trigamma vertical bound controls the digamma
part, giving the explicit curvature bound `|windingRateDeriv u| ≤ 3/u² + π/(4u)`.  With the
winding floor and amplitude already explicit, the archimedean resonance moment is bounded by
a closed-form function of the envelope sup and the segment height alone: Hardy's `1/log`
decay of the non-oscillating carrier moment holds unconditionally above an absolute height.
-/
import GaloisForLFunctions.RHTower.WindingAmplitude
import GaloisForLFunctions.RHTower.TrigammaVertical

open Complex Metric

namespace RHTower

/-- The winding derivative in rational-plus-trigamma form. -/
theorem archWindingDeriv_eq (u : ℝ) :
    archWindingDeriv u =
      ((-2 * (linePt u) ^ 2 + 2 * linePt u - 1) / (linePt u * (linePt u - 1)) ^ 2 +
        deriv Complex.digamma ((linePt u) / 2) / 4) * Complex.I := by
  have hre : 0 < (linePt u).re := by
    rw [linePt_re]
    norm_num
  have hs0 : linePt u ≠ 0 := by
    intro h0
    have h := congrArg Complex.re h0
    rw [linePt_re] at h
    norm_num at h
  have hs1 : linePt u - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro h1
    have h := congrArg Complex.re h1
    rw [linePt_re] at h
    norm_num at h
  have hprod_ne : linePt u * (linePt u - 1) ≠ 0 := mul_ne_zero hs0 hs1
  have h2half : 0 < ((linePt u) / 2).re := by
    rw [re_div_two, linePt_re]
    norm_num
  have hrat_s : HasDerivAt (fun s : ℂ => (2 * s - 1) / (s * (s - 1)))
      ((-2 * (linePt u) ^ 2 + 2 * linePt u - 1) / (linePt u * (linePt u - 1)) ^ 2)
      (linePt u) := by
    have hnum : HasDerivAt (fun s : ℂ => 2 * s - 1) ((2 : ℂ)) (linePt u) := by
      simpa using ((hasDerivAt_id (linePt u)).const_mul (2 : ℂ)).sub_const (1 : ℂ)
    have hden : HasDerivAt (fun s : ℂ => s * (s - 1))
        (1 * (linePt u - 1) + linePt u * 1) (linePt u) :=
      (hasDerivAt_id (linePt u)).mul ((hasDerivAt_id (linePt u)).sub_const 1)
    have hdiv := hnum.div hden hprod_ne
    convert! hdiv using 1
    field_simp
    ring
  have hψat : HasDerivAt Complex.digamma
      (deriv Complex.digamma ((linePt u) / 2)) ((linePt u) / 2) :=
    (digamma_analyticOnNhd_re_pos _ h2half).differentiableAt.hasDerivAt
  have hhalf : HasDerivAt (fun z : ℂ => z / 2) ((1 : ℂ) / 2) (linePt u) := by
    simpa using (hasDerivAt_id (linePt u)).div_const (2 : ℂ)
  have hΨ_s : HasDerivAt
      (fun s : ℂ => Complex.digamma (s / 2) / 2 - (Real.log Real.pi : ℂ) / 2)
      (deriv Complex.digamma ((linePt u) / 2) / 4) (linePt u) := by
    have hcomp := HasDerivAt.comp (linePt u) hψat hhalf
    have h := (hcomp.div_const (2 : ℂ)).sub_const ((Real.log Real.pi : ℂ) / 2)
    convert! h using 1
    ring
  have hsum_s := hrat_s.add hΨ_s
  have hcomp := HasDerivAt.comp u hsum_s (hasDerivAt_linePt u)
  have hwind : HasDerivAt archWinding
      (((-2 * (linePt u) ^ 2 + 2 * linePt u - 1) / (linePt u * (linePt u - 1)) ^ 2 +
        deriv Complex.digamma ((linePt u) / 2) / 4) * Complex.I) u := by
    have hfun : archWinding = fun u : ℝ =>
        (2 * linePt u - 1) / (linePt u * (linePt u - 1)) +
          (Complex.digamma ((linePt u) / 2) / 2 - (Real.log Real.pi : ℂ) / 2) :=
      funext archWinding_eq
    rw [hfun]
    simpa [Function.comp] using! hcomp
  exact (hasDerivAt_archWinding u).unique hwind

/-- **Explicit curvature bound for the winding rate:**
`|windingRateDeriv u| ≤ 3/u² + π/(4u)` at every positive height. -/
theorem windingRateDeriv_abs_le {u : ℝ} (hu : 0 < u) :
    |windingRateDeriv u| ≤ 3 / u ^ 2 + Real.pi / (4 * u) := by
  unfold windingRateDeriv
  refine le_trans (Complex.abs_re_le_norm _) ?_
  rw [archWindingDeriv_eq u, norm_mul, Complex.norm_I, mul_one]
  refine le_trans (norm_add_le _ _) ?_
  have h2 : linePt u * (linePt u - 1) = ((-(1 / 4 + u ^ 2) : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    linear_combination ((u : ℂ)) ^ 2 * Complex.I_sq
  have hnum_eq : -2 * (linePt u) ^ 2 + 2 * linePt u - 1 = ((2 * u ^ 2 - 1 / 2 : ℝ) : ℂ) := by
    have hstep : -2 * (linePt u) ^ 2 + 2 * linePt u - 1 =
        -2 * (linePt u * (linePt u - 1)) - 1 := by ring
    rw [hstep, h2]
    push_cast
    ring
  have hrat_norm : ‖(-2 * (linePt u) ^ 2 + 2 * linePt u - 1) /
      (linePt u * (linePt u - 1)) ^ 2‖ ≤ 2 / u ^ 2 := by
    rw [norm_div, hnum_eq, h2, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs,
      show |(-(1 / 4 + u ^ 2) : ℝ)| = 1 / 4 + u ^ 2 from by
        rw [abs_neg]; exact abs_of_pos (by positivity)]
    have hnum_le : |2 * u ^ 2 - 1 / 2| ≤ 2 * (1 / 4 + u ^ 2) := by
      rw [abs_le]
      constructor <;> nlinarith
    calc |2 * u ^ 2 - 1 / 2| / (1 / 4 + u ^ 2) ^ 2
        ≤ 2 * (1 / 4 + u ^ 2) / (1 / 4 + u ^ 2) ^ 2 :=
          div_le_div₀ (by positivity) hnum_le (by positivity) le_rfl
      _ = 2 / (1 / 4 + u ^ 2) := by
          field_simp
      _ ≤ 2 / u ^ 2 :=
          div_le_div₀ (by norm_num) le_rfl (by positivity) (by nlinarith)
  have hψ'norm : ‖deriv Complex.digamma ((linePt u) / 2) / 4‖ ≤
      (4 / u ^ 2 + Real.pi / u) / 4 := by
    have harg : (linePt u) / 2 = ((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I := by
      unfold linePt
      push_cast
      ring
    have hb := norm_deriv_digamma_vertical_le (σ := 1 / 4) (t := u / 2)
      (by norm_num) (by positivity)
    rw [← harg] at hb
    have e1 : 1 / ((u / 2 : ℝ)) ^ 2 = 4 / u ^ 2 := by
      rw [show ((u : ℝ) / 2) ^ 2 = u ^ 2 / 4 from by ring, one_div_div]
    have e2 : Real.pi / (2 * (u / 2)) = Real.pi / u := by
      rw [show 2 * (u / 2) = u from by ring]
    rw [e1, e2] at hb
    rw [norm_div, show ‖(4 : ℂ)‖ = 4 from by norm_num]
    exact div_le_div₀ (by positivity) hb (by norm_num) le_rfl
  calc ‖(-2 * (linePt u) ^ 2 + 2 * linePt u - 1) / (linePt u * (linePt u - 1)) ^ 2‖ +
        ‖deriv Complex.digamma ((linePt u) / 2) / 4‖
      ≤ 2 / u ^ 2 + (4 / u ^ 2 + Real.pi / u) / 4 := add_le_add hrat_norm hψ'norm
    _ = 3 / u ^ 2 + Real.pi / (4 * u) := by ring

/-- **All-explicit resonance-moment bound.**  Above the explicit winding threshold, the first
moment of the archimedean envelope is bounded by a closed-form function of the envelope sup
`M₀` and the segment height alone: every van der Corput face — floor, amplitude, curvature —
is a theorem. -/
theorem norm_integral_archFactor_line_le_all_explicit
    {α β M₀ : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hm : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀) :
    ‖∫ u in α..β, archFactor (linePt u)‖ ≤
      2 * (M₀ / ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)) +
      (β - α) * (M₀ * (3 / α + Real.pi / 4) /
          ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) +
        M₀ * (3 / α ^ 2 + Real.pi / (4 * α)) /
          ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) ^ 2) := by
  have hM₀0 : 0 ≤ M₀ := le_trans (norm_nonneg _) (hM₀ α ⟨le_rfl, hαβ⟩)
  refine norm_integral_archFactor_line_le_explicit hα hαβ hm hM₀ ?_ ?_
  · intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hα hu.1
    have him := archWinding_im_abs_le hu0
    have hmono : 3 / u + Real.pi / 4 ≤ 3 / α + Real.pi / 4 := by
      have : 3 / u ≤ 3 / α := div_le_div₀ (by norm_num) le_rfl hα hu.1
      linarith
    calc ‖archFactor (linePt u)‖ * |(archWinding u).im|
        ≤ M₀ * (3 / α + Real.pi / 4) :=
          mul_le_mul (hM₀ u hu) (le_trans him hmono) (abs_nonneg _) hM₀0
      _ = M₀ * (3 / α + Real.pi / 4) := rfl
  · intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le hα hu.1
    have hcurv := windingRateDeriv_abs_le hu0
    have hmono : 3 / u ^ 2 + Real.pi / (4 * u) ≤ 3 / α ^ 2 + Real.pi / (4 * α) := by
      have h1 : 3 / u ^ 2 ≤ 3 / α ^ 2 :=
        div_le_div₀ (by norm_num) le_rfl (by positivity) (by nlinarith [hu.1])
      have h2 : Real.pi / (4 * u) ≤ Real.pi / (4 * α) :=
        div_le_div₀ Real.pi_pos.le le_rfl (by positivity) (by linarith [hu.1])
      linarith
    exact le_trans hcurv hmono

end RHTower
