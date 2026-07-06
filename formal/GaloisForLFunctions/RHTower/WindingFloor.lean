/-
Explicit floor for the winding rate of the archimedean envelope.

On the critical line the rational part `(2s−1)/(s(s−1))` of the winding datum is purely
imaginary, so the winding rate is exactly `(Re ψ(1/4 + iu/2) − log π)/2`.  The vertical
digamma lower bound then floors it by `(log(u/2π) − 4/u² − π/u)/2` — positive above an
explicit absolute height — and monotonicity in `u` extends the floor from the left endpoint
over any segment.  Feeding this into the winding cancellation bound makes the resonance
moment of the completed carrier decay like `1/log α` with fully explicit constants.
-/
import GaloisForLFunctions.RHTower.ArchWinding
import GaloisForLFunctions.RHTower.DigammaAsymptotic

open Complex Metric

namespace RHTower

/-- The winding datum in rational-plus-digamma form. -/
theorem archWinding_eq (u : ℝ) :
    archWinding u = (2 * linePt u - 1) / (linePt u * (linePt u - 1)) +
      (Complex.digamma ((linePt u) / 2) / 2 - (Real.log Real.pi : ℂ) / 2) := by
  have hG : Complex.Gammaℝ (linePt u) ≠ 0 :=
    Gammaℝ_ne_zero_of_re_pos (by rw [linePt_re]; norm_num)
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
  unfold archWinding archFactorDeriv archFactor
  field_simp

/-- On the critical line the rational part of the winding datum is purely imaginary, so the
winding rate is exactly the recentred vertical digamma real part. -/
theorem windingRate_eq (u : ℝ) :
    windingRate u = (Complex.digamma ((linePt u) / 2)).re / 2 - Real.log Real.pi / 2 := by
  have h1 : 2 * linePt u - 1 = ((2 * u : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  have h2 : linePt u * (linePt u - 1) = ((-(1 / 4 + u ^ 2) : ℝ) : ℂ) := by
    unfold linePt
    push_cast
    linear_combination ((u : ℂ)) ^ 2 * Complex.I_sq
  have h3 : ((2 * u : ℝ) : ℂ) * Complex.I / ((-(1 / 4 + u ^ 2) : ℝ) : ℂ) =
      ((2 * u / (-(1 / 4 + u ^ 2)) : ℝ) : ℂ) * Complex.I := by
    rw [Complex.ofReal_div, div_mul_eq_mul_div]
  have hpolyre : ((2 * linePt u - 1) / (linePt u * (linePt u - 1))).re = 0 := by
    rw [h1, h2, h3, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    norm_num
  unfold windingRate
  rw [archWinding_eq u, Complex.add_re, hpolyre, zero_add, Complex.sub_re,
    re_div_two, re_div_two, Complex.ofReal_re]

/-- **Explicit winding-rate floor.**  The vertical digamma bound gives
`windingRate u ≥ (log(u/2π) − 4/u² − π/u)/2` for every positive height. -/
theorem windingRate_ge {u : ℝ} (hu : 0 < u) :
    (Real.log (u / (2 * Real.pi)) - (4 / u ^ 2 + Real.pi / u)) / 2 ≤ windingRate u := by
  rw [windingRate_eq]
  have harg : (linePt u) / 2 = ((1 / 4 : ℝ) : ℂ) + ((u / 2 : ℝ) : ℂ) * Complex.I := by
    unfold linePt
    push_cast
    ring
  have h := re_digamma_ge (x := 1 / 4) (y := u / 2) (by norm_num) (by positivity)
  rw [harg]
  have e1 : 1 / ((u / 2) ^ 2) = 4 / u ^ 2 := by
    rw [show ((u : ℝ) / 2) ^ 2 = u ^ 2 / 4 from by ring, one_div_div]
  have e2 : 2 * (u / 2) = u := by ring
  rw [e1, e2] at h
  have hlog : Real.log (u / (2 * Real.pi)) = Real.log (u / 2) - Real.log Real.pi := by
    rw [show u / (2 * Real.pi) = (u / 2) / Real.pi from by ring,
      Real.log_div (by positivity : (0 : ℝ) < u / 2).ne' (ne_of_gt Real.pi_pos)]
  linarith

/-- Segment floor from the left endpoint: the floor is monotone in the height, so the
left-endpoint value bounds the whole segment. -/
theorem windingRate_uIcc_floor {α β : ℝ} (hα : 0 < α) (hαβ : α ≤ β) :
    ∀ u ∈ Set.uIcc α β,
      (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2 ≤ |windingRate u| := by
  intro u hu
  rw [Set.uIcc_of_le hαβ] at hu
  have hu0 : 0 < u := lt_of_lt_of_le hα hu.1
  have hmono1 : Real.log (α / (2 * Real.pi)) ≤ Real.log (u / (2 * Real.pi)) :=
    Real.log_le_log (by positivity)
      (div_le_div₀ (by linarith [hu.1] : (0:ℝ) ≤ u) hu.1 (by positivity) le_rfl)
  have hmono2 : 4 / u ^ 2 ≤ 4 / α ^ 2 :=
    div_le_div₀ (by norm_num) le_rfl (by positivity) (by nlinarith [hu.1])
  have hmono3 : Real.pi / u ≤ Real.pi / α :=
    div_le_div₀ Real.pi_pos.le le_rfl hα hu.1
  have h := windingRate_ge hu0
  have hchain : (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2 ≤
      windingRate u := by
    linarith
  exact le_trans hchain (le_abs_self _)

/-- **Fully explicit resonance-moment cancellation.**  Above a height where the explicit
winding floor `(log(α/2π) − 4/α² − π/α)/2` is positive, the first moment of the archimedean
envelope on `[α, β]` obeys the van der Corput bound with that floor — the resonance moment
decays like the reciprocal logarithm of the height, with no undischarged phase data. -/
theorem norm_integral_archFactor_line_le_explicit
    {α β M₀ Mim Mp : ℝ} (hα : 0 < α) (hαβ : α ≤ β)
    (hm : 0 < (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)
    (hM₀ : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ ≤ M₀)
    (hMim : ∀ u ∈ Set.Icc α β, ‖archFactor (linePt u)‖ * |(archWinding u).im| ≤ Mim)
    (hMp : ∀ u ∈ Set.Icc α β, |windingRateDeriv u| ≤ Mp) :
    ‖∫ u in α..β, archFactor (linePt u)‖ ≤
      2 * (M₀ / ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2)) +
      (β - α) * (Mim / ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) +
        M₀ * Mp / ((Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2) ^ 2) :=
  norm_integral_archFactor_line_le_of_winding_floor hαβ hm
    (windingRate_uIcc_floor hα hαβ) hM₀ hMim hMp

end RHTower

namespace RHTower

/-- The winding-floor expression is monotone in the height. -/
theorem winding_floor_expr_mono {α α' : ℝ} (h0 : 0 < α) (hαα' : α ≤ α') :
    (Real.log (α / (2 * Real.pi)) - (4 / α ^ 2 + Real.pi / α)) / 2 ≤
      (Real.log (α' / (2 * Real.pi)) - (4 / α' ^ 2 + Real.pi / α')) / 2 := by
  have h0' : 0 < α' := lt_of_lt_of_le h0 hαα'
  have hlog : Real.log (α / (2 * Real.pi)) ≤ Real.log (α' / (2 * Real.pi)) :=
    Real.log_le_log (by positivity)
      (div_le_div₀ h0'.le hαα' (by positivity) le_rfl)
  have h4 : 4 / α' ^ 2 ≤ 4 / α ^ 2 :=
    div_le_div₀ (by norm_num) le_rfl (by positivity) (by nlinarith)
  have hπ : Real.pi / α' ≤ Real.pi / α :=
    div_le_div₀ Real.pi_pos.le le_rfl h0 hαα'
  linarith

end RHTower
