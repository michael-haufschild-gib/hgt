import GaloisForLFunctions.RHTower.XiMassConjugatedBound

/-!
# The caustic symbol on a complex balance window

The Cauchy iteration needs the symbol to be small not only on the balance ray but on a complex disc
around it, because every derivative of the conjugated carrier is read off a circle.  The disc that
works has radius `√u`: the residue identity

`4a²(τ² + w²) − w² = 4a²σ² + 8ia²σu + (4a²−1)(2κ_B u s + s²)`,  `w = κ_B u + s`,

is an algebraic identity and holds for complex displacements verbatim, and on `‖s‖ ≤ √u` its right
side is `O(u^{3/2})` while `‖τ² + w²‖ ≳ u²`.  So the symbol is `O(u^{-1/2})` on the whole disc, not
merely on the ray, and one Cauchy step per derivative keeps that order.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The residue identity at a complex displacement.** -/
theorem xiMassCausticSymbolC_residue {a sigma u : ℝ} (ha : 1 / 2 < a) (s : ℂ) :
    4 * (a : ℂ) ^ 2
        * (((sigma : ℂ) + (u : ℂ) * Complex.I) ^ 2
          + (((xiMassSpacelikeSharpSlope a * u : ℝ) : ℂ) + s) ^ 2)
      - (((xiMassSpacelikeSharpSlope a * u : ℝ) : ℂ) + s) ^ 2
      = 4 * (a : ℂ) ^ 2 * (sigma : ℂ) ^ 2
        + 8 * Complex.I * (a : ℂ) ^ 2 * (sigma : ℂ) * (u : ℂ)
        + (4 * (a : ℂ) ^ 2 - 1)
          * (2 * ((xiMassSpacelikeSharpSlope a : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 4 * a ^ 2 - 1 := by nlinarith
  have hkey : (4 * a ^ 2 - 1) * xiMassSpacelikeSharpSlope a ^ 2 = 4 * a ^ 2 := by
    rw [xiMassSpacelikeSharpSlope_sq ha]
    field_simp
  have hkeyC : (4 * (a : ℂ) ^ 2 - 1) * ((xiMassSpacelikeSharpSlope a : ℝ) : ℂ) ^ 2
      = 4 * (a : ℂ) ^ 2 := by
    have h := congrArg (fun t : ℝ => ((t : ℝ) : ℂ)) hkey
    push_cast at h
    linear_combination h
  push_cast
  linear_combination ((u : ℂ) ^ 2) * hkeyC + Complex.I_sq * (4 * (a : ℂ) ^ 2 * (u : ℂ) ^ 2)

set_option maxHeartbeats 1000000 in
/-- **The caustic symbol is `O(u^{-1/2})` on the complex square-root window.** -/
theorem exists_norm_xiMassCausticSymbolC_le {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ∃ C u₀ : ℝ, 0 < C ∧ 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ s : ℂ, ‖s‖ ≤ Real.sqrt u →
      ‖xiMassCausticSymbolC a ((sigma : ℂ) + (u : ℂ) * Complex.I)
          (((xiMassSpacelikeSharpSlope a * u : ℝ) : ℂ) + s)‖ ≤ C / Real.sqrt u := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 4 * a ^ 2 - 1 := by nlinarith
  set κ : ℝ := xiMassSpacelikeSharpSlope a with hκdef
  have hκ1 : 1 < κ := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < κ := by linarith
  set q : ℝ := κ ^ 2 - 1 with hqdef
  have hq0 : (0 : ℝ) < q := by rw [hqdef]; nlinarith
  set C₁ : ℝ := 12 * a ^ 2 + (4 * a ^ 2 - 1) * (2 * κ + 1) with hC₁def
  have hC₁0 : (0 : ℝ) < C₁ := by rw [hC₁def]; positivity
  refine ⟨2 * a ^ 2 * C₁ / q,
    max (max 1 (sigma ^ 2)) (((8 * κ + 4 * sigma + 4) / q) ^ 2), by positivity,
    le_trans (le_max_left 1 (sigma ^ 2)) (le_max_left _ _), ?_⟩
  intro u hu s hs
  have hu1 : (1 : ℝ) ≤ u := le_trans (le_trans (le_max_left 1 (sigma ^ 2)) (le_max_left _ _)) hu
  have huσ : sigma ^ 2 ≤ u := le_trans (le_trans (le_max_right 1 (sigma ^ 2)) (le_max_left _ _)) hu
  have huκ : ((8 * κ + 4 * sigma + 4) / q) ^ 2 ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0 : ℝ) < u := by linarith
  set r : ℝ := Real.sqrt u with hrdef
  have hr0 : (0 : ℝ) < r := Real.sqrt_pos.2 hu0
  have hrsq : r ^ 2 = u := Real.sq_sqrt hu0.le
  have hr1 : (1 : ℝ) ≤ r := by nlinarith
  have hσr : sigma ≤ r := by
    have h1 : Real.sqrt (sigma ^ 2) ≤ Real.sqrt u := Real.sqrt_le_sqrt huσ
    rwa [Real.sqrt_sq hsigma.le] at h1
  have hs0 : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have hsn : ‖s‖ ≤ r := hs
  have hur : u ≤ u * r := by nlinarith
  set τ : ℂ := (sigma : ℂ) + (u : ℂ) * Complex.I with hτdef
  set w : ℂ := ((κ * u : ℝ) : ℂ) + s with hwdef
  set z : ℂ := τ ^ 2 + w ^ 2 with hzdef
  -- the propagation argument is dominated by its `u²` term
  have hzsplit : z = ((q * u ^ 2 : ℝ) : ℂ)
      + (((sigma ^ 2 : ℝ) : ℂ) + 2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2
        + 2 * Complex.I * (sigma : ℂ) * (u : ℂ)) := by
    rw [hzdef, hτdef, hwdef, hqdef]
    push_cast
    linear_combination Complex.I_sq * ((u : ℂ) ^ 2)
  have hEbound : ‖((sigma ^ 2 : ℝ) : ℂ) + 2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2
        + 2 * Complex.I * (sigma : ℂ) * (u : ℂ)‖
      ≤ sigma ^ 2 + 2 * κ * u * r + u + 2 * sigma * u := by
    have h1 : ‖((sigma ^ 2 : ℝ) : ℂ)‖ = sigma ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg sigma)]
    have h2 : ‖2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s‖ ≤ 2 * κ * u * r := by
      rw [show (2 : ℂ) * ((κ : ℝ) : ℂ) * (u : ℂ) * s = ((2 * κ * u : ℝ) : ℂ) * s by
        push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * κ * u)]
      exact mul_le_mul_of_nonneg_left hsn (by positivity)
    have h3 : ‖s ^ 2‖ ≤ u := by
      rw [norm_pow]
      nlinarith [hs0, hsn, hrsq]
    have h4 : ‖2 * Complex.I * (sigma : ℂ) * (u : ℂ)‖ = 2 * sigma * u := by
      rw [show (2 : ℂ) * Complex.I * (sigma : ℂ) * (u : ℂ)
          = Complex.I * ((2 * sigma * u : ℝ) : ℂ) by push_cast; ring, norm_mul, Complex.norm_I,
        one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc ‖((sigma ^ 2 : ℝ) : ℂ) + 2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2
            + 2 * Complex.I * (sigma : ℂ) * (u : ℂ)‖
        ≤ ‖((sigma ^ 2 : ℝ) : ℂ) + 2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2‖
          + ‖2 * Complex.I * (sigma : ℂ) * (u : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖((sigma ^ 2 : ℝ) : ℂ) + 2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s‖ + ‖s ^ 2‖)
          + ‖2 * Complex.I * (sigma : ℂ) * (u : ℂ)‖ := by
            linarith [norm_add_le (((sigma ^ 2 : ℝ) : ℂ) + 2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s) (s ^ 2)]
      _ ≤ ((‖((sigma ^ 2 : ℝ) : ℂ)‖ + ‖2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s‖) + ‖s ^ 2‖)
          + ‖2 * Complex.I * (sigma : ℂ) * (u : ℂ)‖ := by
            linarith [norm_add_le (((sigma ^ 2 : ℝ) : ℂ)) (2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s)]
      _ ≤ sigma ^ 2 + 2 * κ * u * r + u + 2 * sigma * u := by
            rw [h1, h4]; linarith [h2, h3]
  have hEsmall : sigma ^ 2 + 2 * κ * u * r + u + 2 * sigma * u ≤ q * u ^ 2 / 2 := by
    have hqr : 8 * κ + 4 * sigma + 4 ≤ q * r := by
      have h := huκ
      have hnn : (0 : ℝ) ≤ (8 * κ + 4 * sigma + 4) / q := by positivity
      have hle : (8 * κ + 4 * sigma + 4) / q ≤ r := by nlinarith
      rw [div_le_iff₀ hq0] at hle
      linarith
    have hprod : (8 * κ + 4 * sigma + 4) * r ^ 3 ≤ (q * r) * r ^ 3 :=
      mul_le_mul_of_nonneg_right hqr (by positivity)
    rw [← hrsq]
    have h1 : sigma ^ 2 ≤ r ^ 3 := by nlinarith [hσr, hr1, hsigma.le, hr0]
    have h2 : r ^ 2 ≤ r ^ 3 := by nlinarith [hr1, hr0]
    have h3 : 2 * sigma * r ^ 2 ≤ 2 * sigma * r ^ 3 := by nlinarith [hr1, hr0, hsigma.le]
    have h4 : (4 * κ + 2 * sigma + 2) * r ^ 3 ≤ q * (r ^ 2) ^ 2 / 2 := by nlinarith [hprod]
    have h5 : (2 * κ + 2 * sigma + 2) * r ^ 3 ≤ (4 * κ + 2 * sigma + 2) * r ^ 3 := by
      nlinarith [hκ0, hr0]
    nlinarith [h1, h2, h3, h4, h5]
  have hznorm : q * u ^ 2 / 2 ≤ ‖z‖ := by
    have hq2 : ‖((q * u ^ 2 : ℝ) : ℂ)‖ = q * u ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have hrev := norm_sub_norm_le (((q * u ^ 2 : ℝ) : ℂ))
      (-(((sigma ^ 2 : ℝ) : ℂ) + 2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2
        + 2 * Complex.I * (sigma : ℂ) * (u : ℂ)))
    rw [sub_neg_eq_add, hq2, norm_neg] at hrev
    rw [hzsplit]
    linarith [hEbound, hEsmall, hrev]
  have hqu : (0 : ℝ) < q * u ^ 2 / 2 := by positivity
  have hzne : z ≠ 0 := by
    intro hcon
    rw [hcon] at hznorm
    simp at hznorm
    linarith
  -- the numerator
  have hnum := xiMassCausticSymbolC_residue (a := a) (sigma := sigma) (u := u) ha s
  rw [← hκdef, ← hτdef] at hnum
  have hnumbound : ‖4 * (a : ℂ) ^ 2 * z - w ^ 2‖ ≤ C₁ * (u * r) := by
    rw [hzdef, hwdef] at *
    rw [hnum]
    have h1 : ‖4 * (a : ℂ) ^ 2 * (sigma : ℂ) ^ 2‖ = 4 * a ^ 2 * sigma ^ 2 := by
      rw [show (4 : ℂ) * (a : ℂ) ^ 2 * (sigma : ℂ) ^ 2
          = ((4 * a ^ 2 * sigma ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖8 * Complex.I * (a : ℂ) ^ 2 * (sigma : ℂ) * (u : ℂ)‖ = 8 * a ^ 2 * sigma * u := by
      rw [show (8 : ℂ) * Complex.I * (a : ℂ) ^ 2 * (sigma : ℂ) * (u : ℂ)
          = Complex.I * ((8 * a ^ 2 * sigma * u : ℝ) : ℂ) by push_cast; ring,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have h3 : ‖(4 * (a : ℂ) ^ 2 - 1) * (2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2)‖
        ≤ (4 * a ^ 2 - 1) * (2 * κ * u * r + u) := by
      rw [show ((4 : ℂ) * (a : ℂ) ^ 2 - 1) = ((4 * a ^ 2 - 1 : ℝ) : ℂ) by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hden]
      refine mul_le_mul_of_nonneg_left ?_ (by linarith)
      have hA : ‖2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s‖ ≤ 2 * κ * u * r := by
        rw [show (2 : ℂ) * ((κ : ℝ) : ℂ) * (u : ℂ) * s = ((2 * κ * u : ℝ) : ℂ) * s by
          push_cast; ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity : (0 : ℝ) < 2 * κ * u)]
        exact mul_le_mul_of_nonneg_left hsn (by positivity)
      have hB : ‖s ^ 2‖ ≤ u := by
        rw [norm_pow]
        nlinarith [hs0, hsn, hrsq]
      calc ‖2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2‖
          ≤ ‖2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s‖ + ‖s ^ 2‖ := norm_add_le _ _
        _ ≤ 2 * κ * u * r + u := by linarith
    have htwo := norm_add_le (4 * (a : ℂ) ^ 2 * (sigma : ℂ) ^ 2)
      (8 * Complex.I * (a : ℂ) ^ 2 * (sigma : ℂ) * (u : ℂ))
    rw [h1, h2] at htwo
    have hsplit := norm_add_le
      (4 * (a : ℂ) ^ 2 * (sigma : ℂ) ^ 2
        + 8 * Complex.I * (a : ℂ) ^ 2 * (sigma : ℂ) * (u : ℂ))
      ((4 * (a : ℂ) ^ 2 - 1) * (2 * ((κ : ℝ) : ℂ) * (u : ℂ) * s + s ^ 2))
    have e1 : 4 * a ^ 2 * sigma ^ 2 ≤ 4 * a ^ 2 * (u * r) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : 8 * a ^ 2 * sigma * u ≤ 8 * a ^ 2 * (u * r) := by
      have hstep : sigma * u ≤ r * u := mul_le_mul_of_nonneg_right hσr hu0.le
      nlinarith [hstep]
    have hin : 2 * κ * u * r + u ≤ (2 * κ + 1) * (u * r) := by nlinarith [hur]
    have e3 : (4 * a ^ 2 - 1) * (2 * κ * u * r + u)
        ≤ (4 * a ^ 2 - 1) * (2 * κ + 1) * (u * r) := by
      have := mul_le_mul_of_nonneg_left hin (le_of_lt hden)
      nlinarith [this]
    rw [hC₁def]
    linarith [hsplit, htwo, h3, e1, e2, e3]
  -- assemble
  have hsymb : xiMassCausticSymbolC a τ w = (a : ℂ) ^ 2 * (4 * (a : ℂ) ^ 2 * z - w ^ 2) / z := by
    rw [xiMassCausticSymbolC, ← hzdef]
    field_simp
  rw [hsymb, norm_div, norm_mul]
  have hanorm : ‖(a : ℂ) ^ 2‖ = a ^ 2 := by
    rw [show ((a : ℂ)) ^ 2 = ((a ^ 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  rw [hanorm]
  have hA : a ^ 2 * ‖4 * (a : ℂ) ^ 2 * z - w ^ 2‖ ≤ a ^ 2 * (C₁ * (u * r)) :=
    mul_le_mul_of_nonneg_left hnumbound (by positivity)
  have hB : a ^ 2 * (C₁ * (u * r)) / ‖z‖ ≤ a ^ 2 * (C₁ * (u * r)) / (q * u ^ 2 / 2) :=
    div_le_div_of_nonneg_left (by positivity) hqu hznorm
  refine le_trans (le_trans (div_le_div_of_nonneg_right hA (norm_nonneg z)) hB) (le_of_eq ?_)
  rw [← hrsq]
  field_simp

end

end RHTower
