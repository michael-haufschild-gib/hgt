import GaloisForLFunctions.RHTower.XiMassCausticNullJet
import GaloisForLFunctions.RHTower.XiMassSpacelikeContourOptimality

/-!
# The caustic symbol of the jet operator

Along the Bessel dispersion relation the caustic-null jet is the real polynomial
`(x² + 4a⁴)^{2N}`, so under the height Fourier transform it is the differential operator
`(4a⁴ − ∂_h²)^{2N}`.  Its *symbol* on the exterior Bessel carrier `e^{-a z}`, `z² = τ² + h²`, is

`4a⁴ − a²h²/z²`,

because `∂_h(-a z) = -a h/z`.  At the balance slope this symbol vanishes: the sharp slope satisfies
`κ_B² = 4a²/(4a²−1)`, hence `κ_B²/(κ_B²−1) = 4a²`, and on the light-cone limit `z² ~ (κ_B²−1)u²`
one gets `a²h²/z² = a²κ_B²/(κ_B²−1) = 4a⁴`.  That exact cancellation is the analytic reason a
caustic-null jet raises the transport power.

Quantitatively the cancellation is not exact off the limit, and the residue is computed in closed
form:

`4a²z² − h² = 4a²σ² + 8ia²σu + (4a²−1)(2κ_B u s + s²)`,  `h = κ_B u + s`.

On the window `|s| ≤ √u` the right-hand side is `O(u^{3/2})` while `|z²| ≫ u²`, so the symbol is
`O(u^{-1/2})` — one half-power of the height per application of the operator, which is exactly the
gain the jet hierarchy claims.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The sharp slope -/

theorem xiMassSpacelikeSharpSlope_sq {a : ℝ} (ha : 1 / 2 < a) :
    xiMassSpacelikeSharpSlope a ^ (2 : ℕ) = 4 * a ^ (2 : ℕ) / (4 * a ^ (2 : ℕ) - 1) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hpos : (0 : ℝ) < a ^ (2 : ℕ) - 1 / 4 := by nlinarith
  have hs : Real.sqrt (a ^ (2 : ℕ) - 1 / 4) ^ (2 : ℕ) = a ^ (2 : ℕ) - 1 / 4 := Real.sq_sqrt hpos.le
  have hden : (0 : ℝ) < 4 * a ^ (2 : ℕ) - 1 := by nlinarith
  rw [xiMassSpacelikeSharpSlope, div_pow, hs]
  field_simp

theorem xiMassSpacelikeSharpSlope_pos {a : ℝ} (ha : 1 / 2 < a) :
    0 < xiMassSpacelikeSharpSlope a := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hpos : (0 : ℝ) < a ^ (2 : ℕ) - 1 / 4 := by nlinarith
  rw [xiMassSpacelikeSharpSlope]
  exact div_pos ha0 (Real.sqrt_pos.2 hpos)

/-- `κ_B² − 1 = 1/(4a²−1)`: the exterior gap of the balance slope. -/
theorem xiMassSpacelikeSharpSlope_sq_sub_one {a : ℝ} (ha : 1 / 2 < a) :
    xiMassSpacelikeSharpSlope a ^ (2 : ℕ) - 1 = 1 / (4 * a ^ (2 : ℕ) - 1) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 4 * a ^ (2 : ℕ) - 1 := by nlinarith
  rw [xiMassSpacelikeSharpSlope_sq ha]
  field_simp
  ring

/-! ## The symbol and its residue -/

/-- The caustic symbol of the jet operator on the exterior Bessel carrier. -/
def xiMassCausticSymbol (a sigma u h : ℝ) : ℂ :=
  4 * (a : ℂ) ^ (4 : ℕ)
    - (a : ℂ) ^ (2 : ℕ) * (h : ℂ) ^ (2 : ℕ) / xiMassSpacelikePropagationArgument sigma u h

/-- **The closed residue of the caustic symbol.**  At the balance slope the leading `u²` terms
cancel identically, leaving only the damping and the window displacement. -/
theorem xiMassCausticSymbol_residue {a sigma u s : ℝ} (ha : 1 / 2 < a) :
    4 * (a : ℂ) ^ (2 : ℕ)
        * xiMassSpacelikePropagationArgument sigma u (xiMassSpacelikeSharpSlope a * u + s)
      - ((xiMassSpacelikeSharpSlope a * u + s : ℝ) : ℂ) ^ (2 : ℕ)
      = 4 * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) ^ (2 : ℕ)
        + 8 * Complex.I * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) * (u : ℂ)
        + (4 * (a : ℂ) ^ (2 : ℕ) - 1)
          * (2 * ((xiMassSpacelikeSharpSlope a : ℝ) : ℂ) * (u : ℂ) * (s : ℂ) + (s : ℂ) ^ (2 : ℕ)) := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 4 * a ^ (2 : ℕ) - 1 := by nlinarith
  have hkey : (4 * a ^ (2 : ℕ) - 1) * xiMassSpacelikeSharpSlope a ^ (2 : ℕ) = 4 * a ^ (2 : ℕ) := by
    rw [xiMassSpacelikeSharpSlope_sq ha]
    field_simp
  have hkeyC : (4 * (a : ℂ) ^ (2 : ℕ) - 1) * ((xiMassSpacelikeSharpSlope a : ℝ) : ℂ) ^ (2 : ℕ)
      = 4 * (a : ℂ) ^ (2 : ℕ) := by
    have := congrArg (fun t : ℝ => ((t : ℝ) : ℂ)) hkey
    push_cast at this
    linear_combination this
  rw [xiMassSpacelikePropagationArgument_eq]
  push_cast
  linear_combination ((u : ℂ) ^ (2 : ℕ)) * hkeyC + Complex.I_sq * (4 * (a : ℂ) ^ (2 : ℕ) * (u : ℂ) ^ (2 : ℕ))

set_option maxHeartbeats 1000000 in
/-- **The caustic symbol is `O(u^{-1/2})` on the square-root window.**  One half power of the height
per application of the jet operator — the analytic content of the caustic-null hierarchy. -/
theorem exists_norm_xiMassCausticSymbol_le {a sigma : ℝ} (ha : 1 / 2 < a) (hsigma : 0 < sigma) :
    ∃ C u₀ : ℝ, 0 < C ∧ 1 ≤ u₀ ∧ ∀ u : ℝ, u₀ ≤ u → ∀ s : ℝ, |s| ≤ Real.sqrt u →
      ‖xiMassCausticSymbol a sigma u (xiMassSpacelikeSharpSlope a * u + s)‖
        ≤ C / Real.sqrt u := by
  have ha0 : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hden : (0 : ℝ) < 4 * a ^ (2 : ℕ) - 1 := by nlinarith
  set κ : ℝ := xiMassSpacelikeSharpSlope a with hκdef
  have hκ1 : 1 < κ := one_lt_xiMassSpacelikeSharpSlope ha
  have hκ0 : (0 : ℝ) < κ := by linarith
  set q : ℝ := κ ^ (2 : ℕ) - 1 with hqdef
  have hq0 : (0 : ℝ) < q := by rw [hqdef]; nlinarith
  set C₁ : ℝ := 12 * a ^ (2 : ℕ) + (4 * a ^ (2 : ℕ) - 1) * (2 * κ + 1) with hC₁def
  have hC₁0 : (0 : ℝ) < C₁ := by rw [hC₁def]; positivity
  refine ⟨2 * a ^ (2 : ℕ) * C₁ / q, max (max 1 (sigma ^ (2 : ℕ))) ((4 * κ / q) ^ (2 : ℕ)), by positivity,
    le_trans (le_max_left 1 (sigma ^ (2 : ℕ))) (le_max_left _ _), ?_⟩
  intro u hu s hs
  have hu1 : (1 : ℝ) ≤ u := le_trans (le_trans (le_max_left 1 (sigma ^ (2 : ℕ))) (le_max_left _ _)) hu
  have huσ : sigma ^ (2 : ℕ) ≤ u := le_trans (le_trans (le_max_right 1 (sigma ^ (2 : ℕ))) (le_max_left _ _)) hu
  have huκ : (4 * κ / q) ^ (2 : ℕ) ≤ u := le_trans (le_max_right _ _) hu
  have hu0 : (0 : ℝ) < u := by linarith
  set r : ℝ := Real.sqrt u with hrdef
  have hr0 : (0 : ℝ) < r := Real.sqrt_pos.2 hu0
  have hrsq : r ^ (2 : ℕ) = u := Real.sq_sqrt hu0.le
  have hr1 : (1 : ℝ) ≤ r := by nlinarith
  have hσr : sigma ≤ r := by
    have h1 : Real.sqrt (sigma ^ (2 : ℕ)) ≤ Real.sqrt u := Real.sqrt_le_sqrt huσ
    rwa [Real.sqrt_sq hsigma.le] at h1
  have hsr : |s| ≤ r := hs
  have hs2 : s ^ (2 : ℕ) ≤ u := by nlinarith [abs_nonneg s, sq_abs s]
  have hur : u ≤ u * r := by nlinarith
  -- the shifted height and its propagation argument
  set h : ℝ := κ * u + s with hhdef
  set z : ℂ := xiMassSpacelikePropagationArgument sigma u h with hzdef
  have hzre : z.re = sigma ^ (2 : ℕ) + h ^ (2 : ℕ) - u ^ (2 : ℕ) := by
    rw [hzdef, xiMassSpacelikePropagationArgument_re, xiMassSpacelikeTrace]
  have hqr : 4 * κ ≤ q * r := by
    have hskey : 4 * κ / q ≤ r := by
      nlinarith [div_nonneg (by positivity : (0:ℝ) ≤ 4 * κ) hq0.le]
    rw [div_le_iff₀ hq0] at hskey
    linarith
  have habsmid : |2 * κ * u * s| ≤ 2 * κ * u * r := by
    have hmul : (2 * κ * u) * |s| ≤ (2 * κ * u) * r :=
      mul_le_mul_of_nonneg_left hsr (by positivity)
    calc |2 * κ * u * s| = (2 * κ * u) * |s| := by
          rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * κ * u)]
      _ ≤ (2 * κ * u) * r := hmul
      _ = 2 * κ * u * r := by ring
  have hlin : 2 * κ * u * r ≤ q * u ^ (2 : ℕ) / 2 := by
    have hprod : 4 * κ * r ^ (3 : ℕ) ≤ (q * r) * r ^ (3 : ℕ) :=
      mul_le_mul_of_nonneg_right hqr (by positivity)
    have e1 : 2 * κ * u * r = 2 * κ * r ^ (3 : ℕ) := by rw [← hrsq]; ring
    have e2 : q * u ^ (2 : ℕ) / 2 = q * r ^ (4 : ℕ) / 2 := by rw [← hrsq]; ring
    rw [e1, e2]
    nlinarith [hprod]
  have hlow : q * u ^ (2 : ℕ) / 2 ≤ z.re := by
    rw [hzre, hhdef]
    have hexp : sigma ^ (2 : ℕ) + (κ * u + s) ^ (2 : ℕ) - u ^ (2 : ℕ)
        = sigma ^ (2 : ℕ) + q * u ^ (2 : ℕ) + 2 * κ * u * s + s ^ (2 : ℕ) := by
      rw [hqdef]; ring
    rw [hexp]
    have hmid := (abs_le.mp habsmid).1
    nlinarith [sq_nonneg sigma, sq_nonneg s, hlin, hmid]
  have hqu : (0 : ℝ) < q * u ^ (2 : ℕ) / 2 := by positivity
  have hzre0 : (0 : ℝ) < z.re := lt_of_lt_of_le hqu hlow
  have hzne : z ≠ 0 := by
    intro hcon
    rw [hcon] at hzre0
    simp at hzre0
  have hznorm : q * u ^ (2 : ℕ) / 2 ≤ ‖z‖ :=
    le_trans hlow (le_trans (le_abs_self _) (Complex.abs_re_le_norm z))
  -- the symbol as a quotient
  have hsymb : xiMassCausticSymbol a sigma u h
      = (a : ℂ) ^ (2 : ℕ) * (4 * (a : ℂ) ^ (2 : ℕ) * z - (h : ℂ) ^ (2 : ℕ)) / z := by
    rw [xiMassCausticSymbol, ← hzdef]
    field_simp
  have hnum := xiMassCausticSymbol_residue (a := a) (sigma := sigma) (u := u) (s := s) ha
  rw [← hκdef, ← hhdef, ← hzdef] at hnum
  -- the numerator is `O(u·√u)`
  have hnumbound : ‖4 * (a : ℂ) ^ (2 : ℕ) * z - (h : ℂ) ^ (2 : ℕ)‖ ≤ C₁ * (u * r) := by
    rw [hnum]
    have h1 : ‖4 * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) ^ (2 : ℕ)‖ = 4 * a ^ (2 : ℕ) * sigma ^ (2 : ℕ) := by
      rw [show (4 : ℂ) * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) ^ (2 : ℕ)
          = ((4 * a ^ (2 : ℕ) * sigma ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h2 : ‖8 * Complex.I * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) * (u : ℂ)‖ = 8 * a ^ (2 : ℕ) * sigma * u := by
      rw [show (8 : ℂ) * Complex.I * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) * (u : ℂ)
          = Complex.I * ((8 * a ^ (2 : ℕ) * sigma * u : ℝ) : ℂ) by push_cast; ring,
        norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
    have h3 : ‖(4 * (a : ℂ) ^ (2 : ℕ) - 1) * (2 * ((κ : ℝ) : ℂ) * (u : ℂ) * (s : ℂ) + (s : ℂ) ^ (2 : ℕ))‖
        = (4 * a ^ (2 : ℕ) - 1) * |2 * κ * u * s + s ^ (2 : ℕ)| := by
      rw [show ((4 : ℂ) * (a : ℂ) ^ (2 : ℕ) - 1) * (2 * ((κ : ℝ) : ℂ) * (u : ℂ) * (s : ℂ) + (s : ℂ) ^ (2 : ℕ))
          = ((4 * a ^ (2 : ℕ) - 1 : ℝ) : ℂ) * ((2 * κ * u * s + s ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; ring,
        norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos hden]
    have habs3 : |2 * κ * u * s + s ^ (2 : ℕ)| ≤ 2 * κ * u * r + u := by
      have hB : |s ^ (2 : ℕ)| ≤ u := by rw [abs_of_nonneg (sq_nonneg s)]; exact hs2
      calc |2 * κ * u * s + s ^ (2 : ℕ)| ≤ |2 * κ * u * s| + |s ^ (2 : ℕ)| := abs_add_le _ _
        _ ≤ 2 * κ * u * r + u := by linarith [habsmid, hB]
    have htwo := norm_add_le (4 * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) ^ (2 : ℕ))
      (8 * Complex.I * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) * (u : ℂ))
    rw [h1, h2] at htwo
    have hmul3 : (4 * a ^ (2 : ℕ) - 1) * |2 * κ * u * s + s ^ (2 : ℕ)|
        ≤ (4 * a ^ (2 : ℕ) - 1) * (2 * κ * u * r + u) :=
      mul_le_mul_of_nonneg_left habs3 (by linarith)
    have hsplit := norm_add_le
      (4 * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) ^ (2 : ℕ)
        + 8 * Complex.I * (a : ℂ) ^ (2 : ℕ) * (sigma : ℂ) * (u : ℂ))
      ((4 * (a : ℂ) ^ (2 : ℕ) - 1) * (2 * ((κ : ℝ) : ℂ) * (u : ℂ) * (s : ℂ) + (s : ℂ) ^ (2 : ℕ)))
    rw [h3] at hsplit
    have e1 : 4 * a ^ (2 : ℕ) * sigma ^ (2 : ℕ) ≤ 4 * a ^ (2 : ℕ) * (u * r) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have e2 : 8 * a ^ (2 : ℕ) * sigma * u ≤ 8 * a ^ (2 : ℕ) * (u * r) := by
      have hstep : sigma * u ≤ r * u := mul_le_mul_of_nonneg_right hσr hu0.le
      nlinarith [hstep]
    have hin : 2 * κ * u * r + u ≤ (2 * κ + 1) * (u * r) := by nlinarith [hur]
    have e3 : (4 * a ^ (2 : ℕ) - 1) * (2 * κ * u * r + u)
        ≤ (4 * a ^ (2 : ℕ) - 1) * (2 * κ + 1) * (u * r) := by
      have := mul_le_mul_of_nonneg_left hin (le_of_lt hden)
      nlinarith [this]
    rw [hC₁def]
    linarith [hsplit, htwo, hmul3, e1, e2, e3]
  -- assemble
  rw [hsymb, norm_div, norm_mul]
  have hanorm : ‖(a : ℂ) ^ (2 : ℕ)‖ = a ^ (2 : ℕ) := by
    rw [show ((a : ℂ)) ^ (2 : ℕ) = ((a ^ (2 : ℕ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg a)]
  rw [hanorm]
  have hA : a ^ (2 : ℕ) * ‖4 * (a : ℂ) ^ (2 : ℕ) * z - (h : ℂ) ^ (2 : ℕ)‖ ≤ a ^ (2 : ℕ) * (C₁ * (u * r)) :=
    mul_le_mul_of_nonneg_left hnumbound (by positivity)
  have hB : a ^ (2 : ℕ) * (C₁ * (u * r)) / ‖z‖ ≤ a ^ (2 : ℕ) * (C₁ * (u * r)) / (q * u ^ (2 : ℕ) / 2) :=
    div_le_div_of_nonneg_left (by positivity) hqu hznorm
  refine le_trans (le_trans (div_le_div_of_nonneg_right hA (norm_nonneg z)) hB) (le_of_eq ?_)
  rw [← hrsq]
  field_simp

end

end RHTower
