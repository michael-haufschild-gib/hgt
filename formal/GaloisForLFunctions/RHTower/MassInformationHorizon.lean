import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The square-root mass information horizon

For a Poisson point `α = R + iJ` and a mass `a`, the shifted frequency `β_a = √(α² + a²) = M + iK`
obeys the two exact elementary relations

`|K| M = R |J|`,   `a ≤ M ≤ a + R`.

At the critical time `τ = σ + iu` the dominant member of the line-conjugate pair has logarithmic
magnitude `E = u|K| − σM = uR|J|/M − σM`, and the reverse member is smaller by exactly
`e^{-2u|K|}`.  The two bounds on `M` therefore sandwich `E` between the two explicit profiles
`uR|J|/a − σa` and `uR|J|/(a+R) − σ(a+R)`, whose signs flip across `a ≍ √u`:

*  `σ a² > u R |J|` forces `E < 0` — every fixed off-line orbit is extinguished;
*  `u R |J| > σ (a+R)²` forces `E > 0` — every fixed off-line orbit stays visible.

The transition constant is `c² = R|J|/σ`.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The exact orbit relations -/

/-- **(24.93)** For a mass-shifted frequency `β = M + iK` with `β² = α² + a²`, the transverse and
longitudinal parts satisfy `|K| M = R|J|` and `a ≤ M ≤ a + R`. -/
theorem massOrbit_bounds {R J a M K : ℝ} (hR : 0 < R) (hJ : J ≠ 0) (hRJ : |J| ≤ R)
    (ha : 0 ≤ a) (hM : 0 < M)
    (hsq : M ^ (2 : ℕ) - K ^ (2 : ℕ) = R ^ (2 : ℕ) - J ^ (2 : ℕ) + a ^ (2 : ℕ)) (hprod : M * K = R * J) :
    |K| * M = R * |J| ∧ a ≤ M ∧ M ≤ a + R := by
  have hJ2 : 0 < J ^ (2 : ℕ) := by positivity
  have hRJ2 : J ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by nlinarith [abs_nonneg J, sq_abs J]
  have habs : |K| * M = R * |J| := by
    have h1 : |K| * M = |K * M| := by
      rw [abs_mul, abs_of_pos hM]
    have h2 : |K * M| = |R * J| := by
      rw [mul_comm K M, hprod]
    rw [h1, h2, abs_mul, abs_of_pos hR]
  -- the quartic relation `M²(M² − R² + J² − a²) = R²J²`
  have hquart : M ^ (2 : ℕ) * (M ^ (2 : ℕ) - R ^ (2 : ℕ) + J ^ (2 : ℕ) - a ^ (2 : ℕ)) = R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
    have hK : M ^ (2 : ℕ) * K ^ (2 : ℕ) = R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
      rw [← mul_pow, ← mul_pow, hprod]
    nlinarith [hsq, hK]
  have hposFactor : 0 < M ^ (2 : ℕ) - R ^ (2 : ℕ) + J ^ (2 : ℕ) - a ^ (2 : ℕ) := by
    by_contra hcon
    have hle : M ^ (2 : ℕ) - R ^ (2 : ℕ) + J ^ (2 : ℕ) - a ^ (2 : ℕ) ≤ 0 := not_lt.mp hcon
    nlinarith [sq_nonneg M, hquart, mul_pos (mul_pos hR hR) hJ2]
  have hlow : a ≤ M := by
    have hkey2 : (M ^ (2 : ℕ) - a ^ (2 : ℕ)) * (M ^ (2 : ℕ) - R ^ (2 : ℕ) + J ^ (2 : ℕ))
        = (R ^ (2 : ℕ) - J ^ (2 : ℕ)) * a ^ (2 : ℕ) + R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
      linear_combination hquart
    have hrhs : 0 ≤ (R ^ (2 : ℕ) - J ^ (2 : ℕ)) * a ^ (2 : ℕ) + R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
      nlinarith [hRJ2, sq_nonneg a, hJ2, hR]
    have hpos2 : 0 < M ^ (2 : ℕ) - R ^ (2 : ℕ) + J ^ (2 : ℕ) := by nlinarith [hposFactor, sq_nonneg a]
    have hM2 : a ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by nlinarith [hkey2, hrhs, hpos2]
    nlinarith [hM, ha]
  have hhigh : M ≤ a + R := by
    have haR : 0 < a + R := by linarith
    have haRnn : 0 ≤ a * R := mul_nonneg ha hR.le
    have hkey : ((a + R) ^ (2 : ℕ) - M ^ (2 : ℕ)) * (2 * a * R + M ^ (2 : ℕ) + J ^ (2 : ℕ))
        = (a + R) ^ (2 : ℕ) * (2 * a * R + J ^ (2 : ℕ)) - R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
      linear_combination -hquart
    have hfs : 0 ≤ (a + R) ^ (2 : ℕ) * (2 * a * R + J ^ (2 : ℕ)) - R ^ (2 : ℕ) * J ^ (2 : ℕ) := by
      nlinarith [haRnn, hJ2, hR, ha, sq_nonneg (a + R)]
    have hfactor : 0 < 2 * a * R + M ^ (2 : ℕ) + J ^ (2 : ℕ) := by nlinarith [haRnn, sq_nonneg M, hJ2]
    have hM2 : M ^ (2 : ℕ) ≤ (a + R) ^ (2 : ℕ) := by nlinarith [hkey, hfs, hfactor]
    nlinarith [hM, haR]
  exact ⟨habs, hlow, hhigh⟩

/-! ## The critical exponent of the orbit -/

/-- **(24.94)** The logarithmic magnitude `E = uR|J|/M − σM` of the dominant conjugate member. -/
def massOrbitExponent (sigma u R J M : ℝ) : ℝ := u * (R * |J|) / M - sigma * M

/-- **(24.96)** The erasure bound: `M ≥ a` pushes the exponent below the `a`-profile. -/
theorem massOrbitExponent_le {sigma u R J a M : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u)
    (hR : 0 < R) (ha : 0 < a) (haM : a ≤ M) :
    massOrbitExponent sigma u R J M ≤ u * (R * |J|) / a - sigma * a := by
  have hM : 0 < M := lt_of_lt_of_le ha haM
  have h1 : u * (R * |J|) / M ≤ u * (R * |J|) / a :=
    div_le_div_of_nonneg_left (by positivity) ha haM
  have h2 : sigma * a ≤ sigma * M := mul_le_mul_of_nonneg_left haM hsigma.le
  rw [massOrbitExponent]
  linarith

/-- **(24.97)** The faithfulness bound: `M ≤ a + R` pushes the exponent above the
`(a+R)`-profile. -/
theorem le_massOrbitExponent {sigma u R J a M : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u)
    (hR : 0 < R) (ha : 0 < a) (hM : 0 < M) (hMa : M ≤ a + R) :
    u * (R * |J|) / (a + R) - sigma * (a + R) ≤ massOrbitExponent sigma u R J M := by
  have haR : 0 < a + R := by linarith
  have h1 : u * (R * |J|) / (a + R) ≤ u * (R * |J|) / M :=
    div_le_div_of_nonneg_left (by positivity) hM hMa
  have h2 : sigma * M ≤ sigma * (a + R) := mul_le_mul_of_nonneg_left hMa hsigma.le
  rw [massOrbitExponent]
  linarith

/-- **(24.99) Erasure half of the phase diagram.**  A mass well above `√u` extinguishes the
orbit. -/
theorem massOrbitExponent_neg {sigma u R J a M : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u)
    (hR : 0 < R) (ha : 0 < a) (haM : a ≤ M) (hphase : u * (R * |J|) < sigma * a ^ (2 : ℕ)) :
    massOrbitExponent sigma u R J M < 0 := by
  refine lt_of_le_of_lt (massOrbitExponent_le hsigma hu hR ha haM) ?_
  rw [sub_neg, div_lt_iff₀ ha]
  nlinarith

/-- **(24.99) Faithfulness half of the phase diagram.**  A mass well below `√u` keeps the orbit
visible. -/
theorem massOrbitExponent_pos {sigma u R J a M : ℝ} (hsigma : 0 < sigma) (hu : 0 ≤ u)
    (hR : 0 < R) (ha : 0 < a) (hM : 0 < M) (hMa : M ≤ a + R)
    (hphase : sigma * (a + R) ^ (2 : ℕ) < u * (R * |J|)) :
    0 < massOrbitExponent sigma u R J M := by
  refine lt_of_lt_of_le ?_ (le_massOrbitExponent hsigma hu hR ha hM hMa)
  have haR : 0 < a + R := by linarith
  rw [sub_pos, lt_div_iff₀ haR]
  nlinarith

/-- **(24.98) The transition constant.**  At `a = c√u` the leading coefficient of the exponent
vanishes exactly when `σ c² = R|J|`. -/
theorem massOrbit_transition {sigma R J c : ℝ} (hc : 0 < c) :
    R * |J| / c - sigma * c = 0 ↔ sigma * c ^ (2 : ℕ) = R * |J| := by
  rw [sub_eq_zero, div_eq_iff (ne_of_gt hc)]
  constructor <;> intro h <;> nlinarith

/-! ## The conjugate pair cannot cancel the exponent -/

/-- The relative size of a perturbation controls the relative size of the norm. -/
theorem abs_norm_add_div_sub_one_le {z w : ℂ} (hz : z ≠ 0) :
    |‖z + w‖ / ‖z‖ - 1| ≤ ‖w‖ / ‖z‖ := by
  have hzn : (0 : ℝ) < ‖z‖ := norm_pos_iff.2 hz
  have hkey : |‖z + w‖ - ‖z‖| ≤ ‖w‖ := by
    simpa using abs_norm_sub_norm_le (z + w) z
  have hrw : ‖z + w‖ / ‖z‖ - 1 = (‖z + w‖ - ‖z‖) / ‖z‖ := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hzn]
  gcongr

/-- **(24.95)** In the mass-shifted line-conjugate pair the dominant member has logarithmic
magnitude `u|K| − σM` and the reverse member is smaller by the factor `e^{-2u|K|}`. -/
theorem norm_massConjugate_exp {sigma u M K : ℝ} :
    ‖Complex.exp (-((sigma : ℂ) + (u : ℂ) * Complex.I) * ((M : ℂ) + (K : ℂ) * Complex.I))‖
      = Real.exp (u * K - sigma * M) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem norm_massConjugate_exp_reverse {sigma u M K : ℝ} :
    ‖Complex.exp (-((sigma : ℂ) + (u : ℂ) * Complex.I) * ((M : ℂ) - (K : ℂ) * Complex.I))‖
      = Real.exp (-(u * K) - sigma * M) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]
  ring

end

end RHTower
