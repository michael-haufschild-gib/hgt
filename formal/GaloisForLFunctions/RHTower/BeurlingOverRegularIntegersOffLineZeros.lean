import GaloisForLFunctions.HTGeometry.FrullaniIntegral

/-!
# Generalized integers more regular than `ℕ` with a zero off the critical line

A continuous Beurling system is given, in the logarithmic coordinate `t = log u`, by a positive
prime density `w` on `(0, ∞)`; its zeta function is `exp (∫_0^∞ e^{-st} w(t) dt)`, and its
generalized integers have the counting measure `dN` with `∫ u^{-s} dN(u) = ζ(s)`.

For parameters `1/3 < μ < 1/2` and `0 < ν < 3μ - 1`, put `p₁ = 3μ - 1 - ν`, `p₂ = 3μ - 1 + ν`
(both positive) and

```
ζ(s) = ((s - (1 - μ))² + γ²) (s + 4μ - 1) / ((s - 1)(s + p₁)(s + p₂)).
```

* **Positive primes** (`primeNumerator_nonneg`, `cexp_integral_primeDensity`). The density
  `w(t) = (e^t - 2e^{(1-μ)t} cos γt + e^{-p₁t} + e^{-p₂t} - e^{-(4μ-1)t}) / t` is nonnegative and
  `exp (∫_0^∞ e^{-st} w) = ζ(s)` for `Re s > 1` (three Frullani integrals). With `x = e^{μt}`,
  `y = e^{νt}`, the numerator is `e^{-(3μ-1)t}(2x²(1 - cos γt) + (y-1)²/y + (x-1)³(x+1)/x)`.
* **Positive integers with an exact count** (`integerDensity_nonneg`,
  `overRegularZeta_eq_one_add_integral`, `countLog`). Partial fractions give
  `ζ(s) = 1 + ρ/(s-1) + c₁/(s+p₁) + c₂/(s+p₂)`, so `dN = δ₁ + m(log u) du/u` with
  `m(t) = ρe^t + c₁e^{-p₁t} + c₂e^{-p₂t} ≥ 0` (convexity of `exp`; the slope identity
  `ρ(3μ+ν) + 2νc₁ = γ² + ν²`). The count is exactly
  `N(x) = ρx + C - (c₁/p₁)x^{-p₁} - (c₂/p₂)x^{-p₂}` for `x ≥ 1`, so `N(x) - ρx - C → 0`
  (`tendsto_count_sub`).
* **A zero off the line** (`overRegularZeta_eq_zero`). `ζ(1 - μ + iγ) = 0` with `1 - μ > 1/2`,
  and the only pole in `Re s > -p₁` is `s = 1`.
* **More regular than `ℕ`** (`not_tendsto_natFloor_sub`). For `ℕ`, `⌊x⌋ - x - C` tends to `0` for
  no constant `C`.

So a positive prime measure together with an integer count whose error tends to a constant (an
error smaller than that of the rational integers) is compatible with a zero at real part `1 - μ`,
any value in `(1/2, 2/3)`, at every height `γ`. No statement about the size of the integer-count
error decides the position of the zeros.
-/

open MeasureTheory Set Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace RHTower.BeurlingOverRegularIntegers

noncomputable section

/-! ## The prime side -/

/-- Numerator of the logarithmic prime density. -/
def primeNumerator (μ ν γ t : ℝ) : ℝ :=
  Real.exp t - 2 * Real.exp ((1 - μ) * t) * Real.cos (γ * t) +
    Real.exp (-((3 * μ - 1 - ν) * t)) + Real.exp (-((3 * μ - 1 + ν) * t)) -
      Real.exp (-((4 * μ - 1) * t))

/-- The logarithmic prime density `w(t)`. -/
def primeDensity (μ ν γ t : ℝ) : ℝ := primeNumerator μ ν γ t / t

/-- **The prime density is a sum of squares.** With `x = e^{μt} ≥ 1` and `y = e^{νt}`, the
numerator is `e^{-(3μ-1)t}(2x²(1 - cos γt) + (y-1)²/y + (x-1)³(x+1)/x)`. -/
theorem primeNumerator_nonneg {μ ν γ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 ≤ t) :
    0 ≤ primeNumerator μ ν γ t := by
  have e1 : Real.exp t = Real.exp (-((3 * μ - 1) * t)) * Real.exp (μ * t) ^ 3 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e2 : Real.exp ((1 - μ) * t) = Real.exp (-((3 * μ - 1) * t)) * Real.exp (μ * t) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have e3 : Real.exp (-((3 * μ - 1 - ν) * t)) =
      Real.exp (-((3 * μ - 1) * t)) * Real.exp (ν * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e4 : Real.exp (-((3 * μ - 1 + ν) * t)) =
      Real.exp (-((3 * μ - 1) * t)) / Real.exp (ν * t) := by
    rw [← Real.exp_sub]; congr 1; ring
  have e5 : Real.exp (-((4 * μ - 1) * t)) =
      Real.exp (-((3 * μ - 1) * t)) / Real.exp (μ * t) := by
    rw [← Real.exp_sub]; congr 1; ring
  rw [primeNumerator, e1, e2, e3, e4, e5]
  have hx1 : 1 ≤ Real.exp (μ * t) := Real.one_le_exp (mul_nonneg hμ ht)
  have hc : Real.cos (γ * t) ≤ 1 := Real.cos_le_one _
  set x := Real.exp (μ * t) with hx
  set y := Real.exp (ν * t) with hy
  set z := Real.exp (-((3 * μ - 1) * t)) with hz
  have hx0 : 0 < x := Real.exp_pos _
  have hy0 : 0 < y := Real.exp_pos _
  have hz0 : 0 < z := Real.exp_pos _
  have key : z * x ^ 3 - 2 * (z * x ^ 2) * Real.cos (γ * t) + z * y + z / y - z / x =
      z * (2 * x ^ 2 * (1 - Real.cos (γ * t)) + (y - 1) ^ 2 / y + (x - 1) ^ 3 * (x + 1) / x) := by
    field_simp
    ring
  rw [key]
  have h1 : 0 ≤ 2 * x ^ 2 * (1 - Real.cos (γ * t)) :=
    mul_nonneg (by positivity) (by linarith)
  have h2 : 0 ≤ (y - 1) ^ 2 / y := by positivity
  have h3 : 0 ≤ (x - 1) ^ 3 * (x + 1) / x :=
    div_nonneg (mul_nonneg (pow_nonneg (by linarith) 3) (by linarith)) hx0.le
  exact mul_nonneg hz0.le (add_nonneg (add_nonneg h1 h2) h3)

theorem primeDensity_nonneg {μ ν γ t : ℝ} (hμ : 0 ≤ μ) (ht : 0 < t) :
    0 ≤ primeDensity μ ν γ t :=
  div_nonneg (primeNumerator_nonneg hμ ht.le) ht.le

/-- Splitting of the weighted prime density into three Frullani integrands. -/
theorem cexp_mul_primeDensity (μ ν γ : ℝ) (s : ℂ) {t : ℝ} (ht : 0 < t) :
    Complex.exp (-(s * t)) * (primeDensity μ ν γ t : ℂ) =
      (Complex.exp (-((s - 1) * t)) - Complex.exp (-((s - (1 - μ) - γ * I) * t))) / t +
      ((Complex.exp (-((s + (3 * μ - 1 - ν)) * t)) -
          Complex.exp (-((s - (1 - μ) + γ * I) * t))) / t +
        (Complex.exp (-((s + (3 * μ - 1 + ν)) * t)) -
          Complex.exp (-((s + (4 * μ - 1)) * t))) / t) := by
  have htne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have ecos : Complex.exp (((γ : ℂ) * (t : ℂ)) * I) + Complex.exp (-(((γ : ℂ) * (t : ℂ)) * I)) =
      2 * Complex.cos ((γ : ℂ) * (t : ℂ)) := by
    rw [Complex.exp_mul_I, show -(((γ : ℂ) * (t : ℂ)) * I) = (-((γ : ℂ) * (t : ℂ))) * I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_neg, Complex.sin_neg]
    ring
  have split : ∀ c : ℂ, Complex.exp (-((s + c) * t)) =
      Complex.exp (-(s * (t : ℂ))) * Complex.exp (-(c * t)) := by
    intro c; rw [← Complex.exp_add]; ring_nf
  have e1 : Complex.exp (-((s - 1) * t)) = Complex.exp (-(s * (t : ℂ))) * Complex.exp (t : ℂ) := by
    rw [← Complex.exp_add]; ring_nf
  have e2 : Complex.exp (-((s - (1 - μ) - γ * I) * t)) =
      Complex.exp (-(s * (t : ℂ))) *
        (Complex.exp ((1 - (μ : ℂ)) * t) * Complex.exp (((γ : ℂ) * (t : ℂ)) * I)) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have e3 : Complex.exp (-((s - (1 - μ) + γ * I) * t)) =
      Complex.exp (-(s * (t : ℂ))) *
        (Complex.exp ((1 - (μ : ℂ)) * t) * Complex.exp (-(((γ : ℂ) * (t : ℂ)) * I))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have hdens : (primeDensity μ ν γ t : ℂ) =
      (Complex.exp (t : ℂ) - 2 * Complex.exp ((1 - (μ : ℂ)) * t) * Complex.cos ((γ : ℂ) * t) +
        Complex.exp (-((3 * (μ : ℂ) - 1 - ν) * t)) + Complex.exp (-((3 * (μ : ℂ) - 1 + ν) * t)) -
          Complex.exp (-((4 * (μ : ℂ) - 1) * t))) / (t : ℂ) := by
    unfold primeDensity primeNumerator
    push_cast
    ring
  rw [hdens, mul_div_assoc', ← add_div, ← add_div]
  congr 1
  rw [e1, e2, e3, split, split, split]
  linear_combination (Complex.exp (-(s * (t : ℂ))) * Complex.exp ((1 - (μ : ℂ)) * t)) * ecos

theorem re_sub_pos {s : ℂ} {a : ℝ} (ha : a ≤ 1) (hs : 1 < s.re) : 0 < (s - (a : ℂ)).re := by
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem re_add_pos {s : ℂ} {a : ℝ} (ha : 0 ≤ a) (hs : 1 < s.re) : 0 < (s + (a : ℂ)).re := by
  simp only [Complex.add_re, Complex.ofReal_re]
  linarith

/-- Laplace transform of the prime density: three Frullani integrals. -/
theorem integral_cexp_mul_primeDensity {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) (h4 : 0 ≤ 4 * μ - 1) {s : ℂ} (hs : 1 < s.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (primeDensity μ ν γ t : ℂ)) =
      (Complex.log (s - (1 - μ) - γ * I) - Complex.log (s - 1)) +
      ((Complex.log (s - (1 - μ) + γ * I) - Complex.log (s + (3 * μ - 1 - ν))) +
        (Complex.log (s + (4 * μ - 1)) - Complex.log (s + (3 * μ - 1 + ν)))) := by
  have hb : 0 < (s - (1 - μ)).re := by
    simpa using re_sub_pos (a := 1 - μ) (by linarith) hs
  have h1 : 0 < (s - 1).re := by simpa using re_sub_pos (a := 1) le_rfl hs
  have hm : 0 < (s - (1 - μ) - γ * I).re := by simpa using hb
  have hp : 0 < (s - (1 - μ) + γ * I).re := by simpa using hb
  have hl : 0 < (s + (3 * μ - 1 - ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 - ν) hlow hs
  have hh : 0 < (s + (3 * μ - 1 + ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 + ν) hhigh hs
  have hq : 0 < (s + (4 * μ - 1)).re := by
    simpa using re_add_pos (a := 4 * μ - 1) h4 hs
  have hsplit :
      (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (primeDensity μ ν γ t : ℂ)) =
        ∫ t in Ioi (0 : ℝ),
          ((Complex.exp (-((s - 1) * t)) - Complex.exp (-((s - (1 - μ) - γ * I) * t))) / t +
          ((Complex.exp (-((s + (3 * μ - 1 - ν)) * t)) -
              Complex.exp (-((s - (1 - μ) + γ * I) * t))) / t +
            (Complex.exp (-((s + (3 * μ - 1 + ν)) * t)) -
              Complex.exp (-((s + (4 * μ - 1)) * t))) / t)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t ht => cexp_mul_primeDensity μ ν γ s ht
  have hint : IntegrableOn
      (fun t : ℝ => (Complex.exp (-((s + (3 * μ - 1 - ν)) * t)) -
          Complex.exp (-((s - (1 - μ) + γ * I) * t))) / t +
        (Complex.exp (-((s + (3 * μ - 1 + ν)) * t)) -
          Complex.exp (-((s + (4 * μ - 1)) * t))) / t) (Ioi (0 : ℝ)) :=
    (integrableOn_frullani hl hp).add (integrableOn_frullani hh hq)
  rw [hsplit, integral_add (integrableOn_frullani h1 hm) hint,
    integral_add (integrableOn_frullani hl hp) (integrableOn_frullani hh hq),
    integral_frullani h1 hm, integral_frullani hl hp, integral_frullani hh hq]

/-- The rational zeta function of the system. -/
def overRegularZeta (μ ν γ : ℝ) (s : ℂ) : ℂ :=
  ((s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2) * (s + (4 * μ - 1)) /
    ((s - 1) * (s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν)))

/-- **The zeta function of the positive prime density.** -/
theorem cexp_integral_primeDensity {μ ν γ : ℝ} (hlow : 0 ≤ 3 * μ - 1 - ν)
    (hhigh : 0 ≤ 3 * μ - 1 + ν) (h4 : 0 ≤ 4 * μ - 1) {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (primeDensity μ ν γ t : ℂ)) =
      overRegularZeta μ ν γ s := by
  have hb : 0 < (s - (1 - μ)).re := by
    simpa using re_sub_pos (a := 1 - μ) (by linarith) hs
  have h1 : 0 < (s - 1).re := by simpa using re_sub_pos (a := 1) le_rfl hs
  have hl : 0 < (s + (3 * μ - 1 - ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 - ν) hlow hs
  have hh : 0 < (s + (3 * μ - 1 + ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 + ν) hhigh hs
  have hq : 0 < (s + (4 * μ - 1)).re := by
    simpa using re_add_pos (a := 4 * μ - 1) h4 hs
  have ne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  have nm : s - (1 - μ) - γ * I ≠ 0 := ne _ (by simpa using hb)
  have np : s - (1 - μ) + γ * I ≠ 0 := ne _ (by simpa using hb)
  rw [integral_cexp_mul_primeDensity hlow hhigh h4 hs, Complex.exp_add, Complex.exp_sub,
    Complex.exp_add, Complex.exp_sub, Complex.exp_sub, Complex.exp_log nm, Complex.exp_log (ne _ h1),
    Complex.exp_log np, Complex.exp_log (ne _ hl), Complex.exp_log (ne _ hq),
    Complex.exp_log (ne _ hh), overRegularZeta]
  have hfac : (s - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 = (s - (1 - μ) - γ * I) * (s - (1 - μ) + γ * I) := by
    linear_combination ((γ : ℂ) ^ 2) * Complex.I_sq
  rw [hfac]
  field_simp [ne _ h1, ne _ hl, ne _ hh]

/-! ## The integer side -/

/-- The density `ρ` of the generalized integers (residue at `s = 1`). -/
def rho (μ ν γ : ℝ) : ℝ := 4 * μ * (μ ^ 2 + γ ^ 2) / ((3 * μ - ν) * (3 * μ + ν))

/-- Residue at `s = -p₁`. -/
def lowResidue (μ ν γ : ℝ) : ℝ := -(((2 * μ - ν) ^ 2 + γ ^ 2) * (μ + ν)) / (2 * ν * (3 * μ - ν))

/-- Residue at `s = -p₂`. -/
def highResidue (μ ν γ : ℝ) : ℝ := ((2 * μ + ν) ^ 2 + γ ^ 2) * (μ - ν) / (2 * ν * (3 * μ + ν))

/-- The logarithmic integer density `m(t) = ρe^t + c₁e^{-p₁t} + c₂e^{-p₂t}`. -/
def integerDensity (μ ν γ t : ℝ) : ℝ :=
  rho μ ν γ * Real.exp t + lowResidue μ ν γ * Real.exp (-((3 * μ - 1 - ν) * t)) +
    highResidue μ ν γ * Real.exp (-((3 * μ - 1 + ν) * t))

theorem rho_mul {μ ν γ : ℝ} (h₁ : 3 * μ - ν ≠ 0) (h₂ : 3 * μ + ν ≠ 0) :
    rho μ ν γ * ((3 * μ - ν) * (3 * μ + ν)) = 4 * μ * (μ ^ 2 + γ ^ 2) :=
  div_mul_cancel₀ _ (mul_ne_zero h₁ h₂)

theorem lowResidue_mul {μ ν γ : ℝ} (hν : ν ≠ 0) (h₁ : 3 * μ - ν ≠ 0) :
    lowResidue μ ν γ * (2 * ν * (3 * μ - ν)) = -(((2 * μ - ν) ^ 2 + γ ^ 2) * (μ + ν)) :=
  div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero two_ne_zero hν) h₁)

theorem highResidue_mul {μ ν γ : ℝ} (hν : ν ≠ 0) (h₂ : 3 * μ + ν ≠ 0) :
    highResidue μ ν γ * (2 * ν * (3 * μ + ν)) = ((2 * μ + ν) ^ 2 + γ ^ 2) * (μ - ν) :=
  div_mul_cancel₀ _ (mul_ne_zero (mul_ne_zero two_ne_zero hν) h₂)

theorem residue_denom_ne_zero {μ ν : ℝ} (hν : ν ≠ 0) (h₁ : 3 * μ - ν ≠ 0) (h₂ : 3 * μ + ν ≠ 0) :
    2 * ν * ((3 * μ - ν) * (3 * μ + ν)) ≠ 0 :=
  mul_ne_zero (mul_ne_zero two_ne_zero hν) (mul_ne_zero h₁ h₂)

/-- The integer density starts at `0`: `ρ + c₁ + c₂ = 0`. -/
theorem rho_add_residues {μ ν γ : ℝ} (hν : ν ≠ 0) (h₁ : 3 * μ - ν ≠ 0) (h₂ : 3 * μ + ν ≠ 0) :
    rho μ ν γ + lowResidue μ ν γ + highResidue μ ν γ = 0 := by
  have key : (rho μ ν γ + lowResidue μ ν γ + highResidue μ ν γ) *
      (2 * ν * ((3 * μ - ν) * (3 * μ + ν))) = 0 := by
    linear_combination (2 * ν) * rho_mul (γ := γ) h₁ h₂ +
      (3 * μ + ν) * lowResidue_mul (γ := γ) hν h₁ + (3 * μ - ν) * highResidue_mul (γ := γ) hν h₂
  exact (mul_eq_zero.mp key).resolve_right (residue_denom_ne_zero hν h₁ h₂)

/-- **Slope identity**: `ρ(3μ + ν) + 2νc₁ = γ² + ν²`. -/
theorem rho_slope {μ ν γ : ℝ} (hν : ν ≠ 0) (h₁ : 3 * μ - ν ≠ 0) (h₂ : 3 * μ + ν ≠ 0) :
    rho μ ν γ * (3 * μ + ν) + 2 * ν * lowResidue μ ν γ = γ ^ 2 + ν ^ 2 := by
  have key : (rho μ ν γ * (3 * μ + ν) + 2 * ν * lowResidue μ ν γ - (γ ^ 2 + ν ^ 2)) *
      (3 * μ - ν) = 0 := by
    linear_combination rho_mul (γ := γ) h₁ h₂ + lowResidue_mul (γ := γ) hν h₁
  linarith [(mul_eq_zero.mp key).resolve_right h₁]

/-- The `s¹` coefficient of the partial fraction expansion. -/
theorem residues_coeff_one {μ ν γ : ℝ} (hν : ν ≠ 0) (h₁ : 3 * μ - ν ≠ 0) (h₂ : 3 * μ + ν ≠ 0) :
    rho μ ν γ * ((3 * μ - 1 - ν) + (3 * μ - 1 + ν)) + lowResidue μ ν γ * ((3 * μ - 1 + ν) - 1) +
        highResidue μ ν γ * ((3 * μ - 1 - ν) - 1) =
      (1 - μ) ^ 2 + γ ^ 2 - 2 * (1 - μ) * (4 * μ - 1) -
        ((3 * μ - 1 - ν) * (3 * μ - 1 + ν) - (3 * μ - 1 - ν) - (3 * μ - 1 + ν)) := by
  have key : (rho μ ν γ * ((3 * μ - 1 - ν) + (3 * μ - 1 + ν)) +
      lowResidue μ ν γ * ((3 * μ - 1 + ν) - 1) + highResidue μ ν γ * ((3 * μ - 1 - ν) - 1) -
      ((1 - μ) ^ 2 + γ ^ 2 - 2 * (1 - μ) * (4 * μ - 1) -
        ((3 * μ - 1 - ν) * (3 * μ - 1 + ν) - (3 * μ - 1 - ν) - (3 * μ - 1 + ν)))) *
      (2 * ν * ((3 * μ - ν) * (3 * μ + ν))) = 0 := by
    linear_combination (2 * ν * ((3 * μ - 1 - ν) + (3 * μ - 1 + ν))) * rho_mul (γ := γ) h₁ h₂ +
      (((3 * μ - 1 + ν) - 1) * (3 * μ + ν)) * lowResidue_mul (γ := γ) hν h₁ +
      (((3 * μ - 1 - ν) - 1) * (3 * μ - ν)) * highResidue_mul (γ := γ) hν h₂
  linarith [(mul_eq_zero.mp key).resolve_right (residue_denom_ne_zero hν h₁ h₂)]

/-- The `s⁰` coefficient of the partial fraction expansion. -/
theorem residues_coeff_zero {μ ν γ : ℝ} (hν : ν ≠ 0) (h₁ : 3 * μ - ν ≠ 0) (h₂ : 3 * μ + ν ≠ 0) :
    rho μ ν γ * ((3 * μ - 1 - ν) * (3 * μ - 1 + ν)) - lowResidue μ ν γ * (3 * μ - 1 + ν) -
        highResidue μ ν γ * (3 * μ - 1 - ν) =
      (4 * μ - 1) * ((1 - μ) ^ 2 + γ ^ 2) + (3 * μ - 1 - ν) * (3 * μ - 1 + ν) := by
  have key : (rho μ ν γ * ((3 * μ - 1 - ν) * (3 * μ - 1 + ν)) -
      lowResidue μ ν γ * (3 * μ - 1 + ν) - highResidue μ ν γ * (3 * μ - 1 - ν) -
      ((4 * μ - 1) * ((1 - μ) ^ 2 + γ ^ 2) + (3 * μ - 1 - ν) * (3 * μ - 1 + ν))) *
      (2 * ν * ((3 * μ - ν) * (3 * μ + ν))) = 0 := by
    linear_combination (2 * ν * ((3 * μ - 1 - ν) * (3 * μ - 1 + ν))) * rho_mul (γ := γ) h₁ h₂ -
      ((3 * μ - 1 + ν) * (3 * μ + ν)) * lowResidue_mul (γ := γ) hν h₁ -
      ((3 * μ - 1 - ν) * (3 * μ - ν)) * highResidue_mul (γ := γ) hν h₂
  linarith [(mul_eq_zero.mp key).resolve_right (residue_denom_ne_zero hν h₁ h₂)]

/-- Convexity of `exp` between `0` and `pt`: `p(e^{qt} - 1) ≤ q(e^{pt} - 1)` for `0 < q ≤ p`. -/
theorem mul_exp_sub_one_le {p q t : ℝ} (hq : 0 < q) (hqp : q ≤ p) :
    p * (Real.exp (q * t) - 1) ≤ q * (Real.exp (p * t) - 1) := by
  have hp : 0 < p := lt_of_lt_of_le hq hqp
  have hc := div_mul_cancel₀ q hp.ne'
  have hconv := convexOn_exp.2 (Set.mem_univ (p * t)) (Set.mem_univ (0 : ℝ))
    (div_nonneg hq.le hp.le) (by rw [sub_nonneg, div_le_one hp]; exact hqp)
    (show q / p + (1 - q / p) = 1 by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have hqt : q / p * (p * t) = q * t := by linear_combination t * hc
  rw [hqt] at hconv
  have := mul_le_mul_of_nonneg_left hconv hp.le
  have hpq : p * (q / p * Real.exp (p * t) + (1 - q / p)) = q * Real.exp (p * t) + (p - q) := by
    linear_combination (Real.exp (p * t) - 1) * hc
  rw [hpq] at this
  linarith

theorem rho_nonneg {μ ν γ : ℝ} (hμ : 0 ≤ μ) (hν : 0 ≤ ν) (hνμ : ν < 3 * μ) :
    0 ≤ rho μ ν γ :=
  div_nonneg (by positivity) (mul_nonneg (by linarith) (by linarith))

/-- **The integer density is nonnegative.** After multiplying by `e^{p₂t}` it is
`ρ(e^{(3μ+ν)t} - 1) + c₁(e^{2νt} - 1)`, and convexity of `exp` with the slope identity bounds it
below by `(γ² + ν²)(e^{2νt} - 1)/(2ν)`. -/
theorem integerDensity_nonneg {μ ν γ t : ℝ} (hμ : 0 ≤ μ) (hν : 0 < ν) (hνμ : ν < 3 * μ)
    (ht : 0 ≤ t) : 0 ≤ integerDensity μ ν γ t := by
  have hν0 : ν ≠ 0 := hν.ne'
  have h₁ : 3 * μ - ν ≠ 0 := by linarith
  have h₂ : 3 * μ + ν ≠ 0 := by linarith
  have hsum := rho_add_residues (γ := γ) hν0 h₁ h₂
  have hslope := rho_slope (γ := γ) hν0 h₁ h₂
  have hρ := rho_nonneg (γ := γ) hμ hν.le hνμ
  have hconv := mul_exp_sub_one_le (t := t) (by linarith : 0 < 2 * ν)
    (by linarith : 2 * ν ≤ 3 * μ + ν)
  have hX : 1 ≤ Real.exp (2 * ν * t) := Real.one_le_exp (by positivity)
  have e1 : Real.exp t = Real.exp (-((3 * μ - 1 + ν) * t)) * Real.exp ((3 * μ + ν) * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-((3 * μ - 1 - ν) * t)) =
      Real.exp (-((3 * μ - 1 + ν) * t)) * Real.exp (2 * ν * t) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE : 0 < Real.exp (-((3 * μ - 1 + ν) * t)) := Real.exp_pos _
  have hform : integerDensity μ ν γ t = Real.exp (-((3 * μ - 1 + ν) * t)) *
      (rho μ ν γ * (Real.exp ((3 * μ + ν) * t) - 1) +
        lowResidue μ ν γ * (Real.exp (2 * ν * t) - 1)) := by
    rw [integerDensity, e1, e2]
    have hc₂ : highResidue μ ν γ = -(rho μ ν γ + lowResidue μ ν γ) := by linarith
    rw [hc₂]
    ring
  rw [hform]
  refine mul_nonneg hE.le ?_
  -- `2ν · [ρ(E - 1) + c₁(X - 1)] ≥ (ρ(3μ+ν) + 2νc₁)(X - 1) = (γ² + ν²)(X - 1) ≥ 0`.
  have hmul := mul_le_mul_of_nonneg_left hconv hρ
  have hkey : 2 * ν * (rho μ ν γ * (Real.exp ((3 * μ + ν) * t) - 1) +
      lowResidue μ ν γ * (Real.exp (2 * ν * t) - 1)) - (γ ^ 2 + ν ^ 2) * (Real.exp (2 * ν * t) - 1) =
      rho μ ν γ * (2 * ν * (Real.exp ((3 * μ + ν) * t) - 1)) -
        rho μ ν γ * ((3 * μ + ν) * (Real.exp (2 * ν * t) - 1)) := by
    rw [← hslope]; ring
  have hpos : 0 ≤ (γ ^ 2 + ν ^ 2) * (Real.exp (2 * ν * t) - 1) :=
    mul_nonneg (by positivity) (by linarith)
  have hgoal : 0 ≤ 2 * ν * (rho μ ν γ * (Real.exp ((3 * μ + ν) * t) - 1) +
      lowResidue μ ν γ * (Real.exp (2 * ν * t) - 1)) := by
    linarith
  exact (mul_nonneg_iff_of_pos_left (by linarith : (0 : ℝ) < 2 * ν)).mp hgoal

/-- **Partial fractions.** -/
theorem overRegularZeta_eq_partialFractions {μ ν γ : ℝ} (hν : ν ≠ 0) (h₁ : 3 * μ - ν ≠ 0)
    (h₂ : 3 * μ + ν ≠ 0) {s : ℂ} (hs1 : s - 1 ≠ 0) (hsl : s + (3 * μ - 1 - ν) ≠ 0)
    (hsh : s + (3 * μ - 1 + ν) ≠ 0) :
    overRegularZeta μ ν γ s = 1 + (rho μ ν γ : ℂ) / (s - 1) +
      (lowResidue μ ν γ : ℂ) / (s + (3 * μ - 1 - ν)) +
        (highResidue μ ν γ : ℂ) / (s + (3 * μ - 1 + ν)) := by
  have e0 : (rho μ ν γ : ℂ) + lowResidue μ ν γ + highResidue μ ν γ = 0 := by
    exact_mod_cast rho_add_residues (γ := γ) hν h₁ h₂
  have e1 := residues_coeff_one (γ := γ) hν h₁ h₂
  have e2 := residues_coeff_zero (γ := γ) hν h₁ h₂
  have e1c : (rho μ ν γ : ℂ) * ((3 * μ - 1 - ν) + (3 * μ - 1 + ν)) +
        (lowResidue μ ν γ : ℂ) * ((3 * μ - 1 + ν) - 1) +
        (highResidue μ ν γ : ℂ) * ((3 * μ - 1 - ν) - 1) =
      (1 - μ) ^ 2 + (γ : ℂ) ^ 2 - 2 * (1 - μ) * (4 * μ - 1) -
        ((3 * μ - 1 - ν) * (3 * μ - 1 + ν) - (3 * μ - 1 - ν) - (3 * μ - 1 + ν)) := by
    exact_mod_cast e1
  have e2c : (rho μ ν γ : ℂ) * ((3 * μ - 1 - ν) * (3 * μ - 1 + ν)) -
        (lowResidue μ ν γ : ℂ) * (3 * μ - 1 + ν) - (highResidue μ ν γ : ℂ) * (3 * μ - 1 - ν) =
      (4 * μ - 1) * ((1 - μ) ^ 2 + (γ : ℂ) ^ 2) + (3 * μ - 1 - ν) * (3 * μ - 1 + ν) := by
    exact_mod_cast e2
  have hu := mul_inv_cancel₀ hs1
  have hv := mul_inv_cancel₀ hsl
  have hw := mul_inv_cancel₀ hsh
  rw [overRegularZeta, eq_comm, eq_div_iff (mul_ne_zero (mul_ne_zero hs1 hsl) hsh)]
  simp only [div_eq_mul_inv]
  linear_combination ((rho μ ν γ : ℂ) * (s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν))) * hu +
    ((lowResidue μ ν γ : ℂ) * (s - 1) * (s + (3 * μ - 1 + ν))) * hv +
    ((highResidue μ ν γ : ℂ) * (s - 1) * (s + (3 * μ - 1 - ν))) * hw +
    s ^ 2 * e0 + s * e1c + e2c

/-- Laplace transform of `e^{-c t}` on `(0, ∞)`. -/
theorem integral_cexp_neg_mul {c : ℂ} (hc : 0 < c.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-c * t)) = 1 / c := by
  have h := integral_exp_mul_complex_Ioi (a := -c) (by simpa using hc) 0
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero] at h
  rw [h, neg_div, div_neg, neg_neg]

theorem integrableOn_cexp_neg_mul {c : ℂ} (hc : 0 < c.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-c * t)) (Ioi (0 : ℝ)) :=
  integrableOn_exp_mul_complex_Ioi (by simpa using hc) 0

/-- **The integers are counted by `dN = δ₁ + m(t) dt`.** For `Re s > 1`,
`ζ(s) = 1 + ∫_0^∞ e^{-st} m(t) dt`. -/
theorem overRegularZeta_eq_one_add_integral {μ ν γ : ℝ} (hν : 0 < ν)
    (hlow : 0 ≤ 3 * μ - 1 - ν) {s : ℂ} (hs : 1 < s.re) :
    overRegularZeta μ ν γ s =
      1 + ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (integerDensity μ ν γ t : ℂ) := by
  have hν0 : ν ≠ 0 := hν.ne'
  have h₁ : 3 * μ - ν ≠ 0 := by linarith
  have h₂ : 3 * μ + ν ≠ 0 := by linarith
  have hhigh : 0 ≤ 3 * μ - 1 + ν := by linarith
  have h1 : 0 < (s - 1).re := by simpa using re_sub_pos (a := 1) le_rfl hs
  have hl : 0 < (s + (3 * μ - 1 - ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 - ν) hlow hs
  have hh : 0 < (s + (3 * μ - 1 + ν)).re := by
    simpa using re_add_pos (a := 3 * μ - 1 + ν) hhigh hs
  have ne : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  have hpt : ∀ t : ℝ, Complex.exp (-(s * t)) * (integerDensity μ ν γ t : ℂ) =
      (rho μ ν γ : ℂ) * Complex.exp (-(s - 1) * t) +
        ((lowResidue μ ν γ : ℂ) * Complex.exp (-(s + (3 * μ - 1 - ν)) * t) +
          (highResidue μ ν γ : ℂ) * Complex.exp (-(s + (3 * μ - 1 + ν)) * t)) := by
    intro t
    have a1 : Complex.exp (-(s - 1) * t) = Complex.exp (-(s * t)) * Complex.exp (t : ℂ) := by
      rw [← Complex.exp_add]; ring_nf
    have a2 : Complex.exp (-(s + (3 * μ - 1 - ν)) * t) =
        Complex.exp (-(s * t)) * Complex.exp (-((3 * (μ : ℂ) - 1 - ν) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    have a3 : Complex.exp (-(s + (3 * μ - 1 + ν)) * t) =
        Complex.exp (-(s * t)) * Complex.exp (-((3 * (μ : ℂ) - 1 + ν) * t)) := by
      rw [← Complex.exp_add]; ring_nf
    rw [a1, a2, a3, integerDensity]
    push_cast
    ring
  have i1 := (integrableOn_cexp_neg_mul h1).const_mul (rho μ ν γ : ℂ)
  have i2 := (integrableOn_cexp_neg_mul hl).const_mul (lowResidue μ ν γ : ℂ)
  have i3 := (integrableOn_cexp_neg_mul hh).const_mul (highResidue μ ν γ : ℂ)
  have i23 : IntegrableOn (fun t : ℝ =>
      (lowResidue μ ν γ : ℂ) * Complex.exp (-(s + (3 * μ - 1 - ν)) * t) +
        (highResidue μ ν γ : ℂ) * Complex.exp (-(s + (3 * μ - 1 + ν)) * t)) (Ioi (0 : ℝ)) :=
    i2.add i3
  simp_rw [hpt]
  rw [integral_add i1 i23, integral_add i2 i3, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_cexp_neg_mul h1, integral_cexp_neg_mul hl,
    integral_cexp_neg_mul hh,
    overRegularZeta_eq_partialFractions hν0 h₁ h₂ (ne _ h1) (ne _ hl) (ne _ hh)]
  ring

/-! ## The counting function -/

/-- The constant term `C = 1 - ρ + c₁/p₁ + c₂/p₂` of the count. -/
def countConst (μ ν γ : ℝ) : ℝ :=
  1 - rho μ ν γ + lowResidue μ ν γ / (3 * μ - 1 - ν) + highResidue μ ν γ / (3 * μ - 1 + ν)

/-- The generalized-integer count at `x = e^T`:
`N(e^T) = ρe^T + C - (c₁/p₁)e^{-p₁T} - (c₂/p₂)e^{-p₂T}`. -/
def countLog (μ ν γ T : ℝ) : ℝ :=
  rho μ ν γ * Real.exp T + countConst μ ν γ -
    lowResidue μ ν γ / (3 * μ - 1 - ν) * Real.exp (-((3 * μ - 1 - ν) * T)) -
      highResidue μ ν γ / (3 * μ - 1 + ν) * Real.exp (-((3 * μ - 1 + ν) * T))

/-- The integer `1` is counted with mass one. -/
theorem countLog_zero (μ ν γ : ℝ) : countLog μ ν γ 0 = 1 := by
  simp only [countLog, countConst, mul_zero, neg_zero, Real.exp_zero, mul_one]
  ring

theorem hasDerivAt_exp_neg_mul (p T : ℝ) :
    HasDerivAt (fun T : ℝ => Real.exp (-(p * T))) (Real.exp (-(p * T)) * (-p)) T := by
  have h := (((hasDerivAt_id' T).const_mul p).neg).exp
  rwa [mul_one] at h

/-- `N(e^T)` has derivative `m(T)`: the count is `1 + ∫_0^T m`. -/
theorem hasDerivAt_countLog {μ ν γ : ℝ} (hlow : 3 * μ - 1 - ν ≠ 0) (hhigh : 3 * μ - 1 + ν ≠ 0)
    (T : ℝ) : HasDerivAt (countLog μ ν γ) (integerDensity μ ν γ T) T := by
  have h := ((((Real.hasDerivAt_exp T).const_mul (rho μ ν γ)).add_const (countConst μ ν γ)).sub
    ((hasDerivAt_exp_neg_mul (3 * μ - 1 - ν) T).const_mul
      (lowResidue μ ν γ / (3 * μ - 1 - ν)))).sub
    ((hasDerivAt_exp_neg_mul (3 * μ - 1 + ν) T).const_mul
      (highResidue μ ν γ / (3 * μ - 1 + ν)))
  have hl := div_mul_cancel₀ (lowResidue μ ν γ) hlow
  have hh := div_mul_cancel₀ (highResidue μ ν γ) hhigh
  have hval : integerDensity μ ν γ T = rho μ ν γ * Real.exp T -
      lowResidue μ ν γ / (3 * μ - 1 - ν) *
        (Real.exp (-((3 * μ - 1 - ν) * T)) * (-(3 * μ - 1 - ν))) -
      highResidue μ ν γ / (3 * μ - 1 + ν) *
        (Real.exp (-((3 * μ - 1 + ν) * T)) * (-(3 * μ - 1 + ν))) := by
    rw [integerDensity]
    linear_combination (-Real.exp (-((3 * μ - 1 - ν) * T))) * hl -
      Real.exp (-((3 * μ - 1 + ν) * T)) * hh
  rw [hval]
  exact h

/-- The count is nondecreasing on `[0, ∞)`. -/
theorem monotoneOn_countLog {μ ν γ : ℝ} (hμ : 0 ≤ μ) (hν : 0 < ν) (hlow : 0 < 3 * μ - 1 - ν) :
    MonotoneOn (countLog μ ν γ) (Ici 0) := by
  have hhigh : 3 * μ - 1 + ν ≠ 0 := by linarith
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · exact fun T _ => (hasDerivAt_countLog hlow.ne' hhigh T).continuousAt.continuousWithinAt
  · exact fun T _ =>
      (hasDerivAt_countLog hlow.ne' hhigh T).differentiableAt.differentiableWithinAt
  · intro T hT
    rw [interior_Ici] at hT
    rw [(hasDerivAt_countLog hlow.ne' hhigh T).deriv]
    exact integerDensity_nonneg hμ hν (by linarith) (le_of_lt hT)

theorem tendsto_exp_neg_mul {p : ℝ} (hp : 0 < p) :
    Tendsto (fun T : ℝ => Real.exp (-(p * T))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun T : ℝ => p * T) atTop atTop := tendsto_id.const_mul_atTop hp
  exact Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)

/-- **The count is asymptotically exact**: `N(e^T) - ρe^T - C → 0`. -/
theorem tendsto_countLog_sub {μ ν γ : ℝ} (hlow : 0 < 3 * μ - 1 - ν) (hhigh : 0 < 3 * μ - 1 + ν) :
    Tendsto (fun T => countLog μ ν γ T - rho μ ν γ * Real.exp T - countConst μ ν γ) atTop
      (𝓝 0) := by
  have := ((tendsto_exp_neg_mul hlow).const_mul (lowResidue μ ν γ / (3 * μ - 1 - ν))).neg.sub
    ((tendsto_exp_neg_mul hhigh).const_mul (highResidue μ ν γ / (3 * μ - 1 + ν)))
  simp only [mul_zero, neg_zero, sub_zero] at this
  refine this.congr fun T => ?_
  simp only [countLog]
  ring

/-- **In the multiplicative variable**: `N(x) - ρx - C → 0` as `x → ∞`, where
`N(x) = countLog (log x)`. -/
theorem tendsto_count_sub {μ ν γ : ℝ} (hlow : 0 < 3 * μ - 1 - ν) (hhigh : 0 < 3 * μ - 1 + ν) :
    Tendsto (fun x : ℝ => countLog μ ν γ (Real.log x) - rho μ ν γ * x - countConst μ ν γ) atTop
      (𝓝 0) := by
  refine ((tendsto_countLog_sub (γ := γ) hlow hhigh).comp Real.tendsto_log_atTop).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  simp [Function.comp, Real.exp_log hx]

/-- **The rational integers are less regular**: for no constant `C` does `⌊x⌋ - x - C → 0`. -/
theorem not_tendsto_natFloor_sub (C : ℝ) :
    ¬ Tendsto (fun x : ℝ => (⌊x⌋₊ : ℝ) - x - C) atTop (𝓝 0) := by
  intro h
  have h1 : Tendsto (fun _ : ℕ => -C) atTop (𝓝 0) :=
    (h.comp tendsto_natCast_atTop_atTop).congr fun n => by simp
  have h2 : Tendsto (fun _ : ℕ => -(1 / 2) - C) atTop (𝓝 0) := by
    refine (h.comp (tendsto_atTop_add_const_right _ (1 / 2 : ℝ)
      tendsto_natCast_atTop_atTop)).congr fun n => ?_
    have hfl : ⌊(n : ℝ) + 1 / 2⌋₊ = n := by
      rw [Nat.floor_eq_iff (by positivity)]
      constructor <;> linarith
    simp only [Function.comp, hfl]
    ring
  have c1 := tendsto_nhds_unique tendsto_const_nhds h1
  have c2 := tendsto_nhds_unique tendsto_const_nhds h2
  linarith

/-! ## The zero -/

/-- **`ζ` vanishes at `1 - μ + iγ`.** -/
theorem overRegularZeta_eq_zero (μ ν γ : ℝ) :
    overRegularZeta μ ν γ ((1 - μ : ℝ) + γ * I) = 0 := by
  have hnum : (((1 - μ : ℝ) : ℂ) + γ * I - (1 - μ)) ^ 2 + (γ : ℂ) ^ 2 = 0 := by
    push_cast
    linear_combination ((γ : ℂ) ^ 2) * Complex.I_sq
  rw [overRegularZeta, hnum, zero_mul, zero_div]

/-- The denominator does not vanish at the zero, so it is a genuine zero. -/
theorem overRegularZeta_denom_ne_zero_at_zero {μ ν γ : ℝ} (hμ : 0 < μ) (hl : ν < 2 * μ)
    (hh : -2 * μ < ν) :
    (((1 - μ : ℝ) : ℂ) + γ * I - 1) * (((1 - μ : ℝ) : ℂ) + γ * I + (3 * μ - 1 - ν)) *
      (((1 - μ : ℝ) : ℂ) + γ * I + (3 * μ - 1 + ν)) ≠ 0 := by
  have hre : ∀ z : ℂ, z.re ≠ 0 → z ≠ 0 := fun z hz h => hz (by rw [h]; simp)
  refine mul_ne_zero (mul_ne_zero (hre _ ?_) (hre _ ?_)) (hre _ ?_) <;> simp <;> linarith

/-- The only pole with `Re s > -p₁` is `s = 1`. -/
theorem overRegularZeta_denom_ne_zero {μ ν : ℝ} (hν : 0 ≤ ν) {s : ℂ}
    (hs : -(3 * μ - 1 - ν) < s.re) (hne : s ≠ 1) :
    (s - 1) * (s + (3 * μ - 1 - ν)) * (s + (3 * μ - 1 + ν)) ≠ 0 := by
  have hre : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  refine mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hne) (hre _ ?_)) (hre _ ?_) <;>
    simp <;> linarith

/-! ## Summary -/

/-- **Integer regularity beyond `ℕ` does not constrain the zeros.** For `μ < 1/2`,
`0 < ν < 3μ - 1` (so `μ > 1/3`) and every `γ`, the continuous Beurling system with prime density
`primeDensity μ ν γ` has

* a nonnegative prime density whose exponential Laplace transform is `overRegularZeta`;
* a nonnegative integer density with `ζ(s) = 1 + ∫_0^∞ e^{-st} m(t) dt` (`Re s > 1`), and an
  nondecreasing integer count `N(x) = countLog (log x)` with `N(1) = 1` and `N(x) - ρx - C → 0`;
* a zero at `1 - μ + iγ`, of real part in `(1/2, 2/3)`, and no pole but `s = 1` in `Re s > -p₁`.

The rational integers satisfy no such asymptotic (`not_tendsto_natFloor_sub`). -/
theorem overRegular_integers_do_not_constrain_zeros {μ ν γ : ℝ} (hμ2 : μ < 1 / 2) (hν0 : 0 < ν)
    (hν1 : ν < 3 * μ - 1) :
    (∀ t : ℝ, 0 < t → 0 ≤ primeDensity μ ν γ t) ∧
    (∀ s : ℂ, 1 < s.re →
      Complex.exp (∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (primeDensity μ ν γ t : ℂ)) =
        overRegularZeta μ ν γ s) ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ integerDensity μ ν γ t) ∧
    (∀ s : ℂ, 1 < s.re → overRegularZeta μ ν γ s =
      1 + ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * (integerDensity μ ν γ t : ℂ)) ∧
    countLog μ ν γ 0 = 1 ∧ MonotoneOn (countLog μ ν γ) (Ici 0) ∧
    Tendsto (fun x : ℝ => countLog μ ν γ (Real.log x) - rho μ ν γ * x - countConst μ ν γ) atTop
      (𝓝 0) ∧
    overRegularZeta μ ν γ ((1 - μ : ℝ) + γ * I) = 0 ∧ 1 / 2 < 1 - μ ∧
    (((1 - μ : ℝ) : ℂ) + γ * I - 1) * (((1 - μ : ℝ) : ℂ) + γ * I + (3 * μ - 1 - ν)) *
      (((1 - μ : ℝ) : ℂ) + γ * I + (3 * μ - 1 + ν)) ≠ 0 := by
  have hμ : 0 < μ := by linarith
  have hlow : 0 < 3 * μ - 1 - ν := by linarith
  have hhigh : 0 < 3 * μ - 1 + ν := by linarith
  refine ⟨fun t ht => primeDensity_nonneg hμ.le ht,
    fun s hs => cexp_integral_primeDensity hlow.le hhigh.le (by linarith) hs,
    fun t ht => integerDensity_nonneg hμ.le hν0 (by linarith) ht,
    fun s hs => overRegularZeta_eq_one_add_integral hν0 hlow.le hs,
    countLog_zero μ ν γ, monotoneOn_countLog hμ.le hν0 hlow, tendsto_count_sub hlow hhigh, overRegularZeta_eq_zero μ ν γ,
    by linarith, overRegularZeta_denom_ne_zero_at_zero hμ (by linarith) (by linarith)⟩

end

end RHTower.BeurlingOverRegularIntegers
