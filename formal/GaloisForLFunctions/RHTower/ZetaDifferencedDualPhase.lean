import Mathlib

/-!
# The dual phase of a Weyl-differenced `ζ` sum

Weyl differencing `Σ n^{−it}` with shift `h` produces the phase `T(log(x + h) − log x)`,
`T = t/2π` (after conjugation).  Adding an integer frequency `kx` does not change `e(·)` at
integers, and makes the derivative nonnegative.  This module records the exact calculus of

  `F(x) = T(log(x + h) − log x) + kx`,
  `F′ = T((x + h)⁻¹ − x⁻¹) + k`, `F″ = T(x⁻² − (x + h)⁻²)`, `F‴ = −2T(x⁻³ − (x + h)⁻³)`,

with `2Th/(x + h)³ ≤ F″ ≤ 2Th/x³` and `|F‴| ≤ 6Th/x⁴` (`diffPhase2_ge`, `diffPhase2_le`,
`abs_diffPhase3_le`), and of its `B`-process dual.

**The dual point.**  `F′(x) = ν` means `x(x + h) = Th/u`, `u = k − ν`, solved by
`x(u) = q(u) − h/2`, `q(u) = √(Th/u + h²/4)` (`diffPhase1_dualX`).

**The dual phase.**  `Φ(ν) = F(x) − νx` has `Φ′ = −x` (the stationarity of `x` kills the inner
derivative).  The chain `G₀ = −Φ`, `G₁ = x`, `G₂, G₃, G₄` (`dualChain`) is explicit in `u`, `q`, `c = Th`:

  `G₂ = c/(2u²q)`, `G₃ = c/(u³q) − c²/(4u⁴q³)`, `G₄ = 3c/(u⁴q) − 3c²/(2u⁵q³) + 3c³/(8u⁶q⁵)`.

With `r = c/(uq²) = c/(c + h²u/4)`, `G₄ = (q/u³)(3r − 3r²/2 + 3r³/8)`, and for `hu ≤ T` (so
`r ≥ 4/5`) this gives `q/u³ ≤ G₄ ≤ 3q/u³` (`dualChain_four_bounds`).
-/

open Real

namespace RHTower

noncomputable section

/-! ## The differenced phase -/

/-- The conjugated Weyl-differenced logarithmic phase, shifted by the frequency `k`. -/
def diffPhase (T h k x : ℝ) : ℝ := T * (Real.log (x + h) - Real.log x) + k * x

/-- `F′`. -/
def diffPhase1 (T h k x : ℝ) : ℝ := T * ((x + h)⁻¹ - x⁻¹) + k

/-- `F″`. -/
def diffPhase2 (T h x : ℝ) : ℝ := T * ((x ^ 2)⁻¹ - ((x + h) ^ 2)⁻¹)

/-- `F‴`. -/
def diffPhase3 (T h x : ℝ) : ℝ := -(2 * T) * ((x ^ 3)⁻¹ - ((x + h) ^ 3)⁻¹)

theorem hasDerivAt_diffPhase {T h k x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt (diffPhase T h k) (diffPhase1 T h k x) x := by
  have hxh : 0 < x + h := by linarith
  have h1 := ((hasDerivAt_id' x).add_const h).log hxh.ne'
  have h2 := (hasDerivAt_id' x).log hx.ne'
  have h3 := ((h1.sub h2).const_mul T).add ((hasDerivAt_id' x).const_mul k)
  refine h3.congr_deriv ?_
  simp only [diffPhase1]
  field_simp

theorem hasDerivAt_diffPhase1 {T h k x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt (diffPhase1 T h k) (diffPhase2 T h x) x := by
  have hxh : 0 < x + h := by linarith
  have h1 := ((hasDerivAt_id' x).add_const h).inv hxh.ne'
  have h2 := (hasDerivAt_id' x).inv hx.ne'
  have h3 := ((h1.sub h2).const_mul T).add_const k
  refine h3.congr_deriv ?_
  simp only [diffPhase2]
  field_simp
  ring

theorem hasDerivAt_diffPhase2 {T h x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt (diffPhase2 T h) (diffPhase3 T h x) x := by
  have hxh : 0 < x + h := by linarith
  have h1 := ((hasDerivAt_id' x).fun_pow 2).inv (pow_ne_zero 2 hx.ne')
  have h2 := (((hasDerivAt_id' x).add_const h).fun_pow 2).inv (pow_ne_zero 2 hxh.ne')
  have h3 := (h1.sub h2).const_mul T
  refine h3.congr_deriv ?_
  simp only [diffPhase3]
  norm_num
  field_simp
  ring

theorem hasDerivAt_diffPhase3 {T h x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt (diffPhase3 T h) (6 * T * ((x ^ 4)⁻¹ - ((x + h) ^ 4)⁻¹)) x := by
  have hxh : 0 < x + h := by linarith
  have h1 := ((hasDerivAt_id' x).fun_pow 3).inv (pow_ne_zero 3 hx.ne')
  have h2 := (((hasDerivAt_id' x).add_const h).fun_pow 3).inv (pow_ne_zero 3 hxh.ne')
  have h3 := (h1.sub h2).const_mul (-(2 * T))
  refine h3.congr_deriv ?_
  norm_num
  field_simp
  ring

/-- `F″ ≥ 2Th/(x + h)³`. -/
theorem diffPhase2_ge {T h x : ℝ} (hT : 0 ≤ T) (hx : 0 < x) (hh : 0 ≤ h) :
    2 * T * h / (x + h) ^ 3 ≤ diffPhase2 T h x := by
  have hxh : 0 < x + h := by linarith
  have e : diffPhase2 T h x = T * h * (2 * x + h) / (x ^ 2 * (x + h) ^ 2) := by
    simp only [diffPhase2]; field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ T * h := mul_nonneg hT hh
  have key : 2 * (x ^ 2 * (x + h) ^ 2) ≤ (2 * x + h) * (x + h) ^ 3 := by
    nlinarith [sq_nonneg x, sq_nonneg h, mul_nonneg hx.le hh, pow_pos hxh 2]
  nlinarith [mul_le_mul_of_nonneg_left key this]

/-- `F″ ≤ 2Th/x³`. -/
theorem diffPhase2_le {T h x : ℝ} (hT : 0 ≤ T) (hx : 0 < x) (hh : 0 ≤ h) :
    diffPhase2 T h x ≤ 2 * T * h / x ^ 3 := by
  have hxh : 0 < x + h := by linarith
  have e : diffPhase2 T h x = T * h * (2 * x + h) / (x ^ 2 * (x + h) ^ 2) := by
    simp only [diffPhase2]; field_simp; ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ T * h := mul_nonneg hT hh
  have key : (2 * x + h) * x ^ 3 ≤ 2 * (x ^ 2 * (x + h) ^ 2) := by
    nlinarith [sq_nonneg x, sq_nonneg h, mul_nonneg hx.le hh, pow_pos hx 3, pow_pos hx 2,
      mul_nonneg (pow_pos hx 2).le hh, mul_nonneg (mul_nonneg hx.le hh) hh]
  nlinarith [mul_le_mul_of_nonneg_left key this]

/-- `|F‴| ≤ 6Th/x⁴`. -/
theorem abs_diffPhase3_le {T h x : ℝ} (hT : 0 ≤ T) (hx : 0 < x) (hh : 0 ≤ h) :
    |diffPhase3 T h x| ≤ 6 * T * h / x ^ 4 := by
  have hxh : 0 < x + h := by linarith
  have e : diffPhase3 T h x
      = -(2 * T * h * (3 * x ^ 2 + 3 * x * h + h ^ 2) / (x ^ 3 * (x + h) ^ 3)) := by
    simp only [diffPhase3]; field_simp; ring
  rw [e, abs_neg, abs_of_nonneg (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ T * h := mul_nonneg hT hh
  have key : (3 * x ^ 2 + 3 * x * h + h ^ 2) * x ^ 4 ≤ 3 * (x ^ 3 * (x + h) ^ 3) := by
    have hxh3 : x ^ 3 ≤ (x + h) ^ 3 := pow_le_pow_left₀ hx.le (by linarith) 3
    have e1 : 3 * (x + h) ^ 3 - x * (3 * x ^ 2 + 3 * x * h + h ^ 2)
        = 6 * x ^ 2 * h + 8 * x * h ^ 2 + 3 * h ^ 3 := by ring
    have hpos : 0 ≤ 6 * x ^ 2 * h + 8 * x * h ^ 2 + 3 * h ^ 3 := by positivity
    have : x * (3 * x ^ 2 + 3 * x * h + h ^ 2) ≤ 3 * (x + h) ^ 3 := by linarith
    calc (3 * x ^ 2 + 3 * x * h + h ^ 2) * x ^ 4
        = x ^ 3 * (x * (3 * x ^ 2 + 3 * x * h + h ^ 2)) := by ring
      _ ≤ x ^ 3 * (3 * (x + h) ^ 3) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = 3 * (x ^ 3 * (x + h) ^ 3) := by ring
  nlinarith [mul_le_mul_of_nonneg_left key this]

/-! ## The dual point -/

/-- `q(u) = √(Th/u + h²/4)`. -/
def dualQ (T h u : ℝ) : ℝ := Real.sqrt (T * h / u + h ^ 2 / 4)

/-- The stationary point `x(u) = q(u) − h/2` of `F(x) − (k − u)x`. -/
def dualX (T h u : ℝ) : ℝ := dualQ T h u - h / 2

theorem dualQ_sq {T h u : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h) (hu : 0 < u) :
    dualQ T h u ^ 2 = T * h / u + h ^ 2 / 4 :=
  Real.sq_sqrt (by positivity)

theorem dualQ_pos {T h u : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < u) : 0 < dualQ T h u :=
  Real.sqrt_pos.mpr (by positivity)

/-- `x(x + h) = Th/u`. -/
theorem dualX_mul_add {T h u : ℝ} (hT : 0 ≤ T) (hh : 0 ≤ h) (hu : 0 < u) :
    dualX T h u * (dualX T h u + h) = T * h / u := by
  have := dualQ_sq hT hh hu
  simp only [dualX]
  nlinarith

theorem dualX_pos {T h u : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < u) : 0 < dualX T h u := by
  have hq := dualQ_sq hT.le hh.le hu
  have hq0 := dualQ_pos hT hh hu
  have hpos : 0 < T * h / u := by positivity
  have hlt : (h / 2) ^ 2 < dualQ T h u ^ 2 := by rw [hq]; nlinarith
  simp only [dualX]
  by_contra hle
  push Not at hle
  have : dualQ T h u ≤ h / 2 := by linarith
  nlinarith

/-- **The dual point solves `F′(x) = k − u`.** -/
theorem diffPhase1_dualX {T h k u : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < u) :
    diffPhase1 T h k (dualX T h u) = k - u := by
  have hx := dualX_pos hT hh hu
  have hxh : 0 < dualX T h u + h := by linarith
  have hm := dualX_mul_add hT.le hh.le hu
  simp only [diffPhase1]
  have e : (dualX T h u + h)⁻¹ - (dualX T h u)⁻¹
      = -(h / (dualX T h u * (dualX T h u + h))) := by
    field_simp; ring
  rw [e, hm]
  field_simp
  ring

/-- The dual point is the unique solution of `x(x + h) = Th/u` among `x > 0`; in particular it is
increasing in `x(x+h)`.  Here: if `Th/u` lies between `a(a + h)` and `b(b + h)`, then `x(u)` lies
between `a` and `b`. -/
theorem dualX_mem_Icc {T h u a b : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < u) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hla : a * (a + h) ≤ T * h / u) (hlb : T * h / u ≤ b * (b + h)) :
    dualX T h u ∈ Set.Icc a b := by
  have hx := dualX_pos hT hh hu
  have hm := dualX_mul_add hT.le hh.le hu
  constructor
  · by_contra hlt
    push Not at hlt
    have : dualX T h u * (dualX T h u + h) < a * (a + h) := by nlinarith
    linarith
  · by_contra hlt
    push Not at hlt
    have : b * (b + h) < dualX T h u * (dualX T h u + h) := by nlinarith
    linarith

/-! ## The dual chain -/

/-- The derivative chain of the negated dual phase `−Φ(ν)`, `Φ(ν) = F(x(k − ν)) − ν x(k − ν)`. -/
def dualChain (T h k : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun ν => -(diffPhase T h k (dualX T h (k - ν)) - ν * dualX T h (k - ν))
  | 1 => fun ν => dualX T h (k - ν)
  | 2 => fun ν => T * h / (2 * (k - ν) ^ 2 * dualQ T h (k - ν))
  | 3 => fun ν => T * h / ((k - ν) ^ 3 * dualQ T h (k - ν))
      - (T * h) ^ 2 / (4 * (k - ν) ^ 4 * dualQ T h (k - ν) ^ 3)
  | _ + 4 => fun ν => 3 * (T * h) / ((k - ν) ^ 4 * dualQ T h (k - ν))
      - 3 * (T * h) ^ 2 / (2 * (k - ν) ^ 5 * dualQ T h (k - ν) ^ 3)
      + 3 * (T * h) ^ 3 / (8 * (k - ν) ^ 6 * dualQ T h (k - ν) ^ 5)

/-- `ν ↦ q(k − ν)` has derivative `c/(2u²q)`. -/
theorem hasDerivAt_dualQ_sub {T h k ν : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν) :
    HasDerivAt (fun ν => dualQ T h (k - ν))
      (T * h / (2 * (k - ν) ^ 2 * dualQ T h (k - ν))) ν := by
  have hq := dualQ_pos hT hh hu
  have hP : HasDerivAt (fun ν => T * h / (k - ν) + h ^ 2 / 4) (T * h / (k - ν) ^ 2) ν := by
    have h1 := ((hasDerivAt_id' ν).const_sub k).inv hu.ne'
    have h2 := (h1.const_mul (T * h)).add_const (h ^ 2 / 4)
    refine h2.congr_deriv ?_
    field_simp
  have hs := hP.sqrt (by positivity)
  refine hs.congr_deriv ?_
  simp only [dualQ]
  field_simp

theorem hasDerivAt_dualChain {T h k ν : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν) (i : ℕ)
    (hi : i < 4) : HasDerivAt (dualChain T h k i) (dualChain T h k (i + 1) ν) ν := by
  have hq := dualQ_pos hT hh hu
  have hQ := hasDerivAt_dualQ_sub hT hh hu
  have hU : HasDerivAt (fun ν : ℝ => k - ν) (-1) ν := by
    simpa using (hasDerivAt_id' ν).const_sub k
  have hX : HasDerivAt (fun ν => dualX T h (k - ν))
      (T * h / (2 * (k - ν) ^ 2 * dualQ T h (k - ν))) ν := by
    simpa [dualX] using hQ.sub_const (h / 2)
  interval_cases i
  · -- `(−Φ)′ = x`, by stationarity
    have hx := dualX_pos hT hh hu
    have hF := (hasDerivAt_diffPhase (T := T) (k := k) hx hh.le).comp ν hX
    have h2 := ((hF.sub ((hasDerivAt_id' ν).mul hX)).neg)
    refine h2.congr_deriv ?_
    have hst := diffPhase1_dualX (k := k) hT hh hu
    simp only [dualChain, hst]
    ring
  · exact hX
  · have h1 : HasDerivAt (fun ν => 2 * (k - ν) ^ 2 * dualQ T h (k - ν))
        (2 * (2 * (k - ν) * (-1)) * dualQ T h (k - ν)
          + 2 * (k - ν) ^ 2 * (T * h / (2 * (k - ν) ^ 2 * dualQ T h (k - ν)))) ν := by
      have := ((hU.fun_pow 2).const_mul 2).mul hQ
      refine this.congr_deriv ?_
      norm_num
    have h2 := (hasDerivAt_const ν (T * h)).div h1 (by positivity)
    refine h2.congr_deriv ?_
    simp only [dualChain]
    field_simp
    ring
  · have h1 : HasDerivAt (fun ν => (k - ν) ^ 3 * dualQ T h (k - ν))
        (3 * (k - ν) ^ 2 * (-1) * dualQ T h (k - ν)
          + (k - ν) ^ 3 * (T * h / (2 * (k - ν) ^ 2 * dualQ T h (k - ν)))) ν := by
      have := (hU.fun_pow 3).mul hQ
      refine this.congr_deriv ?_
      norm_num
    have h2 : HasDerivAt (fun ν => 4 * (k - ν) ^ 4 * dualQ T h (k - ν) ^ 3)
        (4 * (4 * (k - ν) ^ 3 * (-1)) * dualQ T h (k - ν) ^ 3
          + 4 * (k - ν) ^ 4 * (3 * dualQ T h (k - ν) ^ 2
            * (T * h / (2 * (k - ν) ^ 2 * dualQ T h (k - ν))))) ν := by
      have := ((hU.fun_pow 4).const_mul 4).mul (hQ.fun_pow 3)
      refine this.congr_deriv ?_
      norm_num
    have h3 := ((hasDerivAt_const ν (T * h)).div h1 (by positivity)).sub
      ((hasDerivAt_const ν ((T * h) ^ 2)).div h2 (by positivity))
    refine h3.congr_deriv ?_
    simp only [dualChain]
    field_simp
    ring

/-- With `r = c/(uq²)`, `G₄ = (q/u³)(3r − 3r²/2 + 3r³/8)`. -/
theorem dualChain_four_eq {T h k ν : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν) :
    dualChain T h k 4 ν = dualQ T h (k - ν) / (k - ν) ^ 3
      * (3 * (T * h / ((k - ν) * dualQ T h (k - ν) ^ 2))
        - 3 / 2 * (T * h / ((k - ν) * dualQ T h (k - ν) ^ 2)) ^ 2
        + 3 / 8 * (T * h / ((k - ν) * dualQ T h (k - ν) ^ 2)) ^ 3) := by
  have hq := dualQ_pos hT hh hu
  simp only [dualChain]
  field_simp

/-- **The fourth derivative of the dual phase.**  For `hu ≤ T`, `q/u³ ≤ G₄ ≤ 3q/u³`. -/
theorem dualChain_four_bounds {T h k ν : ℝ} (hT : 0 < T) (hh : 0 < h) (hu : 0 < k - ν)
    (hsmall : h * (k - ν) ≤ T) :
    dualQ T h (k - ν) / (k - ν) ^ 3 ≤ dualChain T h k 4 ν
      ∧ dualChain T h k 4 ν ≤ 3 * (dualQ T h (k - ν) / (k - ν) ^ 3) := by
  have hq := dualQ_pos hT hh hu
  have hq2 := dualQ_sq hT.le hh.le hu
  set u := k - ν with hudef
  set q := dualQ T h u with hqdef
  set r := T * h / (u * q ^ 2) with hr
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity), hq2]
    field_simp
    nlinarith [sq_nonneg h, hu.le]
  have hr45 : 4 / 5 ≤ r := by
    rw [hr, le_div_iff₀ (by positivity), hq2]
    field_simp
    nlinarith [mul_le_mul_of_nonneg_left hsmall hh.le]
  rw [dualChain_four_eq hT hh hu]
  have hb : 0 < q / u ^ 3 := by positivity
  have hp1 : 1 ≤ 3 * r - 3 / 2 * r ^ 2 + 3 / 8 * r ^ 3 := by nlinarith
  have hp3 : 3 * r - 3 / 2 * r ^ 2 + 3 / 8 * r ^ 3 ≤ 3 := by nlinarith
  constructor
  · nlinarith
  · nlinarith

end

end RHTower
