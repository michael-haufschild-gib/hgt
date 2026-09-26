import GaloisForLFunctions.RHTower.PoleVanishingWeilTraceCertificate
import GaloisForLFunctions.HTGeometry.MidpointRadiusTrigEnclosures
import GaloisForLFunctions.RHTower.SuzukiRemainderFourierTransform

/-!
# Weil positivity on the pole-vanishing subspace at `√2`, and past the first prime

The pole-vanishing ground energy of the exact restricted Weil form at the aperture `a = ½ log 2`
(multiplicative support `[2^{-1/2}, 2^{1/2}]`) is at least `1/10`.  Since this ground energy is
continuous in the aperture, it stays positive on an interval of apertures strictly beyond
`½ log 2`, where the translation by `log 2` of the prime `2` enters the form.  So the restricted
Weil form, prime `2` included, is positive definite on pole-vanishing test functions supported
in `[λ^{-1}, λ]` for all `λ` in some interval `[√2, λ₁)`, `λ₁ > √2`.

The proof evaluates the trace certificate of `PoleVanishingWeilTraceCertificate` at `α = 3/10`
on fourteen frequency shells of width `1/10`:

* the archimedean symbol `W(ξ) = Re ψ(1/4 + iπξ) - log π` is bounded below at the grid points
  from the digamma recurrence `ψ(s + 16) = ψ(s) + Σ_{j<16} (s + j)⁻¹`, the half-plane asymptotic
  `|Re ψ(z) - log|z|| ≤ (10 + Re z)/(2|z|²)`, and `log π < 1.146`;
* on each shell the Fourier mass of a pole-vanishing vector is bounded through the closed-form
  plane-wave residual at a reference frequency `θ/(π log 2)` with rational phase `θ`, enclosed
  by midpoint–radius arithmetic from `log 2`, `2^{1/4}` and degree-20 Taylor enclosures of
  `sin θ, cos θ`, plus the Lipschitz offset `4π² (0.0501)² · 2a³/3 ≤ 0.00276`.

The certificate total is `Σ_k (2/10) G_k R_k < 0.2`, so the ground energy is at least
`3/10 - 2/10`.  The large negative dip `W(0) = ψ(1/4) - log π ≈ -5.37` is absorbed because a
pole-vanishing vector has almost no Fourier mass at low frequency: the plane wave `e_ξ` is within
`L²`-distance `O(ξ²)` of the span of `e^{± x/2}` on the aperture.
-/

open MeasureTheory Complex Set
open scoped FourierTransform InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-! ## The constants `log 2` and `2^{1/4}` -/

theorem exp_log_two_div_four_pow_four : Real.exp (Real.log 2 / 4) ^ 4 = 2 := by
  rw [← Real.exp_nat_mul]
  rw [show ((4 : ℕ) : ℝ) * (Real.log 2 / 4) = Real.log 2 by push_cast; ring]
  exact Real.exp_log (by norm_num)

theorem quarter_root_two_bounds :
    (1.1892071150 : ℝ) ≤ Real.exp (Real.log 2 / 4) ∧
      Real.exp (Real.log 2 / 4) ≤ 1.1892071151 := by
  have hx4 := exp_log_two_div_four_pow_four
  have hxpos := Real.exp_pos (Real.log 2 / 4)
  constructor
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ hxpos.le h.le 4
    rw [hx4] at this
    norm_num at this
  · by_contra h
    push Not at h
    have := pow_le_pow_left₀ (by norm_num) h.le 4
    rw [hx4] at this
    norm_num at this

theorem sinh_half_log_two :
    Real.sinh (Real.log 2 / 2) = (1 / 4) * (Real.exp (Real.log 2 / 4) * Real.exp (Real.log 2 / 4)) := by
  have hx4 := exp_log_two_div_four_pow_four
  have hsq : Real.exp (Real.log 2 / 2) = Real.exp (Real.log 2 / 4) ^ 2 := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Real.sinh_eq, Real.exp_neg, hsq]
  have hx0 : Real.exp (Real.log 2 / 4) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  nlinarith [hx4]

theorem sinh_quarter_log_two :
    Real.sinh (Real.log 2 / 4) =
      (1 / 2) * (Real.exp (Real.log 2 / 4) - (Real.exp (Real.log 2 / 4))⁻¹) := by
  rw [Real.sinh_eq, Real.exp_neg]
  ring

theorem cosh_quarter_log_two :
    Real.cosh (Real.log 2 / 4) =
      (1 / 2) * (Real.exp (Real.log 2 / 4) + (Real.exp (Real.log 2 / 4))⁻¹) := by
  rw [Real.cosh_eq, Real.exp_neg]
  ring

/-! ## The residual closed form in the variables `log 2`, `2^{1/4}`, `sin θ`, `cos θ` -/

/-- The residual closed form, written with the exact operation tree of its enclosure. -/
def residualExpr (L x s c θ p q : ℝ) : ℝ :=
  2 * ((1 / 2) * L) -
      (2 * p) * (4 * (((c * ((1 / 2) * (x - x⁻¹))) +
          (2 * (2 * θ * L⁻¹)) * (s * ((1 / 2) * (x + x⁻¹)))) *
        (1 + 4 * ((2 * θ * L⁻¹) * (2 * θ * L⁻¹)))⁻¹)) +
    p ^ 2 * ((1 / 2) * L + (1 / 4) * (x * x)) -
      (2 * q) * (4 * (((s * ((1 / 2) * (x + x⁻¹))) -
          (2 * (2 * θ * L⁻¹)) * (c * ((1 / 2) * (x - x⁻¹)))) *
        (1 + 4 * ((2 * θ * L⁻¹) * (2 * θ * L⁻¹)))⁻¹)) +
    q ^ 2 * ((1 / 4) * (x * x) - (1 / 2) * L)

theorem poleResidualClosedForm_halfLogTwo (θ p q : ℝ) :
    poleResidualClosedForm halfLogTwoAperture.1
        (2 * Real.pi * (θ / (Real.pi * Real.log 2))) p q =
      residualExpr (Real.log 2) (Real.exp (Real.log 2 / 4)) (Real.sin θ) (Real.cos θ) θ p q := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have ha : halfLogTwoAperture.1 = Real.log 2 / 2 := rfl
  have hθ : 2 * Real.pi * (θ / (Real.pi * Real.log 2)) * (Real.log 2 / 2) = θ := by
    field_simp
  have hω : 2 * Real.pi * (θ / (Real.pi * Real.log 2)) = 2 * θ * (Real.log 2)⁻¹ := by
    field_simp
  unfold poleResidualClosedForm poleCosCoshIntegral poleSinSinhIntegral residualExpr
  rw [ha, hθ, show Real.log 2 / 2 / 2 = Real.log 2 / 4 by ring, sinh_half_log_two,
    sinh_quarter_log_two, cosh_quarter_log_two, hω]
  ring

/-- The enclosure tree of `residualExpr`. -/
def residualEncl (eL ex es ec : Encl) (θ p q : ℝ) : Encl :=
  let eω := Encl.smul (2 * θ) (Encl.inv eL)
  let es2 := Encl.smul (1 / 2) (Encl.sub ex (Encl.inv ex))
  let ec2 := Encl.smul (1 / 2) (Encl.add ex (Encl.inv ex))
  let esh := Encl.smul (1 / 4) (Encl.mul ex ex)
  let ea := Encl.smul (1 / 2) eL
  let eD := Encl.inv (Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul eω eω)))
  let eC := Encl.smul 4 (Encl.mul (Encl.add (Encl.mul ec es2)
    (Encl.mul (Encl.smul 2 eω) (Encl.mul es ec2))) eD)
  let eS := Encl.smul 4 (Encl.mul (Encl.sub (Encl.mul es ec2)
    (Encl.mul (Encl.smul 2 eω) (Encl.mul ec es2))) eD)
  Encl.add (Encl.sub (Encl.add (Encl.sub (Encl.smul 2 ea) (Encl.smul (2 * p) eC))
    (Encl.smul (p ^ 2) (Encl.add ea esh))) (Encl.smul (2 * q) eS))
    (Encl.smul (q ^ 2) (Encl.sub esh ea))

theorem holds_residualEncl {L x s c θ p q : ℝ} {eL ex es ec : Encl}
    (hL : Encl.Holds L eL) (hx : Encl.Holds x ex) (hs : Encl.Holds s es)
    (hc : Encl.Holds c ec) (hLi : eL.r < |eL.c|) (hxi : ex.r < |ex.c|)
    (hDi : (Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul (Encl.smul (2 * θ) (Encl.inv eL))
      (Encl.smul (2 * θ) (Encl.inv eL))))).r <
      |(Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul (Encl.smul (2 * θ) (Encl.inv eL))
      (Encl.smul (2 * θ) (Encl.inv eL))))).c|) :
    Encl.Holds (residualExpr L x s c θ p q) (residualEncl eL ex es ec θ p q) := by
  have hLinv := Encl.holds_inv hL hLi
  have hxinv := Encl.holds_inv hx hxi
  have hω : Encl.Holds (2 * θ * L⁻¹) (Encl.smul (2 * θ) (Encl.inv eL)) :=
    Encl.holds_smul (2 * θ) hLinv
  have hs2 := Encl.holds_smul (1 / 2) (Encl.holds_sub hx hxinv)
  have hc2 := Encl.holds_smul (1 / 2) (Encl.holds_add hx hxinv)
  have hsh := Encl.holds_smul (1 / 4) (Encl.holds_mul hx hx)
  have ha := Encl.holds_smul (1 / 2) hL
  have hD := Encl.holds_inv (Encl.holds_add (Encl.holds_exact 1)
    (Encl.holds_smul 4 (Encl.holds_mul hω hω))) hDi
  have hC := Encl.holds_smul 4 (Encl.holds_mul (Encl.holds_add (Encl.holds_mul hc hs2)
    (Encl.holds_mul (Encl.holds_smul 2 hω) (Encl.holds_mul hs hc2))) hD)
  have hS := Encl.holds_smul 4 (Encl.holds_mul (Encl.holds_sub (Encl.holds_mul hs hc2)
    (Encl.holds_mul (Encl.holds_smul 2 hω) (Encl.holds_mul hc hs2))) hD)
  exact Encl.holds_add (Encl.holds_sub (Encl.holds_add (Encl.holds_sub
    (Encl.holds_smul 2 ha) (Encl.holds_smul (2 * p) hC))
    (Encl.holds_smul (p ^ 2) (Encl.holds_add ha hsh))) (Encl.holds_smul (2 * q) hS))
    (Encl.holds_smul (q ^ 2) (Encl.holds_sub hsh ha))

/-- The standard enclosures of `log 2` and `2^{1/4}`. -/
def logTwoEncl : Encl := Encl.ofBounds 0.6931471803 0.6931471808
def quarterRootTwoEncl : Encl := Encl.ofBounds 1.1892071150 1.1892071151

theorem holds_logTwoEncl : Encl.Holds (Real.log 2) logTwoEncl :=
  Encl.holds_ofBounds Real.log_two_gt_d9.le Real.log_two_lt_d9.le

theorem holds_quarterRootTwoEncl :
    Encl.Holds (Real.exp (Real.log 2 / 4)) quarterRootTwoEncl :=
  Encl.holds_ofBounds quarter_root_two_bounds.1 quarter_root_two_bounds.2

/-- **The residual at a rational phase `θ`.**  With `m = θ/(π log 2)`, the closed residual is
bounded by the enclosure evaluated at rational data. -/
theorem poleResidualClosedForm_halfLogTwo_le (θ p q : ℝ) (hθ : |θ| ≤ 10)
    (hDi : (Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul
      (Encl.smul (2 * θ) (Encl.inv logTwoEncl)) (Encl.smul (2 * θ) (Encl.inv logTwoEncl))))).r <
      |(Encl.add (Encl.exact 1) (Encl.smul 4 (Encl.mul
      (Encl.smul (2 * θ) (Encl.inv logTwoEncl)) (Encl.smul (2 * θ) (Encl.inv logTwoEncl))))).c|) :
    poleResidualClosedForm halfLogTwoAperture.1
        (2 * Real.pi * (θ / (Real.pi * Real.log 2))) p q ≤
      (residualEncl logTwoEncl quarterRootTwoEncl
        ⟨sinTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩
        ⟨cosTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩ θ p q).c +
      (residualEncl logTwoEncl quarterRootTwoEncl
        ⟨sinTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩
        ⟨cosTaylor 10 θ, |θ| ^ 20 / (Nat.factorial 20 : ℝ) * 2⟩ θ p q).r := by
  rw [poleResidualClosedForm_halfLogTwo]
  apply Encl.le_of_holds
  apply holds_residualEncl holds_logTwoEncl holds_quarterRootTwoEncl (encl_sin θ hθ)
    (encl_cos θ hθ)
  · norm_num [logTwoEncl, Encl.ofBounds]
  · norm_num [quarterRootTwoEncl, Encl.ofBounds]
  · exact hDi

/-! ## Mirror symmetry of the residual -/

theorem poleResidualClosedForm_neg (a ω p q : ℝ) :
    poleResidualClosedForm a (-ω) p (-q) = poleResidualClosedForm a ω p q := by
  unfold poleResidualClosedForm poleCosCoshIntegral poleSinSinhIntegral
  simp only [neg_mul, Real.cos_neg, Real.sin_neg, neg_sq]
  ring

/-! ## Lower bounds for the archimedean symbol -/

theorem digamma_add_nat_eq {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Complex.digamma (s + n) = Complex.digamma s + ∑ j ∈ Finset.range n, (s + j)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hne : ∀ m : ℕ, s + (n : ℂ) ≠ -(m : ℂ) := by
      intro m h
      have hre := congrArg Complex.re h
      simp only [Complex.add_re, Complex.natCast_re, Complex.neg_re] at hre
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    rw [show s + ((n + 1 : ℕ) : ℂ) = (s + n) + 1 by push_cast; ring,
      Complex.digamma_apply_add_one _ hne, ih, Finset.sum_range_succ]
    ring

theorem re_inv_quarter_add (y : ℝ) (j : ℕ) :
    ((((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I) + j)⁻¹.re =
      ((j : ℝ) + 1 / 4) / (((j : ℝ) + 1 / 4) ^ 2 + y ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_zero, Complex.natCast_re, Complex.add_im,
    Complex.mul_im, zero_add, Complex.natCast_im, add_zero]
  ring

/-- `Re ψ(1/4 + iy) ≥ ½ log(16.25² + y²) − 13.125/(16.25² + y²) − Σ_{j<16} (j+¼)/((j+¼)² + y²)`. -/
theorem re_digamma_quarter_ge (y : ℝ) :
    (1 / 2) * Real.log (264.0625 + y ^ 2) - 13.125 / (264.0625 + y ^ 2) -
        ∑ j ∈ Finset.range 16, ((j : ℝ) + 1 / 4) / (((j : ℝ) + 1 / 4) ^ 2 + y ^ 2) ≤
      (Complex.digamma (((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I)).re := by
  set s : ℂ := ((1 / 4 : ℝ) : ℂ) + (y : ℂ) * I with hsdef
  have hsre : 0 < s.re := by simp [hsdef]
  have hrec := digamma_add_nat_eq hsre 16
  set z : ℂ := s + ((16 : ℕ) : ℂ) with hz
  have hzre : z.re = 16.25 := by simp [hz, hsdef]; norm_num
  have hzim : z.im = y := by simp [hz, hsdef]
  have hznorm2 : ‖z‖ ^ 2 = 264.0625 + y ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim]
    ring
  have hX : 0 < 264.0625 + y ^ 2 := by positivity
  -- the asymptotic bound at `2z`
  have h2z : (2 * z) / 2 = z := by ring
  have hnorm2z : ‖2 * z‖ = 2 * ‖z‖ := by
    rw [norm_mul]
    norm_num
  have hz16 : 16 ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hzre] at this
    norm_num at this
    linarith
  have hzpos : 0 < ‖z‖ := by linarith
  have hasym := abs_re_digamma_half_sub_log_le (s := 2 * z)
    (by simp [hzre]; norm_num) (by rw [hnorm2z]; linarith)
  rw [h2z, hnorm2z] at hasym
  have hlog : Real.log (2 * ‖z‖) - Real.log 2 = (1 / 2) * Real.log (264.0625 + y ^ 2) := by
    rw [Real.log_mul (by norm_num) hzpos.ne', ← hznorm2, Real.log_pow]
    push_cast
    ring
  have hre2z : (2 * z).re = 32.5 := by simp [hzre]; norm_num
  rw [hlog, hre2z] at hasym
  have hden : (2 * ‖z‖) ^ 2 = 4 * (264.0625 + y ^ 2) := by
    rw [mul_pow, hznorm2]
    norm_num
  rw [hden] at hasym
  have hlow : (1 / 2) * Real.log (264.0625 + y ^ 2) - 13.125 / (264.0625 + y ^ 2) ≤
      (Complex.digamma z).re := by
    have := (abs_le.mp hasym).1
    have heq : (20 + 32.5) / (4 * (264.0625 + y ^ 2)) = 13.125 / (264.0625 + y ^ 2) := by
      field_simp
      norm_num
    linarith
  -- the recurrence
  have hre := congrArg Complex.re hrec
  rw [Complex.add_re, Complex.re_sum] at hre
  have hsum : ∑ j ∈ Finset.range 16, (s + (j : ℂ))⁻¹.re =
      ∑ j ∈ Finset.range 16, ((j : ℝ) + 1 / 4) / (((j : ℝ) + 1 / 4) ^ 2 + y ^ 2) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hsdef]
    exact re_inv_quarter_add y j
  rw [hsum] at hre
  linarith

theorem log_pi_lt : Real.log Real.pi < 1.146 := by
  rw [Real.log_lt_iff_lt_exp Real.pi_pos]
  have h1 : Real.exp 1.146 = Real.exp 1 * Real.exp 0.146 := by
    rw [← Real.exp_add]
    norm_num
  have h2 := Real.quadratic_le_exp_of_nonneg (x := (0.146 : ℝ)) (by norm_num)
  have h3 := Real.exp_one_gt_d9
  rw [h1]
  have h4 := Real.pi_lt_d6
  nlinarith [Real.exp_pos 0.146]

theorem log_sixteen_quarter_ge : 4 * 0.6931471803 + (1 - 64 / 65) ≤ Real.log 16.25 := by
  have h16 : Real.log 16.25 = 4 * Real.log 2 + Real.log (65 / 64) := by
    rw [show (16.25 : ℝ) = 2 ^ 4 * (65 / 64) by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast
    ring
  have h1 := Real.one_sub_inv_le_log_of_pos (x := (65 / 64 : ℝ)) (by norm_num)
  have h2 := Real.log_two_gt_d9
  rw [h16]
  norm_num at h1 ⊢
  linarith

/-- **The grid lower bound for `W`.**  For `0 ≤ Y ≤ (πξ)²`. -/
theorem archimedeanWeilSymbol_ge_of_sq {ξ Y : ℝ} (hY0 : 0 ≤ Y) (hY : Y ≤ (Real.pi * ξ) ^ 2) :
    (4 * 0.6931471803 + (1 - 64 / 65)) + (1 / 2) * (1 - 264.0625 / (264.0625 + Y)) -
        13.125 / (264.0625 + Y) -
        ∑ j ∈ Finset.range 16, ((j : ℝ) + 1 / 4) / (((j : ℝ) + 1 / 4) ^ 2 + Y) - 1.146 ≤
      archimedeanWeilSymbol ξ := by
  rw [archimedeanWeilSymbol_eq]
  have hmain := re_digamma_quarter_ge (Real.pi * ξ)
  set y2 := (Real.pi * ξ) ^ 2 with hy2
  have hX : 0 < 264.0625 + Y := by positivity
  have hXY : 264.0625 + Y ≤ 264.0625 + y2 := by linarith
  -- the logarithm
  have hlogX : Real.log 264.0625 + (1 - 264.0625 / (264.0625 + y2)) ≤
      Real.log (264.0625 + y2) := by
    have h := Real.one_sub_inv_le_log_of_pos (x := (264.0625 + y2) / 264.0625) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num), inv_div] at h
    linarith
  have hlog264 : 2 * (4 * 0.6931471803 + (1 - 64 / 65)) ≤ Real.log 264.0625 := by
    rw [show (264.0625 : ℝ) = 16.25 ^ 2 by norm_num, Real.log_pow]
    push_cast
    linarith [log_sixteen_quarter_ge]
  have hfrac : 1 - 264.0625 / (264.0625 + Y) ≤ 1 - 264.0625 / (264.0625 + y2) := by
    have := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 264.0625) hX hXY
    linarith
  have hfrac2 : 13.125 / (264.0625 + y2) ≤ 13.125 / (264.0625 + Y) :=
    div_le_div_of_nonneg_left (by norm_num) hX hXY
  have hsum : ∑ j ∈ Finset.range 16, ((j : ℝ) + 1 / 4) / (((j : ℝ) + 1 / 4) ^ 2 + y2) ≤
      ∑ j ∈ Finset.range 16, ((j : ℝ) + 1 / 4) / (((j : ℝ) + 1 / 4) ^ 2 + Y) := by
    apply Finset.sum_le_sum
    intro j _
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    linarith
  have hlp := log_pi_lt
  have hπξ : ((Real.pi * ξ : ℝ) : ℂ) = (Real.pi * ξ : ℝ) := rfl
  linarith

/-! ## The shell bounds -/

/-- The Lipschitz offset: `4π² d² · 2a³/3 ≤ 0.00276` for `d ≤ 0.0501` at `a = ½ log 2`. -/
theorem lipschitz_offset_le {d : ℝ} (hd : |d| ≤ 0.0501) :
    4 * Real.pi ^ 2 * d ^ 2 * (2 * halfLogTwoAperture.1 ^ 3 / 3) ≤ 0.00276 := by
  have hpi := Real.pi_lt_d6
  have hpi0 := Real.pi_pos
  have hL := Real.log_two_lt_d9
  have hL0 := Real.log_two_gt_d9
  have ha : halfLogTwoAperture.1 = Real.log 2 / 2 := rfl
  rw [ha]
  have hd2 : d ^ 2 ≤ 0.0501 ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg d) hd 2
  have hpi2 : Real.pi ^ 2 ≤ 3.141593 ^ 2 := pow_le_pow_left₀ hpi0.le hpi.le 2
  have ha3 : (Real.log 2 / 2) ^ 3 ≤ (0.6931471808 / 2) ^ 3 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 3
  calc 4 * Real.pi ^ 2 * d ^ 2 * (2 * (Real.log 2 / 2) ^ 3 / 3) ≤
        4 * 3.141593 ^ 2 * 0.0501 ^ 2 * (2 * (0.6931471808 / 2) ^ 3 / 3) := by
        gcongr
    _ ≤ 0.00276 := by norm_num

/-- **One shell.**  If the closed residual at the rational phase `θ` is at most `r`, and the
reference frequency `θ/(π log 2)` lies within `0.0501` of every point of the shell
`lo ≤ |ξ| < hi`, then every pole-vanishing aperture vector has Fourier mass density at most
`((1+η) r + (1 + 1/η) · 0.00276) ‖f‖²` on that shell. -/
theorem shell_fourier_bound {θ p q r η lo hi : ℝ} (hη : 0 < η)
    (hres : poleResidualClosedForm halfLogTwoAperture.1
      (2 * Real.pi * (θ / (Real.pi * Real.log 2))) p q ≤ r)
    (hlo : θ / (Real.pi * Real.log 2) - lo ≤ 0.0501)
    (hhi : hi - θ / (Real.pi * Real.log 2) ≤ 0.0501)
        (f : suzukiApertureHilbert halfLogTwoAperture)
    (hplus : inner ℂ (ccmPolarL2Vector halfLogTwoAperture (1 / 2)) f.1 = 0)
    (hminus : inner ℂ (ccmPolarL2Vector halfLogTwoAperture (-1 / 2)) f.1 = 0)
    (ξ : ℝ) (hξlo : lo ≤ |ξ|) (hξhi : |ξ| < hi) :
    ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ ((1 + η) * r + (1 + 1 / η) * 0.00276) * ‖f‖ ^ 2 := by
  set m := θ / (Real.pi * Real.log 2) with hm
  have h1η : 0 ≤ 1 + 1 / η := by positivity
  have hf2 : 0 ≤ ‖f‖ ^ 2 := sq_nonneg _
  rcases le_or_gt 0 ξ with hξ | hξ
  · rw [abs_of_nonneg hξ] at hξlo hξhi
    have hb := norm_fourier_sq_le_of_polar halfLogTwoAperture f hplus hminus ξ m p q η hη
    have hoff := lipschitz_offset_le (d := ξ - m) (by rw [abs_le]; constructor <;> linarith)
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hf2)
    have := mul_le_mul_of_nonneg_left hres (by linarith : (0 : ℝ) ≤ 1 + η)
    have := mul_le_mul_of_nonneg_left hoff h1η
    linarith
  · rw [abs_of_neg hξ] at hξlo hξhi
    have hb := norm_fourier_sq_le_of_polar halfLogTwoAperture f hplus hminus ξ (-m) p (-q) η hη
    have hsym : poleResidualClosedForm halfLogTwoAperture.1 (2 * Real.pi * -m) p (-q) =
        poleResidualClosedForm halfLogTwoAperture.1 (2 * Real.pi * m) p q := by
      rw [show 2 * Real.pi * -m = -(2 * Real.pi * m) by ring, poleResidualClosedForm_neg]
    rw [hsym] at hb
    have hoff := lipschitz_offset_le (d := ξ - -m) (by rw [abs_le]; constructor <;> linarith)
    refine hb.trans (mul_le_mul_of_nonneg_right ?_ hf2)
    have := mul_le_mul_of_nonneg_left hres (by linarith : (0 : ℝ) ≤ 1 + η)
    have := mul_le_mul_of_nonneg_left hoff h1η
    linarith

/-- Bounds on `π log 2` used to place the reference frequencies. -/
theorem pi_mul_log_two_bounds :
    (2.1775856 : ℝ) ≤ Real.pi * Real.log 2 ∧ Real.pi * Real.log 2 ≤ 2.1775864 := by
  have h1 := Real.pi_gt_d6
  have h2 := Real.pi_lt_d6
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  constructor <;> nlinarith

/-! ## The fourteen shell residuals -/

theorem shellResidual_0 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((1089 / 10000 : ℝ) / (Real.pi * Real.log 2))) (99302 / 100000) (6258 / 10000) ≤
      0.0002 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_1 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((3266 / 10000 : ℝ) / (Real.pi * Real.log 2))) (97733 / 100000) (18594 / 10000) ≤
      0.0005 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_2 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((5444 / 10000 : ℝ) / (Real.pi * Real.log 2))) (94638 / 100000) (30401 / 10000) ≤
      0.0019 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_3 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((7622 / 10000 : ℝ) / (Real.pi * Real.log 2))) (90103 / 100000) (41354 / 10000) ≤
      0.0058 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_4 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((9799 / 10000 : ℝ) / (Real.pi * Real.log 2))) (84264 / 100000) (51145 / 10000) ≤
      0.0140 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_5 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((11977 / 10000 : ℝ) / (Real.pi * Real.log 2))) (77275 / 100000) (59510 / 10000) ≤
      0.0288 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_6 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((14154 / 10000 : ℝ) / (Real.pi * Real.log 2))) (69335 / 100000) (66238 / 10000) ≤
      0.0515 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_7 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((16332 / 10000 : ℝ) / (Real.pi * Real.log 2))) (60659 / 100000) (71162 / 10000) ≤
      0.0835 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_8 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((18509 / 10000 : ℝ) / (Real.pi * Real.log 2))) (51484 / 100000) (74184 / 10000) ≤
      0.1255 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_9 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((20687 / 10000 : ℝ) / (Real.pi * Real.log 2))) (42051 / 100000) (75260 / 10000) ≤
      0.1765 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_10 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((22865 / 10000 : ℝ) / (Real.pi * Real.log 2))) (32606 / 100000) (74416 / 10000) ≤
      0.2355 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_11 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((25042 / 10000 : ℝ) / (Real.pi * Real.log 2))) (23385 / 100000) (71736 / 10000) ≤
      0.2995 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_12 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((27220 / 10000 : ℝ) / (Real.pi * Real.log 2))) (14613 / 100000) (67359 / 10000) ≤
      0.3660 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

theorem shellResidual_13 : poleResidualClosedForm halfLogTwoAperture.1
    (2 * Real.pi * ((29397 / 10000 : ℝ) / (Real.pi * Real.log 2))) (6492 / 100000) (61475 / 10000) ≤
      0.4315 := by
  refine (poleResidualClosedForm_halfLogTwo_le _ _ _ (by norm_num [abs_of_nonneg]) ?_).trans ?_
  · norm_num [Encl.add, Encl.smul, Encl.mul, Encl.inv, Encl.exact, logTwoEncl, Encl.ofBounds]
  · norm_num [residualEncl, Encl.add, Encl.sub, Encl.smul, Encl.mul, Encl.inv, Encl.exact,
      logTwoEncl, quarterRootTwoEncl, Encl.ofBounds, sinTaylor, cosTaylor, Finset.sum_range_succ,
      Nat.factorial]

/-! ## The fifteen grid values of the archimedean symbol -/

theorem archimedeanWeilSymbol_ge_grid {ξ : ℝ} (hξ : 0 ≤ ξ) :
    (4 * 0.6931471803 + (1 - 64 / 65)) +
        (1 / 2) * (1 - 264.0625 / (264.0625 + (3.141592 * ξ) ^ 2)) -
        13.125 / (264.0625 + (3.141592 * ξ) ^ 2) -
        ∑ j ∈ Finset.range 16, ((j : ℝ) + 1 / 4) / (((j : ℝ) + 1 / 4) ^ 2 + (3.141592 * ξ) ^ 2) -
        1.146 ≤ archimedeanWeilSymbol ξ :=
  archimedeanWeilSymbol_ge_of_sq (by positivity)
    (pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right Real.pi_gt_d6.le hξ) 2)

theorem gridSymbol_0 : (-5.40 : ℝ) ≤ archimedeanWeilSymbol ((0 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_1 : (-2.89 : ℝ) ≤ archimedeanWeilSymbol ((1 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_2 : (-1.73 : ℝ) ≤ archimedeanWeilSymbol ((2 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_3 : (-1.26 : ℝ) ≤ archimedeanWeilSymbol ((3 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_4 : (-0.955 : ℝ) ≤ archimedeanWeilSymbol ((4 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_5 : (-0.725 : ℝ) ≤ archimedeanWeilSymbol ((5 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_6 : (-0.54 : ℝ) ≤ archimedeanWeilSymbol ((6 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_7 : (-0.385 : ℝ) ≤ archimedeanWeilSymbol ((7 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_8 : (-0.252 : ℝ) ≤ archimedeanWeilSymbol ((8 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_9 : (-0.133 : ℝ) ≤ archimedeanWeilSymbol ((9 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_10 : (-0.027 : ℝ) ≤ archimedeanWeilSymbol ((10 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_11 : (0.068 : ℝ) ≤ archimedeanWeilSymbol ((11 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_12 : (0.155 : ℝ) ≤ archimedeanWeilSymbol ((12 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_13 : (0.235 : ℝ) ≤ archimedeanWeilSymbol ((13 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

theorem gridSymbol_14 : (0.3 : ℝ) ≤ archimedeanWeilSymbol ((14 : ℕ) * (1 / 10)) := by
  refine le_trans ?_ (archimedeanWeilSymbol_ge_grid (by norm_num))
  norm_num [Finset.sum_range_succ]

/-! ## Assembly -/

/-- The step heights of the certificate: `0.3` minus the grid values of the symbol. -/
def certG : ℕ → ℝ
  | 0 => 5.70
  | 1 => 3.19
  | 2 => 2.03
  | 3 => 1.56
  | 4 => 1.255
  | 5 => 1.025
  | 6 => 0.84
  | 7 => 0.685
  | 8 => 0.552
  | 9 => 0.433
  | 10 => 0.327
  | 11 => 0.232
  | 12 => 0.145
  | 13 => 0.065
  | _ => 0

/-- The shell Fourier-mass constants of the certificate. -/
def certR : ℕ → ℝ
  | 0 => (1 + 4) * 0.0002 + (1 + 1 / 4) * 0.00276
  | 1 => (1 + 2) * 0.0005 + (1 + 1 / 2) * 0.00276
  | 2 => (1 + 1.2) * 0.0019 + (1 + 1 / 1.2) * 0.00276
  | 3 => (1 + 0.7) * 0.0058 + (1 + 1 / 0.7) * 0.00276
  | 4 => (1 + 0.45) * 0.0140 + (1 + 1 / 0.45) * 0.00276
  | 5 => (1 + 0.3) * 0.0288 + (1 + 1 / 0.3) * 0.00276
  | 6 => (1 + 0.23) * 0.0515 + (1 + 1 / 0.23) * 0.00276
  | 7 => (1 + 0.18) * 0.0835 + (1 + 1 / 0.18) * 0.00276
  | 8 => (1 + 0.15) * 0.1255 + (1 + 1 / 0.15) * 0.00276
  | 9 => (1 + 0.125) * 0.1765 + (1 + 1 / 0.125) * 0.00276
  | 10 => (1 + 0.11) * 0.2355 + (1 + 1 / 0.11) * 0.00276
  | 11 => (1 + 0.096) * 0.2995 + (1 + 1 / 0.096) * 0.00276
  | 12 => (1 + 0.087) * 0.3660 + (1 + 1 / 0.087) * 0.00276
  | 13 => (1 + 0.08) * 0.4315 + (1 + 1 / 0.08) * 0.00276
  | _ => 0

theorem certG_nonneg (k : ℕ) : 0 ≤ certG k := by
  unfold certG
  split <;> norm_num

theorem ref_le {θ : ℝ} (hθ : 0 ≤ θ) : θ / (Real.pi * Real.log 2) ≤ θ / 2.1775856 :=
  div_le_div_of_nonneg_left hθ (by norm_num) pi_mul_log_two_bounds.1

theorem ref_ge {θ : ℝ} (hθ : 0 ≤ θ) : θ / 2.1775864 ≤ θ / (Real.pi * Real.log 2) :=
  div_le_div_of_nonneg_left hθ (by nlinarith [pi_mul_log_two_bounds.1])
    pi_mul_log_two_bounds.2

theorem cert_hWk : ∀ k < 14, (3 / 10 : ℝ) - certG k ≤ archimedeanWeilSymbol (k * (1 / 10)) := by
  intro k hk
  interval_cases k
  · have := gridSymbol_0
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_1
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_2
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_3
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_4
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_5
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_6
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_7
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_8
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_9
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_10
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_11
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_12
    norm_num [certG] at this ⊢
    linarith
  · have := gridSymbol_13
    norm_num [certG] at this ⊢
    linarith

theorem cert_hWK : (3 / 10 : ℝ) ≤ archimedeanWeilSymbol ((14 : ℕ) * (1 / 10)) := by
  have := gridSymbol_14
  norm_num at this ⊢
  linarith

theorem cert_hR : ∀ k : ℕ, k < 14 → ∀ f : suzukiApertureHilbert halfLogTwoAperture,
    inner ℂ (ccmPolarL2Vector halfLogTwoAperture (1 / 2)) f.1 = 0 →
    inner ℂ (ccmPolarL2Vector halfLogTwoAperture (-1 / 2)) f.1 = 0 →
    ∀ ξ : ℝ, (k : ℝ) * (1 / 10) ≤ |ξ| → |ξ| < ((k : ℝ) + 1) * (1 / 10) →
      ‖𝓕 (f.1 : ℝ → ℂ) ξ‖ ^ 2 ≤ certR k * ‖f‖ ^ 2 := by
  intro k hk f hplus hminus ξ hlo hhi
  interval_cases k
  · have h1 := ref_le (θ := (1089 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (1089 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 4) (by norm_num) shellResidual_0
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (3266 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (3266 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 2) (by norm_num) shellResidual_1
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (5444 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (5444 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 1.2) (by norm_num) shellResidual_2
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (7622 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (7622 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.7) (by norm_num) shellResidual_3
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (9799 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (9799 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.45) (by norm_num) shellResidual_4
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (11977 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (11977 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.3) (by norm_num) shellResidual_5
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (14154 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (14154 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.23) (by norm_num) shellResidual_6
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (16332 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (16332 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.18) (by norm_num) shellResidual_7
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (18509 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (18509 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.15) (by norm_num) shellResidual_8
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (20687 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (20687 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.125) (by norm_num) shellResidual_9
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (22865 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (22865 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.11) (by norm_num) shellResidual_10
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (25042 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (25042 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.096) (by norm_num) shellResidual_11
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (27220 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (27220 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.087) (by norm_num) shellResidual_12
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi
  · have h1 := ref_le (θ := (29397 / 10000 : ℝ)) (by norm_num)
    have h2 := ref_ge (θ := (29397 / 10000 : ℝ)) (by norm_num)
    exact shell_fourier_bound (η := 0.08) (by norm_num) shellResidual_13
      (by norm_num at h1 ⊢; linarith) (by norm_num at h2 ⊢; linarith) f hplus hminus ξ hlo hhi

/-- **Weil positivity on the pole-vanishing subspace at `√2`, without numerical assistance.**
The pole-vanishing ground energy of the exact restricted Weil form at the aperture `½ log 2`
(multiplicative support `[2^{-1/2}, 2^{1/2}]`) is at least `1/10`. -/
theorem one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo :
    (1 / 10 : ℝ) ≤ ccmRestrictedWeilPolarGroundEnergy halfLogTwoAperture := by
  have h := le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo_of_grid (α := 3 / 10)
    (h := 1 / 10) (K := 14) (G := certG) (R := certR) (by norm_num) certG_nonneg cert_hWk
    cert_hWK cert_hR
  refine le_trans ?_ h
  norm_num [Finset.sum_range_succ, certG, certR]

/-- **Weil positivity with the first prime past `√2`.**  There is an aperture strictly beyond
`½ log 2` up to which the pole-vanishing restricted Weil form, including the prime `2`, is
positive definite on its form domain. -/
theorem exists_polarGroundEnergy_pos_past_halfLogTwo :
    ∃ b : SuzukiPositiveAperture, halfLogTwoAperture.1 < b.1 ∧
      ∀ c : SuzukiPositiveAperture, c.1 ≤ b.1 → 0 < ccmRestrictedWeilPolarGroundEnergy c := by
  have hpos : 0 < ccmRestrictedWeilPolarGroundEnergy halfLogTwoAperture :=
    lt_of_lt_of_le (by norm_num) one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo
  have hev := eventually_ccmRestrictedWeilPolarGroundEnergy_pos hpos
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hball⟩ := hev
  refine ⟨⟨halfLogTwoAperture.1 + ε / 2, by
    have := halfLogTwoAperture.property; linarith⟩, by simp; linarith, ?_⟩
  intro c hc
  by_cases hcle : c.1 ≤ halfLogTwoAperture.1
  · have hanti := ccmRestrictedWeilPolarGroundEnergy_antitone (a := c) (b := halfLogTwoAperture)
      hcle
    linarith
  · push Not at hcle
    apply hball
    rw [Subtype.dist_eq, Real.dist_eq, abs_lt]
    constructor <;> simp at hc <;> linarith

end RHTower
