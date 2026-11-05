import GaloisForLFunctions.FiniteFreeProbability.XiJensenCircleFormula
import GaloisForLFunctions.FiniteFreeProbability.GammaFactorSlope

/-!
# The saddle model of the Jensen polynomials of `Ξ`

Let `a₀`, `τ₁` satisfy `(a₀ − ix) τ₁ = d`. On the circle `τ = τ₁ e^{iφ}` the exponential `e^{(a₀ − ix)τ}` is exactly
`e^{d e^{iφ}}`, and Cauchy's formula gives `∫_{−π}^{π} e^{d(e^{iφ} − iφ)} dφ = 2π d^d/d!`. Comparing `ξ(1/2 + τ)` with the
exponential `G(τ₁) e^{a₀(τ − τ₁)}` on the half-circle formula yields the exact identity

`R_d(x) = 2 Re[(x + i a₀)^d G(τ₁) e^{−a₀ τ₁} (1 + ε)]`,

where `ε` is the mean of `Q − 1`, `Q = ξ(1/2 + τ) / (G(τ₁) e^{a₀(τ − τ₁)})`, against the weight `(d!/2π d^d) e^{d(e^{iφ} − iφ)}` of
total mass `1` and size `≲ √d e^{−d(1 − cos φ)}`, together with the part of the weight on the left half-circle.

When `a₀ = a(τ₁)` is the slope of `G` at `τ₁`, `Q` is close to `1` near `φ = 0`, and `|ε|` is small once `Re a₀` and `Re τ₁` are large.
No property of the zeros enters: the only input from `ζ` is a polynomial bound on `Re s ≥ 1/2` and its approach to `1`.
-/

open Polynomial Filter Topology Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-! ## The exact weight -/

/-- `W_d(φ) = exp(d e^{iφ} − i d φ)`. -/
def saddleWeight (d : ℕ) (φ : ℝ) : ℂ := Complex.exp ((d : ℂ) * Complex.exp (φ * I) - d * φ * I)

theorem continuous_saddleWeight (d : ℕ) : Continuous (saddleWeight d) := by
  unfold saddleWeight
  fun_prop

theorem norm_saddleWeight (d : ℕ) (φ : ℝ) : ‖saddleWeight d φ‖ = Real.exp (d * Real.cos φ) := by
  rw [saddleWeight, Complex.norm_exp]
  congr 1
  simp [Complex.exp_ofReal_mul_I_re]

theorem saddleWeight_periodic (d : ℕ) : Function.Periodic (saddleWeight d) (2 * π) := by
  intro φ
  have h1 : Complex.exp (((φ + 2 * π : ℝ) : ℂ) * I) = Complex.exp (φ * I) := by
    have : ((φ + 2 * π : ℝ) : ℂ) * I = φ * I + 2 * π * I := by
      push_cast
      ring
    rw [this, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h2 : (d : ℂ) * Complex.exp (φ * I) - d * ((φ + 2 * π : ℝ) : ℂ) * I =
      ((d : ℂ) * Complex.exp (φ * I) - d * φ * I) - d * (2 * π * I) := by
    push_cast
    ring
  simp only [saddleWeight]
  rw [h1, h2]
  exact Complex.exp_periodic.sub_nat_mul_eq d _

/-- The total mass of the weight is Cauchy's formula for `e^{dζ}`. -/
theorem integral_saddleWeight_zero (d : ℕ) :
    ∫ φ in (0 : ℝ)..(2 * π), saddleWeight d φ = 2 * π * (d : ℂ) ^ d / (d.factorial : ℂ) := by
  have hdiff : Differentiable ℂ fun ζ : ℂ => Complex.exp ((d : ℂ) * ζ) := by fun_prop
  have hc := (hdiff.differentiableOn (s := Metric.closedBall 0 1)).circleIntegral_one_div_sub_center_pow_smul
    one_pos d
  rw [iteratedDeriv_cexp_const_mul] at hc
  have hint : (∮ z in C(0, 1), (1 / (z - 0) ^ (d + 1)) • Complex.exp ((d : ℂ) * z)) =
      I * ∫ φ in (0 : ℝ)..(2 * π), saddleWeight d φ := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    have hz : Complex.exp (φ * I) ≠ 0 := Complex.exp_ne_zero _
    have hw : saddleWeight d φ = Complex.exp ((d : ℂ) * Complex.exp (φ * I)) / Complex.exp (φ * I) ^ d := by
      rw [saddleWeight, Complex.exp_sub, ← Complex.exp_nat_mul]
      congr 2
      ring
    simp only [deriv_circleMap, circleMap, ofReal_one, one_mul, zero_add, sub_zero, smul_eq_mul, pow_succ, hw]
    field_simp
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  apply mul_left_cancel₀ hI
  rw [← hint, hc]
  simp only [smul_eq_mul, mul_zero, Complex.exp_zero, mul_one]
  ring

theorem integral_saddleWeight (d : ℕ) (a : ℝ) :
    ∫ φ in a..(a + 2 * π), saddleWeight d φ = 2 * π * (d : ℂ) ^ d / (d.factorial : ℂ) := by
  have h := (saddleWeight_periodic d).intervalIntegral_add_eq 0 a
  rw [zero_add] at h
  rw [← h, integral_saddleWeight_zero]

/-! ## The comparison function and the exact identity -/

/-- `Q(φ) = ξ(1/2 + τ) / (G(τ₁) e^{a₀(τ − τ₁)})`, `τ = τ₁ e^{iφ}`. -/
def saddleRatio (a₀ τ₁ : ℂ) (φ : ℝ) : ℂ :=
  xiCentered (τ₁ * Complex.exp (φ * I)) * Complex.exp (-(a₀ * τ₁ * (Complex.exp (φ * I) - 1))) / gammaFactor τ₁

theorem continuous_saddleRatio (a₀ τ₁ : ℂ) : Continuous (saddleRatio a₀ τ₁) := by
  unfold saddleRatio
  refine Continuous.div_const (Continuous.mul ?_ (by fun_prop)) _
  exact differentiable_xiCentered.continuous.comp (by fun_prop)

theorem circleMap_arg_add {τ₁ : ℂ} (φ : ℝ) :
    circleMap 0 ‖τ₁‖ (Complex.arg τ₁ + φ) = τ₁ * Complex.exp (φ * I) := by
  have h := Complex.norm_mul_exp_arg_mul_I τ₁
  simp only [circleMap, zero_add]
  conv_rhs => rw [← h]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- The circle integrand is the weight times the ratio. -/
theorem jensenCircleTerm_arg_add {d : ℕ} {x : ℝ} {a₀ τ₁ : ℂ} (hτ₁ : τ₁ ≠ 0) (hG : gammaFactor τ₁ ≠ 0)
    (hs : (a₀ - I * x) * τ₁ = d) (φ : ℝ) :
    jensenCircleTerm d x ‖τ₁‖ (Complex.arg τ₁ + φ) =
      gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) / τ₁ ^ d * (saddleWeight d φ * saddleRatio a₀ τ₁ φ) := by
  set E := Complex.exp (φ * I) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have h1 : Complex.exp (-(I * x * (τ₁ * E))) = Complex.exp ((d : ℂ) * E) * Complex.exp (-(a₀ * (τ₁ * E))) := by
    rw [← Complex.exp_add]
    congr 1
    linear_combination (-E) * hs
  have h2 : saddleWeight d φ = Complex.exp ((d : ℂ) * E) / E ^ d := by
    rw [saddleWeight, Complex.exp_sub, hE, ← Complex.exp_nat_mul]
    congr 2
    ring
  have h3 : Complex.exp (-(a₀ * τ₁)) * Complex.exp (-(a₀ * τ₁ * (E - 1))) = Complex.exp (-(a₀ * (τ₁ * E))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [jensenCircleTerm, circleMap_arg_add, h2, saddleRatio, ← hE, h1, mul_pow, ← h3]
  field_simp

/-- The defect `ε`. -/
def saddleError (d : ℕ) (a₀ τ₁ : ℂ) : ℂ :=
  ((d.factorial : ℂ) / (2 * π * (d : ℂ) ^ d)) *
    ((∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
        saddleWeight d φ * (saddleRatio a₀ τ₁ φ - 1)) -
      ∫ φ in (π / 2 - Complex.arg τ₁)..(-(π / 2) - Complex.arg τ₁ + 2 * π), saddleWeight d φ)

/-- **The exact saddle identity.** -/
theorem eval_jensenRev_xiSeries_eq_saddle {d : ℕ} (hd : 0 < d) {x : ℝ} {a₀ τ₁ : ℂ} (hτ₁ : τ₁ ≠ 0)
    (hG : gammaFactor τ₁ ≠ 0) (hs : (a₀ - I * x) * τ₁ = d) :
    (jensenRev d xiSeries).eval (x : ℂ) =
      ((2 * (((x : ℂ) + I * a₀) ^ d * gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) *
        (1 + saddleError d a₀ τ₁)).re : ℝ) : ℂ) := by
  have hρ : 0 < ‖τ₁‖ := norm_pos_iff.2 hτ₁
  set θ := Complex.arg τ₁ with hθ
  have hW := continuous_saddleWeight d
  have hQ := continuous_saddleRatio a₀ τ₁
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hfact : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set K := gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) / τ₁ ^ d with hK
  have hB : ∫ t in (-(π / 2))..(π / 2), jensenCircleTerm d x ‖τ₁‖ t =
      K * ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * saddleRatio a₀ τ₁ φ := by
    rw [← intervalIntegral.integral_const_mul]
    have h := intervalIntegral.integral_comp_add_left (a := -(π / 2) - θ) (b := π / 2 - θ)
      (jensenCircleTerm d x ‖τ₁‖) θ
    rw [show θ + (-(π / 2) - θ) = -(π / 2) by ring, show θ + (π / 2 - θ) = π / 2 by ring] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun φ _ => jensenCircleTerm_arg_add hτ₁ hG hs φ
  have hsplit : ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * saddleRatio a₀ τ₁ φ =
      (2 * π * (d : ℂ) ^ d / (d.factorial : ℂ)) * (1 + saddleError d a₀ τ₁) := by
    have h1 : ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * saddleRatio a₀ τ₁ φ =
        (∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ) +
          ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * (saddleRatio a₀ τ₁ φ - 1) := by
      rw [← intervalIntegral.integral_add (hW.intervalIntegrable _ _)
        ((hW.mul (hQ.sub continuous_const)).intervalIntegrable _ _)]
      refine intervalIntegral.integral_congr fun φ _ => ?_
      simp only
      ring
    have h2 : (∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ) +
        ∫ φ in (π / 2 - θ)..(-(π / 2) - θ + 2 * π), saddleWeight d φ =
          2 * π * (d : ℂ) ^ d / (d.factorial : ℂ) := by
      rw [intervalIntegral.integral_add_adjacent_intervals (hW.intervalIntegrable _ _)
        (hW.intervalIntegrable _ _), integral_saddleWeight]
    rw [h1, saddleError, ← hθ]
    have hdpow : (d : ℂ) ^ d ≠ 0 := pow_ne_zero _ hdC
    set U := ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ
    set V := ∫ φ in (π / 2 - θ)..(-(π / 2) - θ + 2 * π), saddleWeight d φ
    set Y := ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * (saddleRatio a₀ τ₁ φ - 1)
    have hU : U = 2 * π * (d : ℂ) ^ d / (d.factorial : ℂ) - V := by rw [← h2]; ring
    rw [hU]
    field_simp
    ring
  rw [eval_jensenRev_xiSeries_eq_half_circle d x hρ, hB, hsplit]
  congr 1
  have hτd : (I * (d : ℂ) / τ₁) = (x : ℂ) + I * a₀ := by
    rw [div_eq_iff hτ₁, ← hs]
    ring_nf
    rw [I_sq]
    ring
  have hmain : I ^ d * (K * ((2 * π * (d : ℂ) ^ d / (d.factorial : ℂ)) * (1 + saddleError d a₀ τ₁))) =
      (((2 * π / d.factorial : ℝ) : ℂ)) * (((x : ℂ) + I * a₀) ^ d * gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) *
        (1 + saddleError d a₀ τ₁)) := by
    rw [← hτd, div_pow, mul_pow, hK]
    push_cast
    have hτd0 : τ₁ ^ d ≠ 0 := pow_ne_zero _ hτ₁
    field_simp
  rw [hmain, Complex.re_ofReal_mul]
  have hf : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  have hπ' : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  push_cast
  field_simp

/-! ## The ratio near the saddle -/

theorem re_mul_exp {τ₁ : ℂ} (ψ : ℝ) :
    (τ₁ * Complex.exp (ψ * I)).re = ‖τ₁‖ * Real.cos (Complex.arg τ₁ + ψ) := by
  rw [← circleMap_arg_add]
  simp [circleMap, Complex.exp_ofReal_mul_I_re, ← Complex.ofReal_add]
  left
  rw [show ((Complex.arg τ₁ : ℂ) + ψ) * I = (((Complex.arg τ₁ + ψ : ℝ) : ℂ)) * I by push_cast; rfl,
    Complex.exp_ofReal_mul_I_re]

theorem norm_mul_exp {τ₁ : ℂ} (ψ : ℝ) : ‖τ₁ * Complex.exp (ψ * I)‖ = ‖τ₁‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- Along the circle the slope of `G` moves at unit speed up to the factor `6`. -/
theorem norm_gammaSlope_mul_exp_sub_le {τ₁ : ℂ} (hρ : 4 ≤ ‖τ₁‖) {σ T : ℝ} (hσ : |σ| = 1) (hT : 0 ≤ T)
    (hre : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ (τ₁ * Complex.exp (((σ * t : ℝ) : ℂ) * I)).re) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    ‖gammaSlope (τ₁ * Complex.exp (((σ * t : ℝ) : ℂ) * I)) - gammaSlope τ₁‖ ≤ 6 * t := by
  have hρ0 : 0 < ‖τ₁‖ := by linarith
  set c : ℝ → ℂ := fun u => τ₁ * Complex.exp (((σ * u : ℝ) : ℂ) * I) with hc
  have hnorm : ∀ u, ‖c u‖ = ‖τ₁‖ := fun u => norm_mul_exp _
  have hne : ∀ u, c u ≠ 1 / 2 := fun u h => by
    have h1 := hnorm u
    rw [h, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at h1
    linarith
  have hcd : ∀ u, HasDerivAt c (I * σ * c u) u := fun u => by
    have h1 : HasDerivAt (fun u : ℝ => (((σ * u : ℝ) : ℂ)) * I) ((σ : ℂ) * I) u := by
      have h := ((hasDerivAt_id u).const_mul σ).ofReal_comp
      have h2 := h.mul_const I
      simpa using h2
    have h2 := (h1.cexp).const_mul τ₁
    refine h2.congr_deriv ?_
    simp only [hc]
    ring
  have hder : ∀ u ∈ Ico (0 : ℝ) t, HasDerivWithinAt (fun u => gammaSlope (c u))
      (gammaSlopeDeriv (c u) * (I * σ * c u)) (Ici u) u := fun u hu => by
    have hu' : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.le.trans ht.2⟩
    exact ((hasDerivAt_gammaSlope (hre u hu') (hne u)).comp u (hcd u)).hasDerivWithinAt
  have hcont : ContinuousOn (fun u => gammaSlope (c u)) (Icc 0 t) := fun u hu => by
    have hu' : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.trans ht.2⟩
    exact ((hasDerivAt_gammaSlope (hre u hu') (hne u)).comp u (hcd u)).continuousAt.continuousWithinAt
  have hbound : ∀ u ∈ Ico (0 : ℝ) t, ‖gammaSlopeDeriv (c u) * (I * σ * c u)‖ ≤ 6 := fun u hu => by
    have hu' : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.le.trans ht.2⟩
    have h := norm_gammaSlopeDeriv_le (hre u hu') (by rw [hnorm]; exact hρ)
    rw [norm_mul, norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hσ, one_mul,
      hnorm]
    rw [hnorm] at h
    calc _ ≤ 6 / ‖τ₁‖ * ‖τ₁‖ := by gcongr
      _ = 6 := by field_simp
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hcont hder hbound t (right_mem_Icc.2 ht.1)
  have h0 : c 0 = τ₁ := by simp [hc]
  simpa [h0, hc] using h

/-- **Grönwall on the circle.** `G(τ) e^{−a₀(τ − τ₁)}/G(τ₁)` stays within `e^{6ρφ²} − 1` of `1`. -/
theorem norm_gammaRatio_sub_one_le {τ₁ : ℂ} (hρ : 4 ≤ ‖τ₁‖) {σ T : ℝ} (hσ : |σ| = 1) (hT : 0 < T)
    (hre : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ (τ₁ * Complex.exp (((σ * t : ℝ) : ℂ) * I)).re) :
    ‖gammaFactor (τ₁ * Complex.exp (((σ * T : ℝ) : ℂ) * I)) *
        Complex.exp (-(gammaSlope τ₁ * τ₁ * (Complex.exp (((σ * T : ℝ) : ℂ) * I) - 1))) / gammaFactor τ₁ - 1‖ ≤
      Real.exp (6 * ‖τ₁‖ * T ^ 2) - 1 := by
  have hρ0 : 0 < ‖τ₁‖ := by linarith
  have hτ0 : τ₁ ≠ 0 := norm_pos_iff.1 hρ0
  set a₀ := gammaSlope τ₁
  set c : ℝ → ℂ := fun u => τ₁ * Complex.exp (((σ * u : ℝ) : ℂ) * I) with hc
  have hnorm : ∀ u, ‖c u‖ = ‖τ₁‖ := fun u => norm_mul_exp _
  have hne : ∀ u, c u ≠ 1 / 2 := fun u h => by
    have h1 := hnorm u
    rw [h, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at h1
    linarith
  have hre1 : (0 : ℝ) ≤ τ₁.re := by
    have := hre 0 ⟨le_rfl, hT.le⟩
    simpa using this
  have hne1 : τ₁ ≠ 1 / 2 := by
    intro h
    rw [h, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at hρ
    linarith
  have hG1 := gammaFactor_ne_zero hre1 hne1
  have hcd : ∀ u, HasDerivAt c (I * σ * c u) u := fun u => by
    have h1 : HasDerivAt (fun u : ℝ => (((σ * u : ℝ) : ℂ)) * I) ((σ : ℂ) * I) u := by
      have h := ((hasDerivAt_id u).const_mul σ).ofReal_comp
      have h2 := h.mul_const I
      simpa using h2
    have h2 := (h1.cexp).const_mul τ₁
    refine h2.congr_deriv ?_
    simp only [hc]
    ring
  set f : ℝ → ℂ := fun u => gammaFactor (c u) * Complex.exp (-(a₀ * (c u - τ₁))) / gammaFactor τ₁ - 1 with hf
  have hf' : ∀ u ∈ Icc (0 : ℝ) T, HasDerivAt f
      ((I * σ * c u) * (gammaSlope (c u) - a₀) * (f u + 1)) u := fun u hu => by
    have h1 := (hasDerivAt_gammaFactor (hre u hu) (hne u)).comp u (hcd u)
    have h2 : HasDerivAt (fun u => Complex.exp (-(a₀ * (c u - τ₁))))
        (Complex.exp (-(a₀ * (c u - τ₁))) * (-(a₀ * (I * σ * c u)))) u :=
      (((hcd u).sub_const τ₁).const_mul a₀).neg.cexp
    have h3 := ((h1.mul h2).div_const (gammaFactor τ₁)).sub_const 1
    refine h3.congr_deriv ?_
    simp only [hf, Function.comp_def, sub_add_cancel]
    ring
  have hzero : f 0 = 0 := by
    simp [hf, hc, div_self hG1]
  set K := 6 * ‖τ₁‖ * T with hK
  have hKpos : 0 < K := by positivity
  have hb : ∀ u ∈ Ico (0 : ℝ) T,
      ‖(I * σ * c u) * (gammaSlope (c u) - a₀) * (f u + 1)‖ ≤ K * ‖f u‖ + K := fun u hu => by
    have hu' : u ∈ Icc (0 : ℝ) T := ⟨hu.1, hu.2.le⟩
    have h1 := norm_gammaSlope_mul_exp_sub_le hρ hσ hT.le hre hu'
    have h2 : ‖I * σ * c u‖ = ‖τ₁‖ := by
      rw [norm_mul, norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, hσ, one_mul, hnorm]
    have h3 : ‖(I * σ * c u) * (gammaSlope (c u) - a₀)‖ ≤ K := by
      rw [norm_mul, h2]
      calc _ ≤ ‖τ₁‖ * (6 * u) := by gcongr
        _ ≤ ‖τ₁‖ * (6 * T) := by gcongr; exact hu.2.le
        _ = K := by rw [hK]; ring
    rw [norm_mul]
    calc _ ≤ K * (‖f u‖ + 1) := by
          gcongr
          exact (norm_add_le _ _).trans (by simp)
      _ = _ := by ring
  have hgr := norm_le_gronwallBound_of_norm_deriv_right_le (f := f) (δ := 0) (K := K) (ε := K) (a := 0) (b := T)
    (fun u hu => (hf' u hu).continuousAt.continuousWithinAt)
    (fun u hu => (hf' u ⟨hu.1, hu.2.le⟩).hasDerivWithinAt) (by rw [hzero, norm_zero]) hb T
    (right_mem_Icc.2 hT.le)
  rw [gronwallBound_of_K_ne_0 hKpos.ne'] at hgr
  simp only [sub_zero, zero_mul, zero_add, div_self hKpos.ne', one_mul] at hgr
  have he : K * T = 6 * ‖τ₁‖ * T ^ 2 := by rw [hK]; ring
  rw [he] at hgr
  convert hgr using 2
  simp only [hf, hc]
  congr 3
  ring

/-- The two-sided form of the Grönwall bound on the part of the circle in `Re τ ≥ 0`. -/
theorem norm_gammaRatio_sub_one_le_of_mem {τ₁ : ℂ} (hρ : 4 ≤ ‖τ₁‖) (hre1 : 0 < τ₁.re) {φ : ℝ}
    (hφ : φ ∈ Icc (-(π / 2) - Complex.arg τ₁) (π / 2 - Complex.arg τ₁)) :
    ‖gammaFactor (τ₁ * Complex.exp (φ * I)) *
        Complex.exp (-(gammaSlope τ₁ * τ₁ * (Complex.exp (φ * I) - 1))) / gammaFactor τ₁ - 1‖ ≤
      Real.exp (6 * ‖τ₁‖ * φ ^ 2) - 1 := by
  have hθ : |Complex.arg τ₁| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.2 (Or.inl hre1)
  have hθ' := abs_lt.1 hθ
  have hne1 : τ₁ ≠ 1 / 2 := by
    intro h
    rw [h, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num] at hρ
    linarith
  rcases eq_or_ne φ 0 with rfl | hφ0
  · simp [div_self (gammaFactor_ne_zero hre1.le hne1)]
  obtain ⟨σ, hσ, hsφ⟩ : ∃ σ : ℝ, |σ| = 1 ∧ σ * |φ| = φ := by
    rcases le_or_gt 0 φ with h | h
    · exact ⟨1, by simp, by rw [one_mul, abs_of_nonneg h]⟩
    · exact ⟨-1, by simp, by rw [abs_of_neg h]; ring⟩
  have hT : 0 < |φ| := abs_pos.2 hφ0
  have hre : ∀ t ∈ Icc (0 : ℝ) |φ|, 0 ≤ (τ₁ * Complex.exp (((σ * t : ℝ) : ℂ) * I)).re := by
    intro t ht
    rw [re_mul_exp]
    refine mul_nonneg (norm_nonneg _) (Real.cos_nonneg_of_mem_Icc ?_)
    have hσ' : σ = 1 ∨ σ = -1 := by
      rcases abs_eq (zero_le_one' ℝ) |>.1 hσ with h | h <;> simp [h]
    rcases le_or_gt 0 φ with h | h
    · rw [abs_of_nonneg h] at ht
      have hs1 : σ = 1 := by
        rcases hσ' with hh | hh
        · exact hh
        · rw [hh, abs_of_nonneg h] at hsφ
          have : φ = 0 := by linarith
          exact absurd this hφ0
      rw [hs1]
      constructor <;> linarith [hφ.1, hφ.2, ht.1, ht.2, hθ'.1, hθ'.2]
    · rw [abs_of_neg h] at ht
      have hs1 : σ = -1 := by
        rcases hσ' with hh | hh
        · rw [hh, abs_of_neg h] at hsφ
          linarith
        · exact hh
      rw [hs1]
      constructor <;> linarith [hφ.1, hφ.2, ht.1, ht.2, hθ'.1, hθ'.2]
  have h := norm_gammaRatio_sub_one_le hρ hσ hT hre
  rw [hsφ, sq_abs] at h
  exact h

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eval_jensenRev_xiSeries_eq_saddle
#print axioms FiniteFreeProbability.norm_gammaRatio_sub_one_le_of_mem
