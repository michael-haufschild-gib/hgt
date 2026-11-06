import GaloisForLFunctions.FiniteFreeProbability.JensenSaddleError

/-!
# The upper transform of the Jensen polynomials of `Ξ`

At a complex point `z` the Cauchy integral for `R_d(Ξ)` splits along the imaginary axis of the
`τ`-plane into the entire function `E_ρ(z) = (d!/2π) i^d ∫_{|θ|≤π/2} e^{-izτ} ξ(1/2+τ) τ^{-d} dθ` and
its reflection: `R_d(z) = E_ρ(z) + conj E_ρ(conj z)`.

Around a saddle `(a₀ - iz₀) τ₁ = d`, every value of `E_{|τ₁|}` is a weighted mean:
`E_{|τ₁|}(w) = M e^{c} 𝓜(c)`, `c = -i(w - z₀)τ₁`, where `M` is the saddle main term and `𝓜` averages
`Q(φ) e^{c(e^{iφ} - 1)}` against the weight `W_d` of total mass `1`. The mean at `c = 0` is `1 + ε`,
with `ε` the defect of the saddle identity.
-/

open Polynomial Filter Topology Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry RHTower
open scoped Real

namespace FiniteFreeProbability

noncomputable section

/-- The Cauchy integrand at a complex evaluation point. -/
def jensenTerm (d : ℕ) (z : ℂ) (ρ θ : ℝ) : ℂ :=
  Complex.exp (-(I * z * circleMap 0 ρ θ)) * xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d

theorem continuous_jensenTerm (d : ℕ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous (jensenTerm d z ρ) := by
  unfold jensenTerm
  refine Continuous.div ?_ ?_ fun θ => pow_ne_zero _ (circleMap_ne_center hρ.ne')
  · exact (Complex.continuous_exp.comp (by fun_prop)).mul
      (differentiable_xiCentered.continuous.comp (continuous_circleMap 0 ρ))
  · exact (continuous_circleMap 0 ρ).pow d

theorem jensenTerm_periodic (d : ℕ) (z : ℂ) (ρ : ℝ) :
    Function.Periodic (jensenTerm d z ρ) (2 * π) := by
  intro θ
  have h : circleMap 0 ρ (θ + 2 * π) = circleMap 0 ρ θ := periodic_circleMap 0 ρ θ
  simp only [jensenTerm, h]

/-- Cauchy's formula at a complex point. -/
theorem integral_jensenTerm (d : ℕ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    I ^ d * (d.factorial : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), jensenTerm d z ρ θ =
      (2 * π : ℝ) * (jensenRev d xiSeries).eval z := by
  set h : ℂ → ℂ := fun τ => Complex.exp (-(I * z * τ)) * xiCentered τ with hh
  have hd : Differentiable ℂ h := by
    simp only [hh]
    exact (Complex.differentiable_exp.comp (by fun_prop)).mul differentiable_xiCentered
  have hc := (hd.differentiableOn (s := Metric.closedBall 0 ρ)).circleIntegral_one_div_sub_center_pow_smul
    hρ d
  have hfact : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hint : (∮ w in C(0, ρ), (1 / (w - 0) ^ (d + 1)) • h w) =
      I * ∫ θ in (0 : ℝ)..(2 * π), jensenTerm d z ρ θ := by
    rw [circleIntegral, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    have hw : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρ.ne'
    simp only [deriv_circleMap, jensenTerm, sub_zero, smul_eq_mul, hh, pow_succ]
    field_simp
  have hcomp : iteratedDeriv d h 0 = (-I) ^ d * (jensenRev d xiSeries).eval z := by
    rw [← taylorPS_XiC, eval_jensenRev_taylorPS XiC_differentiable]
    have hfun : h = fun τ => (fun w => Complex.exp (z * w) * XiC w) (-I * τ) := by
      funext τ
      simp only [hh]
      rw [XiC_eq_xiCentered]
      congr 2
      · ring
      · rw [← mul_assoc]
        simp
    have hg : ContDiff ℂ d fun w => Complex.exp (z * w) * XiC w :=
      (((Complex.differentiable_exp.comp (by fun_prop)).mul XiC_differentiable)).contDiff
    rw [hfun, iteratedDeriv_comp_const_mul hg]
    simp
  have hmain : I * ∫ θ in (0 : ℝ)..(2 * π), jensenTerm d z ρ θ =
      (2 * π * I / (d.factorial : ℂ)) * ((-I) ^ d * (jensenRev d xiSeries).eval z) := by
    rw [← hint, hc, hcomp, smul_eq_mul]
  have hIneg : I ^ d * (-I) ^ d = 1 := by
    rw [← mul_pow]
    simp
  have hcancel : ∫ θ in (0 : ℝ)..(2 * π), jensenTerm d z ρ θ =
      (2 * π / (d.factorial : ℂ)) * ((-I) ^ d * (jensenRev d xiSeries).eval z) := by
    apply mul_left_cancel₀ hI
    rw [hmain]
    ring
  rw [hcancel]
  push_cast
  have e : I ^ d * (d.factorial : ℂ) * (2 * π / (d.factorial : ℂ) * ((-I) ^ d * (jensenRev d xiSeries).eval z)) =
      2 * π * (jensenRev d xiSeries).eval z * (I ^ d * (-I) ^ d) := by
    field_simp
  rw [e, hIneg, mul_one]

theorem jensenTerm_add_pi (d : ℕ) (z : ℂ) (ρ θ : ℝ) :
    jensenTerm d z ρ (θ + π) =
      (-1) ^ d * (Complex.exp (I * z * circleMap 0 ρ θ) * xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d) := by
  have hw : circleMap 0 ρ (θ + π) = -circleMap 0 ρ θ := by
    simp only [circleMap, zero_add, ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  rw [jensenTerm, hw, xiCentered_neg, neg_pow]
  have hexp : -(I * z * -circleMap 0 ρ θ) = I * z * circleMap 0 ρ θ := by ring
  have h2 : ((-1 : ℂ) ^ d) * (-1) ^ d = 1 := by rw [← mul_pow]; simp
  have hp : ((-1 : ℂ) ^ d)⁻¹ = (-1) ^ d := inv_eq_of_mul_eq_one_right h2
  rw [hexp, div_eq_mul_inv, mul_inv, hp, div_eq_mul_inv]
  ring

/-- Reflection in the real axis exchanges `z` and its conjugate. -/
theorem jensenTerm_conj (d : ℕ) (z : ℂ) (ρ θ : ℝ) :
    Complex.exp (I * z * circleMap 0 ρ (-θ)) * xiCentered (circleMap 0 ρ (-θ)) / circleMap 0 ρ (-θ) ^ d =
      (starRingEnd ℂ) (jensenTerm d ((starRingEnd ℂ) z) ρ θ) := by
  have hw : circleMap 0 ρ (-θ) = (starRingEnd ℂ) (circleMap 0 ρ θ) := by
    simp only [circleMap, zero_add, map_mul, conj_ofReal, ← Complex.exp_conj, conj_I, ofReal_neg]
    congr 2
    ring
  rw [hw, jensenTerm, xiCentered_conj, map_div₀, map_mul, map_pow, ← Complex.exp_conj]
  congr 3
  simp only [map_neg, map_mul, conj_I, starRingEnd_self_apply]
  ring

/-- The upper transform `E_ρ`. -/
def jensenUpper (d : ℕ) (ρ : ℝ) (z : ℂ) : ℂ :=
  (d.factorial : ℂ) / (2 * π) * (I ^ d * ∫ θ in (-(π / 2))..(π / 2), jensenTerm d z ρ θ)

/-- **Splitting of `R_d(Ξ)` at a complex point.** -/
theorem eval_eq_jensenUpper_add_conj (d : ℕ) (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) :
    (jensenRev d xiSeries).eval z =
      jensenUpper d ρ z + (starRingEnd ℂ) (jensenUpper d ρ ((starRingEnd ℂ) z)) := by
  set B := ∫ θ in (-(π / 2))..(π / 2), jensenTerm d z ρ θ with hB
  set B' := ∫ θ in (-(π / 2))..(π / 2), jensenTerm d ((starRingEnd ℂ) z) ρ θ with hB'
  have hcont := continuous_jensenTerm d z hρ
  have hshift : ∫ θ in (0 : ℝ)..(2 * π), jensenTerm d z ρ θ =
      ∫ θ in (-(π / 2))..(3 * π / 2), jensenTerm d z ρ θ := by
    have h := (jensenTerm_periodic d z ρ).intervalIntegral_add_eq 0 (-(π / 2))
    rw [zero_add] at h
    rw [h]
    congr 1
    ring
  have hsplit : ∫ θ in (-(π / 2))..(3 * π / 2), jensenTerm d z ρ θ =
      B + ∫ θ in (π / 2)..(3 * π / 2), jensenTerm d z ρ θ :=
    (intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)).symm
  have hsecond : ∫ θ in (π / 2)..(3 * π / 2), jensenTerm d z ρ θ =
      (-1) ^ d * (starRingEnd ℂ) B' := by
    have h1 : ∫ θ in (π / 2)..(3 * π / 2), jensenTerm d z ρ θ =
        ∫ θ in (-(π / 2))..(π / 2), jensenTerm d z ρ (θ + π) := by
      rw [intervalIntegral.integral_comp_add_right (jensenTerm d z ρ) π]
      congr 1 <;> ring
    rw [h1, hB', ← intervalIntegral_conj]
    simp only [jensenTerm_add_pi]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hneg := intervalIntegral.integral_comp_neg (a := -(π / 2)) (b := π / 2)
      (fun θ => Complex.exp (I * z * circleMap 0 ρ θ) * xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d)
    rw [neg_neg] at hneg
    rw [← hneg]
    exact intervalIntegral.integral_congr fun θ _ => jensenTerm_conj d z ρ θ
  have hfull := integral_jensenTerm d z hρ
  rw [hshift, hsplit, hsecond] at hfull
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hfact : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have hconj : (starRingEnd ℂ) (jensenUpper d ρ ((starRingEnd ℂ) z)) =
      (d.factorial : ℂ) / (2 * π) * (I ^ d * ((-1) ^ d * (starRingEnd ℂ) B')) := by
    rw [jensenUpper, map_mul, map_mul, map_div₀, map_mul, map_pow, conj_I, neg_pow,
      Complex.conj_natCast, Complex.conj_ofReal, map_ofNat]
    ring
  have h2π : ((2 * π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * π : ℝ) ≠ 0)
  apply mul_left_cancel₀ h2π
  rw [← hfull, hconj, jensenUpper, ← hB]
  push_cast
  field_simp

/-- The upper transform is entire. -/
theorem differentiable_jensenUpper (d : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Differentiable ℂ (jensenUpper d ρ) := by
  intro w₀
  have hg : Continuous fun θ : ℝ => xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d :=
    Continuous.div (differentiable_xiCentered.continuous.comp (continuous_circleMap 0 ρ))
      ((continuous_circleMap 0 ρ).pow d) fun θ => pow_ne_zero _ (circleMap_ne_center hρ.ne')
  set G : ℝ → ℂ := fun θ => xiCentered (circleMap 0 ρ θ) / circleMap 0 ρ θ ^ d with hGdef
  have hterm (w : ℂ) (θ : ℝ) :
      jensenTerm d w ρ θ = Complex.exp (-(I * w * circleMap 0 ρ θ)) * G θ := by
    simp only [jensenTerm, hGdef]
    ring
  have hnorm (θ : ℝ) : ‖circleMap 0 ρ θ‖ = ρ := by
    simp [circleMap, abs_of_pos hρ]
  let F' : ℂ → ℝ → ℂ := fun w θ =>
    (-(I * circleMap 0 ρ θ)) * (Complex.exp (-(I * w * circleMap 0 ρ θ)) * G θ)
  have hderiv (w : ℂ) (θ : ℝ) :
      HasDerivAt (fun v : ℂ => jensenTerm d v ρ θ) (F' w θ) w := by
    have h0 : HasDerivAt (fun v : ℂ => (-(I * circleMap 0 ρ θ)) * v)
        (-(I * circleMap 0 ρ θ)) w := by
      simpa using (hasDerivAt_id w).const_mul (-(I * circleMap 0 ρ θ))
    have h1 : HasDerivAt (fun v : ℂ => -(I * v * circleMap 0 ρ θ))
        (-(I * circleMap 0 ρ θ)) w :=
      h0.congr_of_eventuallyEq (Eventually.of_forall fun v => by ring)
    have h2 := (h1.cexp.mul_const (G θ))
    refine (h2.congr_deriv ?_).congr_of_eventuallyEq (Eventually.of_forall fun v => hterm v θ)
    simp only [F']
    ring
  have hmain : HasDerivAt (fun w => ∫ θ in (-(π / 2))..(π / 2), jensenTerm d w ρ θ)
      (∫ θ in (-(π / 2))..(π / 2), F' w₀ θ) w₀ := by
    refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (s := Metric.ball w₀ 1)
      (bound := fun θ => ρ * Real.exp ((‖w₀‖ + 1) * ρ) * ‖G θ‖) (Metric.ball_mem_nhds w₀ one_pos)
      ?_ ?_ ?_ ?_ ?_ ?_).2
    · exact Eventually.of_forall fun w => (continuous_jensenTerm d w hρ).aestronglyMeasurable
    · exact (continuous_jensenTerm d w₀ hρ).intervalIntegrable _ _
    · have : Continuous (F' w₀) := by
        simp only [F']
        exact ((continuous_const.mul (continuous_circleMap 0 ρ)).neg).mul
          ((Complex.continuous_exp.comp ((continuous_const.mul
            (continuous_circleMap 0 ρ)).neg)).mul hg)
      exact this.aestronglyMeasurable
    · refine Eventually.of_forall fun θ _ w hw => ?_
      simp only [F', norm_mul, norm_neg, Complex.norm_I, one_mul, hnorm]
      have hwn : ‖w‖ ≤ ‖w₀‖ + 1 := by
        have h := norm_le_norm_add_norm_sub' w w₀
        have hd : ‖w - w₀‖ < 1 := by simpa [dist_eq_norm] using hw
        linarith
      have he : ‖Complex.exp (-(I * w * circleMap 0 ρ θ))‖ ≤ Real.exp ((‖w₀‖ + 1) * ρ) := by
        refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.2 ?_)
        rw [norm_neg, norm_mul, norm_mul, Complex.norm_I, one_mul, hnorm]
        exact mul_le_mul_of_nonneg_right hwn hρ.le
      calc
        ρ * (‖Complex.exp (-(I * w * circleMap 0 ρ θ))‖ * ‖G θ‖) ≤
            ρ * (Real.exp ((‖w₀‖ + 1) * ρ) * ‖G θ‖) := by gcongr
        _ = _ := by ring
    · exact ((continuous_const.mul hg.norm).intervalIntegrable _ _)
    · exact Eventually.of_forall fun θ _ w _ => hderiv w θ
  have hc : DifferentiableAt ℂ (fun w => ∫ θ in (-(π / 2))..(π / 2), jensenTerm d w ρ θ) w₀ :=
    hmain.differentiableAt
  unfold jensenUpper
  exact ((differentiableAt_const _).mul ((differentiableAt_const _).mul hc))

/-! ## The saddle mean -/

/-- The normalization `F_d = d!/(2π d^d)` of the weight. -/
def saddleF (d : ℕ) : ℂ := (d.factorial : ℂ) / (2 * π * (d : ℂ) ^ d)

/-- The mean of `Q(φ) e^{c(e^{iφ} - 1)}` over the right half-circle against `W_d`. -/
def saddleMean (d : ℕ) (a₀ τ₁ c : ℂ) : ℂ :=
  saddleF d * ∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
    saddleWeight d φ * saddleRatio a₀ τ₁ φ * Complex.exp (c * (Complex.exp (φ * I) - 1))

/-- The Cauchy integrand at the saddle circle, displaced to another evaluation point. -/
theorem jensenTerm_arg_add {d : ℕ} {z₀ w a₀ τ₁ : ℂ} (hτ₁ : τ₁ ≠ 0) (hG : gammaFactor τ₁ ≠ 0)
    (hs : (a₀ - I * z₀) * τ₁ = d) (φ : ℝ) :
    jensenTerm d w ‖τ₁‖ (Complex.arg τ₁ + φ) =
      gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) / τ₁ ^ d *
        (saddleWeight d φ * saddleRatio a₀ τ₁ φ *
          Complex.exp (-(I * (w - z₀) * (τ₁ * Complex.exp (φ * I))))) := by
  set E := Complex.exp (φ * I) with hE
  have hE0 : E ≠ 0 := Complex.exp_ne_zero _
  have h1 : Complex.exp (-(I * w * (τ₁ * E))) =
      Complex.exp ((d : ℂ) * E) * Complex.exp (-(a₀ * (τ₁ * E))) *
        Complex.exp (-(I * (w - z₀) * (τ₁ * E))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination E * hs
  have h2 : saddleWeight d φ = Complex.exp ((d : ℂ) * E) / E ^ d := by
    rw [saddleWeight, Complex.exp_sub, hE, ← Complex.exp_nat_mul]
    congr 2
    ring
  have h3 : Complex.exp (-(a₀ * τ₁)) * Complex.exp (-(a₀ * τ₁ * (E - 1))) =
      Complex.exp (-(a₀ * (τ₁ * E))) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [jensenTerm, circleMap_arg_add, h2, saddleRatio, ← hE, h1, mul_pow, ← h3]
  field_simp

/-- `e^{c e^{iφ}} = e^{c} e^{c(e^{iφ} - 1)}`. -/
theorem exp_displacement (w z₀ τ₁ E : ℂ) :
    Complex.exp (-(I * (w - z₀) * (τ₁ * E))) =
      Complex.exp (-(I * (w - z₀) * τ₁)) * Complex.exp (-(I * (w - z₀) * τ₁) * (E - 1)) := by
  rw [← Complex.exp_add]
  congr 1
  ring

/-- **The upper transform as a saddle integral.** -/
theorem jensenUpper_eq_integral {d : ℕ} (hd : 0 < d) {z₀ w a₀ τ₁ : ℂ} (hτ₁ : τ₁ ≠ 0)
    (hG : gammaFactor τ₁ ≠ 0) (hs : (a₀ - I * z₀) * τ₁ = d) :
    jensenUpper d ‖τ₁‖ w =
      (z₀ + I * a₀) ^ d * gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) *
        (saddleF d * ∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
          saddleWeight d φ * saddleRatio a₀ τ₁ φ *
            Complex.exp (-(I * (w - z₀) * (τ₁ * Complex.exp (φ * I))))) := by
  set θ := Complex.arg τ₁ with hθ
  set Y := ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * saddleRatio a₀ τ₁ φ *
    Complex.exp (-(I * (w - z₀) * (τ₁ * Complex.exp (φ * I)))) with hY
  have hB : ∫ t in (-(π / 2))..(π / 2), jensenTerm d w ‖τ₁‖ t =
      gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) / τ₁ ^ d * Y := by
    rw [hY, ← intervalIntegral.integral_const_mul]
    have h := intervalIntegral.integral_comp_add_left (a := -(π / 2) - θ) (b := π / 2 - θ)
      (jensenTerm d w ‖τ₁‖) θ
    rw [show θ + (-(π / 2) - θ) = -(π / 2) by ring, show θ + (π / 2 - θ) = π / 2 by ring] at h
    rw [← h]
    exact intervalIntegral.integral_congr fun φ _ => jensenTerm_arg_add hτ₁ hG hs φ
  have hτd : I * (d : ℂ) / τ₁ = z₀ + I * a₀ := by
    rw [div_eq_iff hτ₁, ← hs]
    ring_nf
    rw [I_sq]
    ring
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hτd0 : τ₁ ^ d ≠ 0 := pow_ne_zero _ hτ₁
  have hdpow : (d : ℂ) ^ d ≠ 0 := pow_ne_zero _ hdC
  rw [jensenUpper, hB, ← hτd, div_pow, mul_pow, saddleF]
  field_simp

/-- **The upper transform as a saddle mean.** -/
theorem jensenUpper_eq_mean {d : ℕ} (hd : 0 < d) {z₀ w a₀ τ₁ : ℂ} (hτ₁ : τ₁ ≠ 0)
    (hG : gammaFactor τ₁ ≠ 0) (hs : (a₀ - I * z₀) * τ₁ = d) :
    jensenUpper d ‖τ₁‖ w =
      (z₀ + I * a₀) ^ d * gammaFactor τ₁ * Complex.exp (-(a₀ * τ₁)) *
        (Complex.exp (-(I * (w - z₀) * τ₁)) * saddleMean d a₀ τ₁ (-(I * (w - z₀) * τ₁))) := by
  have h : ∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
        saddleWeight d φ * saddleRatio a₀ τ₁ φ *
          Complex.exp (-(I * (w - z₀) * (τ₁ * Complex.exp (φ * I)))) =
      Complex.exp (-(I * (w - z₀) * τ₁)) *
        ∫ φ in (-(π / 2) - Complex.arg τ₁)..(π / 2 - Complex.arg τ₁),
          saddleWeight d φ * saddleRatio a₀ τ₁ φ *
            Complex.exp (-(I * (w - z₀) * τ₁) * (Complex.exp (φ * I) - 1)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [exp_displacement w z₀ τ₁]
    ring
  rw [jensenUpper_eq_integral hd hτ₁ hG hs, saddleMean, h]
  ring

/-- The mean at `c = 0` is `1 + ε`. -/
theorem saddleMean_zero {d : ℕ} (hd : 0 < d) (a₀ τ₁ : ℂ) :
    saddleMean d a₀ τ₁ 0 = 1 + saddleError d a₀ τ₁ := by
  set θ := Complex.arg τ₁ with hθ
  have hW := continuous_saddleWeight d
  have hQ := continuous_saddleRatio a₀ τ₁
  have hdC : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hfact : (d.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 d.factorial_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * saddleRatio a₀ τ₁ φ *
        Complex.exp (0 * (Complex.exp (φ * I) - 1)) =
      (∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ) +
        ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * (saddleRatio a₀ τ₁ φ - 1) := by
    have hI1 : IntervalIntegrable (fun φ => saddleWeight d φ) volume (-(π / 2) - θ) (π / 2 - θ) :=
      hW.intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun φ => saddleWeight d φ * (saddleRatio a₀ τ₁ φ - 1)) volume
        (-(π / 2) - θ) (π / 2 - θ) := (hW.mul (hQ.sub continuous_const)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add hI1 hI2]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [zero_mul, Complex.exp_zero, mul_one]
    ring
  have h2 : (∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ) +
      ∫ φ in (π / 2 - θ)..(-(π / 2) - θ + 2 * π), saddleWeight d φ =
        2 * π * (d : ℂ) ^ d / (d.factorial : ℂ) := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hW.intervalIntegrable _ _)
      (hW.intervalIntegrable _ _), integral_saddleWeight]
  rw [saddleMean, ← hθ, h1, saddleError, ← hθ, saddleF]
  have hdpow : (d : ℂ) ^ d ≠ 0 := pow_ne_zero _ hdC
  set U := ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ
  set V := ∫ φ in (π / 2 - θ)..(-(π / 2) - θ + 2 * π), saddleWeight d φ
  set Y := ∫ φ in (-(π / 2) - θ)..(π / 2 - θ), saddleWeight d φ * (saddleRatio a₀ τ₁ φ - 1)
  have hU : U = 2 * π * (d : ℂ) ^ d / (d.factorial : ℂ) - V := by rw [← h2]; ring
  rw [hU]
  field_simp
  ring

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eval_eq_jensenUpper_add_conj
#print axioms FiniteFreeProbability.differentiable_jensenUpper
#print axioms FiniteFreeProbability.jensenUpper_eq_mean
#print axioms FiniteFreeProbability.saddleMean_zero
