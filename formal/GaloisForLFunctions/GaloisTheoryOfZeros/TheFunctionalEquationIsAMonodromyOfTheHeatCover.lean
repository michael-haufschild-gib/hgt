import GaloisForLFunctions.GaloisTheoryOfZeros.TheSheetsOfACollisionAreAllItsZeros
import GaloisForLFunctions.RHTower.FiniteZeroSubquadraticRigidity

/-!
# The functional equation is a monodromy of the heat cover

The heat cover is ramified, unconditionally. The centre value `τ ↦ H_τ(0) = ∫ Φ(x) e^{τx²} dx` is
an entire function of the time. It has order at most `3/2`
(`exists_norm_complexHeat_center_le`), and along the real axis it grows faster than every
exponential, because the weight `Φ` has mass arbitrarily far out
(`exists_lt_log_norm_complexHeat_center`). An entire function with these two properties has
infinitely many zeros. Hence:

* `infinite_centerTimes`: there are infinitely many complex times `τ₀` with `H_τ₀(0) = 0`;
* `im_ne_zero_of_complexHeat_center_eq_zero`: none of them is real, since `H_t(0) > 0`;
* `exists_isCollision_center`: at each of them an even number `m ≥ 2` of zeros collide at the
  centre;
* `infinite_branchTimes`: the heat cover has infinitely many branch points.

At a collision at the centre the turn of the time around `τ₀` carries each colliding zero `z` to
`−z` (`neg_collisionZero_center`). So the reflection of the functional equation, which is a deck
transformation of the heat cover, is realized there as its local monodromy
(`infinite_setOf_center_monodromy`). Complex conjugation is realized as a local monodromy exactly at
the real collisions, and the Riemann hypothesis says that there is none at a positive time.
-/

open Complex MeasureTheory Filter Topology Set Metric
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The centre value at real times -/

theorem complexHeat_ofReal_center (t : ℝ) :
    complexHeat (t : ℂ) 0 = ((∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ) := by
  have h := integral_ofReal (μ := (volume : Measure ℝ)) (𝕜 := ℂ)
    (f := fun x : ℝ => riemannKernelReal x * Real.exp (t * x ^ 2))
  rw [complexHeat]
  refine Eq.trans ?_ h
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  show (riemannKernelReal x : ℂ) * cexp ((t : ℂ) * (x : ℂ) ^ 2 + I * 0 * x) =
    ((riemannKernelReal x * Real.exp (t * x ^ 2) : ℝ) : ℂ)
  rw [mul_zero, zero_mul, add_zero, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem integrable_riemannKernelReal_mul_exp (t : ℝ) :
    Integrable fun x : ℝ => riemannKernelReal x * Real.exp (t * x ^ 2) := by
  have h := (integrable_complexWeight_mul_pow_mul_exp (t : ℂ) 0 0).norm
  refine h.congr (Eventually.of_forall fun x => ?_)
  have hpos := riemannKernelReal_pos x
  have hre : ((t : ℂ) * (x : ℂ) ^ 2).re = t * x ^ 2 := by
    rw [show (t : ℂ) * (x : ℂ) ^ 2 = ((t * x ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  simp only [pow_zero, mul_one, mul_zero, zero_mul, Complex.exp_zero, complexWeight, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, Complex.norm_exp, hre]

/-- A lower bound for the centre value at a real time by the part of the weight on an interval. -/
theorem le_integral_riemannKernelReal_mul_exp {t a b μ L : ℝ} (hab : a ≤ b)
    (hμ : ∀ x ∈ Icc a b, μ ≤ riemannKernelReal x) (hL : ∀ x ∈ Icc a b, L ≤ t * x ^ 2) :
    μ * Real.exp L * (b - a) ≤ ∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2) := by
  have hint := integrable_riemannKernelReal_mul_exp t
  calc μ * Real.exp L * (b - a) = ∫ _ in Icc a b, μ * Real.exp L := by
        rw [setIntegral_const, Measure.real, Real.volume_Icc,
          ENNReal.toReal_ofReal (by linarith), smul_eq_mul, mul_comm]
    _ ≤ ∫ x in Icc a b, riemannKernelReal x * Real.exp (t * x ^ 2) := by
        refine setIntegral_mono_on ?_ hint.integrableOn measurableSet_Icc fun x hx => ?_
        · exact integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
        · exact mul_le_mul (hμ x hx) (Real.exp_le_exp.mpr (hL x hx)) (Real.exp_pos _).le
            (riemannKernelReal_pos x).le
    _ ≤ ∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2) :=
        setIntegral_le_integral hint (Eventually.of_forall fun x =>
          mul_nonneg (riemannKernelReal_pos x).le (Real.exp_pos _).le)

/-- The weight is bounded below by a positive constant on every compact interval. -/
theorem exists_pos_le_riemannKernelReal {a b : ℝ} (hab : a ≤ b) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ x ∈ Icc a b, μ ≤ riemannKernelReal x := by
  obtain ⟨x₀, -, hmin⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMinOn
    (nonempty_Icc.mpr hab) continuous_riemannKernelReal.continuousOn
  exact ⟨riemannKernelReal x₀, riemannKernelReal_pos x₀, fun x hx => isMinOn_iff.mp hmin x hx⟩

/-- **At a real time the centre value is positive.** -/
theorem integral_riemannKernelReal_mul_exp_pos (t : ℝ) :
    0 < ∫ x : ℝ, riemannKernelReal x * Real.exp (t * x ^ 2) := by
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_riemannKernelReal (zero_le_one' ℝ)
  have h := le_integral_riemannKernelReal_mul_exp (t := t) (L := -|t|) (zero_le_one' ℝ) hμle
    fun x hx => by
      have hx2 : x ^ 2 ≤ 1 := by nlinarith [hx.1, hx.2]
      nlinarith [neg_abs_le t, abs_nonneg t, sq_nonneg x]
  have hpos : 0 < μ * Real.exp (-|t|) * (1 - 0) := by positivity
  exact hpos.trans_le h

/-- A time at which the family vanishes at the centre is not real. -/
theorem im_ne_zero_of_complexHeat_center_eq_zero {τ : ℂ} (h : complexHeat τ 0 = 0) :
    τ.im ≠ 0 := by
  intro him
  have hτ : τ = (τ.re : ℂ) := Complex.ext rfl (by rw [Complex.ofReal_im]; exact him)
  rw [hτ, complexHeat_ofReal_center, Complex.ofReal_eq_zero] at h
  exact (integral_riemannKernelReal_mul_exp_pos τ.re).ne' h

/-! ## Growth of the centre value in the time -/

/-- A quadratic is absorbed by half of an exponential at the cost `(1 + T)^{3/2}`: with `w = u²`
and `κ w³ ≤ (B/2) e^{bu}`, either `w` is at most a multiple of `√(1 + T)` or `κ w² ≥ T`. -/
private theorem exists_sq_le_half_exp_add {B b : ℝ} (hB : 0 < B) (hb : 0 < b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T u : ℝ, 0 ≤ T → 0 ≤ u →
      T * u ^ 2 ≤ B / 2 * Real.exp (b * u) + K * (1 + T) ^ (3 / 2 : ℝ) := by
  set κ : ℝ := B / 2 * b ^ 6 / 720 with hκ
  have hκpos : 0 < κ := by positivity
  refine ⟨1 + 1 / κ, by positivity, fun T u hT hu => ?_⟩
  have hexp : κ * u ^ 6 ≤ B / 2 * Real.exp (b * u) := by
    have h6 := Real.pow_div_factorial_le_exp (b * u) (by positivity) 6
    have h720 : ((6 : ℕ).factorial : ℝ) = 720 := by norm_num [Nat.factorial]
    rw [h720] at h6
    rw [show κ * u ^ 6 = B / 2 * ((b * u) ^ 6 / 720) by rw [hκ]; ring]
    exact mul_le_mul_of_nonneg_left h6 (by positivity)
  set S : ℝ := Real.sqrt (1 + T) with hS
  have hS2 : S ^ 2 = 1 + T := Real.sq_sqrt (by linarith)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hrpow : (1 + T) ^ (3 / 2 : ℝ) = (1 + T) * S := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_one_add' (by linarith) (by norm_num),
      ← Real.sqrt_eq_rpow]
  have hκinv : 0 < 1 / κ := by positivity
  set lam : ℝ := S * (1 + 1 / κ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  -- `κ λ² ≥ T`
  have hlam2 : T ≤ κ * lam ^ 2 := by
    have e : κ * lam ^ 2 = (1 + T) * (κ + 2 + 1 / κ) := by
      rw [hlam, mul_pow, hS2]
      field_simp
      ring
    rw [e]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + T) (by positivity : (0 : ℝ) ≤ κ + 1 / κ)]
  set w : ℝ := u ^ 2 with hw
  have hw0 : 0 ≤ w := by positivity
  have hmain : T * w ≤ κ * w ^ 3 + T * lam := by
    rcases le_or_gt w lam with h | h
    · have h1 : T * w ≤ T * lam := mul_le_mul_of_nonneg_left h hT
      have h2 : 0 ≤ κ * w ^ 3 := by positivity
      linarith
    · have h1 : lam ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hlam0 h.le 2
      have h2 : T ≤ κ * w ^ 2 := hlam2.trans (mul_le_mul_of_nonneg_left h1 hκpos.le)
      have h3 : T * w ≤ κ * w ^ 2 * w := mul_le_mul_of_nonneg_right h2 hw0
      have h4 : 0 ≤ T * lam := mul_nonneg hT hlam0
      nlinarith
  have hlast : T * lam ≤ (1 + 1 / κ) * ((1 + T) * S) := by
    rw [hlam]
    nlinarith [mul_nonneg hS0 (by positivity : (0 : ℝ) ≤ 1 + 1 / κ)]
  rw [hrpow]
  calc T * u ^ 2 ≤ κ * w ^ 3 + T * lam := hmain
    _ = κ * u ^ 6 + T * lam := by rw [hw]; ring
    _ ≤ B / 2 * Real.exp (b * u) + (1 + 1 / κ) * ((1 + T) * S) := add_le_add hexp hlast

/-- **The centre value has order at most `3/2` in the time.** -/
theorem exists_norm_complexHeat_center_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℂ, ‖complexHeat τ 0‖ ≤ Real.exp (C * (1 + ‖τ‖) ^ (3 / 2 : ℝ)) := by
  obtain ⟨A, B, b, c, hA, hB, hb, hc, hdecay⟩ := riemannKernel_superExp.decay
  obtain ⟨K, hK, hsq⟩ := exists_sq_le_half_exp_add hB hb
  have hβpos : 0 < B * b ^ 2 / 4 := by positivity
  have hgauss : Integrable fun x : ℝ => Real.exp (-(B * b ^ 2 / 4) * x ^ 2) :=
    integrable_exp_neg_mul_sq hβpos
  set J : ℝ := ∫ x : ℝ, Real.exp (-(B * b ^ 2 / 4) * x ^ 2) with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun x => (Real.exp_pos _).le
  -- the weight at the time `τ` is below a Gaussian with a constant of order `3/2`
  have hpt : ∀ (τ : ℂ) (x : ℝ), ‖complexWeight τ x‖ ≤
      A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) *
        Real.exp (-(B * b ^ 2 / 4) * x ^ 2) := by
    intro τ x
    have hpos := riemannKernelReal_pos x
    have hw : ‖heatWeight ‖τ‖ x‖ = riemannKernelReal x * Real.exp (‖τ‖ * x ^ 2) := by
      rw [heatWeight, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (mul_pos hpos (Real.exp_pos _))]
    have h2 := hsq (c + ‖τ‖) |x| (by positivity) (abs_nonneg x)
    rw [sq_abs] at h2
    have h3 := exp_neg_half_doubleExp_le hB hb x
    have hE : 0 ≤ A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) :=
      mul_nonneg hA (Real.exp_pos _).le
    calc ‖complexWeight τ x‖ ≤ riemannKernelReal x * Real.exp (‖τ‖ * x ^ 2) :=
          (norm_complexWeight_le τ x).trans hw.le
      _ ≤ A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2) * Real.exp (‖τ‖ * x ^ 2) :=
          mul_le_mul_of_nonneg_right (hdecay x) (Real.exp_pos _).le
      _ = A * Real.exp (-(B * Real.exp (b * |x|)) + c * x ^ 2 + ‖τ‖ * x ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]
      _ ≤ A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ) +
            -(B / 2 * Real.exp (b * |x|))) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hA
      _ = A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) *
            Real.exp (-(B / 2 * Real.exp (b * |x|))) := by
          rw [Real.exp_add, mul_assoc]
      _ ≤ A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) *
            Real.exp (-(B * b ^ 2 / 4) * x ^ 2) := mul_le_mul_of_nonneg_left h3 hE
  have hc32 : 0 ≤ (1 + c) ^ (3 / 2 : ℝ) := Real.rpow_nonneg (by linarith) _
  refine ⟨A * J + K * (1 + c) ^ (3 / 2 : ℝ),
    add_nonneg (mul_nonneg hA hJ0) (mul_nonneg hK hc32), fun τ => ?_⟩
  have hnorm : ‖complexHeat τ 0‖ ≤ A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) * J := by
    have hE : ∀ x : ℝ, complexWeight τ x * cexp (I * 0 * x) = complexWeight τ x := fun x => by
      simp
    rw [complexHeat_eq_expTransform, expTransform]
    simp_rw [hE]
    calc ‖∫ x : ℝ, complexWeight τ x‖
        ≤ ∫ x : ℝ, A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) *
            Real.exp (-(B * b ^ 2 / 4) * x ^ 2) :=
          norm_integral_le_of_norm_le (hgauss.const_mul _) (Eventually.of_forall (hpt τ))
      _ = A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) * J := by rw [integral_const_mul]
  have hτ0 := norm_nonneg τ
  set P : ℝ := (1 + ‖τ‖) ^ (3 / 2 : ℝ) with hP
  have hP1 : 1 ≤ P := Real.one_le_rpow (by linarith) (by norm_num)
  have hrp : (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ) ≤ (1 + c) ^ (3 / 2 : ℝ) * P := by
    rw [hP, ← Real.mul_rpow (by linarith) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith) (by norm_num)
  have hAJ0 : 0 ≤ A * J := mul_nonneg hA hJ0
  have hAJ : A * J ≤ Real.exp (A * J * P) := by
    have h1 : A * J ≤ A * J * P := le_mul_of_one_le_right hAJ0 hP1
    linarith [Real.add_one_le_exp (A * J * P)]
  calc ‖complexHeat τ 0‖ ≤ A * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) * J := hnorm
    _ = A * J * Real.exp (K * (1 + (c + ‖τ‖)) ^ (3 / 2 : ℝ)) := by ring
    _ ≤ Real.exp (A * J * P) * Real.exp (K * ((1 + c) ^ (3 / 2 : ℝ) * P)) :=
        mul_le_mul hAJ (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hrp hK))
          (Real.exp_pos _).le (Real.exp_pos _).le
    _ = Real.exp ((A * J + K * (1 + c) ^ (3 / 2 : ℝ)) * P) := by
        rw [← Real.exp_add]
        congr 1
        ring

/-- **Along the real time axis the centre value grows faster than every exponential**: the weight
has mass on `[R, R + 1]` for every `R`. -/
theorem exists_lt_log_norm_complexHeat_center (A : ℝ) :
    ∃ σ : ℝ, 1 ≤ σ ∧ A * σ < Real.log ‖complexHeat (σ : ℂ) 0‖ := by
  set R : ℝ := |A| + 1 with hR
  have hR0 : 0 ≤ R := by positivity
  have hR1 : A + 1 ≤ R ^ 2 := by
    rw [hR]
    nlinarith [abs_nonneg A, le_abs_self A]
  obtain ⟨μ, hμ, hμle⟩ := exists_pos_le_riemannKernelReal (by linarith : R ≤ R + 1)
  set σ : ℝ := 1 + |Real.log μ| with hσ
  have hσ1 : 1 ≤ σ := by
    rw [hσ]
    linarith [abs_nonneg (Real.log μ)]
  refine ⟨σ, hσ1, ?_⟩
  have hlow := le_integral_riemannKernelReal_mul_exp (t := σ) (L := σ * R ^ 2)
    (by linarith : R ≤ R + 1) hμle fun x hx =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hx.1 2) (by linarith)
  rw [show R + 1 - R = 1 by ring, mul_one] at hlow
  have hpos : 0 < μ * Real.exp (σ * R ^ 2) := by positivity
  rw [complexHeat_ofReal_center, Complex.norm_real, Real.norm_eq_abs]
  calc A * σ < Real.log μ + σ * R ^ 2 := by
        nlinarith [neg_abs_le (Real.log μ),
          mul_nonneg (by linarith : (0 : ℝ) ≤ σ) (by linarith : (0 : ℝ) ≤ R ^ 2 - A - 1)]
    _ = Real.log (μ * Real.exp (σ * R ^ 2)) := by
        rw [Real.log_mul hμ.ne' (Real.exp_pos _).ne', Real.log_exp]
    _ ≤ Real.log |∫ x : ℝ, riemannKernelReal x * Real.exp (σ * x ^ 2)| :=
        Real.log_le_log hpos (hlow.trans (le_abs_self _))

/-! ## Collisions at the centre -/

/-- The centre value is an entire function of the time. -/
theorem differentiable_complexHeat_center : Differentiable ℂ fun τ : ℂ => complexHeat τ 0 := by
  intro τ
  have h1 : DifferentiableAt ℂ (fun p : ℂ × ℂ => complexHeat p.1 p.2) (τ, 0) :=
    (analyticAt_complexHeat (τ, 0)).differentiableAt
  have h2 : DifferentiableAt ℂ (fun τ : ℂ => (τ, (0 : ℂ))) τ := by fun_prop
  have h3 := h1.comp τ h2
  exact h3

/-- **Central collisions exist.** There are infinitely many complex times `τ` with
`H_τ(0) = 0`. -/
theorem infinite_centerTimes : {τ : ℂ | complexHeat τ 0 = 0}.Infinite := by
  obtain ⟨C, hC, hgrow⟩ := exists_norm_complexHeat_center_le
  exact zeroSet_infinite_of_subquadratic_superlinear_ray differentiable_complexHeat_center
    (by norm_num) (by norm_num) hC hgrow exists_lt_log_norm_complexHeat_center

/-- At a time with `H_τ(0) = 0` an even number `m ≥ 2` of zeros collide at the centre. -/
theorem exists_isCollision_center {τ : ℂ} (h : complexHeat τ 0 = 0) :
    ∃ m, 2 ≤ m ∧ Even m ∧ IsCollision τ 0 m := by
  obtain ⟨m, hm1, hc⟩ := exists_isCollision h
  have he := hc.even_of_center
  refine ⟨m, ?_, he, hc⟩
  obtain ⟨k, hk⟩ := he
  omega

theorem mem_branchTimes_of_complexHeat_center_eq_zero {τ : ℂ} (h : complexHeat τ 0 = 0) :
    τ ∈ branchTimes := by
  obtain ⟨m, hm2, -, hc⟩ := exists_isCollision_center h
  have hd := hc.vanish 1 (by omega)
  rw [iteratedDeriv_one] at hd
  exact ⟨(τ, 0), ⟨h, hd⟩, rfl⟩

/-- **The heat cover has infinitely many branch points.** -/
theorem infinite_branchTimes : branchTimes.Infinite :=
  infinite_centerTimes.mono fun _ h => mem_branchTimes_of_complexHeat_center_eq_zero h

/-- **The functional equation is a monodromy of the heat cover.** There are infinitely many complex
times `τ₀`, none of them real, at which an even number `m ≥ 2` of zeros collide at the centre, and
the turn of the time around `τ₀` carries the zero on each sheet to its negative. -/
theorem infinite_setOf_center_monodromy :
    {τ₀ : ℂ | τ₀.im ≠ 0 ∧ ∃ m, 2 ≤ m ∧ Even m ∧ IsCollision τ₀ 0 m ∧
      ∀ ρ, heatModelFwd m ρ = 0 →
        ∀ᶠ s in 𝓝 0, -collisionZero τ₀ 0 m ρ s = collisionZero τ₀ 0 m ρ (-s)}.Infinite :=
  infinite_centerTimes.mono fun τ h => by
    obtain ⟨m, hm2, he, hc⟩ := exists_isCollision_center h
    exact ⟨im_ne_zero_of_complexHeat_center_eq_zero h, m, hm2, he, hc,
      fun ρ hρ => neg_collisionZero_center hc hρ⟩

end

end GaloisForLFunctions.GaloisTheoryOfZeros
