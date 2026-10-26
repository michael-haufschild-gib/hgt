import GaloisForLFunctions.ArithmeticDefectRigidity.OnePrimeEulerLawsLeavePeriodicGhosts
import Mathlib.Analysis.Fourier.AddCircle

/-!
# Twisted one-prime laws on the line force tied exponents

Complex version of the one-prime ghost calculus on the log scale. A twisted law with period `τ`
and multiplier `e^{(κ + iγ)τ}`, `κ > 0`, asks `g − e^{(κ+iγ)τ} g(· − τ) ∈ L²`
(`twistedDefect`). Rotating by `e^{-iγu}` turns it into two real one-prime laws, so
`g = e^{(κ+iγ)u} Π − e^{iγu} S` with `Π` a.e. `τ`-periodic and `S ∈ L²`
(`exists_twisted_ghost_decomposition`).

For two laws with incommensurable periods `τ₂, τ₃` and the same growth `κ`
(`exists_lintegral_sub_const_mul_cexp_ne_top`): either `g ∈ L²`, or `g − c e^{zu} ∈ L²` where the
exponent `z` is tied, `e^{zτ₂} = e^{(κ+iγ₂)τ₂}` and `e^{zτ₃} = e^{(κ+iγ₃)τ₃}`. The ghost `G₃`
becomes an eigenfunction of the rotation by `τ₂` on `ℝ/τ₃ℤ`; Parseval forces a nonzero Fourier
coefficient, which fixes the eigenvalue as a character value, and ergodicity makes the twisted ghost
constant (`eigenfunction_of_irrational_rotation`).
-/

open MeasureTheory Filter Topology Set Complex
open scoped Real

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-! ### Exact periodization -/

/-- The `b`-periodic function agreeing with `F` on the fundamental domain `(0, b]`. -/
def periodize (b : ℝ) [hb : Fact (0 < b)] {E : Type*} (F : ℝ → E) (u : ℝ) : E :=
  F (toIocMod hb.out 0 u)

section Periodize

variable {b : ℝ} [hb : Fact (0 < b)] {E : Type*}

omit hb in
theorem ae_periodic_intMul' {F : ℝ → E} (hper : ∀ᵐ u : ℝ, F (u + b) = F u) (k : ℤ) :
    ∀ᵐ u : ℝ, F (u + k * b) = F u := by
  induction k using Int.induction_on with
  | zero => simp
  | succ k ih =>
    filter_upwards [ih, ae_comp_add_right hper ((k : ℤ) * b)] with u h1 h2
    rw [show u + ((k : ℤ) + 1 : ℤ) * b = u + (k : ℤ) * b + b by push_cast; ring, h2, h1]
  | pred k ih =>
    filter_upwards [ih, ae_comp_add_right hper ((-(k : ℤ) - 1 : ℤ) * b)] with u h1 h2
    rw [show u + (-(k : ℤ) - 1 : ℤ) * b + b = u + (-(k : ℤ) : ℤ) * b by push_cast; ring] at h2
    rw [← h2, h1]

theorem coe_eq_coe_toIocMod (u : ℝ) :
    (u : AddCircle b) = ((toIocMod hb.out 0 u : ℝ) : AddCircle b) := by
  have h : (u : AddCircle b) =
      ((toIocMod hb.out 0 u + toIocDiv hb.out 0 u • b : ℝ) : AddCircle b) := by
    rw [toIocMod_add_toIocDiv_zsmul]
  rw [h, AddCircle.coe_add, AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]

theorem measurable_toIocMod : Measurable (toIocMod hb.out (0 : ℝ)) := by
  have h : toIocMod hb.out (0 : ℝ) =
      fun u : ℝ => ((AddCircle.equivIoc b 0 (u : AddCircle b) : Ioc 0 (0 + b)) : ℝ) := by
    funext u
    rw [coe_eq_coe_toIocMod u, AddCircle.equivIoc_coe_eq (toIocMod_mem_Ioc hb.out 0 u)]
  rw [h]
  exact measurable_subtype_coe.comp
    ((AddCircle.measurableEquivIoc b 0).measurable.comp AddCircle.measurable_mk')

theorem periodize_periodic (F : ℝ → E) : Function.Periodic (periodize b F) b := fun u => by
  simp only [periodize, toIocMod_add_right]

theorem measurable_periodize [MeasurableSpace E] {F : ℝ → E} (hF : Measurable F) :
    Measurable (periodize b F) :=
  hF.comp measurable_toIocMod

theorem periodize_ae_eq {F : ℝ → E} (hper : ∀ᵐ u : ℝ, F (u + b) = F u) :
    periodize b F =ᵐ[volume] F := by
  have hall : ∀ᵐ u : ℝ, ∀ k : ℤ, F (u + k * b) = F u :=
    ae_all_iff.mpr (ae_periodic_intMul' hper)
  filter_upwards [hall] with u hu
  have hm : toIocMod hb.out 0 u = u + ((-toIocDiv hb.out 0 u : ℤ) : ℝ) * b := by
    rw [← self_sub_toIocDiv_zsmul hb.out 0 u, zsmul_eq_mul]; push_cast; ring
  rw [periodize, hm]
  exact hu _

end Periodize

/-! ### Eigenfunctions of an irrational rotation -/

/-- The circle character `e_k(u) = e^{2πiku/b}`. -/
def circleChar (b : ℝ) (k : ℤ) (u : ℝ) : ℂ := Complex.exp (2 * π * I * k * u / b)

theorem circleChar_add (b : ℝ) (k : ℤ) (u v : ℝ) :
    circleChar b k (u + v) = circleChar b k u * circleChar b k v := by
  rw [circleChar, circleChar, circleChar, ← Complex.exp_add]; congr 1; push_cast; ring

theorem circleChar_neg_mul (b : ℝ) (k : ℤ) (u : ℝ) :
    circleChar b (-k) u * circleChar b k u = 1 := by
  rw [circleChar, circleChar, ← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero

theorem circleChar_neg_apply (b : ℝ) (k : ℤ) (u : ℝ) :
    circleChar b (-k) (-u) = circleChar b k u := by
  rw [circleChar, circleChar]; push_cast; ring_nf

theorem circleChar_add_period {b : ℝ} (hb : b ≠ 0) (k : ℤ) (u : ℝ) :
    circleChar b k (u + b) = circleChar b k u := by
  have hper : circleChar b k b = 1 := by
    rw [circleChar, show 2 * π * I * (k : ℂ) * (b : ℂ) / (b : ℂ) = (k : ℂ) * (2 * π * I) by
      have : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hb
      field_simp, Complex.exp_int_mul_two_pi_mul_I]
  rw [circleChar_add, hper, mul_one]

theorem norm_circleChar (b : ℝ) (k : ℤ) (u : ℝ) : ‖circleChar b k u‖ = 1 := by
  rw [circleChar, Complex.norm_exp]
  have : (2 * π * I * (k : ℂ) * (u : ℂ) / (b : ℂ)).re = 0 := by
    rw [show 2 * π * I * (k : ℂ) * (u : ℂ) / (b : ℂ) = ((2 * π * k * u / b : ℝ) : ℂ) * I by
      push_cast; ring]
    simp
  rw [this, Real.exp_zero]

theorem continuous_circleChar (b : ℝ) (k : ℤ) : Continuous (circleChar b k) := by
  unfold circleChar; fun_prop

/-- The `n`-th Fourier integral on `(0, b]`. -/
def coeffOn (b : ℝ) (F : ℝ → ℂ) (n : ℤ) : ℂ := ∫ x in (0 : ℝ)..b, circleChar b (-n) x * F x

section Rotation

variable {b : ℝ} [hb : Fact (0 < b)]


/-- Shifting the function multiplies the Fourier integral by the character value. -/
theorem integral_circleChar_mul_shift {F : ℝ → ℂ} (hF : Function.Periodic F b) (a : ℝ) (n : ℤ) :
    ∫ x in (0 : ℝ)..b, circleChar b (-n) x * F (x + a) = circleChar b n a * coeffOn b F n := by
  have hb0 : b ≠ 0 := hb.out.ne'
  have hrw : ∀ x : ℝ, circleChar b (-n) x * F (x + a) =
      (fun y => circleChar b n a * (circleChar b (-n) y * F y)) (x + a) := by
    intro x
    simp only
    rw [circleChar_add, ← circleChar_neg_apply b n a, show (-a) = (-a : ℝ) from rfl]
    have h := circleChar_neg_mul b (-n) (-a)
    rw [neg_neg] at h
    rw [show circleChar b (-n) (-a) = circleChar b n a from circleChar_neg_apply b n a] at *
    have h2 : circleChar b n a * circleChar b (-n) a = 1 := by
      rw [mul_comm]; exact circleChar_neg_mul b n a
    linear_combination (-(circleChar b (-n) x * F (x + a))) * h2
  simp_rw [hrw]
  rw [intervalIntegral.integral_comp_add_right (fun y => circleChar b n a * (circleChar b (-n) y * F y)) a,
    intervalIntegral.integral_const_mul, zero_add]
  have hper : Function.Periodic (fun y => circleChar b (-n) y * F y) b := fun y => by
    simp only; rw [circleChar_add_period hb0, hF y]
  rw [show b + a = a + b by ring, hper.intervalIntegral_add_eq a 0, zero_add, coeffOn]

theorem fourierCoeffOn_eq_coeffOn (F : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hb.out F n = (1 / b : ℂ) * coeffOn b F n := by
  rw [fourierCoeffOn_eq_integral F n hb.out, coeffOn, sub_zero, Complex.real_smul]
  congr 1
  · push_cast; ring
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [smul_eq_mul]
    congr 1
    rw [fourier_coe_apply, circleChar]

/-- **Eigenfunctions of an irrational rotation are characters.** If `F` is a.e. `b`-periodic and
`F(u + a) = μ F(u)` a.e. with `|μ| = 1` and `a/b` irrational, then `F = 0` a.e., or
`μ = e^{2πika/b}` and `F = c e^{2πiku/b}` a.e. for some `k ∈ ℤ`. -/
theorem eigenfunction_of_irrational_rotation {a : ℝ} (hord : addOrderOf (a : AddCircle b) = 0)
    {F : ℝ → ℂ} (hF : Measurable F) {μ : ℂ} (hμ : ‖μ‖ = 1)
    (hpb : ∀ᵐ u : ℝ, F (u + b) = F u) (hpa : ∀ᵐ u : ℝ, F (u + a) = μ * F u) :
    (∀ᵐ u : ℝ, F u = 0) ∨
      ∃ k : ℤ, ∃ c : ℂ, μ = circleChar b k a ∧ ∀ᵐ u : ℝ, F u = c * circleChar b k u := by
  -- the modulus is constant
  obtain ⟨r, hr⟩ := exists_ae_eq_const_of_two_periods (b := b) (φ := fun u => ‖F u‖)
    hF.norm hord (by filter_upwards [hpb] with u hu; simp only [hu])
    (by filter_upwards [hpa] with u hu; simp only [hu, norm_mul, hμ, one_mul])
  by_cases hr0 : r = 0
  · left
    filter_upwards [hr] with u hu
    simpa [hr0] using hu
  right
  set G := periodize b F with hGdef
  have hGF : G =ᵐ[volume] F := periodize_ae_eq hpb
  have hGper : Function.Periodic G b := periodize_periodic F
  have hGm : Measurable G := measurable_periodize hF
  have hGa : ∀ᵐ u : ℝ, G (u + a) = μ * G u := by
    filter_upwards [hGF, ae_comp_add_right hGF a, hpa] with u h1 h2 h3
    rw [h2, h1, h3]
  have hGr : ∀ᵐ u : ℝ, ‖G u‖ = r := by
    filter_upwards [hGF, hr] with u h1 h2
    rw [h1]; exact h2
  -- every Fourier integral is killed by `μ − e_n(a)`
  have hcoeff : ∀ n : ℤ, μ * coeffOn b G n = circleChar b n a * coeffOn b G n := by
    intro n
    rw [← integral_circleChar_mul_shift hGper a n, coeffOn, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hGa] with x hx _
    rw [hx]; ring
  -- Parseval: some coefficient is nonzero
  have hL2 : MemLp G 2 (volume.restrict (Ioc 0 b)) :=
    MemLp.of_bound hGm.aestronglyMeasurable r (ae_restrict_of_ae (hGr.mono fun u hu => hu.le))
  have hpars := hasSum_sq_fourierCoeffOn hb.out hL2
  have hint : ∫ x in (0 : ℝ)..b, ‖G x‖ ^ 2 = r ^ 2 * b := by
    rw [intervalIntegral.integral_congr_ae (g := fun _ => r ^ 2) ?_]
    · simp [mul_comm]
    · filter_upwards [hGr] with x hx _
      rw [hx]
  rw [hint, sub_zero] at hpars
  obtain ⟨k, hk⟩ : ∃ k : ℤ, coeffOn b G k ≠ 0 := by
    by_contra hall
    push Not at hall
    have h0 : (fun i : ℤ => ‖fourierCoeffOn hb.out G i‖ ^ 2) = fun _ => 0 := by
      funext i; rw [fourierCoeffOn_eq_coeffOn, hall i, mul_zero, norm_zero]; norm_num
    rw [h0] at hpars
    have := hpars.unique hasSum_zero
    have hbne : b ≠ 0 := hb.out.ne'
    have hb0 : b⁻¹ * (r ^ 2 * b) = r ^ 2 := by field_simp
    rw [smul_eq_mul, hb0] at this
    exact hr0 (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  have hμk : μ = circleChar b k a := mul_right_cancel₀ hk (hcoeff k)
  -- the untwisted function has both periods, hence is constant
  set H : ℝ → ℂ := fun u => F u * circleChar b (-k) u with hHdef
  have hHm : Measurable H := hF.mul (continuous_circleChar b (-k)).measurable
  have hHb : ∀ᵐ u : ℝ, H (u + b) = H u := by
    filter_upwards [hpb] with u hu
    simp only [hHdef]; rw [hu, circleChar_add_period hb.out.ne']
  have hHa : ∀ᵐ u : ℝ, H (u + a) = H u := by
    filter_upwards [hpa] with u hu
    simp only [hHdef]
    rw [hu, circleChar_add, hμk]
    have h := circleChar_neg_mul b k a
    rw [mul_comm (circleChar b (-k) a)] at h
    linear_combination (F u * circleChar b (-k) u) * h
  obtain ⟨c₁, hc₁⟩ := exists_ae_eq_const_of_two_periods (b := b) (φ := fun u => (H u).re)
    (Complex.measurable_re.comp hHm) hord (by filter_upwards [hHb] with u hu; simp only [hu])
    (by filter_upwards [hHa] with u hu; simp only [hu])
  obtain ⟨c₂, hc₂⟩ := exists_ae_eq_const_of_two_periods (b := b) (φ := fun u => (H u).im)
    (Complex.measurable_im.comp hHm) hord (by filter_upwards [hHb] with u hu; simp only [hu])
    (by filter_upwards [hHa] with u hu; simp only [hu])
  refine ⟨k, ⟨c₁, c₂⟩, hμk, ?_⟩
  filter_upwards [hc₁, hc₂] with u h1 h2
  have hH : H u = ⟨c₁, c₂⟩ := Complex.ext h1 h2
  have h := circleChar_neg_mul b k u
  calc F u = F u * (circleChar b (-k) u * circleChar b k u) := by rw [h, mul_one]
    _ = H u * circleChar b k u := by simp only [hHdef]; ring
    _ = _ := by rw [hH]

/-! ### Twisted laws -/

theorem norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]

/-- **Transfer of a twisted period.** If `P(u + τ) = θP(u)`, `Q(u + σ) = ηQ(u)` with unimodular
multipliers, and `e^{κu}(P − Q)` has finite energy, then `Q(u + τ) = θQ(u)` a.e. -/
theorem ae_twisted_periodic_of_weighted_difference {κ τ σ : ℝ} (hκ : 0 < κ) (hτ : 0 < τ)
    [Fact (0 < σ)] {P Q : ℝ → ℂ} (hP : Measurable P) (hQ : Measurable Q) {θ η : ℂ}
    (hθ : ‖θ‖ = 1) (hη : ‖η‖ = 1)
    (hPper : ∀ᵐ u : ℝ, P (u + τ) = θ * P u) (hQper : ∀ᵐ u : ℝ, Q (u + σ) = η * Q u)
    (hfin : ∫⁻ u, ENNReal.ofReal (Real.exp (κ * u) ^ 2 * ‖P u - Q u‖ ^ 2) ≠ ⊤) :
    ∀ᵐ u : ℝ, Q (u + τ) = θ * Q u := by
  set W : ℝ → ENNReal := fun u => ENNReal.ofReal (Real.exp (κ * u) ^ 2 * ‖P u - Q u‖ ^ 2)
    with hWdef
  have hWm : Measurable W := ENNReal.measurable_ofReal.comp
    (((Real.measurable_exp.comp (measurable_id.const_mul κ)).pow_const 2).mul
      ((hP.sub hQ).norm.pow_const 2))
  set ψ : ℝ → ℂ := fun u => Q (u + τ) - θ * Q u with hψdef
  have hψm : Measurable fun u => ‖ψ u‖ :=
    ((hQ.comp (measurable_add_const τ)).sub (measurable_const.mul hQ)).norm
  have hψper : ∀ᵐ u : ℝ, ‖ψ (u + σ)‖ = ‖ψ u‖ := by
    filter_upwards [hQper, ae_comp_add_right hQper τ] with u h1 h2
    simp only [hψdef]
    rw [show u + σ + τ = u + τ + σ by ring, h2, h1,
      show η * Q (u + τ) - θ * (η * Q u) = η * (Q (u + τ) - θ * Q u) by ring, norm_mul, hη, one_mul]
  have hpt : ∀ᵐ u : ℝ, u ∈ Ioi (0 : ℝ) →
      ENNReal.ofReal (‖ψ u‖ ^ 2) ≤ 2 * W (u + τ) + 2 * W u := by
    filter_upwards [hPper] with u hu hu0
    have hu0' : (0 : ℝ) ≤ u := le_of_lt hu0
    have hψ : ψ u = (P (u + τ) - Q (u + τ)) * (-1) - θ * (P u - Q u) * (-1) := by
      simp only [hψdef]; rw [hu]; ring
    have he1 : 1 ≤ Real.exp (κ * (u + τ)) ^ 2 :=
      one_le_pow₀ (one_le_exp_mul hκ.le (by linarith))
    have he2 : 1 ≤ Real.exp (κ * u) ^ 2 := one_le_pow₀ (one_le_exp_mul hκ.le hu0')
    have hA : ‖(P (u + τ) - Q (u + τ)) * (-1)‖ ^ 2 ≤
        Real.exp (κ * (u + τ)) ^ 2 * ‖P (u + τ) - Q (u + τ)‖ ^ 2 := by
      rw [norm_mul, norm_neg, norm_one, mul_one]
      nlinarith [sq_nonneg ‖P (u + τ) - Q (u + τ)‖]
    have hB : ‖θ * (P u - Q u) * (-1)‖ ^ 2 ≤ Real.exp (κ * u) ^ 2 * ‖P u - Q u‖ ^ 2 := by
      rw [norm_mul, norm_mul, norm_neg, norm_one, mul_one, hθ, one_mul]
      nlinarith [sq_nonneg ‖P u - Q u‖]
    rw [hψ]
    calc ENNReal.ofReal (‖(P (u + τ) - Q (u + τ)) * (-1) - θ * (P u - Q u) * (-1)‖ ^ 2)
        ≤ ENNReal.ofReal (2 * ‖(P (u + τ) - Q (u + τ)) * (-1)‖ ^ 2 +
            2 * ‖θ * (P u - Q u) * (-1)‖ ^ 2) := ENNReal.ofReal_le_ofReal (norm_sub_sq_le _ _)
      _ ≤ ENNReal.ofReal (2 * (Real.exp (κ * (u + τ)) ^ 2 * ‖P (u + τ) - Q (u + τ)‖ ^ 2) +
            2 * (Real.exp (κ * u) ^ 2 * ‖P u - Q u‖ ^ 2)) := by
          refine ENNReal.ofReal_le_ofReal ?_; linarith
      _ = 2 * W (u + τ) + 2 * W u := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_mul (p := 2) (by norm_num),
            ENNReal.ofReal_ofNat]
  have hψfin : ∫⁻ u in Ioi 0, ENNReal.ofReal (‖ψ u‖ ^ 2) ≠ ⊤ := by
    have h1 : ∫⁻ u in Ioi 0, ENNReal.ofReal (‖ψ u‖ ^ 2) ≤
        ∫⁻ u in Ioi 0, (2 * W (u + τ) + 2 * W u) :=
      lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr hpt)
    have h2 : ∫⁻ u in Ioi 0, (2 * W (u + τ) + 2 * W u) ≤ ∫⁻ u, (2 * W (u + τ) + 2 * W u) :=
      setLIntegral_le_lintegral _ _
    have hWτ : Measurable fun u => W (u + τ) := hWm.comp (measurable_add_const τ)
    have hWτ2 : Measurable fun u => 2 * W (u + τ) := hWτ.const_mul 2
    have h3 : ∫⁻ u, (2 * W (u + τ) + 2 * W u) = (2 * ∫⁻ u, W u) + 2 * ∫⁻ u, W u := by
      rw [lintegral_add_left hWτ2, lintegral_const_mul _ hWτ, lintegral_const_mul _ hWm]
      rw [lintegral_add_right_eq_self (μ := volume) W τ]
    have hfin' : ∫⁻ u, W u ≠ ⊤ := hfin
    refine ne_top_of_le_ne_top ?_ (h1.trans (h2.trans h3.le))
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hfin',
      ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hfin'⟩
  filter_upwards [ae_eq_zero_of_periodic hψm hψper hψfin] with u hu
  have : ψ u = 0 := norm_eq_zero.mp hu
  simp only [hψdef] at this
  linear_combination this

/-- The twisted law defect `g − e^{(κ+iγ)τ} g(· − τ)`. -/
def twistedDefect (κ γ τ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  g u - Complex.exp ((κ + γ * I) * τ) * g (u - τ)

/-- Real part of the rotation `e^{-iγu} g`. -/
def rotRe (γ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℝ := (Complex.exp (-(γ * u * I)) * g u).re

/-- Imaginary part of the rotation `e^{-iγu} g`. -/
def rotIm (γ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℝ := (Complex.exp (-(γ * u * I)) * g u).im

theorem rot_mul_twistedDefect (κ γ τ : ℝ) (g : ℝ → ℂ) (u : ℝ) :
    Complex.exp (-(γ * u * I)) * twistedDefect κ γ τ g u =
      Complex.exp (-(γ * u * I)) * g u -
        (Real.exp (κ * τ) : ℂ) * (Complex.exp (-(γ * ((u - τ : ℝ) : ℂ) * I)) * g (u - τ)) := by
  rw [twistedDefect, mul_sub, Complex.ofReal_exp, ← mul_assoc, ← mul_assoc, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 3
  push_cast; ring

theorem lawDefect_rotRe (κ γ τ : ℝ) (g : ℝ → ℂ) (u : ℝ) :
    lawDefect κ τ (rotRe γ g) u = (Complex.exp (-(γ * u * I)) * twistedDefect κ γ τ g u).re := by
  rw [rot_mul_twistedDefect, Complex.sub_re, Complex.re_ofReal_mul, lawDefect, rotRe, rotRe]

theorem lawDefect_rotIm (κ γ τ : ℝ) (g : ℝ → ℂ) (u : ℝ) :
    lawDefect κ τ (rotIm γ g) u = (Complex.exp (-(γ * u * I)) * twistedDefect κ γ τ g u).im := by
  rw [rot_mul_twistedDefect, Complex.sub_im, Complex.im_ofReal_mul, lawDefect, rotIm, rotIm]

theorem norm_exp_neg_mul_I (γ u : ℝ) : ‖Complex.exp (-(γ * u * I))‖ = 1 := by
  rw [Complex.norm_exp]
  have : (-((γ : ℂ) * (u : ℂ) * I)).re = 0 := by simp
  rw [this, Real.exp_zero]

theorem lintegral_sq_rot_lawDefect_le (κ γ τ : ℝ) (g : ℝ → ℂ) :
    ∫⁻ u, ENNReal.ofReal (lawDefect κ τ (rotRe γ g) u ^ 2) ≤
        ∫⁻ u, ENNReal.ofReal (‖twistedDefect κ γ τ g u‖ ^ 2) ∧
      ∫⁻ u, ENNReal.ofReal (lawDefect κ τ (rotIm γ g) u ^ 2) ≤
        ∫⁻ u, ENNReal.ofReal (‖twistedDefect κ γ τ g u‖ ^ 2) := by
  have hbound : ∀ u : ℝ, ‖Complex.exp (-(γ * u * I)) * twistedDefect κ γ τ g u‖ =
      ‖twistedDefect κ γ τ g u‖ := fun u => by rw [norm_mul, norm_exp_neg_mul_I, one_mul]
  constructor
  · refine lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_
    rw [lawDefect_rotRe, ← hbound u, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  · refine lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_
    rw [lawDefect_rotIm, ← hbound u, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2

/-- The twisted ghost `Π = π(Re) + iπ(Im)` of the rotated profile. -/
def twistedGhost (κ γ τ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  (logGhost κ τ (rotRe γ g) u : ℂ) + (logGhost κ τ (rotIm γ g) u : ℂ) * I

/-- The twisted anti-causal tail. -/
def twistedTail (κ γ τ : ℝ) (g : ℝ → ℂ) (u : ℝ) : ℂ :=
  (antiCausalSum κ τ (lawDefect κ τ (rotRe γ g)) u : ℂ) +
    (antiCausalSum κ τ (lawDefect κ τ (rotIm γ g)) u : ℂ) * I

/-- **The twisted decomposition** `g = e^{(κ+iγ)u} Π − e^{iγu} S`, identically. -/
theorem eq_twisted_decomposition (κ γ τ : ℝ) (g : ℝ → ℂ) (u : ℝ) :
    g u = Complex.exp ((κ + γ * I) * u) * twistedGhost κ γ τ g u -
      Complex.exp (γ * u * I) * twistedTail κ γ τ g u := by
  have hre := eq_exp_mul_logGhost_sub κ τ (rotRe γ g) u
  have him := eq_exp_mul_logGhost_sub κ τ (rotIm γ g) u
  have hxy : Complex.exp (-(γ * u * I)) * g u =
      (Real.exp (κ * u) : ℂ) * twistedGhost κ γ τ g u - twistedTail κ γ τ g u := by
    apply Complex.ext
    · simp only [twistedGhost, twistedTail, Complex.sub_re, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        zero_mul, sub_zero, add_zero]
      change rotRe γ g u = _
      rw [hre]
    · simp only [twistedGhost, twistedTail, Complex.sub_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
        zero_mul, zero_add, add_zero]
      change rotIm γ g u = _
      rw [him]
  have hexp : Complex.exp (γ * u * I) * Complex.exp (-(γ * u * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc g u = Complex.exp (γ * u * I) * (Complex.exp (-(γ * u * I)) * g u) := by
        rw [← mul_assoc, hexp, one_mul]
    _ = _ := by
        rw [hxy, mul_sub, ← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
        congr 3
        push_cast; ring

theorem measurable_rotRe (γ : ℝ) {g : ℝ → ℂ} (hg : Measurable g) : Measurable (rotRe γ g) :=
  Complex.measurable_re.comp ((Complex.measurable_exp.comp
    (((Complex.measurable_ofReal.comp measurable_id).const_mul (γ : ℂ)).mul_const I).neg).mul hg)

theorem measurable_rotIm (γ : ℝ) {g : ℝ → ℂ} (hg : Measurable g) : Measurable (rotIm γ g) :=
  Complex.measurable_im.comp ((Complex.measurable_exp.comp
    (((Complex.measurable_ofReal.comp measurable_id).const_mul (γ : ℂ)).mul_const I).neg).mul hg)

theorem measurable_twistedGhost (κ γ τ : ℝ) {g : ℝ → ℂ} (hg : Measurable g) :
    Measurable (twistedGhost κ γ τ g) :=
  (Complex.measurable_ofReal.comp (measurable_logGhost κ τ (measurable_rotRe γ hg))).add
    ((Complex.measurable_ofReal.comp (measurable_logGhost κ τ (measurable_rotIm γ hg))).mul_const I)

theorem measurable_lawDefect (κ τ : ℝ) {g : ℝ → ℝ} (hg : Measurable g) :
    Measurable (lawDefect κ τ g) :=
  hg.sub (measurable_const.mul (hg.comp (measurable_sub_const τ)))

theorem ae_periodic_twistedGhost {κ γ τ : ℝ} (hκτ : 0 < κ * τ) {g : ℝ → ℂ} (hg : Measurable g)
    (hfin : ∫⁻ u, ENNReal.ofReal (‖twistedDefect κ γ τ g u‖ ^ 2) ≠ ⊤) :
    ∀ᵐ u : ℝ, twistedGhost κ γ τ g (u + τ) = twistedGhost κ γ τ g u := by
  obtain ⟨h1, h2⟩ := lintegral_sq_rot_lawDefect_le κ γ τ g
  filter_upwards [ae_periodic_logGhost hκτ (measurable_lawDefect κ τ (measurable_rotRe γ hg))
      (ne_top_of_le_ne_top hfin h1),
    ae_periodic_logGhost hκτ (measurable_lawDefect κ τ (measurable_rotIm γ hg))
      (ne_top_of_le_ne_top hfin h2)] with u hu1 hu2
  simp only [twistedGhost, hu1, hu2]

theorem lintegral_sq_twistedTail_ne_top {κ γ τ : ℝ} (hκτ : 0 < κ * τ) {g : ℝ → ℂ}
    (hg : Measurable g) (hfin : ∫⁻ u, ENNReal.ofReal (‖twistedDefect κ γ τ g u‖ ^ 2) ≠ ⊤) :
    ∫⁻ u, ENNReal.ofReal (‖twistedTail κ γ τ g u‖ ^ 2) ≠ ⊤ := by
  obtain ⟨h1, h2⟩ := lintegral_sq_rot_lawDefect_le κ γ τ g
  have hA := lintegral_sq_antiCausalSum_ne_top hκτ
    (measurable_lawDefect κ τ (measurable_rotRe γ hg)) (ne_top_of_le_ne_top hfin h1)
  have hB := lintegral_sq_antiCausalSum_ne_top hκτ
    (measurable_lawDefect κ τ (measurable_rotIm γ hg)) (ne_top_of_le_ne_top hfin h2)
  have hmA : Measurable fun u =>
      ENNReal.ofReal (antiCausalSum κ τ (lawDefect κ τ (rotRe γ g)) u ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_antiCausalSum κ τ
      (measurable_lawDefect κ τ (measurable_rotRe γ hg))).pow_const 2)
  have hsplit : (fun u => ENNReal.ofReal (‖twistedTail κ γ τ g u‖ ^ 2)) =
      fun u => ENNReal.ofReal (antiCausalSum κ τ (lawDefect κ τ (rotRe γ g)) u ^ 2) +
        ENNReal.ofReal (antiCausalSum κ τ (lawDefect κ τ (rotIm γ g)) u ^ 2) := by
    funext u
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _), Complex.sq_norm, Complex.normSq_apply]
    simp only [twistedTail, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring_nf
  rw [hsplit, lintegral_add_left hmA]
  exact ENNReal.add_ne_top.mpr ⟨hA, hB⟩

theorem norm_cexp_mul_I (γ u : ℝ) : ‖Complex.exp (γ * u * I)‖ = 1 := by
  rw [Complex.norm_exp]
  have : ((γ : ℂ) * (u : ℂ) * I).re = 0 := by simp
  rw [this, Real.exp_zero]

/-- **Two twisted laws with incommensurable periods tie the exponent.** If
`g − e^{(κ+iγ₂)τ₂}g(· − τ₂)` and `g − e^{(κ+iγ₃)τ₃}g(· − τ₃)` have finite energy, `κ > 0`,
`τ₂/τ₃ ∉ ℚ`, then `g − c e^{zu}` has finite energy, where `Re z = κ` and, unless `c = 0`, `z` is
tied: `e^{zτ₂} = e^{(κ+iγ₂)τ₂}` and `e^{zτ₃} = e^{(κ+iγ₃)τ₃}`. -/
theorem exists_lintegral_sub_const_mul_cexp_ne_top {κ : ℝ} (hκ : 0 < κ) {τ₂ τ₃ : ℝ}
    (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (h23 : addOrderOf (τ₂ : AddCircle τ₃) = 0) {γ₂ γ₃ : ℝ}
    {g : ℝ → ℂ} (hg : Measurable g)
    (h2 : ∫⁻ u, ENNReal.ofReal (‖twistedDefect κ γ₂ τ₂ g u‖ ^ 2) ≠ ⊤)
    (h3 : ∫⁻ u, ENNReal.ofReal (‖twistedDefect κ γ₃ τ₃ g u‖ ^ 2) ≠ ⊤) :
    ∃ c z : ℂ, z.re = κ ∧
      (c ≠ 0 → Complex.exp (z * τ₂) = Complex.exp ((κ + γ₂ * I) * τ₂) ∧
        Complex.exp (z * τ₃) = Complex.exp ((κ + γ₃ * I) * τ₃)) ∧
      ∫⁻ u, ENNReal.ofReal (‖g u - c * Complex.exp (z * u)‖ ^ 2) ≠ ⊤ := by
  haveI : Fact (0 < τ₃) := ⟨hτ₃⟩
  have hT₂ := lintegral_sq_twistedTail_ne_top (mul_pos hκ hτ₂) hg h2
  have hT₃ := lintegral_sq_twistedTail_ne_top (mul_pos hκ hτ₃) hg h3
  have hp₂ := ae_periodic_twistedGhost (mul_pos hκ hτ₂) hg h2
  have hp₃ := ae_periodic_twistedGhost (mul_pos hκ hτ₃) hg h3
  have hm₂ : Measurable (twistedGhost κ γ₂ τ₂ g) := measurable_twistedGhost κ γ₂ τ₂ hg
  have hm₃ : Measurable (twistedGhost κ γ₃ τ₃ g) := measurable_twistedGhost κ γ₃ τ₃ hg
  set P : ℝ → ℂ := fun u => Complex.exp (γ₂ * u * I) * (twistedGhost κ γ₂ τ₂ g) u with hPdef
  set Q : ℝ → ℂ := fun u => Complex.exp (γ₃ * u * I) * (twistedGhost κ γ₃ τ₃ g) u with hQdef
  have hcexp : ∀ (γ u v : ℝ), Complex.exp (γ * ((u + v : ℝ) : ℂ) * I) =
      Complex.exp (γ * v * I) * Complex.exp (γ * u * I) := fun γ u v => by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have hPper : ∀ᵐ u : ℝ, P (u + τ₂) = Complex.exp (γ₂ * τ₂ * I) * P u := by
    filter_upwards [hp₂] with u hu
    simp only [hPdef]; rw [hcexp, hu]; ring
  have hQper : ∀ᵐ u : ℝ, Q (u + τ₃) = Complex.exp (γ₃ * τ₃ * I) * Q u := by
    filter_upwards [hp₃] with u hu
    simp only [hQdef]; rw [hcexp, hu]; ring
  have hsplit : ∀ (γ u : ℝ), Complex.exp ((κ + γ * I) * u) =
      (Real.exp (κ * u) : ℂ) * Complex.exp (γ * u * I) := fun γ u => by
    rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
  have hdiff : ∀ u, (Real.exp (κ * u) : ℂ) * (P u - Q u) =
      Complex.exp (γ₂ * u * I) * (twistedTail κ γ₂ τ₂ g) u - Complex.exp (γ₃ * u * I) * (twistedTail κ γ₃ τ₃ g) u := by
    intro u
    have e2 := eq_twisted_decomposition κ γ₂ τ₂ g u
    have e3 := eq_twisted_decomposition κ γ₃ τ₃ g u
    rw [hsplit] at e2 e3
    simp only [hPdef, hQdef]
    linear_combination e3 - e2
  have hW : ∫⁻ u, ENNReal.ofReal (Real.exp (κ * u) ^ 2 * ‖P u - Q u‖ ^ 2) ≠ ⊤ := by
    have hpt : ∀ u, ENNReal.ofReal (Real.exp (κ * u) ^ 2 * ‖P u - Q u‖ ^ 2) ≤
        2 * ENNReal.ofReal (‖(twistedTail κ γ₂ τ₂ g) u‖ ^ 2) + 2 * ENNReal.ofReal (‖(twistedTail κ γ₃ τ₃ g) u‖ ^ 2) := by
      intro u
      have hn : Real.exp (κ * u) ^ 2 * ‖P u - Q u‖ ^ 2 =
          ‖Complex.exp (γ₂ * u * I) * (twistedTail κ γ₂ τ₂ g) u - Complex.exp (γ₃ * u * I) * (twistedTail κ γ₃ τ₃ g) u‖ ^ 2 := by
        rw [← hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), mul_pow]
      rw [hn]
      calc ENNReal.ofReal (‖Complex.exp (γ₂ * u * I) * (twistedTail κ γ₂ τ₂ g) u - Complex.exp (γ₃ * u * I) * (twistedTail κ γ₃ τ₃ g) u‖ ^ 2)
          ≤ ENNReal.ofReal (2 * ‖(twistedTail κ γ₂ τ₂ g) u‖ ^ 2 + 2 * ‖(twistedTail κ γ₃ τ₃ g) u‖ ^ 2) := by
            refine ENNReal.ofReal_le_ofReal ?_
            have := norm_sub_sq_le (Complex.exp (γ₂ * u * I) * (twistedTail κ γ₂ τ₂ g) u) (Complex.exp (γ₃ * u * I) * (twistedTail κ γ₃ τ₃ g) u)
            rwa [norm_mul, norm_mul, norm_cexp_mul_I, norm_cexp_mul_I, one_mul, one_mul] at this
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (p := 2) (by norm_num), ENNReal.ofReal_mul (p := 2) (by norm_num),
              ENNReal.ofReal_ofNat]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono hpt)
    have hmT : Measurable fun u => 2 * ENNReal.ofReal (‖(twistedTail κ γ₂ τ₂ g) u‖ ^ 2) := by
      have hm : Measurable (twistedTail κ γ₂ τ₂ g) :=
        (Complex.measurable_ofReal.comp (measurable_antiCausalSum κ τ₂
          (measurable_lawDefect κ τ₂ (measurable_rotRe γ₂ hg)))).add
          ((Complex.measurable_ofReal.comp (measurable_antiCausalSum κ τ₂
            (measurable_lawDefect κ τ₂ (measurable_rotIm γ₂ hg)))).mul_const I)
      exact (ENNReal.measurable_ofReal.comp (hm.norm.pow_const 2)).const_mul 2
    rw [lintegral_add_left hmT, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hT₂,
      ENNReal.mul_ne_top (by norm_num : (2 : ENNReal) ≠ ⊤) hT₃⟩
  have hmP : Measurable P :=
    (Complex.measurable_exp.comp (((Complex.measurable_ofReal.comp measurable_id).const_mul
      (γ₂ : ℂ)).mul_const I)).mul hm₂
  have hmQ : Measurable Q :=
    (Complex.measurable_exp.comp (((Complex.measurable_ofReal.comp measurable_id).const_mul
      (γ₃ : ℂ)).mul_const I)).mul hm₃
  -- the `τ₃`-ghost inherits the twisted period `τ₂`
  have hQ₂ := ae_twisted_periodic_of_weighted_difference (σ := τ₃) hκ hτ₂ hmP hmQ
    (norm_cexp_mul_I γ₂ τ₂) (norm_cexp_mul_I γ₃ τ₃) hPper hQper hW
  set μ : ℂ := Complex.exp (((γ₂ - γ₃ : ℝ) : ℂ) * τ₂ * I) with hμdef
  have hμ : ‖μ‖ = 1 := norm_cexp_mul_I (γ₂ - γ₃) τ₂
  have hμmul : μ * Complex.exp (γ₃ * τ₂ * I) = Complex.exp (γ₂ * τ₂ * I) := by
    rw [hμdef, ← Complex.exp_add]; congr 1; push_cast; ring
  have heig : ∀ᵐ u : ℝ, twistedGhost κ γ₃ τ₃ g (u + τ₂) = μ * twistedGhost κ γ₃ τ₃ g u := by
    filter_upwards [hQ₂] with u hu
    simp only [hQdef] at hu
    rw [hcexp] at hu
    have hne : Complex.exp (γ₃ * τ₂ * I) * Complex.exp (γ₃ * u * I) ≠ 0 :=
      mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)
    apply mul_left_cancel₀ hne
    linear_combination hu - (Complex.exp (γ₃ * u * I) * twistedGhost κ γ₃ τ₃ g u) * hμmul
  rcases eigenfunction_of_irrational_rotation (b := τ₃) h23 hm₃ hμ hp₃ heig with h0 | ⟨k, c, hk, hc⟩
  · refine ⟨0, κ, by simp, fun h => absurd rfl h, ?_⟩
    have hcongr : (fun u => ENNReal.ofReal (‖g u - 0 * Complex.exp ((κ : ℂ) * u)‖ ^ 2)) =ᵐ[volume]
        fun u => ENNReal.ofReal (‖twistedTail κ γ₃ τ₃ g u‖ ^ 2) := by
      filter_upwards [h0] with u hu
      rw [zero_mul, sub_zero, eq_twisted_decomposition κ γ₃ τ₃ g u, hu, mul_zero, zero_sub, norm_neg,
        norm_mul, norm_cexp_mul_I, one_mul]
    rw [lintegral_congr_ae hcongr]
    exact hT₃
  · have hτ₃0 : (τ₃ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hτ₃.ne'
    refine ⟨c, κ + (γ₃ + 2 * π * k / τ₃) * I, ?_, fun _ => ⟨?_, ?_⟩, ?_⟩
    · simp
    · have h1 : ((κ : ℂ) + (γ₃ + 2 * π * k / τ₃) * I) * τ₂ =
          (κ + γ₃ * I) * τ₂ + 2 * π * I * k * τ₂ / τ₃ := by ring
      rw [h1, Complex.exp_add, show Complex.exp (2 * π * I * k * τ₂ / τ₃) = circleChar τ₃ k τ₂ from
        rfl, ← hk, hμdef, ← Complex.exp_add]
      congr 1; push_cast; ring
    · have h1 : ((κ : ℂ) + (γ₃ + 2 * π * k / τ₃) * I) * τ₃ = (κ + γ₃ * I) * τ₃ + k * (2 * π * I) := by
        field_simp
        ring
      rw [h1, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    · have hchar : ∀ u : ℝ, Complex.exp ((κ + γ₃ * I) * u) * circleChar τ₃ k u =
          Complex.exp ((κ + (γ₃ + 2 * π * k / τ₃) * I) * u) := fun u => by
        rw [circleChar, ← Complex.exp_add]; congr 1; ring
      have hcongr : (fun u => ENNReal.ofReal (‖g u - c *
          Complex.exp ((κ + (γ₃ + 2 * π * k / τ₃) * I) * u)‖ ^ 2)) =ᵐ[volume]
          fun u => ENNReal.ofReal (‖twistedTail κ γ₃ τ₃ g u‖ ^ 2) := by
        filter_upwards [hc] with u hu
        rw [eq_twisted_decomposition κ γ₃ τ₃ g u, hu, ← hchar u]
        rw [show Complex.exp ((κ + γ₃ * I) * u) * (c * circleChar τ₃ k u) -
            Complex.exp (γ₃ * u * I) * twistedTail κ γ₃ τ₃ g u -
            c * (Complex.exp ((κ + γ₃ * I) * u) * circleChar τ₃ k u) =
            -(Complex.exp (γ₃ * u * I) * twistedTail κ γ₃ τ₃ g u) by ring,
          norm_neg, norm_mul, norm_cexp_mul_I, one_mul]
      rw [lintegral_congr_ae hcongr]
      exact hT₃

end Rotation

end GaloisForLFunctions.ArithmeticDefectRigidity
