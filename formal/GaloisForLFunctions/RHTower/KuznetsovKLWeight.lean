import GaloisForLFunctions.RHTower.KuznetsovUniformBounds

/-!
# The Kontorovich–Lebedev weight on the line `σ = 2`

For a test function `f` (smooth, compact support in `(0, ∞)`) put
`H(t) = (4/π²) t sinh(2πt) g(2t)`, `g` the Kontorovich–Lebedev transform of `f`.  Then

* `∫ H(t) K_{2it}(x) dt = x f(x)` for `x > 0` (`integral_klWeight_mul_besselK`, the inversion formula
  after `y = 2t`);
* `Γ(2+it)Γ(2−it) = (1+t²)πt / sinh(πt)` (`Gamma_two_add_mul_Gamma_two_sub`), so that
  `|H(t) Γ(2+it)Γ(2−it)| ≤ D (1+t²)⁻¹` (`exists_bound_klWeight_mul_Gamma`);
* `|H(t) K_{2it}(x)| ≤ D (|log x| + 1)(1+t²)⁻¹` (`exists_bound_klWeight_mul_besselK`);
* `|K_ν(x)| ≤ (1 + 1/x) e^{−x}` for `|Re ν| ≤ 1` (`norm_modifiedBesselKOrder_le_of_abs_re_le_one`).
-/

open UpperHalfPlane ModularGroup MeasureTheory Set Filter Topology Complex
open scoped MatrixGroups ComplexConjugate InnerProductSpace

namespace GaloisForLFunctions.RHTower.DeckPointPair

open MaassFiniteDeckDirichlet MaassCongruenceL2 SelbergMaassCongruenceTrace
  GaloisForLFunctions.HTGeometry MaassWhittaker KontorovichLebedev

noncomputable section

/-! ## `K_ν(x)` for `|Re ν| ≤ 1` -/

theorem integral_exp_neg_mul_cosh_mul_cosh_le {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.cosh u ≤ (1 + 1 / x) * Real.exp (-x) := by
  have hint₁ : IntegrableOn (fun u => Real.exp (-(x * Real.cosh u)) * Real.cosh u) (Ioi 0) := by
    refine ((integrable_exp_neg_mul_cosh (half_pos hx)).const_mul (2 / x)).integrableOn.mono'
      (by fun_prop) (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact cosh_mul_exp_neg_le hx u
  have hsinh : ∀ u, Real.exp (-(x * Real.cosh u)) * Real.cosh u =
      Real.exp (-(x * Real.cosh u)) * Real.sinh u + Real.exp (-(x * Real.cosh u)) * Real.exp (-u) :=
    fun u => by rw [← mul_add, Real.cosh_eq, Real.sinh_eq]; ring
  have hint₂ : IntegrableOn (fun u => Real.exp (-(x * Real.cosh u)) * Real.exp (-u)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).mono' (by fun_prop) (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact mul_le_of_le_one_left (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by
        nlinarith [Real.cosh_pos u])))
  have hint₃ : IntegrableOn (fun u => Real.exp (-(x * Real.cosh u)) * Real.sinh u) (Ioi 0) := by
    refine hint₁.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.sinh_nonneg_iff.2 (le_of_lt hu)))]
    exact mul_le_mul_of_nonneg_left (Real.sinh_lt_cosh u).le (Real.exp_pos _).le
  have hI₁ : ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.sinh u =
      Real.exp (-x) / x := by
    have hF : ∀ u ∈ Ioi (0 : ℝ), HasDerivAt (fun u => -(Real.exp (-(x * Real.cosh u)) / x))
        (Real.exp (-(x * Real.cosh u)) * Real.sinh u) u := fun u _ => by
      have h := (((Real.hasDerivAt_cosh u).const_mul x).neg.exp).div_const x |>.neg
      exact h.congr_deriv (by simp only [Pi.neg_apply]; field_simp)
    have hlim : Tendsto (fun u => -(Real.exp (-(x * Real.cosh u)) / x)) atTop (𝓝 0) := by
      have hc : Tendsto Real.cosh atTop atTop := tendsto_atTop_mono (fun u => by
        have h1 := one_add_sq_div_four_le_cosh u
        have h2 : 0 ≤ (u - 2) ^ 2 := sq_nonneg _
        have h3 : (u - 2) ^ 2 = u ^ 2 - 4 * u + 4 := by ring
        show u ≤ Real.cosh u
        linarith) tendsto_id
      have h1 : Tendsto (fun u => x * Real.cosh u) atTop atTop := hc.const_mul_atTop hx
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).div_const x
      simpa using h2.neg
    rw [integral_Ioi_of_hasDerivAt_of_tendsto (by fun_prop) hF hint₃ hlim]
    simp
  have hI₂ : ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.exp (-u) ≤ Real.exp (-x) := by
    calc ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.exp (-u)
        ≤ ∫ u in Ioi (0 : ℝ), Real.exp (-x) * Real.exp (-u) := by
          refine setIntegral_mono_on hint₂ ((integrableOn_exp_neg_Ioi 0).const_mul _)
            measurableSet_Ioi fun u _ => ?_
          refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le
          nlinarith [Real.one_le_cosh u]
      _ = Real.exp (-x) := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsinh u), integral_add hint₃ hint₂, hI₁]
  calc Real.exp (-x) / x + ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.exp (-u)
      ≤ Real.exp (-x) / x + Real.exp (-x) := by linarith
    _ = (1 + 1 / x) * Real.exp (-x) := by ring

/-- **`‖K_ν(x)‖ ≤ (1 + 1/x) e^{−x}`** for `|Re ν| ≤ 1`. -/
theorem norm_modifiedBesselKOrder_le_of_abs_re_le_one {x : ℝ} (hx : 0 < x) {ν : ℂ}
    (hν : |ν.re| ≤ 1) : ‖modifiedBesselKOrder x ν‖ ≤ (1 + 1 / x) * Real.exp (-x) := by
  refine (norm_integral_le_integral_norm _).trans ((setIntegral_mono_on
    (integrableOn_besselOrderKernel hx ν).norm ?_ measurableSet_Ioi fun u hu => ?_).trans
    (integral_exp_neg_mul_cosh_mul_cosh_le hx))
  · refine ((integrable_exp_neg_mul_cosh (half_pos hx)).const_mul (2 / x)).integrableOn.mono'
      (by fun_prop) (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_comm]
    exact cosh_mul_exp_neg_le hx u
  · unfold besselOrderKernel
    rw [norm_mul, show -(x : ℂ) * Complex.cosh (u : ℂ) = ((-(x * Real.cosh u) : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_exp_ofReal]
    refine mul_le_mul_of_nonneg_left ((norm_cosh_le _).trans ?_) (Real.exp_pos _).le
    rw [Real.cosh_le_cosh, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hν

/-! ## The Gamma factor on the line `σ = 2` -/

/-- **`Γ(2+it)Γ(2−it) = (1+t²) πt / sinh(πt)`.** -/
theorem Gamma_two_add_mul_Gamma_two_sub {t : ℝ} (ht : t ≠ 0) :
    Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I) =
      (((1 + t ^ 2) * Real.pi * t / Real.sinh (Real.pi * t) : ℝ) : ℂ) := by
  set z : ℂ := t * Complex.I
  have hz : z ≠ 0 := mul_ne_zero (by exact_mod_cast ht) Complex.I_ne_zero
  have hz1 : 1 + z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [z] at this
  have hz2 : 1 - z ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp [z] at this
  have hsh : Real.sinh (Real.pi * t) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  have h1 : Complex.Gamma (2 + z) = (1 + z) * (z * Complex.Gamma z) := by
    rw [show (2 : ℂ) + z = (1 + z) + 1 by ring, Complex.Gamma_add_one _ hz1, add_comm 1 z,
      Complex.Gamma_add_one _ hz]
  have h2 : Complex.Gamma (2 - z) = (1 - z) * Complex.Gamma (1 - z) := by
    rw [show (2 : ℂ) - z = (1 - z) + 1 by ring, Complex.Gamma_add_one _ hz2]
  have hrefl := Complex.Gamma_mul_Gamma_one_sub z
  have hsin : Complex.sin (Real.pi * z) = Real.sinh (Real.pi * t) * Complex.I := by
    rw [show (Real.pi : ℂ) * z = ((Real.pi * t : ℝ) : ℂ) * Complex.I by simp [z]; ring,
      Complex.sin_mul_I, ← Complex.ofReal_sinh]
  rw [hsin] at hrefl
  rw [h1, h2]
  calc (1 + z) * (z * Complex.Gamma z) * ((1 - z) * Complex.Gamma (1 - z))
      = (1 + z) * (1 - z) * z * (Complex.Gamma z * Complex.Gamma (1 - z)) := by ring
    _ = _ := by
        rw [hrefl]
        have hshC : (Real.sinh (Real.pi * t) : ℂ) ≠ 0 := by exact_mod_cast hsh
        rw [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_add,
          Complex.ofReal_one, Complex.ofReal_pow]
        simp only [z]
        field_simp
        ring_nf
        rw [Complex.I_sq]
        ring

/-! ## The weight -/

variable {f : ℝ → ℂ}

/-- The Kontorovich–Lebedev weight `H(t) = (4/π²) t sinh(2πt) g(2t)`. -/
def klWeight (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ((4 / Real.pi ^ 2 * t * Real.sinh (2 * Real.pi * t) : ℝ) : ℂ) * klTransform f (2 * t)

/-- **Inversion in the variable `t`**: `∫ H(t) K_{2it}(x) dt = x f(x)`. -/
theorem integral_klWeight_mul_besselK (hf : IsKLTest f) {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ, klWeight f t * modifiedBesselKOrder x (2 * t * Complex.I) = x * f x := by
  have hKL := kontorovichLebedev_inversion hf hx
  set G : ℝ → ℂ := fun y => (y : ℂ) * Real.sinh (Real.pi * y) * kIm x y * klTransform f y
  have hsub := Measure.integral_comp_mul_left G 2
  rw [hKL, abs_of_pos (by norm_num : (0 : ℝ) < 2⁻¹), Complex.real_smul] at hsub
  have hpt : ∀ t : ℝ, klWeight f t * modifiedBesselKOrder x (2 * t * Complex.I) =
      (2 / Real.pi ^ 2 : ℂ) * G (2 * t) := fun t => by
    simp only [klWeight, G, kIm]
    rw [show Real.pi * (2 * t) = 2 * Real.pi * t by ring]
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, hsub]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp
  push_cast
  ring

theorem one_add_pow_le_two_pow_mul {a : ℝ} (ha : 0 ≤ a) {k n : ℕ} (hkn : k ≤ n) :
    (1 + a) ^ k ≤ 2 ^ k * (1 + a ^ n) := by
  rcases le_or_gt a 1 with h | h
  · calc (1 + a) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ ≤ 2 ^ k * (1 + a ^ n) := le_mul_of_one_le_right (by positivity)
          (by have := pow_nonneg ha n; linarith)
  · calc (1 + a) ^ k ≤ (2 * a) ^ k := pow_le_pow_left₀ (by linarith) (by linarith) k
      _ = 2 ^ k * a ^ k := mul_pow 2 a k
      _ ≤ 2 ^ k * (1 + a ^ n) := by
          gcongr
          have := pow_le_pow_right₀ h.le hkn
          linarith

theorem cosh_le_exp_abs' (x : ℝ) : Real.cosh x ≤ Real.exp |x| := by
  rw [← Real.cosh_abs, Real.cosh_eq]
  have := Real.exp_le_exp.2 (show -|x| ≤ |x| by linarith [abs_nonneg x])
  linarith

theorem pow_ten_le (t : ℝ) : |t| ^ 10 ≤ (2 * t) ^ 10 := by
  rw [mul_pow, show (t ^ 10 : ℝ) = |t| ^ 10 by rw [show (10 : ℕ) = 2 * 5 from rfl, pow_mul,
    pow_mul, sq_abs]]
  have := pow_nonneg (abs_nonneg t) 10
  nlinarith

/-- **`|H(t) Γ(2+it)Γ(2−it)| ≤ D(1+t²)⁻¹`.** -/
theorem exists_bound_klWeight_mul_Gamma (hf : IsKLTest f) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ t : ℝ, ‖klWeight f t‖ *
      ‖Complex.Gamma (2 + t * Complex.I) * Complex.Gamma (2 - t * Complex.I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_bound_klTransform hf 5
  have hπ := Real.pi_pos
  refine ⟨16 / Real.pi * C * 128, by positivity, fun t => ?_⟩
  rcases eq_or_ne t 0 with rfl | ht
  · simp [klWeight]; positivity
  set a := |t|
  have ha : 0 ≤ a := abs_nonneg t
  rw [Gamma_two_add_mul_Gamma_two_sub ht, Complex.norm_real, Real.norm_eq_abs]
  have hsh : Real.sinh (Real.pi * t) ≠ 0 := by
    rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero Real.pi_ne_zero ht
  have hshabs : 0 < |Real.sinh (Real.pi * t)| := abs_pos.2 hsh
  have h2 : Real.sinh (2 * Real.pi * t) = 2 * Real.sinh (Real.pi * t) * Real.cosh (Real.pi * t) := by
    rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.sinh_two_mul]
  have hW : ‖klWeight f t‖ = 4 / Real.pi ^ 2 * a * |Real.sinh (2 * Real.pi * t)| *
      ‖klTransform f (2 * t)‖ := by
    rw [klWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi ^ 2)]
  have hg := hb (2 * t)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hg
  have hlog := log_two_add_abs_le (2 * t)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hlog
  have hcosh : Real.cosh (Real.pi * t) * Real.exp (-(Real.pi * (2 * a)) / 2) ≤ 1 := by
    have := cosh_le_exp_abs' (Real.pi * t)
    rw [abs_mul, abs_of_pos hπ] at this
    calc Real.cosh (Real.pi * t) * Real.exp (-(Real.pi * (2 * a)) / 2)
        ≤ Real.exp (Real.pi * a) * Real.exp (-(Real.pi * (2 * a)) / 2) :=
          mul_le_mul_of_nonneg_right this (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hden : 0 < 1 + (2 * t) ^ (2 * 5) := by
    have : 0 ≤ (2 * t) ^ (2 * 5) := by rw [pow_mul]; positivity
    linarith
  have hpoly : (1 + a) ^ 5 * (1 + t ^ 2) ≤ 128 * (1 + (2 * t) ^ (2 * 5)) := by
    have h1 : (1 + t ^ 2) ≤ (1 + a) ^ 2 := by
      have : t ^ 2 = a ^ 2 := (sq_abs t).symm
      nlinarith
    have h2 := one_add_pow_le_two_pow_mul ha (show 7 ≤ 10 by norm_num)
    have h3 := pow_ten_le t
    calc (1 + a) ^ 5 * (1 + t ^ 2) ≤ (1 + a) ^ 5 * (1 + a) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 + a) ^ 7 := by ring
      _ ≤ 2 ^ 7 * (1 + a ^ 10) := h2
      _ ≤ 128 * (1 + (2 * t) ^ (2 * 5)) := by norm_num; linarith
  rw [hW, h2]
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (Real.cosh_pos _), abs_div, abs_mul, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2), abs_of_pos hπ]
  have hsq : a * a = t ^ 2 := by rw [← sq, sq_abs]
  have hkey : 4 / Real.pi ^ 2 * a * (2 * |Real.sinh (Real.pi * t)| * Real.cosh (Real.pi * t)) *
      ‖klTransform f (2 * t)‖ * ((1 + t ^ 2) * Real.pi * a / |Real.sinh (Real.pi * t)|) =
      8 / Real.pi * (a * a) * (1 + t ^ 2) * Real.cosh (Real.pi * t) * ‖klTransform f (2 * t)‖ := by
    field_simp
    ring
  have hA : t ^ 2 * (1 + t ^ 2) * (Real.log (2 + 2 * a) + 1) ≤ 2 * (1 + a) ^ 5 := by
    have hta : t ^ 2 ≤ (1 + a) ^ 2 := by
      have : t ^ 2 = a ^ 2 := (sq_abs t).symm
      nlinarith
    have hl : Real.log (2 + 2 * a) + 1 ≤ 2 * (1 + a) := by linarith
    have hl0 : 0 ≤ Real.log (2 + 2 * a) + 1 := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ 2 + 2 * a by linarith); linarith
    calc t ^ 2 * (1 + t ^ 2) * (Real.log (2 + 2 * a) + 1)
        ≤ (1 + a) ^ 2 * (1 + a) ^ 2 * (2 * (1 + a)) := by
          gcongr
          nlinarith
      _ = 2 * (1 + a) ^ 5 := by ring
  rw [hkey, hsq]
  rw [le_mul_inv_iff₀ (by positivity)]
  calc 8 / Real.pi * t ^ 2 * (1 + t ^ 2) * Real.cosh (Real.pi * t) * ‖klTransform f (2 * t)‖ *
        (1 + t ^ 2)
      ≤ 8 / Real.pi * t ^ 2 * (1 + t ^ 2) * Real.cosh (Real.pi * t) *
          (C * (Real.log (2 + 2 * a) + 1) * Real.exp (-(Real.pi * (2 * a)) / 2) /
            (1 + (2 * t) ^ (2 * 5))) * (1 + t ^ 2) := by gcongr
    _ = 8 / Real.pi * C * (t ^ 2 * (1 + t ^ 2) * (Real.log (2 + 2 * a) + 1)) *
          (Real.cosh (Real.pi * t) * Real.exp (-(Real.pi * (2 * a)) / 2)) * (1 + t ^ 2) /
            (1 + (2 * t) ^ (2 * 5)) := by ring
    _ ≤ 8 / Real.pi * C * (2 * (1 + a) ^ 5) * 1 * (1 + t ^ 2) / (1 + (2 * t) ^ (2 * 5)) := by
        gcongr 8 / Real.pi * C * ?_ * ?_ * (1 + t ^ 2) / _
    _ = 16 / Real.pi * C * ((1 + a) ^ 5 * (1 + t ^ 2)) / (1 + (2 * t) ^ (2 * 5)) := by ring
    _ ≤ 16 / Real.pi * C * (128 * (1 + (2 * t) ^ (2 * 5))) / (1 + (2 * t) ^ (2 * 5)) := by
        gcongr
    _ = 16 / Real.pi * C * 128 := by field_simp

/-- **`|H(t) K_{2it}(x)| ≤ D (|log x| + 1)(1+t²)⁻¹`.** -/
theorem exists_bound_klWeight_mul_besselK (hf : IsKLTest f) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x : ℝ, 0 < x → ∀ t : ℝ, ‖klWeight f t‖ *
      ‖modifiedBesselKOrder x (2 * t * Complex.I)‖ ≤ D * (|Real.log x| + 1) * (1 + t ^ 2)⁻¹ := by
  obtain ⟨C, hC, hb⟩ := exists_bound_klTransform hf 5
  have hπ := Real.pi_pos
  refine ⟨4 / Real.pi ^ 2 * Real.exp 2 * C * 8 * 32, by positivity, fun x hx t => ?_⟩
  set a := |t|
  have ha : 0 ≤ a := abs_nonneg t
  have hW : ‖klWeight f t‖ ≤ 4 / Real.pi ^ 2 * a * Real.exp (2 * Real.pi * a) *
      ‖klTransform f (2 * t)‖ := by
    rw [klWeight, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (by positivity : (0 : ℝ) < 4 / Real.pi ^ 2)]
    gcongr
    refine (norm_sinh_le_exp_abs _).trans (le_of_eq ?_)
    congr 1; rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hπ]
  have hg := hb (2 * t)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hg
  have hK := norm_modifiedBesselKOrder_I_mul_le_log hx (2 * t)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hK
  push_cast at hK
  have hlog := log_two_add_abs_le (2 * t)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hlog
  have hl0 : 0 ≤ Real.log (2 + 2 * a) := Real.log_nonneg (by linarith)
  have hden : 0 < 1 + (2 * t) ^ (2 * 5) := by
    have : 0 ≤ (2 * t) ^ (2 * 5) := by rw [pow_mul]; positivity
    linarith
  have hexp : Real.exp (2 * Real.pi * a) * Real.exp (-(Real.pi * (2 * a)) / 2) *
      Real.exp (-(Real.pi * (2 * a)) / 2) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf; exact Real.exp_zero
  have hpoly : (1 + a) ^ 3 * (1 + t ^ 2) ≤ 32 * (1 + (2 * t) ^ (2 * 5)) := by
    have h1 : (1 + t ^ 2) ≤ (1 + a) ^ 2 := by
      have : t ^ 2 = a ^ 2 := (sq_abs t).symm
      nlinarith
    have h2 := one_add_pow_le_two_pow_mul ha (show 5 ≤ 10 by norm_num)
    have h3 := pow_ten_le t
    calc (1 + a) ^ 3 * (1 + t ^ 2) ≤ (1 + a) ^ 3 * (1 + a) ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (1 + a) ^ 5 := by ring
      _ ≤ 2 ^ 5 * (1 + a ^ 10) := h2
      _ ≤ 32 * (1 + (2 * t) ^ (2 * 5)) := by norm_num; linarith
  have hA : a * (Real.log (2 + 2 * a) + 1) * (|Real.log x| + Real.log (2 + 2 * a) + 3) ≤
      8 * (|Real.log x| + 1) * (1 + a) ^ 3 := by
    have hlx := abs_nonneg (Real.log x)
    have e1 : Real.log (2 + 2 * a) + 1 ≤ 2 * (1 + a) := by linarith
    have e2 : |Real.log x| + Real.log (2 + 2 * a) + 3 ≤ 4 * (|Real.log x| + 1) * (1 + a) := by
      nlinarith
    calc a * (Real.log (2 + 2 * a) + 1) * (|Real.log x| + Real.log (2 + 2 * a) + 3)
        ≤ (1 + a) * (2 * (1 + a)) * (4 * (|Real.log x| + 1) * (1 + a)) := by
          gcongr; nlinarith
      _ = 8 * (|Real.log x| + 1) * (1 + a) ^ 3 := by ring
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ‖klWeight f t‖ * ‖modifiedBesselKOrder x (2 * t * Complex.I)‖ * (1 + t ^ 2)
      ≤ (4 / Real.pi ^ 2 * a * Real.exp (2 * Real.pi * a) *
          (C * (Real.log (2 + 2 * a) + 1) * Real.exp (-(Real.pi * (2 * a)) / 2) /
            (1 + (2 * t) ^ (2 * 5)))) *
          (Real.exp 2 * (|Real.log x| + Real.log (2 + 2 * a) + 3) *
            Real.exp (-(Real.pi * (2 * a)) / 2)) * (1 + t ^ 2) := by
        gcongr
        exact hW.trans (by gcongr)
    _ = 4 / Real.pi ^ 2 * Real.exp 2 * C *
          (a * (Real.log (2 + 2 * a) + 1) * (|Real.log x| + Real.log (2 + 2 * a) + 3)) *
          (Real.exp (2 * Real.pi * a) * Real.exp (-(Real.pi * (2 * a)) / 2) *
            Real.exp (-(Real.pi * (2 * a)) / 2)) * (1 + t ^ 2) / (1 + (2 * t) ^ (2 * 5)) := by ring
    _ ≤ 4 / Real.pi ^ 2 * Real.exp 2 * C * (8 * (|Real.log x| + 1) * (1 + a) ^ 3) * 1 *
          (1 + t ^ 2) / (1 + (2 * t) ^ (2 * 5)) := by
        rw [hexp]
        gcongr
    _ = 4 / Real.pi ^ 2 * Real.exp 2 * C * 8 * (|Real.log x| + 1) *
          ((1 + a) ^ 3 * (1 + t ^ 2)) / (1 + (2 * t) ^ (2 * 5)) := by ring
    _ ≤ 4 / Real.pi ^ 2 * Real.exp 2 * C * 8 * (|Real.log x| + 1) *
          (32 * (1 + (2 * t) ^ (2 * 5))) / (1 + (2 * t) ^ (2 * 5)) := by gcongr
    _ = 4 / Real.pi ^ 2 * Real.exp 2 * C * 8 * 32 * (|Real.log x| + 1) := by field_simp

/-! ## Joint continuity of `K_ν(x)` -/

/-- `(x, ν) ↦ K_ν(x)` is continuous on `(0, ∞) × ℂ`. -/
theorem continuousOn_modifiedBesselKOrder :
    ContinuousOn (fun p : ℝ × ℂ => modifiedBesselKOrder p.1 p.2) (Ioi 0 ×ˢ univ) := by
  rintro ⟨x₀, ν₀⟩ ⟨hx₀, -⟩
  have hx₀' : (0 : ℝ) < x₀ := hx₀
  refine ContinuousAt.continuousWithinAt ?_
  set R : ℝ := |ν₀.re| + 1
  refine continuousAt_of_dominated (μ := volume.restrict (Ioi 0))
    (bound := fun u => ‖besselOrderKernel (x₀ / 2) (R : ℂ) u‖) ?_ ?_
    (integrableOn_besselOrderKernel (half_pos hx₀') _).norm ?_
  · exact Eventually.of_forall fun p =>
      (by unfold besselOrderKernel; fun_prop : Continuous (besselOrderKernel p.1 p.2)).aestronglyMeasurable
  · have hU : {p : ℝ × ℂ | x₀ / 2 < p.1 ∧ |p.2.re - ν₀.re| < 1} ∈ 𝓝 (x₀, ν₀) := by
      refine IsOpen.mem_nhds ?_ ⟨by linarith, by simp⟩
      exact (isOpen_lt continuous_const continuous_fst).inter
        (isOpen_lt ((Complex.continuous_re.comp continuous_snd).sub continuous_const).abs continuous_const)
    filter_upwards [hU] with p hp
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := hu
    unfold besselOrderKernel
    rw [norm_mul, norm_mul]
    gcongr
    · rw [show -(p.1 : ℂ) * Complex.cosh (u : ℂ) = ((-(p.1 * Real.cosh u) : ℝ) : ℂ) by
          push_cast; ring,
        show -((x₀ / 2 : ℝ) : ℂ) * Complex.cosh (u : ℂ) = ((-(x₀ / 2 * Real.cosh u) : ℝ) : ℂ) by
          push_cast; ring, Complex.norm_exp_ofReal, Complex.norm_exp_ofReal]
      exact Real.exp_le_exp.2 (by nlinarith [Real.cosh_pos u, hp.1])
    · refine (norm_cosh_le _).trans ?_
      rw [show (R : ℂ) * (u : ℂ) = ((R * u : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_cosh,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.cosh_pos _), Real.cosh_le_cosh]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [abs_mul, abs_mul, abs_of_pos hu0, abs_of_pos (by positivity : (0 : ℝ) < R)]
      gcongr
      have := abs_sub_abs_le_abs_sub p.2.re ν₀.re
      simp only [R]; linarith [hp.2]
  · exact Eventually.of_forall fun u =>
      (by unfold besselOrderKernel; fun_prop : Continuous fun p : ℝ × ℂ =>
        besselOrderKernel p.1 p.2 u).continuousAt

/-! ## The `x`-integral of the weight -/

theorem abs_log_le_add_inv {x : ℝ} (hx : 0 < x) : |Real.log x| ≤ x + 1 / x := by
  rcases le_or_gt 1 x with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    have := Real.log_le_sub_one_of_pos hx
    have : 0 < 1 / x := by positivity
    linarith
  · rw [abs_of_neg (Real.log_neg hx h), ← Real.log_inv]
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hx)
    rw [one_div]; linarith

theorem integrableOn_besselMellinMajorant :
    IntegrableOn (fun x : ℝ => x ^ 2 * (|Real.log x| + 1) * ((1 + 1 / x) * Real.exp (-x))) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x) * x ^ ((4 : ℝ) - 1) +
      2 * (Real.exp (-x) * x ^ ((3 : ℝ) - 1)) + 2 * (Real.exp (-x) * x ^ ((2 : ℝ) - 1)) +
      Real.exp (-x) * x ^ ((1 : ℝ) - 1)) (Ioi 0) :=
    (((Real.GammaIntegral_convergent (by norm_num)).add
      ((Real.GammaIntegral_convergent (by norm_num)).const_mul 2)).add
      ((Real.GammaIntegral_convergent (by norm_num)).const_mul 2)).add
      (Real.GammaIntegral_convergent (by norm_num))
  refine hg.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ContinuousOn.mul (ContinuousOn.mul (by fun_prop) ?_) ?_
    · exact (Real.continuousOn_log.mono fun x hx => (ne_of_gt (show (0:ℝ) < x from hx))).abs.add
        continuousOn_const
    · exact (continuousOn_const.add (continuousOn_const.div continuousOn_id
        fun x hx => ne_of_gt (show (0:ℝ) < x from hx))).mul (by fun_prop)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hlog := abs_log_le_add_inv hx0
    have he := Real.exp_pos (-x)
    simp only [show (4 : ℝ) - 1 = (3 : ℕ) by norm_num, show (3 : ℝ) - 1 = (2 : ℕ) by norm_num,
      show (2 : ℝ) - 1 = (1 : ℕ) by norm_num, show (1 : ℝ) - 1 = (0 : ℕ) by norm_num,
      Real.rpow_natCast]
    have hinv : x * (1 / x) = 1 := by field_simp
    calc x ^ 2 * (|Real.log x| + 1) * ((1 + 1 / x) * Real.exp (-x))
        ≤ x ^ 2 * (x + 1 / x + 1) * ((1 + 1 / x) * Real.exp (-x)) := by gcongr
      _ = (x ^ 3 + 2 * x ^ 2 + 2 * x + 1) * Real.exp (-x) := by field_simp; ring
      _ = _ := by ring

theorem continuous_klWeight (hf : IsKLTest f) : Continuous (klWeight f) := by
  unfold klWeight
  exact (by fun_prop : Continuous fun t : ℝ =>
    ((4 / Real.pi ^ 2 * t * Real.sinh (2 * Real.pi * t) : ℝ) : ℂ)).mul
    ((continuous_klTransform hf).comp (continuous_const.mul continuous_id))

theorem besselPairMellin_two (t : ℝ) (ν : ℂ) :
    besselPairMellin 2 t ν = ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 *
      modifiedBesselKOrder x (2 * t * Complex.I) * modifiedBesselKOrder x (2 * ν) := by
  unfold besselPairMellin
  congr 1; funext x
  rw [show ((2 * 2 - 2 : ℝ) : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]

/-- **The `t`-integral of the weight against `M(t, ν)`**:
`∫ H(t) M(t, ν) dt = ∫_0^∞ x² K_{2ν}(x) x f(x) dx` for `|Re ν| ≤ ½` (`σ = 2`). -/
theorem integral_klWeight_mul_besselPairMellin (hf : IsKLTest f) {ν : ℂ} (hν : |ν.re| ≤ 1 / 2) :
    ∫ t : ℝ, klWeight f t * besselPairMellin 2 t ν =
      ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * ν) * (x * f x) := by
  obtain ⟨D, hD, hb⟩ := exists_bound_klWeight_mul_besselK hf
  have h2ν : |(2 * ν).re| ≤ 1 := by
    rw [show (2 * ν).re = 2 * ν.re by simp, abs_mul, abs_two]; linarith
  set F : ℝ → ℝ → ℂ := fun t x => klWeight f t * ((x : ℂ) ^ 2 *
    modifiedBesselKOrder x (2 * t * Complex.I) * modifiedBesselKOrder x (2 * ν))
  have hprod : (volume : Measure ℝ).prod (volume.restrict (Ioi (0 : ℝ))) =
      ((volume : Measure ℝ).prod volume).restrict (univ ×ˢ Ioi 0) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hcont : ContinuousOn (Function.uncurry F) (univ ×ˢ Ioi 0) := by
    have hg₁ : Continuous (fun p : ℝ × ℝ => ((p.2, 2 * (p.1 : ℂ) * Complex.I) : ℝ × ℂ)) := by
      fun_prop
    have hg₂ : Continuous (fun p : ℝ × ℝ => ((p.2, 2 * ν) : ℝ × ℂ)) := by fun_prop
    have hK := continuousOn_modifiedBesselKOrder.comp hg₁.continuousOn
      (s := univ ×ˢ Ioi (0 : ℝ)) fun p hp => ⟨hp.2, mem_univ _⟩
    have hK' := continuousOn_modifiedBesselKOrder.comp hg₂.continuousOn
      (s := univ ×ˢ Ioi (0 : ℝ)) fun p hp => ⟨hp.2, mem_univ _⟩
    simp only [Function.comp_def] at hK hK'
    exact ((continuous_klWeight hf).comp continuous_fst).continuousOn.mul
      ((((by fun_prop : Continuous fun p : ℝ × ℝ => (p.2 : ℂ) ^ 2).continuousOn).mul hK).mul hK')
  have hint : Integrable (Function.uncurry F) ((volume : Measure ℝ).prod (volume.restrict (Ioi 0))) := by
    have hB := (integrable_inv_one_add_sq.const_mul D).mul_prod
      (integrableOn_besselMellinMajorant)
    refine hB.mono' ?_ ?_
    · rw [hprod]
      exact hcont.aestronglyMeasurable (MeasurableSet.univ.prod measurableSet_Ioi)
    · rw [hprod]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
      have hx : (0 : ℝ) < p.2 := hp.2
      simp only [Function.uncurry, F, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hx]
      have h1 := hb p.2 hx p.1
      have h2 := norm_modifiedBesselKOrder_le_of_abs_re_le_one hx h2ν
      calc ‖klWeight f p.1‖ * (p.2 ^ 2 * ‖modifiedBesselKOrder p.2 (2 * p.1 * Complex.I)‖ *
            ‖modifiedBesselKOrder p.2 (2 * ν)‖)
          = (‖klWeight f p.1‖ * ‖modifiedBesselKOrder p.2 (2 * p.1 * Complex.I)‖) *
              (p.2 ^ 2 * ‖modifiedBesselKOrder p.2 (2 * ν)‖) := by ring
        _ ≤ (D * (|Real.log p.2| + 1) * (1 + p.1 ^ 2)⁻¹) *
              (p.2 ^ 2 * ((1 + 1 / p.2) * Real.exp (-p.2))) := by gcongr
        _ = D * (1 + p.1 ^ 2)⁻¹ *
              (p.2 ^ 2 * (|Real.log p.2| + 1) * ((1 + 1 / p.2) * Real.exp (-p.2))) := by ring
  have hL : ∫ t : ℝ, klWeight f t * besselPairMellin 2 t ν =
      ∫ t : ℝ, ∫ x in Ioi (0 : ℝ), F t x := by
    congr 1; funext t
    rw [besselPairMellin_two, ← integral_const_mul]
  rw [hL, integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
  simp only [F]
  have h := integral_klWeight_mul_besselK hf (show (0 : ℝ) < x from hx)
  calc ∫ t : ℝ, klWeight f t * ((x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * t * Complex.I) *
        modifiedBesselKOrder x (2 * ν))
      = (x : ℂ) ^ 2 * modifiedBesselKOrder x (2 * ν) *
          ∫ t : ℝ, klWeight f t * modifiedBesselKOrder x (2 * t * Complex.I) := by
        rw [← integral_const_mul]; congr 1; funext t; ring
    _ = _ := by rw [h]

end

end GaloisForLFunctions.RHTower.DeckPointPair
