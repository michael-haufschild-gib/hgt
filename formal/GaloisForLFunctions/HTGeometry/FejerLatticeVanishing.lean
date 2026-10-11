import Mathlib

/-!
# Fejér lattice sums vanish off resonance

The triangle `Λ_a(u) = (1 − |u|/a)⁺` has Fourier transform `𝓕Λ_a(ξ) = a · sinc(π a ξ)²`
(`fourier_triangleFn`). By Poisson summation (`Real.tsum_eq_tsum_fourier_of_rpow_decay`),

`Σ_{m ∈ ℤ} a sinc(π a m)² e^{2πimx} = Σ_{n ∈ ℤ} Λ_a(x + n)`,

and the right side vanishes when `x` is at distance `≥ a` from every integer
(`tsum_sinc_sq_mul_fourier_eq_zero`). So a Fejér-weighted exponential sum over a perfect lattice
is exactly zero away from resonance.
-/

noncomputable section

open Real Complex MeasureTheory Filter Asymptotics

namespace GaloisForLFunctions.HTGeometry

variable {a : ℝ}

/-- The triangle `Λ_a(u) = (1 − |u|/a)⁺`. -/
def triangleFn (a u : ℝ) : ℝ := max (1 - |u| / a) 0

theorem triangleFn_nonneg (a u : ℝ) : 0 ≤ triangleFn a u := le_max_right _ _

theorem triangleFn_eq_zero {a u : ℝ} (ha : 0 < a) (hu : a ≤ |u|) : triangleFn a u = 0 := by
  unfold triangleFn
  apply max_eq_right
  rw [sub_nonpos, le_div_iff₀ ha]; linarith

theorem continuous_triangleFn (a : ℝ) : Continuous (triangleFn a) := by
  unfold triangleFn; fun_prop

theorem triangleFn_le_one {a : ℝ} (ha : 0 < a) (u : ℝ) : triangleFn a u ≤ 1 := by
  unfold triangleFn
  apply max_le _ zero_le_one
  have : 0 ≤ |u| / a := by positivity
  linarith

/-- The antiderivative identity on `[0, a]`. -/
theorem integral_triangle_cexp_right {a ω : ℝ} (ha : 0 < a) (hω : ω ≠ 0) :
    ∫ v in (0 : ℝ)..a, ((1 - v / a : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I) =
      (I / ω - 1 / (ω ^ 2 * a) : ℂ) * (Complex.exp (-(ω * a : ℝ) * I) - 1) +
        (-I / (ω * a) : ℂ) * (a * Complex.exp (-(ω * a : ℝ) * I)) := by
  set A : ℂ := I / ω - 1 / (ω ^ 2 * a) with hA
  set B : ℂ := -I / (ω * a) with hB
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hderiv : ∀ v : ℝ, HasDerivAt (fun v : ℝ => Complex.exp (-(ω * v : ℝ) * I) * (A + B * v))
      (((1 - v / a : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I)) v := by
    intro v
    have h1 : HasDerivAt (fun v : ℝ => (-(ω * v : ℝ) : ℂ) * I) (-(ω : ℂ) * I) v := by
      have := ((hasDerivAt_id v).const_mul ω).ofReal_comp.neg.mul_const I
      simpa using this
    have h2 := h1.cexp
    have h3 : HasDerivAt (fun v : ℝ => A + B * (v : ℂ)) B v := by
      have := (hasDerivAt_id v).ofReal_comp.const_mul B |>.const_add A
      simpa using this
    have h4 := h2.mul h3
    refine h4.congr_deriv ?_
    generalize Complex.exp (-(ω * v : ℝ) * I) = E
    rw [hA, hB]
    push_cast
    field_simp
    ring_nf
    simp only [Complex.I_sq]
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ => hderiv v)]
  · simp only [Complex.ofReal_zero, mul_zero, neg_zero, zero_mul, Complex.exp_zero, one_mul,
      add_zero]
    ring
  · apply Continuous.intervalIntegrable
    fun_prop


/-- The value of the right half: `∫_0^a (1 − v/a) e^{−iωv} dv = −i/ω + (1 − e^{−iωa})/(ω²a)`. -/
theorem integral_triangle_cexp_right' {a ω : ℝ} (ha : 0 < a) (hω : ω ≠ 0) :
    ∫ v in (0 : ℝ)..a, ((1 - v / a : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I) =
      -I / ω + (1 - Complex.exp (-(ω * a : ℝ) * I)) / (ω ^ 2 * a) := by
  rw [integral_triangle_cexp_right ha hω]
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  ring

/-- `∫_{−a}^{a} Λ_a(v) e^{−iωv} dv = (2 − 2 cos(ωa))/(ω²a)` for `ω ≠ 0`. -/
theorem integral_triangleFn_cexp {a ω : ℝ} (ha : 0 < a) (hω : ω ≠ 0) :
    ∫ v in (-a)..a, ((triangleFn a v : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I) =
      ((2 - 2 * Real.cos (ω * a)) / (ω ^ 2 * a) : ℝ) := by
  have hcont : Continuous (fun v : ℝ => ((triangleFn a v : ℝ) : ℂ) *
      Complex.exp (-(ω * v : ℝ) * I)) := by
    have := continuous_triangleFn a; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  -- the right half
  have hR : ∫ v in (0 : ℝ)..a, ((triangleFn a v : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I) =
      ∫ v in (0 : ℝ)..a, ((1 - v / a : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I) := by
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le ha.le] at hv
    congr 2
    unfold triangleFn
    rw [abs_of_nonneg hv.1]
    apply max_eq_left
    rw [sub_nonneg, div_le_one ha]; exact hv.2
  -- the left half, reflected
  have hL : ∫ v in (-a)..0, ((triangleFn a v : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I) =
      ∫ v in (0 : ℝ)..a, ((1 - v / a : ℝ) : ℂ) * Complex.exp (-((-ω) * v : ℝ) * I) := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := a)
      (fun v : ℝ => ((triangleFn a v : ℝ) : ℂ) * Complex.exp (-(ω * v : ℝ) * I))
    rw [neg_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun v hv => ?_
    rw [Set.uIcc_of_le ha.le] at hv
    congr 1
    · congr 1
      unfold triangleFn
      rw [abs_neg, abs_of_nonneg hv.1]
      apply max_eq_left
      rw [sub_nonneg, div_le_one ha]; exact hv.2
    · congr 2; push_cast; ring
  rw [hR, hL, integral_triangle_cexp_right' ha hω, integral_triangle_cexp_right' ha (neg_ne_zero.mpr hω)]
  have hω' : (ω : ℂ) ≠ 0 := by exact_mod_cast hω
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have e1 : Complex.exp (-(-(ω : ℂ) * (a : ℂ)) * I) = Complex.exp ((ω * a : ℝ) * I) := by
    congr 1; push_cast; ring
  have e2 : Complex.exp (-((ω : ℂ) * (a : ℂ)) * I) = Complex.exp (-(ω * a : ℝ) * I) := by
    congr 1; push_cast; ring
  have hcos : ((Real.cos (ω * a) : ℝ) : ℂ) =
      (Complex.exp ((ω * a : ℝ) * I) + Complex.exp (-(ω * a : ℝ) * I)) / 2 := by
    rw [Complex.ofReal_cos, Complex.cos]
  push_cast at e1 e2 hcos ⊢
  rw [e1, e2, hcos]
  field_simp
  ring


/-- `∫_{−a}^{a} Λ_a = a`. -/
theorem integral_triangleFn {a : ℝ} (ha : 0 < a) :
    ∫ v in (-a)..a, ((triangleFn a v : ℝ) : ℂ) = (a : ℂ) := by
  have hcont : Continuous (fun v : ℝ => ((triangleFn a v : ℝ) : ℂ)) := by
    have := continuous_triangleFn a; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have hpos : ∀ v ∈ Set.uIcc (0 : ℝ) a, ((triangleFn a v : ℝ) : ℂ) = ((1 - v / a : ℝ) : ℂ) := by
    intro v hv
    rw [Set.uIcc_of_le ha.le] at hv
    congr 1
    unfold triangleFn
    rw [abs_of_nonneg hv.1]
    apply max_eq_left
    rw [sub_nonneg, div_le_one ha]; exact hv.2
  have hneg : ∀ v ∈ Set.uIcc (-a) (0 : ℝ),
      ((triangleFn a v : ℝ) : ℂ) = ((1 + v / a : ℝ) : ℂ) := by
    intro v hv
    rw [Set.uIcc_of_le (by linarith)] at hv
    congr 1
    unfold triangleFn
    rw [abs_of_nonpos hv.2, show 1 - -v / a = 1 + v / a by ring]
    apply max_eq_left
    have : -1 ≤ v / a := by rw [le_div_iff₀ ha]; linarith [hv.1]
    linarith
  rw [intervalIntegral.integral_congr hneg, intervalIntegral.integral_congr hpos,
    intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
  have hd1 : ∀ v ∈ Set.uIcc (-a) (0 : ℝ), HasDerivAt (fun v : ℝ => v + v ^ 2 / (2 * a))
      (1 + v / a) v := by
    intro v _
    have h := (hasDerivAt_id v).add ((hasDerivAt_pow 2 v).div_const (2 * a))
    refine h.congr_deriv ?_
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    field_simp
  have hd2 : ∀ v ∈ Set.uIcc (0 : ℝ) a, HasDerivAt (fun v : ℝ => v - v ^ 2 / (2 * a))
      (1 - v / a) v := by
    intro v _
    have h := (hasDerivAt_id v).sub ((hasDerivAt_pow 2 v).div_const (2 * a))
    refine h.congr_deriv ?_
    simp only [show (2 : ℕ) - 1 = 1 from rfl, pow_one, Nat.cast_ofNat]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd1 (by
      apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd2 (by
      apply Continuous.intervalIntegrable; fun_prop)]
  push_cast
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  field_simp
  ring

/-- **The Fourier transform of the triangle.** `𝓕Λ_a(ξ) = a sinc(π a ξ)²`. -/
theorem fourier_triangleFn {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    FourierTransform.fourier (fun u : ℝ => ((triangleFn a u : ℝ) : ℂ)) ξ =
      ((a * Real.sinc (Real.pi * a * ξ) ^ 2 : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq]
  have hint : (∫ v : ℝ, Real.fourierChar (-(v * ξ)) • ((triangleFn a v : ℝ) : ℂ)) =
      ∫ v in (-a)..a, ((triangleFn a v : ℝ) : ℂ) * Complex.exp (-((2 * Real.pi * ξ) * v : ℝ) * I) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Icc (-a) a)]
    · refine setIntegral_congr_fun measurableSet_Icc fun v _ => ?_
      simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
      push_cast
      ring_nf
    · intro v hv
      have : a ≤ |v| := by
        by_contra h; push Not at h
        exact hv ⟨by linarith [neg_abs_le v], by linarith [le_abs_self v]⟩
      rw [triangleFn_eq_zero ha this]; simp
  rw [hint]
  rcases eq_or_ne ξ 0 with h0 | h0
  · subst h0
    simp only [mul_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, mul_one,
      Real.sinc_zero, one_pow]
    exact integral_triangleFn ha
  · have hω : 2 * Real.pi * ξ ≠ 0 := by positivity
    rw [integral_triangleFn_cexp ha hω]
    congr 1
    have hθ : Real.pi * a * ξ ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hθ]
    have hc : Real.cos (2 * Real.pi * ξ * a) = 1 - 2 * Real.sin (Real.pi * a * ξ) ^ 2 := by
      rw [show 2 * Real.pi * ξ * a = 2 * (Real.pi * a * ξ) by ring, Real.cos_two_mul,
        Real.cos_sq']
      ring
    rw [hc]
    field_simp
    ring


/-- `|sinc y| ≤ 1/|y|`. -/
theorem abs_sinc_le_inv {y : ℝ} (hy : y ≠ 0) : |Real.sinc y| ≤ 1 / |y| := by
  rw [Real.sinc_of_ne_zero hy, abs_div]
  exact div_le_div_of_nonneg_right (Real.abs_sin_le_one y) (abs_nonneg y)

/-- The set `{|x| ≥ R}` belongs to the cocompact filter. -/
theorem eventually_abs_ge_cocompact (R : ℝ) : ∀ᶠ x : ℝ in cocompact ℝ, R ≤ |x| := by
  refine Filter.mem_of_superset (isCompact_Icc (a := -R) (b := R)).compl_mem_cocompact ?_
  intro x hx
  simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le] at hx
  simp only [Set.mem_setOf_eq]
  rcases hx with h | h
  · linarith [neg_le_abs x]
  · linarith [le_abs_self x]

/-- **Poisson summation for the triangle.** -/
theorem tsum_triangleFn_eq (ha : 0 < a) (x : ℝ) :
    ∑' n : ℤ, ((triangleFn a (x + n) : ℝ) : ℂ) =
      ∑' n : ℤ, ((a * Real.sinc (Real.pi * a * n) ^ 2 : ℝ) : ℂ) * (fourier n) (x : UnitAddCircle) := by
  have hf : Continuous (fun u : ℝ => ((triangleFn a u : ℝ) : ℂ)) := by
    have := continuous_triangleFn a; fun_prop
  have h1 : (fun u : ℝ => ((triangleFn a u : ℝ) : ℂ)) =O[cocompact ℝ] fun x => |x| ^ (-(2 : ℝ)) := by
    refine IsBigO.of_bound 1 ?_
    filter_upwards [eventually_abs_ge_cocompact a] with u hu
    rw [triangleFn_eq_zero ha hu]; simp only [Complex.ofReal_zero, norm_zero, one_mul]
    positivity
  have h2 : FourierTransform.fourier (fun u : ℝ => ((triangleFn a u : ℝ) : ℂ)) =O[cocompact ℝ]
      fun x => |x| ^ (-(2 : ℝ)) := by
    refine IsBigO.of_bound (1 / (Real.pi ^ 2 * a)) ?_
    filter_upwards [eventually_abs_ge_cocompact 1] with u hu
    have hu0 : u ≠ 0 := by intro h; rw [h, abs_zero] at hu; linarith
    rw [fourier_triangleFn ha, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ |u| ^ (-(2 : ℝ))), Real.rpow_neg (abs_nonneg u),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hθ : Real.pi * a * u ≠ 0 := by positivity
    have hs := abs_sinc_le_inv hθ
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos, abs_of_pos ha] at hs
    rw [abs_mul, abs_of_pos ha, abs_pow, sq_abs]
    have hsq : Real.sinc (Real.pi * a * u) ^ 2 ≤ (1 / (Real.pi * a * |u|)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
    calc a * Real.sinc (Real.pi * a * u) ^ 2 ≤ a * (1 / (Real.pi * a * |u|)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq ha.le
      _ = 1 / (Real.pi ^ 2 * a) * (|u| ^ 2)⁻¹ := by field_simp
  have := Real.tsum_eq_tsum_fourier_of_rpow_decay hf (by norm_num : (1 : ℝ) < 2) h1 h2 x
  rw [this]
  congr 1; funext n
  rw [fourier_triangleFn ha]

/-- **Fejér lattice sums vanish off resonance.** If `x` is at distance `≥ a` from every integer,
`Σ_m sinc(π a m)² e^{2πimx} = 0`. -/
theorem tsum_sinc_sq_mul_fourier_eq_zero (ha : 0 < a) {x : ℝ} (hx : ∀ n : ℤ, a ≤ |x + n|) :
    ∑' n : ℤ, ((Real.sinc (Real.pi * a * n) ^ 2 : ℝ) : ℂ) * (fourier n) (x : UnitAddCircle) = 0 := by
  have h := tsum_triangleFn_eq ha x
  have h0 : ∑' n : ℤ, ((triangleFn a (x + n) : ℝ) : ℂ) = 0 := by
    have : ∀ n : ℤ, ((triangleFn a (x + n) : ℝ) : ℂ) = 0 := fun n => by
      rw [triangleFn_eq_zero ha (hx n)]; simp
    simp [this]
  rw [h0] at h
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h' : ∑' n : ℤ, ((a * Real.sinc (Real.pi * a * n) ^ 2 : ℝ) : ℂ) * (fourier n) (x : UnitAddCircle) =
      (a : ℂ) * ∑' n : ℤ, ((Real.sinc (Real.pi * a * n) ^ 2 : ℝ) : ℂ) *
        (fourier n) (x : UnitAddCircle) := by
    rw [← tsum_mul_left]; congr 1; funext n; push_cast; ring
  rw [h'] at h
  exact (mul_eq_zero.mp h.symm).resolve_left ha'

end GaloisForLFunctions.HTGeometry
