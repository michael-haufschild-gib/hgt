import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheSineKernelMomentsMatchTheBlindSpot

/-!
# The sine-kernel fourth Gram moment is `13/4`
-/

open MeasureTheory Complex FourierTransform
open scoped ComplexConjugate Convolution

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SineKernel

open _root_.RHTower

/-! ### The quadratic spline `Δ ⋆ 1` -/

/-- The real spline `(Δ ⋆ 1)(η) = ∫_{η−1/2}^{η+1/2} (1 − |t|)₊ dt`. -/
def quadR (η : ℝ) : ℝ := ∫ t in (η - 1 / 2)..(η + 1 / 2), triR t

theorem continuous_triR : Continuous triR := by unfold triR; fun_prop

theorem quad_apply (η : ℝ) : quad η = (quadR η : ℂ) := by
  have hpt : (fun t => (ContinuousLinearMap.mul ℂ ℂ) (tri t) (ind (η - t))) =
      (Set.Icc (η - 1 / 2) (η + 1 / 2)).indicator fun t => (triR t : ℂ) := by
    funext t
    rw [ContinuousLinearMap.mul_apply', ind_apply, tri_apply, Set.indicator_apply]
    by_cases h : η - t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
    · rw [if_pos h, if_pos ⟨by linarith [h.2], by linarith [h.1]⟩, mul_one]
    · rw [if_neg h, if_neg fun h' => h ⟨by linarith [h'.2], by linarith [h'.1]⟩, mul_zero]
  rw [quad, convolution_def, hpt, integral_indicator measurableSet_Icc, integral_complex_ofReal,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), quadR]

theorem intervalIntegral_lin (a b c d : ℝ) :
    ∫ t in a..b, (c + d * t) = c * (b - a) + d * (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id.const_mul d), intervalIntegral.integral_const,
    intervalIntegral.integral_const_mul, integral_id, smul_eq_mul]
  ring

theorem triR_eq_of_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : triR t = 1 + -1 * t := by
  rw [triR, abs_of_nonneg h0, max_eq_left (by linarith)]; ring

theorem triR_eq_of_nonpos {t : ℝ} (h0 : t ≤ 0) (h1 : -1 ≤ t) : triR t = 1 + 1 * t := by
  rw [triR, abs_of_nonpos h0, max_eq_left (by linarith)]; ring

theorem triR_eq_zero {t : ℝ} (h : 1 ≤ |t|) : triR t = 0 := max_eq_right (by linarith)

theorem quadR_of_abs_le_half {η : ℝ} (h : |η| ≤ 1 / 2) : quadR η = 3 / 4 - η ^ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp h
  have hc := continuous_triR
  rw [quadR, ← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun t => 1 + 1 * t) fun t ht => ?_,
    intervalIntegral.integral_congr (a := 0) (g := fun t => 1 + -1 * t) fun t ht => ?_,
    intervalIntegral_lin, intervalIntegral_lin]
  · ring
  · rw [Set.uIcc_of_le (by linarith)] at ht
    exact triR_eq_of_nonneg ht.1 (by linarith [ht.2])
  · rw [Set.uIcc_of_le (by linarith)] at ht
    exact triR_eq_of_nonpos ht.2 (by linarith [ht.1])

theorem quadR_of_half_le {η : ℝ} (h1 : 1 / 2 ≤ η) (h2 : η ≤ 3 / 2) :
    quadR η = (3 / 2 - η) ^ 2 / 2 := by
  have hc := continuous_triR
  rw [quadR, ← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun t => 1 + -1 * t) fun t ht => ?_,
    intervalIntegral.integral_congr (a := 1) (g := fun _ => (0 : ℝ)) fun t ht => ?_,
    intervalIntegral_lin, intervalIntegral.integral_zero]
  · ring
  · rw [Set.uIcc_of_le (by linarith)] at ht
    exact triR_eq_zero (by rw [abs_of_nonneg (by linarith [ht.1])]; exact ht.1)
  · rw [Set.uIcc_of_le (by linarith)] at ht
    exact triR_eq_of_nonneg (by linarith [ht.1]) ht.2

theorem quadR_of_le_neg_half {η : ℝ} (h1 : -(3 / 2) ≤ η) (h2 : η ≤ -(1 / 2)) :
    quadR η = (3 / 2 + η) ^ 2 / 2 := by
  have hc := continuous_triR
  rw [quadR, ← intervalIntegral.integral_add_adjacent_intervals (b := -1)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_,
    intervalIntegral.integral_congr (a := -1) (g := fun t => 1 + 1 * t) fun t ht => ?_,
    intervalIntegral_lin, intervalIntegral.integral_zero]
  · ring
  · rw [Set.uIcc_of_le (by linarith)] at ht
    exact triR_eq_of_nonpos (by linarith [ht.2]) ht.1
  · rw [Set.uIcc_of_le (by linarith)] at ht
    exact triR_eq_zero (by rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2])

theorem quadR_eq_zero {η : ℝ} (h : 3 / 2 ≤ |η|) : quadR η = 0 := by
  rw [quadR, intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_,
    intervalIntegral.integral_zero]
  rw [Set.uIcc_of_le (by linarith)] at ht
  refine triR_eq_zero ?_
  rcases le_abs'.mp h with h' | h'
  · rw [abs_of_nonpos (by linarith [ht.2])]; linarith [ht.2]
  · rw [abs_of_nonneg (by linarith [ht.1])]; linarith [ht.1]

theorem continuous_quadR : Continuous quadR := by
  have hc := continuous_triR
  have hp := intervalIntegral.continuous_primitive (μ := volume)
    (fun a b => hc.intervalIntegrable a b) 0
  have e : quadR = fun η => (∫ t in (0 : ℝ)..(η + 1 / 2), triR t) -
      ∫ t in (0 : ℝ)..(η - 1 / 2), triR t := by
    funext η
    rw [quadR, intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  rw [e]
  exact (hp.comp (continuous_id.add continuous_const)).sub
    (hp.comp (continuous_id.sub continuous_const))

/-- `∫ (Δ ⋆ 1)² = 11/20`. -/
theorem integral_quadR_sq : ∫ η, quadR η ^ 2 = 11 / 20 := by
  have hs : ∫ η in Set.Icc (-(3 / 2) : ℝ) (3 / 2), quadR η ^ 2 = ∫ η, quadR η ^ 2 :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun η hη => by
      rw [quadR_eq_zero, zero_pow two_ne_zero]
      by_contra hlt
      exact hη (abs_le.mp (le_of_lt (not_le.mp hlt)))
  have hc : Continuous fun η => quadR η ^ 2 := continuous_quadR.pow 2
  rw [← hs, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    ← intervalIntegral.integral_add_adjacent_intervals (b := -(1 / 2))
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := -(1 / 2)) (b := 1 / 2)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),
    intervalIntegral.integral_congr (a := -(3 / 2)) (b := -(1 / 2))
      (g := fun η => (3 / 2 + η) ^ 4 / 4) fun η hη => ?_,
    intervalIntegral.integral_congr (a := -(1 / 2)) (b := 1 / 2)
      (g := fun η => 9 / 16 - 3 / 2 * η ^ 2 + η ^ 4) fun η hη => ?_,
    intervalIntegral.integral_congr (a := 1 / 2) (b := 3 / 2)
      (g := fun η => (3 / 2 - η) ^ 4 / 4) fun η hη => ?_]
  · have e1 := intervalIntegral.integral_comp_add_left (fun u : ℝ => u ^ 4) (3 / 2 : ℝ)
      (a := -(3 / 2)) (b := -(1 / 2))
    have e3 := intervalIntegral.integral_comp_sub_left (fun u : ℝ => u ^ 4) (3 / 2 : ℝ)
      (a := 1 / 2) (b := 3 / 2)
    beta_reduce at e1 e3
    rw [intervalIntegral.integral_div, intervalIntegral.integral_div, e1, e3,
      intervalIntegral.integral_add ((by fun_prop : Continuous fun x : ℝ => 9 / 16 - 3 / 2 * x ^ 2)
        |>.intervalIntegrable _ _) ((continuous_pow 4).intervalIntegrable _ _),
      intervalIntegral.integral_sub intervalIntegrable_const
        ((by fun_prop : Continuous fun x : ℝ => 3 / 2 * x ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    norm_num [integral_pow]
  all_goals
    rw [Set.uIcc_of_le (by norm_num)] at hη
    first
    | rw [quadR_of_le_neg_half hη.1 hη.2]; ring
    | rw [quadR_of_abs_le_half (abs_le.mpr ⟨hη.1, hη.2⟩)]; ring
    | rw [quadR_of_half_le hη.1 hη.2]; ring

theorem conj_quad (η : ℝ) : conj (quad η) = quad η := by rw [quad_apply, Complex.conj_ofReal]

/-- `∫ 1·(Δ ⋆ 1)² = ∫_{−1/2}^{1/2} (3/4 − η²)² = 9/20`. -/
theorem integral_ind_mul_quad_sq : ∫ η, ind η * quad η ^ 2 = ((9 / 20 : ℝ) : ℂ) := by
  have hpt : (fun η => ind η * quad η ^ 2) =
      (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator fun η => ((quadR η ^ 2 : ℝ) : ℂ) := by
    funext η
    rw [ind_apply, Set.indicator_apply, quad_apply]
    split_ifs <;> push_cast <;> ring
  rw [hpt, integral_indicator measurableSet_Icc, integral_complex_ofReal,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_congr (g := fun η => 9 / 16 - 3 / 2 * η ^ 2 + η ^ 4) fun η hη => ?_]
  · rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun x : ℝ => 9 / 16 - 3 / 2 * x ^ 2)
        |>.intervalIntegrable _ _) ((continuous_pow 4).intervalIntegrable _ _),
      intervalIntegral.integral_sub intervalIntegrable_const
        ((by fun_prop : Continuous fun x : ℝ => 3 / 2 * x ^ 2).intervalIntegrable _ _),
      intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
    norm_num [integral_pow]
  · rw [Set.uIcc_of_le (by norm_num)] at hη
    show quadR η ^ 2 = _
    rw [quadR_of_abs_le_half (abs_le.mpr ⟨hη.1, hη.2⟩)]; ring

/-- `∫ S⁶ = ∫ (Δ ⋆ 1)² = 11/20`. -/
theorem integral_sk_pow_six : Integrable (fun x => sk x ^ 6) ∧ ∫ x, sk x ^ 6 = 11 / 20 := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_quad memLp_two_quad integrable_quad
    memLp_two_quad fourier_quad' fourier_quad'
  simp_rw [conj_quad, quad_apply, ← Complex.ofReal_mul, integral_complex_ofReal] at he
  have h := Complex.ofReal_inj.mp he
  have e : (fun x => sk x ^ 6) = fun x => sk x ^ 3 * sk x ^ 3 := funext fun x => by ring
  refine ⟨by rw [e]; exact hi, ?_⟩
  rw [e, h]
  simp_rw [← sq]
  exact integral_quadR_sq

/-- `∫ S³ A = ∫ 1·(Δ ⋆ 1)² = 9/20`. -/
theorem integral_sk_cube_mul_sA :
    Integrable (fun x => sk x ^ 3 * sA x) ∧ ∫ x, sk x ^ 3 * sA x = 9 / 20 := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_quad memLp_two_quad
    integrable_ind_mul_quad memLp_two_ind_mul_quad fourier_quad' fourier_ind_mul_quad
  simp_rw [conj_quad] at he
  rw [show (fun η => quad η * (ind η * quad η)) = fun η => ind η * quad η ^ 2 from
    funext fun η => by ring, integral_ind_mul_quad_sq] at he
  exact ⟨hi, by exact_mod_cast he⟩

/-! ### Correlation determinants -/

/-- The kernel matrix `[S(p_a − p_b)]` of a configuration `p`. -/
def kernelMatrix {n : ℕ} (p : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun a b => sk (p a - p b)

/-- The three-point correlation `ρ₃(0, x, y) = det[S(p_a − p_b)]`. -/
def rho₃ (x y : ℝ) : ℝ := (kernelMatrix ![0, x, y]).det

/-- The four-point correlation `ρ₄(0, x, y, z) = det[S(p_a − p_b)]`. -/
def rho₄ (x y z : ℝ) : ℝ := (kernelMatrix ![0, x, y, z]).det

theorem sk_zero : sk 0 = 1 := by simp [sk]

theorem sk_sub_comm (a b : ℝ) : sk (b - a) = sk (a - b) := by rw [← neg_sub, sk_neg]

theorem rho₃_eq (x y : ℝ) :
    rho₃ x y = 1 - sk x ^ 2 - sk y ^ 2 - sk (x - y) ^ 2 + 2 * sk x * sk y * sk (x - y) := by
  simp only [rho₃, kernelMatrix, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, sub_self,
    sub_zero, zero_sub, sk_neg, sk_zero, sk_sub_comm x y]
  ring

theorem rho₄_eq (x y z : ℝ) :
    rho₄ x y z = 1 - (sk x ^ 2 + sk y ^ 2 + sk z ^ 2 + sk (x - y) ^ 2 + sk (x - z) ^ 2 +
      sk (y - z) ^ 2) + 2 * (sk x * sk y * sk (x - y) + sk x * sk z * sk (x - z) +
      sk y * sk z * sk (y - z) + sk (x - y) * sk (x - z) * sk (y - z)) +
      (sk x ^ 2 * sk (y - z) ^ 2 + sk y ^ 2 * sk (x - z) ^ 2 + sk z ^ 2 * sk (x - y) ^ 2) -
      2 * (sk x * sk (x - y) * sk (y - z) * sk z + sk x * sk (x - z) * sk (y - z) * sk y +
        sk y * sk (x - y) * sk (x - z) * sk z) := by
  simp only [rho₄, kernelMatrix, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.of_apply,
    Matrix.submatrix_apply, Fin.succAbove, Matrix.cons_val_zero, Fin.sum_univ_zero]
  simp [Fin.lt_def, sk_neg, sk_zero, sk_sub_comm x y, sk_sub_comm x z, sk_sub_comm y z,
    Fin.succ, Fin.castSucc, Fin.castAdd, Fin.castLE]
  ring

/-! ### The pair and square-pair terms -/

/-- The pair term with weight `S⁴`: `∫ S⁴ ρ₂`. -/
def sineQuartPair : ℝ := ∫ x, sk x ^ 4 * (1 - sk x ^ 2)

theorem sineQuartPair_eq : sineQuartPair = 7 / 60 := by
  have e : (fun x => sk x ^ 4 * (1 - sk x ^ 2)) = fun x => sk x ^ 4 - sk x ^ 6 :=
    funext fun x => by ring
  rw [sineQuartPair, e, integral_sub integral_sk_pow_four.1 integral_sk_pow_six.1,
    integral_sk_pow_four.2, integral_sk_pow_six.2]
  norm_num

/-- The non-adjacent triple term `∬ S(x)² S(y)² ρ₃(0, x, y)`. -/
def sineSquarePair : ℝ := ∫ x, ∫ y, sk x ^ 2 * sk y ^ 2 * rho₃ x y

theorem integrable_sk_sq_mul_one_sub :
    Integrable fun x => sk x ^ 2 * (1 - sk x ^ 2) := by
  have e : (fun x => sk x ^ 2 * (1 - sk x ^ 2)) = fun x => sk x ^ 2 - sk x ^ 4 :=
    funext fun x => by ring
  rw [e]; exact integral_sk_sq.1.sub integral_sk_pow_four.1

theorem sineSquarePair_eq : sineSquarePair = 1 / 15 := by
  have hin : ∀ x, ∫ y, sk x ^ 2 * sk y ^ 2 * rho₃ x y =
      sk x ^ 2 * (1 - sk x ^ 2) - 2 / 3 * sk x ^ 2 - sk x ^ 2 * sB x +
        2 * (sk x ^ 3 * sA x) := by
    intro x
    have e : (fun y => sk x ^ 2 * sk y ^ 2 * rho₃ x y) = fun y =>
        sk x ^ 2 * (1 - sk x ^ 2) * sk y ^ 2 - sk x ^ 2 * sk y ^ 4 -
          sk x ^ 2 * (sk (x - y) ^ 2 * sk y ^ 2) + 2 * sk x ^ 3 * (sk (x - y) * sk y ^ 3) :=
      funext fun y => by rw [rho₃_eq]; ring
    have h1 := integral_sk_sq.1
    have h2 := integral_sk_pow_four.1
    have h3 := integrable_sB_integrand x
    have h4 := integrable_sA_integrand x
    rw [e, integral_add ?_ (h4.const_mul _), integral_sub ?_ (h3.const_mul _),
      integral_sub (h1.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, integral_sk_sq.2, integral_sk_pow_four.2,
      show ∫ y, sk (x - y) ^ 2 * sk y ^ 2 = sB x from rfl,
      show ∫ y, sk (x - y) * sk y ^ 3 = sA x from rfl]
    · ring
    all_goals first
      | exact (h1.const_mul _).sub (h2.const_mul _)
      | exact ((h1.const_mul _).sub (h2.const_mul _)).sub (h3.const_mul _)
  have hp := integrable_sk_sq_mul_one_sub
  have hs := integral_sk_sq.1
  obtain ⟨hB, eB⟩ := integral_sk_sq_mul_sB
  obtain ⟨hA, eA⟩ := integral_sk_cube_mul_sA
  rw [sineSquarePair]
  simp_rw [hin]
  rw [integral_add ?_ (hA.const_mul _), integral_sub ?_ hB, integral_sub hp (hs.const_mul _),
    integral_const_mul, integral_const_mul, eA, eB, integral_sk_sq.2, ← sinePair, sinePair_eq]
  · norm_num
  · exact hp.sub (hs.const_mul _)
  · exact (hp.sub (hs.const_mul _)).sub hB

/-! ### Kernel bounds and modulated convolutions -/

theorem sk_eq_sinc (x : ℝ) : sk x = Real.sinc (Real.pi * x) := by
  by_cases hx : x = 0
  · simp [sk, hx]
  · rw [sk, if_neg hx, Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx)]

theorem continuous_sk : Continuous sk := by
  rw [show sk = fun x => Real.sinc (Real.pi * x) from funext sk_eq_sinc]
  exact Real.continuous_sinc.comp (continuous_const.mul continuous_id)

theorem abs_sk_le_one (x : ℝ) : |sk x| ≤ 1 := by
  rw [sk_eq_sinc]; exact Real.abs_sinc_le_one _

theorem sk_sq_le_one (x : ℝ) : sk x ^ 2 ≤ 1 := by
  have h := abs_sk_le_one x
  rw [← sq_abs]; nlinarith [abs_nonneg (sk x)]

/-- A Fourier-side profile bounded by `1` with `L¹` norm at most `1`. -/
def Nice (f : ℝ → ℂ) : Prop := Integrable f ∧ (∀ η, ‖f η‖ ≤ 1) ∧ ∫ η, ‖f η‖ ≤ 1

theorem nice_ind : Nice ind := by
  refine ⟨integrable_ind, norm_ind_le, le_of_eq ?_⟩
  have e : (fun η => ‖ind η‖) = (Set.Icc (-(1 / 2) : ℝ) (1 / 2)).indicator fun _ => (1 : ℝ) := by
    funext η; rw [ind_apply, Set.indicator_apply]; split_ifs <;> simp
  rw [e, integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc,
    smul_eq_mul, mul_one]
  norm_num

theorem nice_tri : Nice tri := by
  refine ⟨integrable_tri, norm_tri_le, le_of_eq ?_⟩
  simp_rw [tri_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (triR_nonneg _)]
  simpa using integral_triR_pow_succ 0

/-- The modulated convolution `h ⋆ (k e_x)`, whose transform is `𝓕h(y) 𝓕k(y − x)`. -/
def mcv (h k : ℝ → ℂ) (x : ℝ) : ℝ → ℂ := h ⋆[ContinuousLinearMap.mul ℂ ℂ] fun η => k η * ex x η

theorem integrable_mcv {h k : ℝ → ℂ} (hh : Nice h) (hk : Nice k) (x : ℝ) :
    Integrable (mcv h k x) :=
  hh.1.integrable_convolution _ (integrable_mul_ex hk.1 x)

theorem fourier_mcv {h k : ℝ → ℂ} (hh : Nice h) (hk : Nice k) (x y : ℝ) :
    𝓕 (mcv h k x) y = 𝓕 h y * 𝓕 k (y - x) := by
  rw [mcv, Real.fourier_mul_convolution_eq hh.1 (integrable_mul_ex hk.1 x), fourier_mul_ex]

theorem norm_mcv_le {h k : ℝ → ℂ} (hh : Nice h) (hk : Nice k) (x η : ℝ) : ‖mcv h k x η‖ ≤ 1 := by
  rw [mcv, convolution_def]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ t, ‖(ContinuousLinearMap.mul ℂ ℂ) (h t) (k (η - t) * ex x (η - t))‖
      ≤ ∫ t, ‖k (η - t)‖ := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun t => norm_nonneg _)
          (hk.1.norm.comp_sub_left η) (Filter.Eventually.of_forall fun t => ?_)
        show ‖(ContinuousLinearMap.mul ℂ ℂ) (h t) (k (η - t) * ex x (η - t))‖ ≤ ‖k (η - t)‖
        rw [ContinuousLinearMap.mul_apply', norm_mul, norm_mul, norm_ex, mul_one]
        exact mul_le_of_le_one_left (norm_nonneg _) (hh.2.1 t)
    _ = ∫ t, ‖k t‖ := integral_sub_left_eq_self (fun t => ‖k t‖) volume η
    _ ≤ 1 := hk.2.2

theorem memLp_two_mcv {h k : ℝ → ℂ} (hh : Nice h) (hk : Nice k) (x : ℝ) : MemLp (mcv h k x) 2 :=
  memLp_two_of_norm_le_one (integrable_mcv hh hk x) (norm_mcv_le hh hk x)

theorem integrable_mul_mcv {g h k : ℝ → ℂ} (hg : Nice g) (hh : Nice h) (hk : Nice k) (x : ℝ) :
    Integrable fun η => g η * mcv h k x η :=
  hg.1.mul_bdd (c := 1) (integrable_mcv hh hk x).aestronglyMeasurable
    (Filter.Eventually.of_forall (norm_mcv_le hh hk x))

theorem memLp_two_mul_mcv {g h k : ℝ → ℂ} (hg : Nice g) (hh : Nice h) (hk : Nice k) (x : ℝ) :
    MemLp (fun η => g η * mcv h k x η) 2 :=
  memLp_two_of_norm_le_one (integrable_mul_mcv hg hh hk x) fun η => by
    rw [norm_mul]; exact mul_le_one₀ (hg.2.1 η) (norm_nonneg _) (norm_mcv_le hh hk x η)

theorem fourier_mcv_ind_ind (x y : ℝ) : 𝓕 (mcv ind ind x) y = ((sk y * sk (x - y) : ℝ) : ℂ) := by
  rw [fourier_mcv nice_ind nice_ind, fourier_ind, fourier_ind, sk_sub_comm x y]; push_cast; rfl

theorem fourier_mcv_ind_tri (x y : ℝ) :
    𝓕 (mcv ind tri x) y = ((sk y * sk (x - y) ^ 2 : ℝ) : ℂ) := by
  rw [fourier_mcv nice_ind nice_tri, fourier_ind, fourier_tri', sk_sub_comm x y]; push_cast; rfl

theorem fourier_mcv_tri_ind (x y : ℝ) :
    𝓕 (mcv tri ind x) y = ((sk y ^ 2 * sk (x - y) : ℝ) : ℂ) := by
  rw [fourier_mcv nice_tri nice_ind, fourier_tri', fourier_ind, sk_sub_comm x y]; push_cast; rfl

/-! ### The three-point inner integrals -/

/-- `J₃(x, y) = ∫ S(y − z) S(z) S(x − z)² dz`. -/
def J3 (x y : ℝ) : ℝ := ∫ z, sk (y - z) * (sk z * sk (x - z) ^ 2)

/-- `J₅(x, y) = ∫ S(y − z) S(z)² S(x − z) dz`. -/
def J5 (x y : ℝ) : ℝ := ∫ z, sk (y - z) * (sk z ^ 2 * sk (x - z))

/-- `J₇(x, y) = ∫ S(y − z)² S(z) S(x − z) dz`. -/
def J7 (x y : ℝ) : ℝ := ∫ z, sk (y - z) ^ 2 * (sk z * sk (x - z))

theorem J3_pair (x y : ℝ) : Integrable (fun z => sk (y - z) * (sk z * sk (x - z) ^ 2)) ∧
    𝓕 (fun η => ind η * mcv ind tri x η) y = (J3 x y : ℂ) := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind y)
    (memLp_two_mul_ex memLp_two_ind y) (integrable_mcv nice_ind nice_tri x)
    (memLp_two_mcv nice_ind nice_tri x) (fourier_ind_mul_ex y) (fourier_mcv_ind_tri x)
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_ind] at he
  exact ⟨hi, by rw [J3, he]⟩

theorem J5_pair (x y : ℝ) : Integrable (fun z => sk (y - z) * (sk z ^ 2 * sk (x - z))) ∧
    𝓕 (fun η => ind η * mcv tri ind x η) y = (J5 x y : ℂ) := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind y)
    (memLp_two_mul_ex memLp_two_ind y) (integrable_mcv nice_tri nice_ind x)
    (memLp_two_mcv nice_tri nice_ind x) (fourier_ind_mul_ex y) (fourier_mcv_tri_ind x)
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_ind] at he
  exact ⟨hi, by rw [J5, he]⟩

theorem J7_pair (x y : ℝ) : Integrable (fun z => sk (y - z) ^ 2 * (sk z * sk (x - z))) ∧
    𝓕 (fun η => tri η * mcv ind ind x η) y = (J7 x y : ℂ) := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_tri y)
    (memLp_two_mul_ex memLp_two_tri y) (integrable_mcv nice_ind nice_ind x)
    (memLp_two_mcv nice_ind nice_ind x) (fourier_tri_mul_ex y) (fourier_mcv_ind_ind x)
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_tri] at he
  exact ⟨hi, by rw [J7, he]⟩

/-! ### Contracting a vertex of degree two -/

/-- `∫ S(x − y) S(y − z) dy = S(x − z)`. -/
theorem integral_sk_sub_mul_sk_sub (x z : ℝ) : ∫ y, sk (x - y) * sk (y - z) = sk (x - z) := by
  calc ∫ y, sk (x - y) * sk (y - z) = ∫ y, sk (x - z - (y - z)) * sk (y - z) := by
        congr 1; funext y; rw [show x - z - (y - z) = x - y by ring]
    _ = ∫ y, sk (x - z - y) * sk y := integral_sub_right_eq_self (fun y => sk (x - z - y) * sk y) z
    _ = sk (x - z) := (integral_sk_sub_mul_sk (x - z)).2

/-- `∫ S(x − y)² S(y − z)² dy = B(x − z)`. -/
theorem integral_sk_sub_sq_mul_sk_sub_sq (x z : ℝ) :
    ∫ y, sk (x - y) ^ 2 * sk (y - z) ^ 2 = sB (x - z) := by
  calc ∫ y, sk (x - y) ^ 2 * sk (y - z) ^ 2 = ∫ y, sk (x - z - (y - z)) ^ 2 * sk (y - z) ^ 2 := by
        congr 1; funext y; rw [show x - z - (y - z) = x - y by ring]
    _ = ∫ y, sk (x - z - y) ^ 2 * sk y ^ 2 :=
        integral_sub_right_eq_self (fun y => sk (x - z - y) ^ 2 * sk y ^ 2) z
    _ = sB (x - z) := rfl

/-- **Fubini contraction.** For kernels with integrable squares and an integrable weight `h`,
the middle integration can be done first:
`∫ k₁(x − y) ∫ k₂(y − z) h(z) dz dy = ∫ h(z) ∫ k₁(x − y) k₂(y − z) dy dz`. -/
theorem integral_contract {k₁ k₂ h : ℝ → ℝ} (hk₁ : Continuous k₁) (hk₂ : Continuous k₂)
    (hk₁2 : Integrable fun t => k₁ t ^ 2) (hk₂2 : Integrable fun t => k₂ t ^ 2)
    (hh : Integrable h) (x : ℝ) :
    Integrable (Function.uncurry fun y z => k₁ (x - y) * (k₂ (y - z) * h z))
      (volume.prod volume) ∧
    ∫ y, k₁ (x - y) * ∫ z, k₂ (y - z) * h z = ∫ z, h z * ∫ y, k₁ (x - y) * k₂ (y - z) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun y z => k₁ (x - y) * (k₂ (y - z) * h z))
      (volume.prod volume) :=
    ((hk₁.comp (continuous_const.sub continuous_fst)).aestronglyMeasurable).mul
      (((hk₂.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hh.aestronglyMeasurable.comp_snd)
  have I1 : Integrable (fun p : ℝ × ℝ => k₁ (x - p.1) ^ 2 * |h p.2|) (volume.prod volume) :=
    (hk₁2.comp_sub_left x).mul_prod hh.abs
  have I2 : Integrable (fun p : ℝ × ℝ => k₂ (p.1 - p.2) ^ 2 * |h p.2|) (volume.prod volume) := by
    have hq : Integrable (fun q : ℝ × ℝ => k₂ q.1 ^ 2 * |h q.2|) (volume.prod volume) :=
      hk₂2.mul_prod hh.abs
    exact ((measurePreserving_sub_prod volume volume).integrable_comp
      hq.aestronglyMeasurable).mpr hq
  have hint : Integrable (Function.uncurry fun y z => k₁ (x - y) * (k₂ (y - z) * h z))
      (volume.prod volume) := by
    refine ((I1.add I2).div_const 2).mono' hmeas (Filter.Eventually.of_forall fun p => ?_)
    obtain ⟨y, z⟩ := p
    show |k₁ (x - y) * (k₂ (y - z) * h z)| ≤ (k₁ (x - y) ^ 2 * |h z| + k₂ (y - z) ^ 2 * |h z|) / 2
    rw [abs_mul, abs_mul]
    have h0 := mul_nonneg (sq_nonneg (|k₁ (x - y)| - |k₂ (y - z)|)) (abs_nonneg (h z))
    rw [← sq_abs (k₁ _), ← sq_abs (k₂ _)]
    nlinarith
  refine ⟨hint, ?_⟩
  have e1 : ∀ y, k₁ (x - y) * ∫ z, k₂ (y - z) * h z = ∫ z, k₁ (x - y) * (k₂ (y - z) * h z) :=
    fun y => (integral_const_mul _ _).symm
  have e2 : ∀ z, ∫ y, k₁ (x - y) * (k₂ (y - z) * h z) = h z * ∫ y, k₁ (x - y) * k₂ (y - z) :=
    fun z => by rw [← integral_const_mul]; congr 1; funext y; ring
  simp_rw [e1]
  rw [integral_integral_swap hint]
  simp_rw [e2]

/-- A finite linear combination of integrable functions integrates termwise. -/
theorem integral_sum_smul {n : ℕ} (c : Fin n → ℝ) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) :
    Integrable (fun z => ∑ i, c i * f i z) ∧ ∫ z, ∑ i, c i * f i z = ∑ i, c i * ∫ z, f i z := by
  refine ⟨integrable_finsetSum _ fun i _ => (hf i).const_mul (c i), ?_⟩
  rw [integral_finsetSum _ fun i _ => (hf i).const_mul (c i)]
  simp_rw [integral_const_mul]

/-! ### Two-point integrals at the middle level -/

theorem fourier_quad_mul_ex (x y : ℝ) :
    𝓕 (fun η => quad η * ex x η) y = ((sk (x - y) ^ 3 : ℝ) : ℂ) := by
  rw [fourier_mul_ex, fourier_quad', sk_sub_comm x y]

/-- `∫ S(x − y) A(y) dy = A(x)`. -/
theorem sA_pair (x : ℝ) :
    Integrable (fun y => sk (x - y) * sA y) ∧ ∫ y, sk (x - y) * sA y = sA x := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) integrable_ind_mul_quad memLp_two_ind_mul_quad
    (fourier_ind_mul_ex x) fourier_ind_mul_quad
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_ind, ← mul_assoc, ind_mul_ind, fourier_ind_mul_quad] at he
  exact ⟨hi, by exact_mod_cast he⟩

/-- `U₁(x) = ∫ S(x − y)³ A(y) dy`. -/
def U1 (x : ℝ) : ℝ := ∫ y, sk (x - y) ^ 3 * sA y

/-- `U₂(x) = ∫ S(y) S(x − y) B(y) dy`. -/
def U2 (x : ℝ) : ℝ := ∫ y, sk y * sk (x - y) * sB y

/-- `U₃(x) = ∫ S(x − y)² B(y) dy`. -/
def U3 (x : ℝ) : ℝ := ∫ y, sk (x - y) ^ 2 * sB y

theorem U1_pair (x : ℝ) : Integrable (fun y => sk (x - y) ^ 3 * sA y) ∧
    𝓕 (fun η => ind η * quad η * quad η) x = (U1 x : ℂ) := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_quad x)
    (memLp_two_mul_ex memLp_two_quad x) integrable_ind_mul_quad memLp_two_ind_mul_quad
    (fourier_quad_mul_ex x) fourier_ind_mul_quad
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_quad] at he
  refine ⟨hi, ?_⟩
  rw [U1, he, show (fun η => ind η * quad η * quad η) = fun η => quad η * (ind η * quad η) from
    funext fun η => by ring]

theorem U3_pair (x : ℝ) : Integrable (fun y => sk (x - y) ^ 2 * sB y) ∧
    𝓕 (fun η => tri η * (tri η * tri η)) x = (U3 x : ℂ) := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mul_ex integrable_tri x)
    (memLp_two_mul_ex memLp_two_tri x) integrable_tri_mul_tri memLp_two_tri_mul_tri
    (fourier_tri_mul_ex x) fourier_tri_mul_tri
  rw [integral_conj_mul_ex] at he
  simp_rw [conj_tri] at he
  exact ⟨hi, by rw [U3, he]⟩

theorem integrable_U2_integrand (x : ℝ) : Integrable fun y => sk y * sk (x - y) * sB y :=
  (integral_mul_eq_of_fourier (integrable_mcv nice_ind nice_ind x)
    (memLp_two_mcv nice_ind nice_ind x) integrable_tri_mul_tri memLp_two_tri_mul_tri
    (fourier_mcv_ind_ind x) fourier_tri_mul_tri).1

/-- `K₁₃(x) = ∫ S(y)² S(x − y) J₃(x, y) dy`. -/
def K13 (x : ℝ) : ℝ := ∫ y, sk y ^ 2 * sk (x - y) * J3 x y

/-- `K₁₅(x) = ∫ S(y) S(x − y) J₇(x, y) dy`. -/
def K15 (x : ℝ) : ℝ := ∫ y, sk y * sk (x - y) * J7 x y

/-- `K₁₇(x) = ∫ S(y) S(x − y)² J₅(x, y) dy`. -/
def K17 (x : ℝ) : ℝ := ∫ y, sk y * sk (x - y) ^ 2 * J5 x y

theorem integrable_K13_integrand (x : ℝ) : Integrable fun y => sk y ^ 2 * sk (x - y) * J3 x y :=
  (integral_mul_eq_of_fourier (integrable_mcv nice_tri nice_ind x)
    (memLp_two_mcv nice_tri nice_ind x) (integrable_mul_mcv nice_ind nice_ind nice_tri x)
    (memLp_two_mul_mcv nice_ind nice_ind nice_tri x) (fourier_mcv_tri_ind x)
    fun y => (J3_pair x y).2).1

theorem integrable_K17_integrand (x : ℝ) : Integrable fun y => sk y * sk (x - y) ^ 2 * J5 x y :=
  (integral_mul_eq_of_fourier (integrable_mcv nice_ind nice_tri x)
    (memLp_two_mcv nice_ind nice_tri x) (integrable_mul_mcv nice_ind nice_tri nice_ind x)
    (memLp_two_mul_mcv nice_ind nice_tri nice_ind x) (fourier_mcv_ind_tri x)
    fun y => (J5_pair x y).2).1

theorem integrable_W6_integrand (x : ℝ) : Integrable fun y => sk (x - y) * J3 x y :=
  (integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) (integrable_mul_mcv nice_ind nice_ind nice_tri x)
    (memLp_two_mul_mcv nice_ind nice_ind nice_tri x) (fourier_ind_mul_ex x)
    fun y => (J3_pair x y).2).1

theorem integrable_W9_integrand (x : ℝ) : Integrable fun y => sk (x - y) * J5 x y :=
  (integral_mul_eq_of_fourier (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) (integrable_mul_mcv nice_ind nice_tri nice_ind x)
    (memLp_two_mul_mcv nice_ind nice_tri nice_ind x) (fourier_ind_mul_ex x)
    fun y => (J5_pair x y).2).1

theorem integrable_W11_integrand (x : ℝ) : Integrable fun y => sk (x - y) ^ 2 * J7 x y :=
  (integral_mul_eq_of_fourier (integrable_mul_ex integrable_tri x)
    (memLp_two_mul_ex memLp_two_tri x) (integrable_mul_mcv nice_tri nice_ind nice_ind x)
    (memLp_two_mul_mcv nice_tri nice_ind nice_ind x) (fourier_tri_mul_ex x)
    fun y => (J7_pair x y).2).1

theorem K15_pair (x : ℝ) : Integrable (fun y => sk y * sk (x - y) * J7 x y) ∧
    (K15 x : ℂ) = ∫ η, conj (mcv ind ind x η) * (tri η * mcv ind ind x η) := by
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier (integrable_mcv nice_ind nice_ind x)
    (memLp_two_mcv nice_ind nice_ind x) (integrable_mul_mcv nice_tri nice_ind nice_ind x)
    (memLp_two_mul_mcv nice_tri nice_ind nice_ind x) (fourier_mcv_ind_ind x)
    fun y => (J7_pair x y).2
  exact ⟨hi, by rw [K15, he]⟩

/-! ### Contracted middle integrals -/

theorem integrable_sk_mul_sk_sub_sq (x : ℝ) : Integrable fun z => sk z * sk (x - z) ^ 2 :=
  (integral_mul_eq_of_fourier integrable_ind memLp_two_ind (integrable_mul_ex integrable_tri x)
    (memLp_two_mul_ex memLp_two_tri x) fourier_ind (fourier_tri_mul_ex x)).1

theorem integrable_sk_sq_mul_sk_sub (x : ℝ) : Integrable fun z => sk z ^ 2 * sk (x - z) :=
  (integral_mul_eq_of_fourier integrable_tri memLp_two_tri (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) fourier_tri' (fourier_ind_mul_ex x)).1

theorem integrable_sk_mul_sk_sub (x : ℝ) : Integrable fun z => sk z * sk (x - z) :=
  (integral_mul_eq_of_fourier integrable_ind memLp_two_ind (integrable_mul_ex integrable_ind x)
    (memLp_two_mul_ex memLp_two_ind x) fourier_ind (fourier_ind_mul_ex x)).1

theorem integrable_sk_sq_sq : Integrable fun t => (sk t ^ 2) ^ 2 := by
  have e : (fun t => (sk t ^ 2) ^ 2) = fun t => sk t ^ 4 := funext fun t => by ring
  rw [e]; exact integral_sk_pow_four.1

/-- Contracting `y` in `∫ S(x − y) J₃(x, y) dy` leaves `A(x)`. -/
theorem integral_W6 (x : ℝ) : ∫ y, sk (x - y) * J3 x y = sA x := by
  have hc := (integral_contract continuous_sk continuous_sk integral_sk_sq.1 integral_sk_sq.1
    (integrable_sk_mul_sk_sub_sq x) x).2
  simp only [integral_sk_sub_mul_sk_sub] at hc
  rw [show (fun y => sk (x - y) * J3 x y) =
    fun y => sk (x - y) * ∫ z, sk (y - z) * (sk z * sk (x - z) ^ 2) from rfl, hc,
    ← (integral_sk_mul_sk_sub_cube x).2]
  congr 1; funext z; ring

/-- Contracting `y` in `∫ S(x − y) J₅(x, y) dy` leaves `B(x)`. -/
theorem integral_W9 (x : ℝ) : ∫ y, sk (x - y) * J5 x y = sB x := by
  have hc := (integral_contract continuous_sk continuous_sk integral_sk_sq.1 integral_sk_sq.1
    (integrable_sk_sq_mul_sk_sub x) x).2
  simp only [integral_sk_sub_mul_sk_sub] at hc
  rw [show (fun y => sk (x - y) * J5 x y) =
    fun y => sk (x - y) * ∫ z, sk (y - z) * (sk z ^ 2 * sk (x - z)) from rfl, hc, sB]
  congr 1; funext z; ring

/-- Contracting `y` in `∫ S(x − y)² J₇(x, y) dy` leaves `U₂(x)`. -/
theorem integral_W11 (x : ℝ) : ∫ y, sk (x - y) ^ 2 * J7 x y = U2 x := by
  have hc := (integral_contract (k₁ := fun t => sk t ^ 2) (k₂ := fun t => sk t ^ 2)
    (continuous_sk.pow 2) (continuous_sk.pow 2) integrable_sk_sq_sq integrable_sk_sq_sq
    (integrable_sk_mul_sk_sub x) x).2
  simp only [integral_sk_sub_sq_mul_sk_sub_sq] at hc
  rw [show (fun y => sk (x - y) ^ 2 * J7 x y) =
    fun y => sk (x - y) ^ 2 * ∫ z, sk (y - z) ^ 2 * (sk z * sk (x - z)) from rfl, hc, U2,
    ← integral_sub_left_eq_self (fun z => sk z * sk (x - z) * sB (x - z)) volume x]
  congr 1; funext z; simp only [sub_sub_cancel]; ring

/-- Outer contraction: `∫ S(x) U₂(x) dx = ∫ S² B = 1/2`. -/
theorem integral_sk_mul_U2 : Integrable (fun x => sk x * U2 x) ∧ ∫ x, sk x * U2 x = 1 / 2 := by
  have hg : Integrable fun y => sk y * sB y :=
    (integral_mul_eq_of_fourier integrable_ind memLp_two_ind integrable_tri_mul_tri
      memLp_two_tri_mul_tri fourier_ind fourier_tri_mul_tri).1
  obtain ⟨hint, hc⟩ := integral_contract continuous_sk continuous_sk integral_sk_sq.1
    integral_sk_sq.1 hg 0
  have e : ∀ x, sk x * U2 x = sk (0 - x) * ∫ y, sk (x - y) * (sk y * sB y) := fun x => by
    rw [U2, zero_sub, sk_neg, ← integral_const_mul, ← integral_const_mul]
    congr 1; funext y; ring
  simp only [integral_sk_sub_mul_sk_sub] at hc
  simp only [zero_sub, sk_neg] at hc
  refine ⟨?_, ?_⟩
  · refine hint.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [e, integral_const_mul]
  · simp_rw [e]
    simp only [zero_sub, sk_neg]
    rw [hc, ← integral_sk_sq_mul_sB.2]
    congr 1; funext y; ring

/-! ### Two-point integrals at the outer level -/

theorem integral_sk_mul_U1 : Integrable (fun x => sk x * U1 x) ∧ ∫ x, sk x * U1 x = 9 / 20 := by
  have hG : Integrable fun η => ind η * quad η * quad η :=
    integrable_ind_mul_quad.mul_bdd (c := 1) integrable_quad.aestronglyMeasurable
      (Filter.Eventually.of_forall norm_quad_le)
  have hG2 : MemLp (fun η => ind η * quad η * quad η) 2 :=
    memLp_two_of_norm_le_one hG fun η => by
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (mul_le_one₀ (norm_ind_le η) (norm_nonneg _) (norm_quad_le η))
        (norm_nonneg _) (norm_quad_le η)
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_ind memLp_two_ind hG hG2 fourier_ind
    fun x => (U1_pair x).2
  simp_rw [conj_ind] at he
  rw [show (fun η => ind η * (ind η * quad η * quad η)) = fun η => ind η * quad η ^ 2 from
    funext fun η => by rw [← mul_assoc, ← mul_assoc, ind_mul_ind]; ring,
    integral_ind_mul_quad_sq] at he
  exact ⟨hi, by exact_mod_cast he⟩

theorem integral_sk_sq_mul_U3 :
    Integrable (fun x => sk x ^ 2 * U3 x) ∧ ∫ x, sk x ^ 2 * U3 x = 2 / 5 := by
  have hG : Integrable fun η => tri η * (tri η * tri η) :=
    integrable_tri.mul_bdd (c := 1) integrable_tri_mul_tri.aestronglyMeasurable
      (Filter.Eventually.of_forall fun η => by
        rw [norm_mul]; exact mul_le_one₀ (norm_tri_le η) (norm_nonneg _) (norm_tri_le η))
  have hG2 : MemLp (fun η => tri η * (tri η * tri η)) 2 :=
    memLp_two_of_norm_le_one hG fun η => by
      rw [norm_mul, norm_mul]
      exact mul_le_one₀ (norm_tri_le η) (by positivity)
        (mul_le_one₀ (norm_tri_le η) (norm_nonneg _) (norm_tri_le η))
  obtain ⟨hi, he⟩ := integral_mul_eq_of_fourier integrable_tri memLp_two_tri hG hG2 fourier_tri'
    fun x => (U3_pair x).2
  simp_rw [conj_tri, show ∀ η, tri η * (tri η * (tri η * tri η)) = tri η ^ (3 + 1) from
    fun η => by ring, integral_tri_pow_succ 3] at he
  refine ⟨hi, ?_⟩
  rw [Complex.ofReal_inj.mp he]; norm_num

/-! ### The complete-graph term through `|P_x|²`

`P_x = 1 ⋆ (1 e_x)` is, for `|η| ≤ 1`, a phase times the transform of the centred indicator of
width `L = (1 − |η|)₊`, so `|P_x(η)|² = (L S(Lx))²`; scaled Parseval then gives
`∫ S(x)² (L S(Lx))² dx = ∫ Δ(u)(L − |u|)₊ du = L² − L³/3`. -/

/-- The centred indicator `1_{[−a, a]}`. -/
def cind (a : ℝ) : ℝ → ℂ := (centralInterval a).indicator fun _ => 1

theorem cind_apply (a η : ℝ) : cind a η = if η ∈ Set.Icc (-a) a then 1 else 0 := by
  simp only [cind, centralInterval, Set.indicator_apply]

theorem fourier_cind {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    𝓕 (cind a) x = ((2 * a * sk (2 * a * x) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le ha with rfl | ha
  · rw [Real.fourier_real_eq_integral_exp_smul]
    have e : (fun v : ℝ => Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) • cind 0 v) =
        (Set.Icc (0 : ℝ) 0).indicator
          fun v => Complex.exp (↑(-2 * Real.pi * v * x) * Complex.I) := by
      funext v; rw [cind_apply, Set.indicator_apply, neg_zero]; split_ifs <;> simp
    rw [e, integral_indicator measurableSet_Icc,
      setIntegral_measure_zero _ (by simp [Real.volume_Icc])]
    simp
  · by_cases hx : x = 0
    · subst hx
      have h0 : 𝓕 (cind a) 0 = ∫ v, cind a v := by
        rw [Real.fourier_real_eq_integral_exp_smul]
        congr 1; funext v; simp
      rw [h0, cind, integral_indicator (measurableSet_centralInterval _), centralInterval,
        setIntegral_const, Real.volume_real_Icc, mul_zero, sk_zero, mul_one,
        max_eq_left (by linarith), Complex.real_smul, mul_one]
      push_cast; ring
    · rw [cind, fourierIntegral_centralIndicator ha hx, sk,
        if_neg (mul_ne_zero (by positivity) hx)]
      congr 1
      field_simp

/-- `1_{[−a,a]} ⋆ 1_{[−a,a]} = (2a − |u|)₊`. -/
theorem cind_conv_apply {a : ℝ} (ha : 0 ≤ a) (u : ℝ) :
    (cind a ⋆[ContinuousLinearMap.mul ℂ ℂ] cind a) u = ((max (2 * a - |u|) 0 : ℝ) : ℂ) := by
  set lo : ℝ := max (-a) (u - a)
  set hi : ℝ := min a (u + a)
  have key : ∀ t : ℝ, (t ∈ Set.Icc (-a) a ∧ u - t ∈ Set.Icc (-a) a) ↔ t ∈ Set.Icc lo hi :=
    fun t => by
      simp only [Set.mem_Icc, lo, hi, max_le_iff, le_min_iff]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, by linarith⟩, h2, by linarith⟩
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨h1, h3⟩, by linarith, by linarith⟩
  have hpt : (fun t => (ContinuousLinearMap.mul ℂ ℂ) (cind a t) (cind a (u - t))) =
      (Set.Icc lo hi).indicator fun _ => (1 : ℂ) := by
    funext t
    rw [ContinuousLinearMap.mul_apply', cind_apply, cind_apply, Set.indicator_apply]
    by_cases hm : t ∈ Set.Icc lo hi
    · obtain ⟨h1, h2⟩ := (key t).mpr hm
      rw [if_pos h1, if_pos h2, if_pos hm, one_mul]
    · rw [if_neg hm]
      by_cases h1 : t ∈ Set.Icc (-a) a
      · rw [if_pos h1, if_neg (fun h2 => hm ((key t).mp ⟨h1, h2⟩)), mul_zero]
      · rw [if_neg h1, zero_mul]
  rw [convolution_def, hpt, integral_indicator measurableSet_Icc, setIntegral_const,
    Real.volume_real_Icc, Complex.real_smul, mul_one]
  congr 1
  rcases le_or_gt 0 u with hu | hu
  · rw [abs_of_nonneg hu]
    rcases le_total u (2 * a) with h2 | h2
    · have hl : lo = u - a := max_eq_right (by linarith)
      have hh : hi = a := min_eq_left (by linarith)
      rw [hl, hh]; ring_nf
    · rw [max_eq_right (by linarith), max_eq_right]
      linarith [min_le_left a (u + a), le_max_right (-a) (u - a)]
  · rw [abs_of_neg hu]
    rcases le_total (-(2 * a)) u with h2 | h2
    · have hl : lo = -a := max_eq_left (by linarith)
      have hh : hi = u + a := min_eq_right (by linarith)
      rw [hl, hh]; ring_nf
    · rw [max_eq_right (by linarith), max_eq_right]
      linarith [min_le_right a (u + a), le_max_left (-a) (u - a)]

/-- `∫ (1 − |u|)₊ (L − |u|)₊ du = L² − L³/3` for `0 ≤ L ≤ 1`. -/
theorem integral_triR_mul_ramp {L : ℝ} (h0 : 0 ≤ L) (h1 : L ≤ 1) :
    ∫ u, triR u * max (L - |u|) 0 = L ^ 2 - L ^ 3 / 3 := by
  have h := integral_comp_abs (f := fun s => max (1 - s) 0 * max (L - s) 0)
  have e : (fun u : ℝ => triR u * max (L - |u|) 0) =
      fun u => max (1 - |u|) 0 * max (L - |u|) 0 := rfl
  rw [e, h]
  have hcont : Continuous fun s : ℝ => max (1 - s) 0 * max (L - s) 0 := by fun_prop
  have hz : ∀ s ∈ Set.Ioi L, max (1 - s) 0 * max (L - s) 0 = 0 := fun s hs => by
    rw [max_eq_right (a := L - s) (by linarith [Set.mem_Ioi.mp hs]), mul_zero]
  have hU : Set.Ioi (0 : ℝ) = Set.Ioc 0 L ∪ Set.Ioi L := (Set.Ioc_union_Ioi_eq_Ioi h0).symm
  rw [hU, setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
    (integrableOn_zero.congr_fun (fun s hs => (hz s hs).symm) measurableSet_Ioi),
    setIntegral_eq_zero_of_forall_eq_zero hz, add_zero, ← intervalIntegral.integral_of_le h0,
    intervalIntegral.integral_congr (g := fun s => L + -(1 + L) * s + s ^ 2) fun s hs => ?_]
  · rw [intervalIntegral.integral_add
      ((by fun_prop : Continuous fun s : ℝ => L + -(1 + L) * s).intervalIntegrable _ _)
      ((continuous_pow 2).intervalIntegrable _ _), intervalIntegral_lin, integral_pow]
    ring
  · rw [Set.uIcc_of_le h0] at hs
    show max (1 - s) 0 * max (L - s) 0 = _
    rw [max_eq_left (by linarith [hs.2]), max_eq_left (by linarith [hs.2])]
    ring

/-- **Scaled Parseval**: `∫ S(x)² (L S(Lx))² dx = L² − L³/3` for `0 ≤ L ≤ 1`. -/
theorem integral_sk_sq_mul_scaled {L : ℝ} (h0 : 0 ≤ L) (h1 : L ≤ 1) :
    ∫ x, sk x ^ 2 * (L * sk (L * x)) ^ 2 = L ^ 2 - L ^ 3 / 3 := by
  have hc1 : Integrable (cind (L / 2)) := integrable_centralIndicator (L / 2)
  have hG1 : Integrable (cind (L / 2) ⋆[ContinuousLinearMap.mul ℂ ℂ] cind (L / 2)) :=
    hc1.integrable_convolution _ hc1
  have hGv : ∀ u, (cind (L / 2) ⋆[ContinuousLinearMap.mul ℂ ℂ] cind (L / 2)) u =
      ((max (L - |u|) 0 : ℝ) : ℂ) := fun u => by
    rw [cind_conv_apply (by linarith), show 2 * (L / 2) = L by ring]
  have hG2 : MemLp (cind (L / 2) ⋆[ContinuousLinearMap.mul ℂ ℂ] cind (L / 2)) 2 :=
    memLp_two_of_norm_le_one hG1 fun u => by
      rw [hGv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact max_le (by linarith [abs_nonneg u]) zero_le_one
  have hg : ∀ x, 𝓕 (cind (L / 2) ⋆[ContinuousLinearMap.mul ℂ ℂ] cind (L / 2)) x =
      (((L * sk (L * x)) ^ 2 : ℝ) : ℂ) := fun x => by
    rw [Real.fourier_mul_convolution_eq hc1 hc1, fourier_cind (by linarith),
      show 2 * (L / 2) = L by ring]
    push_cast; ring
  obtain ⟨-, he⟩ := integral_mul_eq_of_fourier integrable_tri memLp_two_tri hG1 hG2 fourier_tri' hg
  simp_rw [conj_tri, tri_apply, hGv, ← Complex.ofReal_mul, integral_complex_ofReal] at he
  rw [Complex.ofReal_inj.mp he, integral_triR_mul_ramp h0 h1]

theorem mem_ind_ind_iff {η : ℝ} (hη : |η| ≤ 1) (t : ℝ) :
    (t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) ∧ η - t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) ↔
      t - η / 2 ∈ Set.Icc (-(triR η / 2)) (triR η / 2) := by
  rw [triR, max_eq_left (by linarith)]
  simp only [Set.mem_Icc]
  rcases le_total 0 η with h | h
  · rw [abs_of_nonneg h]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · rw [abs_of_nonpos h]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- For `|η| ≤ 1`, `P_x(η) = e_x(η/2) · 𝓕 1_{[−L/2, L/2]}(x)` with `L = 1 − |η|`. -/
theorem mcv_ind_ind_eq (x : ℝ) {η : ℝ} (hη : |η| ≤ 1) :
    mcv ind ind x η = ex x (η / 2) * 𝓕 (cind (triR η / 2)) x := by
  have hpt : ∀ t, (ContinuousLinearMap.mul ℂ ℂ) (ind t) (ind (η - t) * ex x (η - t)) =
      ex x (η / 2) * (Complex.exp (↑(-2 * Real.pi * (t - η / 2) * x) * Complex.I) •
        cind (triR η / 2) (t - η / 2)) := fun t => by
    rw [ContinuousLinearMap.mul_apply', ind_apply, ind_apply, cind_apply, smul_eq_mul]
    have hex : ex x (η - t) =
        ex x (η / 2) * Complex.exp (↑(-2 * Real.pi * (t - η / 2) * x) * Complex.I) := by
      rw [ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring
    by_cases hm : t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) ∧ η - t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
    · rw [if_pos hm.1, if_pos hm.2, if_pos ((mem_ind_ind_iff hη t).mp hm), hex]; ring
    · rw [if_neg fun h' => hm ((mem_ind_ind_iff hη t).mpr h')]
      by_cases h1 : t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)
      · rw [if_pos h1, if_neg fun h2 => hm ⟨h1, h2⟩]; ring
      · rw [if_neg h1]; ring
  rw [mcv, convolution_def]
  show ∫ t, (ContinuousLinearMap.mul ℂ ℂ) (ind t) (ind (η - t) * ex x (η - t)) = _
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub_right_eq_self
    (fun s => Complex.exp (↑(-2 * Real.pi * s * x) * Complex.I) • cind (triR η / 2) s) (η / 2),
    Real.fourier_real_eq_integral_exp_smul]
  congr 2; funext s; congr 3; ring

/-- `|P_x(η)| = |L S(Lx)|` with `L = (1 − |η|)₊`. -/
theorem norm_mcv_ind_ind (x η : ℝ) : ‖mcv ind ind x η‖ = |triR η * sk (triR η * x)| := by
  by_cases hη : |η| ≤ 1
  · rw [mcv_ind_ind_eq x hη, norm_mul, norm_ex, one_mul, fourier_cind (by linarith [triR_nonneg η]),
      Complex.norm_real, Real.norm_eq_abs, show 2 * (triR η / 2) = triR η by ring]
  · have hL : triR η = 0 := max_eq_right (by linarith [not_le.mp hη])
    have h0 : mcv ind ind x η = 0 := by
      rw [mcv, convolution_def]
      refine (integral_congr_ae (g := fun _ => (0 : ℂ))
        (Filter.Eventually.of_forall fun t => ?_)).trans integral_zero
      show (ContinuousLinearMap.mul ℂ ℂ) (ind t) (ind (η - t) * ex x (η - t)) = 0
      rw [ContinuousLinearMap.mul_apply', ind_apply, ind_apply]
      split_ifs with h1 h2
      · exfalso; apply hη; rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
      all_goals simp
    rw [h0, hL]; simp

/-- `K₁₅(x) = ∫ Δ(η) (L S(Lx))² dη` with `L = Δ(η)`. -/
theorem K15_eq (x : ℝ) : K15 x = ∫ η, triR η * (triR η * sk (triR η * x)) ^ 2 := by
  have h := (K15_pair x).2
  have e : (fun η => conj (mcv ind ind x η) * (tri η * mcv ind ind x η)) =
      fun η => ((triR η * (triR η * sk (triR η * x)) ^ 2 : ℝ) : ℂ) := by
    funext η
    rw [show conj (mcv ind ind x η) * (tri η * mcv ind ind x η) =
      tri η * (conj (mcv ind ind x η) * mcv ind ind x η) by ring, Complex.conj_mul',
      norm_mcv_ind_ind, sq_abs, tri_apply]
    push_cast; ring
  rw [e, integral_complex_ofReal] at h
  exact_mod_cast h

theorem integrable_triR_pow (k : ℕ) : Integrable fun η => triR η ^ (k + 1) := by
  by_contra hni
  have h := integral_triR_pow_succ k
  rw [integral_undef hni] at h
  have : (0 : ℝ) < 2 / (k + 2) := by positivity
  linarith

/-- **The complete-graph integral**: `∫ S(x)² K₁₅(x) dx = ∫ (Δ³ − Δ⁴/3) = 11/30`. -/
theorem integral_sk_sq_mul_K15 :
    Integrable (fun x => sk x ^ 2 * K15 x) ∧ ∫ x, sk x ^ 2 * K15 x = 11 / 30 := by
  have hF : Integrable (Function.uncurry fun x η =>
      sk x ^ 2 * (triR η * (triR η * sk (triR η * x)) ^ 2)) (volume.prod volume) := by
    refine (integral_sk_sq.1.mul_prod (integrable_triR_pow 0)).mono' ?_
      (Filter.Eventually.of_forall fun p => ?_)
    · exact (((continuous_sk.comp continuous_fst).pow 2).mul
        ((continuous_triR.comp continuous_snd).mul (((continuous_triR.comp continuous_snd).mul
          (continuous_sk.comp ((continuous_triR.comp continuous_snd).mul
            continuous_fst))).pow 2))).aestronglyMeasurable
    · obtain ⟨x, η⟩ := p
      show |sk x ^ 2 * (triR η * (triR η * sk (triR η * x)) ^ 2)| ≤ sk x ^ 2 * triR η ^ (0 + 1)
      have hq : (triR η * sk (triR η * x)) ^ 2 ≤ 1 := by
        rw [mul_pow]
        exact mul_le_one₀ (pow_le_one₀ (triR_nonneg η) (triR_le_one η)) (sq_nonneg _)
          (sk_sq_le_one _)
      rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) (mul_nonneg (triR_nonneg η) (sq_nonneg _))),
        zero_add, pow_one]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_right (triR_nonneg η) hq) (sq_nonneg _)
  have hK : ∀ x, sk x ^ 2 * K15 x =
      ∫ η, sk x ^ 2 * (triR η * (triR η * sk (triR η * x)) ^ 2) := fun x => by
    rw [K15_eq, integral_const_mul]
  refine ⟨hF.integral_prod_left.congr (Filter.Eventually.of_forall fun x => (hK x).symm), ?_⟩
  simp_rw [hK]
  rw [integral_integral_swap hF]
  have hin : ∀ η, ∫ x, sk x ^ 2 * (triR η * (triR η * sk (triR η * x)) ^ 2) =
      triR η ^ (2 + 1) - 1 / 3 * triR η ^ (3 + 1) := fun η => by
    rw [show triR η ^ (2 + 1) - 1 / 3 * triR η ^ (3 + 1) =
      triR η * (triR η ^ 2 - triR η ^ 3 / 3) by ring,
      ← integral_sk_sq_mul_scaled (triR_nonneg η) (triR_le_one η), ← integral_const_mul]
    congr 1; funext x; ring
  simp_rw [hin]
  rw [integral_sub (integrable_triR_pow 2) ((integrable_triR_pow 3).const_mul _),
    integral_const_mul, integral_triR_pow_succ, integral_triR_pow_succ]
  norm_num

/-! ### The other two complete-graph terms -/

theorem abs_J3_le (x y : ℝ) : |J3 x y| ≤ 1 := by
  rw [J3]
  refine (abs_integral_le_integral_abs).trans ?_
  have hb : Integrable fun z => (sk (y - z) ^ 2 + sk z ^ 2) / 2 :=
    ((integral_sk_sq.1.comp_sub_left y).add integral_sk_sq.1).div_const 2
  calc ∫ z, |sk (y - z) * (sk z * sk (x - z) ^ 2)| ≤ ∫ z, (sk (y - z) ^ 2 + sk z ^ 2) / 2 :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => abs_nonneg _) hb
          (Filter.Eventually.of_forall fun z => ?_)
    _ = 1 := by
        rw [integral_div, integral_add (integral_sk_sq.1.comp_sub_left y) integral_sk_sq.1,
          integral_sub_left_eq_self (fun z => sk z ^ 2) volume y, integral_sk_sq.2]
        norm_num
  have hc : |sk (x - z)| ^ 2 ≤ 1 := by
    nlinarith [abs_sk_le_one (x - z), abs_nonneg (sk (x - z))]
  have hab : |sk (y - z)| * |sk z| ≤ (sk (y - z) ^ 2 + sk z ^ 2) / 2 := by
    nlinarith [sq_nonneg (|sk (y - z)| - |sk z|), sq_abs (sk (y - z)), sq_abs (sk z)]
  calc |sk (y - z) * (sk z * sk (x - z) ^ 2)| = |sk (y - z)| * |sk z| * |sk (x - z)| ^ 2 := by
        rw [abs_mul, abs_mul, abs_pow]; ring
    _ ≤ |sk (y - z)| * |sk z| * 1 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ _ := by rw [mul_one]; exact hab

theorem stronglyMeasurable_J3 : StronglyMeasurable fun p : ℝ × ℝ => J3 p.1 p.2 := by
  have hf : StronglyMeasurable fun q : (ℝ × ℝ) × ℝ =>
      sk (q.1.2 - q.2) * (sk q.2 * sk (q.1.1 - q.2) ^ 2) :=
    ((continuous_sk.comp ((continuous_snd.comp continuous_fst).sub continuous_snd)).mul
      ((continuous_sk.comp continuous_snd).mul ((continuous_sk.comp
        ((continuous_fst.comp continuous_fst).sub continuous_snd)).pow 2))).stronglyMeasurable
  exact hf.integral_prod_right'

/-- **Swapping the two outer variables** turns the `{0y, xz}` complete-graph term into the
`{0x, yz}` one. -/
theorem integral_sk_mul_K13 :
    Integrable (fun x => sk x * K13 x) ∧ ∫ x, sk x * K13 x = ∫ x, sk x ^ 2 * K15 x := by
  have I1 : Integrable (fun p : ℝ × ℝ => sk p.1 ^ 2 * sk p.2 ^ 2) (volume.prod volume) :=
    integral_sk_sq.1.mul_prod integral_sk_sq.1
  have I2 : Integrable (fun p : ℝ × ℝ => sk (p.1 - p.2) ^ 2 * sk p.2 ^ 2) (volume.prod volume) :=
    ((measurePreserving_sub_prod volume volume).integrable_comp I1.aestronglyMeasurable).mpr I1
  have hG : Integrable (Function.uncurry fun x y => sk x * (sk y ^ 2 * sk (x - y) * J3 x y))
      (volume.prod volume) := by
    refine ((I1.add I2).div_const 2).mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact ((continuous_sk.comp continuous_fst).aestronglyMeasurable).mul
        ((((continuous_sk.comp continuous_snd).pow 2).mul
          (continuous_sk.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable.mul
          stronglyMeasurable_J3.aestronglyMeasurable)
    · obtain ⟨x, y⟩ := p
      show |sk x * (sk y ^ 2 * sk (x - y) * J3 x y)| ≤
        (sk x ^ 2 * sk y ^ 2 + sk (x - y) ^ 2 * sk y ^ 2) / 2
      have hJ := abs_J3_le x y
      have h1 : |sk x| * |sk (x - y)| ≤ (sk x ^ 2 + sk (x - y) ^ 2) / 2 := by
        nlinarith [sq_nonneg (|sk x| - |sk (x - y)|), sq_abs (sk x), sq_abs (sk (x - y))]
      rw [abs_mul, abs_mul, abs_mul, abs_pow]
      calc |sk x| * (|sk y| ^ 2 * |sk (x - y)| * |J3 x y|)
          ≤ |sk x| * (|sk y| ^ 2 * |sk (x - y)| * 1) := by gcongr
        _ = (|sk x| * |sk (x - y)|) * sk y ^ 2 := by rw [sq_abs]; ring
        _ ≤ (sk x ^ 2 + sk (x - y) ^ 2) / 2 * sk y ^ 2 :=
            mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = _ := by ring
  have hJ : ∀ x y, J3 x y = J7 y x := fun x y => by rw [J3, J7]; congr 1; funext z; ring
  refine ⟨hG.integral_prod_left.congr (Filter.Eventually.of_forall fun x => ?_), ?_⟩
  · show ∫ y, sk x * (sk y ^ 2 * sk (x - y) * J3 x y) = sk x * K13 x
    rw [K13, integral_const_mul]
  · calc ∫ x, sk x * K13 x = ∫ x, ∫ y, sk x * (sk y ^ 2 * sk (x - y) * J3 x y) := by
          congr 1; funext x; rw [K13, integral_const_mul]
      _ = ∫ y, ∫ x, sk x * (sk y ^ 2 * sk (x - y) * J3 x y) := integral_integral_swap hG
      _ = ∫ x, sk x ^ 2 * K15 x := by
          congr 1; funext y; rw [K15, ← integral_const_mul]
          congr 1; funext x; rw [hJ x y, sk_sub_comm x y]; ring

theorem J3_eq_J5 (x y : ℝ) : J3 x y = J5 x (x - y) := by
  rw [J3, ← integral_sub_left_eq_self (fun z => sk (y - z) * (sk z * sk (x - z) ^ 2)) volume x, J5]
  congr 1; funext z
  simp only [sub_sub_cancel]
  rw [show y - (x - z) = -(x - y - z) by ring, sk_neg]; ring

/-- The `{0z, xy}` and `{0y, xz}` terms agree: substitute `z ↦ x − z`, then `y ↦ x − y`. -/
theorem K13_eq_K17 (x : ℝ) : K13 x = K17 x := by
  rw [K13, K17]
  simp_rw [J3_eq_J5]
  rw [← integral_sub_left_eq_self (fun y => sk y ^ 2 * sk (x - y) * J5 x (x - y)) volume x]
  congr 1; funext y; simp only [sub_sub_cancel]; ring

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SineKernel
