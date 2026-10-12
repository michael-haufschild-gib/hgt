import GaloisForLFunctions.RHTower.XiGaussianHeatTestPhysicalSide
import GaloisForLFunctions.HTGeometry.GaussianPolynomialScaledTails

/-!
# The physical heat test of a real polynomial

For `a > 0` and a real polynomial `P` of degree `n`, the physical heat test
`g = (2πa)^{-1/2} Σ_k p_k (−1)^k ∂^{2k} e^{-x²/(2a)}` is a real even polynomial–Gaussian
`g(x) = Q(x) e^{-x²/(2a)}` with `deg Q ≤ 2n` (`heatPhysical_map_eq`, `natDegree_heatPolyR_le`,
`heatPolyR_comp_neg`).  Its Fourier–Laplace transform is `G(z) = e^{-az²/2} P(z²)`, and the heat
Hankel form is the zero sum of squares `H_a(P, P) = Σ_q G(z_q)²` (`heatHankel_map_eq_tsum_sq`).

**Strip bounds.**  For `|Im z| ≤ ½` and `f` with `|f| e^{|x|/2}` integrable,
`|∫ f e^{ixz}| ≤ ∫ |f| e^{|x|/2}` (`norm_heatStripTransform_le`).  If moreover `f` is
differentiable with derivative `f'` of the same kind, integration by parts gives
`|z| |∫ f e^{ixz}| ≤ ∫ |f'| e^{|x|/2}` (`norm_mul_norm_heatStripTransform_le`), and twice
`|z|² |∫ f e^{ixz}| ≤ ∫ |f''| e^{|x|/2}` (`sq_norm_mul_norm_heatStripTransform_le`).
-/

open scoped Real
open Complex Polynomial MeasureTheory
open GaloisForLFunctions (gaussPolyFun gaussPolyDerivPoly continuous_gaussPolyFun
  hasDerivAt_gaussPolyFun)

namespace RHTower

noncomputable section

/-! ## The real form -/

/-- The real polynomial factor of the `m`-th derivative of `e^{-bx²}`. -/
def gaussDerivPolyR (b : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | m + 1 => derivative (gaussDerivPolyR b m) - C (2 * b) * X * gaussDerivPolyR b m

theorem gaussDerivPoly_eq_map (b : ℝ) (m : ℕ) :
    gaussDerivPoly b m = (gaussDerivPolyR b m).map (algebraMap ℝ ℂ) := by
  induction m with
  | zero => simp [gaussDerivPoly, gaussDerivPolyR]
  | succ m ih =>
    rw [gaussDerivPoly, gaussDerivPolyR, ih, Polynomial.map_sub, Polynomial.derivative_map,
      Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X]
    congr 3
    simp

theorem natDegree_gaussDerivPolyR_le (b : ℝ) (m : ℕ) : (gaussDerivPolyR b m).natDegree ≤ m := by
  induction m with
  | zero => simp [gaussDerivPolyR]
  | succ m ih =>
    rw [gaussDerivPolyR]
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · exact (natDegree_derivative_le _).trans (by omega)
    · refine natDegree_mul_le.trans ?_
      have h1 : (C (2 * b) * X : ℝ[X]).natDegree ≤ 1 :=
        (natDegree_C_mul_le _ _).trans natDegree_X_le
      omega

theorem gaussDerivPolyR_comp_neg (b : ℝ) (m : ℕ) :
    (gaussDerivPolyR b m).comp (-X) = C ((-1) ^ m) * gaussDerivPolyR b m := by
  induction m with
  | zero => simp [gaussDerivPolyR]
  | succ m ih =>
    have hd : (derivative (gaussDerivPolyR b m)).comp (-X) =
        -(C ((-1) ^ m) * derivative (gaussDerivPolyR b m)) := by
      have h := derivative_comp (gaussDerivPolyR b m) (-X)
      rw [ih, derivative_C_mul, derivative_neg, derivative_X] at h
      linear_combination h
    have hc : C ((-1 : ℝ) ^ (m + 1)) = -C ((-1) ^ m) := by
      rw [pow_succ, C_mul]
      simp
    rw [gaussDerivPolyR, sub_comp, hd, mul_comp, mul_comp, C_comp, X_comp, ih, hc]
    ring

theorem gaussDerivPolyR_two_mul_comp_neg (b : ℝ) (k : ℕ) :
    (gaussDerivPolyR b (2 * k)).comp (-X) = gaussDerivPolyR b (2 * k) := by
  rw [gaussDerivPolyR_comp_neg, pow_mul]
  simp

/-- The real polynomial factor of the physical heat test. -/
def heatPolyR (a : ℝ) (P : ℝ[X]) : ℝ[X] :=
  C ((2 * π * a) ^ (-(1 / 2 : ℝ))) * ∑ k ∈ Finset.range (P.natDegree + 1),
    C (P.coeff k * (-1) ^ k) * gaussDerivPolyR (1 / (2 * a)) (2 * k)

theorem natDegree_heatPolyR_le (a : ℝ) (P : ℝ[X]) :
    (heatPolyR a P).natDegree ≤ 2 * P.natDegree := by
  refine (natDegree_C_mul_le _ _).trans (natDegree_sum_le_of_forall_le _ _ fun k hk => ?_)
  refine (natDegree_C_mul_le _ _).trans ((natDegree_gaussDerivPolyR_le _ _).trans ?_)
  have := Finset.mem_range.1 hk
  omega

theorem heatPolyR_comp_neg (a : ℝ) (P : ℝ[X]) : (heatPolyR a P).comp (-X) = heatPolyR a P := by
  rw [heatPolyR, mul_comp, C_comp, sum_comp]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_comp, C_comp, gaussDerivPolyR_two_mul_comp_neg]

theorem eval_map_ofReal (Q : ℝ[X]) (x : ℝ) :
    (Q.map (algebraMap ℝ ℂ)).eval (x : ℂ) = ((Q.eval x : ℝ) : ℂ) := by
  rw [eval_map, ← Complex.coe_algebraMap, eval₂_at_apply]

theorem gaussDeriv_eq_ofReal (b : ℝ) (m : ℕ) (x : ℝ) :
    gaussDeriv b m x = (((gaussDerivPolyR b m).eval x * Real.exp (-(b * x ^ 2)) : ℝ) : ℂ) := by
  rw [gaussDeriv, gaussDerivPoly_eq_map, eval_map_ofReal]
  push_cast
  ring_nf

/-- **The physical heat test of a real polynomial is the real polynomial–Gaussian
`Q(x) e^{-x²/(2a)}`.** -/
theorem heatPhysical_map_eq {a : ℝ} (ha : 0 < a) (P : ℝ[X]) (x : ℝ) :
    heatPhysical a (P.map (algebraMap ℝ ℂ)) x =
      ((gaussPolyFun (heatPolyR a P) (1 / (2 * a)) x : ℝ) : ℂ) := by
  have hcp : ((2 * π * a : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) =
      (((2 * π * a) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    ring_nf
  rw [heatPhysical, natDegree_map, hcp]
  simp only [coeff_map, gaussDeriv_eq_ofReal, gaussPolyFun, heatPolyR, eval_mul, eval_C,
    eval_finsetSum, Complex.coe_algebraMap]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-! ## Fourier side and the heat Hankel form -/

/-- The Fourier–Laplace transform `∫ f(x) e^{ixz} dx`. -/
def heatStripTransform (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ x : ℝ, f x * Complex.exp (I * z * x)

/-- The Fourier–Laplace transform of the real physical heat test. -/
theorem heatStripTransform_heatPhysical {a : ℝ} (ha : 0 < a) (P : ℝ[X]) (z : ℂ) :
    heatStripTransform (fun x => ((gaussPolyFun (heatPolyR a P) (1 / (2 * a)) x : ℝ) : ℂ)) z =
      Complex.exp (-(a : ℂ) * z ^ 2 / 2) * (P.map (algebraMap ℝ ℂ)).eval (z ^ 2) := by
  rw [← integral_heatPhysical_mul_cexp ha]
  unfold heatStripTransform
  simp_rw [heatPhysical_map_eq ha]

theorem conj_eval_map_ofReal_conj (P : ℝ[X]) (w : ℂ) :
    (starRingEnd ℂ) ((P.map (algebraMap ℝ ℂ)).eval ((starRingEnd ℂ) w)) =
      (P.map (algebraMap ℝ ℂ)).eval w := by
  rw [eval_map, eval_map, hom_eval₂, Complex.conj_conj]
  congr 1
  ext r
  simp

/-- **The heat Hankel form of a real polynomial is a zero sum of squares** `Σ_q G(z_q)²`. -/
theorem heatHankelTermAt_map_eq_sq (a : ℝ) (P : ℝ[X]) (z : ℂ) :
    heatHankelTermAt a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) (z ^ 2) =
      (Complex.exp (-(a : ℂ) * z ^ 2 / 2) * (P.map (algebraMap ℝ ℂ)).eval (z ^ 2)) ^ 2 := by
  rw [heatHankelTermAt, conj_eval_map_ofReal_conj, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

theorem heatHankel_map_eq_tsum_sq {a : ℝ} (ha : 0 < a) (P : ℝ[X]) :
    heatHankel a (P.map (algebraMap ℝ ℂ)) (P.map (algebraMap ℝ ℂ)) =
      ∑' q : XiZeroCopy, heatStripTransform
        (fun x => ((gaussPolyFun (heatPolyR a P) (1 / (2 * a)) x : ℝ) : ℂ))
        (xiSpectralPoint q) ^ 2 := by
  unfold heatHankel
  refine tsum_congr fun q => ?_
  rw [heatStripTransform_heatPhysical ha, xiHeatFrequency, heatHankelTermAt_map_eq_sq]

/-! ## Strip bounds -/

theorem norm_cexp_I_mul_le_of_strip {z : ℂ} (hz : |z.im| ≤ 1 / 2) (x : ℝ) :
    ‖Complex.exp (I * z * x)‖ ≤ Real.exp (|x| / 2) := by
  rw [Complex.norm_exp]
  refine Real.exp_le_exp.2 ?_
  have h : (I * z * (x : ℂ)).re = -(z.im * x) := by simp
  rw [h]
  have := abs_mul z.im x
  have h1 : |z.im| * |x| ≤ 1 / 2 * |x| := mul_le_mul_of_nonneg_right hz (abs_nonneg x)
  have h2 := neg_abs_le (z.im * x)
  linarith

theorem integrable_mul_cexp_of_strip {f : ℝ → ℂ} (hf : Continuous f)
    (hint : Integrable (fun x => ‖f x‖ * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable (fun x : ℝ => f x * Complex.exp (I * z * x)) := by
  refine hint.mono' (hf.mul (Complex.continuous_exp.comp
    (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_of_strip hz x) (norm_nonneg _)

/-- `|∫ f e^{ixz}| ≤ ∫ |f| e^{|x|/2}` on the strip `|Im z| ≤ ½`. -/
theorem norm_heatStripTransform_le {f : ℝ → ℂ}
    (hint : Integrable (fun x => ‖f x‖ * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖heatStripTransform f z‖ ≤ ∫ x, ‖f x‖ * Real.exp (|x| / 2) := by
  unfold heatStripTransform
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) hint
    (Filter.Eventually.of_forall fun x => ?_))
  simp only
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_cexp_I_mul_le_of_strip hz x) (norm_nonneg _)

/-- **Integration by parts on the strip.**  `F_{f'}(z) = −iz F_f(z)`. -/
theorem heatStripTransform_deriv {f f' : ℝ → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hint : Integrable (fun x => ‖f x‖ * Real.exp (|x| / 2)))
    (hint' : Integrable (fun x => ‖f' x‖ * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    heatStripTransform f' z = -(I * z) * heatStripTransform f z := by
  have hv : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Complex.exp (I * z * y))
      (Complex.exp (I * z * x) * (I * z)) x := fun x => by
    have h := ((hasDerivAt_id (x : ℂ)).const_mul (I * z)).cexp.comp_ofReal
    refine h.congr_deriv ?_
    simp
  have h1 := integrable_mul_cexp_of_strip hf hint hz
  have h2 := integrable_mul_cexp_of_strip hf' hint' hz
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := f)
    (v := fun y : ℝ => Complex.exp (I * z * y)) (u' := f')
    (v' := fun x => Complex.exp (I * z * x) * (I * z)) (fun x _ => hderiv x) (fun x _ => hv x)
    (by
      refine (h1.mul_const (I * z)).congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.mul_apply]
      ring)
    h2 h1
  unfold heatStripTransform
  have e : (∫ x : ℝ, f x * (Complex.exp (I * z * x) * (I * z))) =
      (∫ x : ℝ, f x * Complex.exp (I * z * x)) * (I * z) := by
    rw [← integral_mul_const]
    congr 1
    funext x
    ring
  rw [e] at hibp
  linear_combination hibp

theorem norm_mul_norm_heatStripTransform_eq {f f' : ℝ → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hint : Integrable (fun x => ‖f x‖ * Real.exp (|x| / 2)))
    (hint' : Integrable (fun x => ‖f' x‖ * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖z‖ * ‖heatStripTransform f z‖ = ‖heatStripTransform f' z‖ := by
  rw [heatStripTransform_deriv hf hf' hderiv hint hint' hz, norm_mul, norm_neg, norm_mul,
    Complex.norm_I, one_mul]

/-- **Integration by parts on the strip.**  `|z| |∫ f e^{ixz}| ≤ ∫ |f'| e^{|x|/2}`. -/
theorem norm_mul_norm_heatStripTransform_le {f f' : ℝ → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (hderiv : ∀ x, HasDerivAt f (f' x) x)
    (hint : Integrable (fun x => ‖f x‖ * Real.exp (|x| / 2)))
    (hint' : Integrable (fun x => ‖f' x‖ * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖z‖ * ‖heatStripTransform f z‖ ≤ ∫ x, ‖f' x‖ * Real.exp (|x| / 2) := by
  rw [norm_mul_norm_heatStripTransform_eq hf hf' hderiv hint hint' hz]
  exact norm_heatStripTransform_le hint' hz

/-- **Two integrations by parts.**  `|z|² |∫ f e^{ixz}| ≤ ∫ |f''| e^{|x|/2}`. -/
theorem sq_norm_mul_norm_heatStripTransform_le {f f' f'' : ℝ → ℂ} (hf : Continuous f)
    (hf' : Continuous f') (hf'' : Continuous f'') (hd : ∀ x, HasDerivAt f (f' x) x)
    (hd' : ∀ x, HasDerivAt f' (f'' x) x)
    (hint : Integrable (fun x => ‖f x‖ * Real.exp (|x| / 2)))
    (hint' : Integrable (fun x => ‖f' x‖ * Real.exp (|x| / 2)))
    (hint'' : Integrable (fun x => ‖f'' x‖ * Real.exp (|x| / 2))) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖z‖ ^ 2 * ‖heatStripTransform f z‖ ≤ ∫ x, ‖f'' x‖ * Real.exp (|x| / 2) := by
  rw [sq, mul_assoc, norm_mul_norm_heatStripTransform_eq hf hf' hd hint hint' hz]
  exact norm_mul_norm_heatStripTransform_le hf' hf'' hd' hint' hint'' hz

end

end RHTower
