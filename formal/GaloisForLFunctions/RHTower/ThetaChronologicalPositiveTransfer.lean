import GaloisForLFunctions.RHTower.ThetaChronologicalCutoffCurrent
import GaloisForLFunctions.RHTower.CausalMobiusThetaTail
import GaloisForLFunctions.RHTower.ZetaNotchSmoothTest
import GaloisForLFunctions.RHTower.ThetaGroupOffLineStripZero

/-!
# Positive forward-dilation transfer between the two theta Euler boundary currents

`D = (1 − ∂)(2 − ∂)` and the positive forward-dilation operator

`(Tf)(y) = (2π)^{−1} Σ_n n^{−2} ∫_0^1 f(y + log n − (1/2) log t) (1 − t)^{−1/2} dt`

carry the cutoff Möbius current `C` to the reflected moving-cusp current `R`:
`e^{3y/2} R(y) = −T(DC)(y)` for every `y`.  The Laplace multiplier of `T` is
`A(z) = ζ(z+2) Γ((z+2)/2) / (2√π Γ((z+3)/2))`, and `H = A·(z+1)(z+2) = ξ(z+2)/G(z)` is holomorphic
and zero-free on `Re z > −1`.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-! ## The derivative operator `D` -/

/-- `D f = (1 − ∂)(2 − ∂) f = 2 f − 3 f' + f''`. -/
def chronoDerivOp (f : ℝ → ℝ) (y : ℝ) : ℝ := 2 * f y - 3 * deriv f y + deriv (deriv f) y

theorem chronoDerivOp_eq_iteratedDeriv (f : ℝ → ℝ) (y : ℝ) :
    chronoDerivOp f y = 2 * iteratedDeriv 0 f y - 3 * iteratedDeriv 1 f y + iteratedDeriv 2 f y := by
  rw [chronoDerivOp, iteratedDeriv_zero, iteratedDeriv_one, iteratedDeriv_succ, iteratedDeriv_one]

/-- `D` does not preserve positivity: it sends the positive Gaussian to a function that is
negative at `−1/2`. -/
theorem chronoDerivOp_gaussian_neg :
    (∀ y : ℝ, 0 < Real.exp (-y ^ 2)) ∧ chronoDerivOp (fun y => Real.exp (-y ^ 2)) (-1 / 2) < 0 := by
  refine ⟨fun y => Real.exp_pos _, ?_⟩
  have h1 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2)) (-2 * y * Real.exp (-y ^ 2)) y := by
    intro y
    have hq : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * y)) y := by
      have := (hasDerivAt_pow 2 y).neg
      norm_num at this
      exact this
    exact hq.exp.congr_deriv (by ring)
  have hd1 : deriv (fun y : ℝ => Real.exp (-y ^ 2)) = fun y => -2 * y * Real.exp (-y ^ 2) :=
    funext fun y => (h1 y).deriv
  have h2 : ∀ y : ℝ, HasDerivAt (fun y : ℝ => -2 * y * Real.exp (-y ^ 2))
      ((4 * y ^ 2 - 2) * Real.exp (-y ^ 2)) y := by
    intro y
    have := ((hasDerivAt_id y).const_mul (-2)).fun_mul (h1 y)
    exact this.congr_deriv (by simp only [id]; ring)
  have hd2 : deriv (deriv fun y : ℝ => Real.exp (-y ^ 2)) = fun y => (4 * y ^ 2 - 2) * Real.exp (-y ^ 2) := by
    rw [hd1]; exact funext fun y => (h2 y).deriv
  rw [chronoDerivOp, hd2, hd1]
  have := Real.exp_pos (-(-1 / 2 : ℝ) ^ 2)
  norm_num
  nlinarith

/-- The derived cutoff current `DC`. -/
def cutoffTransferSource (y : ℝ) : ℝ := chronoDerivOp cofinalBoundaryProfile y

theorem cutoffTransferSource_eq (y : ℝ) :
    cutoffTransferSource y = 2 * iteratedDeriv 0 cofinalBoundaryProfile y -
      3 * iteratedDeriv 1 cofinalBoundaryProfile y + iteratedDeriv 2 cofinalBoundaryProfile y :=
  chronoDerivOp_eq_iteratedDeriv _ y

theorem continuous_cutoffTransferSource : Continuous cutoffTransferSource := by
  have h := fun j => continuous_iteratedDeriv_cofinalBoundaryProfile j
  simp_rw [show cutoffTransferSource = fun y => 2 * iteratedDeriv 0 cofinalBoundaryProfile y -
      3 * iteratedDeriv 1 cofinalBoundaryProfile y + iteratedDeriv 2 cofinalBoundaryProfile y from
    funext cutoffTransferSource_eq]
  exact (((h 0).const_mul 2).sub ((h 1).const_mul 3)).add (h 2)

theorem exists_abs_cutoffTransferSource_le :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |cutoffTransferSource y| ≤ M := by
  obtain ⟨M0, h0, hM0⟩ := exists_abs_iteratedDeriv_cofinalBoundaryProfile_le 0
  obtain ⟨M1, h1, hM1⟩ := exists_abs_iteratedDeriv_cofinalBoundaryProfile_le 1
  obtain ⟨M2, h2, hM2⟩ := exists_abs_iteratedDeriv_cofinalBoundaryProfile_le 2
  refine ⟨2 * M0 + 3 * M1 + M2, by positivity, fun y => ?_⟩
  rw [cutoffTransferSource_eq]
  have a0 := hM0 y; have a1 := hM1 y; have a2 := hM2 y
  calc |2 * iteratedDeriv 0 cofinalBoundaryProfile y - 3 * iteratedDeriv 1 cofinalBoundaryProfile y +
        iteratedDeriv 2 cofinalBoundaryProfile y|
      ≤ |2 * iteratedDeriv 0 cofinalBoundaryProfile y| + |3 * iteratedDeriv 1 cofinalBoundaryProfile y| +
          |iteratedDeriv 2 cofinalBoundaryProfile y| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ _ := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_of_pos (by norm_num : (0:ℝ) < 3)]
        linarith

/-- **`ℒ(DC)(z) = (z+1)(z+2) ℒC(z)`** for `Re z > 0`, with absolute convergence. -/
theorem integral_cexp_mul_cutoffTransferSource {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * (cutoffTransferSource y : ℂ)) ∧
      (∫ y : ℝ, Complex.exp (z * y) * (cutoffTransferSource y : ℂ)) =
        (z + 1) * (z + 2) * -(commutatorGammaFactor z * (riemannZeta (1 + z))⁻¹) := by
  obtain ⟨i0, e0⟩ := integral_cexp_mul_iteratedDeriv_cofinalBoundaryProfile 0 hz
  obtain ⟨i1, e1⟩ := integral_cexp_mul_iteratedDeriv_cofinalBoundaryProfile 1 hz
  obtain ⟨i2, e2⟩ := integral_cexp_mul_iteratedDeriv_cofinalBoundaryProfile 2 hz
  have hfun : (fun y : ℝ => Complex.exp (z * y) * (cutoffTransferSource y : ℂ)) =
      fun y : ℝ => 2 * (Complex.exp (z * y) * ((iteratedDeriv 0 cofinalBoundaryProfile y : ℝ) : ℂ)) -
        3 * (Complex.exp (z * y) * ((iteratedDeriv 1 cofinalBoundaryProfile y : ℝ) : ℂ)) +
          Complex.exp (z * y) * ((iteratedDeriv 2 cofinalBoundaryProfile y : ℝ) : ℂ) := by
    funext y; rw [cutoffTransferSource_eq]; push_cast; ring
  have hi : Integrable fun y : ℝ => 2 * (Complex.exp (z * y) * ((iteratedDeriv 0 cofinalBoundaryProfile y : ℝ) : ℂ)) -
        3 * (Complex.exp (z * y) * ((iteratedDeriv 1 cofinalBoundaryProfile y : ℝ) : ℂ)) :=
    (i0.const_mul 2).sub (i1.const_mul 3)
  refine ⟨hfun ▸ hi.add i2, ?_⟩
  rw [hfun, integral_add hi i2, integral_sub (i0.const_mul 2) (i1.const_mul 3), integral_const_mul,
    integral_const_mul, e0, e1, e2]
  ring

/-! ## The positive forward-dilation operator `T` -/

/-- The kernel weight `(1 − t)^{−1/2}`. -/
def forwardDilationWeight (t : ℝ) : ℝ := (Real.sqrt (1 - t))⁻¹

/-- The forward shift `log n − (1/2) log t`. -/
def forwardDilationShift (n : ℕ) (t : ℝ) : ℝ := Real.log n - Real.log t / 2

/-- `∫_0^1 f(y + log n − (1/2) log t) (1 − t)^{−1/2} dt`. -/
def forwardDilationAverage (f : ℝ → ℝ) (n : ℕ) (y : ℝ) : ℝ :=
  ∫ t in Ioo (0 : ℝ) 1, f (y + forwardDilationShift n t) * forwardDilationWeight t

/-- **(3) The positive forward-dilation operator.** -/
def positiveTransfer (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ * forwardDilationAverage f n y

theorem forwardDilationWeight_eq_rpow {t : ℝ} (ht : t ≤ 1) : forwardDilationWeight t = (1 - t) ^ (-(1 / 2 : ℝ)) := by
  rw [forwardDilationWeight, Real.sqrt_eq_rpow, Real.rpow_neg (by linarith)]

theorem forwardDilationWeight_nonneg (t : ℝ) : 0 ≤ forwardDilationWeight t := inv_nonneg.2 (Real.sqrt_nonneg _)

theorem measurable_forwardDilationWeight : Measurable forwardDilationWeight :=
  (Real.continuous_sqrt.measurable.comp (measurable_const.sub measurable_id)).inv

theorem intervalIntegrable_forwardDilationWeight :
    IntervalIntegrable forwardDilationWeight volume 0 1 := by
  have h : IntervalIntegrable (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) volume (1 - 1) (1 - 0) :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 : IntervalIntegrable (fun x : ℝ => (1 - x) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    have := h.comp_sub_left 1
    simp only [sub_zero, sub_self] at this
    exact this.symm
  refine h2.congr fun t ht => ?_
  rw [uIoc_of_le zero_le_one] at ht
  exact (forwardDilationWeight_eq_rpow ht.2).symm

theorem integrableOn_forwardDilationWeight : IntegrableOn forwardDilationWeight (Ioo 0 1) :=
  (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).1 intervalIntegrable_forwardDilationWeight

/-- The kernel mass of one dilation average: `∫_0^1 (1 − t)^{−1/2} dt = 2`. -/
theorem integral_forwardDilationWeight : ∫ t in Ioo (0 : ℝ) 1, forwardDilationWeight t = 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one]
  have h1 : ∫ t in (0 : ℝ)..1, forwardDilationWeight t = ∫ t in (0 : ℝ)..1, (1 - t) ^ (-(1 / 2 : ℝ)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    exact forwardDilationWeight_eq_rpow ht.2
  rw [h1, intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(1 / 2 : ℝ))) 1,
    integral_rpow (Or.inl (by norm_num))]
  norm_num

theorem forwardDilationShift_nonneg {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
    0 ≤ forwardDilationShift n t := by
  have h1 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have h2 : Real.log t < 0 := Real.log_neg ht.1 ht.2
  rw [forwardDilationShift]; linarith

theorem measurable_forwardDilationShift (n : ℕ) : Measurable (forwardDilationShift n) :=
  measurable_const.sub (Real.measurable_log.div_const 2)

theorem integrableOn_forwardDilationIntegrand {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ}
    (hM : ∀ x, |f x| ≤ M) (n : ℕ) (y : ℝ) :
    IntegrableOn (fun t => f (y + forwardDilationShift n t) * forwardDilationWeight t) (Ioo 0 1) := by
  refine (integrableOn_forwardDilationWeight.const_mul M).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact ((hf.measurable.comp (measurable_const.add (measurable_forwardDilationShift n))).mul
      measurable_forwardDilationWeight).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (forwardDilationWeight_nonneg t)]
    exact mul_le_mul_of_nonneg_right (hM _) (forwardDilationWeight_nonneg t)

theorem abs_forwardDilationAverage_le {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (n : ℕ) (y : ℝ) : |forwardDilationAverage f n y| ≤ 2 * M := by
  rw [forwardDilationAverage, ← Real.norm_eq_abs]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc ∫ t in Ioo (0 : ℝ) 1, ‖f (y + forwardDilationShift n t) * forwardDilationWeight t‖
      ≤ ∫ t in Ioo (0 : ℝ) 1, M * forwardDilationWeight t := by
        refine setIntegral_mono_on (integrableOn_forwardDilationIntegrand hf hM n y).norm
          (integrableOn_forwardDilationWeight.const_mul M) measurableSet_Ioo fun t _ => ?_
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (forwardDilationWeight_nonneg t)]
        exact mul_le_mul_of_nonneg_right (hM _) (forwardDilationWeight_nonneg t)
    _ = 2 * M := by rw [integral_const_mul, integral_forwardDilationWeight]; ring

theorem summable_inv_sq_nat : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ :=
  Real.summable_nat_pow_inv.2 (by norm_num)

theorem summable_positiveTransfer_terms {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (y : ℝ) : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ * forwardDilationAverage f n y := by
  refine Summable.of_norm_bounded (summable_inv_sq_nat.mul_right (2 * M)) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_forwardDilationAverage_le hf hM n y) (by positivity)

theorem continuous_forwardDilationAverage {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (n : ℕ) : Continuous (forwardDilationAverage f n) := by
  refine continuous_of_dominated (bound := fun t => M * forwardDilationWeight t)
    (fun y => (integrableOn_forwardDilationIntegrand hf hM n y).aestronglyMeasurable)
    (fun y => Eventually.of_forall fun t => ?_) (integrableOn_forwardDilationWeight.const_mul M)
    (Eventually.of_forall fun t => ?_)
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (forwardDilationWeight_nonneg t)]
    exact mul_le_mul_of_nonneg_right (hM _) (forwardDilationWeight_nonneg t)
  · exact (hf.comp (continuous_id.add continuous_const)).mul continuous_const

/-- **`T` maps bounded continuous functions to continuous functions.** -/
theorem continuous_positiveTransfer {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) :
    Continuous (positiveTransfer f) := by
  refine continuous_const.mul (continuous_tsum (fun n => continuous_const.mul
    (continuous_forwardDilationAverage hf hM n)) (summable_inv_sq_nat.mul_right (2 * M)) fun n y => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (abs_forwardDilationAverage_le hf hM n y) (by positivity)

/-- **`T` is positive.** -/
theorem positiveTransfer_nonneg {f : ℝ → ℝ} (hf0 : ∀ x, 0 ≤ f x) (y : ℝ) : 0 ≤ positiveTransfer f y := by
  refine mul_nonneg (by positivity) (tsum_nonneg fun n => mul_nonneg (by positivity) ?_)
  exact setIntegral_nonneg measurableSet_Ioo fun t _ => mul_nonneg (hf0 _) (forwardDilationWeight_nonneg t)

/-- **`T` is forward:** `Tf(y)` only reads `f` on `[y, ∞)`. -/
theorem positiveTransfer_congr_forward {f g : ℝ → ℝ} {y : ℝ} (hfg : ∀ x, y ≤ x → f x = g x) :
    positiveTransfer f y = positiveTransfer g y := by
  rw [positiveTransfer, positiveTransfer]
  congr 1
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [hfg _ (by linarith [forwardDilationShift_nonneg hn ht])]

/-- **The kernel of `T` has total mass `ζ(2)/π`.** -/
theorem positiveTransfer_one (y : ℝ) :
    ((positiveTransfer (fun _ => 1) y : ℝ) : ℂ) = riemannZeta 2 / Real.pi := by
  have h : ∀ n : ℕ, forwardDilationAverage (fun _ => 1) n y = 2 := fun n => by
    simp only [forwardDilationAverage, one_mul]; exact integral_forwardDilationWeight
  have hs : ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ = Real.pi ^ 2 / 6 := by
    rw [← hasSum_zeta_two.tsum_eq]; simp only [one_div]
  simp only [positiveTransfer, h]
  rw [tsum_mul_right, riemannZeta_two, hs]
  push_cast
  field_simp

/-! ## The Laplace law of `T` -/

theorem integral_norm_cexp_mul_comp_add (z : ℂ) (c : ℝ) (G : ℝ → ℂ) :
    (∫ x : ℝ, ‖Complex.exp (z * x) * G (x + c)‖) =
      Real.exp (-(z.re * c)) * ∫ y : ℝ, ‖Complex.exp (z * y) * G y‖ := by
  have h := integral_add_right_eq_self (μ := volume) (fun y : ℝ => ‖Complex.exp (z * y) * G y‖) c
  rw [← h, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- The beta factor `∫_0^1 t^{z/2} (1 − t)^{−1/2} dt`. -/
def forwardDilationBeta (z : ℂ) : ℂ := ∫ t in Ioo (0 : ℝ) 1, (t : ℂ) ^ (z / 2) * (forwardDilationWeight t : ℂ)

theorem cexp_neg_mul_forwardDilationShift {n : ℕ} (hn : 0 < n) {t : ℝ} (ht : 0 < t) (z : ℂ) :
    Complex.exp (-(z * (forwardDilationShift n t : ℂ))) = (n : ℂ) ^ (-z) * (t : ℂ) ^ (z / 2) := by
  have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  rw [natCast_cpow_eq_cexp_mul_log hn, Complex.cpow_def_of_ne_zero htC, ← Complex.ofReal_log ht.le,
    ← Complex.exp_add, forwardDilationShift]
  push_cast
  ring_nf

/-- **One dilation average.**  For `Re z ≥ 0` and `n ≥ 1`:
`ℒ(avg_n f)(z) = n^{−z} β(z) ℒf(z)`, absolutely, with `‖e^{z·} avg_n f‖₁ ≤ 2 ‖e^{z·} f‖₁`. -/
theorem forwardDilationAverage_laplace {f : ℝ → ℝ} (hf : Continuous f) {z : ℂ} (hz : 0 ≤ z.re) (hfint : Integrable fun y : ℝ => Complex.exp (z * y) * (f y : ℂ))
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ)) ∧
      (∫ y : ℝ, ‖Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ)‖) ≤
        2 * ∫ y : ℝ, ‖Complex.exp (z * y) * (f y : ℂ)‖ ∧
      (∫ y : ℝ, Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ)) =
        (n : ℂ) ^ (-z) * forwardDilationBeta z * ∫ y : ℝ, Complex.exp (z * y) * (f y : ℂ) := by
  set ν : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  set I : ℝ := ∫ y : ℝ, ‖Complex.exp (z * y) * (f y : ℂ)‖
  have hI : 0 ≤ I := integral_nonneg fun _ => norm_nonneg _
  set F : ℝ × ℝ → ℂ := fun p => Complex.exp (z * p.1) *
    ((f (p.1 + forwardDilationShift n p.2) * forwardDilationWeight p.2 : ℝ) : ℂ)
  have hFeq : ∀ y t, F (y, t) = (forwardDilationWeight t : ℂ) *
      (Complex.exp (z * y) * (f (y + forwardDilationShift n t) : ℂ)) := fun y t => by
    simp only [F]; push_cast; ring
  have hFt : ∀ t, Integrable (fun y => F (y, t)) := fun t => by
    simp_rw [hFeq]
    exact (integrable_cexp_mul_comp_add (forwardDilationShift n t) (G := fun y => (f y : ℂ)) hfint).const_mul _
  have hnormF : ∀ t, (∫ y, ‖F (y, t)‖) =
      forwardDilationWeight t * Real.exp (-(z.re * forwardDilationShift n t)) * I := fun t => by
    have h1 : (fun y : ℝ => ‖F (y, t)‖) = fun y : ℝ => forwardDilationWeight t *
        ‖Complex.exp (z * y) * (f (y + forwardDilationShift n t) : ℂ)‖ := by
      funext y
      rw [hFeq, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (forwardDilationWeight_nonneg t)]
    rw [h1, integral_const_mul, integral_norm_cexp_mul_comp_add z (forwardDilationShift n t) (fun y => (f y : ℂ))]
    ring
  have hmeas : AEStronglyMeasurable F (volume.prod ν) := by
    refine Measurable.aestronglyMeasurable ?_
    refine (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp measurable_fst))).mul
      (Complex.measurable_ofReal.comp ((hf.measurable.comp (measurable_fst.add
        ((measurable_forwardDilationShift n).comp measurable_snd))).mul
        (measurable_forwardDilationWeight.comp measurable_snd)))
  have hbound : ∀ t ∈ Ioo (0 : ℝ) 1, (∫ y, ‖F (y, t)‖) ≤ forwardDilationWeight t * I := fun t ht => by
    rw [hnormF]
    have hs := forwardDilationShift_nonneg hn ht
    have he : Real.exp (-(z.re * forwardDilationShift n t)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith)
    have := forwardDilationWeight_nonneg t
    calc forwardDilationWeight t * Real.exp (-(z.re * forwardDilationShift n t)) * I ≤ forwardDilationWeight t * 1 * I := by
          gcongr
      _ = _ := by ring
  have hprod : Integrable F (volume.prod ν) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall hFt, ?_⟩
    refine (integrableOn_forwardDilationWeight.mul_const I).mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp_rw [hnormF]
      exact (measurable_forwardDilationWeight.mul (Real.measurable_exp.comp
        ((measurable_forwardDilationShift n).const_mul z.re).neg)).mul_const I
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact hbound t ht
  have hinner : ∀ y : ℝ, (∫ t, F (y, t) ∂ν) = Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ) := by
    intro y
    simp only [F]
    rw [integral_const_mul, integral_complex_ofReal]
    rfl
  have hint : Integrable (fun y : ℝ => Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ)) := by
    have := hprod.integral_prod_left
    simp_rw [hinner] at this
    exact this
  refine ⟨hint, ?_, ?_⟩
  · calc (∫ y : ℝ, ‖Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ)‖)
        ≤ ∫ y : ℝ, (∫ t : ℝ, ‖F (y, t)‖ ∂ν) := by
          refine integral_mono hint.norm hprod.norm.integral_prod_left fun y => ?_
          rw [← hinner]
          exact norm_integral_le_integral_norm _
      _ = ∫ t : ℝ, (∫ y : ℝ, ‖F (y, t)‖) ∂ν :=
          integral_integral_swap (f := fun y t => ‖F (y, t)‖) hprod.norm
      _ ≤ ∫ t : ℝ, forwardDilationWeight t * I ∂ν := by
          refine setIntegral_mono_on ?_ (integrableOn_forwardDilationWeight.mul_const I) measurableSet_Ioo hbound
          refine (integrableOn_forwardDilationWeight.mul_const I).mono' ?_ ?_
          · refine Measurable.aestronglyMeasurable ?_
            simp_rw [hnormF]
            exact (measurable_forwardDilationWeight.mul (Real.measurable_exp.comp
              ((measurable_forwardDilationShift n).const_mul z.re).neg)).mul_const I
          · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun t ht => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
            exact hbound t ht
      _ = 2 * I := by rw [integral_mul_const, integral_forwardDilationWeight]
  · calc (∫ y : ℝ, Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ))
        = ∫ y : ℝ, (∫ t : ℝ, F (y, t) ∂ν) :=
          integral_congr_ae (Eventually.of_forall fun y => (hinner y).symm)
      _ = ∫ t : ℝ, (∫ y : ℝ, F (y, t)) ∂ν := integral_integral_swap (f := fun y t => F (y, t)) hprod
      _ = ∫ t : ℝ, (n : ℂ) ^ (-z) * ((t : ℂ) ^ (z / 2) * (forwardDilationWeight t : ℂ)) *
            (∫ y : ℝ, Complex.exp (z * y) * (f y : ℂ)) ∂ν := by
          refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          simp_rw [hFeq]
          rw [integral_const_mul, integral_cexp_mul_comp_add z (forwardDilationShift n t) (fun y => (f y : ℂ)),
            cexp_neg_mul_forwardDilationShift hn ht.1]
          ring
      _ = _ := by
          rw [integral_mul_const, integral_const_mul, forwardDilationBeta]

theorem natCast_inv_sq_mul_cpow_neg (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (((n : ℝ) ^ 2)⁻¹ : ℂ) * (n : ℂ) ^ (-z) = 1 / (n : ℂ) ^ (z + 2) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : z + 2 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
    simp [Complex.zero_cpow this]
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Complex.cpow_add _ _ hnC, Complex.cpow_neg, show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
      Complex.cpow_natCast]
    push_cast
    field_simp

/-- **The Laplace law of `T`.**  For continuous `f` with `e^{z·} f ∈ L¹`, `Re z > 0`:
`ℒ(Tf)(z) = (2π)^{−1} ζ(z+2) β(z) ℒf(z)`, with absolute convergence. -/
theorem integral_cexp_mul_positiveTransfer {f : ℝ → ℝ} (hf : Continuous f) {z : ℂ} (hz : 0 < z.re)
    (hfint : Integrable fun y : ℝ => Complex.exp (z * y) * (f y : ℂ)) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * (positiveTransfer f y : ℂ)) ∧
      (∫ y : ℝ, Complex.exp (z * y) * (positiveTransfer f y : ℂ)) =
        ((2 * Real.pi)⁻¹ : ℂ) * riemannZeta (z + 2) * forwardDilationBeta z *
          ∫ y : ℝ, Complex.exp (z * y) * (f y : ℂ) := by
  set I : ℝ := ∫ y : ℝ, ‖Complex.exp (z * y) * (f y : ℂ)‖
  set G : ℕ → ℝ → ℂ := fun n y => (((n : ℝ) ^ 2)⁻¹ : ℂ) *
    (Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ))
  have hG : ∀ n, Integrable (G n) ∧ (∫ y, ‖G n y‖) ≤ ((n : ℝ) ^ 2)⁻¹ * (2 * I) ∧
      (∫ y, G n y) = (((n : ℝ) ^ 2)⁻¹ : ℂ) * (n : ℂ) ^ (-z) * forwardDilationBeta z *
        ∫ y : ℝ, Complex.exp (z * y) * (f y : ℂ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [G]
    obtain ⟨h1, h2, h3⟩ := forwardDilationAverage_laplace hf hz.le hfint hn
    refine ⟨h1.const_mul _, ?_, ?_⟩
    · have hnorm : ∀ y : ℝ, ‖G n y‖ = ((n : ℝ) ^ 2)⁻¹ *
          ‖Complex.exp (z * y) * (forwardDilationAverage f n y : ℂ)‖ := fun y => by
        simp only [G]
        rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, Nat.abs_cast]
      simp_rw [hnorm]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    · simp only [G]; rw [integral_const_mul, h3]; ring
  have hsum : Summable fun n => ∫ y, ‖G n y‖ :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) (fun n => (hG n).2.1)
      (summable_inv_sq_nat.mul_right (2 * I))
  have hfun : (fun y : ℝ => Complex.exp (z * y) * (positiveTransfer f y : ℂ)) =
      fun y => ((2 * Real.pi)⁻¹ : ℂ) * ∑' n, G n y := by
    funext y
    simp only [positiveTransfer, G]
    push_cast
    rw [mul_left_comm, ← tsum_mul_left]
    congr 1
    refine tsum_congr fun n => ?_
    ring
  have hint := GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
    (fun n => (hG n).1) hsum
  refine ⟨hfun ▸ hint.const_mul _, ?_⟩
  rw [hfun, integral_const_mul, ← (hasSum_integral_of_summable_integral_norm (fun n => (hG n).1)
    hsum).tsum_eq, tsum_congr fun n => (hG n).2.2]
  have hz2 : 1 < (z + 2).re := by simp; linarith
  rw [zeta_eq_tsum_one_div_nat_cpow hz2, ← tsum_congr fun n => natCast_inv_sq_mul_cpow_neg n hz,
    tsum_mul_right, tsum_mul_right]
  ring

/-! ## The multiplier `A` and the completed-zeta factorisation -/

/-- `A(z) = ζ(z+2) Γ((z+2)/2) / (2√π Γ((z+3)/2))`. -/
def transferMultiplier (z : ℂ) : ℂ :=
  ((2 * Real.sqrt Real.pi)⁻¹ : ℂ) * riemannZeta (z + 2) * Complex.Gamma ((z + 2) / 2) /
    Complex.Gamma ((z + 3) / 2)

theorem cpow_half_pi_eq_sqrt : (Real.pi : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow Real.pi_pos.le]
  push_cast; rfl

/-- **Euler's beta integral.**  `β(z) = √π Γ((z+2)/2)/Γ((z+3)/2)` for `Re z > −2`. -/
theorem forwardDilationBeta_eq {z : ℂ} (hz : -2 < z.re) :
    forwardDilationBeta z = (Real.sqrt Real.pi : ℂ) * Complex.Gamma ((z + 2) / 2) / Complex.Gamma ((z + 3) / 2) := by
  have hu : 0 < (z / 2 + 1).re := by simp; linarith
  have hv : 0 < (1 / 2 : ℂ).re := by norm_num
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral hu hv
  have hG3 : Complex.Gamma ((z + 3) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hsum : z / 2 + 1 + 1 / 2 = (z + 3) / 2 := by ring
  rw [hsum, Complex.Gamma_one_half_eq, cpow_half_pi_eq_sqrt] at hB
  have hbeta : forwardDilationBeta z = (z / 2 + 1).betaIntegral (1 / 2) := by
    rw [forwardDilationBeta, Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
    rw [forwardDilationWeight_eq_rpow ht.2.le, Complex.ofReal_cpow (by linarith [ht.2])]
    congr 1
    · ring_nf
    · push_cast; ring_nf
  rw [hbeta, eq_div_iff hG3, show (z + 2) / 2 = z / 2 + 1 by ring, mul_comm _ (Complex.Gamma _), ← hB]
  ring

/-- **(5)** `(2π)^{−1} ζ(z+2) β(z) = A(z)` for `Re z > −2`. -/
theorem transferMultiplier_eq_beta {z : ℂ} (hz : -2 < z.re) :
    ((2 * Real.pi)⁻¹ : ℂ) * riemannZeta (z + 2) * forwardDilationBeta z = transferMultiplier z := by
  rw [forwardDilationBeta_eq hz, transferMultiplier]
  have hs : (Real.sqrt Real.pi : ℂ) ^ 2 = Real.pi := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs0 : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  rw [← hs]
  field_simp

/-- **(6)** `ξ(z+2) = A(z)(z+1)(z+2) G(z)` for `Re z > −1`. -/
theorem xi_add_two_eq_transferMultiplier {z : ℂ} (hz : -1 < z.re) :
    xi (z + 2) = transferMultiplier z * (z + 1) * (z + 2) * commutatorGammaFactor z := by
  have h0 : z + 2 ≠ 0 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  have h1 : z + 2 ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  rw [ZetaNotch.xi_eq_half_mul_gammaR_zeta h0 h1 (by simp; linarith), Complex.Gammaℝ_def,
    transferMultiplier, commutatorGammaFactor]
  have hG3 : Complex.Gamma ((z + 3) / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hpow : (Real.pi : ℂ) ^ (-(z + 2) / 2) = (Real.pi : ℂ) ^ (-(z + 1) / 2) * (Real.sqrt Real.pi : ℂ)⁻¹ := by
    rw [← cpow_half_pi_eq_sqrt, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hπ]
    ring_nf
  rw [hpow]
  have hs0 : (Real.sqrt Real.pi : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
  field_simp
  ring_nf

/-- **`ℒ(T f) = A ℒf`** in closed form. -/
theorem integral_cexp_mul_positiveTransfer_eq {f : ℝ → ℝ} (hf : Continuous f) {z : ℂ} (hz : 0 < z.re)
    (hfint : Integrable fun y : ℝ => Complex.exp (z * y) * (f y : ℂ)) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * (positiveTransfer f y : ℂ)) ∧
      (∫ y : ℝ, Complex.exp (z * y) * (positiveTransfer f y : ℂ)) =
        transferMultiplier z * ∫ y : ℝ, Complex.exp (z * y) * (f y : ℂ) := by
  obtain ⟨h1, h2⟩ := integral_cexp_mul_positiveTransfer hf hz hfint
  exact ⟨h1, by rw [h2, transferMultiplier_eq_beta (by linarith)]⟩

/-! ## The physical-source identity (4) -/

/-- **(2) in shifted form.**  `ℒ(e^{3·/2} R)(z) = ξ(z+2)/ζ(1+z)` for `Re z > 0`. -/
theorem integral_cexp_mul_reflectedCurrent {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun y : ℝ => Complex.exp (z * y) *
        ((Real.exp (3 * y / 2) * movingCuspDualLimit y : ℝ) : ℂ)) ∧
      (∫ y : ℝ, Complex.exp (z * y) * ((Real.exp (3 * y / 2) * movingCuspDualLimit y : ℝ) : ℂ)) =
        xi (z + 2) * (riemannZeta (1 + z))⁻¹ := by
  obtain ⟨h1, h2⟩ := integral_cexp_mul_movingCuspDualLimit (w := z + 3 / 2) (by simp; linarith)
  have hfun : (fun y : ℝ => Complex.exp (z * y) * ((Real.exp (3 * y / 2) * movingCuspDualLimit y : ℝ) : ℂ)) =
      fun y : ℝ => Complex.exp ((z + 3 / 2) * y) * (movingCuspDualLimit y : ℂ) := by
    funext y
    push_cast
    rw [← mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [hfun]
  refine ⟨h1, ?_⟩
  rw [h2, XiC_I_mul_eq_xi_half_add, show 1 / 2 + (z + 3 / 2) = z + 2 by ring,
    show z + 3 / 2 - 1 / 2 = 1 + z by ring]

/-- **(7)** `ℒ(−T(DC))(z) = ξ(z+2)/ζ(1+z)` for `Re z > 0`. -/
theorem integral_cexp_mul_neg_positiveTransfer_cutoff {z : ℂ} (hz : 0 < z.re) :
    Integrable (fun y : ℝ => Complex.exp (z * y) * (positiveTransfer cutoffTransferSource y : ℂ)) ∧
      -(∫ y : ℝ, Complex.exp (z * y) * (positiveTransfer cutoffTransferSource y : ℂ)) =
        xi (z + 2) * (riemannZeta (1 + z))⁻¹ := by
  obtain ⟨hDi, hDe⟩ := integral_cexp_mul_cutoffTransferSource hz
  obtain ⟨h1, h2⟩ := integral_cexp_mul_positiveTransfer_eq continuous_cutoffTransferSource hz hDi
  refine ⟨h1, ?_⟩
  rw [h2, hDe, xi_add_two_eq_transferMultiplier (by linarith)]
  ring

/-- **(4) The exact physical-source identity.**  `e^{3y/2} R(y) = −T(DC)(y)` for every real `y`. -/
theorem exp_mul_movingCuspDualLimit_eq_neg_positiveTransfer (y : ℝ) :
    Real.exp (3 * y / 2) * movingCuspDualLimit y = -positiveTransfer cutoffTransferSource y := by
  obtain ⟨M, -, hM⟩ := exists_abs_cutoffTransferSource_le
  set g : ℝ → ℝ := fun y => Real.exp (3 * y / 2) * movingCuspDualLimit y +
    positiveTransfer cutoffTransferSource y
  have hgc : Continuous g :=
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id |>.div_const 2)).mul
      continuous_movingCuspDualLimit).add (continuous_positiveTransfer continuous_cutoffTransferSource hM)
  set k : ℝ → ℂ := fun x => Complex.exp ((1 : ℂ) * x) * (g x : ℂ)
  have hlap : ∀ z : ℂ, 0 < z.re → Integrable (fun x : ℝ => Complex.exp (z * x) * (g x : ℂ)) ∧
      (∫ x : ℝ, Complex.exp (z * x) * (g x : ℂ)) = 0 := by
    intro z hz
    obtain ⟨a1, a2⟩ := integral_cexp_mul_reflectedCurrent hz
    obtain ⟨b1, b2⟩ := integral_cexp_mul_neg_positiveTransfer_cutoff hz
    have hfun : (fun x : ℝ => Complex.exp (z * x) * (g x : ℂ)) = fun x : ℝ =>
        Complex.exp (z * x) * ((Real.exp (3 * x / 2) * movingCuspDualLimit x : ℝ) : ℂ) +
          Complex.exp (z * x) * (positiveTransfer cutoffTransferSource x : ℂ) := by
      funext x; simp only [g]; push_cast; ring
    rw [hfun]
    refine ⟨a1.add b1, ?_⟩
    rw [integral_add a1 b1, a2, ← b2]
    ring
  have hk0 : k = 0 := by
    refine eq_zero_of_fourier_eq_zero ?_ (hlap 1 (by norm_num)).1 fun u => ?_
    · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).mul
        (Complex.continuous_ofReal.comp hgc)
    · have h := (hlap (1 - Complex.I * u) (by simp)).2
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [k]
      rw [← mul_assoc, ← Complex.exp_add]
      ring_nf
  have hgx := congrFun hk0 y
  simp only [k, Pi.zero_apply, mul_eq_zero, Complex.exp_ne_zero, false_or, Complex.ofReal_eq_zero] at hgx
  simp only [g] at hgx
  linarith

/-! ## (8) The zero-free transfer multiplier -/

/-- `H(z) = A(z)(z+1)(z+2)`. -/
def transferMultiplierH (z : ℂ) : ℂ := transferMultiplier z * (z + 1) * (z + 2)

/-- `H = ξ(z+2)/G(z)` on `Re z > −1`. -/
theorem transferMultiplierH_eq {z : ℂ} (hz : -1 < z.re) :
    transferMultiplierH z = xi (z + 2) / commutatorGammaFactor z := by
  rw [eq_div_iff (commutatorGammaFactor_ne_zero (by linarith)), xi_add_two_eq_transferMultiplier hz,
    transferMultiplierH]

/-- **(8a) `H` is holomorphic on `Re z > −1`.** -/
theorem differentiableOn_transferMultiplierH :
    DifferentiableOn ℂ transferMultiplierH {z : ℂ | -1 < z.re} := by
  intro z hz
  have hz' : -1 < z.re := hz
  refine DifferentiableAt.differentiableWithinAt ?_
  have hζ : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (z + 2)) z := by
    refine (differentiableAt_riemannZeta fun h => ?_).comp z (differentiableAt_id.add_const 2)
    have := congrArg Complex.re h; simp at this; linarith
  have hΓ : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma ((z + 2) / 2)) z := by
    refine (Complex.differentiableAt_Gamma _ fun m h => ?_).comp z
      ((differentiableAt_id.add_const 2).div_const 2)
    have := congrArg Complex.re h
    simp at this
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hΓ3 : DifferentiableAt ℂ (fun z : ℂ => (Complex.Gamma ((z + 3) / 2))⁻¹) z :=
    Complex.differentiable_one_div_Gamma.differentiableAt.comp z
      ((differentiableAt_id.add_const 3).div_const 2)
  have hfun : transferMultiplierH = fun z => ((2 * Real.sqrt Real.pi)⁻¹ : ℂ) * riemannZeta (z + 2) *
      Complex.Gamma ((z + 2) / 2) * (Complex.Gamma ((z + 3) / 2))⁻¹ * (z + 1) * (z + 2) := by
    funext z; simp only [transferMultiplierH, transferMultiplier, div_eq_mul_inv]
  rw [hfun]
  exact (((((differentiableAt_const _).mul hζ).mul hΓ).mul hΓ3).mul
    (differentiableAt_id.add_const 1)).mul (differentiableAt_id.add_const 2)

/-- **(8b) `H` has no zero on `Re z > −1`.** -/
theorem transferMultiplierH_ne_zero {z : ℂ} (hz : -1 < z.re) : transferMultiplierH z ≠ 0 := by
  rw [transferMultiplierH_eq hz]
  refine div_ne_zero ?_ (commutatorGammaFactor_ne_zero (by linarith))
  have h1 : z + 2 ≠ 1 := fun h => by have := congrArg Complex.re h; simp at this; linarith
  rw [Ne, xi_eq_zero_iff (by simp; linarith) h1]
  exact riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)

theorem meromorphicAt_riemannZeta_one_add (x : ℂ) : MeromorphicAt (fun z => riemannZeta (1 + z)) x := by
  have := meromorphicAt_riemannZeta_add 1 x
  simpa only [add_comm] using this

/-- **(8c) Pole transport.**  At every point of `Re z > −1` the continuations of the two boundary
transforms `ξ(z+2)/ζ(1+z)` and `−G(z)/ζ(1+z)` have the same meromorphic order: each hypothetical
pole of `1/ζ(1+z)` passes between the two currents with unchanged location and order. -/
theorem meromorphicOrderAt_reflected_eq_cutoff {z₀ : ℂ} (hz₀ : -1 < z₀.re) :
    meromorphicOrderAt (fun z => xi (z + 2) * (riemannZeta (1 + z))⁻¹) z₀ =
      meromorphicOrderAt (fun z => -(commutatorGammaFactor z * (riemannZeta (1 + z))⁻¹)) z₀ := by
  have hopen : {z : ℂ | -1 < z.re} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz₀
  have hH : AnalyticAt ℂ transferMultiplierH z₀ := differentiableOn_transferMultiplierH.analyticAt hopen
  have hmero : MeromorphicAt (fun z => -(commutatorGammaFactor z * (riemannZeta (1 + z))⁻¹)) z₀ :=
    ((analyticAt_commutatorGammaFactor (by linarith)).meromorphicAt.mul
      (meromorphicAt_riemannZeta_one_add z₀).inv).neg
  have hcongr : (fun z => xi (z + 2) * (riemannZeta (1 + z))⁻¹) =ᶠ[𝓝[≠] z₀]
      (-transferMultiplierH) * fun z => -(commutatorGammaFactor z * (riemannZeta (1 + z))⁻¹) := by
    filter_upwards [nhdsWithin_le_nhds hopen] with z hz
    simp only [Pi.mul_apply, Pi.neg_apply]
    rw [xi_add_two_eq_transferMultiplier hz, transferMultiplierH]
    ring
  rw [meromorphicOrderAt_congr hcongr, meromorphicOrderAt_mul hH.neg.meromorphicAt hmero,
    meromorphicOrderAt_eq_zero_of_analyticAt hH.neg (neg_ne_zero.2 (transferMultiplierH_ne_zero hz₀)),
    zero_add]

/-! ## (9) The three-frame resonance identity -/

/-- The analytic correction `E = H_causal − K` of the causal frame. -/
def causalFrameCorrection (w : ℂ) : ℂ := causalTailCorrection w - thetaHalfLaplace w

theorem differentiable_causalFrameCorrection : Differentiable ℂ causalFrameCorrection :=
  differentiable_causalTailCorrection.sub differentiable_thetaHalfLaplace

/-- The causal half-line identity `ℒ_t B(w) = K(w)(1/ζ(w+1/2) − 1) − E(w)`, `Re w > 1/2`. -/
theorem causalTailMellin_eq_frame {w : ℂ} (hw : 1 / 2 < w.re) :
    causalTailMellin w =
      thetaHalfLaplace w * ((riemannZeta (w + 1 / 2))⁻¹ - 1) - causalFrameCorrection w := by
  have := causalTailMellin_add_correction hw
  rw [causalFrameCorrection]
  linear_combination this

/-- **(9) Three-frame resonance identity.**
`ℒ_t B(w) = −[K(w)/G(w−1/2)] ℒC(w−1/2) − K(w) − E(w)` for `Re w > 1/2`. -/
theorem causalTailMellin_three_frame {w : ℂ} (hw : 1 / 2 < w.re) :
    causalTailMellin w = -(thetaHalfLaplace w / commutatorGammaFactor (w - 1 / 2)) *
        (∫ y : ℝ, Complex.exp ((w - 1 / 2) * y) * (cofinalBoundaryProfile y : ℂ)) -
      thetaHalfLaplace w - causalFrameCorrection w := by
  rw [(integral_cexp_mul_cofinalBoundaryProfile (z := w - 1 / 2) (by simp; linarith)).2,
    show 1 + (w - 1 / 2) = w + 1 / 2 by ring, causalTailMellin_eq_frame hw]
  have hG := commutatorGammaFactor_ne_zero (z := w - 1 / 2) (by simp; linarith)
  set g := commutatorGammaFactor (w - 1 / 2)
  have key : thetaHalfLaplace w / g * (g * (riemannZeta (w + 1 / 2))⁻¹) =
      thetaHalfLaplace w * (riemannZeta (w + 1 / 2))⁻¹ := by
    field_simp
  linear_combination -key

/-- The meromorphic continuation of the causal-frame transform. -/
def causalFrameContinuation (w : ℂ) : ℂ :=
  thetaHalfLaplace w * ((riemannZeta (w + 1 / 2))⁻¹ - 1) - causalFrameCorrection w

theorem causalTailMellin_eq_continuation {w : ℂ} (hw : 1 / 2 < w.re) :
    causalTailMellin w = causalFrameContinuation w :=
  causalTailMellin_eq_frame hw

theorem meromorphicOrderAt_riemannZeta_pos_ne_top {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ ≠ 1) :
    0 < meromorphicOrderAt riemannZeta ρ ∧ meromorphicOrderAt riemannZeta ρ ≠ ⊤ := by
  have hdiff : DifferentiableOn ℂ riemannZeta {(1 : ℂ)}ᶜ := fun z hz =>
    (differentiableAt_riemannZeta hz).differentiableWithinAt
  have hζan : AnalyticAt ℂ riemannZeta ρ := hdiff.analyticAt (isOpen_compl_singleton.mem_nhds h1)
  have hfin : meromorphicOrderAt riemannZeta ρ ≠ ⊤ := by
    rw [← meromorphicOrderAt_xi_eq_riemannZeta h0 h1, Ne, meromorphicOrderAt_eq_top_iff]
    intro htop
    obtain ⟨z, hz1, hz2⟩ := (htop.and (eventually_xi_ne_zero ρ)).exists
    exact hz2 hz1
  refine ⟨?_, hfin⟩
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := analyticOrderAt_ne_zero.2 ⟨hζan, hρ⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℕ∞) = analyticOrderAt riemannZeta ρ := by
    refine ENat.ne_top_iff_exists.1 fun htop => hfin ?_
    rw [hζan.meromorphicOrderAt_eq, htop]
    rfl
  rw [hζan.meromorphicOrderAt_eq, ← hk, ENat.map_coe]
  have : k ≠ 0 := by rintro rfl; exact hne hk.symm
  exact_mod_cast Nat.pos_of_ne_zero this

/-- **No analytic correction hides an off-line pole.**  At a hypothetical zero `ρ` of `ζ` with
`1/2 < Re ρ < 1`, the continued causal-frame transform has a genuine pole at `ρ − 1/2` whose order is
the multiplicity of `ρ`. -/
theorem meromorphicOrderAt_causalFrameContinuation {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h1 : 1 / 2 < ρ.re) (h2 : ρ.re < 1) :
    meromorphicOrderAt causalFrameContinuation (ρ - 1 / 2) = -meromorphicOrderAt riemannZeta ρ ∧
      meromorphicOrderAt causalFrameContinuation (ρ - 1 / 2) < 0 := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h2; simp at h2
  obtain ⟨hpos, hfin⟩ := meromorphicOrderAt_riemannZeta_pos_ne_top hρ (by linarith) hρ1
  set m := meromorphicOrderAt riemannZeta ρ
  have hK : AnalyticAt ℂ thetaHalfLaplace (ρ - 1 / 2) :=
    differentiable_thetaHalfLaplace.differentiableOn.analyticAt univ_mem
  have hK0 : thetaHalfLaplace (ρ - 1 / 2) ≠ 0 := thetaHalfLaplace_ne_zero_of_riemannZeta_eq_zero hρ h1 h2
  have hfirst : meromorphicOrderAt (fun w => thetaHalfLaplace w * (riemannZeta (w + 1 / 2))⁻¹)
      (ρ - 1 / 2) = -m := by
    have hinv : meromorphicOrderAt (fun w => riemannZeta (w + 1 / 2))⁻¹ (ρ - 1 / 2) = -m := by
      rw [meromorphicOrderAt_inv, meromorphicOrderAt_riemannZeta_comp_add, sub_add_cancel]
    rw [show (fun w => thetaHalfLaplace w * (riemannZeta (w + 1 / 2))⁻¹) =
        thetaHalfLaplace * (fun w => riemannZeta (w + 1 / 2))⁻¹ from rfl,
      meromorphicOrderAt_mul hK.meromorphicAt (meromorphicAt_riemannZeta_add _ _).inv,
      meromorphicOrderAt_eq_zero_of_analyticAt hK hK0, hinv, zero_add]
  have hrest : AnalyticAt ℂ (fun w => -thetaHalfLaplace w - causalFrameCorrection w) (ρ - 1 / 2) :=
    ((differentiable_thetaHalfLaplace.neg.sub differentiable_causalFrameCorrection).differentiableOn).analyticAt
      univ_mem
  have hdecomp : causalFrameContinuation =
      (fun w => thetaHalfLaplace w * (riemannZeta (w + 1 / 2))⁻¹) +
        fun w => -thetaHalfLaplace w - causalFrameCorrection w := by
    funext w; simp only [causalFrameContinuation, Pi.add_apply]; ring
  have hneg : -m < 0 := by
    obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hfin
    rw [← hk] at hpos ⊢
    have : (0 : ℤ) < k := by exact_mod_cast hpos
    exact_mod_cast (neg_neg_of_pos this)
  have hlt : -m < meromorphicOrderAt (fun w => -thetaHalfLaplace w - causalFrameCorrection w) (ρ - 1 / 2) :=
    hneg.trans_le hrest.meromorphicOrderAt_nonneg
  have heq : meromorphicOrderAt causalFrameContinuation (ρ - 1 / 2) = -m := by
    rw [hdecomp, meromorphicOrderAt_add_eq_left_of_lt hrest.meromorphicAt (hfirst ▸ hlt), hfirst]
  exact ⟨heq, heq ▸ hneg⟩

end

end RHTower
