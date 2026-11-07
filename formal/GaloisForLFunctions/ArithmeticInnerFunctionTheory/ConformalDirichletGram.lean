import GaloisForLFunctions.ArithmeticInnerFunctionTheory.ConformalDirichletProjection
import GaloisForLFunctions.ArithmeticInnerFunctionTheory.MollifiedLogDilationBridge

/-! # Dirichlet Gram energy after conformal projection

Dirichlet coefficients enter the Poisson Gram form through the Abel kernel `1/max(m,n)`.
Conformal projection removes exactly the squared Laguerre moments from this energy.
Polynomial exponentials on fixed or translated charts have absolutely summable Taylor
coefficients. Their Gram entries and their pairings with Dirichlet modes are exact coefficient
series. Chart translation and Dirichlet translation are kept as independent parameters.
-/

open Complex Metric Filter Topology MeasureTheory Set Finset
open scoped Real ComplexConjugate NNReal

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open _root_.RHTower

noncomputable section

/-- The critical zeta budget has an exact conformal projection remainder. Its coefficients
belong to the product with the zeta datum, rather than to the mollifier alone. -/
theorem budget_conformal_projection_remainder (Q : Polynomial ℂ) (N : ℕ) :
    Real.circleAverage (fun z =>
      ‖mollified Q z - ∑ k ∈ Finset.range N, z ^ k * taylorCoeff (mollified Q) k‖ ^ 2) 0 1 =
      budget 1 Q - ∑ k ∈ Finset.range N, ‖taylorCoeff (mollified Q) k‖ ^ 2 := by
  rw [(isHardyDisc_mollified Q).projection_remainder,
    (integrable_and_circleAverage_mollified Q).2]

/-- A shifted budget keeps the conformal chart fixed and translates only its zeta weight. -/
theorem shiftedBudget_eq_circleAverage (δ : ℝ) (Q : Polynomial ℂ) :
    shiftedBudget δ 1 Q = Real.circleAverage (fun z =>
      shiftedChartWeight δ 1 z * ‖Complex.exp (Q.eval z)‖ ^ 2) 0 1 := by
  have hc := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun τ => ‖riemannZeta (1 / 2 + (δ : ℂ) + (τ : ℂ) * I)‖ ^ 2 *
      ‖Complex.exp (Q.eval (blaschkeCoord 1 (1 / 2 + (τ : ℂ) * I)))‖ ^ 2)
    (fun z => shiftedChartWeight δ 1 z * ‖Complex.exp (Q.eval z)‖ ^ 2)
    (fun τ => by
      have hb := blaschkeCoord_line (w := 1) (by norm_num) τ
      norm_num at hb
      simp only [shiftedChartWeight, discChart_circleMap]
      norm_num
      rw [hb]
      congr 4
      ring)
  exact hc.2.symm

/-- A shifted Dirichlet polynomial expressed on the fixed unit disc. -/
def dirichletDiscPoly (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) (z : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M, ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ) * dirichletDisc (Real.log m) z

theorem norm_dirichletDiscPoly_le (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖dirichletDiscPoly M b δ z‖ ≤ ∑ m ∈ Finset.Icc 1 M, |b m * (m : ℝ) ^ (-δ)| := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _)
    (norm_dirichletDisc_le_one (Real.log_nonneg hm1) hz)

theorem isHardyDisc_dirichletDiscPoly (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) :
    IsHardyDisc (dirichletDiscPoly M b δ) := by
  apply isHardyDisc_of_bounded (M := ∑ m ∈ Finset.Icc 1 M, |b m * (m : ℝ) ^ (-δ)|)
  · intro z hz
    have hd (m : ℕ) : DifferentiableAt ℂ
        (fun u => ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ) * dirichletDisc (Real.log m) u) z :=
      (differentiableAt_dirichletDisc _ hz).const_mul _
    exact (DifferentiableAt.fun_sum (fun m _ => hd m)).differentiableWithinAt
  · unfold dirichletDiscPoly
    exact Finset.measurable_fun_sum _ fun m _ => measurable_const.mul (measurable_dirichletDisc _)
  · exact fun _ hz => norm_dirichletDiscPoly_le M b δ hz

theorem dirichletLineMode_log_eq_cpow {m : ℕ} (hm : 1 ≤ m) (δ τ : ℝ) :
    dirichletLineMode (Real.log m) δ τ = (m : ℂ) ^ (-(1 / 2 + (δ : ℂ) + (τ : ℂ) * I)) := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hmne : (m : ℂ) ≠ 0 := by exact_mod_cast hmpos.ne'
  rw [Complex.cpow_def_of_ne_zero hmne, ← Complex.ofReal_natCast, ← Complex.ofReal_log hmpos.le,
    dirichletLineMode]
  congr 1
  ring

theorem dirichletDiscPoly_circleMap (M : ℕ) (b : ℕ → ℝ) (δ τ : ℝ) :
    dirichletDiscPoly M b δ (circleMap 0 1 (criticalLineAngle τ)) =
      realDirichletPoly M b (1 / 2 + (δ : ℂ) + (τ : ℂ) * I) := by
  unfold dirichletDiscPoly realDirichletPoly
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm1 := (Finset.mem_Icc.mp hm).1
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have he : (m : ℝ) ^ (-δ) = Real.exp (-δ * Real.log m) := by
    rw [Real.rpow_def_of_pos hmpos]
    congr 1
    ring
  rw [dirichletDisc_circleMap, he, Complex.ofReal_mul, mul_assoc,
    ← dirichletLineMode_shift, dirichletLineMode_log_eq_cpow hm1]

/-- The shifted finite Dirichlet polynomial has exactly the Abel Gram energy. -/
theorem circleAverage_norm_sq_dirichletDiscPoly (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) :
    Real.circleAverage (fun z => ‖dirichletDiscPoly M b δ z‖ ^ 2) 0 1 =
      ∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) / (max m n : ℝ) := by
  have hc := circleAverage_shift_eq_poisson (s0 := 1) (by norm_num)
    (fun τ => ‖realDirichletPoly M b (1 / 2 + (δ : ℂ) + (τ : ℂ) * I)‖ ^ 2)
    (fun z => ‖dirichletDiscPoly M b δ z‖ ^ 2)
    (fun τ => by rw [dirichletDiscPoly_circleMap]; norm_num)
  rw [hc.2, integral_dirichletPoly_norm_sq_poisson]

/-- The conformal moments of a Dirichlet polynomial are finite sums of explicit Laguerre jets. -/
theorem taylorCoeff_dirichletDiscPoly (M : ℕ) (b : ℕ → ℝ) (δ : ℝ) (k : ℕ) :
    taylorCoeff (dirichletDiscPoly M b δ) k =
      ∑ m ∈ Finset.Icc 1 M, ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ) *
        (Complex.exp (-(Real.log m : ℂ)) *
          (laguerreJetPoly (Real.log m) k).eval 1 / (k.factorial : ℂ)) := by
  have hlog (m : ℕ) (hm : m ∈ Finset.Icc 1 M) : 0 ≤ Real.log m :=
    Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp hm).1)
  rw [← (isHardyDisc_dirichletDiscPoly M b δ).circleAverage_conj_pow_mul k]
  have he : (fun z => conj (z ^ k) * dirichletDiscPoly M b δ z) =
      fun z => ∑ m ∈ Finset.Icc 1 M, ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ) *
        (conj (z ^ k) * dirichletDisc (Real.log m) z) := by
    funext z
    simp only [dirichletDiscPoly, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hint (m : ℕ) (hm : m ∈ Finset.Icc 1 M) :
      CircleIntegrable (fun z => ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ) *
        (conj (z ^ k) * dirichletDisc (Real.log m) z)) 0 1 :=
    ((isHardyDisc_dirichletDisc (hlog m hm)).circleIntegrable_conj_pow_mul k).const_smul
      (a := ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ))
  rw [he, Real.circleAverage_fun_sum hint]
  refine Finset.sum_congr rfl fun m hm => ?_
  change Real.circleAverage (fun z => ((b m * (m : ℝ) ^ (-δ) : ℝ) : ℂ) •
    (conj (z ^ k) * dirichletDisc (Real.log m) z)) 0 1 = _
  rw [Real.circleAverage_fun_smul,
    (isHardyDisc_dirichletDisc (hlog m hm)).circleAverage_conj_pow_mul,
    taylorCoeff_dirichletDisc, smul_eq_mul]

/-- Conformal projection subtracts a positive sum of squares from the exact Dirichlet Gram form. -/
theorem dirichletGram_minus_conformal_squares (M N : ℕ) (b : ℕ → ℝ) (δ : ℝ) :
    Real.circleAverage (fun z =>
      ‖dirichletDiscPoly M b δ z -
        ∑ k ∈ Finset.range N, z ^ k * taylorCoeff (dirichletDiscPoly M b δ) k‖ ^ 2) 0 1 =
      (∑ m ∈ Finset.Icc 1 M, ∑ n ∈ Finset.Icc 1 M,
        (b m * (m : ℝ) ^ (-δ)) * (b n * (n : ℝ) ^ (-δ)) / (max m n : ℝ)) -
      ∑ k ∈ Finset.range N, ‖taylorCoeff (dirichletDiscPoly M b δ) k‖ ^ 2 := by
  rw [(isHardyDisc_dirichletDiscPoly M b δ).projection_remainder,
    circleAverage_norm_sq_dirichletDiscPoly]

/-- Abel partial sums dominate every finite set of conformal moments of the same polynomial. -/
theorem conformal_squares_le_abel {M : ℕ} (hM : 1 ≤ M) (N : ℕ) (b : ℕ → ℝ) (δ : ℝ) :
    ∑ k ∈ Finset.range N, ‖taylorCoeff (dirichletDiscPoly M b δ) k‖ ^ 2 ≤
      (∑ m ∈ Finset.Icc 1 M, b m * (m : ℝ) ^ (-δ)) ^ 2 / (M : ℝ) +
        ∑ j ∈ Finset.Icc 1 (M - 1),
          (((j : ℝ)⁻¹ - ((j + 1 : ℕ) : ℝ)⁻¹) *
            (∑ m ∈ Finset.Icc 1 j, b m * (m : ℝ) ^ (-δ)) ^ 2) := by
  have h := (isHardyDisc_dirichletDiscPoly M b δ).sum_norm_sq_le N
  rw [circleAverage_norm_sq_dirichletDiscPoly,
    dirichletGram_eq_abel_squares hM] at h
  exact h

/-- A conformal polynomial exponential, with an independent chart translation. -/
def conformalDiscExp (Q : Polynomial ℂ) (η : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Q.eval (translatedDiscCoord η z))

theorem conformalDiscExp_circleMap (Q : Polynomial ℂ) (η τ : ℝ) :
    conformalDiscExp Q η (circleMap 0 1 (criticalLineAngle τ)) =
      polyMollifier 1 Q (1 / 2 + (η : ℂ) + (τ : ℂ) * I) := by
  rw [conformalDiscExp, translatedDiscCoord_circleMap, polyMollifier]

/-- Each translated chart exponential is holomorphic on a disc strictly larger than the unit disc. -/
theorem conformalDiscExp_larger_disc (Q : Polynomial ℂ) {η : ℝ} (hη : 0 ≤ η) :
    ∃ R : ℝ≥0, 1 < (R : ℝ) ∧
      DifferentiableOn ℂ (conformalDiscExp Q η) (closedBall 0 R) := by
  let d : ℝ := 2 * (η + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  let r : ℝ := 1 + d⁻¹
  have hr : 1 < r := by dsimp [r]; linarith [inv_pos.mpr hd]
  let R : ℝ≥0 := ⟨r, by linarith⟩
  refine ⟨R, hr, ?_⟩
  intro z hz
  have hzre : z.re ≤ r := by
    change z.re ≤ (R : ℝ)
    exact (Complex.re_le_norm z).trans (by
      simpa only [mem_closedBall, dist_zero_right] using hz)
  have hden : 1 + (η : ℂ) - (η : ℂ) * z ≠ 0 := by
    intro he
    have heR := congrArg Complex.re he
    simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, zero_mul, sub_zero, Complex.zero_re] at heR
    have hb : η * z.re ≤ η + η / d := by
      calc η * z.re ≤ η * r := mul_le_mul_of_nonneg_left hzre hη
        _ = η + η / d := by dsimp [r]; ring
    have hfrac : η / d < 1 := (div_lt_one hd).mpr (by dsimp [d]; linarith)
    linarith
  have hψ : DifferentiableAt ℂ (translatedDiscCoord η) z := by
    have hnum : DifferentiableAt ℂ (fun u : ℂ => (η : ℂ) + (1 - (η : ℂ)) * u) z := by
      fun_prop
    have hden' : DifferentiableAt ℂ (fun u : ℂ => 1 + (η : ℂ) - (η : ℂ) * u) z := by
      fun_prop
    exact hnum.div hden' hden
  exact (Complex.differentiable_exp.differentiableAt.comp z
    (Q.differentiable.differentiableAt.comp z hψ)).differentiableWithinAt

theorem conformalDiscExp_differentiableOn (Q : Polynomial ℂ) {η : ℝ} (hη : 0 ≤ η) :
    DifferentiableOn ℂ (conformalDiscExp Q η) (closedBall 0 1) := by
  obtain ⟨R, hR, hd⟩ := conformalDiscExp_larger_disc Q hη
  exact hd.mono (closedBall_subset_closedBall hR.le)

theorem conformalDiscExp_summable_taylor (Q : Polynomial ℂ) {η : ℝ} (hη : 0 ≤ η) :
    Summable (fun k => ‖taylorCoeff (conformalDiscExp Q η) k‖) ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 →
        HasSum (fun k => z ^ k * taylorCoeff (conformalDiscExp Q η) k) (conformalDiscExp Q η z) := by
  obtain ⟨R, hR, hd⟩ := conformalDiscExp_larger_disc Q hη
  exact summable_taylor_of_larger_disc hR hd

/-- Exact Gram matrix of conformal polynomial exponentials, including translated charts. -/
theorem hasSum_polyMollifier_gram (Q R : Polynomial ℂ) {η ξ : ℝ} (hη : 0 ≤ η) (hξ : 0 ≤ ξ) :
    HasSum (fun k => conj (taylorCoeff (conformalDiscExp Q η) k) *
      taylorCoeff (conformalDiscExp R ξ) k)
      (∫ τ : ℝ, conj (polyMollifier 1 Q (1 / 2 + (η : ℂ) + (τ : ℂ) * I)) *
        polyMollifier 1 R (1 / 2 + (ξ : ℂ) + (τ : ℂ) * I) *
          (halfPlanePoissonKernel 1 τ : ℂ)) := by
  have hdQ := conformalDiscExp_differentiableOn Q hη
  have hdR := conformalDiscExp_differentiableOn R hξ
  have hcQ := hdQ.continuousOn.mono sphere_subset_closedBall
  have hcR := hdR.continuousOn.mono sphere_subset_closedBall
  have hiR : CircleIntegrable (conformalDiscExp R ξ) 0 1 := hcR.circleIntegrable zero_le_one
  obtain ⟨ha, hsum⟩ := conformalDiscExp_summable_taylor Q hη
  have hs := hasSum_circleAverage_conj_series_mul hiR ha (fun z hz => hsum z hz.le)
  simp only [circleAverage_conj_pow_mul_of_differentiableOn hdR] at hs
  have hconj : ContinuousOn (fun z => conj (conformalDiscExp Q η z)) (sphere 0 1) :=
    Complex.conjCLE.continuous.comp_continuousOn hcQ
  have hprod : CircleIntegrable (fun z => conj (conformalDiscExp Q η z) * conformalDiscExp R ξ z) 0 1 :=
    hiR.mul_of_continuousOn (by simpa only [abs_one] using hconj)
  have hchange := circleAverage_complex_eq_poisson
    (F := fun τ => conj (polyMollifier 1 Q (1 / 2 + (η : ℂ) + (τ : ℂ) * I)) *
      polyMollifier 1 R (1 / 2 + (ξ : ℂ) + (τ : ℂ) * I)) hprod (fun τ => by
    rw [conformalDiscExp_circleMap Q η, conformalDiscExp_circleMap R ξ])
  rwa [hchange.2] at hs

/-- Exact conformal-exponential/Dirichlet cross Gram matrix. The chart shift `η` and the
Dirichlet shift `δ` are independent; the fixed-chart budgets use `η=0`. -/
theorem hasSum_polyMollifier_dirichlet (Q : Polynomial ℂ) {η t : ℝ}
    (hη : 0 ≤ η) (ht : 0 ≤ t) (δ : ℝ) :
    HasSum (fun k => conj (taylorCoeff (conformalDiscExp Q η) k) *
      ((Real.exp (-δ * t) : ℂ) *
        (Complex.exp (-(t : ℂ)) * (laguerreJetPoly t k).eval 1 / (k.factorial : ℂ))))
      (∫ τ : ℝ, conj (polyMollifier 1 Q (1 / 2 + (η : ℂ) + (τ : ℂ) * I)) *
        dirichletLineMode t δ τ * (halfPlanePoissonKernel 1 τ : ℂ)) := by
  obtain ⟨ha, hsum⟩ := conformalDiscExp_summable_taylor Q hη
  have hD := isHardyDisc_dirichletDisc ht
  have hs := hD.hasSum_conj_taylor_mul ha (fun z hz => hsum z hz.le)
  have hc := (conformalDiscExp_differentiableOn Q hη).continuousOn.mono sphere_subset_closedBall
  have hconj : ContinuousOn (fun z => conj (conformalDiscExp Q η z)) (sphere 0 1) :=
    Complex.conjCLE.continuous.comp_continuousOn hc
  have hprod : CircleIntegrable (fun z => conj (conformalDiscExp Q η z) * dirichletDisc t z) 0 1 :=
    hD.circleIntegrable.mul_of_continuousOn (by simpa only [abs_one] using hconj)
  have hchange := circleAverage_complex_eq_poisson
    (F := fun τ => conj (polyMollifier 1 Q (1 / 2 + (η : ℂ) + (τ : ℂ) * I)) *
      dirichletLineMode t 0 τ) hprod (fun τ => by
    rw [conformalDiscExp_circleMap Q η, dirichletDisc_circleMap])
  rw [hchange.2] at hs
  have he : (fun τ : ℝ => conj (polyMollifier 1 Q (1 / 2 + (η : ℂ) + (τ : ℂ) * I)) *
      dirichletLineMode t δ τ * (halfPlanePoissonKernel 1 τ : ℂ)) =
      fun τ : ℝ => (Real.exp (-δ * t) : ℂ) *
        (conj (polyMollifier 1 Q (1 / 2 + (η : ℂ) + (τ : ℂ) * I)) *
          dirichletLineMode t 0 τ * (halfPlanePoissonKernel 1 τ : ℂ)) := by
    funext τ
    rw [dirichletLineMode_shift]
    ring
  rw [he, integral_const_mul]
  exact (hs.mul_left (Real.exp (-δ * t) : ℂ)).congr_fun fun k => by
    rw [taylorCoeff_dirichletDisc]
    ring

/-- Outer conformal factors change the logarithmic dilation integral only by their centre values. -/
theorem conformal_log_dilation_eq_centres (Q : Polynomial ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∫ τ : ℝ,
      (Real.log ‖polyMollifier 1 Q (1 / 2 + (τ : ℂ) * I)‖ -
        Real.log ‖polyMollifier 1 Q (1 / 2 + (δ : ℂ) + (τ : ℂ) * I)‖) *
          halfPlanePoissonKernel 1 τ) =
      (Q.eval 0).re - (Q.eval ((δ : ℂ) / (1 + (δ : ℂ)))).re := by
  have h0 := integral_log_polyMollifier_shifted Q (δ := 0) le_rfl
  have h1 := integral_log_polyMollifier_shifted Q hδ
  simp only [Complex.ofReal_zero, add_zero, zero_div] at h0
  simp_rw [sub_mul]
  rw [integral_sub h0.1 h1.1, h0.2, h1.2]

/-- Centre normalization cancels the entire logarithmic contribution of a conformal factor. -/
theorem conformal_normalized_log_dilation_eq_zero (Q : Polynomial ℂ) {δ : ℝ}
    (hδ : 0 ≤ δ) :
    (∫ τ : ℝ,
      (Real.log ‖polyMollifier 1 Q (1 / 2 + (τ : ℂ) * I)‖ -
        Real.log ‖polyMollifier 1 Q (1 / 2 + (δ : ℂ) + (τ : ℂ) * I)‖) *
          halfPlanePoissonKernel 1 τ) +
      Real.log ‖polyMollifier 1 Q (1 + (δ : ℂ))‖ -
      Real.log ‖polyMollifier 1 Q 1‖ = 0 := by
  have hcentre : blaschkeCoord 1 (1 + (δ : ℂ)) = (δ : ℂ) / (1 + (δ : ℂ)) := by
    rw [blaschkeCoord_one]
    congr 1
    ring
  have hzero : blaschkeCoord 1 1 = 0 := by rw [blaschkeCoord_one]; norm_num
  rw [conformal_log_dilation_eq_centres Q hδ]
  simp only [polyMollifier, Complex.norm_exp, Real.log_exp, hcentre, hzero]
  ring

#print axioms dirichletGram_minus_conformal_squares
#print axioms budget_conformal_projection_remainder
#print axioms shiftedBudget_eq_circleAverage
#print axioms conformal_squares_le_abel
#print axioms taylorCoeff_dirichletDiscPoly
#print axioms hasSum_polyMollifier_gram
#print axioms hasSum_polyMollifier_dirichlet
#print axioms conformal_log_dilation_eq_centres
#print axioms conformal_normalized_log_dilation_eq_zero

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
