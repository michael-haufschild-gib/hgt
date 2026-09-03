import GaloisForLFunctions.RHTower.SemilocalBoostRowTaylorIdentification
import GaloisForLFunctions.RHTower.SemilocalCosineModeFirstOrderResponse
import GaloisForLFunctions.HTGeometry.CentralBinomialSeries

/-!
# Closed form of the diagonal boost matrix elements

Evaluating the Taylor coefficients of the closed row function
`R_m(z) = K_m (z + iτ)^m (1 − iτz)^{−(m+1/2)}` by the Leibniz rule and specializing to the diagonal
`m = n` gives

`M_{nn}(t) = ∫ p_n² e^{its} dμ = (cosh t)^{-1/2} Σ_{l ≤ n} C(n,l) · ((−(n+½)) choose l) · tanh^{2l} t`,

i.e. `m_n(t) = (cosh t)^{-1/2} ₂F₁(−n, n+½; 1; tanh² t) = (cosh t)^{-1/2} P_n^{(0,−1/2)}(1 − 2 tanh² t)`
(the Pochhammer form of the generalized binomial coefficient).  The real part is the diagonal cosine
moment `cosineDiagonalMoment` of the first-order response module, so the Route J profile derivation
now has its analytic input in Lean.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

namespace MeixnerPollaczek

open GaloisForLFunctions.HTGeometry

/-! ## The two factors of the closed row function -/

noncomputable def rowPolyFactor (t : ℝ) (m : ℕ) (z : ℂ) : ℂ := (z + I * (Real.tanh t : ℂ)) ^ m

noncomputable def rowPowerFactor (t : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  (1 - I * (Real.tanh t : ℂ) * z) ^ (-((m : ℂ) + 1 / 2))

noncomputable def rowConstant (t : ℝ) (m : ℕ) : ℂ :=
  ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (Ring.choose (-(1 / 2 : ℂ)) m * (-1) ^ m / (semilocalArchimedeanJacobiNormalization m : ℂ))

theorem boostRowClosed_eq_factors (t : ℝ) (m : ℕ) :
    boostRowClosed t m = fun z => rowConstant t m * (rowPolyFactor t m z * rowPowerFactor t m z) := by
  funext z
  rfl

theorem contDiffAt_rowPolyFactor (t : ℝ) (m : ℕ) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (rowPolyFactor t m) 0 := by
  unfold rowPolyFactor
  fun_prop

theorem differentiableOn_rowPowerFactor (t : ℝ) (m : ℕ) :
    DifferentiableOn ℂ (rowPowerFactor t m) (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa using hz
  apply DifferentiableAt.differentiableWithinAt
  have h : DifferentiableAt ℂ (fun w : ℂ => 1 - I * (Real.tanh t : ℂ) * w) z :=
    (differentiableAt_id.const_mul _).const_sub 1
  exact h.cpow_const (one_sub_I_tanh_mul_mem_slitPlane t hz')

theorem contDiffAt_rowPowerFactor (t : ℝ) (m : ℕ) (n : WithTop ℕ∞) :
    ContDiffAt ℂ n (rowPowerFactor t m) 0 :=
  ((differentiableOn_rowPowerFactor t m).contDiffOn Metric.isOpen_ball).contDiffAt
    (Metric.ball_mem_nhds _ one_pos)

theorem iteratedDeriv_rowPolyFactor_zero (t : ℝ) (m i : ℕ) :
    iteratedDeriv i (rowPolyFactor t m) 0 =
      i.factorial * (if i ≤ m then (m.choose i : ℂ) * (I * (Real.tanh t : ℂ)) ^ (m - i) else 0) :=
  iteratedDeriv_add_const_pow_zero (I * (Real.tanh t : ℂ)) m i

theorem iteratedDeriv_rowPowerFactor_zero (t : ℝ) (m k : ℕ) :
    iteratedDeriv k (rowPowerFactor t m) 0 =
      k.factorial * (Ring.choose (-((m : ℂ) + 1 / 2)) k * (-(I * (Real.tanh t : ℂ))) ^ k) := by
  have hc : ‖I * (Real.tanh t : ℂ)‖ < 4 := by
    rw [norm_mul, norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith [Real.abs_tanh_lt_one t]
  exact iteratedDeriv_one_sub_mul_cpow_neg_zero ((m : ℂ) + 1 / 2) (I * (Real.tanh t : ℂ)) hc k

/-- **Leibniz evaluation of the Taylor coefficients of the closed row function.** -/
theorem iteratedDeriv_boostRowClosed_zero (t : ℝ) (m n : ℕ) :
    iteratedDeriv n (boostRowClosed t m) 0 =
      rowConstant t m * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        iteratedDeriv i (rowPolyFactor t m) 0 * iteratedDeriv (n - i) (rowPowerFactor t m) 0 := by
  rw [boostRowClosed_eq_factors,
    iteratedDeriv_const_mul _ ((contDiffAt_rowPolyFactor t m _).mul (contDiffAt_rowPowerFactor t m _))]
  rw [show (fun z => rowPolyFactor t m z * rowPowerFactor t m z) =
      rowPolyFactor t m * rowPowerFactor t m from rfl,
    iteratedDeriv_mul (contDiffAt_rowPolyFactor t m _) (contDiffAt_rowPowerFactor t m _)]

/-! ## The central binomial normalization -/

theorem centralBinom_div_four_pow_eq_normalization_sq (n : ℕ) :
    (Nat.centralBinom n : ℝ) / 4 ^ n = semilocalArchimedeanJacobiNormalization n ^ 2 := by
  rw [semilocalArchimedeanJacobiNormalization_sq]
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  rw [← Nat.centralBinom_eq_two_mul_choose, show 2 * n - n = n by omega] at h
  have h' : ((2 * n).factorial : ℝ) = Nat.centralBinom n * n.factorial * n.factorial := by
    exact_mod_cast h.symm
  rw [h', show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul]
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp
  ring

theorem ringChoose_neg_half_mul_neg_one_pow (n : ℕ) :
    Ring.choose (-(1 / 2 : ℂ)) n * (-1) ^ n = (semilocalArchimedeanJacobiNormalization n : ℂ) ^ 2 := by
  have h := ringChoose_neg_half n
  have hc : ((Ring.choose (-(1 : ℝ) / 2) n : ℝ) : ℂ) = Ring.choose (-(1 / 2 : ℂ)) n := by
    rw [Complex.ofReal_choose]
    push_cast
    ring_nf
  have h2 := centralBinom_div_four_pow_eq_normalization_sq n
  have h3 : Ring.choose (-(1 / 2 : ℂ)) n = (-1) ^ n * (semilocalArchimedeanJacobiNormalization n : ℂ) ^ 2 := by
    rw [← hc, h, mul_div_assoc, h2]
    push_cast
    ring
  rw [h3, mul_assoc, mul_comm ((semilocalArchimedeanJacobiNormalization n : ℂ) ^ 2), ← mul_assoc,
    ← mul_pow]
  simp

/-! ## The diagonal -/

/-- **Closed form of the diagonal boost matrix element:**
`∫ p_n² e^{its} dμ = (cosh t)^{-1/2} Σ_{l ≤ n} C(n,l) ((−(n+½)) choose l) tanh^{2l} t`. -/
theorem boostMatrixEntry_diag (t : ℝ) (n : ℕ) :
    boostMatrixEntry t n n = ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
      ∑ l ∈ Finset.range (n + 1), (n.choose l : ℂ) * Ring.choose (-((n : ℂ) + 1 / 2)) l *
        ((Real.tanh t : ℂ) ^ 2) ^ l := by
  set c : ℂ := (semilocalArchimedeanJacobiNormalization n : ℂ) with hcdef
  have hc : c ≠ 0 := by
    rw [hcdef]; exact_mod_cast (semilocalArchimedeanJacobiNormalization_pos n).ne'
  have hfacn : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  set τ : ℂ := (Real.tanh t : ℂ) with hτ
  have key := normalization_mul_boostMatrixEntry_eq t n n
  rw [iteratedDeriv_boostRowClosed_zero] at key
  have hsum : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
      iteratedDeriv i (rowPolyFactor t n) 0 * iteratedDeriv (n - i) (rowPowerFactor t n) 0 =
      (n.factorial : ℂ) * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
        Ring.choose (-((n : ℂ) + 1 / 2)) (n - i) * (τ ^ 2) ^ (n - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [iteratedDeriv_rowPolyFactor_zero, iteratedDeriv_rowPowerFactor_zero,
      if_pos (by omega : i ≤ n)]
    have hfac : (n.choose i : ℂ) * i.factorial * (n - i).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by omega : i ≤ n)
    have hpow : (I * τ) ^ (n - i) * (-(I * τ)) ^ (n - i) = (τ ^ 2) ^ (n - i) := by
      rw [← mul_pow]
      congr 1
      linear_combination (-(τ ^ 2)) * I_sq
    linear_combination ((n.choose i : ℂ) * Ring.choose (-((n : ℂ) + 1 / 2)) (n - i) *
        ((I * τ) ^ (n - i) * (-(I * τ)) ^ (n - i))) * hfac +
      ((n.choose i : ℂ) * Ring.choose (-((n : ℂ) + 1 / 2)) (n - i) * (n.factorial : ℂ)) * hpow
  rw [hsum] at key
  have hrefl : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℂ) *
      Ring.choose (-((n : ℂ) + 1 / 2)) (n - i) * (τ ^ 2) ^ (n - i) =
      ∑ l ∈ Finset.range (n + 1), (n.choose l : ℂ) * Ring.choose (-((n : ℂ) + 1 / 2)) l *
        (τ ^ 2) ^ l := by
    rw [← Finset.sum_range_reflect (fun l => (n.choose l : ℂ) *
      Ring.choose (-((n : ℂ) + 1 / 2)) l * (τ ^ 2) ^ l) (n + 1)]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [show n + 1 - 1 - i = n - i by omega]
    rw [Nat.choose_symm (by omega : i ≤ n)]
  rw [hrefl] at key
  have h2 : c * boostMatrixEntry t n n = rowConstant t n *
      ∑ l ∈ Finset.range (n + 1), (n.choose l : ℂ) * Ring.choose (-((n : ℂ) + 1 / 2)) l *
        (τ ^ 2) ^ l := by
    rw [key, mul_div_assoc, mul_div_cancel_left₀ _ hfacn]
  have hconst : rowConstant t n / c = ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    unfold rowConstant
    rw [ringChoose_neg_half_mul_neg_one_pow, ← hcdef]
    field_simp
  have hM : boostMatrixEntry t n n = (rowConstant t n / c) *
      ∑ l ∈ Finset.range (n + 1), (n.choose l : ℂ) * Ring.choose (-((n : ℂ) + 1 / 2)) l *
        (τ ^ 2) ^ l := by
    rw [div_mul_eq_mul_div, eq_div_iff hc, mul_comm, h2]
  rw [hM, hconst]

/-! ## The real diagonal cosine moment -/

theorem integrable_eval_mul_eval_mul_cexp (m n : ℕ) (t : ℝ) :
    Integrable (fun s : ℝ => (((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) *
      (((semilocalArchimedeanJacobiPolynomial n).eval s : ℝ) : ℂ) * cexp (((t * s : ℝ) : ℂ) * I))
      semilocalArchimedeanGammaMeasure := by
  have h := (integrable_eval_mul_eval_semilocalArchimedeanGammaMeasure
    (semilocalArchimedeanJacobiPolynomial m) (semilocalArchimedeanJacobiPolynomial n)).norm
  refine h.mono' ?_ ?_
  · exact (((Complex.continuous_ofReal.comp (Polynomial.continuous _)).mul
      (Complex.continuous_ofReal.comp (Polynomial.continuous _))).mul
      (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
        (continuous_const.mul continuous_id)).mul continuous_const))).aestronglyMeasurable
  · filter_upwards with s
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]

theorem cosineDiagonalMoment_eq_re_boostMatrixEntry (δ : ℝ) (n : ℕ) :
    CosineModeResponse.cosineDiagonalMoment δ n = (boostMatrixEntry δ n n).re := by
  unfold CosineModeResponse.cosineDiagonalMoment boostMatrixEntry
  have h := Complex.reCLM.integral_comp_comm (integrable_eval_mul_eval_mul_cexp n n δ)
  simp only [Complex.reCLM_apply] at h
  rw [← h]
  congr 1
  funext s
  rw [mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp [Complex.mul_re, Complex.mul_im]

/-- **Closed form of the diagonal cosine moments (real form):**
`∫ p_n² cos(δ s) dμ = (cosh δ)^{-1/2} Σ_{l ≤ n} C(n,l) ((−(n+½)) choose l) tanh^{2l} δ`, i.e.
`(cosh δ)^{-1/2} ₂F₁(−n, n+½; 1; tanh² δ)`. -/
theorem cosineDiagonalMoment_eq (δ : ℝ) (n : ℕ) :
    CosineModeResponse.cosineDiagonalMoment δ n =
      Real.cosh δ ^ (-(1 / 2 : ℝ)) * ∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) *
        Ring.choose (-((n : ℝ) + 1 / 2)) l * (Real.tanh δ ^ 2) ^ l := by
  rw [cosineDiagonalMoment_eq_re_boostMatrixEntry, boostMatrixEntry_diag]
  have hsum : (∑ l ∈ Finset.range (n + 1), (n.choose l : ℂ) * Ring.choose (-((n : ℂ) + 1 / 2)) l *
      ((Real.tanh δ : ℂ) ^ 2) ^ l) =
      ((∑ l ∈ Finset.range (n + 1), (n.choose l : ℝ) * Ring.choose (-((n : ℝ) + 1 / 2)) l *
        (Real.tanh δ ^ 2) ^ l : ℝ) : ℂ) := by
    push_cast
    try (apply Finset.sum_congr rfl; intro l _; rfl)
  rw [hsum, ← Complex.ofReal_mul, Complex.ofReal_re]

end MeixnerPollaczek

end RHTower
