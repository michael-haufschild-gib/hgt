import GaloisForLFunctions.RHTower.SemilocalBoostGeneratingFunctionClosedForm

/-!
# Boost matrix entries as Taylor coefficients of the closed row function

With `M_{mn}(t) = ∫ p_m p_n e^{its} dμ` and the row function `L_m(z) = ∫ G_s(z) p_m(s) e^{its} dμ`,
term-by-term integration gives `L_m(z) = Σ_n c_n M_{mn} z^n`, while the closed form of the boost
generating function gives, for real `z`,

`L_m(z) = R_m(z) := (cosh t)^{-1/2} · ((−1/2 choose m)(−1)^m / c_m) · (z + iτ)^m (1 − iτz)^{−(m+1/2)}`.

Real-axis uniqueness identifies `c_n M_{mn} = R_m^{(n)}(0)/n!`.  The Taylor coefficients of the two
factors `(z + iτ)^m` and `(1 − iτz)^{−(m+1/2)}` are recorded for the Leibniz evaluation.
-/

open Complex MeasureTheory
open scoped BigOperators

namespace RHTower

namespace MeixnerPollaczek

open ComplexRapidity PowerSeriesUniqueness

/-- The boost matrix entry `M_{mn}(t) = ∫ p_m p_n e^{its} dμ`. -/
noncomputable def boostMatrixEntry (t : ℝ) (m n : ℕ) : ℂ :=
  ∫ s : ℝ, (((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) *
    (((semilocalArchimedeanJacobiPolynomial n).eval s : ℝ) : ℂ) * cexp (((t * s : ℝ) : ℂ) * I)
    ∂semilocalArchimedeanGammaMeasure

/-- The row function `L_m(z) = ∫ G_s(z) p_m(s) e^{its} dμ`. -/
noncomputable def boostRowFunction (t : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ∫ s : ℝ, mpGeneratingFunction s z *
    ((((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) * cexp (((t * s : ℝ) : ℂ) * I))
    ∂semilocalArchimedeanGammaMeasure

theorem hasSum_boostRowFunction (t : ℝ) (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / 4) :
    HasSum (fun n : ℕ => (semilocalArchimedeanJacobiNormalization n : ℂ) *
        boostMatrixEntry t m n * z ^ n)
      (boostRowFunction t m z) := by
  have h := hasSum_integral_mpCoefficient_mul_row m t hz
  refine h.congr_fun fun n => ?_
  have hfun : (fun s : ℝ => (mpCoefficient s n : ℂ) * z ^ n *
      ((((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) *
        cexp (((t * s : ℝ) : ℂ) * I))) =
      fun s : ℝ => ((semilocalArchimedeanJacobiNormalization n : ℂ) * z ^ n) *
        ((((semilocalArchimedeanJacobiPolynomial m).eval s : ℝ) : ℂ) *
          (((semilocalArchimedeanJacobiPolynomial n).eval s : ℝ) : ℂ) *
          cexp (((t * s : ℝ) : ℂ) * I)) := by
    funext s
    unfold mpCoefficient
    push_cast
    ring
  rw [hfun, integral_const_mul]
  unfold boostMatrixEntry
  ring

/-- The closed row function `R_m(z)`. -/
noncomputable def boostRowClosed (t : ℝ) (m : ℕ) (z : ℂ) : ℂ :=
  ((Real.cosh t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    (Ring.choose (-(1 / 2 : ℂ)) m * (-1) ^ m / (semilocalArchimedeanJacobiNormalization m : ℂ)) *
    ((z + I * (Real.tanh t : ℂ)) ^ m * (1 - I * (Real.tanh t : ℂ) * z) ^ (-((m : ℂ) + 1 / 2)))

theorem re_one_sub_I_tanh_mul_pos (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (1 - I * (Real.tanh t : ℂ) * z).re := by
  have hτ := Real.abs_tanh_lt_one t
  have him := abs_im_le_norm z
  have h : |Real.tanh t * z.im| < 1 := by
    rw [abs_mul]
    calc |Real.tanh t| * |z.im| ≤ 1 * |z.im| :=
          mul_le_mul_of_nonneg_right hτ.le (abs_nonneg _)
      _ = |z.im| := one_mul _
      _ < 1 := him.trans_lt hz
  simp only [sub_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, zero_sub,
    mul_im, mul_zero, neg_mul, zero_add]
  linarith [(abs_lt.mp h).1]

theorem one_sub_I_tanh_mul_mem_slitPlane (t : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - I * (Real.tanh t : ℂ) * z ∈ slitPlane :=
  mem_slitPlane_iff.mpr (Or.inl (re_one_sub_I_tanh_mul_pos t hz))

theorem differentiableOn_boostRowClosed (t : ℝ) (m : ℕ) :
    DifferentiableOn ℂ (boostRowClosed t m) (Metric.ball (0 : ℂ) (1 / 4)) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by
    rw [Metric.mem_ball, dist_zero_right] at hz
    linarith
  apply DifferentiableAt.differentiableWithinAt
  unfold boostRowClosed
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.mul
  · exact (differentiableAt_id.add_const _).pow m
  · have h : DifferentiableAt ℂ (fun w : ℂ => 1 - I * (Real.tanh t : ℂ) * w) z :=
      (differentiableAt_id.const_mul _).const_sub 1
    exact h.cpow_const (one_sub_I_tanh_mul_mem_slitPlane t hz')

theorem boostRowFunction_ofReal (t : ℝ) (m : ℕ) {z : ℝ} (hz : |z| < 1 / 4) :
    boostRowFunction t m z = boostRowClosed t m z := by
  have hcm : (semilocalArchimedeanJacobiNormalization m : ℂ) ≠ 0 := by
    exact_mod_cast (semilocalArchimedeanJacobiNormalization_pos m).ne'
  have h1 : boostRowFunction t m z =
      boostRowCoefficient t z m / (semilocalArchimedeanJacobiNormalization m : ℂ) := by
    unfold boostRowFunction boostRowCoefficient
    rw [eq_div_iff hcm, ← integral_mul_const]
    congr 1
    funext s
    unfold mpCoefficient
    push_cast
    ring
  rw [h1, boostRowCoefficient_eq t hz]
  unfold boostClosedCoefficient boostRowClosed boostRatio
  have hD : (1 - I * (Real.tanh t : ℂ) * z) ≠ 0 := one_sub_I_tanh_mul_ne_zero t z
  rw [neg_pow, div_pow, show (-((m : ℂ) + 1 / 2)) = (-(1 / 2 : ℂ)) + (-(m : ℂ)) by ring,
    cpow_add _ _ hD, cpow_neg, cpow_neg, cpow_natCast]
  field_simp

theorem hasSum_taylor_boostRowClosed (t : ℝ) (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1 / 4) :
    HasSum (fun n : ℕ => (iteratedDeriv n (boostRowClosed t m) 0 / n.factorial) * z ^ n)
      (boostRowClosed t m z) := by
  have h := Complex.hasSum_taylorSeries_on_ball (differentiableOn_boostRowClosed t m)
    (z := z) (by simpa using hz)
  refine h.congr_fun fun n => ?_
  rw [sub_zero, smul_eq_mul, smul_eq_mul]
  ring

/-- **The boost matrix entries are the Taylor coefficients of the closed row function:**
`c_n M_{mn}(t) = R_m^{(n)}(0) / n!`. -/
theorem normalization_mul_boostMatrixEntry_eq (t : ℝ) (m n : ℕ) :
    (semilocalArchimedeanJacobiNormalization n : ℂ) * boostMatrixEntry t m n =
      iteratedDeriv n (boostRowClosed t m) 0 / n.factorial :=
  congrFun (eq_of_hasSum_mul_pow_eq_of_ofReal (by norm_num : (0 : ℝ) < 1 / 4)
    (fun z hz => hasSum_boostRowFunction t m hz)
    (fun z hz => hasSum_taylor_boostRowClosed t m hz)
    (fun x hx => boostRowFunction_ofReal t m hx)) n

/-! ## Taylor coefficients of the two factors -/

/-- Taylor coefficients of `(z + c)^m` at `0`. -/
theorem iteratedDeriv_add_const_pow_zero (c : ℂ) (m i : ℕ) :
    iteratedDeriv i (fun z : ℂ => (z + c) ^ m) 0 =
      i.factorial * (if i ≤ m then (m.choose i : ℂ) * c ^ (m - i) else 0) := by
  have hcoef : ∀ w : ℂ, ‖w‖ < 1 →
      HasSum (fun i : ℕ => (if i ≤ m then (m.choose i : ℂ) * c ^ (m - i) else 0) * w ^ i)
        ((w + c) ^ m) := by
    intro w _
    rw [add_pow]
    have h : HasSum (fun i : ℕ => (if i ≤ m then (m.choose i : ℂ) * c ^ (m - i) else 0) * w ^ i)
        (∑ i ∈ Finset.range (m + 1),
          (if i ≤ m then (m.choose i : ℂ) * c ^ (m - i) else 0) * w ^ i) :=
      hasSum_sum_of_ne_finset_zero (by
        intro i hi
        rw [Finset.mem_range] at hi
        simp [show ¬ i ≤ m by omega])
    convert h using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    simp only [show i ≤ m by omega, if_true]
    ring
  have h := coeff_eq_iteratedDeriv_div_factorial_of_hasSum one_pos hcoef i
  rw [h]
  have hf : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  field_simp

/-- Taylor coefficients of `(1 − c z)^{−a}` at `0`. -/
theorem iteratedDeriv_one_sub_mul_cpow_neg_zero (a c : ℂ) (hc : ‖c‖ < 4) (k : ℕ) :
    iteratedDeriv k (fun z : ℂ => (1 - c * z) ^ (-a)) 0 =
      k.factorial * (Ring.choose (-a) k * (-c) ^ k) := by
  have hcoef : ∀ w : ℂ, ‖w‖ < 1 / 4 →
      HasSum (fun k : ℕ => (Ring.choose (-a) k * (-c) ^ k) * w ^ k) ((1 - c * w) ^ (-a)) := by
    intro w hw
    have hu : ‖c * w‖ < 1 := by
      rw [norm_mul]
      calc ‖c‖ * ‖w‖ < 4 * (1 / 4) := mul_lt_mul'' hc hw (norm_nonneg _) (norm_nonneg _)
        _ = 1 := by norm_num
    have h := hasSum_one_sub_cpow_neg a hu
    refine h.congr_fun fun k => ?_
    rw [neg_mul_eq_neg_mul, mul_pow]
    ring
  have h := coeff_eq_iteratedDeriv_div_factorial_of_hasSum (by norm_num) hcoef k
  rw [h]
  have hf : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  field_simp

end MeixnerPollaczek

end RHTower
