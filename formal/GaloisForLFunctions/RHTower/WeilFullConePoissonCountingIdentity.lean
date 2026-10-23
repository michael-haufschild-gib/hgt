import GaloisForLFunctions.RHTower.WeilConeSingularDeficitCounting
import GaloisForLFunctions.RHTower.WeilFullConeAtomExtraction

/-!
# Exact Poisson counting identity for a Weil-positive system

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam`.  Smooth the spectral counting
function by the Poisson kernel of width `3/2`, and the zero counting function of `ξ` by the Poisson
kernels of the copies at abscissa `2`.  Then for every `T ≥ 0`

`∫ (arctan((T−r)/(3/2)) + arctan(r/(3/2))) dμ_lam(r)
   − Σ_q (arctan((T−γ_q)/(2−β_q)) + arctan(γ_q/(2−β_q)))
 = Σ_{n≥2} (Λ(n) − lam(n)) n^{−2} sin(T log n)/log n`

(`poissonCount_sub_eq`), and the right side is bounded by `Σ|Λ − lam| n^{−2}/log 2` uniformly in
`T` (`abs_poissonCount_sub_le`).

So the Poisson-smoothed spectral count of every producer equals the Poisson-smoothed zero count
of `ζ` up to an explicit bounded almost-periodic function.  This is the exact form of the mass
law: the main terms `(T/2)log(T/2πe)` cancel identically.

**Proof.**  Integrate `Re Φ_lam(2+it) − Re ξ'/ξ(2+it) = Σ (Λ − lam)(n)n^{−2}cos(t log n)` over
`[0,T]`.  The left side is a Poisson integral of `μ_lam` (Fubini) and a Hadamard sum of Poisson
terms (dominated termwise integration).  Each Poisson term integrates to an arctangent
difference, and each cosine to `sin(T log n)/log n`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz

theorem hasDerivAt_arctan_shift (r b t : ℝ) (hb : 0 < b) :
    HasDerivAt (fun t => Real.arctan ((t - r) / b)) (b / (b ^ 2 + (r - t) ^ 2)) t := by
  have h := (((hasDerivAt_id' t).sub_const r).div_const b).arctan
  refine h.congr_deriv ?_
  have : 0 < b ^ 2 + (r - t) ^ 2 := by positivity
  field_simp
  ring

/-- The Poisson kernel of width `b` integrates over `[0,T]` to an arctangent difference. -/
private theorem integral_poissonKernel_eq (r b T : ℝ) (hb : 0 < b) :
    ∫ t in (0 : ℝ)..T, b / (b ^ 2 + (r - t) ^ 2) =
      Real.arctan ((T - r) / b) + Real.arctan (r / b) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_arctan_shift r b t hb)
    ((continuous_const.div (by fun_prop) fun t => by positivity :
      Continuous fun t : ℝ => b / (b ^ 2 + (r - t) ^ 2)).intervalIntegrable _ _)]
  rw [zero_sub, neg_div, Real.arctan_neg, sub_neg_eq_add]

/-- `Re Φ_lam(2 + it)` is the width-`3/2` Poisson integral of `μ_lam`. -/
theorem re_weilFunction_two_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    (weilFunction lam ((2 : ℂ) + t * I)).re =
      ∫ r, (3 / 2) / ((3 / 2) ^ 2 + (r - t) ^ 2) ∂boundaryMeasure hW := by
  have hs : 1 < ((2 : ℂ) + t * I).re := by simp
  have h := lintegral_poissonDensity_eq hW hs
  have hw : ((2 : ℂ) + t * I) - 1 / 2 = ((3 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
  have hwre : (((2 : ℂ) + t * I) - 1 / 2).re = 3 / 2 := by rw [hw]; simp
  rw [hwre] at h
  have hnn : 0 ≤ (weilFunction lam ((2 : ℂ) + t * I)).re := by
    have := re_weilFunction_nonneg hW (s := (2 : ℂ) + t * I) hs
    exact this
  have hint : ∫ r, (poissonDensity (((2 : ℂ) + t * I) - 1 / 2) r).toReal ∂boundaryMeasure hW =
      (weilFunction lam ((2 : ℂ) + t * I)).re / (3 / 2) := by
    rw [integral_toReal (measurable_poissonDensity _).aemeasurable
      (Eventually.of_forall fun r => (poissonDensity_ne_top _ r).lt_top), h,
      ENNReal.toReal_ofReal (by positivity)]
  have hpt : ∀ r : ℝ, (poissonDensity (((2 : ℂ) + t * I) - 1 / 2) r).toReal =
      1 / ((3 / 2) ^ 2 + (r - t) ^ 2) := by
    intro r
    rw [poissonDensity_toReal, hw]
    simp
  simp_rw [hpt] at hint
  rw [show (fun r : ℝ => (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2)) =
    fun r => (3 / 2) * (1 / ((3 / 2) ^ 2 + (r - t) ^ 2)) by funext r; ring,
    integral_const_mul, hint]
  field_simp

theorem arctanSum_eq_integral (r T : ℝ) :
    Real.arctan ((T - r) / (3 / 2)) + Real.arctan (r / (3 / 2)) =
      ∫ t in (0 : ℝ)..T, (3 / 2) / ((3 / 2) ^ 2 + (r - t) ^ 2) :=
  (integral_poissonKernel_eq r (3 / 2) T (by norm_num)).symm

theorem arctanSum_nonneg (r : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ Real.arctan ((T - r) / (3 / 2)) + Real.arctan (r / (3 / 2)) := by
  rw [arctanSum_eq_integral]
  exact intervalIntegral.integral_nonneg hT fun t _ => by positivity

theorem ofReal_re_weilFunction_two_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) (t : ℝ) :
    ENNReal.ofReal (weilFunction lam ((2 : ℂ) + t * I)).re =
      ∫⁻ r, ENNReal.ofReal ((3 / 2) / ((3 / 2) ^ 2 + (r - t) ^ 2)) ∂boundaryMeasure hW := by
  have hs : 1 < ((2 : ℂ) + t * I).re := by simp
  have h := lintegral_poissonDensity_eq hW hs
  have hw : ((2 : ℂ) + t * I) - 1 / 2 = ((3 / 2 : ℝ) : ℂ) + t * I := by push_cast; ring
  have hwre : (((2 : ℂ) + t * I) - 1 / 2).re = 3 / 2 := by rw [hw]; simp
  rw [hwre] at h
  calc ENNReal.ofReal (weilFunction lam ((2 : ℂ) + t * I)).re
      = ENNReal.ofReal (3 / 2) *
          ENNReal.ofReal ((weilFunction lam ((2 : ℂ) + t * I)).re / (3 / 2)) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        field_simp
    _ = ENNReal.ofReal (3 / 2) * ∫⁻ r, poissonDensity (((2 : ℂ) + t * I) - 1 / 2) r
          ∂boundaryMeasure hW := by rw [h]
    _ = ∫⁻ r, ENNReal.ofReal (3 / 2) * poissonDensity (((2 : ℂ) + t * I) - 1 / 2) r
          ∂boundaryMeasure hW := (lintegral_const_mul _ (measurable_poissonDensity _)).symm
    _ = ∫⁻ r, ENNReal.ofReal ((3 / 2) / ((3 / 2) ^ 2 + (r - t) ^ 2)) ∂boundaryMeasure hW := by
        refine lintegral_congr fun r => ?_
        rw [← ENNReal.ofReal_toReal (poissonDensity_ne_top _ r), poissonDensity_toReal, hw,
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im,
          Complex.mul_im, zero_add]
        ring

theorem continuous_re_weilFunction_two {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Continuous fun t : ℝ => (weilFunction lam ((2 : ℂ) + t * I)).re := by
  have hc : Continuous fun t : ℝ => (weilContinuation hW ((2 : ℂ) + t * I)).re := by
    refine Complex.continuous_re.comp ?_
    refine (differentiableOn_weilContinuation hW).continuousOn.comp_continuous (by fun_prop)
      fun t => ?_
    show 1 / 2 < ((2 : ℂ) + t * I).re
    simp; norm_num
  refine hc.congr fun t => ?_
  rw [weilContinuation_eq hW (by simp)]

/-- **Spectral side.**  `∫_0^T Re Φ_lam(2+it) dt = ∫ (arctan((T−r)/(3/2)) + arctan(r/(3/2))) dμ_lam`. -/
theorem integral_re_weilFunction_two_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {T : ℝ}
    (hT : 0 ≤ T) :
    ∫ t in (0 : ℝ)..T, (weilFunction lam ((2 : ℂ) + t * I)).re =
      ∫ r, (Real.arctan ((T - r) / (3 / 2)) + Real.arctan (r / (3 / 2))) ∂boundaryMeasure hW := by
  haveI := sFinite_boundaryMeasure hW
  have hnn : ∀ t : ℝ, 0 ≤ (weilFunction lam ((2 : ℂ) + t * I)).re := fun t =>
    re_weilFunction_nonneg hW (by simp)
  rw [intervalIntegral.integral_of_le hT, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall hnn) (continuous_re_weilFunction_two hW).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun r => arctanSum_nonneg r hT)
    ((by fun_prop : Continuous fun r : ℝ =>
      Real.arctan ((T - r) / (3 / 2)) + Real.arctan (r / (3 / 2))).aestronglyMeasurable)]
  congr 1
  simp_rw [ofReal_re_weilFunction_two_eq hW]
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun r => ?_
    have hk : Continuous fun t : ℝ => (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (r - t) ^ 2) :=
      continuous_const.div (by fun_prop) fun t => by positivity
    rw [← ofReal_integral_eq_lintegral_ofReal (hk.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      (Eventually.of_forall fun t => by positivity), ← intervalIntegral.integral_of_le hT,
      ← arctanSum_eq_integral]
  · refine Measurable.aemeasurable ?_
    exact ENNReal.measurable_ofReal.comp (Continuous.measurable (continuous_const.div
      (by fun_prop) fun p => by positivity :
        Continuous fun p : ℝ × ℝ => (3 / 2 : ℝ) / ((3 / 2) ^ 2 + (p.2 - p.1) ^ 2)))

/-- **Zero side.**  `∫_0^T Re ξ'/ξ(2+it) dt = Σ_q (arctan((T−γ_q)/(2−β_q)) + arctan(γ_q/(2−β_q)))`. -/
theorem hasSum_integral_copyPoisson_two {T : ℝ} (hT : 0 ≤ T) :
    HasSum (fun q : XiZeroCopy => ∫ t in (0 : ℝ)..T, copyPoisson 2 t q)
      (∫ t in (0 : ℝ)..T, (logDeriv xi ((2 : ℂ) + t * I)).re) := by
  set C : ℝ := (1 + (2 * T + 2) ^ 2) / (2 - 1) + 8 * 2 with hC
  refine intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun q _ => C * (1 / (1 + ((q.1 : ℂ)).im ^ 2))) (fun q =>
      (continuous_copyPoisson (by norm_num) q).aestronglyMeasurable) (fun q => ?_) ?_ ?_ ?_
  · refine Eventually.of_forall fun t ht => ?_
    rw [uIoc_of_le hT] at ht
    rw [Real.norm_eq_abs, abs_of_nonneg (copyPoisson_pos (by norm_num) t q).le]
    exact copyPoisson_le_local (by norm_num) (abs_le.mpr ⟨by linarith [ht.1], ht.2⟩) q
  · exact Eventually.of_forall fun t _ => summable_inv_one_add_sq_im.mul_left C
  · exact intervalIntegrable_const
  · refine Eventually.of_forall fun t _ => ?_
    have h := re_logDeriv_xi_eq_tsum_copyPoisson (σ := 2) (by norm_num) t
    push_cast at h
    rw [h]
    exact (summable_copyPoisson (by norm_num) t).hasSum

theorem integral_copyPoisson_two_eq (q : XiZeroCopy) (T : ℝ) :
    ∫ t in (0 : ℝ)..T, copyPoisson 2 t q =
      Real.arctan ((T - ((q.1 : ℂ)).im) / (2 - ((q.1 : ℂ)).re)) +
        Real.arctan (((q.1 : ℂ)).im / (2 - ((q.1 : ℂ)).re)) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_arctan_copy (by norm_num) q t)
    ((continuous_copyPoisson (by norm_num) q).intervalIntegrable _ _), zero_sub, neg_div,
    Real.arctan_neg, sub_neg_eq_add]

/-- **Dirichlet side.**  `∫_0^T Σ a_n cos(t log n) dt = Σ a_n sin(T log n)/log n`. -/
theorem hasSum_integral_logCosSeries {a : ℕ → ℝ} (ha : Summable fun n => |a n|)
    (ha0 : a 0 = 0) (ha1 : a 1 = 0) (T : ℝ) :
    HasSum (fun n : ℕ => a n * Real.sin (T * Real.log n) / Real.log n)
      (∫ t in (0 : ℝ)..T, logCosSeries a t) := by
  have hterm : ∀ n : ℕ, ∫ t in (0 : ℝ)..T, a n * Real.cos (t * Real.log n) =
      a n * Real.sin (T * Real.log n) / Real.log n := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp [ha0, ha1]
    · have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast hn)
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_right
        (fun x => Real.cos x) hlog.ne', integral_cos, zero_mul, Real.sin_zero, sub_zero,
        smul_eq_mul]
      field_simp
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := T)
    (F := fun n t => a n * Real.cos (t * Real.log n)) (f := logCosSeries a)
    (fun n _ => |a n|) (fun n => (by fun_prop : Continuous fun t : ℝ =>
      a n * Real.cos (t * Real.log n)).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    (Eventually.of_forall fun t _ => ha) intervalIntegrable_const
    (Eventually.of_forall fun t _ => (ha.of_norm_bounded (fun n => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))).hasSum)
  simpa only [hterm] using h

/-- **The exact Poisson counting identity.** -/
theorem poissonCount_sub_eq {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {T : ℝ} (hT : 0 ≤ T) :
    HasSum (fun n : ℕ => deviationCoeff lam 2 n * Real.sin (T * Real.log n) / Real.log n)
      ((∫ r, (Real.arctan ((T - r) / (3 / 2)) + Real.arctan (r / (3 / 2))) ∂boundaryMeasure hW) -
        ∑' q : XiZeroCopy, (Real.arctan ((T - ((q.1 : ℂ)).im) / (2 - ((q.1 : ℂ)).re)) +
          Real.arctan (((q.1 : ℂ)).im / (2 - ((q.1 : ℂ)).re)))) := by
  have hdev := hasSum_integral_logCosSeries (summable_abs_deviationCoeff hW (σ := 2) (by norm_num))
    (by simp [deviationCoeff]) (by simp [deviationCoeff]) T
  have hzero := hasSum_integral_copyPoisson_two hT
  simp_rw [integral_copyPoisson_two_eq] at hzero
  rw [← integral_re_weilFunction_two_eq hW hT, hzero.tsum_eq]
  convert hdev using 1
  rw [← intervalIntegral.integral_sub ((continuous_re_weilFunction_two hW).intervalIntegrable _ _)
    ?_]
  · refine intervalIntegral.integral_congr fun t _ => ?_
    show (weilFunction lam ((2 : ℂ) + t * I)).re - (logDeriv xi ((2 : ℂ) + t * I)).re = _
    have := re_weilFunction_sub_re_logDeriv_xi hW (σ := 2) (by norm_num) t
    push_cast at this
    exact this
  · have hc : Continuous fun t : ℝ => (logDeriv xi ((2 : ℂ) + t * I)).re := by
      have e : (fun t : ℝ => (logDeriv xi ((2 : ℂ) + t * I)).re) =
          fun t => ∑' q, copyPoisson 2 t q := by
        funext t
        have h := re_logDeriv_xi_eq_tsum_copyPoisson (σ := 2) (by norm_num) t
        push_cast at h
        exact h
      rw [e]
      exact continuous_tsum_copyPoisson (by norm_num)
    exact hc.intervalIntegrable _ _

/-- The Poisson counting difference is bounded uniformly in `T`. -/
theorem abs_poissonCount_sub_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ r, (Real.arctan ((T - r) / (3 / 2)) + Real.arctan (r / (3 / 2))) ∂boundaryMeasure hW) -
        ∑' q : XiZeroCopy, (Real.arctan ((T - ((q.1 : ℂ)).im) / (2 - ((q.1 : ℂ)).re)) +
          Real.arctan (((q.1 : ℂ)).im / (2 - ((q.1 : ℂ)).re)))| ≤
      (∑' n : ℕ, |deviationCoeff lam 2 n|) / Real.log 2 := by
  have h := poissonCount_sub_eq hW hT
  have hsum := summable_abs_deviationCoeff hW (σ := 2) (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← h.tsum_eq]
  have hb : ∀ n : ℕ, |deviationCoeff lam 2 n * Real.sin (T * Real.log n) / Real.log n| ≤
      |deviationCoeff lam 2 n| / Real.log 2 := by
    intro n
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n <;> simp [deviationCoeff]
    · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      rw [abs_div, abs_mul, abs_of_pos (hl2.trans_le hlog)]
      calc |deviationCoeff lam 2 n| * |Real.sin (T * Real.log n)| / Real.log n
          ≤ |deviationCoeff lam 2 n| * 1 / Real.log n :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _)
              (abs_nonneg _)) (hl2.trans_le hlog).le
        _ ≤ |deviationCoeff lam 2 n| / Real.log 2 := by
            rw [mul_one]
            exact div_le_div_of_nonneg_left (abs_nonneg _) hl2 hlog
  have hsum2 : Summable fun n : ℕ =>
      |deviationCoeff lam 2 n * Real.sin (T * Real.log n) / Real.log n| :=
    (hsum.div_const _).of_nonneg_of_le (fun _ => abs_nonneg _) hb
  calc |∑' n : ℕ, deviationCoeff lam 2 n * Real.sin (T * Real.log n) / Real.log n|
      ≤ ∑' n : ℕ, |deviationCoeff lam 2 n * Real.sin (T * Real.log n) / Real.log n| := by
        have := norm_tsum_le_tsum_norm (f := fun n : ℕ =>
          deviationCoeff lam 2 n * Real.sin (T * Real.log n) / Real.log n)
          (by simpa only [Real.norm_eq_abs] using hsum2)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, |deviationCoeff lam 2 n| / Real.log 2 :=
        hsum2.tsum_le_tsum hb (hsum.div_const _)
    _ = (∑' n : ℕ, |deviationCoeff lam 2 n|) / Real.log 2 := tsum_div_const

end RHTower.WeilSpectral

end
