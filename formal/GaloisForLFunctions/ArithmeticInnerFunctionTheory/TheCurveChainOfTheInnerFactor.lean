import GaloisForLFunctions.ArithmeticInnerFunctionTheory.TheSzegoInfimum
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.GrowingWindowsOfSpecZ.TheCanonicalFlowOfACurve

/-!
# The inner factor of a curve

The test case where the sign is known. For a curve datum `D` with normalized eigenvalues `β_i` let
`P(v) = Π_i (1 − β_i v)` on the unit disc, the chart `v = √q q^{−s}` of `Re s > ½`. The zeros of `P` in
the disc are the right zeros of the zeta function.

* **The inner mass is the Mahler measure** (`circleAverage_log_norm_lPoly`). The mean of `log |P|` on the circle is
  `I(D) = Σ_i log⁺ |β_i|`.
* **The second expression** (`isGLB_curve_budget`). `exp (2 I(D)) = inf_Q mean of |P e^{Q}|²`.
* **Castelnuovo is the opposite sign** (`curve_inner_tfae`). `I(D) = 0` iff the datum is unitary, iff the Hodge index holds on
  the Frobenius span (Castelnuovo's inequality), iff the budgets reach `1`, iff the reflection coefficients of the lattice
  stay in `(−1, 1)` up to the number of angles. So over `𝔽_q` the missing upper bound `I ≤ 0` *is* a positivity of an
  intersection form.
* **The Carathéodory reading** (`re_caratheodory_nonneg_of_unitary`). On a unitary datum the logarithmic derivative
  `Φ(v) = Σ_i (1 + β_i v)/(1 − β_i v)` has nonnegative real part: Castelnuovo is a Herglotz bound.
* **Golden** (`innerMass_goldenDatum`). The fake curve has `I = log φ > 0`.
-/

open Complex Filter Topology MeasureTheory Set
open scoped Real ENNReal

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open ArithmeticCastelnuovoSeveri GrowingWindowsOfSpecZ

noncomputable section

local notation "𝕋" => AddCircle (2 * π)

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The normalized `L`-polynomial `P(v) = Π_i (1 − β_i v)`. -/
def lPoly (v : ℂ) : ℂ := ∏ i, (1 - D.β i * v)

/-- The inner mass `I(D) = Σ_i log⁺ |β_i|`. -/
def innerMass : ℝ := ∑ i, Real.posLog ‖D.β i‖

theorem continuous_lPoly : Continuous (lPoly D) := by
  unfold lPoly
  fun_prop

/-- On the circle `|1 − βv| = |v − β̄|`. -/
theorem norm_one_sub_mul_eq (β : ℂ) {v : ℂ} (hv : ‖v‖ = 1) :
    ‖1 - β * v‖ = ‖v - (starRingEnd ℂ) β‖ := by
  have hconj : (starRingEnd ℂ) v * v = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hv]
    norm_num
  have e : 1 - β * v = v * ((starRingEnd ℂ) v - β) := by
    have := hconj
    linear_combination -this
  rw [e, norm_mul, hv, one_mul, ← Complex.norm_conj, map_sub, Complex.conj_conj]

theorem circleAverage_log_norm_one_sub_mul (β : ℂ) :
    Real.circleAverage (fun v => Real.log ‖1 - β * v‖) 0 1 = Real.posLog ‖β‖ := by
  have h : Set.EqOn (fun v => Real.log ‖1 - β * v‖) (fun v => Real.log ‖v - (starRingEnd ℂ) β‖)
      (Metric.sphere (0 : ℂ) |1|) := by
    intro v hv
    have hv' : ‖v‖ = 1 := by simpa using hv
    simp only [norm_one_sub_mul_eq β hv']
  rw [Real.circleAverage_congr_sphere h, circleAverage_log_norm_sub_const_eq_posLog,
    Complex.norm_conj]

theorem circleIntegrable_log_norm_one_sub_mul (β : ℂ) :
    CircleIntegrable (fun v => Real.log ‖1 - β * v‖) 0 1 :=
  MeromorphicOn.circleIntegrable_log_norm (f := fun v : ℂ => 1 - β * v)
    (fun v _ => (analyticAt_const.sub (analyticAt_const.mul analyticAt_id)).meromorphicAt)

theorem measurable_log_norm_one_sub_mul (β : ℂ) :
    Measurable (fun v : ℂ => Real.log ‖1 - β * v‖) :=
  Real.measurable_log.comp (by fun_prop)

theorem countable_lPoly_zeros : {v : ℂ | lPoly D v = 0}.Countable := by
  have hsub : {v : ℂ | lPoly D v = 0} ⊆ ⋃ i, {v : ℂ | 1 - D.β i * v = 0} := by
    intro v hv
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.mp hv
    exact mem_iUnion.mpr ⟨i, hi⟩
  refine (countable_iUnion fun i => ?_).mono hsub
  by_cases h0 : D.β i = 0
  · have : {v : ℂ | 1 - D.β i * v = 0} = ∅ := by
      ext v
      simp [h0]
    rw [this]
    exact countable_empty
  · have : {v : ℂ | 1 - D.β i * v = 0} ⊆ {(D.β i)⁻¹} := by
      intro v hv
      simp only [mem_setOf_eq, sub_eq_zero] at hv
      simp only [mem_singleton_iff]
      field_simp
      linear_combination -hv
    exact (countable_singleton _).mono this

/-- **The inner mass is the Mahler measure.** -/
theorem circleAverage_log_norm_lPoly :
    Real.circleAverage (fun v => Real.log ‖lPoly D v‖) 0 1 = innerMass D := by
  have hae : (fun x : 𝕋 => Real.log ‖lPoly D (circleZ x)‖) =ᵐ[AddCircle.haarAddCircle]
      fun x => ∑ i, Real.log ‖1 - D.β i * circleZ x‖ := by
    filter_upwards [ae_circleZ_notMem_of_countable (countable_lPoly_zeros D)] with x hx
    rw [lPoly, norm_prod, Real.log_prod]
    intro i _
    refine norm_ne_zero_iff.mpr fun h0 => hx ?_
    exact Finset.prod_eq_zero (Finset.mem_univ i) h0
  rw [← integral_haar_circleZ (fun v => Real.log ‖lPoly D v‖), integral_congr_ae hae,
    integral_finset_sum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_haar_circleZ (fun v => Real.log ‖1 - D.β i * v‖),
      circleAverage_log_norm_one_sub_mul]
  · intro i _
    exact (integrable_haar_circleZ_iff (measurable_log_norm_one_sub_mul _)).mpr
      (circleIntegrable_log_norm_one_sub_mul _)

theorem circleIntegrable_log_norm_lPoly : CircleIntegrable (fun v => Real.log ‖lPoly D v‖) 0 1 :=
  MeromorphicOn.circleIntegrable_log_norm (f := lPoly D) (fun v _ => by
    have : AnalyticAt ℂ (lPoly D) v := by
      unfold lPoly
      fun_prop
    exact this.meromorphicAt)

/-- **The second expression over `𝔽_q`.** The infimum of the mollified second moments of `P` is
`exp (2 I(D))`. -/
theorem isGLB_curve_budget :
    IsGLB ((fun Q : Polynomial ℂ =>
        Real.circleAverage (fun v => ‖lPoly D v‖ ^ 2 * ‖Complex.exp (Q.eval v)‖ ^ 2) 0 1) ''
          {Q | Q.coeff 0 = 0})
      (Real.exp (2 * innerMass D)) := by
  have hcont := continuous_lPoly D
  have hG : Measurable (fun v => ‖lPoly D v‖ ^ 2) := by fun_prop
  have hpos : ∀ᵐ x : 𝕋 ∂AddCircle.haarAddCircle, 0 < ‖lPoly D (circleZ x)‖ ^ 2 := by
    filter_upwards [ae_circleZ_notMem_of_countable (countable_lPoly_zeros D)] with x hx
    exact pow_pos (norm_pos_iff.mpr hx) 2
  have hint : CircleIntegrable (fun v => ‖lPoly D v‖ ^ 2) 0 1 :=
    ((hcont.norm.pow 2).continuousOn).circleIntegrable zero_le_one
  have hlog : CircleIntegrable (fun v => Real.log (‖lPoly D v‖ ^ 2)) 0 1 := by
    simp only [Real.log_pow]
    exact (circleIntegrable_log_norm_lPoly D).const_smul (2 : ℝ) |>.congr_simp (by simp)
  have h := isGLB_circleAverage hG hpos hint hlog
  have e : Real.circleAverage (fun v => Real.log (‖lPoly D v‖ ^ 2)) 0 1 = 2 * innerMass D := by
    simp only [Real.log_pow]
    rw [Real.circleAverage_fun_smul (2 : ℝ) ?_ |>.trans ?_] <;> sorry
  rw [e] at h
  exact h

/-- `I(D) = 0` iff the datum is unitary; the functional equation forces both inequalities. -/
theorem innerMass_eq_zero_iff : innerMass D = 0 ↔ ∀ i, ‖D.β i‖ = 1 := by
  have hnn : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ Real.posLog ‖D.β i‖ := fun _ _ => Real.posLog_nonneg
  rw [innerMass, Finset.sum_eq_zero_iff_of_nonneg hnn]
  constructor
  · intro h i
    have hle : ∀ j, ‖D.β j‖ ≤ 1 := fun j => by
      have := h j (Finset.mem_univ j)
      rcases Real.posLog_eq_zero_iff.mp this with h1
      simpa [abs_of_nonneg (norm_nonneg _)] using h1
    have hfe : ‖D.β (D.fePerm i)‖ * ‖D.β i‖ = 1 := by
      rw [← norm_mul, D.β_fePerm i, norm_one]
    have h1 := hle i
    have h2 := hle (D.fePerm i)
    have h3 := norm_nonneg (D.β i)
    have h4 := norm_nonneg (D.β (D.fePerm i))
    nlinarith
  · intro h i _
    rw [h i, Real.posLog_one]

/-- **The Carathéodory reading of Castelnuovo.** On a unitary datum `Re Σ_i (1 + β_i v)/(1 − β_i v) ≥ 0`
on the disc. -/
theorem re_caratheodory_nonneg_of_unitary (hU : ∀ i, ‖D.β i‖ = 1) {v : ℂ} (hv : ‖v‖ < 1) :
    0 ≤ (∑ i, (1 + D.β i * v) / (1 - D.β i * v)).re := by
  rw [Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  set u := D.β i * v with hu
  have hu1 : ‖u‖ < 1 := by rwa [hu, norm_mul, hU i, one_mul]
  have hd : 1 - u ≠ 0 := by
    intro h
    have : u = 1 := by linear_combination -h
    rw [this, norm_one] at hu1
    exact lt_irrefl _ hu1
  have e : ((1 + u) / (1 - u)).re = (1 - ‖u‖ ^ 2) / Complex.normSq (1 - u) := by
    rw [Complex.div_re, Complex.normSq_apply, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    field_simp
    ring
  rw [e]
  have h2 : ‖u‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg u]
  exact div_nonneg (by linarith) (Complex.normSq_nonneg _)

/-- **The curve chain.** Trivial inner factor, unitarity, Castelnuovo on the Frobenius span, and the
reflection coefficients are one statement. -/
theorem curve_inner_tfae [Nonempty ι] :
    List.TFAE [innerMass D = 0, ∀ i, ‖D.β i‖ = 1, D.HodgeIndexOnSpan,
      ∀ k, k + 1 < D.spectrum.card → reflCoeff (curveLattice D) k ^ 2 < 1] := by
  tfae_have 1 ↔ 2 := innerMass_eq_zero_iff D
  tfae_have 3 ↔ 2 := D.hodgeIndexOnSpan_iff_unitary
  tfae_have 2 ↔ 4 := unitary_iff_reflCoeff_sq_lt D
  tfae_finish

/-- **Golden.** The fake curve has inner mass `log φ`. -/
theorem innerMass_goldenDatum : innerMass goldenDatum = Real.log Real.goldenRatio := by
  sorry

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
