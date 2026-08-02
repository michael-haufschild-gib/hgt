import GaloisForLFunctions.HTGeometry.RatApproxDatum
import GaloisForLFunctions.HTGeometry.UniformTubeLimit

/-!
# The vertical logarithm and the principal logarithm

The boundary shape measures the logarithmic level by `vertLog t = log t + iπ/2`, while the vertical
expansions of the digamma jets produce the principal logarithm of the argument.  The two agree to
leading order: `ψ` is asymptotic to `vertLog` uniformly on a tube, and `ψ - log` is bounded, so the
ratio `log s / vertLog t` tends to one.

Consequently a quotient of polynomials times a power of the principal logarithm has the boundary
datum its degrees and that power predict.
-/

open Filter Set Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A polynomial is bounded on the closed unit disc by the sum of its coefficient moduli. -/
theorem norm_polyEval_le_of_norm_le_one (P : Polynomial ℂ) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖P.eval w‖ ≤ ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖ := by
  rw [Polynomial.eval_eq_sum_range]
  refine le_trans (norm_sum_le _ _) ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_mul, norm_pow]
  have hpow : ‖w‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) hw
  nlinarith [norm_nonneg (P.coeff k)]

/-- `ψ - log` is bounded on every vertical tube beyond a height. -/
theorem exists_bound_digamma_sub_clog :
    ∃ C T : ℝ, 0 ≤ C ∧ 2 ≤ T ∧ ∀ σ t : ℝ, 0 < σ → T ≤ t →
      ‖Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
        - Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨P, C₀, T₀, hC₀, hT₀, hb⟩ := exists_digamma_shift_expansion 0 0
  refine ⟨C₀ + ∑ k ∈ Finset.range (P.natDegree + 1), ‖P.coeff k‖, T₀, by positivity, hT₀,
    fun σ t hσ ht => ?_⟩
  have ht2 : (2 : ℝ) ≤ t := le_trans hT₀ ht
  have htpos : (0 : ℝ) < t := by linarith
  have hval := hb σ t hσ (by linarith) ht
  have harg : (((σ + 0 : ℝ) : ℂ) + (t : ℂ) * Complex.I) = ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [harg, pow_one] at hval
  set s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hs
  have hsnorm : t ≤ ‖s‖ := norm_vertical_ge_im σ t
  have hspos : (0 : ℝ) < ‖s‖ := lt_of_lt_of_le htpos hsnorm
  have hinv : ‖1 / s‖ ≤ 1 := by
    rw [norm_div, norm_one, div_le_one hspos]
    linarith
  have hP := norm_polyEval_le_of_norm_le_one P hinv
  have hCt : C₀ / t ≤ C₀ := by
    rw [div_le_iff₀ htpos]
    nlinarith
  have hsplit : ‖Complex.log s - Complex.digamma s‖
      ≤ ‖Complex.digamma s - Complex.log s - P.eval (1 / s)‖ + ‖P.eval (1 / s)‖ := by
    have hEq : Complex.log s - Complex.digamma s
        = -((Complex.digamma s - Complex.log s - P.eval (1 / s)) + P.eval (1 / s)) := by ring
    rw [hEq, norm_neg]
    exact norm_add_le _ _
  linarith

/-- **The principal logarithm is asymptotic to the vertical logarithm**, uniformly on a tube. -/
theorem tubeLimit_clog_div_vertLog {M : ℝ} (hM : 0 < M) :
    TubeLimit M (fun σ t => Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t) 1 := by
  obtain ⟨C, T, hC, hT, hb⟩ := exists_bound_digamma_sub_clog
  have hdig : TubeLimit M (fun σ t =>
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t) 1 := by
    refine (tubeLimit_digamma_pow_div_vertLog_pow hM 1).congr (T₀ := 3) fun σ t hσ hσM ht => ?_
    rw [pow_one, pow_one]
  have hnull : TubeLimit M (fun σ t =>
      (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)
        - Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) / vertLog t) 0 := by
    have hg : Tendsto (fun t : ℝ => C * ‖vertLog t‖⁻¹) atTop (nhds 0) := by
      have := tendsto_norm_vertLog.inv_tendsto_atTop
      simpa using this.const_mul C
    refine tubeLimit_of_squeeze (T₀ := T) (g := fun t : ℝ => C * ‖vertLog t‖⁻¹)
      (fun σ t hσ hσM ht => ?_) hg
    rw [norm_div]
    by_cases hv : ‖vertLog t‖ = 0
    · rw [hv]
      simp
    · have hvpos : 0 < ‖vertLog t‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (hb σ t hσ ht) (by positivity)
  have hsum := hdig.add hnull
  rw [add_zero] at hsum
  refine hsum.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
  rw [← add_div]
  congr 1
  ring

/-- Powers of the logarithmic ratio, as tube limits. -/
theorem tubeLimit_clog_div_vertLog_pow {M : ℝ} (hM : 0 < M) (k : ℕ) :
    TubeLimit M (fun σ t =>
      (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t) ^ k) 1 := by
  induction k with
  | zero => simpa using tubeLimit_const (M := M) 1
  | succ n ih =>
      have hmul := ih.mul (tubeLimit_clog_div_vertLog hM)
      rw [mul_one] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      rw [pow_succ]

/-- **A quotient of polynomials times a power of the principal logarithm has a boundary datum.** -/
theorem hasShiftTubeDatum_ratEval_clogPow {M : ℝ} (hM : 0 < M) {p q : Polynomial ℂ}
    (hp : p ≠ 0) (hq : q ≠ 0) (k : ℕ) :
    HasShiftTubeDatum M 0
      (fun σ t => Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) p
        / Polynomial.eval ((σ : ℂ) + (t : ℂ) * Complex.I) q
        * (Complex.log ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ k)
      0 ((p.natDegree : ℝ) - (q.natDegree : ℝ)) (k : ℤ) (p.leadingCoeff / q.leadingCoeff) := by
  classical
  obtain ⟨Tq, hTq, hqne⟩ := exists_height_polyEval_ne_zero hq
  have hbase := hasShiftTubeDatum_multiMonomial (M := M) hM (r := 0) (fun _ => 0)
    (fun i => i.elim0) (fun _ => 0) (c := 1) one_ne_zero (q := p) (p := q) hp hq (k : ℤ)
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Finset.prod_empty, one_mul, mul_one,
    zero_add] at hbase
  refine ⟨hbase.1, ?_⟩
  have hmul := hbase.2.mul (tubeLimit_clog_div_vertLog_pow hM k)
  rw [mul_one] at hmul
  refine hmul.congr (T₀ := max 3 Tq) fun σ t hσ hσM ht => ?_
  have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htpos : (0 : ℝ) < t := by linarith
  have hL : vertLog t ≠ 0 := vertLog_ne_zero_of_three_le ht3
  have hQ := hqne σ t (le_trans (le_max_right _ _) ht)
  have hshape : gammaShiftShape 0 σ 0 ((p.natDegree : ℝ) - (q.natDegree : ℝ)) (k : ℤ) t ≠ 0 :=
    gammaShiftShape_ne_zero (by linarith) ht3 _ _ _
  simp only [zpow_natCast, div_pow]
  field_simp

end

end GaloisForLFunctions.HTGeometry
