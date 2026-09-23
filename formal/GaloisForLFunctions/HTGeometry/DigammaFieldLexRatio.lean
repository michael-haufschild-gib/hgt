import GaloisForLFunctions.HTGeometry.DigammaFieldRatio

/-!
# Lexicographic dominance on the digamma field

The digamma grows logarithmically while the argument grows linearly, so any power of the digamma is
negligible against a positive power of the argument.  Consequently a ratio whose rational datum has
strictly smaller degree vanishes no matter what the digamma exponents are, and the componentwise
dominance of the previous file upgrades to lexicographic dominance in `(degree, digamma exponent)`.

This is eq. (5) for the digamma field in its final form: a finite family normalized by a
lexicographically minimal member has a constant projective limit, nonzero exactly at the members
sharing the minimal datum.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- A power of the logarithm is negligible against the identity. -/
theorem tendsto_pow_log_div_self (j : ℕ) :
    Tendsto (fun t : ℝ => Real.log t ^ j / t) atTop (nhds 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 j one_ne_zero
  simpa using h

/-- The leading logarithm is bounded by the real logarithm plus the constant phase. -/
theorem norm_vertLog_le {t : ℝ} (ht : 1 ≤ t) : ‖vertLog t‖ ≤ Real.log t + Real.pi / 2 := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have hre : (vertLog t).re = Real.log t := by simp [vertLog]
  have him : (vertLog t).im = Real.pi / 2 := by simp [vertLog]
  calc ‖vertLog t‖ ≤ |(vertLog t).re| + |(vertLog t).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log t + Real.pi / 2 := by
        rw [hre, him, abs_of_nonneg hlog, abs_of_nonneg (by positivity)]

/-- **Logarithmic growth is negligible against the argument.**  A power of the digamma divided by a
positive power of the argument vanishes on a vertical line. -/
theorem tendsto_digamma_pow_div_vertical_pow {σ : ℝ} (hσ : 0 ≤ σ) (j : ℕ) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ m) atTop (nhds 0) := by
  set c : ℝ := Real.pi / 2 + 1 with hc
  have hcpos : 0 < c := by positivity
  have hsub : Tendsto (fun t : ℝ =>
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖) atTop (nhds 0) := by
    rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact RHTower.digamma_vertical_sub_log_I_tendsto_zero σ hσ
  have hbound : ∀ᶠ t : ℝ in atTop,
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ j
        / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ m‖ ≤ 2 ^ j * (Real.log t ^ j / t) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.exp c),
      hsub.eventually_le_const (by norm_num : (0:ℝ) < 1)] with t ht1 htc hdiff
    have hlog : 0 ≤ Real.log t := Real.log_nonneg ht1
    have hlogc : c ≤ Real.log t := by
      have := Real.log_le_log (Real.exp_pos c) htc
      rwa [Real.log_exp] at this
    have hpsi : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ 2 * Real.log t := by
      have h1 : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ ‖vertLog t‖ + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖ := by
        calc ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
            = ‖vertLog t + (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t)‖ := by
              ring_nf
          _ ≤ _ := norm_add_le _ _
      have h2 := norm_vertLog_le ht1
      have : Real.pi / 2 + 1 ≤ Real.log t := hlogc
      linarith
    have hnormz : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by
      have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
      calc t = |((σ : ℂ) + (t : ℂ) * Complex.I).im| := by
            rw [him, abs_of_nonneg (by linarith)]
        _ ≤ _ := Complex.abs_im_le_norm _
    have htpos : (0 : ℝ) < t := by linarith
    have hden : t ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ m := by
      calc t = t ^ (1 : ℕ) := (pow_one t).symm
        _ ≤ t ^ m := pow_le_pow_right₀ ht1 hm
        _ ≤ ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ m := pow_le_pow_left₀ (by linarith) hnormz m
    rw [norm_div, norm_pow, norm_pow]
    have hnum : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ j ≤ (2 * Real.log t) ^ j :=
      pow_le_pow_left₀ (norm_nonneg _) hpsi j
    have hdenpos : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ m := by
      have : (0 : ℝ) < ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ := by linarith
      positivity
    calc ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ j
          / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ m
        ≤ (2 * Real.log t) ^ j / ‖(σ : ℂ) + (t : ℂ) * Complex.I‖ ^ m := by
          gcongr
      _ ≤ (2 * Real.log t) ^ j / t := by
          gcongr
      _ = 2 ^ j * (Real.log t ^ j / t) := by
          rw [mul_pow]
          ring
  refine squeeze_zero_norm' hbound ?_
  have := (tendsto_pow_log_div_self j).const_mul ((2 : ℝ) ^ j)
  simpa using this

/-- **Eq. (5), strict-degree case.**  When the rational datum of the numerator has strictly smaller
degree, the ratio vanishes whatever the digamma exponents: logarithmic growth cannot compensate a
power of the argument. -/
theorem tendsto_ratio_digammaField_of_degree_lt {σ : ℝ} (hσ : 0 < σ)
    (pa qa pb qb : Polynomial ℂ) (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0) {Da Db : ℕ}
    (hlt : (pa * qb).natDegree < (qa * pb).natDegree) :
    Tendsto (fun t : ℝ =>
      ((pa.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / qa.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
          * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Da)
        / ((pb.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / qb.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
          * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Db)) atTop (nhds 0) := by
  have hv : qa * pb ≠ 0 := mul_ne_zero hqa hpb
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (qa * pb).natDegree = (pa * qb).natDegree + m :=
    ⟨(qa * pb).natDegree - (pa * qb).natDegree, by omega⟩
  have hmpos : 0 < m := by omega
  have hA := tendsto_ratio_eval_vertical σ (pa * qb) (qa * pb) hv
  have hB := tendsto_digamma_pow_div_vertical_pow (le_of_lt hσ) Da hmpos
  have hC := tendsto_digamma_pow_ratio (le_of_lt hσ) (Da := 0) (Db := Db) (Nat.zero_le Db)
  have hprod := (hA.mul hB).mul hC
  rw [mul_zero, zero_mul] at hprod
  refine hprod.congr' ?_
  have hne : ∀ᶠ t : ℝ in atTop, Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [(tendsto_norm_digamma_vertical (le_of_lt hσ)).eventually_gt_atTop 0] with t ht
    intro h
    rw [h] at ht
    simp at ht
  filter_upwards [eventually_vertical_ne_zero σ, eventually_eval_ne_zero σ hqa,
    eventually_eval_ne_zero σ hqb, eventually_eval_ne_zero σ hpb, hne] with t hs hqat hqbt hpbt hψt
  simp only [Polynomial.eval_mul, pow_zero]
  rw [hm, pow_add]
  field_simp

/-- **Eq. (5) for the digamma field, lexicographic form.**  A numerator dominated lexicographically
in `(degree, digamma exponent)` has a convergent normalized ratio, with nonzero limit exactly when
both data agree. -/
theorem tendsto_ratio_digammaField_lex {σ : ℝ} (hσ : 0 < σ)
    (pa qa pb qb : Polynomial ℂ) (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0) {Da Db : ℕ}
    (hlex : (pa * qb).natDegree < (qa * pb).natDegree ∨
      ((pa * qb).natDegree = (qa * pb).natDegree ∧ Da ≤ Db)) :
    Tendsto (fun t : ℝ =>
      ((pa.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / qa.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
          * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Da)
        / ((pb.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / qb.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
          * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Db)) atTop
      (nhds (if (pa * qb).natDegree = (qa * pb).natDegree ∧ Da = Db
              then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0)) := by
  classical
  rcases hlex with hlt | ⟨hdeq, hD⟩
  · rw [if_neg (fun h => absurd h.1 (Nat.ne_of_lt hlt))]
    exact tendsto_ratio_digammaField_of_degree_lt hσ pa qa pb qb hqa hqb hpb hlt
  · have h := tendsto_ratio_digammaField hσ pa qa pb qb hqa hqb hpb (le_of_eq hdeq) hD
    by_cases hDeq : Da = Db
    · rw [if_pos ⟨hdeq, hDeq⟩]
      rw [if_pos hdeq, if_pos hDeq, mul_one] at h
      exact h
    · rw [if_neg (fun hc => hDeq hc.2)]
      rw [if_pos hdeq, if_neg hDeq, mul_zero] at h
      exact h

end GaloisForLFunctions
