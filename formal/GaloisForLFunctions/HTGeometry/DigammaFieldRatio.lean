import GaloisForLFunctions.HTGeometry.DigammaFieldValuationRational

/-!
# The projective boundary of the digamma field

The digamma grows on a vertical line, so a power with a smaller exponent is negligible against a
larger one, and a quotient of polynomials of no larger degree converges — to the quotient of the
leading coefficients when the degrees agree, and to zero otherwise.

Multiplying the two gives eq. (5) for the elements `R(s)·ψ^D` of `ℂ(s)⟨ψ⟩`: a componentwise
dominated numerator has a convergent normalized ratio, with the limit nonzero exactly when both the
degree datum and the digamma exponent agree.
-/

open Filter Topology Complex Polynomial

namespace GaloisForLFunctions

/-- The digamma modulus grows along a vertical line. -/
theorem tendsto_norm_digamma_vertical {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun t : ℝ => ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖) atTop atTop := by
  have hsub : Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t) atTop (nhds 0) :=
    RHTower.digamma_vertical_sub_log_I_tendsto_zero σ hσ
  have hnorm : Tendsto (fun t : ℝ =>
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖) atTop (nhds 0) := by
    rw [← tendsto_zero_iff_norm_tendsto_zero] at *
    exact hsub
  have hbound : ∀ᶠ t : ℝ in atTop,
      ‖vertLog t‖ - 1 ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
    filter_upwards [hnorm.eventually_le_const (by norm_num : (0:ℝ) < 1)] with t ht
    have htri : ‖vertLog t‖ ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
        + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖ := by
      calc ‖vertLog t‖
          = ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)
              - (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t)‖ := by ring_nf
        _ ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖
              + ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖ :=
            norm_sub_le _ _
    linarith
  refine tendsto_atTop_mono' atTop hbound ?_
  exact tendsto_atTop_add_const_right _ _ tendsto_norm_vertLog

/-- Powers of the digamma with a smaller exponent are negligible. -/
theorem tendsto_digamma_pow_ratio {σ : ℝ} (hσ : 0 ≤ σ) {Da Db : ℕ} (hD : Da ≤ Db) :
    Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Da
        / Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Db) atTop
      (nhds (if Da = Db then 1 else 0)) := by
  have hne : ∀ᶠ t : ℝ in atTop, Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [(tendsto_norm_digamma_vertical hσ).eventually_gt_atTop 0] with t ht
    intro h
    rw [h] at ht
    simp at ht
  by_cases hEq : Da = Db
  · subst hEq
    rw [if_pos rfl]
    refine (tendsto_const_nhds (x := (1 : ℂ)) (f := atTop (α := ℝ))).congr' ?_
    filter_upwards [hne] with t ht
    rw [div_self (pow_ne_zero _ ht)]
  · rw [if_neg hEq]
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Db = Da + k := ⟨Db - Da, by omega⟩
    have hkpos : 0 < k := by omega
    have hinv : Tendsto (fun t : ℝ =>
        1 / Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ k) atTop (nhds 0) := by
      have hpow : Tendsto (fun t : ℝ =>
          ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ k) atTop atTop :=
        (tendsto_pow_atTop hkpos.ne').comp (tendsto_norm_digamma_vertical hσ)
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine hpow.inv_tendsto_atTop.congr fun t => ?_
      simp [norm_pow]
    refine hinv.congr' ?_
    filter_upwards [hne] with t ht
    rw [hk, pow_add]
    field_simp

/-- A nonzero polynomial is eventually nonvanishing on a vertical line. -/
theorem eventually_eval_ne_zero (σ : ℝ) {p : Polynomial ℂ} (hp : p ≠ 0) :
    ∀ᶠ t : ℝ in atTop, p.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
  have h := tendsto_eval_div_pow_natDegree_vertical σ p
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  filter_upwards [h.eventually_ne hlead] with t ht
  intro hz
  exact ht (by rw [hz, zero_div])

/-- **The projective boundary of a quotient of polynomials on a vertical line.** -/
theorem tendsto_ratio_poly_le (σ : ℝ) (u v : Polynomial ℂ) (hv : v ≠ 0)
    (hdeg : u.natDegree ≤ v.natDegree) :
    Tendsto (fun t : ℝ =>
      u.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / v.eval ((σ : ℂ) + (t : ℂ) * Complex.I)) atTop
      (nhds (if u.natDegree = v.natDegree then u.leadingCoeff / v.leadingCoeff else 0)) := by
  have hu := tendsto_eval_div_pow_natDegree_vertical σ u
  have hvv := tendsto_eval_div_pow_natDegree_vertical σ v
  have hvlead : v.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hv
  have hratio := hu.div hvv hvlead
  by_cases hEq : u.natDegree = v.natDegree
  · rw [if_pos hEq]
    refine hratio.congr' ?_
    filter_upwards [eventually_vertical_ne_zero σ, eventually_eval_ne_zero σ hv] with t ht hvt
    simp only [Pi.div_apply]
    rw [hEq]
    field_simp
  · rw [if_neg hEq]
    have hlt : u.natDegree < v.natDegree := lt_of_le_of_ne hdeg hEq
    obtain ⟨k, hk⟩ : ∃ k : ℕ, v.natDegree = u.natDegree + k := ⟨v.natDegree - u.natDegree, by omega⟩
    have hkpos : 0 < k := by omega
    have hprod := hratio.mul (tendsto_one_div_vertical_pow σ hkpos)
    rw [mul_zero] at hprod
    refine hprod.congr' ?_
    filter_upwards [eventually_vertical_ne_zero σ, eventually_eval_ne_zero σ hv] with t ht hvt
    simp only [Pi.div_apply]
    rw [hk, pow_add]
    field_simp

/-- **Eq. (5) for the digamma field.**  The ratio of two monomial elements `R(s)·ψ^D` of
`ℂ(s)⟨ψ⟩` converges whenever the numerator is dominated componentwise: to the quotient of the
leading coefficients when both data agree, and to zero otherwise. -/
theorem tendsto_ratio_digammaField {σ : ℝ} (hσ : 0 < σ)
    (pa qa pb qb : Polynomial ℂ) (hqa : qa ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0) {Da Db : ℕ}
    (hdeg : (pa * qb).natDegree ≤ (qa * pb).natDegree) (hD : Da ≤ Db) :
    Tendsto (fun t : ℝ =>
      ((pa.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / qa.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
          * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Da)
        / ((pb.eval ((σ : ℂ) + (t : ℂ) * Complex.I) / qb.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
          * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ Db)) atTop
      (nhds ((if (pa * qb).natDegree = (qa * pb).natDegree
                then (pa * qb).leadingCoeff / (qa * pb).leadingCoeff else 0)
              * (if Da = Db then 1 else 0))) := by
  have hqapb : qa * pb ≠ 0 := mul_ne_zero hqa hpb
  have hrat := tendsto_ratio_poly_le σ (pa * qb) (qa * pb) hqapb hdeg
  have hjet := tendsto_digamma_pow_ratio (le_of_lt hσ) hD
  have hmul := hrat.mul hjet
  refine hmul.congr' ?_
  have hne : ∀ᶠ t : ℝ in atTop,
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    filter_upwards [(tendsto_norm_digamma_vertical (le_of_lt hσ)).eventually_gt_atTop 0] with t ht
    intro h
    rw [h] at ht
    simp at ht
  filter_upwards [eventually_eval_ne_zero σ hqa, eventually_eval_ne_zero σ hqb,
    eventually_eval_ne_zero σ hpb, hne] with t hqat hqbt hpbt hψt
  simp only [Polynomial.eval_mul]
  field_simp

end GaloisForLFunctions
