import GaloisForLFunctions.HTGeometry.DigammaVerticalUniformLog
import GaloisForLFunctions.HTGeometry.DigammaLogPowers

/-!
# Powers of digamma against powers of the vertical logarithm, uniformly on a tube

`ψ(σ+it)/(log t + iπ/2) → 1` holds uniformly on a vertical tube, because the difference
`ψ − (log t + iπ/2)` is `O(1/t)` there while the logarithm grows.  Raising to a power costs only a
factor `2^e`, since a number within `1` of `1` has modulus at most `2`.

This is the logarithmic level of the tube form of eq. (19): the `ψ`-degree of a jet polynomial
contributes its power of the logarithm uniformly in the abscissa.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A power of a number close to `1` stays close to `1`. -/
theorem norm_pow_sub_one_le_of_norm_sub_one_le {x : ℂ} (hx : ‖x - 1‖ ≤ 1) (e : ℕ) :
    ‖x ^ e - 1‖ ≤ 2 ^ e * ‖x - 1‖ := by
  have hxle : ‖x‖ ≤ 2 := by
    have := norm_add_le (x - 1) 1
    simp only [sub_add_cancel, norm_one] at this
    linarith
  have hgeom : (∑ i ∈ Finset.range e, x ^ i) * (x - 1) = x ^ e - 1 := geom_sum_mul x e
  rw [← hgeom, norm_mul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc ‖∑ i ∈ Finset.range e, x ^ i‖ ≤ ∑ i ∈ Finset.range e, ‖x ^ i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range e, (2 : ℝ) ^ i := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) hxle i
    _ = 2 ^ e - 1 := by
        rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
        ring
    _ ≤ 2 ^ e := by
        have : (0 : ℝ) < 1 := one_pos
        linarith

/-- **Digamma against the vertical logarithm, uniformly on a tube.** -/
theorem exists_uniform_height_digamma_div_vertLog {M : ℝ} (hM : 0 < M) {ε : ℝ} (hε : 0 < ε) :
    ∃ T : ℝ, ∀ σ t : ℝ, 0 ≤ σ → σ ≤ M → T ≤ t →
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t - 1‖ ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_bound_digamma_sub_vertLog hM
  refine ⟨max 3 (C / ε + 1), fun σ t hσ hσM ht => ?_⟩
  have ht3 : (3 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htC : C / ε + 1 ≤ t := le_trans (le_max_right _ _) ht
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htpos : (0 : ℝ) < t := by linarith
  -- the logarithm has modulus at least one
  have hlogre : (vertLog t).re = Real.log t := by
    rw [vertLog]
    simp
  have hlog1 : (1 : ℝ) ≤ ‖vertLog t‖ := by
    have hlogt : (1 : ℝ) ≤ Real.log t := by
      have hexp : Real.exp 1 ≤ t := le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith)
      have := Real.log_le_log (Real.exp_pos 1) hexp
      rwa [Real.log_exp] at this
    calc (1 : ℝ) ≤ Real.log t := hlogt
      _ = (vertLog t).re := hlogre.symm
      _ ≤ ‖vertLog t‖ := Complex.re_le_norm _
  have hlogne : vertLog t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlog1
    linarith
  -- the difference divided by the logarithm
  have hsplit : Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t - 1
      = (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t) / vertLog t := by
    field_simp
  rw [hsplit, norm_div]
  have hnum := hbound σ t hσ hσM ht1
  have hCt : C / t ≤ ε := by
    rw [div_le_iff₀ htpos]
    have hCe : C / ε ≤ t := by linarith
    rw [div_le_iff₀ hε] at hCe
    nlinarith
  calc ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖ / ‖vertLog t‖
      ≤ ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖ :=
        div_le_self (norm_nonneg _) hlog1
    _ ≤ C / t := hnum
    _ ≤ ε := hCt

/-- **Powers of digamma against powers of the vertical logarithm, uniformly on a tube.** -/
theorem exists_uniform_height_digamma_pow_div_vertLog_pow {M : ℝ} (hM : 0 < M) (e : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T : ℝ, ∀ σ t : ℝ, 0 ≤ σ → σ ≤ M → T ≤ t →
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e / vertLog t ^ e - 1‖ ≤ ε := by
  have hpos : 0 < min 1 (ε / 2 ^ e) := by positivity
  obtain ⟨T, hT⟩ := exists_uniform_height_digamma_div_vertLog hM hpos
  refine ⟨T, fun σ t hσ hσM ht => ?_⟩
  have hclose := hT σ t hσ hσM ht
  have hle1 : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t - 1‖ ≤ 1 :=
    le_trans hclose (min_le_left _ _)
  have hpow := norm_pow_sub_one_le_of_norm_sub_one_le hle1 e
  rw [← div_pow]
  refine le_trans hpow ?_
  have hstep : ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t - 1‖
      ≤ ε / 2 ^ e := le_trans hclose (min_le_right _ _)
  calc (2 : ℝ) ^ e * ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t - 1‖
      ≤ 2 ^ e * (ε / 2 ^ e) := mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ε := by field_simp

end

end GaloisForLFunctions.HTGeometry
