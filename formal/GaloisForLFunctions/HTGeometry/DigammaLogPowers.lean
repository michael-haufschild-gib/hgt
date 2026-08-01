import GaloisForLFunctions.HTGeometry.DigammaFieldValuation

/-!
# Powers of digamma against powers of the vertical logarithm

The digamma function differs from the vertical logarithm by a vanishing amount, so each power of
digamma has the corresponding power of the logarithm as its datum:

`ψ(σ+it)^e / (log t + iπ/2)^e → 1`.

This is the logarithmic level of the residue law for a pure power, the case in which no cancellation
between monomials can occur.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **A power of digamma has the corresponding power of the vertical logarithm as its datum.** -/
theorem tendsto_digamma_pow_div_vertLog_pow (hσ : 0 ≤ σ) (e : ℕ) :
    Tendsto (fun t : ℝ => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e / vertLog t ^ e)
      atTop (nhds 1) := by
  have h := (tendsto_digamma_div_vertLog hσ).pow e
  rw [one_pow] at h
  refine h.congr fun t => ?_
  rw [div_pow]

/-- The same statement normalized: a power of digamma is asymptotic to the power of the logarithm. -/
theorem tendsto_digamma_pow_mul_inv_vertLog_pow (hσ : 0 ≤ σ) (e : ℕ) :
    Tendsto (fun t : ℝ => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e
        * (vertLog t ^ e)⁻¹) atTop (nhds 1) := by
  refine (tendsto_digamma_pow_div_vertLog_pow hσ e).congr fun t => ?_
  rw [div_eq_mul_inv]

/-- **The logarithmic level of a datum.**  Multiplying a function that has a datum by a power of
digamma multiplies the datum by the corresponding power of the vertical logarithm. -/
theorem tendsto_datum_mul_digamma_pow (hσ : 0 ≤ σ) (e : ℕ) {g : ℝ → ℂ} {p : ℕ} {c : ℂ}
    (hg : Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p * g t) atTop (nhds c)) :
    Tendsto (fun t : ℝ => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
        * (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e * g t) / vertLog t ^ e)
      atTop (nhds c) := by
  have hlog := tendsto_digamma_pow_div_vertLog_pow hσ e
  have hmul := hlog.mul hg
  rw [one_mul] at hmul
  refine hmul.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero] with t ht
  have hpow : vertLog t ^ e ≠ 0 := pow_ne_zero _ ht
  field_simp

/-- **A higher power of the vertical logarithm dominates a lower one.**  This is why groups of
different `ψ`-degree cannot cancel: at a fixed order in `s` they carry distinct powers of the
logarithm. -/
theorem tendsto_vertLog_pow_ratio {e e' : ℕ} (h : e' < e) :
    Tendsto (fun t : ℝ => vertLog t ^ e' / vertLog t ^ e) atTop (nhds 0) := by
  obtain ⟨k, hk⟩ : ∃ k, e = e' + (k + 1) := ⟨e - e' - 1, by omega⟩
  have hnorm : Tendsto (fun t : ℝ => ‖vertLog t‖ ^ (k + 1)) atTop atTop :=
    (tendsto_pow_atTop (by omega : k + 1 ≠ 0)).comp tendsto_norm_vertLog
  have hinv := hnorm.inv_tendsto_atTop
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine hinv.congr' ?_
  filter_upwards [eventually_vertLog_ne_zero] with t ht
  have hpow : vertLog t ^ e' ≠ 0 := pow_ne_zero _ ht
  have hval : vertLog t ^ e' / vertLog t ^ e = (vertLog t ^ (k + 1))⁻¹ := by
    rw [hk, pow_add]
    field_simp
  rw [hval, norm_inv, norm_pow]
  rfl

end GaloisForLFunctions
