import GaloisForLFunctions.HTGeometry.IntegerSeriesBounds

/-!
# Power weights on the integer lattice

The weight `1/(1 + |j|)^s` is summable over `ℤ` for every real `s > 1`, its `ℝ≥0∞` total is
finite, and therefore its tails outside a finite band are arbitrarily small.  The quadratic weight
is the case `s = 2`.

Sub-quadratic exponents are what a band-split estimate needs when the amplitudes it is applied to
have been convolved: a product of two sequences decaying like `1/(1+|j|)` decays like
`log(2+|j|)/(1+|j|)`, which is dominated by `1/(1+|j|)^θ` for every `θ < 1`, so the weight
`1/(1+|j|)^(2θ)` with `2θ > 1` absorbs the logarithmic loss.

Summability is obtained, as for the quadratic weight, by comparison with the half-integer shifted
series `1/|j + 1/2|^s`, which never meets its own singularity.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions

/-- **The power integer weight is summable** for every exponent above one. -/
theorem summable_one_div_one_add_abs_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun j : ℤ => 1 / (1 + |(j : ℝ)|) ^ s) := by
  have hbase : Summable (fun j : ℤ => 1 / |(j : ℝ) + (1 / 2 : ℝ)| ^ s) :=
    (Real.summable_one_div_int_add_rpow (1 / 2) s).mpr hs
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hbase
  have hpos : 0 < |(j : ℝ) + 1 / 2| := abs_int_add_half_pos j
  have hle : |(j : ℝ) + 1 / 2| ≤ 1 + |(j : ℝ)| := by
    rcases abs_cases ((j : ℝ) + 1 / 2) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
      rcases abs_cases ((j : ℝ)) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
        rw [h1, h2] <;> linarith
  refine div_le_div_of_nonneg_left (by norm_num) (by positivity) ?_
  exact Real.rpow_le_rpow hpos.le hle (by linarith)

/-- The power integer weight, valued in `ℝ≥0∞`. -/
noncomputable def intPowWeight (s : ℝ) (j : ℤ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (1 + |(j : ℝ)|) ^ s)

theorem intPowWeight_two : intPowWeight 2 = intQuadWeight := by
  funext j
  rw [intPowWeight, intQuadWeight]
  congr 2
  rw [← Real.rpow_natCast (1 + |(j : ℝ)|) 2]
  norm_num

/-- The total power weight is finite. -/
theorem tsum_intPowWeight_ne_top {s : ℝ} (hs : 1 < s) :
    (∑' j : ℤ, intPowWeight s j) ≠ ⊤ := by
  have hsummable : Summable (fun j : ℤ => (1 / (1 + |(j : ℝ)|) ^ s).toNNReal) := by
    rw [← NNReal.summable_coe]
    refine (summable_one_div_one_add_abs_rpow hs).congr fun j => ?_
    rw [Real.coe_toNNReal _ (by positivity)]
  have hrepr : (∑' j : ℤ, intPowWeight s j)
      = ∑' j : ℤ, (((1 / (1 + |(j : ℝ)|) ^ s).toNNReal : ℝ≥0) : ℝ≥0∞) := rfl
  rw [hrepr]
  exact ENNReal.tsum_coe_ne_top_iff_summable.mpr hsummable

theorem tsum_const_mul_intPowWeight_ne_top {s : ℝ} (hs : 1 < s) {C : ℝ≥0∞} (hC : C ≠ ⊤) :
    (∑' j : ℤ, C * intPowWeight s j) ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left]
  exact ENNReal.mul_ne_top hC (tsum_intPowWeight_ne_top hs)

/-- **Uniformly small tails** for a power weight above exponent one. -/
theorem exists_finset_tsum_compl_intPowWeight_le {s : ℝ} (hs : 1 < s) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ S : Finset ℤ, ∑' j : {x : ℤ // x ∉ S}, C * intPowWeight s (j : ℤ) ≤ ε := by
  have htail := ENNReal.tendsto_tsum_compl_atTop_zero
    (tsum_const_mul_intPowWeight_ne_top hs hC)
  obtain ⟨S, hS⟩ := (ENNReal.tendsto_nhds_zero.mp htail ε hε).exists
  exact ⟨S, hS⟩

/-! ## Logarithmic losses are absorbed by any sub-linear power -/

/-- A logarithmic loss on a linearly decaying sequence is dominated by any power below one:
`log(2+x)/(1+x) ≤ C/(1+x)^θ` for `0 < θ < 1`. -/
theorem log_div_le_rpow_div {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 0 ≤ x →
      Real.log (2 + x) / (1 + x) ≤ C / (1 + x) ^ θ := by
  have hpos : 0 < 1 - θ := by linarith
  refine ⟨2 / (1 - θ) + Real.log 2, by positivity, fun x hx => ?_⟩
  have h1 : (0 : ℝ) < 1 + x := by linarith
  have hlog : Real.log (2 + x) ≤ Real.log 2 + Real.log (1 + x) := by
    have hle : (2 : ℝ) + x ≤ 2 * (1 + x) := by linarith
    calc Real.log (2 + x) ≤ Real.log (2 * (1 + x)) :=
          Real.log_le_log (by linarith) hle
      _ = Real.log 2 + Real.log (1 + x) := by
          rw [Real.log_mul (by norm_num) (by linarith)]
  have hpow : Real.log (1 + x) ≤ (1 - θ)⁻¹ * (1 + x) ^ (1 - θ) := by
    have h := Real.log_le_rpow_div (x := 1 + x) (by linarith) hpos
    calc Real.log (1 + x) ≤ (1 + x) ^ (1 - θ) / (1 - θ) := h
      _ = (1 - θ)⁻¹ * (1 + x) ^ (1 - θ) := by
          rw [div_eq_inv_mul]
  have hone : (1 : ℝ) ≤ (1 + x) ^ (1 - θ) := Real.one_le_rpow (by linarith) hpos.le
  have hsplit : (1 + x) = (1 + x) ^ (1 - θ) * (1 + x) ^ θ := by
    rw [← Real.rpow_add h1]
    norm_num
  rw [div_le_div_iff₀ h1 (by positivity)]
  have hlogle : Real.log (2 + x) ≤ (Real.log 2 + (1 - θ)⁻¹) * (1 + x) ^ (1 - θ) := by
    have hL2 : Real.log 2 ≤ Real.log 2 * (1 + x) ^ (1 - θ) := by
      nlinarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2), hone]
    calc Real.log (2 + x) ≤ Real.log 2 + Real.log (1 + x) := hlog
      _ ≤ Real.log 2 * (1 + x) ^ (1 - θ) + (1 - θ)⁻¹ * (1 + x) ^ (1 - θ) := by
          linarith
      _ = (Real.log 2 + (1 - θ)⁻¹) * (1 + x) ^ (1 - θ) := by ring
  have hCle : Real.log 2 + (1 - θ)⁻¹ ≤ 2 / (1 - θ) + Real.log 2 := by
    have : (1 - θ)⁻¹ ≤ 2 / (1 - θ) := by
      rw [inv_eq_one_div, div_le_div_iff₀ hpos hpos]
      nlinarith
    linarith
  calc Real.log (2 + x) * (1 + x) ^ θ
      ≤ ((Real.log 2 + (1 - θ)⁻¹) * (1 + x) ^ (1 - θ)) * (1 + x) ^ θ := by
        refine mul_le_mul_of_nonneg_right hlogle (by positivity)
    _ = (Real.log 2 + (1 - θ)⁻¹) * (1 + x) := by rw [mul_assoc, ← hsplit]
    _ ≤ (2 / (1 - θ) + Real.log 2) * (1 + x) := by
        exact mul_le_mul_of_nonneg_right hCle (by linarith)

end GaloisForLFunctions
