import GaloisForLFunctions.RHTower.BaezDuarteGramDiscrete

/-!
# The pairing series, and the identity `∑ (n mod m)/(n(n+1)) = log m`

`BaezDuarteGramDiscrete` showed that the Báez-Duarte generator at `θ = 1/m` is piecewise constant:
`bdGenReal (1/m) v = (a mod m)/(m·v)` on the cell `(a, a+1)`.  Pairing it with the target `1/v` and summing
the cells evaluates the right-hand side of the normal equations as a rational series.  Comparing with the
closed form `⟪bdGen θ, bdTarget⟫ = −θ log θ` of `BaezDuarteTargetPairing` gives an exact arithmetic identity
that neither computation produces on its own:

**`hasSum_mod_div_mul_succ` — `∑_{n≥1} (n mod m)/(n(n+1)) = log m`.**

Both sides are elementary and unconditional; the logarithm on the right comes from the dilation identity of
the pairing, and the left side is pure cell counting.  For `m = 1` both sides vanish; for `m = 2` it is the
classical `∑_{n odd} 1/(n(n+1)) = log 2`.

With this, both data of the discrete Báez-Duarte normal system are explicit rational series: the matrix by
`hasSum_bdGram_discrete` and the right-hand side by `hasSum_pairing_discrete`.
-/

open MeasureTheory Set
open scoped Topology

noncomputable section

namespace RHTower

/-- The pointwise bound behind every integrability argument in this layer. -/
theorem abs_bdGenReal_le {θ : ℝ} (hθ : |θ| ≤ 1) {v : ℝ} (hv : 0 < v) :
    |bdGenReal θ v| ≤ 2 * v⁻¹ := by
  rw [bdGenReal, abs_div, abs_of_pos hv, div_le_iff₀ hv]
  have h1 : |Int.fract (θ * v) - θ * Int.fract v| ≤ 2 := by
    refine le_trans (abs_sub _ _) ?_
    have hA : |Int.fract (θ * v)| ≤ 1 := by
      rw [abs_of_nonneg (Int.fract_nonneg _)]
      exact (Int.fract_lt_one _).le
    have hB : |θ * Int.fract v| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (Int.fract_nonneg v)]
      calc |θ| * Int.fract v ≤ 1 * 1 :=
            mul_le_mul hθ (Int.fract_lt_one _).le (Int.fract_nonneg _) (by positivity)
        _ = 1 := one_mul 1
    linarith
  calc |Int.fract (θ * v) - θ * Int.fract v| ≤ 2 := h1
    _ = 2 * v⁻¹ * v := by field_simp

theorem integrableOn_bdGenReal_mul_inv {θ : ℝ} (hθ : |θ| ≤ 1) :
    IntegrableOn (fun v => bdGenReal θ v * v⁻¹) (Ioi 1) := by
  have hmeas : Measurable (fun v : ℝ => bdGenReal θ v * v⁻¹) := by
    refine Measurable.mul ?_ measurable_id.inv
    exact ((measurable_fract.comp (measurable_const_mul θ)).sub
      ((measurable_const).mul measurable_fract)).div measurable_id
  refine Integrable.mono' (g := fun v => 2 * v ^ (-2 : ℝ))
    ((integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul 2)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
  have hv0 : (0 : ℝ) < v := lt_trans zero_lt_one (mem_Ioi.mp hv)
  rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos hv0, ← inv_sq_eq_rpow hv0]
  calc |bdGenReal θ v| * v⁻¹ ≤ (2 * v⁻¹) * v⁻¹ :=
        mul_le_mul_of_nonneg_right (abs_bdGenReal_le hθ hv0) (by positivity)
    _ = 2 * (v⁻¹) ^ 2 := by ring

/-- **The pairing on one cell.** -/
theorem integral_tailCell_bdGenReal_mul_inv {m : ℕ} (hm : 1 ≤ m) (n : ℕ) :
    (∫ v in tailCell n, bdGenReal (1 / (m : ℝ)) v * v⁻¹)
      = (((n + 1) % m : ℕ) : ℝ) / ((m : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  set a : ℕ := n + 1 with ha
  have haR : ((a : ℕ) : ℝ) = (n : ℝ) + 1 := by rw [ha]; push_cast; ring
  have hcell : tailCell n = Ioc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1) := by
    rw [tailCell, haR, show ((n : ℝ) + 2) = ((n : ℝ) + 1) + 1 from by ring]
  have hmR : ((m : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    exact ne_of_gt this
  have hcongr : ∀ v ∈ Ioo ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1),
      bdGenReal (1 / (m : ℝ)) v * v⁻¹
        = ((a % m : ℕ) : ℝ) / (m : ℝ) * (v⁻¹) ^ 2 := by
    intro v hv
    have hv0 : (0 : ℝ) < v := lt_of_le_of_lt (Nat.cast_nonneg a) hv.1
    have hvne : v ≠ 0 := ne_of_gt hv0
    rw [bdGenReal_inv_nat_eq_of_mem_cell hm hv]
    field_simp
  have hpos : (0 : ℝ) < ((a : ℕ) : ℝ) := by rw [haR]; positivity
  have hle : ((a : ℕ) : ℝ) ≤ ((a : ℕ) : ℝ) + 1 := by linarith
  have hzero : (0 : ℝ) ∉ Set.uIcc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1) := by
    rw [Set.uIcc_of_le hle, Set.mem_Icc]
    intro h
    linarith [h.1]
  have hsq : (∫ v in ((a : ℕ) : ℝ)..(((a : ℕ) : ℝ) + 1), (v⁻¹) ^ 2)
      = 1 / ((a : ℕ) : ℝ) - 1 / (((a : ℕ) : ℝ) + 1) := by
    have hcongr2 : ∀ v ∈ Set.uIcc ((a : ℕ) : ℝ) (((a : ℕ) : ℝ) + 1), (v⁻¹) ^ 2 = v ^ (-2 : ℤ) := by
      intro v _
      rw [show (-2 : ℤ) = -((2 : ℕ) : ℤ) from by norm_num, zpow_neg, zpow_natCast, ← inv_pow]
    rw [intervalIntegral.integral_congr hcongr2, integral_zpow (Or.inr ⟨by norm_num, hzero⟩)]
    have hane : ((a : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
    have hane1 : ((a : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  rw [hcell, MeasureTheory.integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hcongr,
    ← MeasureTheory.integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hle,
    intervalIntegral.integral_const_mul, hsq]
  have hane : ((a : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
  rw [haR] at hane ⊢
  rw [ha]
  field_simp
  ring

/-- **The right-hand side of the normal system as a rational series.** -/
theorem hasSum_pairing_discrete {m : ℕ} (hm : 1 ≤ m) :
    HasSum (fun n : ℕ => (((n + 1) % m : ℕ) : ℝ) / ((m : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (Real.log (m : ℝ) / (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have habs : |1 / (m : ℝ)| ≤ 1 := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    rw [abs_of_pos (by positivity), div_le_one hm0]
    exact hm1
  have hint : IntegrableOn (fun v => bdGenReal (1 / (m : ℝ)) v * v⁻¹) (⋃ n : ℕ, tailCell n) := by
    rw [iUnion_tailCell]
    exact integrableOn_bdGenReal_mul_inv habs
  have h := MeasureTheory.hasSum_integral_iUnion measurableSet_tailCell
    pairwise_disjoint_tailCell hint
  rw [iUnion_tailCell] at h
  have hval : (∫ v in Ioi (1:ℝ), bdGenReal (1 / (m : ℝ)) v * v⁻¹)
      = Real.log (m : ℝ) / (m : ℝ) := by
    have hθ0 : (0 : ℝ) < 1 / (m : ℝ) := by positivity
    have hθ1 : 1 / (m : ℝ) ≤ 1 := by
      rw [div_le_one hm0]
      exact_mod_cast hm
    rw [integral_bdGenReal_mul_inv hθ0 hθ1, Real.log_div one_ne_zero (ne_of_gt hm0),
      Real.log_one]
    field_simp
    ring
  rw [hval] at h
  exact (funext (fun n => integral_tailCell_bdGenReal_mul_inv hm n)) ▸ h

/-- **`∑_{n≥1} (n mod m)/(n(n+1)) = log m`.**  The two evaluations of the same pairing — cell counting on one
side, the dilation identity on the other — meet in an exact arithmetic identity. -/
theorem hasSum_mod_div_mul_succ {m : ℕ} (hm : 1 ≤ m) :
    HasSum (fun n : ℕ => (((n + 1) % m : ℕ) : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)))
      (Real.log (m : ℝ)) := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have h := (hasSum_pairing_discrete hm).mul_left (m : ℝ)
  have hterm : ∀ n : ℕ, (m : ℝ) * ((((n + 1) % m : ℕ) : ℝ)
      / ((m : ℝ) * ((n : ℝ) + 1) * ((n : ℝ) + 2)))
      = (((n + 1) % m : ℕ) : ℝ) / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
    intro n
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    field_simp
  have hval : (m : ℝ) * (Real.log (m : ℝ) / (m : ℝ)) = Real.log (m : ℝ) := by
    field_simp
  rw [hval] at h
  exact (funext hterm) ▸ h

end RHTower

end
