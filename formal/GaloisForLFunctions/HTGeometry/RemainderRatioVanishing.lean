import GaloisForLFunctions.HTGeometry.FacEnvShiftBound

/-!
# The endpoint remainder is negligible against the normalised coefficient

Combining the remainder bound at the base index with the two-sided coefficient envelope gives

`‖E_M‖ / (‖a_M‖ · M^{smax}) ≤ const · M^{B + B' − smax} ⟶ 0`

as soon as `smax > B + B'`.  Both `B` (the polynomial weight of the endpoint remainder) and `B'`
(the polynomial weight of the coefficient envelope) are fixed by the differential polynomial and the
slope data, while `smax` grows linearly with the endpoint cutoff — so the hypothesis is achieved by
taking the cutoff large.

This supplies, verbatim, the normalised hypothesis of the chirp-independence lemma.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The normalised remainder vanishes.** -/
theorem tendsto_remainder_ratio {r 𝔞 : ℝ} (h𝔞 : 0 < 𝔞) {E : ℕ → ℂ} {A : ℕ → ℝ}
    {B B' R : ℕ} {c₁ K smax : ℝ} (hc₁ : 0 ≤ c₁) (hK : 0 < K)
    (hE : ∀ M : ℕ, R ≤ M → ‖E M‖ ≤ c₁ * (((M + R : ℕ) : ℝ) + 1) ^ B * facEnv r 𝔞 M)
    (hA : ∀ M : ℕ, 1 ≤ M → facEnv r 𝔞 M ≤ K * (M : ℝ) ^ B' * A M)
    (hAnn : ∀ M, 0 ≤ A M)
    (hsmax : ((B : ℝ) + (B' : ℝ)) < smax) :
    Tendsto (fun M : ℕ => ‖E M‖ / (A M * Real.exp (smax * Real.log M))) atTop (𝓝 0) := by
  have hlogtop : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  -- the majorant
  have hmaj : Tendsto (fun M : ℕ =>
      c₁ * 2 ^ B * K * Real.exp (((B : ℝ) + (B' : ℝ) - smax) * Real.log M)) atTop (𝓝 0) := by
    have hbot : Tendsto (fun M : ℕ => ((B : ℝ) + (B' : ℝ) - smax) * Real.log M) atTop atBot := by
      have hpos : Tendsto (fun M : ℕ => (smax - ((B : ℝ) + (B' : ℝ))) * Real.log M)
          atTop atTop :=
        Filter.Tendsto.const_mul_atTop (by linarith) hlogtop
      have hneg := Filter.tendsto_neg_atTop_atBot.comp hpos
      refine hneg.congr fun M => ?_
      simp only [Function.comp_apply]
      ring
    have hexp : Tendsto (fun M : ℕ => Real.exp (((B : ℝ) + (B' : ℝ) - smax) * Real.log M))
        atTop (𝓝 0) := Real.tendsto_exp_atBot.comp hbot
    have := hexp.const_mul (c₁ * 2 ^ B * K)
    simpa using this
  refine squeeze_zero' (Eventually.of_forall fun M => ?_) ?_ hmaj
  · exact div_nonneg (norm_nonneg _) (mul_nonneg (hAnn M) (Real.exp_pos _).le)
  filter_upwards [eventually_ge_atTop (max (R + 1) 1)] with M hM
  have hMR : R + 1 ≤ M := le_trans (le_max_left _ _) hM
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hMRle : R ≤ M := by omega
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have hfacpos : 0 < facEnv r 𝔞 M := facEnv_pos (r := r) h𝔞 M
  have hApos : 0 < A M := by
    by_contra hc
    have hzero : A M = 0 := le_antisymm (not_lt.mp hc) (hAnn M)
    have := hA M hM1
    rw [hzero, mul_zero] at this
    linarith
  have hexppos : (0 : ℝ) < Real.exp (smax * Real.log M) := Real.exp_pos _
  -- the numerator estimate
  have hshift : (((M + R : ℕ) : ℝ) + 1) ≤ 2 * (M : ℝ) := by
    have hcast : ((M + R : ℕ) : ℝ) = (M : ℝ) + (R : ℝ) := by push_cast; ring
    have hRle : (R : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hMR
    rw [hcast]
    linarith
  have hpowshift : (((M + R : ℕ) : ℝ) + 1) ^ B ≤ (2 * (M : ℝ)) ^ B :=
    pow_le_pow_left₀ (by positivity) hshift B
  have hEle : ‖E M‖ ≤ c₁ * 2 ^ B * K * ((M : ℝ) ^ B * (M : ℝ) ^ B') * A M := by
    refine le_trans (hE M hMRle) ?_
    calc c₁ * (((M + R : ℕ) : ℝ) + 1) ^ B * facEnv r 𝔞 M
        ≤ c₁ * (2 * (M : ℝ)) ^ B * facEnv r 𝔞 M := by
          have hnn : (0 : ℝ) ≤ facEnv r 𝔞 M := le_of_lt hfacpos
          have := mul_le_mul_of_nonneg_left hpowshift hc₁
          nlinarith
      _ ≤ c₁ * (2 * (M : ℝ)) ^ B * (K * (M : ℝ) ^ B' * A M) := by
          have hnn : (0 : ℝ) ≤ c₁ * (2 * (M : ℝ)) ^ B := by positivity
          exact mul_le_mul_of_nonneg_left (hA M hM1) hnn
      _ = c₁ * 2 ^ B * K * ((M : ℝ) ^ B * (M : ℝ) ^ B') * A M := by
          rw [mul_pow]
          ring
  -- divide
  have hexpsplit : (M : ℝ) ^ B * (M : ℝ) ^ B' / Real.exp (smax * Real.log M)
      = Real.exp (((B : ℝ) + (B' : ℝ) - smax) * Real.log M) := by
    have hB : (M : ℝ) ^ B = Real.exp ((B : ℝ) * Real.log M) := by
      rw [Real.exp_nat_mul, Real.exp_log hMpos]
    have hB' : (M : ℝ) ^ B' = Real.exp ((B' : ℝ) * Real.log M) := by
      rw [Real.exp_nat_mul, Real.exp_log hMpos]
    rw [hB, hB', ← Real.exp_add, ← Real.exp_sub]
    congr 1
    ring
  rw [div_le_iff₀ (by positivity)]
  calc ‖E M‖ ≤ c₁ * 2 ^ B * K * ((M : ℝ) ^ B * (M : ℝ) ^ B') * A M := hEle
    _ = c₁ * 2 ^ B * K * ((M : ℝ) ^ B * (M : ℝ) ^ B' / Real.exp (smax * Real.log M))
        * (A M * Real.exp (smax * Real.log M)) := by
        field_simp
    _ = c₁ * 2 ^ B * K * Real.exp (((B : ℝ) + (B' : ℝ) - smax) * Real.log M)
        * (A M * Real.exp (smax * Real.log M)) := by rw [hexpsplit]

end

end GaloisForLFunctions.HTGeometry
