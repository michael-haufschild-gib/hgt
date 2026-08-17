import GaloisForLFunctions.RHTower.ProlateLeakageRatioVanishing
import GaloisForLFunctions.RHTower.ProlateSignedLadderEnvelope

/-!
# The step-one ladder envelope

The vanishing ratio holds for every pair of corpus indices, so the *full* signed leakage sequence —
not only its Fourier-even sublattice — is a ladder envelope.  The two limits it needs are

```text
1 / c^{3/4} → 0        and        a / c^{3/4} → 0 ,
```

the second because `c = 2π a²` makes `c^{3/4} = (2π)^{3/4} a^{3/2}`, so `a / c^{3/4} ≍ a^{-1/2}`.
-/

noncomputable section

open Set Filter Topology

namespace RHTower

open GaloisForLFunctions.RHTower

theorem sqrt_signedModeRadialBandwidth {a : ℝ} (ha : 0 ≤ a) :
    Real.sqrt (signedModeRadialBandwidth a) = Real.sqrt (2 * Real.pi) * a := by
  rw [signedModeRadialBandwidth, Real.sqrt_mul (by positivity), Real.sqrt_sq ha]

theorem tendsto_sqrt_sqrt_bandwidth_atTop :
    Tendsto (fun a : ℝ => Real.sqrt (Real.sqrt (signedModeRadialBandwidth a))) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp
    tendsto_signedModeRadialBandwidth_atTop)

theorem tendsto_prolateRatioScale_atTop :
    Tendsto prolateRatioScale atTop atTop := by
  have h1 : Tendsto (fun a : ℝ => Real.sqrt (signedModeRadialBandwidth a)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_signedModeRadialBandwidth_atTop
  have h2 := tendsto_sqrt_sqrt_bandwidth_atTop
  have := h1.atTop_mul_atTop₀ h2
  exact this.congr fun a => rfl

theorem tendsto_inv_prolateRatioScale (K : ℝ) :
    Tendsto (fun a : ℝ => K / prolateRatioScale a) atTop (𝓝 0) := by
  have h : Tendsto (fun a : ℝ => (prolateRatioScale a)⁻¹) atTop (𝓝 0) :=
    tendsto_prolateRatioScale_atTop.inv_tendsto_atTop
  have h2 := h.const_mul K
  rw [mul_zero] at h2
  simpa [div_eq_mul_inv] using h2

theorem tendsto_mul_inv_prolateRatioScale (K : ℝ) :
    Tendsto (fun a : ℝ => a * (K / prolateRatioScale a)) atTop (𝓝 0) := by
  have hkey : ∀ᶠ a : ℝ in atTop,
      a * (K / prolateRatioScale a)
        = K / Real.sqrt (2 * Real.pi) / Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    have hc : 0 < signedModeRadialBandwidth a := by
      rw [signedModeRadialBandwidth]
      positivity
    have hs : Real.sqrt (signedModeRadialBandwidth a) = Real.sqrt (2 * Real.pi) * a :=
      sqrt_signedModeRadialBandwidth ha.le
    have hpi : (0 : ℝ) < Real.sqrt (2 * Real.pi) := by
      have := Real.pi_pos
      positivity
    have hss : 0 < Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)) :=
      Real.sqrt_pos.2 (Real.sqrt_pos.2 hc)
    rw [prolateRatioScale, hs]
    field_simp
  have hss : Tendsto (fun a : ℝ => (Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)))⁻¹)
      atTop (𝓝 0) := tendsto_sqrt_sqrt_bandwidth_atTop.inv_tendsto_atTop
  have hlim := hss.const_mul (K / Real.sqrt (2 * Real.pi))
  rw [mul_zero] at hlim
  have hlim' : Tendsto (fun a : ℝ =>
      K / Real.sqrt (2 * Real.pi) / Real.sqrt (Real.sqrt (signedModeRadialBandwidth a)))
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hlim
  exact hlim'.congr' (hkey.mono fun a h => h.symm)

/-- **The full signed leakage sequence is a ladder envelope.**  The ratio bound holds for every pair
of indices, so no Fourier-even restriction is needed. -/
theorem ladderEnvelope_evenProlateSignedLeakage_full :
    LadderEnvelope fun a j => evenProlateSignedLeakage a j where
  nonneg := fun a j => evenProlateSignedLeakage_nonneg a j
  mono := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha i j hij
    exact evenProlateSignedLeakage_monotone a ha hij
  lt_succ := by
    intro j
    have hratio := eventually_signedLeakage_le_div_sqrt j (j + 1) (Nat.lt_succ_self j)
    have hsmall : ∀ᶠ a : ℝ in atTop, leakageRatioConst j (j + 1) / prolateRatioScale a < 1 :=
      (tendsto_inv_prolateRatioScale (leakageRatioConst j (j + 1))).eventually
        (eventually_lt_nhds (by norm_num))
    filter_upwards [hratio, hsmall, eventually_evenProlateSignedLeakage_pos (j + 1) (by omega)]
      with a hr hs hp
    nlinarith [hr, hs, hp]
  ratio_tendsto_zero := by
    intro j
    have hratio := eventually_signedLeakage_le_div_sqrt j (j + 1) (Nat.lt_succ_self j)
    refine squeeze_zero' ?_ ?_ (tendsto_inv_prolateRatioScale (leakageRatioConst j (j + 1)))
    · filter_upwards [eventually_evenProlateSignedLeakage_pos (j + 1) (by omega)] with a hp
      exact div_nonneg (evenProlateSignedLeakage_nonneg a j) hp.le
    · filter_upwards [hratio, eventually_evenProlateSignedLeakage_pos (j + 1) (by omega)] with a hr hp
      rw [div_le_iff₀ hp]
      exact hr
  tail_tendsto_zero := by
    intro j
    have hratio := eventually_signedLeakage_le_div_sqrt (j + 1) (j + 2) (Nat.lt_succ_self (j + 1))
    have hhalf : ∀ᶠ a : ℝ in atTop,
        leakageRatioConst (j + 1) (j + 2) / prolateRatioScale a < 1 / 2 :=
      (tendsto_inv_prolateRatioScale (leakageRatioConst (j + 1) (j + 2))).eventually
        (eventually_lt_nhds (by norm_num))
    have htail := (tendsto_mul_inv_prolateRatioScale
      (leakageRatioConst (j + 1) (j + 2))).const_mul 2
    rw [mul_zero] at htail
    refine squeeze_zero' ?_ ?_ htail
    · filter_upwards [hratio, hhalf, eventually_evenProlateSignedLeakage_pos (j + 2) (by omega),
        eventually_gt_atTop (0 : ℝ)] with a hr hs hp ha
      have hden : 0 < evenProlateSignedLeakage a (j + 2) - evenProlateSignedLeakage a (j + 1) := by
        nlinarith [hr, hs, hp]
      exact div_nonneg (mul_nonneg ha.le (evenProlateSignedLeakage_nonneg a (j + 1))) hden.le
    · filter_upwards [hratio, hhalf, eventually_evenProlateSignedLeakage_pos (j + 2) (by omega),
        eventually_gt_atTop (0 : ℝ)] with a hr hs hp ha
      have hden : 0 < evenProlateSignedLeakage a (j + 2) - evenProlateSignedLeakage a (j + 1) := by
        nlinarith [hr, hs, hp]
      have hhalfden : evenProlateSignedLeakage a (j + 2) / 2
          ≤ evenProlateSignedLeakage a (j + 2) - evenProlateSignedLeakage a (j + 1) := by
        nlinarith [hr, hs, hp]
      rw [div_le_iff₀ hden]
      have hup : a * evenProlateSignedLeakage a (j + 1)
          ≤ a * (leakageRatioConst (j + 1) (j + 2) / prolateRatioScale a)
            * evenProlateSignedLeakage a (j + 2) := by
        have := mul_le_mul_of_nonneg_left hr ha.le
        nlinarith [this]
      nlinarith [hup, hhalfden, hden, hp, ha,
        mul_nonneg ha.le (evenProlateSignedLeakage_nonneg a (j + 1))]

end RHTower

end
