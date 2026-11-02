import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryPolylogConductorSpanIsPositiveAtLogLogOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryProfileHasAPolynomialHighConductorLoss

/-!
# Polynomial conductor spans at growing overlap

The weighted high-conductor loss is `O(c⁴(1 + log c))`. Splitting at a small
polylogarithmic conductor retains the exponential low-block floor and a growing
high-block gap whenever `c ≤ (log log N)^β`, `β < 1/4`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

private theorem eventually_log_power_times_nat_power_le_nat (C a : ℝ) {p : ℝ}
    (hp : p < 1) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.log (N : ℝ) ^ a * (N : ℝ) ^ p ≤ (N : ℝ) := by
  have hlim : Tendsto (fun N : ℕ =>
      C * (Real.log (N : ℝ) ^ a / (N : ℝ) ^ (1 - p))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      (((isLittleO_log_rpow_rpow_atTop a (sub_pos.mpr hp)).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)).const_mul C
  filter_upwards [hlim.eventually (ge_mem_nhds zero_lt_one), eventually_ge_atTop 1]
    with N hsmall hN1
  have hN : (0 : ℝ) < N := by exact_mod_cast hN1
  have hbound : C * Real.log (N : ℝ) ^ a ≤ (N : ℝ) ^ (1 - p) := by
    apply (div_le_one (Real.rpow_pos_of_pos hN (1 - p))).mp
    convert hsmall using 1; ring
  calc
    _ ≤ (N : ℝ) ^ (1 - p) * (N : ℝ) ^ p :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hN.le p)
    _ = (N : ℝ) := by rw [← Real.rpow_add hN, sub_add_cancel, Real.rpow_one]

private theorem tendsto_power_log_cost_div_self {β : ℝ} (hβ : β < 1 / 4) :
    Tendsto (fun t : ℝ => t ^ (4 * β) * (1 + β * Real.log t) / t) atTop (𝓝 0) := by
  have hs : 0 < 1 - 4 * β := by linarith only [hβ]
  have hinv : Tendsto (fun t : ℝ => (t ^ (1 - 4 * β))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hs)
  have hlog : Tendsto (fun t : ℝ => Real.log t / t ^ (1 - 4 * β)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      (isLittleO_log_rpow_rpow_atTop 1 hs).tendsto_div_nhds_zero
  have hh : Tendsto (fun t : ℝ => (t ^ (1 - 4 * β))⁻¹ +
      β * (Real.log t / t ^ (1 - 4 * β))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hinv.add (hlog.const_mul β)
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_sub ht, Real.rpow_one]
  field_simp

private theorem eventually_sublinear_power_le_multiple {β γ : ℝ}
    (hβ : β < 1) (hγ : 0 < γ) :
    ∀ᶠ t : ℝ in atTop, t ^ β ≤ γ * t := by
  have hlim : Tendsto (fun t : ℝ => (t ^ (1 - β))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop (sub_pos.mpr hβ))
  filter_upwards [hlim.eventually (ge_mem_nhds hγ), eventually_gt_atTop (0 : ℝ)]
    with t hsmall ht
  rw [Real.rpow_sub ht, Real.rpow_one, inv_div] at hsmall
  exact (div_le_iff₀ ht).mp hsmall

private theorem eventually_polynomial_span_horizon {θ β γ C : ℝ}
    (hθ : 0 < θ) (hθlt : θ < 1 / 1080) (_hβ : 0 < β) (hβlt : β < 1 / 4)
    (hγ : 0 < γ) (hC : 0 < C) :
    ∀ᶠ N : ℕ in atTop,
      let Q := ⌊Real.log (N : ℝ) ^ (1 / 8 : ℝ)⌋₊
      let R := ⌊(N : ℝ) ^ θ⌋₊
      2 ≤ Q ∧ Q ≤ R ∧ R ^ 6 ≤ N ∧ 1080 * (1 + Real.log R) ≤ Real.log N ∧
      ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ β →
        c ≤ γ * Real.log (Real.log (N : ℝ)) ∧ c / N ≤ 1 / 3 ∧
        ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N ∧
        ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N ∧
        (1 + Real.log R) * (R : ℝ) ^ 2 * (Real.log N / N) ≤ 1 ∧
        4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) ∧
        C * c ^ 4 * (1 + Real.log c) + 1 ≤ (1 / 4 : ℝ) * Real.log Q := by
  have hβ1 : β < 1 := by linarith only [hβlt]
  have h2θ : 2 * θ < 1 := by linarith only [hθlt]
  have h6θ : 6 * θ ≤ 1 := by linarith only [hθlt]
  have hframeDen : 0 < 1 - 1080 * θ := by linarith only [hθlt]
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  have hQlim := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp hLlim
  have hQRlim : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ (1 / 8 : ℝ) / (N : ℝ) ^ θ) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      ((isLittleO_log_rpow_rpow_atTop (1 / 8 : ℝ) hθ).tendsto_div_nhds_zero).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hcostLim : Tendsto (fun N : ℕ => C *
      (Real.log (Real.log (N : ℝ)) ^ (4 * β) *
        (1 + β * Real.log (Real.log (Real.log (N : ℝ)))) /
          Real.log (Real.log (N : ℝ)))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_power_log_cost_div_self hβlt).comp htlim).const_mul C
  let Cnear := 2 * Real.exp 2 + 1
  let Cup := Real.exp 1 + 1
  have hCnear : 0 < Cnear := by dsimp only [Cnear]; positivity
  have hCup : 0 < Cup := by dsimp only [Cup]; positivity
  filter_upwards [eventually_ge_atTop 2, hLlim.eventually_ge_atTop 1,
    htlim.eventually_ge_atTop 1, hQlim.eventually_ge_atTop 2,
    hQRlim.eventually (ge_mem_nhds zero_lt_one),
    hLlim.eventually_ge_atTop (1080 / (1 - 1080 * θ)),
    htlim.eventually (eventually_sublinear_power_le_multiple hβ1 hγ),
    eventually_log_power_times_nat_power_le_nat 3 1 (by norm_num : (0 : ℝ) < 1),
    eventually_log_power_times_nat_power_le_nat (2 * Cnear) 1 h2θ,
    eventually_log_power_times_nat_power_le_nat (2 * Cup) 1 h2θ,
    eventually_log_power_times_nat_power_le_nat (1 + θ) 2 h2θ,
    eventually_log_power_times_nat_power_le_nat (4 * (Real.exp 1 + 3) ^ 2) 2
      (by norm_num : (0 : ℝ) < 1),
    hcostLim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 64)),
    htlim.eventually_ge_atTop (64 * (1 + Real.log 2 / 4))]
    with N hN2 hL1 ht1 hQpow2 hQRsmall hframeN hγN hwidthN hnearN hupN htailN hrawN
      hcostN hgapN
  let L := Real.log (N : ℝ)
  let t := Real.log L
  let Q := ⌊L ^ (1 / 8 : ℝ)⌋₊
  let R := ⌊(N : ℝ) ^ θ⌋₊
  change 1 ≤ t at ht1
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hQ2 : 2 ≤ Q := Nat.le_floor hQpow2
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ L ^ (1 / 8 : ℝ) := Nat.floor_le (Real.rpow_nonneg hL.le _)
  have hRpow : (R : ℝ) ≤ (N : ℝ) ^ θ := Nat.floor_le (Real.rpow_nonneg hN.le _)
  have hQR : Q ≤ R := Nat.le_floor
    (hQpow.trans ((div_le_one (Real.rpow_pos_of_pos hN θ)).mp hQRsmall))
  have hR1 : (1 : ℝ) ≤ R := by exact_mod_cast (show 1 ≤ R by omega)
  have hR6 : R ^ 6 ≤ N := by
    have hh : (R : ℝ) ^ 6 ≤ (N : ℝ) := by
      calc
        _ ≤ ((N : ℝ) ^ θ) ^ 6 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRpow 6
        _ = (N : ℝ) ^ (6 * θ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
          norm_num only [Nat.cast_ofNat]
          rw [mul_comm θ]
        _ ≤ _ := by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le hN1 h6θ
    exact_mod_cast hh
  have hlogR : Real.log (R : ℝ) ≤ θ * L := by
    have hh := Real.log_le_log (zero_lt_one.trans_le hR1) hRpow
    rwa [Real.log_rpow hN] at hh
  have hframe : 1080 * (1 + Real.log R) ≤ L := by
    have hh := (div_le_iff₀ hframeDen).mp hframeN
    change 1080 ≤ L * (1 - 1080 * θ) at hh
    linarith only [hh, hlogR]
  have hQlower : L ^ (1 / 8 : ℝ) / 2 ≤ (Q : ℝ) := by
    have hh := Nat.lt_floor_add_one (L ^ (1 / 8 : ℝ))
    have hQcast : (2 : ℝ) ≤ Q := by exact_mod_cast hQ2
    change L ^ (1 / 8 : ℝ) < (Q : ℝ) + 1 at hh
    linarith only [hh, hQcast]
  have hlogQ : (1 / 8 : ℝ) * t - Real.log 2 ≤ Real.log (Q : ℝ) := by
    have hh := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hL _) zero_lt_two) hQlower
    rwa [Real.log_div (Real.rpow_pos_of_pos hL _).ne' (by norm_num), Real.log_rpow hL] at hh
  have hRtwo : (R : ℝ) ^ 2 ≤ (N : ℝ) ^ (2 * θ) := by
    calc
      _ ≤ ((N : ℝ) ^ θ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hRpow 2
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hN.le, mul_comm θ]
  have hRsum : ((R * R : ℕ) + 1 : ℝ) ≤ 2 * (N : ℝ) ^ (2 * θ) := by
    have hp : 1 ≤ (N : ℝ) ^ (2 * θ) := Real.one_le_rpow hN1 (by positivity)
    push_cast
    nlinarith only [hRtwo, hp]
  refine ⟨hQ2, hQR, hR6, hframe, ?_⟩
  intro c hc1 hcpow
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have htβ : t ^ β ≤ t := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le ht1 hβ1.le
  have hcT : c ≤ t := hcpow.trans htβ
  have htL : t ≤ L := by dsimp only [t]; linarith only [Real.log_le_sub_one_of_pos hL]
  have hcL : c ≤ L := hcT.trans htL
  have hcγ : c ≤ γ * t := hcpow.trans hγN
  have hcN : c / N ≤ 1 / 3 := by
    apply (div_le_iff₀ hN).mpr
    have hh : 3 * L ≤ (N : ℝ) := by simpa only [Real.rpow_one, Real.rpow_zero, mul_one] using hwidthN
    linarith only [hcL, hh]
  have hnearRadius : linearNearRowRadius c + 1 ≤ Cnear * L := by
    dsimp only [linearNearRowRadius, Cnear]
    have hh := mul_le_mul_of_nonneg_right hcL (Real.exp_pos 2).le
    nlinarith only [hh, hL1]
  have hupRadius : c * Real.exp 1 + 1 ≤ Cup * L := by
    dsimp only [Cup]
    have hh := mul_le_mul_of_nonneg_right hcL (Real.exp_pos 1).le
    nlinarith only [hh, hL1]
  have hnearSize : ((R * R : ℕ) + 1 : ℝ) * (linearNearRowRadius c + 1) ≤ N := by
    calc
      _ ≤ (2 * (N : ℝ) ^ (2 * θ)) * (Cnear * L) :=
        mul_le_mul hRsum hnearRadius (by unfold linearNearRowRadius; positivity) (by positivity)
      _ = (2 * Cnear) * L ^ (1 : ℝ) * (N : ℝ) ^ (2 * θ) := by rw [Real.rpow_one]; ring
      _ ≤ _ := hnearN
  have hupSize : ((R * R : ℕ) + 1 : ℝ) * (c * Real.exp 1 + 1) ≤ N := by
    calc
      _ ≤ (2 * (N : ℝ) ^ (2 * θ)) * (Cup * L) :=
        mul_le_mul hRsum hupRadius (by positivity) (by positivity)
      _ = (2 * Cup) * L ^ (1 : ℝ) * (N : ℝ) ^ (2 * θ) := by rw [Real.rpow_one]; ring
      _ ≤ _ := hupN
  have htail : (1 + Real.log R) * (R : ℝ) ^ 2 * (L / N) ≤ 1 := by
    have hlogBound : 1 + Real.log R ≤ (1 + θ) * L := by linarith only [hlogR, hL1]
    have hbound : (1 + θ) * L ^ 2 * (N : ℝ) ^ (2 * θ) ≤ N := by
      simpa only [Real.rpow_two] using htailN
    calc
      _ ≤ ((1 + θ) * L) * (N : ℝ) ^ (2 * θ) * (L / N) := by gcongr
      _ = ((1 + θ) * L ^ 2 * (N : ℝ) ^ (2 * θ)) / N := by ring
      _ ≤ 1 := (div_le_one hN).mpr hbound
  have hraw : 4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) :=
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hc.le hcL 2) (by positivity)).trans
      (by simpa only [Real.rpow_two, Real.rpow_zero, mul_one] using hrawN)
  have hlogc0 : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc1]
  have hlogc : Real.log c ≤ β * Real.log t := by
    have hh := Real.log_le_log hc hcpow
    rwa [Real.log_rpow ht] at hh
  have hc4 : c ^ 4 ≤ t ^ (4 * β) := by
    calc
      _ ≤ (t ^ β) ^ 4 := pow_le_pow_left₀ hc.le hcpow 4
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
        norm_num only [Nat.cast_ofNat]
        rw [mul_comm β]
  have hcost : C * c ^ 4 * (1 + Real.log c) ≤ t / 64 := by
    have hh : C * (t ^ (4 * β) * (1 + β * Real.log t)) ≤ t / 64 := by
      have hh' : (C * (t ^ (4 * β) * (1 + β * Real.log t))) / t ≤ 1 / 64 := by
        simpa only [div_eq_mul_inv, mul_assoc] using hcostN
      have hh'' := (div_le_iff₀ ht).mp hh'
      linarith only [hh'']
    calc
      _ ≤ C * t ^ (4 * β) * (1 + β * Real.log t) := by gcongr
      _ ≤ t / 64 := by linarith only [hh]
  have hgap : C * c ^ 4 * (1 + Real.log c) + 1 ≤ (1 / 4 : ℝ) * Real.log Q := by
    change 64 * (1 + Real.log 2 / 4) ≤ t at hgapN
    linarith only [hcost, hgapN, hlogQ]
  exact ⟨hcγ, hcN, hnearSize, hupSize, htail, hraw, hgap⟩

private theorem profile_energy_smul (φ : ℝ → ℝ) (c : ℝ) {N : ℕ} (s : ℝ)
    (u : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (s • u) = s ^ 2 * completeWeilEnergy φ c N u := by
  simp only [completeWeilEnergy, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

private theorem profile_energy_add (φ : ℝ → ℝ) (c : ℝ) {N : ℕ}
    (x y : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    completeWeilEnergy φ c N (x + y) = completeWeilEnergy φ c N x +
      2 * ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, y⟫ +
        completeWeilEnergy φ c N y := by
  have hsym := (Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (completeWeilMatrix_isHermitian φ c N)) y x
  simp only [completeWeilEnergy, map_add, inner_add_left, inner_add_right]
  rw [hsym, real_inner_comm y (Matrix.toEuclideanLin (completeWeilMatrix φ c N) x)]
  ring

/-- Every nonzero compact `C²` profile is coercive on polynomial conductor spans at
poly-log-log overlap of exponent below `1/4`. The exponential rate is universal, and
the profile prefactor is independent of both growth exponents. -/
theorem exists_universal_growing_overlap_polynomial_span_coercivity :
    ∃ B : ℝ, 0 < B ∧ ∀ φ : ℝ → ℝ, ContDiff ℝ 2 φ →
      (∀ x : ℝ, x ∉ Set.Icc 0 1 → φ x = 0) → (0 < ∫ x, φ x ^ 2) →
      ∃ a : ℝ, 0 < a ∧ ∀ θ : ℝ, 0 < θ → θ < 1 / 1080 →
      ∀ β : ℝ, 0 < β → β < 1 / 4 →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ β →
      ∀ x ∈ conductorSubspace ⌊(N : ℝ) ^ θ⌋₊ N,
        a * Real.exp (-B * c) * ‖x‖ ^ 2 ≤ completeWeilEnergy φ c N x := by
  obtain ⟨B, α, hB, hα, hlowAll⟩ := exists_universal_loglog_overlap_all_polylog_coercivity
  let γ := min α (1 / (8 * B))
  have hγ : 0 < γ := lt_min hα (div_pos zero_lt_one (mul_pos (by norm_num) hB))
  have hBγ : 2 * B * γ ≤ 1 / 4 := by
    calc
      _ ≤ 2 * B * (1 / (8 * B)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by field_simp; norm_num
  refine ⟨B, hB, ?_⟩
  intro φ hφ hsupp hM
  obtain ⟨a₀, ha₀, hlow⟩ := hlowAll φ hφ hsupp hM
  let a := min a₀ 1
  have ha : 0 < a := lt_min ha₀ zero_lt_one
  have ha1 : a ≤ 1 := min_le_right _ _
  have haa₀ : a ≤ a₀ := min_le_left _ _
  obtain ⟨C, hC, hhigh⟩ := exists_profile_highConductor_polynomial_loss hφ hsupp hM
  refine ⟨a / 2, div_pos ha zero_lt_two, ?_⟩
  intro θ hθ hθlt β hβ hβlt
  filter_upwards [hlow (1 / 8 : ℝ) (by norm_num),
    eventually_raw_residual_below_exponential_floor hφ hsupp hM hB.le hγ.le hBγ ha,
    eventually_polynomial_span_horizon hθ hθlt hβ hβlt hγ hC]
    with N hlowN hrawN hhorN
  let Q := ⌊Real.log (N : ℝ) ^ (1 / 8 : ℝ)⌋₊
  let R := ⌊(N : ℝ) ^ θ⌋₊
  obtain ⟨hQ2, hQR, hR6, hlogR, hhor⟩ := hhorN
  have hL1 : 1 ≤ Real.log (N : ℝ) := by linarith only [hlogR, Real.log_natCast_nonneg R]
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQpow : (Q : ℝ) ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
    Nat.floor_le (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  have hRR : R * R ≤ N := by
    have hh := (Nat.pow_le_pow_right (by omega : 0 < R) (by norm_num : 2 ≤ 6)).trans hR6
    simpa only [sq] using hh
  have hQQ : Q * Q ≤ N := (Nat.mul_le_mul hQR hQR).trans hRR
  have hlogQ : 18 * (1 + Real.log Q) ≤ Real.log N := by
    have hQRreal : (Q : ℝ) ≤ R := by exact_mod_cast hQR
    have hh := Real.log_le_log hQ0 hQRreal
    linarith only [hh, hlogR, Real.log_natCast_nonneg R]
  intro c hc hcpow x hx
  obtain ⟨hcγ, hw, hsizeNear, hsizeUp, htail, hresWidth, hgap⟩ := hhor c hc hcpow
  have hct : c ≤ α * Real.log (Real.log (N : ℝ)) := hcγ.trans
    (mul_le_mul_of_nonneg_right (min_le_left α (1 / (8 * B))) (Real.log_nonneg hL1))
  let e := a * Real.exp (-B * c)
  have he : 0 < e := mul_pos ha (Real.exp_pos _)
  have he1 : e ≤ 1 := by
    have hexp : Real.exp (-B * c) ≤ 1 := Real.exp_le_one_iff.mpr
      (by have hc0 := zero_le_one.trans hc; nlinarith only [mul_nonneg hB.le hc0])
    exact (mul_le_mul ha1 hexp (Real.exp_pos _).le zero_le_one).trans_eq (one_mul _)
  have hres := hrawN c hc hcγ hresWidth Q (by omega) hQpow
  have hlowEnergy : ∀ p ∈ conductorSubspace Q N,
      e * ‖p‖ ^ 2 ≤ completeWeilEnergy φ c N p := by
    intro p hp
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right haa₀ (Real.exp_pos _).le) (sq_nonneg ‖p‖)).trans
        (hlowN c hc hct p hp)
  have hhighEnergy : ∀ z ∈ conductorSubspace R N, z ∈ (conductorSubspace Q N)ᗮ →
      ‖z‖ ^ 2 ≤ completeWeilEnergy φ c N z := by
    intro z hzR hzQ
    by_cases hz0 : z = 0
    · simp only [hz0, norm_zero, zero_pow (by decide : 2 ≠ 0), completeWeilEnergy,
        map_zero, inner_zero_left, le_refl]
    have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
    let y := ‖z‖⁻¹ • z
    have hyR : y ∈ conductorSubspace R N := Submodule.smul_mem _ _ hzR
    have hyQ : y ∈ (conductorSubspace Q N)ᗮ := Submodule.smul_mem _ _ hzQ
    have hyNorm : ‖y‖ = 1 := by
      dsimp only [y]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hzNorm), inv_mul_cancel₀ hzNorm.ne']
    obtain ⟨b, -, hby⟩ := (mem_conductorSubspace_iff (M := R) (N := N) (x := y)).mp hyR
    rw [hby] at hyQ hyNorm
    have hh := hhigh hQ2 hQR hR6 hlogR hc hw hsizeNear hsizeUp htail b hyQ hyNorm
    rw [← hby] at hh
    have hWy : 1 ≤ completeWeilEnergy φ c N y := by
      linarith only [hh, hgap, primeAdjunctionMass_nonneg R b]
    change 1 ≤ completeWeilEnergy φ c N (‖z‖⁻¹ • z) at hWy
    rw [profile_energy_smul] at hWy
    have hprod := mul_le_mul_of_nonneg_left hWy (sq_nonneg ‖z‖)
    have hscale : ‖z‖ ^ 2 * (‖z‖⁻¹ ^ 2 * completeWeilEnergy φ c N z) =
        completeWeilEnergy φ c N z := by field_simp
    rwa [mul_one, hscale] at hprod
  have hxR : x ∈ conductorSubspace R N := hx
  let p := (conductorSubspace Q N).starProjection x
  let z := x - p
  have hp : p ∈ conductorSubspace Q N := (conductorSubspace Q N).starProjection_apply_mem x
  have hzQ : z ∈ (conductorSubspace Q N)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [real_inner_comm]
    exact (conductorSubspace Q N).starProjection_inner_eq_zero x v hv
  have hzR : z ∈ conductorSubspace R N :=
    (conductorSubspace R N).sub_mem hxR (conductorSubspace_mono hQR N hp)
  have hpyth : ‖p‖ ^ 2 + ‖z‖ ^ 2 = ‖x‖ ^ 2 :=
    norm_starProjection_sq_add_sub_sq (conductorSubspace Q N) x
  have hpEnergy := hlowEnergy p hp
  have hzEnergy := hhighEnergy z hzR hzQ
  have hcross := low_packet_cross_le hQ2 hQQ hlogQ (completeWeilMatrix φ c N)
    (completedConductorEnergy φ c) he hres hp hzQ
  have hcrossCost : 2 * |⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫| ≤
      e / 8 * (‖p‖ ^ 2 + ‖z‖ ^ 2) := by
    have hh := mul_nonneg (show 0 ≤ e / 8 by positivity) (sq_nonneg (‖p‖ - ‖z‖))
    nlinarith only [hcross, hh]
  have hxSplit : x = p + z := by dsimp only [z]; abel
  have henergy := profile_energy_add φ c p z
  rw [← hxSplit] at henergy
  have hcrossLower := neg_abs_le ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) p, z⟫
  have hzReserve := mul_le_mul_of_nonneg_right he1 (sq_nonneg ‖z‖)
  have hnonneg := mul_nonneg he.le (add_nonneg (sq_nonneg ‖p‖) (sq_nonneg ‖z‖))
  have hhalf : a / 2 * Real.exp (-B * c) = e / 2 := by dsimp only [e]; ring
  rw [hhalf, ← hpyth]
  nlinarith only [hpEnergy, hzEnergy, hcrossCost, henergy, hcrossLower, hzReserve, hnonneg]


end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
