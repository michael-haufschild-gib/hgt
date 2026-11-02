import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.EveryPolylogConductorSpanIsPositiveAtLogLogOverlap

/-!
# Logarithmic floors control quadratic-overlap residuals

On a conductor block of size `(log N)^q`, the raw squared residual sum is
smaller than `(log N)^(-2η)` whenever `2q + 2η < 1`. This remains uniform up
to quadratic log-log overlap; the arbitrarily small prime-error exponent
absorbs the remaining logarithmic factors.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Finset Filter Topology
open scoped Classical RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open CompletedArithmeticForms RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  CriticalScaleArithmeticRigidity

private theorem logarithmic_residual_rate_envelope {K q η ν L n c : ℝ}
    (hK : 0 ≤ K) (hq : 0 ≤ q) (hL1 : 1 ≤ L) (ht1 : 1 ≤ Real.log L)
    {Q : ℕ} (hQ1 : 1 ≤ Q) (hQ : (Q : ℝ) ≤ L ^ q)
    (hc : 1 ≤ c) (hcT : c ≤ (Real.log L) ^ 2) :
    K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 *
        (c ^ 2 * (1 + Real.log c) ^ 3 * L ^ ν / L + c ^ 10 * (L / n) ^ 2) *
          L ^ (2 * η) ≤
      K * (1 + q) ^ 2 *
        (L ^ (2 * q + ν + 2 * η - 1) * (Real.log L) ^ 12 +
          L ^ (2 * q + 2 * η + 24) / n ^ 2) := by
  let t := Real.log L
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have ht : 0 ≤ t := zero_le_one.trans ht1
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hlogc0 : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
  have hlogc : 1 + Real.log c ≤ t ^ 2 :=
    (by linarith only [Real.log_le_sub_one_of_pos hc0] : 1 + Real.log c ≤ c).trans hcT
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ1
  have hlogQ : Real.log (Q : ℝ) ≤ q * t := by
    have hh := Real.log_le_log hQ0 hQ
    rwa [Real.log_rpow hL] at hh
  have hQsq : (Q : ℝ) ^ 2 ≤ L ^ (2 * q) := by
    calc
      _ ≤ (L ^ q) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hQ 2
      _ = _ := by rw [← Real.rpow_two, ← Real.rpow_mul hL.le, mul_comm q]
  have hlogSq : (1 + Real.log (Q : ℝ)) ^ 2 ≤ (1 + q) ^ 2 * t ^ 2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log (Q : ℝ))
      (show 1 + Real.log (Q : ℝ) ≤ (1 + q) * t by linarith only [hlogQ, ht1]) 2
    simpa only [mul_pow] using hh
  have hnear : c ^ 2 * (1 + Real.log c) ^ 3 ≤ t ^ 10 := by
    calc
      _ ≤ (t ^ 2) ^ 2 * (t ^ 2) ^ 3 := mul_le_mul
        (pow_le_pow_left₀ hc0.le hcT 2) (pow_le_pow_left₀ hlogc0 hlogc 3)
        (by positivity) (sq_nonneg (t ^ 2))
      _ = _ := by ring
  have htail : c ^ 10 ≤ t ^ 20 := by
    simpa only [← pow_mul] using pow_le_pow_left₀ hc0.le hcT 10
  have hrate := add_le_add
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hnear (Real.rpow_nonneg hL.le ν)) hL.le)
    (mul_le_mul_of_nonneg_right htail (sq_nonneg (L / n)))
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul_of_nonneg_left hQsq hK) hlogSq (sq_nonneg _) (by positivity))
    hrate (by positivity) (by positivity)
  have hfull := mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hL.le (2 * η))
  have htL : t ≤ L := by dsimp only [t]; linarith only [Real.log_le_sub_one_of_pos hL]
  have htailPower : t ^ 22 * L ^ (2 * q + 2 * η + 2) ≤
      L ^ (2 * q + 2 * η + 24) := by
    calc
      _ ≤ L ^ (22 : ℕ) * L ^ (2 * q + 2 * η + 2) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht htL 22) (Real.rpow_nonneg hL.le _)
      _ = _ := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hL]
        congr 1
        norm_num
        ring
  calc
    _ ≤ K * L ^ (2 * q) * ((1 + q) ^ 2 * t ^ 2) *
        (t ^ 10 * L ^ ν / L + t ^ 20 * (L / n) ^ 2) * L ^ (2 * η) := hfull
    _ = K * (1 + q) ^ 2 *
        (L ^ (2 * q + ν + 2 * η - 1) * t ^ 12 +
          t ^ 22 * L ^ (2 * q + 2 * η + 2) / n ^ 2) := by
      have hp₁ : L ^ (2 * q + ν + 2 * η - 1) =
          L ^ (2 * q) * L ^ ν * L ^ (2 * η) / L := by
        rw [Real.rpow_sub hL, Real.rpow_add hL, Real.rpow_add hL, Real.rpow_one]
      have hp₂ : L ^ (2 * q + 2 * η + 2) =
          L ^ (2 * q) * L ^ (2 * η) * L ^ 2 := by
        rw [Real.rpow_add hL, Real.rpow_add hL, Real.rpow_two]
      rw [hp₁, hp₂, div_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (add_le_add le_rfl (div_le_div_of_nonneg_right htailPower (sq_nonneg n)))
      (mul_nonneg hK (sq_nonneg _))

/-- A logarithmic energy floor pays the summed raw residual on a small logarithmic
conductor block, uniformly through quadratic log-log overlap. -/
theorem eventually_raw_residual_below_logarithmic_floor {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ x, x ∉ Set.Icc 0 1 → φ x = 0)
    (hM : 0 < ∫ x, φ x ^ 2) {q η : ℝ} (hq : 0 ≤ q)
    (hgap : 2 * q + 2 * η < 1) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ 2 →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ∀ Q : ℕ, 1 ≤ Q → (Q : ℝ) ≤ Real.log (N : ℝ) ^ q →
      (∑ m ∈ Icc 1 Q,
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
        (Real.log (N : ℝ) ^ (-η)) ^ 2 / 128 := by
  obtain ⟨K, hK, hres⟩ := exists_completeWeil_quadratic_conductor_residual_variable_rate hφ hsupp hM
  let δ := (1 - 2 * q - 2 * η) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith only [hgap]
  let k : ℕ := ⌈1 / δ⌉₊ + 1
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hν : 1 / (k : ℝ) ≤ δ := by
    have hceil := (div_le_iff₀ hδ).mp (Nat.le_ceil (1 / δ))
    apply (div_le_iff₀ hk0).mpr
    dsimp only [k]
    push_cast
    nlinarith only [hceil, hδ]
  have hexponent : 2 * q + 1 / (k : ℝ) + 2 * η - 1 < 0 := by
    dsimp only [δ] at hν
    linarith only [hν, hgap]
  have hfirst : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ (2 * q + 1 / (k : ℝ) + 2 * η - 1) *
        Real.log (Real.log (N : ℝ)) ^ 12) atTop (𝓝 0) := by
    simpa only [Function.comp_def] using
      (_root_.RHTower.Sieve.tendsto_logRpow_mul_logLogPow hexponent 12).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have htail : Tendsto (fun N : ℕ =>
      Real.log (N : ℝ) ^ (2 * q + 2 * η + 24) / (N : ℝ) ^ 2) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.rpow_two] using
      ((isLittleO_log_rpow_rpow_atTop (2 * q + 2 * η + 24)
        (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero).comp
          (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlim := (hfirst.add htail).const_mul (K * (1 + q) ^ 2)
  simp only [add_zero, mul_zero] at hlim
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htlim := Real.tendsto_log_atTop.comp hLlim
  filter_upwards [hres q hq k hk,
    hlim.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 128)),
    hLlim.eventually_ge_atTop 1, htlim.eventually_ge_atTop 1]
    with N hresN hsmall hL1 ht1
  intro c hc hcT hwidth Q hQ1 hQ
  let L := Real.log (N : ℝ)
  have hL : 0 < L := zero_lt_one.trans_le hL1
  let r := c ^ 2 * (1 + Real.log c) ^ 3 * L ^ (1 / (k : ℝ)) / L +
    c ^ 10 * (L / N) ^ 2
  have hr : 0 ≤ r := by
    have hc0 : 0 ≤ c := zero_le_one.trans hc
    have hlogc : 0 ≤ 1 + Real.log c := by linarith only [Real.log_nonneg hc]
    dsimp only [r]
    positivity
  have hsum : (∑ m ∈ Icc 1 Q,
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2) ≤
      K * (Q : ℝ) ^ 2 * (1 + Real.log Q) ^ 2 * r := by
    calc
      _ ≤ ∑ m ∈ Icc 1 Q, K * (m : ℝ) * (1 + Real.log Q) ^ 2 * r := by
        refine sum_le_sum fun m hm => ?_
        have hm0 : (0 : ℝ) < m := by exact_mod_cast (mem_Icc.mp hm).1
        have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
        have hlog := Real.log_le_log hm0 hmQ
        have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + Real.log (m : ℝ))
          (show 1 + Real.log (m : ℝ) ≤ 1 + Real.log Q by linarith only [hlog]) 2
        have hh := hresN m (mem_Icc.mp hm).1 (hmQ.trans hQ) c hc hwidth
        change _ ≤ K * ((m : ℝ) * (1 + Real.log m) ^ 2) * r at hh
        exact (hh.trans_eq (by ring)).trans
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hp (mul_nonneg hK.le hm0.le)) hr)
      _ ≤ ∑ _m ∈ Icc 1 Q, K * (Q : ℝ) * (1 + Real.log Q) ^ 2 * r := by
        refine sum_le_sum fun m hm => ?_
        have hmQ : (m : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hm).2
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmQ hK.le) (sq_nonneg _)) hr
      _ = _ := by
        rw [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        ring
  have hscaled := (mul_le_mul_of_nonneg_right hsum (Real.rpow_nonneg hL.le (2 * η))).trans
    (logarithmic_residual_rate_envelope hK.le hq hL1 ht1 hQ1 hQ hc hcT)
  have heq : (L ^ (-η)) ^ 2 / 128 * L ^ (2 * η) = 1 / 128 := by
    rw [← Real.rpow_two, ← Real.rpow_mul hL.le]
    calc
      _ = (L ^ (-η * 2) * L ^ (2 * η)) / 128 := by ring
      _ = _ := by rw [← Real.rpow_add hL, show -η * 2 + 2 * η = 0 by ring,
        Real.rpow_zero]
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hL (2 * η))).mp
  rw [heq]
  exact hscaled.trans hsmall

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
