import GaloisForLFunctions.RHTower.Sieve.InghamNearHalfGabrielDensity
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorZeroDensityPolylog

/-!
# Zero density right of the critical line at rate `6/5`

Run the uniform Gabriel detector at `σ' = (501 + 950u)/1001`, whose moving centre is exactly
`c = 1/2 + (19/20)u`. Its height exponent `E(σ') = x(3183/1000 + 9009x/50000)/(1 + 1271x/1000)`,
`x = 1 − σ'`, equals `1` at `u = 0` and is concave, so `E(σ') ≤ 1 − (6/5)u` for `0 ≤ u ≤ 1/5`
(`inghamUniformGabrielConservativeExponent_nearHalf_le`). Littlewood's charge of the zeros right of
`1/2 + u` is at least the gap `u/20`, so for all large `X`, uniformly in `0 < u ≤ 1/5`,

`#{ρ : Re ρ ≥ 1/2 + u, |Im ρ| ≤ X − 2} ≤ (K/u) X^{1 − 6u/5} (1 + log X)²`
(`exists_eventually_zeroCountAbove_le_nearHalf`), zeros counted with multiplicity.
-/

open Complex Filter Set

namespace RHTower.Sieve.InghamNearHalf

noncomputable section

/-- The parameter whose moving centre is `1/2 + (19/20)u`. -/
def nearHalfSigma (u : ℝ) : ℝ := (501 + 950 * u) / 1001

theorem inghamUniformGabrielCenter_nearHalfSigma (u : ℝ) :
    inghamUniformGabrielCenter (nearHalfSigma u) = 1 / 2 + 19 / 20 * u := by
  unfold inghamUniformGabrielCenter nearHalfSigma
  ring

/-- `E(σ') ≤ 1 − (6/5)u` on `0 ≤ u ≤ 1/5`. -/
theorem inghamUniformGabrielConservativeExponent_nearHalf_le {u : ℝ} (hu0 : 0 ≤ u)
    (hu1 : u ≤ 1 / 5) :
    inghamUniformGabrielConservativeExponent (nearHalfSigma u) ≤ 1 - 6 / 5 * u := by
  have hσ : nearHalfSigma u ≤ 1 := by unfold nearHalfSigma; rw [div_le_one (by norm_num)]; linarith
  rw [inghamUniformGabrielConservativeExponent_eq hσ]
  have hx : 1 - nearHalfSigma u = (500 - 950 * u) / 1001 := by unfold nearHalfSigma; ring
  rw [hx]
  have hden : 0 < 1 + (1271 / 1000 : ℝ) * ((500 - 950 * u) / 1001) := by nlinarith
  rw [div_le_iff₀ hden]
  nlinarith [mul_nonneg hu0 hu0, mul_nonneg hu0 (by linarith : (0 : ℝ) ≤ 1 / 5 - u)]

/-- The detector constant is uniformly bounded on `0 ≤ u ≤ 1/5`. -/
theorem nearHalf_detectorConstant_le {u : ℝ} (hu1 : u ≤ 1 / 5) :
    ((1 + 1 / (1 - inghamUniformGabrielCenter (nearHalfSigma u))) * Real.exp 1) ^ (2 : ℕ) *
        (1 + inghamMovingRightTranslatedExplicitConstant
          ((9 / 100 : ℝ) * (1 - nearHalfSigma u))) ≤
      ((1 + 10 / 3) * Real.exp 1) ^ (2 : ℕ) *
        (1 + Real.exp 8 * ((1 + 1000 / 27) ^ 4 *
          (5 * Real.pi * Real.exp 1 + (5 * Real.pi / 2) * (4 * Real.exp (1 / 2 : ℝ))))) := by
  rw [inghamUniformGabrielCenter_nearHalfSigma]
  have hc : 1 - (1 / 2 + 19 / 20 * u) ≥ 3 / 10 := by linarith
  have h1 : 1 / (1 - (1 / 2 + 19 / 20 * u)) ≤ 10 / 3 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hδ : (27 / 1000 : ℝ) ≤ (9 / 100 : ℝ) * (1 - nearHalfSigma u) := by
    unfold nearHalfSigma
    rw [show (9 / 100 : ℝ) * (1 - (501 + 950 * u) / 1001) = (9 / 100) * ((500 - 950 * u) / 1001) by
      ring]
    linarith
  have hinv : 1 / ((9 / 100 : ℝ) * (1 - nearHalfSigma u)) ≤ 1000 / 27 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hpow : (1 + 1 / ((9 / 100 : ℝ) * (1 - nearHalfSigma u))) ^ 4 ≤ (1 + 1000 / 27) ^ 4 := by
    have h0 : 0 ≤ 1 + 1 / ((9 / 100 : ℝ) * (1 - nearHalfSigma u)) := by
      have : 0 < (9 / 100 : ℝ) * (1 - nearHalfSigma u) := by linarith
      positivity
    exact pow_le_pow_left₀ h0 (by linarith) 4
  have hconst : inghamMovingRightTranslatedExplicitConstant ((9 / 100 : ℝ) * (1 - nearHalfSigma u)) ≤
      Real.exp 8 * ((1 + 1000 / 27) ^ 4 *
        (5 * Real.pi * Real.exp 1 + (5 * Real.pi / 2) * (4 * Real.exp (1 / 2 : ℝ)))) := by
    unfold inghamMovingRightTranslatedExplicitConstant
    have hA : 0 ≤ 5 * Real.pi * Real.exp 1 + (5 * Real.pi / 2) * (4 * Real.exp (1 / 2 : ℝ)) := by
      positivity
    have he8 : 0 ≤ Real.exp 8 := (Real.exp_pos 8).le
    have : 5 * Real.pi * Real.exp 1 * (1 + 1 / ((9 / 100 : ℝ) * (1 - nearHalfSigma u))) ^ 4 +
        ((5 * Real.pi / 2) * (1 + 1 / ((9 / 100 : ℝ) * (1 - nearHalfSigma u))) ^ 4) *
          (4 * Real.exp (1 / 2 : ℝ)) =
        (1 + 1 / ((9 / 100 : ℝ) * (1 - nearHalfSigma u))) ^ 4 *
          (5 * Real.pi * Real.exp 1 + (5 * Real.pi / 2) * (4 * Real.exp (1 / 2 : ℝ))) := by ring
    rw [this]
    gcongr
  have hfac : (1 + 1 / (1 - (1 / 2 + 19 / 20 * u))) * Real.exp 1 ≤ (1 + 10 / 3) * Real.exp 1 :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos 1).le
  have hfac0 : 0 ≤ (1 + 1 / (1 - (1 / 2 + 19 / 20 * u))) * Real.exp 1 := by
    have : 0 < 1 - (1 / 2 + 19 / 20 * u) := by linarith
    positivity
  have hconst0 : 0 ≤ inghamMovingRightTranslatedExplicitConstant
      ((9 / 100 : ℝ) * (1 - nearHalfSigma u)) := by
    unfold inghamMovingRightTranslatedExplicitConstant
    have : 0 < (9 / 100 : ℝ) * (1 - nearHalfSigma u) := by linarith
    positivity
  exact mul_le_mul (pow_le_pow_left₀ hfac0 hfac 2) (by linarith) (by linarith) (by positivity)

/-- The count from Littlewood's charge: `(u/20) N ≤ M`, `2π M ≤ K₀ (1 + B + L²)`,
`B ≤ Q₀ P`, `L² ≤ P`, `1 ≤ P` give `N ≤ (20 K₀ (2 + Q₀)/(2π)) / u · P`. -/
theorem count_le_of_charge {K₀ Q₀ u N M B L2 P : ℝ} (hK₀ : 0 ≤ K₀) (hu : 0 < u)
    (hcharge : u / 20 * N ≤ M) (hmass : 2 * Real.pi * M ≤ K₀ * (1 + B + L2))
    (hB : B ≤ Q₀ * P) (hL2 : L2 ≤ P) (hP : 1 ≤ P) :
    N ≤ 20 * K₀ * (2 + Q₀) / (2 * Real.pi) / u * P := by
  have hpi : 0 < 2 * Real.pi := by positivity
  have h1 : 1 + B + L2 ≤ (2 + Q₀) * P := by nlinarith
  have h2 : 2 * Real.pi * (u / 20 * N) ≤ K₀ * ((2 + Q₀) * P) := by
    have := mul_le_mul_of_nonneg_left hcharge hpi.le
    exact this.trans (hmass.trans (mul_le_mul_of_nonneg_left h1 hK₀))
  have hrhs : 20 * K₀ * (2 + Q₀) / (2 * Real.pi) / u * P =
      K₀ * ((2 + Q₀) * P) / (2 * Real.pi * (u / 20)) := by
    field_simp
  rw [hrhs, le_div_iff₀ (by positivity)]
  linarith

/-- **Zero density right of the critical line at rate `6/5`.** -/
theorem exists_eventually_zeroCountAbove_le_nearHalf :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ X : ℕ in atTop, ∀ u : ℝ, 0 < u → u ≤ 1 / 5 →
      zetaLittlewoodZeroCountAbove (1 / 2 + 19 / 20 * u) 4 ((X : ℝ) - 2) (1 / 2 + u) ≤
        K / u * (X : ℝ) ^ (1 - 6 / 5 * u) * (1 + Real.log X) ^ 2 := by
  obtain ⟨K₀, hK₀, hmass⟩ := exists_eventually_zetaZeroMass_le_uniformGabrielExplicit
  set Q₀ : ℝ := ((1 + 10 / 3) * Real.exp 1) ^ (2 : ℕ) *
    (1 + Real.exp 8 * ((1 + 1000 / 27) ^ 4 *
      (5 * Real.pi * Real.exp 1 + (5 * Real.pi / 2) * (4 * Real.exp (1 / 2 : ℝ))))) with hQ₀
  have hQ₀0 : 0 ≤ Q₀ := by rw [hQ₀]; positivity
  refine ⟨20 * K₀ * (2 + Q₀) / (2 * Real.pi), by positivity, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop 10] with X hX hX10 u hu hu5
  have hXR : (10 : ℝ) ≤ X := by exact_mod_cast hX10
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hσ0 : 501 / 1001 ≤ nearHalfSigma u := by
    unfold nearHalfSigma; rw [le_div_iff₀ (by norm_num)]; linarith
  have hσ1 : nearHalfSigma u < 1 := by
    unfold nearHalfSigma; rw [div_lt_one (by norm_num)]; linarith
  obtain ⟨T₁, hT₁, T₂, hT₂, hm⟩ := hX hσ0 hσ1
  rw [inghamUniformGabrielCenter_nearHalfSigma] at hm
  have hcount := zetaLittlewoodZeroCountAbove_mul_le_selectedRectangleMass
    (c := 1 / 2 + 19 / 20 * u) (d := 4) (T := (X : ℝ) - 2) (T₁ := T₁) (T₂ := T₂)
    (sigma := 1 / 2 + u) (by linarith) (by linarith) (by linarith [hT₁.2]) (le_of_lt hT₂.1)
  have hgap : (1 / 2 + u) - (1 / 2 + 19 / 20 * u) = u / 20 := by ring
  rw [hgap] at hcount
  -- the right-hand side
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = 1 + Real.log X := ⟨_, rfl⟩
  have hL1 : 1 ≤ L := by rw [hL]; linarith [Real.log_nonneg hX1]
  rw [← hL] at hm ⊢
  have hE := inghamUniformGabrielConservativeExponent_nearHalf_le hu.le hu5
  have hPow : (X : ℝ) ^ inghamUniformGabrielConservativeExponent (nearHalfSigma u) ≤
      (X : ℝ) ^ (1 - 6 / 5 * u) := Real.rpow_le_rpow_of_exponent_le hX1 hE
  have hcs0 : 0 ≤ inghamUniformGabrielCriticalShare (nearHalfSigma u) :=
    inghamUniformGabrielCriticalShare_nonneg hσ1.le
  have hcs1 : inghamUniformGabrielCriticalShare (nearHalfSigma u) ≤ 1 :=
    inghamUniformGabrielCriticalShare_le_one hσ0 hσ1.le
  have hLpow : L ^ (2 * inghamUniformGabrielCriticalShare (nearHalfSigma u)) ≤ L ^ (2 : ℕ) := by
    have := Real.rpow_le_rpow_of_exponent_le hL1
      (show 2 * inghamUniformGabrielCriticalShare (nearHalfSigma u) ≤ 2 by linarith)
    simpa [Real.rpow_two] using this
  have hQ := nearHalf_detectorConstant_le hu5
  rw [inghamUniformGabrielCenter_nearHalfSigma] at hQ
  have hXp1 : 1 ≤ (X : ℝ) ^ (1 - 6 / 5 * u) := Real.one_le_rpow hX1 (by linarith)
  have hL2 : 1 ≤ L ^ (2 : ℕ) := one_le_pow₀ hL1
  have hQ0 : 0 ≤ ((1 + 1 / (1 - (1 / 2 + 19 / 20 * u))) * Real.exp 1) ^ (2 : ℕ) *
      (1 + inghamMovingRightTranslatedExplicitConstant
        ((9 / 100 : ℝ) * (1 - nearHalfSigma u))) := by
    have : 0 < 1 - (1 / 2 + 19 / 20 * u) := by linarith
    have : 0 ≤ inghamMovingRightTranslatedExplicitConstant
        ((9 / 100 : ℝ) * (1 - nearHalfSigma u)) := by
      unfold inghamMovingRightTranslatedExplicitConstant
      have : 0 < (9 / 100 : ℝ) * (1 - nearHalfSigma u) := by
        unfold nearHalfSigma; nlinarith
      positivity
    positivity
  have hXe0 : 0 ≤ (X : ℝ) ^ inghamUniformGabrielConservativeExponent (nearHalfSigma u) :=
    Real.rpow_nonneg (by linarith) _
  have hLe0 : 0 ≤ L ^ (2 * inghamUniformGabrielCriticalShare (nearHalfSigma u)) :=
    Real.rpow_nonneg (by linarith) _
  have hB : ((1 + 1 / (1 - (1 / 2 + 19 / 20 * u))) * Real.exp 1) ^ (2 : ℕ) *
        (1 + inghamMovingRightTranslatedExplicitConstant
          ((9 / 100 : ℝ) * (1 - nearHalfSigma u))) *
        (X : ℝ) ^ inghamUniformGabrielConservativeExponent (nearHalfSigma u) *
        L ^ (2 * inghamUniformGabrielCriticalShare (nearHalfSigma u)) ≤
      Q₀ * ((X : ℝ) ^ (1 - 6 / 5 * u) * L ^ (2 : ℕ)) := by
    calc _ ≤ Q₀ * (X : ℝ) ^ (1 - 6 / 5 * u) * L ^ (2 : ℕ) := by gcongr
      _ = Q₀ * ((X : ℝ) ^ (1 - 6 / 5 * u) * L ^ (2 : ℕ)) := by ring
  have hL2P : L ^ (2 : ℕ) ≤ (X : ℝ) ^ (1 - 6 / 5 * u) * L ^ (2 : ℕ) :=
    le_mul_of_one_le_left (by positivity) hXp1
  have hP1 : 1 ≤ (X : ℝ) ^ (1 - 6 / 5 * u) * L ^ (2 : ℕ) := one_le_mul_of_one_le_of_one_le hXp1 hL2
  have hfinal := count_le_of_charge hK₀ hu hcount hm hB hL2P hP1
  refine hfinal.trans (le_of_eq ?_)
  ring

end

end RHTower.Sieve.InghamNearHalf
