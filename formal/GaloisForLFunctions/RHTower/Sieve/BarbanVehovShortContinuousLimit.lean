import GaloisForLFunctions.RHTower.Sieve.BarbanVehovShortContinuousAsymptotic

/-!
# Limits of the exact continuous short-main polynomials

Every lower-degree harmonic constant is retained in the exact polynomials and then shown to vanish
under the relevant normalization.  The homogeneous terms are evaluated by the unconditional Selberg
moment asymptotics.
-/

open Filter Topology

namespace RHTower.Sieve

noncomputable section

set_option maxHeartbeats 800000

private theorem tendsto_div_log_pow_succ_zero
    {f : ℕ → ℝ} {a : ℕ} {c : ℝ}
    (h : Tendsto (fun N : ℕ => f N / Real.log N ^ a) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => f N / Real.log N ^ (a + 1)) atTop (𝓝 0) := by
  have hinv : Tendsto (fun N : ℕ => (Real.log (N : ℝ))⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hm := h.mul hinv
  convert hm using 1
  · funext N
    rw [pow_succ]
    field_simp
  · ring

private theorem tendsto_div_log_pow_add_two_zero
    {f : ℕ → ℝ} {a : ℕ} {c : ℝ}
    (h : Tendsto (fun N : ℕ => f N / Real.log N ^ a) atTop (𝓝 c)) :
    Tendsto (fun N : ℕ => f N / Real.log N ^ (a + 2)) atTop (𝓝 0) := by
  have h1 := tendsto_div_log_pow_succ_zero h
  have h2 := tendsto_div_log_pow_succ_zero h1
  simpa [Nat.add_assoc] using h2

/-- The base continuous polynomial has leading coefficient `τ + 5/2`. -/
theorem tendsto_barbanVehovShortBaseContinuousPolynomial_div_log_sq (τ : ℝ) :
    Tendsto (fun M : ℕ =>
      barbanVehovShortBaseContinuousPolynomial τ M / Real.log M ^ (2 : ℕ))
      atTop (𝓝 (τ + 5 / 2)) := by
  have h11 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 1) (by norm_num) (by norm_num)
  have h21 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 2) (j := 1) (by norm_num) (by norm_num)
  have h12 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 2) (by norm_num) (by norm_num)
  have hg11 := tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    (i := 1) (j := 1) (by norm_num) (by norm_num)
  have h11zero := tendsto_div_log_pow_succ_zero h11
  norm_num at h11 h21 h12 hg11 h11zero
  have hcomb := ((((h11.const_mul τ).add
    (h11zero.const_mul (harmonicLogMomentTotalConstant 0))).add h21).add h12).add hg11
  have hcomb' : Tendsto (fun M : ℕ =>
      τ * (selbergOriginalLogMonomial 1 1 M / Real.log M) +
        harmonicLogMomentTotalConstant 0 *
          (selbergOriginalLogMonomial 1 1 M / Real.log M ^ (2 : ℕ)) +
        selbergOriginalLogMonomial 2 1 M / Real.log M ^ (2 : ℕ) +
        selbergOriginalLogMonomial 1 2 M / Real.log M ^ (2 : ℕ) +
        selbergOriginalGcdLogMonomial 1 1 M / Real.log M ^ (2 : ℕ))
      atTop (𝓝 (τ + 5 / 2)) := by
    convert hcomb using 1 <;> ring
  refine hcomb'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hlog : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  rw [barbanVehovShortBaseContinuousPolynomial]
  field_simp [hlog]

/-- The cross continuous polynomial has leading coefficient `-(2 + 2τ + τ²/2)`. -/
theorem tendsto_barbanVehovShortCrossContinuousPolynomial_div_log_cube (τ : ℝ) :
    Tendsto (fun M : ℕ =>
      barbanVehovShortCrossContinuousPolynomial τ M / Real.log M ^ (3 : ℕ))
      atTop (𝓝 (-(2 + 2 * τ + τ ^ (2 : ℕ) / 2))) := by
  have h11 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 1) (by norm_num) (by norm_num)
  have h21 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 2) (j := 1) (by norm_num) (by norm_num)
  have h12 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 2) (by norm_num) (by norm_num)
  have h31 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 3) (j := 1) (by norm_num) (by norm_num)
  have h13 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 3) (by norm_num) (by norm_num)
  have hg11 := tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    (i := 1) (j := 1) (by norm_num) (by norm_num)
  have hg21 := tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    (i := 2) (j := 1) (by norm_num) (by norm_num)
  have hg2 := tendsto_selbergOriginalGcdLogPowerMonomial_div_log_pow 2
  have h11z := tendsto_div_log_pow_succ_zero h11
  have h11zz := tendsto_div_log_pow_add_two_zero h11
  have h21z := tendsto_div_log_pow_succ_zero h21
  have hg11z := tendsto_div_log_pow_succ_zero hg11
  norm_num at h11 h21 h12 h31 h13 hg11 hg21 hg2 h11z h11zz h21z hg11z
  have hmain := (((((((h11.const_mul (-(τ + τ ^ (2 : ℕ) / 2))).add
    (h21.const_mul (-1))).add (hg11.const_mul (-1))).add
      (h12.const_mul (-(1 + τ)))).add (h31.const_mul (1 / 2 : ℝ))).add hg21).add
        (hg2.const_mul (1 / 2 : ℝ))).add (h13.const_mul (-1 / 2 : ℝ))
  have hconst0 := ((h11z.sub h21z).sub hg11z).const_mul
    (-(harmonicLogMomentTotalConstant 0))
  have hconst1 := h11zz.const_mul (-(harmonicLogMomentTotalConstant 1))
  have hcomb := (hmain.add hconst0).add hconst1
  have hcomb' : Tendsto (fun M : ℕ =>
      -(τ + τ ^ (2 : ℕ) / 2) *
          (selbergOriginalLogMonomial 1 1 M / Real.log M) -
        selbergOriginalLogMonomial 2 1 M / Real.log M ^ (2 : ℕ) -
        selbergOriginalGcdLogMonomial 1 1 M / Real.log M ^ (2 : ℕ) -
        (1 + τ) * (selbergOriginalLogMonomial 1 2 M / Real.log M ^ (2 : ℕ)) +
        (1 / 2 : ℝ) * (selbergOriginalLogMonomial 3 1 M / Real.log M ^ (3 : ℕ)) +
        selbergOriginalGcdLogMonomial 2 1 M / Real.log M ^ (3 : ℕ) +
        (1 / 2 : ℝ) *
          (selbergOriginalGcdLogPowerMonomial 2 M / Real.log M ^ (3 : ℕ)) -
        (1 / 2 : ℝ) * (selbergOriginalLogMonomial 1 3 M / Real.log M ^ (3 : ℕ)) -
        harmonicLogMomentTotalConstant 0 *
          (selbergOriginalLogMonomial 1 1 M / Real.log M ^ (2 : ℕ) -
            selbergOriginalLogMonomial 2 1 M / Real.log M ^ (3 : ℕ) -
            selbergOriginalGcdLogMonomial 1 1 M / Real.log M ^ (3 : ℕ)) -
        harmonicLogMomentTotalConstant 1 *
          (selbergOriginalLogMonomial 1 1 M / Real.log M ^ (3 : ℕ)))
      atTop (𝓝 (-(2 + 2 * τ + τ ^ (2 : ℕ) / 2))) := by
    convert hcomb using 1
    · funext M
      ring
    · ring
  refine hcomb'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hlog : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  rw [barbanVehovShortCrossContinuousPolynomial]
  field_simp [hlog]

/-- The differentiated-square continuous polynomial has its full cubic-in-`τ` leading
coefficient. -/
theorem tendsto_barbanVehovShortDerivativeContinuousPolynomial_div_log_four (τ : ℝ) :
    Tendsto (fun M : ℕ =>
      barbanVehovShortDerivativeContinuousPolynomial τ M / Real.log M ^ (4 : ℕ))
      atTop (𝓝 (13 / 4 + 13 * τ / 3 + 2 * τ ^ (2 : ℕ) + τ ^ (3 : ℕ) / 3)) := by
  have h11 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 1) (by norm_num) (by norm_num)
  have h21 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 2) (j := 1) (by norm_num) (by norm_num)
  have h12 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 2) (by norm_num) (by norm_num)
  have h22 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 2) (j := 2) (by norm_num) (by norm_num)
  have h32 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 3) (j := 2) (by norm_num) (by norm_num)
  have h23 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 2) (j := 3) (by norm_num) (by norm_num)
  have h41 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 4) (j := 1) (by norm_num) (by norm_num)
  have h14 := tendsto_selbergOriginalLogMonomial_div_log_pow
    (i := 1) (j := 4) (by norm_num) (by norm_num)
  have hg11 := tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    (i := 1) (j := 1) (by norm_num) (by norm_num)
  have hg21 := tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    (i := 2) (j := 1) (by norm_num) (by norm_num)
  have hg12 := tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    (i := 1) (j := 2) (by norm_num) (by norm_num)
  have hg22 := tendsto_selbergOriginalGcdLogMonomial_div_log_pow
    (i := 2) (j := 2) (by norm_num) (by norm_num)
  have hg2 := tendsto_selbergOriginalGcdLogPowerMonomial_div_log_pow 2
  have hg3 := tendsto_selbergOriginalGcdLogPowerMonomial_div_log_pow 3
  have hsq21 := tendsto_selbergOriginalGcdLogSquareTwoOneMonomial_div_log_four
  have hsq12 := tendsto_selbergOriginalGcdLogSquareOneTwoMonomial_div_log_four
  have h11z := tendsto_div_log_pow_succ_zero h11
  have h11zz := tendsto_div_log_pow_add_two_zero h11
  have h11zzz := tendsto_div_log_pow_succ_zero h11zz
  have h21z := tendsto_div_log_pow_succ_zero h21
  have h21zz := tendsto_div_log_pow_succ_zero h21z
  have h12z := tendsto_div_log_pow_succ_zero h12
  have h12zz := tendsto_div_log_pow_succ_zero h12z
  have h22z := tendsto_div_log_pow_succ_zero h22
  have hg11z := tendsto_div_log_pow_succ_zero hg11
  have hg11zz := tendsto_div_log_pow_succ_zero hg11z
  have hg21z := tendsto_div_log_pow_succ_zero hg21
  have hg12z := tendsto_div_log_pow_succ_zero hg12
  have hg2z := tendsto_div_log_pow_succ_zero hg2
  norm_num at h11 h21 h12 h22 h32 h23 h41 h14 hg11 hg21 hg12 hg22 hg2 hg3
  norm_num at hsq21 hsq12 h11z h11zz h11zzz h21z h21zz h12z h12zz h22z hg11z
  norm_num at hg11zz hg21z hg12z hg2z
  have hmain0 := (h11.const_mul (τ + τ ^ (2 : ℕ) + τ ^ (3 : ℕ) / 3)).add
    ((h21.add h12).const_mul (1 + τ + τ ^ (2 : ℕ) / 2))
  have hmain1 := (hmain0.add hg11).add (h22.const_mul τ)
  have hmain2 := ((hmain1.sub hg21).sub hg12).sub hg2
  have hmain3 := hmain2.add ((h32.add h23).const_mul (1 / 2 : ℝ))
  have hmain4 := hmain3.add ((h41.add h14).const_mul (-1 / 6 : ℝ))
  have hmain5 := (hmain4.add hg22).add ((hsq21.add hsq12).const_mul (1 / 2 : ℝ))
  have hmain := hmain5.add (hg3.const_mul (1 / 3 : ℝ))
  have hconst0core := ((((((h11z.sub h21z).sub h12z).sub
    (hg11z.const_mul 2)).add h22z).add hg21z).add hg12z).add hg2z
  have hconst0 := hconst0core.const_mul (harmonicLogMomentTotalConstant 0)
  have hconst1core := (((h11zz.const_mul 2).sub h21zz).sub h12zz).sub
    (hg11zz.const_mul 2)
  have hconst1 := hconst1core.const_mul (harmonicLogMomentTotalConstant 1)
  have hconst2 := h11zzz.const_mul (harmonicLogMomentTotalConstant 2)
  have hcomb := ((hmain.add hconst0).add hconst1).add hconst2
  convert hcomb using 1
  · funext M
    by_cases hlog : Real.log (M : ℝ) = 0
    · simp [barbanVehovShortDerivativeContinuousPolynomial, hlog]
    · rw [barbanVehovShortDerivativeContinuousPolynomial]
      field_simp [hlog]
      ring
  · ring

/-- Limiting continuous short-energy constant at logarithmic separation `τ` and reciprocal
derivative tuning `ρ`. -/
def barbanVehovShortContinuousLimitConstant (τ ρ : ℝ) : ℝ :=
  τ + 5 / 2 - 2 * ρ * (2 + 2 * τ + τ ^ (2 : ℕ) / 2) +
    ρ ^ (2 : ℕ) * (13 / 4 + 13 * τ / 3 + 2 * τ ^ (2 : ℕ) + τ ^ (3 : ℕ) / 3)

/-- Exact polynomial version of the normalized continuous short energy. -/
def barbanVehovShortContinuousPolynomialEnergy (τ ρ : ℝ) (M : ℕ) : ℝ :=
  (barbanVehovShortBaseContinuousPolynomial τ M +
      2 * (ρ / Real.log M) * barbanVehovShortCrossContinuousPolynomial τ M +
      (ρ / Real.log M) ^ (2 : ℕ) *
        barbanVehovShortDerivativeContinuousPolynomial τ M) /
    Real.log M ^ (2 : ℕ)

theorem tendsto_barbanVehovShortContinuousPolynomialEnergy (τ ρ : ℝ) :
    Tendsto (barbanVehovShortContinuousPolynomialEnergy τ ρ)
      atTop (𝓝 (barbanVehovShortContinuousLimitConstant τ ρ)) := by
  have hb := tendsto_barbanVehovShortBaseContinuousPolynomial_div_log_sq τ
  have hc := tendsto_barbanVehovShortCrossContinuousPolynomial_div_log_cube τ
  have hd := tendsto_barbanVehovShortDerivativeContinuousPolynomial_div_log_four τ
  have hcomb := (hb.add (hc.const_mul (2 * ρ))).add (hd.const_mul (ρ ^ (2 : ℕ)))
  have hcomb' : Tendsto (fun M : ℕ =>
      barbanVehovShortBaseContinuousPolynomial τ M / Real.log M ^ (2 : ℕ) +
        2 * ρ *
          (barbanVehovShortCrossContinuousPolynomial τ M / Real.log M ^ (3 : ℕ)) +
        ρ ^ (2 : ℕ) *
          (barbanVehovShortDerivativeContinuousPolynomial τ M / Real.log M ^ (4 : ℕ)))
      atTop (𝓝 (barbanVehovShortContinuousLimitConstant τ ρ)) := by
    convert hcomb using 1
    rw [barbanVehovShortContinuousLimitConstant]
    ring
  refine hcomb'.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with M hM
  have hlog : Real.log (M : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hM)).ne'
  rw [barbanVehovShortContinuousPolynomialEnergy]
  field_simp [hlog]

theorem barbanVehovShortEnergyContinuous_eq_polynomialEnergy
    {X M : ℕ} (hX : 0 < X) (hM : 0 < M) {τ ρ : ℝ}
    (hlog : Real.log X = (2 + τ) * Real.log M) :
    barbanVehovShortEnergyContinuous (ρ / Real.log M) X M =
      barbanVehovShortContinuousPolynomialEnergy τ ρ M := by
  rw [barbanVehovShortEnergyContinuous,
    barbanVehovShortContinuousPolynomialEnergy,
    barbanVehovShortBaseContinuous_eq_polynomial hX hM hlog,
    barbanVehovShortCrossContinuous_eq_polynomial hX hM hlog,
    barbanVehovShortDerivativeContinuous_eq_polynomial hX hM hlog]

private theorem tendsto_nat_pow_fortyNine_atTop :
    Tendsto (fun N : ℕ => N ^ (49 : ℕ)) atTop atTop := by
  rw [tendsto_atTop]
  intro B
  filter_upwards [eventually_ge_atTop (max B 1)] with N hN
  have hBN : B ≤ N := (Nat.le_max_left B 1).trans hN
  have hN1 : 1 ≤ N := (Nat.le_max_right B 1).trans hN
  exact hBN.trans (by
    calc
      N ≤ N * N ^ (48 : ℕ) := Nat.le_mul_of_pos_right N (pow_pos hN1 48)
      _ = N ^ (49 : ℕ) := by ring)

private theorem log_hundred_eq_two_add_twoOverFortyNine_mul_log_fortyNine
    (N : ℕ) :
    Real.log (((N ^ (100 : ℕ) : ℕ) : ℝ)) =
      (2 + (2 / 49 : ℝ)) * Real.log (((N ^ (49 : ℕ) : ℕ) : ℝ)) := by
  norm_num [Nat.cast_pow, Real.log_pow]
  ring

theorem barbanVehovShortContinuousLimitConstant_twoOverFortyNine_fortyNineOverHundred :
    barbanVehovShortContinuousLimitConstant (2 / 49) (49 / 100) =
      (7782751 / 5880000 : ℝ) := by
  rw [barbanVehovShortContinuousLimitConstant]
  norm_num

/-- Continuous short detector at the exact `X=N^(100 : ℕ)`, `M=N^(49 : ℕ)` reciprocal schedule. -/
theorem tendsto_barbanVehovShortEnergyContinuous_fortyNine_reciprocal :
    Tendsto (fun N : ℕ =>
      barbanVehovShortEnergyContinuous
        ((49 / 100 : ℝ) / (49 * Real.log N)) (N ^ (100 : ℕ)) (N ^ (49 : ℕ)))
      atTop (𝓝 (7782751 / 5880000 : ℝ)) := by
  have hpoly := tendsto_barbanVehovShortContinuousPolynomialEnergy
    (2 / 49 : ℝ) (49 / 100 : ℝ)
  have hcomp := hpoly.comp tendsto_nat_pow_fortyNine_atTop
  rw [barbanVehovShortContinuousLimitConstant_twoOverFortyNine_fortyNineOverHundred]
    at hcomp
  refine hcomp.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hNpos : 0 < N := by omega
  have hMpos : 0 < N ^ (49 : ℕ) := pow_pos hNpos 49
  have hXpos : 0 < N ^ (100 : ℕ) := pow_pos hNpos 100
  have hlam :
      (49 / 100 : ℝ) / (49 * Real.log N) =
        (49 / 100 : ℝ) / Real.log (N ^ (49 : ℕ) : ℕ) := by
    rw [show (((N ^ (49 : ℕ) : ℕ) : ℝ)) = (N : ℝ) ^ (49 : ℕ) by norm_num,
      Real.log_pow]
    norm_num
  rw [hlam]
  simpa only [Function.comp_apply] using
    (barbanVehovShortEnergyContinuous_eq_polynomialEnergy
      (τ := (2 / 49 : ℝ)) (ρ := (49 / 100 : ℝ)) hXpos hMpos
      (log_hundred_eq_two_add_twoOverFortyNine_mul_log_fortyNine N)).symm

end

end RHTower.Sieve
