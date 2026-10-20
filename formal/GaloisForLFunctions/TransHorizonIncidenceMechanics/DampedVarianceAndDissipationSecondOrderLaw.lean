import GaloisForLFunctions.TransHorizonIncidenceMechanics.HalfDampingDissipationLaw

/-!
# The second-order law of the damped variance and dissipation

The damped divisor function `τ_ε` has variance `V(ε) = E[τ_ε²] - E[τ_ε]²` and Haar dissipation rate
`R(ε) = E[τ_ε²] - Σ_e μ(e) w_ε(e)²`, both `ε/2 + o(ε)`. At second order they separate:

* **the Euler constant cancels in the second moment**: `E[τ_ε²] = H(ε) ζ(1+2ε)/ζ(1+ε)²` with the
  Euler correction `1 - H(ε) = O(ε²)`, and `ζ(1+s) = 1/s + γ + o(1)` gives
  `ζ(1+2ε)/ζ(1+ε)² = ε/2 + (γ - γ) ε² + o(ε²)`, so `E[τ_ε²] = ε/2 + o(ε²)`;
* **parity kills the lag-one Bézout mean**: removing the prime `2` from the sum over moduli factors
  out `1 - (2^{1+ε} - 1)^{-2} = O(ε)`, so `Σ_e μ(e) w_ε(e)² = O(ε E[τ_ε]²) = O(ε³)`.

Hence, with `E[τ_ε] = ε + O(ε²)`,

`V(ε) = ε/2 - ε² + o(ε²)`,  `R(ε) = ε/2 + o(ε²)`,  `A_ε(1) = -ε² + o(ε²)`:

the dissipation rate agrees with the full second moment, not with the variance, and exceeds the
variance by the squared mean. Successive values of `τ_ε` are anti-correlated at exactly the scale of
the squared mean, because one of two consecutive integers is even and `τ_ε` of an even number carries
the factor `1 - 2^{-ε}`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Zeta near one -/

/-- `ζ(1 + cε) - 1/(cε) → γ` as `ε → 0⁺`. -/
theorem tendsto_riemannZeta_one_add_sub_inv {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε : ℝ => riemannZeta (1 + ((c * ε : ℝ) : ℂ)) - 1 / ((c * ε : ℝ) : ℂ)) (𝓝[>] 0)
      (𝓝 (Real.eulerMascheroniConstant : ℂ)) := by
  have hmap : Tendsto (fun ε : ℝ => 1 + c * ε) (𝓝[>] 0) (𝓝[>] 1) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : Continuous (fun ε : ℝ => 1 + c * ε) := by fun_prop
      simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have : 0 < c * ε := mul_pos hc hε
      show 1 < 1 + c * ε
      linarith
  refine (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp hmap).congr fun ε => ?_
  simp only [Function.comp_apply]
  have h1 : ((1 + c * ε : ℝ) : ℂ) = 1 + ((c * ε : ℝ) : ℂ) := by push_cast; ring
  rw [h1, add_sub_cancel_left]

/-- With `Z(s) = ζ(1+s)`: `Z(2ε) - ε Z(ε)²/2 → 0` (the Euler constant cancels) and `ε Z(ε) → 1`. -/
private theorem tendsto_zeta_second_order :
    Tendsto (fun ε : ℝ => riemannZeta (1 + ((2 * ε : ℝ) : ℂ)) -
      (ε : ℂ) * riemannZeta (1 + (ε : ℂ)) ^ 2 / 2) (𝓝[>] 0) (𝓝 0) ∧
    Tendsto (fun ε : ℝ => (ε : ℂ) * riemannZeta (1 + (ε : ℂ))) (𝓝[>] 0) (𝓝 1) := by
  have hu := tendsto_riemannZeta_one_add_sub_inv (c := 1) one_pos
  have hv := tendsto_riemannZeta_one_add_sub_inv (c := 2) two_pos
  simp only [one_mul] at hu
  have he : Tendsto (fun ε : ℝ => (ε : ℂ)) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Complex.continuous_ofReal.tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  set γ : ℂ := (Real.eulerMascheroniConstant : ℂ)
  constructor
  · have h := (hv.sub hu).sub ((he.mul (hu.pow 2)).div_const 2)
    rw [show γ - γ - 0 * γ ^ 2 / 2 = (0 : ℂ) by ring] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
    push_cast
    field_simp
    ring
  · have h := (he.mul hu).const_add 1
    rw [show (1 : ℂ) + 0 * γ = 1 by ring] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε0 : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hε)
    field_simp
    ring

/-- `(ρ_ε²/ρ_{2ε} - ε/2)/ε² → 0` for the density `ρ_ε = E[τ_ε] = 1/ζ(1+ε)`. -/
private theorem tendsto_density_ratio_second_order :
    Tendsto (fun ε : ℝ => ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 /
      (RHTower.pmPowerDampedDivisorDensity (2 * ε)).re - ε / 2) / ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨hnum, hden⟩ := tendsto_zeta_second_order
  have hc := hnum.div (hden.pow 2) (by norm_num)
  rw [zero_div] at hc
  have hr := (Complex.continuous_re.tendsto _).comp hc
  rw [Complex.zero_re] at hr
  refine hr.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have hεc : (ε : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hε0.ne'
  have hZ1 : riemannZeta (1 + (ε : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hZ2 : riemannZeta (1 + 2 * (ε : ℂ)) ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by simp; linarith)
  have hρ1 : ((RHTower.pmPowerDampedDivisorDensity ε).re : ℂ) = 1 / riemannZeta (1 + (ε : ℂ)) := by
    rw [← RHTower.pmPowerDampedDivisorDensity_eq_ofReal_re hε0]; rfl
  have hρ2 : ((RHTower.pmPowerDampedDivisorDensity (2 * ε)).re : ℂ) =
      1 / riemannZeta (1 + 2 * (ε : ℂ)) := by
    rw [← RHTower.pmPowerDampedDivisorDensity_eq_ofReal_re (by linarith),
      RHTower.pmPowerDampedDivisorDensity]
    push_cast; rfl
  have key : (riemannZeta (1 + ((2 * ε : ℝ) : ℂ)) - (ε : ℂ) * riemannZeta (1 + (ε : ℂ)) ^ 2 / 2) /
      ((ε : ℂ) * riemannZeta (1 + (ε : ℂ))) ^ 2 =
      ((((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 /
        (RHTower.pmPowerDampedDivisorDensity (2 * ε)).re - ε / 2) / ε ^ 2 : ℝ) : ℂ) := by
    push_cast
    rw [hρ1, hρ2]
    field_simp
  simp only [Function.comp_apply, Pi.div_apply]
  rw [key, Complex.ofReal_re]

/-! ### The Euler correction is second order -/

private theorem summable_primes_rpow :
    Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) :=
  (Real.summable_nat_rpow.mpr (by norm_num : -(3 / 2 : ℝ) < -1)).comp_injective
    Subtype.val_injective

/-- Each prime deficit of the Euler correction is `≤ 64 ε² p^{-3/2}`: `1 - p^{-ε} ≤ ε log p`. -/
private theorem primeDeficit_le {ε : ℝ} (hε : 0 ≤ ε) (p : Nat.Primes) :
    RHTower.pmPowerDampedVariancePrimeDeficit ε p ≤ 64 * ε ^ 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.property.two_le
  set P : ℝ := ((p : ℕ) : ℝ)
  set t := P ^ (-ε)
  have hp0 : (0 : ℝ) < P := by linarith
  have ht0 : 0 ≤ t := Real.rpow_nonneg hp0.le _
  have ht1 : t ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hlog : Real.log P ≤ 4 * P ^ (1 / 4 : ℝ) := by
    calc Real.log P ≤ P ^ (1 / 4 : ℝ) / (1 / 4) :=
          Real.log_le_rpow_div hp0.le (by norm_num)
      _ = 4 * P ^ (1 / 4 : ℝ) := by ring
  have h1t : 1 - t ≤ ε * Real.log P := by
    have := Real.add_one_le_exp (Real.log P * (-ε))
    rw [← Real.rpow_def_of_pos hp0] at this
    linarith
  have hlog0 : 0 ≤ Real.log P := Real.log_nonneg (by linarith)
  have hq0 : 0 ≤ (t - t ^ 2) / (P - t) := div_nonneg (by nlinarith) (by linarith)
  have hq : (t - t ^ 2) / (P - t) ≤ 8 * ε * P ^ (1 / 4 : ℝ) / P := by
    rw [div_le_div_iff₀ (by linarith) hp0]
    have hnum : t - t ^ 2 ≤ 4 * ε * P ^ (1 / 4 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hε]
    have hP4 : 0 ≤ P ^ (1 / 4 : ℝ) := Real.rpow_nonneg hp0.le _
    nlinarith [mul_nonneg hε hP4]
  have hpow : (8 * ε * P ^ (1 / 4 : ℝ) / P) ^ 2 = 64 * ε ^ 2 * P ^ (-(3 / 2 : ℝ)) := by
    rw [div_pow, mul_pow, mul_pow, ← Real.rpow_natCast (P ^ (1 / 4 : ℝ)) 2,
      ← Real.rpow_mul hp0.le, ← Real.rpow_natCast P 2, mul_div_assoc, ← Real.rpow_sub hp0]
    norm_num
  unfold RHTower.pmPowerDampedVariancePrimeDeficit
  calc ((P ^ (-ε) - (P ^ (-ε)) ^ 2) / (P - P ^ (-ε))) ^ 2
      ≤ (8 * ε * P ^ (1 / 4 : ℝ) / P) ^ 2 := pow_le_pow_left₀ hq0 hq 2
    _ = _ := hpow

/-- `(H(ε) - 1)/ε → 0` for the Euler correction `H = E[τ_ε²] ρ_{2ε}/ρ_ε²`. -/
private theorem tendsto_varianceCorrection_sub_one_div :
    Tendsto (fun ε : ℝ => (RHTower.pmPowerDampedVarianceCorrection ε - 1) / ε) (𝓝[>] 0) (𝓝 0) := by
  set S := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
  have hb : Tendsto (fun ε : ℝ => 64 * S * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using ((tendsto_id.mono_left nhdsWithin_le_nhds :
      Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0))).const_mul (64 * S)
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  obtain ⟨hlo, hhi⟩ := RHTower.pmPowerDampedVarianceCorrection_bounds hε0
  have hsum : ∑' p : Nat.Primes, RHTower.pmPowerDampedVariancePrimeDeficit ε p ≤
      64 * ε ^ 2 * S := by
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum (fun p => primeDeficit_le hε0.le p)
      (RHTower.summable_pmPowerDampedVariancePrimeDeficit hε0.le) (summable_primes_rpow.mul_left _)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hε0, div_le_iff₀ hε0, abs_sub_comm,
    abs_of_nonneg (by linarith)]
  have : 64 * ε ^ 2 * S = 64 * S * ε * ε := by ring
  linarith

/-! ### The second moment and the variance -/

/-- **The Euler constant cancels.** `E[τ_ε²] = ε/2 + o(ε²)`. -/
theorem tendsto_pmPowerDampedSecondDensity_second_order :
    Tendsto (fun ε : ℝ => (RHTower.pmPowerDampedSecondDensity ε - ε / 2) / ε ^ 2) (𝓝[>] 0)
      (𝓝 0) := by
  have h := (RHTower.tendsto_pmPowerDampedVarianceCorrection.mul
    tendsto_density_ratio_second_order).add (tendsto_varianceCorrection_sub_one_div.div_const 2)
  rw [mul_zero, zero_div, add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : (0 : ℝ) < ε := hε
  have ha := RHTower.pmPowerDampedDivisorDensity_re_ne_zero hε0
  have ha2 := RHTower.pmPowerDampedDivisorDensity_re_ne_zero (show (0 : ℝ) < 2 * ε by linarith)
  simp only [RHTower.pmPowerDampedVarianceCorrection]
  field_simp
  ring

/-- **Second-order variance.** `V(ε) = ε/2 - ε² + o(ε²)`. -/
theorem tendsto_pmPowerDampedDivisorVariance_second_order :
    Tendsto (fun ε : ℝ => (RHTower.pmPowerDampedDivisorVariance ε - ε / 2) / ε ^ 2) (𝓝[>] 0)
      (𝓝 (-1)) := by
  have h := tendsto_pmPowerDampedSecondDensity_second_order.sub
    (RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter.pow 2)
  rw [one_pow, zero_sub] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : ε ≠ 0 := ne_of_gt hε
  simp only [RHTower.pmPowerDampedDivisorVariance]
  field_simp
  ring

/-! ### Parity and the lag-one Bézout mean -/

private theorem summable_bezout_term {ε : ℝ} (hε : 0 < ε) :
    Summable fun e : ℕ => moebiusReal e * dampedRamanujanCoeff ε e ^ 2 := by
  refine Summable.of_norm_bounded ((summable_sqfreeTotientInv_div_totient.1).mul_left
    ((RHTower.pmPowerDampedDivisorDensity ε).re ^ 2)) fun e => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (dampedRamanujanCoeff ε e))]
  have hμ : |moebiusReal e| ≤ 1 := by
    unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc |moebiusReal e| * dampedRamanujanCoeff ε e ^ 2 ≤ 1 * dampedRamanujanCoeff ε e ^ 2 :=
        mul_le_mul_of_nonneg_right hμ (sq_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact dampedRamanujanCoeff_sq_le hε e

theorem moebiusReal_two_mul_odd {m : ℕ} (hm : ¬ 2 ∣ m) :
    moebiusReal (2 * m) = -moebiusReal m := by
  unfold moebiusReal
  have hcop : Nat.Coprime 2 m := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  push_cast; ring

theorem moebiusReal_four_mul (j : ℕ) : moebiusReal (2 * (2 * j)) = 0 := by
  unfold moebiusReal
  rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree]
  · simp
  · intro h
    have := h 2 ⟨j, by ring⟩
    simp at this

/-- At an odd modulus, doubling divides the Ramanujan coefficient by `-(2^{1+ε} - 1)`. -/
private theorem dampedRamanujanCoeff_two_mul {ε : ℝ} (hε : 0 < ε) {m : ℕ} (hm : ¬ 2 ∣ m) :
    dampedRamanujanCoeff ε (2 * m) = -dampedRamanujanCoeff ε m / ((2 : ℝ) ^ (1 + ε) - 1) := by
  unfold dampedRamanujanCoeff
  rw [RHTower.pmPowerDampedRamanujanWeight_prime_mul hε Nat.prime_two hm, Complex.div_ofReal_re,
    Complex.neg_re]
  norm_num

/-- **Parity factorisation.** `Σ_e μ(e) w_ε(e)² = (1 - (2^{1+ε} - 1)^{-2}) Σ_{e odd} μ(e) w_ε(e)²`. -/
theorem dampedBezoutLimit_eq_parity {ε : ℝ} (hε : 0 < ε) :
    dampedBezoutLimit ε = (1 - 1 / ((2 : ℝ) ^ (1 + ε) - 1) ^ 2) *
      ∑' j : ℕ, moebiusReal (2 * j + 1) * dampedRamanujanCoeff ε (2 * j + 1) ^ 2 := by
  set f : ℕ → ℝ := fun e => moebiusReal e * dampedRamanujanCoeff ε e ^ 2
  have hf : Summable f := summable_bezout_term hε
  have hinj2 : Function.Injective (fun k : ℕ => 2 * k) := mul_right_injective₀ two_ne_zero
  have hinj1 : Function.Injective (fun k : ℕ => 2 * k + 1) :=
    fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega
  have h2 : Summable fun k => f (2 * k) := hf.comp_injective hinj2
  have h1 : Summable fun k => f (2 * k + 1) := hf.comp_injective hinj1
  have h4 : Summable fun j => f (2 * (2 * j)) := h2.comp_injective hinj2
  have h3 : Summable fun j => f (2 * (2 * j + 1)) := h2.comp_injective hinj1
  have hy : (2 : ℝ) ^ (1 + ε) - 1 ≠ 0 := by
    have : (2 : ℝ) < 2 ^ (1 + ε) := by
      calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
        _ < 2 ^ (1 + ε) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
    linarith
  have hodd : ∀ j, f (2 * (2 * j + 1)) =
      -(1 / ((2 : ℝ) ^ (1 + ε) - 1) ^ 2) * f (2 * j + 1) := fun j => by
    have hm : ¬ 2 ∣ 2 * j + 1 := by omega
    simp only [f]
    rw [moebiusReal_two_mul_odd hm, dampedRamanujanCoeff_two_mul hε hm]
    field_simp
  have heven : ∀ j, f (2 * (2 * j)) = 0 := fun j => by
    simp only [f]; rw [moebiusReal_four_mul, zero_mul]
  have hsplit := tsum_even_add_odd (f := fun k => f (2 * k)) h4 h3
  unfold dampedBezoutLimit
  rw [← tsum_even_add_odd h2 h1, ← hsplit]
  simp only [heven, tsum_zero, zero_add, hodd, tsum_mul_left]
  ring

/-- The odd Bézout sum is bounded by `16 E[τ_ε]²`. -/
private theorem abs_odd_bezout_sum_le {ε : ℝ} (hε : 0 < ε) :
    |∑' j : ℕ, moebiusReal (2 * j + 1) * dampedRamanujanCoeff ε (2 * j + 1) ^ 2| ≤
      16 * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := by
  set ρ := (RHTower.pmPowerDampedDivisorDensity ε).re
  set g : ℕ → ℝ := fun e => RHTower.Sieve.sqfreeTotientInv e / (Nat.totient e : ℝ)
  obtain ⟨hg, hg16⟩ := summable_sqfreeTotientInv_div_totient
  have hg0 : ∀ e, 0 ≤ g e := fun e =>
    div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg e) (Nat.cast_nonneg _)
  have hinj : Function.Injective (fun j : ℕ => 2 * j + 1) :=
    fun a b (h : 2 * a + 1 = 2 * b + 1) => by omega
  have hgo : Summable fun j => g (2 * j + 1) := hg.comp_injective hinj
  have hgo_le : ∑' j, g (2 * j + 1) ≤ 16 := (tsum_comp_le_tsum_of_inj hg hg0 hinj).trans hg16
  have hfo : Summable fun j => moebiusReal (2 * j + 1) * dampedRamanujanCoeff ε (2 * j + 1) ^ 2 :=
    (summable_bezout_term hε).comp_injective hinj
  have hterm : ∀ e, ‖moebiusReal e * dampedRamanujanCoeff ε e ^ 2‖ ≤ ρ ^ 2 * g e := fun e => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg (dampedRamanujanCoeff ε e))]
    have hμ : |moebiusReal e| ≤ 1 := by
      unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc |moebiusReal e| * dampedRamanujanCoeff ε e ^ 2 ≤ 1 * dampedRamanujanCoeff ε e ^ 2 :=
          mul_le_mul_of_nonneg_right hμ (sq_nonneg _)
      _ ≤ _ := by rw [one_mul]; exact dampedRamanujanCoeff_sq_le hε e
  calc |∑' j : ℕ, moebiusReal (2 * j + 1) * dampedRamanujanCoeff ε (2 * j + 1) ^ 2|
      = ‖∑' j : ℕ, moebiusReal (2 * j + 1) * dampedRamanujanCoeff ε (2 * j + 1) ^ 2‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∑' j : ℕ, ‖moebiusReal (2 * j + 1) * dampedRamanujanCoeff ε (2 * j + 1) ^ 2‖ :=
        norm_tsum_le_tsum_norm hfo.norm
    _ ≤ ∑' j : ℕ, ρ ^ 2 * g (2 * j + 1) :=
        Summable.tsum_le_tsum (fun j => hterm _) hfo.norm (hgo.mul_left _)
    _ = ρ ^ 2 * ∑' j : ℕ, g (2 * j + 1) := tsum_mul_left
    _ ≤ ρ ^ 2 * 16 := mul_le_mul_of_nonneg_left hgo_le (sq_nonneg ρ)
    _ = 16 * ρ ^ 2 := by ring

/-- The parity factor: `0 ≤ 1 - (2^{1+ε} - 1)^{-2} ≤ 8ε` for `0 ≤ ε ≤ 1`. -/
private theorem parity_factor_bounds {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    0 ≤ 1 - 1 / ((2 : ℝ) ^ (1 + ε) - 1) ^ 2 ∧ 1 - 1 / ((2 : ℝ) ^ (1 + ε) - 1) ^ 2 ≤ 8 * ε := by
  have h2 : (2 : ℝ) ^ (1 + ε) = 2 * 2 ^ ε := by
    rw [Real.rpow_add (by norm_num), Real.rpow_one]
  have hlo : (1 : ℝ) ≤ 2 ^ ε := Real.one_le_rpow (by norm_num) hε
  have hhi : (2 : ℝ) ^ ε ≤ 1 + ε := by
    have := rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hε hε1
    norm_num at this ⊢; linarith
  set y := (2 : ℝ) ^ (1 + ε) - 1
  have hy1 : 1 ≤ y := by simp only [y]; rw [h2]; linarith
  have hy2 : y ≤ 1 + 2 * ε := by simp only [y]; rw [h2]; linarith
  have ht1 : 1 ≤ y ^ 2 := by nlinarith
  have ht0 : 0 < y ^ 2 := by linarith
  constructor
  · rw [sub_nonneg, div_le_one ht0]; exact ht1
  · have hinv : 2 - y ^ 2 ≤ 1 / y ^ 2 := by
      rw [le_div_iff₀ ht0]; nlinarith [sq_nonneg (y ^ 2 - 1)]
    nlinarith

/-- **The lag-one Bézout mean is cubic.** For `0 < ε ≤ 1`, `|Σ_e μ(e) w_ε(e)²| ≤ 128 ε E[τ_ε]²`. -/
theorem abs_dampedBezoutLimit_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    |dampedBezoutLimit ε| ≤ 128 * ε * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := by
  rw [dampedBezoutLimit_eq_parity hε, abs_mul]
  obtain ⟨h0, h8⟩ := parity_factor_bounds hε.le hε1
  rw [abs_of_nonneg h0]
  calc _ ≤ 8 * ε * (16 * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2) :=
        mul_le_mul h8 (abs_odd_bezout_sum_le hε) (abs_nonneg _) (by positivity)
    _ = _ := by ring

/-- `Σ_e μ(e) w_ε(e)² = o(ε²)`. -/
theorem tendsto_dampedBezoutLimit_div_sq :
    Tendsto (fun ε : ℝ => dampedBezoutLimit ε / ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have hρ := RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter
  have he : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun ε : ℝ => 128 * (ε * ((RHTower.pmPowerDampedDivisorDensity ε).re / ε) ^ 2))
      (𝓝[>] 0) (𝓝 0) := by
    simpa using (he.mul (hρ.pow 2)).const_mul 128
  refine squeeze_zero_norm' ?_ hb
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
  obtain ⟨hε0, hε1⟩ := hε
  have hbd := abs_dampedBezoutLimit_le hε0 hε1.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0 : ℝ) < ε ^ 2),
    div_le_iff₀ (by positivity)]
  calc |dampedBezoutLimit ε| ≤ 128 * ε * (RHTower.pmPowerDampedDivisorDensity ε).re ^ 2 := hbd
    _ = 128 * (ε * ((RHTower.pmPowerDampedDivisorDensity ε).re / ε) ^ 2) * ε ^ 2 := by
        field_simp

/-! ### The second-order law -/

/-- **Second-order dissipation.** `R(ε) = ε/2 + o(ε²)`: the dissipation rate follows the full second
moment to second order. -/
theorem tendsto_dampedDissipationRate_second_order :
    Tendsto (fun ε : ℝ => (dampedDissipationRate ε - ε / 2) / ε ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h := tendsto_pmPowerDampedSecondDensity_second_order.sub tendsto_dampedBezoutLimit_div_sq
  rw [sub_zero] at h
  refine h.congr' (Eventually.of_forall fun ε => ?_)
  simp only [dampedDissipationRate]
  ring

/-- **Neighbour anti-correlation.** `A_ε(1) = -ε² + o(ε²)`. -/
theorem tendsto_dampedAutocorrelation_one_second_order :
    Tendsto (fun ε : ℝ => dampedAutocorrelation ε 1 / ε ^ 2) (𝓝[>] 0) (𝓝 (-1)) := by
  have h := tendsto_pmPowerDampedDivisorVariance_second_order.sub
    tendsto_dampedDissipationRate_second_order
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  rw [dampedDissipationRate_eq_variance_sub_autocorrelation hε]
  ring

/-- **Dissipation exceeds variance by the squared mean.** `(R(ε) - V(ε))/ε² → 1`. -/
theorem tendsto_dampedDissipationRate_sub_variance :
    Tendsto (fun ε : ℝ => (dampedDissipationRate ε - RHTower.pmPowerDampedDivisorVariance ε) / ε ^ 2)
      (𝓝[>] 0) (𝓝 1) := by
  have h := tendsto_dampedDissipationRate_second_order.sub
    tendsto_pmPowerDampedDivisorVariance_second_order
  rw [zero_sub, neg_neg] at h
  refine h.congr' (Eventually.of_forall fun ε => ?_)
  ring

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
