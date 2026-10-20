import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedDiscrepancyEnergyGrowthLaw

/-!
# Spectral escape of the Möbius response, tightness of the damped one

The complete-period variance of a sieve response is its Ramanujan spectrum, the mode masses
`φ(e) Y_N(e)²` on the moduli `2 ≤ e ≤ N`. For the Möbius weight every fixed modulus loses its mass,
`Y_N(e) = μ(e)/e · m_e(N/e) → 0`, while the total mass stays above `1/288`. Hence the Möbius spectrum
**escapes**: for every `E`, eventually all but an arbitrarily small part of the variance sits on moduli
`e > E` — the variance floor is carried by moduli comparable with the horizon.

The damped spectrum is **tight**, uniformly in the horizon: the masses are dominated by
`ζ(1+ε)² e^{-1-2ε}`, so the moduli above `E` carry at most `ζ(1+ε)² ((1+2ε)/(2ε)) E^{-2ε}` at every
horizon. The two rows have opposite spectral geometry: escape to the horizon versus a fixed limit
spectrum (the Parseval spectrum of `τ_ε`).
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- **Escape of every fixed modulus.** For every `E`, the Möbius spectral mass on the moduli `e ≤ E`
tends to zero. -/
theorem tendsto_moebius_low_spectral_mass (E : ℕ) :
    Tendsto (fun N : ℕ => ∑ e ∈ Icc 1 E, (Nat.totient e : ℝ) *
      selbergMultiplesCoord N moebiusReal e ^ 2) atTop (𝓝 0) := by
  rw [show (0 : ℝ) = ∑ e ∈ Icc 1 E, (Nat.totient e : ℝ) * 0 by simp]
  refine tendsto_finsetSum _ fun e he => (Tendsto.const_mul _ ?_)
  have he0 : 0 < e := (mem_Icc.mp he).1
  simp_rw [selbergMultiplesCoord_moebiusReal_sq]
  by_cases hsq : Squarefree e
  · have hm := tendsto_coprimeHarmonicMoebius_prod e.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp)
    rw [Nat.prod_primeFactors_of_squarefree hsq] at hm
    have := ((hm.comp (Nat.tendsto_div_const_atTop he0.ne')).pow 2).const_mul
      (moebiusReal e ^ 2 / (e : ℝ) ^ 2)
    simpa using this
  · simp [moebiusReal_eq_zero_of_not_squarefree e hsq]

/-- **The variance escapes.** For every `E`, at all large horizons the moduli above `E` carry at
least `1/300` of Möbius spectral mass. -/
theorem eventually_moebius_high_spectral_mass_ge (E : ℕ) :
    ∀ᶠ N : ℕ in atTop, (1 : ℝ) / 300 ≤ ∑ e ∈ Icc (E + 1) N, (Nat.totient e : ℝ) *
      selbergMultiplesCoord N moebiusReal e ^ 2 := by
  filter_upwards [eventually_periodCovariance_moebius_zero_ge,
    (tendsto_moebius_low_spectral_mass E).eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 288 - 1 / 300 by norm_num)), eventually_ge_atTop E]
    with N hvar hlow hNE
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal] at hvar
  simp_rw [ramanujanLagWeight_zero_left] at hvar
  -- split `[2, N]` into `[2, E]` and `(E, N]`
  have hsplit : ∑ e ∈ Icc 2 N, (Nat.totient e : ℝ) * selbergMultiplesCoord N moebiusReal e ^ 2 ≤
      ∑ e ∈ Icc 1 E, (Nat.totient e : ℝ) * selbergMultiplesCoord N moebiusReal e ^ 2 +
        ∑ e ∈ Icc (E + 1) N, (Nat.totient e : ℝ) * selbergMultiplesCoord N moebiusReal e ^ 2 := by
    rw [← sum_union (disjoint_left.mpr fun e h1 h2 => by
      simp only [mem_Icc] at h1 h2; omega)]
    exact sum_le_sum_of_subset_of_nonneg (fun e he => by
      simp only [mem_Icc, mem_union] at he ⊢; omega) fun e _ _ => by positivity
  linarith

/-- **Damped tightness.** For `ε > 0`, the damped spectral mass on moduli above `E` is at most
`ζ(1+ε)² ((1+2ε)/(2ε)) E^{-2ε}`, uniformly in the horizon. -/
theorem damped_high_spectral_mass_le {ε : ℝ} (hε : 0 < ε) (E N : ℕ) (hE : 1 ≤ E) :
    ∑ e ∈ Icc (E + 1) N, (Nat.totient e : ℝ) * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2 ≤
      (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 * ((1 + 2 * ε) / (2 * ε) * (E : ℝ) ^ (-(2 * ε))) := by
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  have hmode : ∀ e ∈ Icc (E + 1) N, (Nat.totient e : ℝ) *
      selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2 ≤ Z ^ 2 * (e : ℝ) ^ (-(1 + 2 * ε)) := by
    intro e he
    have he0 : 0 < e := by have := (mem_Icc.mp he).1; omega
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have hY := abs_selbergMultiplesCoord_pmPowerDamped_le hε N he0
    have hφ : (Nat.totient e : ℝ) ≤ e := by exact_mod_cast Nat.totient_le e
    have hpow : (e : ℝ) * ((e : ℝ) ^ (-1 - ε)) ^ 2 = (e : ℝ) ^ (-(1 + 2 * ε)) := by
      rw [← Real.rpow_natCast ((e : ℝ) ^ (-1 - ε)) 2, ← Real.rpow_mul heR.le,
        ← Real.rpow_one_add' heR.le (by push_cast; linarith)]
      push_cast; ring_nf
    calc (Nat.totient e : ℝ) * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2
        ≤ (e : ℝ) * ((e : ℝ) ^ (-1 - ε) * Z) ^ 2 := by
          rw [← sq_abs (selbergMultiplesCoord N _ e)]
          exact mul_le_mul hφ (pow_le_pow_left₀ (abs_nonneg _) hY 2) (sq_nonneg _) heR.le
      _ = Z ^ 2 * ((e : ℝ) * ((e : ℝ) ^ (-1 - ε)) ^ 2) := by ring
      _ = Z ^ 2 * (e : ℝ) ^ (-(1 + 2 * ε)) := by rw [hpow]
  have htail := RHTower.Sieve.sum_rpow_neg_tail_le (c := 1 + 2 * ε) (by linarith)
    (R := E + 1) (N := N) (by omega)
  have hE1 : ((E + 1 : ℕ) : ℝ) ^ (1 - (1 + 2 * ε)) ≤ (E : ℝ) ^ (-(2 * ε)) := by
    rw [show 1 - (1 + 2 * ε) = -(2 * ε) by ring]
    exact Real.rpow_le_rpow_of_nonpos (by exact_mod_cast hE) (by push_cast; linarith) (by linarith)
  calc ∑ e ∈ Icc (E + 1) N, (Nat.totient e : ℝ) *
        selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2
      ≤ ∑ e ∈ Icc (E + 1) N, Z ^ 2 * (e : ℝ) ^ (-(1 + 2 * ε)) := sum_le_sum hmode
    _ = Z ^ 2 * ∑ e ∈ Icc (E + 1) N, (e : ℝ) ^ (-(1 + 2 * ε)) := by rw [mul_sum]
    _ ≤ Z ^ 2 * ((1 + 2 * ε) / (1 + 2 * ε - 1) * ((E + 1 : ℕ) : ℝ) ^ (1 - (1 + 2 * ε))) :=
        mul_le_mul_of_nonneg_left htail (sq_nonneg Z)
    _ ≤ Z ^ 2 * ((1 + 2 * ε) / (2 * ε) * (E : ℝ) ^ (-(2 * ε))) := by
        rw [show 1 + 2 * ε - 1 = 2 * ε by ring]
        gcongr

/-- The damped tail bound vanishes as the cut-off grows: the damped spectrum is tight. -/
theorem tendsto_damped_tail_bound {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun E : ℕ => (∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2 *
      ((1 + 2 * ε) / (2 * ε) * (E : ℝ) ^ (-(2 * ε)))) atTop (𝓝 0) := by
  have h := ((tendsto_rpow_neg_atTop (show 0 < 2 * ε by linarith)).comp
    tendsto_natCast_atTop_atTop).const_mul ((1 + 2 * ε) / (2 * ε))
  have h2 := h.const_mul ((∑' m : ℕ, (m : ℝ) ^ (-1 - ε)) ^ 2)
  simpa using h2

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
