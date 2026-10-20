import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedVarianceAndDissipationSecondOrderLaw
import GaloisForLFunctions.BezoutValuationIncidence.HardyLittlewoodSingularSeriesOfTheDampedSource
import GaloisForLFunctions.BezoutValuationIncidence.BarbanVehovMollifierKloostermanGcdAndLogEnergyWallOneBridge
import GaloisForLFunctions.RHTower.Sieve.CoprimeLogMoebiusLimit
import GaloisForLFunctions.RHTower.Sieve.SquarefreeTotientLogMean

/-!
# Period correlations of the Selberg row are the singular series

The Selberg (Barban–Vehov) row at its own horizon, `ℓ_N(d) = μ(d) log(N/d)` for `d ≤ N`, has the
response `s_N(k; ℓ_N) = Σ_{d ∣ k, d ≤ N} μ(d) log(N/d)`, Selberg's truncated von Mangoldt function.
It is the `ε`-tangent of the Möbius identity: `Σ_{d ∣ k} μ(d) log(1/d) = Λ(k)`. Its Selberg
coordinates are coprime logarithmic Möbius sums,

`Y_N(e) = μ(e) T_e(N/e)/e`,  `|T_e| ≤ A e/φ(e)` uniformly,  `T_e(Y) → e/φ(e)`,

so `Y_N(e) → μ(e)/φ(e)` with the summable domination `|c_e(h)| Y_N(e)² ≤ σ(h) A² μ(e)²/φ(e)²`.
The Ramanujan diagonalisation of the complete-period covariance then gives, for every lag `h ≥ 1`,

`Cov_N(h; ℓ_N) → 𝔖(h) - 1`,  `H_N(ℓ_N) → 1`,

the Hardy–Littlewood singular series `𝔖(h) = Σ_q μ(q)² c_q(h)/φ(q)²`, while the variance `Cov_N(0; ℓ_N) = Σ φ(e) Y_N(e)²` diverges,
since its modes tend to `μ(e)²/φ(e)`. So the Selberg row sees prime-pair correlations on the
period torus, unlike the literal Möbius row whose lag covariances all vanish. Its normalised
correlations still tend to zero. The limit is the second-order law of the damped row: the Haar
limit `lim_{ε→0} A_ε(h)/ε²` (the damped source carries `𝔖(h)` at scale `ρ_ε² ∼ ε²`) and the
horizon limit of the Selberg tangent row agree at every lag.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open RHTower.Sieve (barbanVehovWeight coprimeLogMoebius coprimeLogMoebiusConst sqfreeTotientInv)

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

private theorem moebiusReal_sq_of_squarefree' {e : ℕ} (hsq : Squarefree e) :
    moebiusReal e ^ 2 = 1 := by
  unfold moebiusReal
  have h1 : |((ArithmeticFunction.moebius e : ℤ) : ℝ)| = 1 := by
    exact_mod_cast abs_moebius_eq_one_of_squarefree hsq
  rw [← sq_abs, h1]; norm_num

/-- `Y_N(e; ℓ_N) = μ(e) T_e(N/e)/e`. -/
theorem selbergMultiplesCoord_barbanVehov_eq {N e : ℕ} (he : 0 < e) :
    selbergMultiplesCoord N (barbanVehovWeight N) e =
      moebiusReal e / e * coprimeLogMoebius e ((N : ℝ) / e) := by
  unfold selbergMultiplesCoord
  exact RHTower.Sieve.barbanVehov_inner_eq he le_rfl

/-- **Mode limits.** `Y_N(e; ℓ_N) → μ(e)/φ(e)` for every `e ≥ 1`. -/
theorem tendsto_selbergMultiplesCoord_barbanVehov {e : ℕ} (he : 0 < e) :
    Tendsto (fun N : ℕ => selbergMultiplesCoord N (barbanVehovWeight N) e) atTop
      (𝓝 (moebiusReal e / (Nat.totient e : ℝ))) := by
  simp_rw [selbergMultiplesCoord_barbanVehov_eq he]
  by_cases hsq : Squarefree e
  · have hdiv : Tendsto (fun N : ℕ => (N : ℝ) / e) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_div_const (by exact_mod_cast he)
    have h := ((RHTower.Sieve.tendsto_coprimeLogMoebius_squarefree e hsq).comp hdiv).const_mul
      (moebiusReal e / e)
    have heR : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have hval : moebiusReal e / e * ((e : ℝ) / (Nat.totient e : ℝ)) =
        moebiusReal e / (Nat.totient e : ℝ) := by
      field_simp
    rw [hval] at h
    exact h
  · simp [moebiusReal_eq_zero_of_not_squarefree e hsq]

/-- **Harmonic mean.** `H_N(ℓ_N) = T_1(N) → 1`. -/
theorem tendsto_finiteHarmonicSum_barbanVehov :
    Tendsto (fun N : ℕ => finiteHarmonicSum N (barbanVehovWeight N)) atTop (𝓝 1) := by
  have h := tendsto_selbergMultiplesCoord_barbanVehov (e := 1) one_pos
  simp only [moebiusReal, ArithmeticFunction.moebius_apply_one, Int.cast_one, Nat.totient_one,
    Nat.cast_one, div_one] at h
  refine h.congr fun N => ?_
  unfold selbergMultiplesCoord finiteHarmonicSum
  simp

/-- `Y_N(e; ℓ_N)² ≤ A² μ(e)²/φ(e)²`. -/
private theorem selbergMultiplesCoord_barbanVehov_sq_le (N : ℕ) {e : ℕ} (he : 0 < e) :
    selbergMultiplesCoord N (barbanVehovWeight N) e ^ 2 ≤
      coprimeLogMoebiusConst ^ 2 * (sqfreeTotientInv e / (Nat.totient e : ℝ)) := by
  by_cases hsq : Squarefree e
  · have hb := BezoutValuationIncidence.abs_selbergMultiplesCoord_barbanVehovWeight_le he
      (le_refl N)
    have hφ : (0 : ℝ) < Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr he
    rw [RHTower.Sieve.sqfreeTotientInv_apply, if_pos hsq, ← sq_abs]
    calc |selbergMultiplesCoord N (barbanVehovWeight N) e| ^ 2
        ≤ (coprimeLogMoebiusConst / (Nat.totient e : ℝ)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hb 2
      _ = _ := by field_simp
  · rw [selbergMultiplesCoord_barbanVehov_eq he, moebiusReal_eq_zero_of_not_squarefree e hsq]
    simp only [zero_div, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (sq_nonneg _) (div_nonneg (RHTower.Sieve.sqfreeTotientInv_nonneg e)
      (Nat.cast_nonneg _))

/-- The limiting mode mass is the singular-series term: `c_e(h) (μ(e)/φ(e))² = c_e(h) μ(e)²/φ(e)²`. -/
private theorem lag_mode_limit_eq (h e : ℕ) :
    ramanujanLagWeight h e * (moebiusReal e / (Nat.totient e : ℝ)) ^ 2 = singularSeriesTerm h e := by
  unfold singularSeriesTerm
  congr 1
  rw [RHTower.Sieve.sqfreeTotientInv_apply]
  split_ifs with hsq
  · rw [div_pow, moebiusReal_sq_of_squarefree' hsq]; ring
  · rw [moebiusReal_eq_zero_of_not_squarefree e hsq]; simp

/-- **The singular-series law of the Selberg row.** For every lag `h ≥ 1`,
`Cov_N(h; ℓ_N) → 𝔖(h) - 1`. -/
theorem tendsto_periodCovariance_barbanVehov {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N (barbanVehovWeight N) h) atTop
      (𝓝 (hardyLittlewoodSingularSeries h - 1)) := by
  set g : ℕ → ℕ → ℝ := fun N e => if e ∈ Icc 2 N then
    ramanujanLagWeight h e * selbergMultiplesCoord N (barbanVehovWeight N) e ^ 2 else 0
  have hrepr : ∀ N : ℕ, TwoLagSieve.periodCovariance N (barbanVehovWeight N) h = ∑' e, g N e := by
    intro N
    rw [periodCovariance_eq_ramanujanLagWeight_diagonal, tsum_eq_sum (s := Icc 2 N)]
    · exact sum_congr rfl fun e he => by simp only [g, if_pos he]
    · intro e he; simp only [g, if_neg he]
  simp_rw [hrepr]
  rw [← (hasSum_singularSeriesTerm_ge_two hh).tsum_eq]
  have hσ0 : 0 ≤ ∑ d ∈ h.divisors, (d : ℝ) := sum_nonneg fun d _ => Nat.cast_nonneg d
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun e => (∑ d ∈ h.divisors, (d : ℝ)) *
      (coprimeLogMoebiusConst ^ 2 * (sqfreeTotientInv e / (Nat.totient e : ℝ))))
    ((summable_sqfreeTotientInv_div_totient.1.mul_left _).mul_left _) (fun e => ?_) ?_
  · by_cases he2 : 2 ≤ e
    · rw [if_pos he2, ← lag_mode_limit_eq]
      refine (((tendsto_selbergMultiplesCoord_barbanVehov (e := e) (by omega)).pow 2).const_mul
        (ramanujanLagWeight h e)).congr' ?_
      filter_upwards [eventually_ge_atTop e] with N hN
      simp only [g, if_pos (mem_Icc.mpr ⟨he2, hN⟩)]
    · rw [if_neg he2]
      refine tendsto_const_nhds.congr fun N => ?_
      simp only [g, mem_Icc, he2, false_and, if_false]
  · refine Eventually.of_forall fun N e => ?_
    simp only [g]
    split_ifs with he
    · have he0 : 0 < e := by have := (mem_Icc.mp he).1; omega
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sq_nonneg (selbergMultiplesCoord N (barbanVehovWeight N) e))]
      exact mul_le_mul (abs_ramanujanLagWeight_le_sigma hh e)
        (selbergMultiplesCoord_barbanVehov_sq_le N he0) (sq_nonneg _) hσ0
    · rw [norm_zero]
      exact mul_nonneg hσ0 (mul_nonneg (sq_nonneg _) (div_nonneg
        (RHTower.Sieve.sqfreeTotientInv_nonneg e) (Nat.cast_nonneg _)))

/-- **Uncentred period correlation.** `H_N(ℓ_N)² + Cov_N(h; ℓ_N) → 𝔖(h)` for every lag `h ≥ 1`. -/
theorem tendsto_periodCorrelation_barbanVehov {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => finiteHarmonicSum N (barbanVehovWeight N) ^ 2 +
      TwoLagSieve.periodCovariance N (barbanVehovWeight N) h) atTop
      (𝓝 (hardyLittlewoodSingularSeries h)) := by
  have h' := (tendsto_finiteHarmonicSum_barbanVehov.pow 2).add (tendsto_periodCovariance_barbanVehov hh)
  rwa [one_pow, add_sub_cancel] at h'

/-- **Odd lags.** `Cov_N(h; ℓ_N) → -1` for every odd `h`. -/
theorem tendsto_periodCovariance_barbanVehov_odd {h : ℕ} (hh : ¬ 2 ∣ h) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N (barbanVehovWeight N) h) atTop (𝓝 (-1)) := by
  have h1 : 1 ≤ h := Nat.pos_of_ne_zero (by rintro rfl; simp at hh)
  have := tendsto_periodCovariance_barbanVehov h1
  rwa [hardyLittlewoodSingularSeries_eq_zero_of_odd h1 hh, zero_sub] at this

/-- **Divergent variance.** `Cov_N(0; ℓ_N) → ∞`: the modes tend to `μ(e)²/φ(e)`, whose sum diverges. -/
theorem tendsto_periodCovariance_barbanVehov_zero :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N (barbanVehovWeight N) 0) atTop atTop := by
  -- the reciprocal-totient mass `Σ_{e ≤ E} μ(e)²/φ(e)` is unbounded
  have hmass : Tendsto (fun E : ℕ => ∑ e ∈ Icc 1 E, sqfreeTotientInv e) atTop atTop := by
    have hlog : Tendsto (fun E : ℕ => Real.log E) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    refine (Tendsto.pos_mul_atTop one_pos RHTower.Sieve.tendsto_sum_sqfreeTotientInv_div_log_one
      hlog).congr' ?_
    filter_upwards [eventually_ge_atTop 2] with E hE
    have : 0 < Real.log E := Real.log_pos (by exact_mod_cast hE)
    field_simp
  refine tendsto_atTop.mpr fun B => ?_
  obtain ⟨E, hE, hE1⟩ := ((tendsto_atTop.mp hmass (B + 2)).and (eventually_ge_atTop 1)).exists
  have hsplit : ∑ e ∈ Icc 1 E, sqfreeTotientInv e = sqfreeTotientInv 1 + ∑ e ∈ Icc 2 E,
      sqfreeTotientInv e := by
    rw [← Finset.add_sum_Ioc_eq_sum_Icc hE1]; rfl
  have h1 : sqfreeTotientInv 1 = 1 := by simp [RHTower.Sieve.sqfreeTotientInv_apply]
  have hfin : Tendsto (fun N : ℕ => ∑ e ∈ Icc 2 E,
      (Nat.totient e : ℝ) * selbergMultiplesCoord N (barbanVehovWeight N) e ^ 2) atTop
      (𝓝 (∑ e ∈ Icc 2 E, sqfreeTotientInv e)) := by
    refine tendsto_finsetSum _ fun e he => ?_
    have he0 : 0 < e := by have := (mem_Icc.mp he).1; omega
    have h := ((tendsto_selbergMultiplesCoord_barbanVehov he0).pow 2).const_mul (Nat.totient e : ℝ)
    have hφ : (Nat.totient e : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.mpr he0).ne'
    have hval : (Nat.totient e : ℝ) * (moebiusReal e / (Nat.totient e : ℝ)) ^ 2 = sqfreeTotientInv e := by
      rw [RHTower.Sieve.sqfreeTotientInv_apply]
      split_ifs with hsq
      · rw [div_pow, moebiusReal_sq_of_squarefree' hsq]; field_simp
      · rw [moebiusReal_eq_zero_of_not_squarefree e hsq]; simp
    rwa [hval] at h
  filter_upwards [hfin.eventually (eventually_gt_nhds (show B < ∑ e ∈ Icc 2 E, sqfreeTotientInv e
    by linarith)), eventually_ge_atTop E] with N hN hNE
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal]
  simp_rw [ramanujanLagWeight_zero_left]
  refine hN.le.trans (sum_le_sum_of_subset_of_nonneg (fun e he => ?_) fun e _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  simp only [mem_Icc] at he ⊢; omega

/-- **Normalised whiteness.** `Cov_N(h; ℓ_N)/Cov_N(0; ℓ_N) → 0` for every lag `h ≥ 1`. -/
theorem tendsto_periodCorrelation_barbanVehov_normalised {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N (barbanVehovWeight N) h /
      TwoLagSieve.periodCovariance N (barbanVehovWeight N) 0) atTop (𝓝 0) :=
  (tendsto_periodCovariance_barbanVehov hh).div_atTop tendsto_periodCovariance_barbanVehov_zero

/-- **The two tangents agree.** At every lag `h ≥ 1` the horizon limit of the Selberg row and the
second-order Haar limit of the damped row, `A_ε(h)/ε² → 𝔖(h) - 1`, have the same value. -/
theorem selberg_and_damped_tangent_correlations_agree {h : ℕ} (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => TwoLagSieve.periodCovariance N (barbanVehovWeight N) h) atTop
        (𝓝 (hardyLittlewoodSingularSeries h - 1)) ∧
      Tendsto (fun ε : ℝ => dampedAutocorrelation ε h / ε ^ 2) (𝓝[>] 0)
        (𝓝 (hardyLittlewoodSingularSeries h - 1)) := by
  refine ⟨tendsto_periodCovariance_barbanVehov hh, ?_⟩
  have hA := (tendsto_dampedAutocorrelation_div_density_sq hh).mul
    (RHTower.tendsto_pmPowerDampedDivisorDensity_re_div_parameter.pow 2)
  rw [one_pow, mul_one] at hA
  refine hA.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hρ := RHTower.pmPowerDampedDivisorDensity_re_pos (show (0 : ℝ) < ε from hε)
  have hε0 : ε ≠ 0 := ne_of_gt hε
  field_simp

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
