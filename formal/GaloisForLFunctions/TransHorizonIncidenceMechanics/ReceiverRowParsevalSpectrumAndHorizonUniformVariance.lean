import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedPeriodVarianceAndNonCommutingLimits
import GaloisForLFunctions.BezoutValuationIncidence.RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanLogMass

/-!
# The receiver row's Parseval spectrum and its horizon-uniform variance

The Ramanujan coefficients of the damped divisor function are the limits of the Selberg
coordinates of the damped Möbius row:

`Y_N(e; c_ε) = Σ_{e | d ≤ N} μ(d) d^{-1-ε} → w_ε(e) = Σ_{e | d} μ(d) d^{-1-ε}`.

The coordinates are dominated by `e^{-1-ε} ζ(1+ε)`, so the period forms converge term by term and,
with the cofinal Selberg limit `Q_Sel(N; c_ε) → E[τ_ε²]`, give the Parseval identity

`E[τ_ε²] = Σ_e φ(e) w_ε(e)²`,   `V(ε) = Σ_{e ≥ 2} φ(e) w_ε(e)²`.

The PM receiver row `c_Q` at horizon `Q + 1` has Selberg coordinates exactly `w_ε(e)` for
`e ≤ Q + 1`. Its period variance is therefore the partial Parseval sum
`Σ_{2 ≤ e ≤ Q+1} φ(e) w_ε(e)²`: it increases with the cutoff, converges to `V(ε)`, and never
exceeds it. Its dissipation rate `Σ_{2 ≤ e ≤ Q+1} (φ(e) - μ(e)) w_ε(e)²` is at most `2V(ε)`.
Since `V(ε) ~ ε/2`, at every small damping the receiver row stays below the Möbius variance and
dissipation floors `1/288`, `1/576` at every horizon: a horizon-uniform statement.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The real Ramanujan coefficient `w_ε(e)` of the damped divisor function. -/
def dampedRamanujanCoeff (ε : ℝ) (e : ℕ) : ℝ :=
  (RHTower.pmPowerDampedRamanujanWeight ε e).re

theorem abs_pmPowerDampedRealWeight_div_le {ε : ℝ} (d : ℕ) :
    |pmPowerDampedRealWeight ε d / d| ≤ (d : ℝ) ^ (-ε) / d := by
  rw [abs_div, Nat.abs_cast]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg d)
  rw [pmPowerDampedRealWeight, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have : |moebiusReal d| ≤ 1 := by
    unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) d) (-ε)]

/-- `w_ε(e) = Σ_m c_ε(em)/(em)`. -/
theorem hasSum_dampedRamanujanCoeff {ε : ℝ} (hε : 0 < ε) {e : ℕ} (he : 0 < e) :
    HasSum (fun m : ℕ => pmPowerDampedRealWeight ε (e * m) / ((e * m : ℕ) : ℝ))
      (dampedRamanujanCoeff ε e) := by
  set f : ℕ → ℝ := fun m => pmPowerDampedRealWeight ε (e * m) / ((e * m : ℕ) : ℝ)
  have heR : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hs : Summable f := by
    refine Summable.of_norm_bounded (Real.summable_nat_rpow.mpr (by linarith : -1 - ε < -1))
      fun m => ?_
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [f, mul_zero, Nat.cast_zero, div_zero, norm_zero]
      exact Real.rpow_nonneg le_rfl _
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hemR : (0 : ℝ) < ((e * m : ℕ) : ℝ) := by positivity
    rw [Real.norm_eq_abs]
    refine (abs_pmPowerDampedRealWeight_div_le (e * m)).trans ?_
    rw [← Real.rpow_sub_one hemR.ne', show -ε - 1 = -1 - ε by ring]
    push_cast
    rw [Real.mul_rpow (by linarith) hmR.le]
    have h1 : (e : ℝ) ^ (-1 - ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos heR (by linarith)
    have h2 : 0 ≤ (m : ℝ) ^ (-1 - ε) := Real.rpow_nonneg hmR.le _
    nlinarith
  have hterm : ∀ m, RHTower.pmPowerDampedMobiusCoeff ε (e * m) / ((e * m : ℕ) : ℂ) =
      ((f m : ℝ) : ℂ) := fun m => by
    simp only [RHTower.pmPowerDampedMobiusCoeff, f, pmPowerDampedRealWeight, moebiusReal]
    push_cast; rfl
  have hw : RHTower.pmPowerDampedRamanujanWeight ε e = ((∑' m, f m : ℝ) : ℂ) := by
    rw [RHTower.pmPowerDampedRamanujanWeight, Complex.ofReal_tsum]
    exact tsum_congr hterm
  have hval : dampedRamanujanCoeff ε e = ∑' m, f m := by
    rw [dampedRamanujanCoeff, hw, Complex.ofReal_re]
  rw [hval]
  exact hs.hasSum

/-- Selberg coordinates as sums over multiples: `Y_N(e) = Σ_{m ≤ N/e} c(em)/(em)`. -/
private theorem selbergMultiplesCoord_eq_sum_range (N : ℕ) {e : ℕ} (he : 0 < e) (c : ℕ → ℝ)
    (hc0 : c 0 = 0) :
    selbergMultiplesCoord N c e = ∑ m ∈ range (N / e + 1), c (e * m) / ((e * m : ℕ) : ℝ) := by
  have hset : (Icc 1 N).filter (fun d => e ∣ d) = (Icc 1 (N / e)).image (fun m => e * m) := by
    ext d
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, ⟨k, rfl⟩⟩
      refine ⟨k, ⟨?_, (Nat.le_div_iff_mul_le he).mpr (by linarith [mul_comm e k])⟩, rfl⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp at h1
      · exact hk
    · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
      have := (Nat.le_div_iff_mul_le he).mp h2
      exact ⟨⟨by nlinarith, by linarith [mul_comm e m]⟩, dvd_mul_right e m⟩
  unfold selbergMultiplesCoord
  rw [hset, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left he h)]
  have hr : ∀ n : ℕ, range (n + 1) = insert 0 (Icc 1 n) := fun n => by
    ext m; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [hr, sum_insert (by simp)]
  simp [hc0]

/-- **Coordinates converge to Ramanujan coefficients.** `Y_N(e; c_ε) → w_ε(e)`. -/
theorem tendsto_selbergMultiplesCoord_pmPowerDamped {ε : ℝ} (hε : 0 < ε) {e : ℕ} (he : 0 < e) :
    Tendsto (fun N : ℕ => selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e) atTop
      (𝓝 (dampedRamanujanCoeff ε e)) := by
  have h := (hasSum_dampedRamanujanCoeff hε he).tendsto_sum_nat.comp
    (tendsto_atTop_mono (fun N => Nat.le_succ _) (Nat.tendsto_div_const_atTop he.ne') :
      Tendsto (fun N : ℕ => N / e + 1) atTop atTop)
  refine h.congr fun N => ?_
  simp only [Function.comp_apply]
  rw [selbergMultiplesCoord_eq_sum_range N he _ (by simp [pmPowerDampedRealWeight, moebiusReal])]

/-! ### Parseval -/

/-- **Cofinal Parseval limit.** `Q_Sel(N; c_ε) → Σ_e φ(e) w_ε(e)²`. -/
theorem tendsto_selbergTotientDiagonalForm_pmPowerDamped_parseval {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun N : ℕ => selbergTotientDiagonalForm N (pmPowerDampedRealWeight ε)) atTop
      (𝓝 (∑' e : ℕ, (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2)) := by
  set Z := ∑' m : ℕ, (m : ℝ) ^ (-1 - ε)
  set F : ℕ → ℕ → ℝ := fun N e =>
    if e ∈ Icc 1 N then (Nat.totient e : ℝ) * selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e ^ 2
    else 0
  have hfin : ∀ N, selbergTotientDiagonalForm N (pmPowerDampedRealWeight ε) = ∑' e, F N e := by
    intro N
    rw [tsum_eq_sum (s := Icc 1 N) (fun e he => by simp only [F]; rw [if_neg he]),
      selbergTotientDiagonalForm]
    exact sum_congr rfl fun e he => by simp only [F]; rw [if_pos he]
  simp_rw [hfin]
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun e => Z ^ 2 * (e : ℝ) ^ (-1 - 2 * ε))
    ((Real.summable_nat_rpow.mpr (by linarith)).mul_left _) (fun e => ?_) ?_
  · rcases Nat.eq_zero_or_pos e with rfl | he
    · simp [F]
    · refine ((tendsto_selbergMultiplesCoord_pmPowerDamped hε he).pow 2 |>.const_mul _).congr' ?_
      filter_upwards [eventually_ge_atTop e] with N hN
      simp only [F, mem_Icc, show 1 ≤ e from he, hN, and_self, if_true]
  · filter_upwards with N e
    simp only [F]
    split_ifs with he
    · have he0 : 0 < e := (mem_Icc.mp he).1
      have heR : (0 : ℝ) < e := by exact_mod_cast he0
      have hY : |selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e| ≤ (e : ℝ) ^ (-1 - ε) * Z :=
        (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun d _ => abs_pmPowerDampedRealWeight_div_le d).trans
          (sum_multiples_rpow_le hε N e he0))
      have hφ : (Nat.totient e : ℝ) ≤ e := by exact_mod_cast Nat.totient_le e
      have hpow : (e : ℝ) * ((e : ℝ) ^ (-1 - ε)) ^ 2 = (e : ℝ) ^ (-1 - 2 * ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul heR.le, ← Real.rpow_one_add' heR.le
          (by push_cast; linarith)]
        push_cast; ring_nf
      rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast, abs_pow]
      calc (Nat.totient e : ℝ) * |selbergMultiplesCoord N (pmPowerDampedRealWeight ε) e| ^ 2
          ≤ (e : ℝ) * ((e : ℝ) ^ (-1 - ε) * Z) ^ 2 :=
            mul_le_mul hφ (pow_le_pow_left₀ (abs_nonneg _) hY 2) (sq_nonneg _) heR.le
        _ = Z ^ 2 * ((e : ℝ) * ((e : ℝ) ^ (-1 - ε)) ^ 2) := by ring
        _ = Z ^ 2 * (e : ℝ) ^ (-1 - 2 * ε) := by rw [hpow]
    · rw [norm_zero]; positivity

/-- The Parseval series converges. -/
theorem summable_totient_mul_dampedRamanujanCoeff_sq {ε : ℝ} (hε : 0 < ε) :
    Summable (fun e : ℕ => (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2) := by
  refine Summable.of_nonneg_of_le (fun e => by positivity) (fun e => ?_)
    (Real.summable_nat_rpow.mpr (by linarith : -1 - 2 * ε < -1))
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp only [Nat.totient_zero, Nat.cast_zero, zero_mul]
    exact Real.rpow_nonneg le_rfl _
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hw : |dampedRamanujanCoeff ε e| ≤ (e : ℝ) ^ (-1 - ε) := by
    have h := RHTower.norm_pmPowerDampedRamanujanWeight_le hε he
    refine (Complex.abs_re_le_norm _).trans (h.trans_eq ?_)
    rw [one_div, ← Real.rpow_neg heR.le]; ring_nf
  have hφ : (Nat.totient e : ℝ) ≤ e := by exact_mod_cast Nat.totient_le e
  have hpow : (e : ℝ) * ((e : ℝ) ^ (-1 - ε)) ^ 2 = (e : ℝ) ^ (-1 - 2 * ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul heR.le, ← Real.rpow_one_add' heR.le
      (by push_cast; linarith)]
    push_cast; ring_nf
  calc (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2
      ≤ (e : ℝ) * ((e : ℝ) ^ (-1 - ε)) ^ 2 := by
        rw [← sq_abs]
        exact mul_le_mul hφ (pow_le_pow_left₀ (abs_nonneg _) hw 2) (sq_nonneg _) heR.le
    _ = (e : ℝ) ^ (-1 - 2 * ε) := hpow

/-- **Parseval identity for the damped divisor function.** `E[τ_ε²] = Σ_e φ(e) w_ε(e)²`. -/
theorem pmPowerDampedSecondDensity_eq_parseval {ε : ℝ} (hε : 0 < ε) :
    RHTower.pmPowerDampedSecondDensity ε =
      ∑' e : ℕ, (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2 :=
  tendsto_nhds_unique (tendsto_selbergTotientDiagonalForm_pmPowerDamped hε)
    (tendsto_selbergTotientDiagonalForm_pmPowerDamped_parseval hε)

/-- `w_ε(1) = E[τ_ε]`. -/
theorem dampedRamanujanCoeff_one {ε : ℝ} (hε : 0 < ε) :
    dampedRamanujanCoeff ε 1 = (RHTower.pmPowerDampedDivisorDensity ε).re := by
  rw [dampedRamanujanCoeff, RHTower.pmPowerDampedRamanujanWeight_one hε]

/-- **Parseval variance.** `V(ε) = Σ_e φ(e) w_ε(e)² - w_ε(1)²`, the mass of the modes `e ≥ 2`. -/
theorem pmPowerDampedDivisorVariance_eq_parseval {ε : ℝ} (hε : 0 < ε) :
    RHTower.pmPowerDampedDivisorVariance ε =
      (∑' e : ℕ, (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2) - dampedRamanujanCoeff ε 1 ^ 2 := by
  rw [RHTower.pmPowerDampedDivisorVariance, pmPowerDampedSecondDensity_eq_parseval hε,
    dampedRamanujanCoeff_one hε]

/-! ### The receiver row -/

/-- **Receiver-row variance = partial Parseval sum.** At horizon `Q + 1`,
`Cov(0; c_Q) = Σ_{2 ≤ e ≤ Q+1} φ(e) w_ε(e)²`. -/
theorem periodCovariance_cofactor_eq (ε : ℝ) (Q : ℕ) :
    TwoLagSieve.periodCovariance (Q + 1) (pmCofactorDivisorWeight ε Q) 0 =
      ∑ e ∈ Icc 2 (Q + 1), (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2 := by
  rw [periodCovariance_eq_ramanujanLagWeight_diagonal]
  refine sum_congr rfl fun e he => ?_
  have he' : e ∈ Icc 1 (Q + 1) := by simp only [mem_Icc] at he ⊢; omega
  rw [ramanujanLagWeight_zero_left, selbergMultiplesCoord_pmCofactorDivisorWeight_of_mem ε he',
    dampedRamanujanCoeff]

/-- The full Parseval mass splits into the mean square `w_ε(1)²` and the modes `e ≥ 2`. -/
private theorem sum_Icc_one_parseval (ε : ℝ) (Q : ℕ) :
    ∑ e ∈ Icc 1 (Q + 1), (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2 =
      dampedRamanujanCoeff ε 1 ^ 2 +
        ∑ e ∈ Icc 2 (Q + 1), (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2 := by
  have hI : Icc 1 (Q + 1) = insert 1 (Icc 2 (Q + 1)) := by
    ext e; simp only [mem_Icc, mem_insert]; omega
  rw [hI, sum_insert (by simp), Nat.totient_one, Nat.cast_one, one_mul]

/-- **Horizon-uniform variance bound.** The receiver row never exceeds the damped variance:
`Cov_{Q+1}(0; c_Q) ≤ V(ε)` for every cutoff `Q`. -/
theorem periodCovariance_cofactor_le_variance {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    TwoLagSieve.periodCovariance (Q + 1) (pmCofactorDivisorWeight ε Q) 0 ≤
      RHTower.pmPowerDampedDivisorVariance ε := by
  rw [periodCovariance_cofactor_eq, pmPowerDampedDivisorVariance_eq_parseval hε]
  have h := (summable_totient_mul_dampedRamanujanCoeff_sq hε).sum_le_tsum (Icc 1 (Q + 1))
    (fun e _ => by positivity)
  rw [sum_Icc_one_parseval] at h
  linarith

/-- The receiver-row variance increases to `V(ε)` as the cutoff grows. -/
theorem tendsto_periodCovariance_cofactor {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun Q : ℕ => TwoLagSieve.periodCovariance (Q + 1) (pmCofactorDivisorWeight ε Q) 0)
      atTop (𝓝 (RHTower.pmPowerDampedDivisorVariance ε)) := by
  have hs := (summable_totient_mul_dampedRamanujanCoeff_sq hε).hasSum.tendsto_sum_nat
  have h := (hs.comp (tendsto_add_atTop_nat 2)).sub_const (dampedRamanujanCoeff ε 1 ^ 2)
  rw [← pmPowerDampedDivisorVariance_eq_parseval hε] at h
  refine h.congr fun Q => ?_
  simp only [Function.comp_apply]
  rw [periodCovariance_cofactor_eq]
  have hr : range (Q + 2) = insert 0 (Icc 1 (Q + 1)) := by
    ext e; simp only [mem_range, mem_insert, mem_Icc]; omega
  rw [hr, sum_insert (by simp), sum_Icc_one_parseval]
  simp

/-- **Receiver-row dissipation.** `R_{Q+1}(c_Q) = Σ_{2 ≤ e ≤ Q+1} (φ(e) - μ(e)) w_ε(e)² ≤ 2V(ε)`
for every cutoff. -/
theorem sieveSuccessorReserve_cofactor_le {ε : ℝ} (hε : 0 < ε) (Q : ℕ) :
    sieveSuccessorReserve (Q + 1) (pmCofactorDivisorWeight ε Q) ≤
      2 * RHTower.pmPowerDampedDivisorVariance ε := by
  unfold sieveSuccessorReserve
  rw [selbergTotientDiagonalForm_pmCofactorDivisorWeight,
    bezoutCoprimeQuadraticForm_pmCofactorDivisorWeight, ← sum_sub_distrib]
  have hI : Icc 1 (Q + 1) = insert 1 (Icc 2 (Q + 1)) := by
    ext e; simp only [mem_Icc, mem_insert]; omega
  rw [hI, sum_insert (by simp)]
  have h1 : (Nat.totient 1 : ℝ) * (RHTower.pmPowerDampedRamanujanWeight ε 1).re ^ 2 -
      moebiusReal 1 * (RHTower.pmPowerDampedRamanujanWeight ε 1).re ^ 2 = 0 := by
    simp [moebiusReal]
  rw [h1, zero_add]
  have hle : ∑ e ∈ Icc 2 (Q + 1), ((Nat.totient e : ℝ) * (RHTower.pmPowerDampedRamanujanWeight ε e).re ^ 2 -
      moebiusReal e * (RHTower.pmPowerDampedRamanujanWeight ε e).re ^ 2) ≤
      2 * ∑ e ∈ Icc 2 (Q + 1), (Nat.totient e : ℝ) * dampedRamanujanCoeff ε e ^ 2 := by
    rw [mul_sum]
    refine sum_le_sum fun e he => ?_
    have he2 : 2 ≤ e := (mem_Icc.mp he).1
    have hφ : (1 : ℝ) ≤ Nat.totient e := by exact_mod_cast Nat.totient_pos.mpr (by omega)
    have hμ : |moebiusReal e| ≤ 1 := by
      unfold moebiusReal; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hw : 0 ≤ dampedRamanujanCoeff ε e ^ 2 := sq_nonneg _
    simp only [dampedRamanujanCoeff] at hw ⊢
    nlinarith [neg_abs_le (moebiusReal e)]
  rw [← periodCovariance_cofactor_eq] at hle
  linarith [periodCovariance_cofactor_le_variance hε Q]

/-- **The receiver row stays below the Möbius floors at every horizon.** For every small damping,
the receiver row has period variance `< 1/288` and dissipation rate `< 1/576` at **every** cutoff
`Q`, while the Möbius response has variance `≥ 1/288` and dissipation `≥ 1/576` at all large
horizons. -/
theorem eventually_cofactor_below_moebius_floors :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ Q : ℕ,
      TwoLagSieve.periodCovariance (Q + 1) (pmCofactorDivisorWeight ε Q) 0 < 1 / 288 ∧
        sieveSuccessorReserve (Q + 1) (pmCofactorDivisorWeight ε Q) < 1 / 576 := by
  filter_upwards [tendsto_pmPowerDampedDivisorVariance_zero.eventually
      (eventually_lt_nhds (show (0 : ℝ) < 1 / 1153 by norm_num)), self_mem_nhdsWithin]
    with ε hV hε Q
  constructor
  · linarith [periodCovariance_cofactor_le_variance hε Q]
  · linarith [sieveSuccessorReserve_cofactor_le hε Q]

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
