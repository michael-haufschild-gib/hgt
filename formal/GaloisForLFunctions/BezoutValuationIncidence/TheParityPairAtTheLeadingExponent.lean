import GaloisForLFunctions.BezoutValuationIncidence.TheMeanValueIsTheLeadingCoefficientOfTheReceiver
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FirstMomentBlindParityPairOfTheNegatedMoebiusWeight
import GaloisForLFunctions.RHTower.MobiusMertensAbscissaLittlewood
import GaloisForLFunctions.RHTower.MobiusMertensAbsoluteMomentExponentLaw
import GaloisForLFunctions.RHTower.Sieve.SquarefreeGlobalCount

/-!
# The parity pair at the leading exponent

The leading-exponent law `E_T(s)/T^{1-2ε} → Γ_ε L(s)²` (`tendsto_patternReceiver_div_rpow`) reads
the mean value `L(s)` of a sign pattern. On the actual source and its twins, for `0 < ε < 1/2`:

* the Möbius pattern has mean value `0`, so `E_T(μ_ε)/T^{1-2ε} → 0` and `A_{μ_ε}(n)/n^{1-ε} → 0`
  (`tendsto_moebius_receiver_div_rpow`, `tendsto_moebius_prefix_div_rpow`);
* the raw twin `μ²(d) d^{-ε}` has mean value `6/π²`, so `E_T/T^{1-2ε} → Γ_ε (6/π²)²`
  (`tendsto_moebiusSq_receiver_div_rpow`);
* the Ramanujan-isometric twin `c'_ε` grows at the full rate, `E_T(c'_ε) ≥ c T^{1-2ε}` for `T ≥ 200`
  (`exists_parityTwin_receiver_ge_rpow`), so `E_T(μ_ε)/E_T(c'_ε) → 0` at every damping, below the
  Vinogradov–Korobov band included (`tendsto_moebius_div_parityTwin_receiver`);
* the first-moment-blind weight `2ρ_ε δ₁ - μ_ε` shares the twin's first pronic moment and its
  Ramanujan coefficients at prime powers, yet its receiver vanishes at the leading exponent: the
  first pronic moment carries no exponent (`firstPronicMoment_carries_no_exponent`);
* the finite statistic that separates the pair at every cutoff `N` is the cutoff mean of the pattern
  (`parityPair_cutoffMean_separation`).

The next rung is a power rate for the Möbius mean value. It is equivalent to `Θ < 1`
(`zetaZeroAbscissa_lt_one_iff_moebius_rate`) and gives `E_T(μ_ε) ≤ K (1 + T^{1-2ε-γ})` at every
damping (`exists_moebius_receiver_le_of_zetaZeroAbscissa_lt_one`).
-/

open Finset Filter Topology
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. The Möbius pattern -/

/-- The damped Möbius receiver is the receiver of the Möbius pattern. -/
theorem weightPronicEnergy_pmPowerDamped_eq_patternReceiver {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T =
      patternReceiver ε moebiusReal T := by
  rw [patternReceiver, ← dampedDensity_eq_tsum hε]
  rfl

theorem weightCenteredPrefix_pmPowerDamped_eq_patternPrefix {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n =
      patternPrefix ε moebiusReal n := by
  rw [patternPrefix, ← dampedDensity_eq_tsum hε]
  rfl

/-- `exp(-√(log x)/12) → 0`. -/
theorem tendsto_exp_neg_sqrt_log_div : Tendsto (fun x : ℕ =>
    Real.exp (-(Real.sqrt (Real.log x) / 12))) atTop (𝓝 0) :=
  Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).atTop_div_const
      (by norm_num))

/-- **The Möbius pattern has mean value zero**, at the de la Vallée Poussin rate. -/
theorem hasMeanValue_moebiusReal : HasMeanValue moebiusReal 0 := by
  obtain ⟨B, -, N₀, hM⟩ := exists_abs_sum_moebiusReal_le_sqrtLog
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) (eventually_atTop.mpr ⟨max N₀ 1, fun x hx => ?_⟩)
    (by simpa using tendsto_exp_neg_sqrt_log_div.const_mul B))
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (le_max_right N₀ 1).trans hx
  rw [sub_zero, Real.norm_eq_abs, abs_div, abs_of_pos hx0, div_le_iff₀ hx0]
  exact (hM x ((le_max_left N₀ 1).trans hx)).trans (le_of_eq (by ring))

/-- **The Möbius receiver vanishes at the leading exponent**: `E_T(μ_ε)/T^{1-2ε} → 0`. -/
theorem tendsto_moebius_receiver_div_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T /
      (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have h := tendsto_patternReceiver_div_rpow hε hε2 abs_moebiusReal_le_one' hasMeanValue_moebiusReal
  rw [zero_pow two_ne_zero, mul_zero] at h
  simpa only [weightPronicEnergy_pmPowerDamped_eq_patternReceiver hε] using h

/-- The damped Möbius prefix is `o(n^{1-ε})`. -/
theorem tendsto_moebius_prefix_div_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    Tendsto (fun n : ℕ => weightCenteredPrefix (pmPowerDampedRealWeight ε) (dampedDensity ε) n /
      (n : ℝ) ^ (1 - ε)) atTop (𝓝 0) := by
  have h := tendsto_patternPrefix_div_rpow hε hε2 abs_moebiusReal_le_one' hasMeanValue_moebiusReal
  rw [zero_mul] at h
  simpa only [weightCenteredPrefix_pmPowerDamped_eq_patternPrefix hε] using h

/-! ## §2. The first rung: a power rate for the Möbius mean value -/

theorem norm_mobiusMertensPartialSum_eq_abs_sum (N : ℕ) :
    ‖_root_.RHTower.mobiusMertensPartialSum N‖ = |∑ e ∈ Icc 1 N, moebiusReal e| := by
  have h : _root_.RHTower.mobiusMertensPartialSum N =
      ((∑ n ∈ range (N + 1), ((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℝ) : ℂ) := by
    simp only [_root_.RHTower.mobiusMertensPartialSum, _root_.RHTower.mobiusComplexCoefficient,
      Complex.ofReal_sum, Complex.ofReal_intCast]
  rw [h, Complex.norm_real, Real.norm_eq_abs, sum_range_moebius_eq_sum_Icc_moebiusReal]

/-- **A power rate for the Möbius mean value is the quasi-Riemann hypothesis**:
`Θ < 1 ⟺ ∃ β < 1, |M(x)| ≤ C x^β`. -/
theorem zetaZeroAbscissa_lt_one_iff_moebius_rate :
    _root_.RHTower.zetaZeroAbscissa < 1 ↔ ∃ C β : ℝ, 0 ≤ C ∧ 0 ≤ β ∧ β < 1 ∧
      ∀ x : ℕ, 1 ≤ x → |∑ e ∈ Icc 1 x, moebiusReal e| ≤ C * (x : ℝ) ^ β := by
  constructor
  · intro hΘ
    have hΘ0 := _root_.RHTower.half_le_zetaZeroAbscissa
    set β : ℝ := (_root_.RHTower.zetaZeroAbscissa + 1) / 2 with hβ
    have hβ0 : 0 ≤ β := by rw [hβ]; linarith
    have hβ1 : β ≤ 1 := by rw [hβ]; linarith
    obtain ⟨C, hC, hM⟩ := _root_.RHTower.mobiusMertens_subpower_zetaZeroAbscissa
      (β - _root_.RHTower.zetaZeroAbscissa) (by rw [hβ]; linarith)
    refine ⟨2 * C, β, by positivity, hβ0, by rw [hβ]; linarith, fun x hx => ?_⟩
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have h := hM x
    rw [norm_mobiusMertensPartialSum_eq_abs_sum, add_sub_cancel] at h
    have h2 : (2 : ℝ) ^ β ≤ 2 :=
      calc (2 : ℝ) ^ β ≤ 2 ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hβ1
        _ = 2 := Real.rpow_one 2
    calc |∑ e ∈ Icc 1 x, moebiusReal e| ≤ C * ((x : ℝ) + 1) ^ β := h
      _ ≤ C * (2 * (x : ℝ)) ^ β := by gcongr; linarith
      _ = C * (2 ^ β * (x : ℝ) ^ β) := by rw [Real.mul_rpow (by norm_num) (by linarith)]
      _ ≤ C * (2 * (x : ℝ) ^ β) := by gcongr
      _ = 2 * C * (x : ℝ) ^ β := by ring
  · rintro ⟨C, β, hC, hβ0, hβ1, hM⟩
    have hS : ∀ X : ℕ, ∑ k ∈ range (X + 1), ‖_root_.RHTower.mobiusMertensPartialSum k‖ ^ (1 : ℝ) ≤
        C * ((X : ℝ) + 1) ^ (1 + β) := by
      intro X
      calc ∑ k ∈ range (X + 1), ‖_root_.RHTower.mobiusMertensPartialSum k‖ ^ (1 : ℝ)
          ≤ ∑ _k ∈ range (X + 1), C * ((X : ℝ) + 1) ^ β := by
            refine sum_le_sum fun k hk => ?_
            rw [Real.rpow_one, norm_mobiusMertensPartialSum_eq_abs_sum]
            rcases Nat.eq_zero_or_pos k with rfl | hk1
            · rw [Finset.Icc_eq_empty (by norm_num), sum_empty, abs_zero]
              positivity
            · have hkX : (k : ℝ) ≤ (X : ℝ) + 1 := by
                have := mem_range.mp hk
                exact_mod_cast this.le
              calc |∑ e ∈ Icc 1 k, moebiusReal e| ≤ C * (k : ℝ) ^ β := hM k hk1
                _ ≤ C * ((X : ℝ) + 1) ^ β := by gcongr
        _ = C * ((X : ℝ) + 1) ^ (1 + β) := by
            rw [sum_const, card_range, nsmul_eq_mul, Real.rpow_add (by positivity), Real.rpow_one]
            push_cast
            ring
    have h := _root_.RHTower.zetaZeroAbscissa_le_of_sum_norm_mertens_rpow_le le_rfl (by linarith) hS
    linarith

/-- **Quasi-RH gives the power saving at every damping**: `E_T(μ_ε) ≤ K (1 + T^{1-2ε-γ})`. -/
theorem exists_moebius_receiver_le_of_zetaZeroAbscissa_lt_one
    (hΘ : _root_.RHTower.zetaZeroAbscissa < 1) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ K γ : ℝ, 0 ≤ K ∧ 0 < γ ∧ ∀ T : ℕ,
      weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T ≤
        K * (1 + (T : ℝ) ^ (1 - 2 * ε - γ)) := by
  obtain ⟨C, β, hC, hβ0, hβ1, hM⟩ := zetaZeroAbscissa_lt_one_iff_moebius_rate.mp hΘ
  obtain ⟨K, hK0, hK⟩ :=
    exists_patternReceiver_le_of_rate hε hε2 abs_moebiusReal_le_one' hC hβ0 hβ1 hM
  have h1 : 0 < 1 - β := by linarith
  have h2 : 0 < 1 - ε := by linarith
  have h3 : 0 < 2 - β := by linarith
  refine ⟨K, min (2 * (1 - β) * (1 - ε) / (2 - β)) ((1 - 2 * ε) / 2), hK0,
    lt_min (by positivity) (by linarith), fun T => ?_⟩
  rw [weightPronicEnergy_pmPowerDamped_eq_patternReceiver hε]
  exact hK T

/-! ## §3. The raw twin `μ²(d) d^{-ε}` -/

/-- The squarefree pattern `μ²`. -/
def moebiusSqPattern (d : ℕ) : ℝ := ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ 2

theorem abs_moebiusSqPattern_le_one (d : ℕ) : |moebiusSqPattern d| ≤ 1 := by
  unfold moebiusSqPattern
  have h : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  rw [abs_pow]
  nlinarith [abs_nonneg ((ArithmeticFunction.moebius d : ℤ) : ℝ)]

/-- **The squarefree pattern has mean value `6/π²`.** -/
theorem hasMeanValue_moebiusSqPattern :
    HasMeanValue moebiusSqPattern _root_.RHTower.Sieve.squarefreeDensity := by
  have hdecay : Tendsto (fun m : ℕ => 3 * (m : ℝ) ^ (-(1 / 2 : ℝ))) atTop (𝓝 0) := by
    simpa using ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul 3
  refine tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) (eventually_atTop.mpr ⟨1, fun m hm => ?_⟩) hdecay)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have h := _root_.RHTower.Sieve.abs_sum_moebius_sq_Icc_sub_le m
  have hkey : 2 * Real.sqrt m + 1 ≤ 3 * (m : ℝ) ^ (-(1 / 2 : ℝ)) * m := by
    have h1 : (m : ℝ) ^ (-(1 / 2 : ℝ)) * m = Real.sqrt m := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hm0.ne']
      norm_num
    have h2 : 1 ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm1
    nlinarith
  rw [Real.norm_eq_abs, show (∑ e ∈ Icc 1 m, moebiusSqPattern e) / m -
      _root_.RHTower.Sieve.squarefreeDensity = (∑ n ∈ Icc 1 m,
        ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ (2 : ℕ) -
          m * _root_.RHTower.Sieve.squarefreeDensity) / m by
    unfold moebiusSqPattern; field_simp, abs_div, abs_of_pos hm0, div_le_iff₀ hm0]
  linarith

/-- **The raw twin carries the full leading coefficient**: `E_T(μ²_ε)/T^{1-2ε} → Γ_ε (6/π²)²`. -/
theorem tendsto_moebiusSq_receiver_div_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => patternReceiver ε moebiusSqPattern T / (T : ℝ) ^ (1 - 2 * ε)) atTop
      (𝓝 (receiverLeadingCoeff ε * (6 / Real.pi ^ 2) ^ 2)) := by
  rw [← _root_.RHTower.Sieve.squarefreeDensity_eq]
  exact tendsto_patternReceiver_div_rpow hε hε2 abs_moebiusSqPattern_le_one
    hasMeanValue_moebiusSqPattern

/-! ## §4. The Ramanujan-isometric twin -/

/-- **The parity twin grows at the full rate**: `E_T(c'_ε) ≥ c T^{1-2ε}` for `T ≥ 200`, from the
drift `A_{c'}(n) ≤ -n Σ_{(n,2n]} c'(d)/d ≤ -K n (2n)^{-ε}`. -/
theorem exists_parityTwin_receiver_ge_rpow {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2) :
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 200 ≤ T →
      c * (T : ℝ) ^ (1 - 2 * ε) ≤ weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T := by
  set K := dampedDensity ε / parityTwinCoprimeMass ε 1 / 16 with hK
  have hK0 : 0 < K := by
    have := div_pos (_root_.RHTower.pmPowerDampedDivisorDensity_re_pos hε)
      (parityTwinCoprimeMass_one_pos hε)
    positivity
  have h2ε : (1 / 2 : ℝ) ≤ (2 : ℝ) ^ (-(2 * ε)) :=
    calc (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; norm_num
      _ ≤ 2 ^ (-(2 * ε)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  -- cells beyond `100` are at least `K²/4 · n^{-2ε}`
  have hcell : ∀ n : ℕ, 100 ≤ n → K ^ 2 / 4 * (n : ℝ) ^ (-(2 * ε)) ≤
      weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hA := weightCenteredPrefix_le_neg_drift (parityTwinWeight_nonneg hε)
      (hasSum_parityTwinWeight_div hε) n
    have hd := parityTwin_drift_ge hε hn
    set A := weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n
    have hP : 0 ≤ K * n * (2 * (n : ℝ)) ^ (-ε) := by positivity
    have hA' : A ≤ -(K * n * (2 * (n : ℝ)) ^ (-ε)) := by rw [hK]; linarith
    have hsq : (K * n * (2 * (n : ℝ)) ^ (-ε)) ^ 2 ≤ A ^ 2 := by nlinarith
    have hpow : ((2 * (n : ℝ)) ^ (-ε)) ^ 2 = (2 : ℝ) ^ (-(2 * ε)) * (n : ℝ) ^ (-(2 * ε)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.mul_rpow (by norm_num)
        hn0.le]
      push_cast
      ring_nf
    have hnp : 0 ≤ (n : ℝ) ^ (-(2 * ε)) := by positivity
    have hnn : (n : ℝ) * ((n : ℝ) + 1) ≤ 2 * (n : ℝ) ^ 2 := by nlinarith
    rw [le_div_iff₀ (by positivity)]
    calc K ^ 2 / 4 * (n : ℝ) ^ (-(2 * ε)) * ((n : ℝ) * ((n : ℝ) + 1))
        ≤ K ^ 2 / 4 * (n : ℝ) ^ (-(2 * ε)) * (2 * (n : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left hnn (by positivity)
      _ = K ^ 2 * (n : ℝ) ^ 2 * (1 / 2 * (n : ℝ) ^ (-(2 * ε))) := by ring
      _ ≤ K ^ 2 * (n : ℝ) ^ 2 * ((2 : ℝ) ^ (-(2 * ε)) * (n : ℝ) ^ (-(2 * ε))) := by gcongr
      _ = (K * n * (2 * (n : ℝ)) ^ (-ε)) ^ 2 := by rw [mul_pow, mul_pow, hpow]
      _ ≤ A ^ 2 := hsq
  refine ⟨K ^ 2 / 8, by positivity, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by exact_mod_cast (by omega : 0 < T)
  have hsub : Ioc (T / 2) T ⊆ Icc 1 T := fun n hn => by
    simp only [mem_Ioc, mem_Icc] at hn ⊢; omega
  have hcard : (T : ℝ) / 2 ≤ ((Ioc (T / 2) T).card : ℝ) := by
    rw [Nat.card_Ioc, Nat.cast_sub (Nat.div_le_self T 2)]
    have : ((T / 2 : ℕ) : ℝ) ≤ (T : ℝ) / 2 := Nat.cast_div_le
    linarith
  have hTp : 0 ≤ K ^ 2 / 4 * (T : ℝ) ^ (-(2 * ε)) := by positivity
  calc K ^ 2 / 8 * (T : ℝ) ^ (1 - 2 * ε)
      = (T : ℝ) / 2 * (K ^ 2 / 4 * (T : ℝ) ^ (-(2 * ε))) := by
        rw [show (1 : ℝ) - 2 * ε = 1 + -(2 * ε) by ring, Real.rpow_add hT0, Real.rpow_one]
        ring
    _ ≤ ((Ioc (T / 2) T).card : ℝ) * (K ^ 2 / 4 * (T : ℝ) ^ (-(2 * ε))) := by gcongr
    _ = ∑ _n ∈ Ioc (T / 2) T, K ^ 2 / 4 * (T : ℝ) ^ (-(2 * ε)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ Ioc (T / 2) T, weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) := by
        refine sum_le_sum fun n hn => ?_
        have hn' := mem_Ioc.mp hn
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
        have hTn : (T : ℝ) ^ (-(2 * ε)) ≤ (n : ℝ) ^ (-(2 * ε)) :=
          Real.rpow_le_rpow_of_nonpos hn0 (by exact_mod_cast hn'.2) (by linarith)
        refine le_trans ?_ (hcell n (by omega))
        exact mul_le_mul_of_nonneg_left hTn (by positivity)
    _ ≤ ∑ n ∈ Icc 1 T, weightCenteredPrefix (parityTwinWeight ε) (dampedDensity ε) n ^ 2 /
          ((n : ℝ) * ((n : ℝ) + 1)) :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => by positivity
    _ = weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T := rfl

/-- **The pair is separated at the leading exponent below the band**: at every damping
`0 < ε < 1/2`, `E_T(μ_ε)/E_T(c'_ε) → 0`. -/
theorem tendsto_moebius_div_parityTwin_receiver {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T /
      weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T) atTop (𝓝 0) := by
  obtain ⟨c, hc, hge⟩ := exists_parityTwin_receiver_ge_rpow hε hε2.le
  have hμ := (tendsto_moebius_receiver_div_rpow hε hε2).div_const c
  rw [zero_div] at hμ
  refine squeeze_zero' (Eventually.of_forall fun T => div_nonneg (weightPronicEnergy_nonneg' _ _ _)
    (weightPronicEnergy_nonneg' _ _ _)) (eventually_atTop.mpr ⟨200, fun T hT => ?_⟩) hμ
  have hp : 0 < (T : ℝ) ^ (1 - 2 * ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast (by omega : 0 < T)) _
  have hcp : 0 < c * (T : ℝ) ^ (1 - 2 * ε) := mul_pos hc hp
  calc weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T /
        weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T
      ≤ weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T /
          (c * (T : ℝ) ^ (1 - 2 * ε)) :=
        div_le_div_of_nonneg_left (weightPronicEnergy_nonneg' _ _ _) hcp (hge T hT)
    _ = weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T /
          (T : ℝ) ^ (1 - 2 * ε) / c := by
        rw [div_div, mul_comm]

/-! ## §5. The first pronic moment carries no exponent -/

/-- **The first pronic moment carries no exponent.** The weight `2ρ_ε δ₁ - μ_ε` and the parity twin
have the same first pronic moment, the same Ramanujan coefficients at every prime power and equal
amplitudes, while the first receiver vanishes at the leading exponent and the second grows at the
full rate `T^{1-2ε}`. -/
theorem firstPronicMoment_carries_no_exponent {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    firstPronicMoment (negatedMoebiusWeight ε) = firstPronicMoment (parityTwinWeight ε) ∧
    (∀ e : ℕ, IsPrimePow e → weightRamanujanCoeff (negatedMoebiusWeight ε) e =
      weightRamanujanCoeff (parityTwinWeight ε) e) ∧
    (∀ e : ℕ, |weightRamanujanCoeff (negatedMoebiusWeight ε) e| =
      |weightRamanujanCoeff (parityTwinWeight ε) e|) ∧
    Tendsto (fun T : ℕ => weightPronicEnergy (negatedMoebiusWeight ε) (dampedDensity ε) T /
      (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 200 ≤ T →
      c * (T : ℝ) ^ (1 - 2 * ε) ≤ weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T := by
  obtain ⟨habs, hpp, hfm, -, hE, -⟩ := firstMomentBlind_parityPair hε hε2.le
  refine ⟨hfm, hpp, habs, ?_, exists_parityTwin_receiver_ge_rpow hε hε2.le⟩
  simpa only [hE] using tendsto_moebius_receiver_div_rpow hε hε2

/-! ## §6. The finite statistic: the cutoff mean -/

/-- **The cutoff mean separates the pair at every cutoff.** For the Möbius pattern
`|S_μ(N)/N| ≤ B e^{-√(log N)/12}`; for the twin pattern `c'_ε(d) d^ε ≥ (ρ_ε/U_ε) μ²(d)` the cutoff
mean is at least `(ρ_ε/U_ε)(6/π² - (2√N + 1)/N)`. -/
theorem parityPair_cutoffMean_separation {ε : ℝ} (hε : 0 < ε) :
    (∃ B : ℝ, 0 ≤ B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N →
      |(∑ e ∈ Icc 1 N, moebiusReal e) / N| ≤ B * Real.exp (-(Real.sqrt (Real.log N) / 12))) ∧
    ∀ N : ℕ, 1 ≤ N → dampedDensity ε / parityTwinCoprimeMass ε 1 *
        (_root_.RHTower.Sieve.squarefreeDensity - (2 * Real.sqrt N + 1) / N) ≤
      (∑ d ∈ Icc 1 N, parityTwinWeight ε d * (d : ℝ) ^ ε) / N := by
  constructor
  · obtain ⟨B, hB, N₀, hM⟩ := exists_abs_sum_moebiusReal_le_sqrtLog
    refine ⟨B, hB, N₀, fun N hN hN1 => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    exact (hM N hN).trans (le_of_eq (by ring))
  · intro N hN1
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    set κ := dampedDensity ε / parityTwinCoprimeMass ε 1 with hκ
    have hκ0 : 0 ≤ κ := (div_pos (_root_.RHTower.pmPowerDampedDivisorDensity_re_pos hε)
      (parityTwinCoprimeMass_one_pos hε)).le
    have hpt : ∀ d ∈ Icc 1 N, κ * ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ (2 : ℕ) ≤
        parityTwinWeight ε d * (d : ℝ) ^ ε := by
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Icc.mp hd).1
      by_cases hsq : Squarefree d
      · have h := parityTwinWeight_ge hε hsq
        have hμ : ((ArithmeticFunction.moebius d : ℤ) : ℝ) ^ (2 : ℕ) ≤ 1 := by
          have := abs_moebiusSqPattern_le_one d
          unfold moebiusSqPattern at this
          exact (le_abs_self _).trans this
        have hcancel : (d : ℝ) ^ (-ε) * (d : ℝ) ^ ε = 1 := by
          rw [← Real.rpow_add hd0, neg_add_cancel, Real.rpow_zero]
        have hprod := mul_le_mul_of_nonneg_right h (Real.rpow_nonneg hd0.le ε)
        rw [mul_assoc, hcancel, mul_one] at hprod
        nlinarith
      · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
        simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
        exact mul_nonneg (parityTwinWeight_nonneg hε d) (Real.rpow_nonneg hd0.le ε)
    have hsum : κ * ∑ n ∈ Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ (2 : ℕ) ≤
        ∑ d ∈ Icc 1 N, parityTwinWeight ε d * (d : ℝ) ^ ε := by
      rw [mul_sum]; exact sum_le_sum hpt
    have hcount := _root_.RHTower.Sieve.abs_sum_moebius_sq_Icc_sub_le N
    have hlow : (N : ℝ) * _root_.RHTower.Sieve.squarefreeDensity - (2 * Real.sqrt N + 1) ≤
        ∑ n ∈ Icc 1 N, ((ArithmeticFunction.moebius n : ℤ) : ℝ) ^ (2 : ℕ) := by
      linarith [(abs_le.mp hcount).1]
    rw [le_div_iff₀ hN0]
    have hexp : κ * (_root_.RHTower.Sieve.squarefreeDensity - (2 * Real.sqrt N + 1) / N) * N =
        κ * ((N : ℝ) * _root_.RHTower.Sieve.squarefreeDensity - (2 * Real.sqrt N + 1)) := by
      field_simp
    rw [hexp]
    nlinarith

/-! ## §7. The pair at the leading exponent -/

/-- **The parity pair at the leading exponent.** At every damping `0 < ε < 1/2`: the Möbius receiver
is `o(T^{1-2ε})`; the raw twin has leading coefficient `Γ_ε (6/π²)² > 0`; the Ramanujan twin grows
at the full rate; and the ratio of the Möbius and twin receivers tends to `0`. -/
theorem parityPair_at_the_leading_exponent {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    Tendsto (fun T : ℕ => weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T /
        (T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) ∧
    Tendsto (fun T : ℕ => patternReceiver ε moebiusSqPattern T / (T : ℝ) ^ (1 - 2 * ε)) atTop
        (𝓝 (receiverLeadingCoeff ε * (6 / Real.pi ^ 2) ^ 2)) ∧
    0 < receiverLeadingCoeff ε * (6 / Real.pi ^ 2) ^ 2 ∧
    (∃ c : ℝ, 0 < c ∧ ∀ T : ℕ, 200 ≤ T →
      c * (T : ℝ) ^ (1 - 2 * ε) ≤ weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T) ∧
    Tendsto (fun T : ℕ => weightPronicEnergy (pmPowerDampedRealWeight ε) (dampedDensity ε) T /
        weightPronicEnergy (parityTwinWeight ε) (dampedDensity ε) T) atTop (𝓝 0) :=
  ⟨tendsto_moebius_receiver_div_rpow hε hε2, tendsto_moebiusSq_receiver_div_rpow hε hε2,
    mul_pos (receiverLeadingCoeff_pos hε hε2) (by positivity),
    exists_parityTwin_receiver_ge_rpow hε hε2.le, tendsto_moebius_div_parityTwin_receiver hε hε2⟩

end

end GaloisForLFunctions.BezoutValuationIncidence
