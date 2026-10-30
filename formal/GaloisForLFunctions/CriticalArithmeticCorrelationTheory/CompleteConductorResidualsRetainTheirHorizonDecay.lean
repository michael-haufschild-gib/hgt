import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UpwardPrimeErrorsRetainTheirHorizonDecay
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeilReplacementErrorsHavePolynomialCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorQuasimodesAreUniformOnBoundedOverlap
import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticResidualBudgetIsUniformInTheHorizon

/-!
# Horizon decay of the complete conductor residual

The exact signed source identity combines a uniform harmonic square budget
with the inverse-horizon kernel error. Each replacement retains its actual
rate before the complete residual is estimated.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell

private theorem norm_add_sq_le_two {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
  nlinarith only [h, sq_nonneg (‖a‖ - ‖b‖)]

private theorem norm_four_sq_le {E : Type*} [SeminormedAddCommGroup E] (a b c d : E) :
    ‖a + b + c + d‖ ^ 2 ≤ 4 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2 + ‖d‖ ^ 2) := by
  have h := norm_add_sq_le_two (a + b) (c + d)
  rw [← add_assoc] at h
  linarith only [h, norm_add_sq_le_two a b, norm_add_sq_le_two c d]

private theorem norm_eight_signed_sq_le {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z u : E) :
    ‖-p + s + c - x + q + (y + z) - u‖ ^ 2 ≤
      8 * (‖p‖ ^ 2 + ‖s‖ ^ 2 + ‖c‖ ^ 2 + ‖x‖ ^ 2 +
        ‖q‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖u‖ ^ 2) := by
  have hid : -p + s + c - x + q + (y + z) - u =
      (-p + s + c + -x) + (q + y + z + -u) := by abel
  rw [hid]
  have h := norm_add_sq_le_two (-p + s + c + -x) (q + y + z + -u)
  have h1 := norm_four_sq_le (-p) s c (-x)
  have h2 := norm_four_sq_le q y z (-u)
  rw [norm_neg, norm_neg] at h1
  rw [norm_neg] at h2
  linarith only [h, h1, h2]

/-- The existing horizon-uniform arithmetic budget gives a normalized prime-residual rate. -/
private theorem exists_primeResidual_norm_sq_log_bound {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        C / Real.log N := by
  obtain ⟨B, hB, hbound⟩ := SignedArithmeticHodgeTheory.exists_uniform_ramanujanPrimeResidual_family_bound
  let mpos : ℕ+ := ⟨m, hm⟩
  let C := B * SignedArithmeticHodgeTheory.ramanujanResidualConductorCost m ^ 2
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro N
  have hraw := hbound {mpos} (fun _ => 1) N
  simp only [sum_singleton, one_mul, one_pow, mul_one] at hraw
  have hraw' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (ramanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • ramanujanHorizonVector m N‖ ^ 2 ≤ C := by
    rw [ramanujanHorizonVector_residual_norm_sq]
    exact hraw
  simp only [normalizedRamanujanHorizonVector, map_smul]
  rw [smul_comm (Real.log N - ramanujanAdjunctionEnergy m) (Real.sqrt (Real.log N))⁻¹,
    ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
    Real.sq_sqrt (Real.log_natCast_nonneg N)]
  have h := div_le_div_of_nonneg_right hraw' (Real.log_natCast_nonneg N)
  simpa only [div_eq_mul_inv, mul_comm] using h


private theorem lower_power_rate_le {C c L N : ℝ} (hC : 0 ≤ C) (hc : 1 ≤ c) (hL : 0 ≤ L)
    {k : ℕ} (hk : k ≤ 5) :
    C * c ^ k / L ≤ C * (c ^ 5 / L + c ^ 10 * (L / N) ^ 2) := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  calc
    _ ≤ C * c ^ 5 / L := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc hk) hC) hL
    _ = C * (c ^ 5 / L) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity)) hC

/-- Every term in the actual complete residual retains its quantitative horizon decay. -/
theorem exists_completeWeil_completedConductor_residual_horizon_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        K * (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_norm_sq_log_bound hm
  obtain ⟨Cs, hCs, hs⟩ := exists_completeWeilSelfError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cc, hCc, hcenter⟩ := exists_fullWeilCenter_norm_sq_polynomial_bound φ hm
  obtain ⟨Cx, hCx, hx⟩ := exists_separatedCrossError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cq, hCq, hq⟩ := exists_fullWeilPoleError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cd, hCd, hdown⟩ := exists_fullNearGammaDownward_norm_sq_polynomial_bound hφ hsupp hM m
  obtain ⟨Cn, hCn, hnear⟩ := exists_nearCenterVector_norm_sq_polynomial_bound hM hm
  obtain ⟨Cu, hCu, hup⟩ := exists_normalizedUpwardPrimeResidual_horizon_harmonic_bound hφ hsupp hM hm
  let A := (Real.sqrt (m.totient : ℝ))⁻¹ ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  let K := 8 * (Cp + Cs + Cc + Cx + Cq + A * Cd + Cn + A * Cu) + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨K, hK, ?_⟩
  filter_upwards [hs, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hs hN hlog
  intro c hc hlarge
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
  let R := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hthree : 3 * c ≤ (N : ℝ) := by
    have he := Real.exp_pos 1
    have hcoef : 3 ≤ 4 * (Real.exp 1 + 3) ^ 2 := by nlinarith only [he]
    have hc2 : c ≤ c ^ 2 := by nlinarith only [hc]
    have h := mul_le_mul_of_nonneg_right hcoef (sq_nonneg c)
    nlinarith only [h, hc2, hlarge]
  have hcN : c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have htwo : 2 * c ≤ (N : ℝ) := by linarith only [hthree, hc0]
  have hw : c / N ≤ 1 / 3 := by
    rw [div_le_iff₀ hN0]
    linarith only [hthree]
  have hp' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cp * R := by
    have h := lower_power_rate_le (N := (N : ℝ)) hCp hc hL0.le (k := 0) (by norm_num)
    simp only [pow_zero, mul_one] at h
    exact (hp N).trans h
  have hs' : ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cs * R := by
    have hc210 : c ^ 2 ≤ c ^ 10 := pow_le_pow_right₀ hc (by norm_num)
    have hL2 : 1 ≤ Real.log (N : ℝ) ^ 2 := one_le_pow₀ hlog
    have hscale := mul_le_mul_of_nonneg_left hL2 (pow_nonneg hc0.le 10)
    have hnum : Cs * c ^ 2 ≤ Cs * (c ^ 10 * Real.log (N : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left (hc210.trans (by simpa only [mul_one] using hscale)) hCs
    calc
      _ ≤ Cs * c ^ 2 / (N : ℝ) ^ 2 := hs c hc0 hcN
      _ ≤ (Cs * (c ^ 10 * Real.log (N : ℝ) ^ 2)) / (N : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ = Cs * (c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by rw [div_pow]; ring
      _ ≤ Cs * R := mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left (by positivity : 0 ≤ c ^ 5 / Real.log N)) hCs
  have hc' := (hcenter c N).trans (lower_power_rate_le (N := (N : ℝ)) hCc hc hL0.le (by norm_num : 2 ≤ 5))
  have hx' := (hx c hc0 N hN).trans (lower_power_rate_le (N := (N : ℝ)) hCx hc hL0.le (by norm_num : 4 ≤ 5))
  have hq' := (hq c hc0 N hN hcN).trans (lower_power_rate_le (N := (N : ℝ)) hCq hc hL0.le (by norm_num : 4 ≤ 5))
  have hn' := (hnear c hc N hN htwo).trans (lower_power_rate_le (N := (N : ℝ)) hCn hc hL0.le (by norm_num : 5 ≤ 5))
  have hd' : ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      (A * Cd) * R := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h := (hdown c hc N hN hw).trans
      (lower_power_rate_le (N := (N : ℝ)) hCd hc hL0.le (by norm_num : 5 ≤ 5))
    exact (mul_le_mul_of_nonneg_left h hA).trans_eq (by dsimp only [R]; ring)
  have hu' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      (A * Cu) * R := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_left (hup N hN hlog c hc hlarge) hA).trans_eq
      (by dsimp only [R]; ring)
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN hm]
  have hsum := norm_eight_signed_sq_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  have hbound := hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hp' hs') hc') hx') hq') hd') hn') hu')
    (by norm_num : (0 : ℝ) ≤ 8))
  change _ ≤ K * R
  calc
    _ ≤ 8 * (Cp * R + Cs * R + Cc * R + Cx * R + Cq * R +
        (A * Cd) * R + Cn * R + (A * Cu) * R) := hbound
    _ = (8 * (Cp + Cs + Cc + Cx + Cq + A * Cd + Cn + A * Cu)) * R := by ring
    _ ≤ K * R := mul_le_mul_of_nonneg_right (by dsimp only [K]; linarith only) hR

/-- The explicit tilted spline satisfies the complete two-rate residual bound. -/
theorem exists_tiltedUnitSpline_completedConductor_residual_horizon_bound {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        K * (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) :=
  exists_completeWeil_completedConductor_residual_horizon_bound contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_completedConductor_residual_horizon_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completedConductor_residual_horizon_bound
