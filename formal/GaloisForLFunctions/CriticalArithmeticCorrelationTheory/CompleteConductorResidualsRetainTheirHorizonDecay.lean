import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.OneHorizonMakesTheCompleteWeilMatrixPositiveThroughTouching
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilReserveHasAnExplicitTouchingHorizon
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.UpwardPrimeErrorsRetainTheirHorizonDecay
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeilReplacementErrorsHavePolynomialCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorQuasimodesAreUniformOnBoundedOverlap
import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticResidualBudgetIsUniformInTheHorizon
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.RamanujanFamiliesHaveExplicitCoordinateMass
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NegativeWeilPacketsHaveExponentialConductorCutoffs
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapConductorFloor

/-!
# Horizon decay of the complete conductor residual

The exact signed source identity combines a uniform harmonic square budget
with the inverse-horizon kernel error. Each replacement retains its actual
rate before the complete residual is estimated.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace
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

/-- A periodic coefficient bound controls the normalized mode at every logarithmic horizon. -/
theorem normalizedRamanujanHorizonVector_norm_sq_le_period_bound
    {m N : ℕ} (hm : 0 < m) (hlog : 1 ≤ Real.log N) :
    ‖normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      2 * (∑ j ∈ range m, |normalizedRamanujanMode m j|) ^ 2 := by
  let A := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  have hL : 0 < Real.log N := zero_lt_one.trans_le hlog
  have hraw : ‖ramanujanHorizonVector m N‖ ^ 2 ≤ A ^ 2 * (1 + Real.log N) := by
    rw [ramanujanHorizonVector_norm_sq]
    calc
      _ ≤ ∑ n ∈ Icc 1 N, A ^ 2 * (1 / (n : ℝ)) := by
        apply sum_le_sum
        intro n hn
        rw [ramanujanPoleProfile, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        have h := mul_self_le_mul_self (abs_nonneg (normalizedRamanujanMode m n))
          (abs_normalizedRamanujanMode_le hm n)
        rw [← sq, sq_abs, ← sq] at h
        simpa only [div_eq_mul_inv, one_mul] using
          div_le_div_of_nonneg_right h (Nat.cast_nonneg n)
      _ = A ^ 2 * ∑ n ∈ Icc 1 N, 1 / (n : ℝ) := (mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (_root_.RHTower.Sieve.sum_Icc_one_div_le_one_add_log N) (sq_nonneg A)
  calc
    _ = ‖ramanujanHorizonVector m N‖ ^ 2 / Real.log N := by
      rw [normalizedRamanujanHorizonVector, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs, inv_pow, Real.sq_sqrt hL.le]
      ring
    _ ≤ A ^ 2 * (1 + Real.log N) / Real.log N :=
      div_le_div_of_nonneg_right hraw hL.le
    _ ≤ 2 * A ^ 2 := by
      rw [div_le_iff₀ hL]
      nlinarith only [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr hlog)]

/-- The self replacement has no conductor-dependent waiting horizon. -/
theorem exists_completeWeilSelfError_norm_sq_explicit_horizon_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log N →
      ∀ c : ℝ, 0 < c → c ≤ (N : ℝ) →
        ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          C * c ^ 2 / (N : ℝ) ^ 2 := by
  let A := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  let B : ℝ := Real.exp (1 / 2) / 2
  refine ⟨2 * A ^ 2 * B ^ 2, by positivity, ?_⟩
  intro N hN hlog c hc hcN
  have hv := normalizedRamanujanHorizonVector_norm_sq_le_period_bound hm hlog
  have hs := abs_completeWeilSelfError_le_of_width_le_one hφ hsupp hM hc hN hcN
  have hsq := mul_self_le_mul_self (abs_nonneg _) hs
  rw [← sq, sq_abs, ← sq] at hsq
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  calc
    _ ≤ (B * (c / N)) ^ 2 * (2 * A ^ 2) :=
      mul_le_mul hsq hv (sq_nonneg _) (sq_nonneg _)
    _ = _ := by ring

/-- Every complete residual term has a stated horizon, with no eventual qualification. -/
theorem exists_completeWeil_completedConductor_residual_explicit_horizon_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 1 ≤ N → 1 ≤ Real.log N → ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        K * (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_norm_sq_log_bound hm
  obtain ⟨Cs, hCs, hs⟩ := exists_completeWeilSelfError_norm_sq_explicit_horizon_bound hφ hsupp hM hm
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
  refine ⟨K, hK, ?_⟩
  intro N hN hlog c hc hlarge
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
      _ ≤ Cs * c ^ 2 / (N : ℝ) ^ 2 := hs N hN hlog c hc0 hcN
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

/-- The eventual formulation follows from the explicit logarithmic horizon. -/
theorem exists_completeWeil_completedConductor_residual_horizon_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        K * (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) := by
  obtain ⟨K, hK, h⟩ :=
    exists_completeWeil_completedConductor_residual_explicit_horizon_bound hφ hsupp hM hm
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact ⟨K, hK, (eventually_ge_atTop 1).and
    (hloglim.eventually_ge_atTop 1) |>.mono fun N hN => h N hN.1 hN.2⟩

/-- The explicit tilted spline satisfies the complete two-rate residual bound. -/
theorem exists_tiltedUnitSpline_completedConductor_residual_horizon_bound {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        K * (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2) :=
  exists_completeWeil_completedConductor_residual_horizon_bound contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hm

private theorem log_div_sq_le_inv_log {t : ℝ} (ht : 0 < t) (hlog : 0 < Real.log t) :
    (Real.log t / t) ^ 2 ≤ 1 / Real.log t := by
  have h := Real.pow_div_factorial_le_exp (2 * Real.log t) (by positivity) 3
  have he : Real.exp (2 * Real.log t) = t ^ 2 := by
    rw [two_mul, Real.exp_add, Real.exp_log ht]
    ring
  rw [he] at h
  norm_num only [Nat.factorial, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] at h
  have hc : Real.log t ^ 3 ≤ t ^ 2 := by
    nlinarith only [h, pow_nonneg hlog.le 3]
  rw [div_pow, div_le_div_iff₀ (sq_pos_of_pos ht) hlog]
  nlinarith only [hc]

/-- The actual Fourier-tail floor, independent of conductor. -/
def tiltedSplineConductorTailFloor (c : ℝ) : ℝ :=
  2 / (∫ u, tiltedUnitSpline u ^ 2) *
    ∫ t in Set.Ioi c, shellSpectrum tiltedUnitSpline t

theorem tiltedSplineConductorTailFloor_pos (c : ℝ) : 0 < tiltedSplineConductorTailFloor c :=
  mul_pos (div_pos zero_lt_two integral_tiltedUnitSpline_sq_pos)
    (integral_shellSpectrum_tiltedUnitSpline_pos c)

private theorem eigenvector_coordinate_sq_le_residual
    {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}
    (hA : A.IsHermitian) (i : I) (hi : hA.eigenvalues i ≤ 0)
    {e E : ℝ} (he : 0 < e) (hE : e ≤ E) (v : EuclideanSpace ℝ I) :
    ⟪hA.eigenvectorBasis i, v⟫ ^ 2 ≤
      ‖Matrix.toEuclideanLin A v - E • v‖ ^ 2 / e ^ 2 := by
  let x := hA.eigenvectorBasis i
  have hx : ‖x‖ = 1 := by
    have h : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith only [h, norm_nonneg x]
  have hAx : Matrix.toEuclideanLin A x = hA.eigenvalues i • x := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  have hr : ⟪Matrix.toEuclideanLin A v - E • v, x⟫ =
      (hA.eigenvalues i - E) * ⟪x, v⟫ := by
    rw [inner_sub_left, (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA) v x,
      hAx, real_inner_smul_right, real_inner_smul_left, real_inner_comm v x]
    ring
  have hcs := norm_inner_le_norm (𝕜 := ℝ) (Matrix.toEuclideanLin A v - E • v) x
  rw [Real.norm_eq_abs, hx, mul_one, hr] at hcs
  have hsq := mul_self_le_mul_self (abs_nonneg _) hcs
  rw [← sq, sq_abs, ← sq, mul_pow] at hsq
  have hgap : e ^ 2 ≤ (hA.eigenvalues i - E) ^ 2 := by
    have h := mul_self_le_mul_self he.le
      (show e ≤ E - hA.eigenvalues i by linarith only [hE, hi])
    nlinarith only [h]
  apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
  have h := mul_le_mul_of_nonneg_right hgap (sq_nonneg ⟪x, v⟫)
  nlinarith only [h, hsq]

/-- A finite set of explicit horizon inequalities makes the actual complete matrix
positive definite. The cutoff and residual constants come from proved source bounds. -/
theorem exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_horizon :
    ∃ C D H : ℝ, 0 < C ∧ 0 < D ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∃ Q : ℕ, ∃ B : ℝ,
        2 ≤ Q ∧ (Q : ℝ) ≤ Real.exp (D * (C * c ^ 16 + 1)) + 2 ∧ 0 < B ∧
        ∀ N : ℕ, Q ^ 4 ≤ N → H * c ^ 8 ≤ (N : ℝ) →
          4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
          max 1 (36 * B * (c ^ 5 + c ^ 10) / tiltedSplineConductorTailFloor c ^ 2) ≤
            Real.log N → (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  classical
  obtain ⟨C, D, H, hC, hD, hH, hcut⟩ :=
    exists_negative_completeWeil_exponential_conductor_cutoff (by norm_num : (0 : ℝ) < 1 / 4)
  choose K hK hres using fun m : ℕ =>
    exists_completeWeil_completedConductor_residual_explicit_horizon_bound
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      (Nat.succ_pos m)
  refine ⟨C, D, H, hC, hD, hH, fun c hc => ?_⟩
  obtain ⟨R, hR, happ⟩ := hcut c hc
  let Q := R + 2
  let B := (∑ m ∈ Icc 1 Q, K (m - 1)) + 1
  have hQ : 2 ≤ Q := by omega
  have hB : 0 < B := by
    have h := sum_nonneg (s := Icc 1 Q) fun m _ => (hK (m - 1)).le
    dsimp only [B]
    linarith only [h]
  refine ⟨Q, B, hQ, ?_, hB, fun N hQN hHN hlarge hlog => ?_⟩
  · dsimp only [Q]
    push_cast
    linarith only [hR]
  have hN : 1 ≤ N := (by omega : 1 ≤ Q).trans
    ((Nat.le_self_pow (by norm_num : 4 ≠ 0) Q).trans hQN)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hL1 : 1 ≤ Real.log N := (le_max_left _ _).trans hlog
  have hL : 0 < Real.log N := zero_lt_one.trans_le hL1
  have he := tiltedSplineConductorTailFloor_pos c
  have hrate : c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 ≤
      (c ^ 5 + c ^ 10) / Real.log N := by
    have h := mul_le_mul_of_nonneg_left (log_div_sq_le_inv_log hNR hL)
      (pow_nonneg (zero_le_one.trans hc) 10)
    rw [add_div]
    rw [mul_one_div] at h
    exact add_le_add_right h _
  apply (completeWeilMatrix_isHermitian tiltedUnitSpline c N).posDef_iff_eigenvalues_pos.mpr
  intro i
  by_contra hi
  have hi0 : (completeWeilMatrix_isHermitian tiltedUnitSpline c N).eigenvalues i ≤ 0 :=
    le_of_not_gt hi
  let hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  let x := hA.eigenvectorBasis i
  have hx : ‖x‖ = 1 := by
    have h : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith only [h, norm_nonneg x]
  have henergy : completeWeilEnergy tiltedUnitSpline c N x ≤ 0 := by
    have hAx : Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x =
        hA.eigenvalues i • x := by
      ext j
      exact congrFun (hA.mulVec_eigenvectorBasis i) j
    change ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x, x⟫ ≤ 0
    rw [hAx, real_inner_smul_left, real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
    exact hi0
  obtain ⟨a, ha⟩ := happ N hHN x hx henergy
  have hmass := normalizedRamanujan_coordinate_mass_ge_of_raw_approximation
    (by omega : R ≤ Q) hQ hQN x hx a ha
  have hterm (m : ℕ) (hm : m ∈ Icc 1 Q) :
      ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤
        K (m - 1) * ((c ^ 5 + c ^ 10) / Real.log N) /
          tiltedSplineConductorTailFloor c ^ 2 := by
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hfloor := completedConductorEnergy_ge_shellTail contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos (zero_lt_one.trans_le hc) hm0
    have hcoord := eigenvector_coordinate_sq_le_residual hA i hi0 he hfloor
      (normalizedRamanujanHorizonVector m N)
    have hr := hres (m - 1) N hN hL1 c hc hlarge
    rw [show (m - 1).succ = m by omega] at hr
    exact hcoord.trans (div_le_div_of_nonneg_right
      (hr.trans (mul_le_mul_of_nonneg_left hrate (hK (m - 1)).le)) (sq_nonneg _))
  have hsum := sum_le_sum hterm
  simp only [← sum_div, ← sum_mul] at hsum
  have hsumB : (∑ m ∈ Icc 1 Q, K (m - 1)) ≤ B := by dsimp only [B]; linarith only
  have hupper : (∑ m ∈ Icc 1 Q, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2) ≤
      B * ((c ^ 5 + c ^ 10) / Real.log N) / tiltedSplineConductorTailFloor c ^ 2 :=
    hsum.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hsumB (by positivity)) (sq_nonneg _))
  have hbudget : B * ((c ^ 5 + c ^ 10) / Real.log N) /
      tiltedSplineConductorTailFloor c ^ 2 ≤ 1 / 36 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos he)).mp ((le_max_right _ _).trans hlog)
    rw [div_le_iff₀ (sq_pos_of_pos he)]
    rw [← mul_div_assoc, div_le_iff₀ hL]
    nlinarith only [hh]
  linarith only [hmass, hupper.trans hbudget]


private theorem completeWeil_ramanujan_touching_residual_eq {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {N : ℕ} (hN : 1 ≤ N) (m : ℕ) :
    Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N =
    -(Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) +
      completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N +
      (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
          (normalizedRamanujanHorizonVector m N) -
        (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N) -
      Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) +
      Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (normalizedRamanujanHorizonVector m N) := by
  have hone : Matrix.toEuclideanLin
      (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (normalizedRamanujanHorizonVector m N) = normalizedRamanujanHorizonVector m N := by
    ext i
    change (Matrix.mulVec (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ)
      (fun j => normalizedRamanujanHorizonVector m N j)) i = normalizedRamanujanHorizonVector m N i
    rw [Matrix.one_mulVec]
  have h := congrArg
    (fun A : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ =>
      Matrix.toEuclideanLin A (normalizedRamanujanHorizonVector m N))
    (completeWeilMatrix_eq_decomposition_at_touching hφ hsupp hM hc0 hc1 hN)
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, hone] at h
  rw [h]
  simp only [completeWeilAdjunctionEnergy]
  module

private theorem exists_touching_crossError_norm_sq_log_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ c : ℝ, 0 < c → c ≤ 1 →
      ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
        (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ C / Real.log N := by
  obtain ⟨C, hC, hb⟩ := exists_uniform_crossError_poleResidual_at_touching hφ hsupp hM
  let A : ℝ := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  have hA : 0 ≤ A := sum_nonneg fun j _ => abs_nonneg _
  refine ⟨(36 * C * A) ^ 2, sq_nonneg _, fun N hN c hc0 hc1 => ?_⟩
  have hraw : ‖Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N)
      (ramanujanHorizonVector m N)‖ ^ 2 ≤ (36 * C * A) ^ 2 := by
    change ‖Matrix.toEuclideanLin
      (horizonKernelMatrix (atomCrossErrorKernel (atomDilate φ (c / N))) N)
      (horizonProfileVector (ramanujanPoleProfile m) N)‖ ^ 2 ≤ _
    rw [horizonKernelMatrix_profile_norm_sq]
    have h := hb c hc0 hc1 N hN (normalizedRamanujanMode m) A hA
      (fun j _ => abs_normalizedRamanujanMode_le hm j)
    have hcSq : c ^ 2 ≤ 1 := by
      simpa only [← pow_two, one_pow] using mul_le_mul hc1 hc1 hc0.le zero_le_one
    have hle : 36 * C * A * c ^ 2 ≤ 36 * C * A :=
      (mul_le_mul_of_nonneg_left hcSq (by positivity)).trans_eq (mul_one _)
    have hs := mul_self_le_mul_self (by positivity : 0 ≤ 36 * C * A * c ^ 2) hle
    exact h.trans (by simpa only [← sq] using hs)
  rw [normalizedRamanujanHorizonVector, map_smul, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  simpa only [div_eq_mul_inv, mul_comm] using
    div_le_div_of_nonneg_right hraw (Real.log_natCast_nonneg N)

/-- Every normalized conductor residual decays at the explicit rate `K/log N`,
uniformly through touching, once `N≥2` and `log N≥1`. -/
theorem exists_completeWeil_touching_residual_explicit_horizon_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 2 ≤ N → 1 ≤ Real.log N →
      ∀ c : ℝ, 0 < c → c ≤ 1 →
        ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
          completeWeilAdjunctionEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
            K / Real.log N := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_norm_sq_log_bound hm
  obtain ⟨Cs, hCs, hs⟩ := exists_completeWeilSelfError_norm_sq_explicit_horizon_bound hφ hsupp hM hm
  obtain ⟨Cc, hCc, hc⟩ := exists_fullWeilCenter_norm_sq_polynomial_bound φ hm
  obtain ⟨Cx, hCx, hx⟩ := exists_touching_crossError_norm_sq_log_bound hφ hsupp hM hm
  obtain ⟨Cq, hCq, hq⟩ := exists_fullWeilPoleError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨D, hD, hnon⟩ := exists_fullWeilNonRatioMatrix_explicit_action_bound hφ hsupp hM
  let A := ∑ j ∈ range m, |normalizedRamanujanMode m j|
  let Cn := 8 * A ^ 2 * D ^ 2
  let K := 8 * (Cp + Cs + Cc + Cx + Cq + Cn) + 1
  have hCn : 0 ≤ Cn := by dsimp only [Cn]; positivity
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun N hN hlog c hc0 hc1 => ?_⟩
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hNR
  have hL : 0 < Real.log N := zero_lt_one.trans_le hlog
  have hc2 : c ^ 2 ≤ 1 := by
    simpa only [← pow_two, one_pow] using mul_le_mul hc1 hc1 hc0.le zero_le_one
  have hc4 : c ^ 4 ≤ 1 := by
    have h := pow_le_pow_left₀ (sq_nonneg c) hc2 2
    simpa only [← pow_mul, one_pow] using h
  have hcN : c ≤ (N : ℝ) := hc1.trans hNR
  have hs' : ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cs / Real.log N := by
    have hLN : Real.log N ≤ (N : ℝ) ^ 2 := by
      have h := Real.log_le_sub_one_of_pos hN0
      nlinarith only [h, hNR]
    exact (hs N hN1 hlog c hc0 hcN).trans
      ((div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc2 hCs) (sq_nonneg _)).trans
        (div_le_div_of_nonneg_left hCs hL hLN))
  have hc' := (hc c N).trans (div_le_div_of_nonneg_right
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc2 hCc) hL.le)
  have hq' := (hq c hc0 N hN1 hcN).trans (div_le_div_of_nonneg_right
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hc4 hCq) hL.le)
  have hn' : ‖Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N)
      (normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤ Cn / Real.log N := by
    have hv := normalizedRamanujanHorizonVector_norm_sq_le_period_bound hm hlog
    have hsucc : Real.log (N + 1 : ℕ) ≤ 2 * Real.log N := by
      have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
      have h := Real.log_le_log (show (0 : ℝ) < (N + 1 : ℕ) by positivity)
        (show ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 by push_cast; nlinarith only [hn2])
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hscale : D * Real.log (N + 1 : ℕ) / N ≤ 2 * D * (Real.log (N : ℝ) / N) := by
      calc
        _ ≤ D * (2 * Real.log N) / N :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsucc hD.le) hN0.le
        _ = _ := by ring
    have hact := (hnon c hc0 hc1 N hN (normalizedRamanujanHorizonVector m N)).trans
      (mul_le_mul_of_nonneg_right hscale (norm_nonneg _))
    have hsq := mul_self_le_mul_self (norm_nonneg _) hact
    rw [← sq, ← sq, mul_pow] at hsq
    have hnorm := mul_le_mul_of_nonneg_left hv (sq_nonneg (2 * D * (Real.log (N : ℝ) / N)))
    have hrate := mul_le_mul_of_nonneg_left (log_div_sq_le_inv_log hN0 hL) hCn
    calc
      _ ≤ (2 * D * (Real.log (N : ℝ) / N)) ^ 2 * (2 * A ^ 2) := hsq.trans hnorm
      _ = Cn * (Real.log (N : ℝ) / N) ^ 2 := by dsimp only [Cn]; ring
      _ ≤ Cn / Real.log N := by simpa only [mul_one_div] using hrate
  rw [completeWeil_ramanujan_touching_residual_eq hφ hsupp hM hc0 hc1 hN1 m]
  have hsum := norm_eight_signed_sq_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    0 0
    (Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) (normalizedRamanujanHorizonVector m N))
  simp only [add_zero, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hsum
  have hbound := hsum.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (hp N) hs') hc')
      (hx N hN1 c hc0 hc1)) hq') hn') (by norm_num : (0 : ℝ) ≤ 8))
  calc
    _ ≤ 8 * (Cp / Real.log N + Cs / Real.log N + Cc / Real.log N +
      Cx / Real.log N + Cq / Real.log N + Cn / Real.log N) := hbound
    _ = (8 * (Cp + Cs + Cc + Cx + Cq + Cn)) / Real.log N := by ring
    _ ≤ K / Real.log N := div_le_div_of_nonneg_right
      (by dsimp only [K]; linarith only) hL.le

private theorem touching_conductor_floor {c : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1)
    {m : ℕ} (hm : 0 < m) :
    tiltedSplineConductorTailFloor 1 ≤ completeWeilAdjunctionEnergy tiltedUnitSpline c m := by
  have hcorr : shellCorrection tiltedUnitSpline 1 1 = 0 := by
    simp only [shellCorrection, Nat.ceil_one, Ico_self, sum_empty, mul_zero]
  have he := completedConductorEnergy_ge_shellTail contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    (c := 1) (m := 1) zero_lt_one zero_lt_one
  have hshape : completedConductorEnergy tiltedUnitSpline 1 1 =
      bumpRobin tiltedUnitSpline 1 / (∫ u, tiltedUnitSpline u ^ 2) +
        completeWeilPoleShift tiltedUnitSpline 1 - Real.log (2 * Real.pi) := by
    rw [completedConductorEnergy_eq_sub_shellCorrection zero_lt_one zero_lt_one, hcorr, sub_zero,
      completeWeilAdjunctionEnergy, SelectiveMultiscaleArithmeticPositivity.ramanujanAdjunctionEnergy_one,
      if_pos rfl, completeWeilSelfFinitePart, mul_one,
      Real.log_div one_ne_zero (by positivity), Real.log_one]
    ring
  rw [hshape] at he
  have hone := he.trans (completed_shape_le_completeWeilAdjunctionEnergy_one
    contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
    hc0 hc1)
  by_cases hm1 : m = 1
  · simpa only [hm1, tiltedSplineConductorTailFloor] using hone
  · exact hone.trans (completeWeilAdjunctionEnergy_one_lt_at_touching
      contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      hc0 hc1 (by omega : 2 ≤ m)).le

/-- One stated fourth-power and logarithmic horizon makes the complete tilted-spline
matrix positive definite simultaneously at every overlap in `(0,1]`. -/
theorem exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_through_touching :
    ∃ Q : ℕ, ∃ B : ℝ, 2 ≤ Q ∧ 0 < B ∧
      ∀ N : ℕ, Q ^ 4 ≤ N →
        max 1 (36 * B / tiltedSplineConductorTailFloor 1 ^ 2) ≤ Real.log N →
        ∀ c : ℝ, 0 < c → c ≤ 1 → (completeWeilMatrix tiltedUnitSpline c N).PosDef := by
  classical
  obtain ⟨C, D, R, hC, hD, hR, hcut⟩ :=
    exists_negative_completeWeil_conductor_cutoff_explicit_through_touching
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      (by norm_num : (0 : ℝ) < 1 / 4)
  choose K hK hres using fun m : ℕ => exists_completeWeil_touching_residual_explicit_horizon_bound
    contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos (Nat.succ_pos m)
  let Q := R + 2
  let B := (∑ m ∈ Icc 1 Q, K (m - 1)) + 1
  have hQ : 2 ≤ Q := by omega
  have hB : 0 < B := by
    have h := sum_nonneg (s := Icc 1 Q) fun m _ => (hK (m - 1)).le
    dsimp only [B]
    linarith only [h]
  refine ⟨Q, B, hQ, hB, fun N hQN hlog c hc0 hc1 => ?_⟩
  have hN : 2 ≤ N := hQ.trans
    ((Nat.le_self_pow (by norm_num : 4 ≠ 0) Q).trans hQN)
  have hL1 : 1 ≤ Real.log N := (le_max_left _ _).trans hlog
  have hL : 0 < Real.log N := zero_lt_one.trans_le hL1
  have he := tiltedSplineConductorTailFloor_pos 1
  apply (completeWeilMatrix_isHermitian tiltedUnitSpline c N).posDef_iff_eigenvalues_pos.mpr
  intro i
  by_contra hi
  have hi0 : (completeWeilMatrix_isHermitian tiltedUnitSpline c N).eigenvalues i ≤ 0 :=
    le_of_not_gt hi
  let hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  let x := hA.eigenvectorBasis i
  have hx : ‖x‖ = 1 := by
    have h : ⟪x, x⟫ = (1 : ℝ) := by
      simpa only [ite_true] using (orthonormal_iff_ite.mp hA.eigenvectorBasis.orthonormal) i i
    rw [real_inner_self_eq_norm_sq] at h
    nlinarith only [h, norm_nonneg x]
  have henergy : completeWeilEnergy tiltedUnitSpline c N x ≤ 0 := by
    have hAx : Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x =
        hA.eigenvalues i • x := by
      ext j
      exact congrFun (hA.mulVec_eigenvectorBasis i) j
    change ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) x, x⟫ ≤ 0
    rw [hAx, real_inner_smul_left, real_inner_self_eq_norm_sq, hx, one_pow, mul_one]
    exact hi0
  obtain ⟨a, ha⟩ := hcut N hN c hc0 hc1 x hx henergy
  have hmass := normalizedRamanujan_coordinate_mass_ge_of_raw_approximation
    (by omega : R ≤ Q) hQ hQN x hx a ha
  have hterm (m : ℕ) (hm : m ∈ Icc 1 Q) :
      ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 ≤
        K (m - 1) / Real.log N / tiltedSplineConductorTailFloor 1 ^ 2 := by
    have hm0 : 0 < m := (mem_Icc.mp hm).1
    have hcoord := eigenvector_coordinate_sq_le_residual hA i hi0 he
      (touching_conductor_floor hc0 hc1 hm0) (normalizedRamanujanHorizonVector m N)
    have hr := hres (m - 1) N hN hL1 c hc0 hc1
    rw [show (m - 1).succ = m by omega] at hr
    exact hcoord.trans (div_le_div_of_nonneg_right hr (sq_nonneg _))
  have hsum := sum_le_sum hterm
  simp only [← sum_div] at hsum
  have hsumB : (∑ m ∈ Icc 1 Q, K (m - 1)) ≤ B := by dsimp only [B]; linarith only
  have hupper := hsum.trans (div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right hsumB hL.le) (sq_nonneg _))
  have hbudget : B / Real.log N / tiltedSplineConductorTailFloor 1 ^ 2 ≤ 1 / 36 := by
    have hh := (div_le_iff₀ (sq_pos_of_pos he)).mp ((le_max_right _ _).trans hlog)
    rw [div_le_iff₀ (sq_pos_of_pos he), div_le_iff₀ hL]
    nlinarith only [hh]
  linarith only [hmass, hupper.trans hbudget]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_completedConductor_residual_horizon_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completedConductor_residual_horizon_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_completedConductor_residual_explicit_horizon_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_horizon

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_touching_residual_explicit_horizon_bound

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_through_touching
