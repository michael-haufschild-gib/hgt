import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheActualUpwardSourceHasPolynomialHarmonicBounds
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeilReplacementErrorsHavePolynomialCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorQuasimodesAreUniformOnBoundedOverlap
import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticResidualBudgetIsUniformInTheHorizon

/-!
# Polynomial error for complete conductor quasimodes

The exact eight-term residual identity combines the arithmetic Hodge budget,
Weil replacement bounds, full downward cancellation, and the actual upward
source. Each fixed conductor has squared residual `O(c^10 / sqrt (log N))`
whenever `c ≥ 1` and `4 (exp 1 + 3)^2 c^2 ≤ N`.
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

private theorem polynomial_div_log_le {C c L : ℝ} (hC : 0 ≤ C) (hc : 1 ≤ c) (hL : 1 ≤ L)
    {k : ℕ} (hk : k ≤ 10) :
    C * c ^ k / L ≤ C * c ^ 10 / Real.sqrt L := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  have hsL : Real.sqrt L ≤ L := by
    nlinarith only [Real.sq_sqrt hL0.le, Real.sqrt_nonneg L, hL]
  exact (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc hk) hC) hL0.le).trans
      (div_le_div_of_nonneg_left (by positivity) hs hsL)

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

/-- All eight actual source terms give a common polynomial completed-conductor residual bound. -/
theorem exists_completeWeil_completedConductor_residual_sq_polynomial_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        K * c ^ 10 / Real.sqrt (Real.log N) := by
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_norm_sq_log_bound hm
  obtain ⟨Cs, hCs, hs⟩ := exists_completeWeilSelfError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cc, hCc, hcenter⟩ := exists_fullWeilCenter_norm_sq_polynomial_bound φ hm
  obtain ⟨Cx, hCx, hx⟩ := exists_separatedCrossError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cq, hCq, hq⟩ := exists_fullWeilPoleError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cd, hCd, hdown⟩ := exists_fullNearGammaDownward_norm_sq_polynomial_bound hφ hsupp hM m
  obtain ⟨Cn, hCn, hnear⟩ := exists_nearCenterVector_norm_sq_polynomial_bound hM hm
  obtain ⟨Cu, hCu, hup⟩ := exists_normalizedUpwardPrimeResidual_norm_sq_polynomial_bound hφ hsupp hM hm
  let A := (Real.sqrt (m.totient : ℝ))⁻¹ ^ 2
  have hA : 0 ≤ A := sq_nonneg _
  let K := 8 * (Cp + Cs + Cc + Cx + Cq + A * Cd + Cn + A * Cu) + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  have hloglim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨K, hK, ?_⟩
  filter_upwards [hs, hup, eventually_ge_atTop 1, hloglim.eventually_ge_atTop 1]
    with N hs hup hN hlog
  intro c hc hlarge
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hlog
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
  have hsqrtN : Real.sqrt (Real.log N) ≤ (N : ℝ) ^ 2 := by
    have hlogN := Real.log_le_sub_one_of_pos hN0
    have hs := Real.sq_sqrt hL0.le
    have hroot : Real.sqrt (Real.log N) ≤ N := by
      nlinarith only [hlogN, hs, hN1, Real.sqrt_nonneg (Real.log N)]
    nlinarith only [hroot, hN1]
  have hp' : ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cp * c ^ 10 / Real.sqrt (Real.log N) := by
    have h := polynomial_div_log_le hCp hc hlog (k := 0) (by norm_num)
    simp only [pow_zero, mul_one] at h
    exact (hp N).trans h
  have hs' : ‖completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cs * c ^ 10 / Real.sqrt (Real.log N) := by
    refine (hs c hc0 hcN).trans ?_
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc (by norm_num : 2 ≤ 10)) hCs) (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left (by positivity) (Real.sqrt_pos.mpr hL0) hsqrtN)
  have hc' := (hcenter c N).trans (polynomial_div_log_le hCc hc hlog (by norm_num : 2 ≤ 10))
  have hx' := (hx c hc0 N hN).trans (polynomial_div_log_le hCx hc hlog (by norm_num : 4 ≤ 10))
  have hq' := (hq c hc0 N hN hcN).trans (polynomial_div_log_le hCq hc hlog (by norm_num : 4 ≤ 10))
  have hn' := (hnear c hc N hN htwo).trans (polynomial_div_log_le hCn hc hlog (by norm_num : 5 ≤ 10))
  have hd' : ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      (A * Cd) * c ^ 10 / Real.sqrt (Real.log N) := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h := (hdown c hc N hN hw).trans (polynomial_div_log_le hCd hc hlog (by norm_num : 5 ≤ 10))
    exact (mul_le_mul_of_nonneg_left h hA).trans_eq (by ring)
  have hu' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      (A * Cu) * c ^ 10 / Real.sqrt (Real.log N) := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_left (hup c hc hlarge) hA).trans_eq (by ring)
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
  dsimp only [K]
  calc
    _ ≤ 8 * (Cp * c ^ 10 / Real.sqrt (Real.log N) + Cs * c ^ 10 / Real.sqrt (Real.log N) +
        Cc * c ^ 10 / Real.sqrt (Real.log N) + Cx * c ^ 10 / Real.sqrt (Real.log N) +
        Cq * c ^ 10 / Real.sqrt (Real.log N) + (A * Cd) * c ^ 10 / Real.sqrt (Real.log N) +
        Cn * c ^ 10 / Real.sqrt (Real.log N) + (A * Cu) * c ^ 10 / Real.sqrt (Real.log N)) := hbound
    _ = (8 * (Cp + Cs + Cc + Cx + Cq + A * Cd + Cn + A * Cu)) *
        c ^ 10 / Real.sqrt (Real.log N) := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      exact mul_le_mul_of_nonneg_right (by linarith only) (pow_nonneg hc0.le 10)

/-- The explicit tilted spline needs no analytic profile input for this residual estimate. -/
theorem exists_tiltedUnitSpline_completedConductor_residual_sq_polynomial_bound {m : ℕ} (hm : 0 < m) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        K * c ^ 10 / Real.sqrt (Real.log N) :=
  exists_completeWeil_completedConductor_residual_sq_polynomial_bound contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hm

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_completedConductor_residual_sq_polynomial_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completedConductor_residual_sq_polynomial_bound
