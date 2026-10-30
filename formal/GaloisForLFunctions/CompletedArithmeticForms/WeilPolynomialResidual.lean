import GaloisForLFunctions.CompletedArithmeticForms.UpwardSourcePayment
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.WeilReplacementErrorsHavePolynomialCost
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.NearGammaDownwardCancellationHasPolynomialGrowth
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompletedConductorQuasimodesAreUniformOnBoundedOverlap
import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheArithmeticResidualBudgetIsUniformInTheHorizon

/-!
# Polynomial payment of every complete Weil residual term

The actual eight-term decomposition has one simultaneous overlap-horizon
bound. Prime adjunction, both polar terms, separated cross terms, near
Gamma cancellation, and the entire upward shell source are all retained.
-/

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CompletedArithmeticForms

open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis
  SignedArithmeticHodgeTheory

/-- The two distinct horizon costs in the complete source residual. -/
def weilResidualScale (c : ℝ) (N : ℕ) : ℝ :=
  c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 + c ^ 6 / Real.sqrt (Real.log N)

theorem weilResidualScale_nonneg (c : ℝ) (N : ℕ) : 0 ≤ weilResidualScale c N := by
  unfold weilResidualScale
  positivity

private theorem norm_add_sq_le_two {V : Type*} [SeminormedAddCommGroup V] (v w : V) :
    ‖v + w‖ ^ 2 ≤ 2 * (‖v‖ ^ 2 + ‖w‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le v w) 2
  nlinarith only [h, sq_nonneg (‖v‖ - ‖w‖)]

private theorem norm_eight_residuals_sq_le {V : Type*} [SeminormedAddCommGroup V]
    (p s c x q y z u : V) :
    ‖-p + s + c - x + q + (y + z) - u‖ ^ 2 ≤
      8 * (‖p‖ ^ 2 + ‖s‖ ^ 2 + ‖c‖ ^ 2 + ‖x‖ ^ 2 +
        ‖q‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 + ‖u‖ ^ 2) := by
  have hp := norm_add_sq_le_two (-p) s
  have hc := norm_add_sq_le_two c (-x)
  have hq := norm_add_sq_le_two q y
  have hz := norm_add_sq_le_two z (-u)
  have hpc := norm_add_sq_le_two (-p + s) (c + -x)
  have hqz := norm_add_sq_le_two (q + y) (z + -u)
  have hall := norm_add_sq_le_two ((-p + s) + (c + -x)) ((q + y) + (z + -u))
  rw [norm_neg] at hp hc hz
  have he : -p + s + c - x + q + (y + z) - u =
      ((-p + s) + (c + -x)) + ((q + y) + (z + -u)) := by abel
  rw [he]
  nlinarith only [hp, hc, hq, hz, hpc, hqz, hall]

/-- The literal normalized prime residual has an inverse-logarithmic squared norm bound. -/
theorem exists_normalizedPrimeResidual_inverse_log_bound {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          C / Real.log N := by
  obtain ⟨B, hB, hbound⟩ := exists_uniform_ramanujanPrimeResidual_family_bound
  refine ⟨B * ramanujanResidualConductorCost m ^ 2, by positivity, ?_⟩
  intro N
  let j : ℕ+ := ⟨m, hm⟩
  have hs := hbound {j} (fun _ => 1) N
  simp only [sum_singleton, one_mul, one_pow, mul_one] at hs
  have heq :
      ‖Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 =
      (∑ n ∈ Icc 1 N, ramanujanPrimeResidual m N n ^ 2) / Real.log N := by
    simp only [normalizedRamanujanHorizonVector, map_smul]
    rw [smul_comm (Real.log N - ramanujanAdjunctionEnergy m) (Real.sqrt (Real.log N))⁻¹,
      ← smul_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow,
      Real.sq_sqrt (Real.log_natCast_nonneg N), ramanujanHorizonVector_residual_norm_sq]
    simp only [ramanujanPrimeResidual, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact div_le_div_of_nonneg_right hs (Real.log_natCast_nonneg N)

private theorem lower_power_div_log_le_scale {C c : ℝ} (hC : 0 ≤ C)
    (hc : 1 ≤ c) {N k : ℕ} (hL : 1 ≤ Real.log (N : ℝ)) (hk : k ≤ 6) :
    C * c ^ k / Real.log N ≤ C * weilResidualScale c N := by
  have hs1 : 1 ≤ Real.sqrt (Real.log (N : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hs0 : 0 < Real.sqrt (Real.log (N : ℝ)) := zero_lt_one.trans_le hs1
  have hsL : Real.sqrt (Real.log (N : ℝ)) ≤ Real.log N := by
    nlinarith only [hs1, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  calc
    _ ≤ C * c ^ 6 / Real.log N := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc hk) hC) (Real.log_natCast_nonneg N)
    _ ≤ C * c ^ 6 / Real.sqrt (Real.log N) :=
      div_le_div_of_nonneg_left (by positivity) hs0 hsL
    _ = C * (c ^ 6 / Real.sqrt (Real.log N)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC

private theorem width_sq_le_scale {C c : ℝ} (hC : 0 ≤ C) (hc : 1 ≤ c)
    {N : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ Real.log (N : ℝ)) :
    C * c ^ 2 / (N : ℝ) ^ 2 ≤ C * weilResidualScale c N := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := zero_lt_one.trans_le hN1
  have hs1 : 1 ≤ Real.sqrt (Real.log (N : ℝ)) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hL
  have hs0 : 0 < Real.sqrt (Real.log (N : ℝ)) := zero_lt_one.trans_le hs1
  have hsN : Real.sqrt (Real.log (N : ℝ)) ≤ (N : ℝ) ^ 2 := by
    have hsL : Real.sqrt (Real.log (N : ℝ)) ≤ Real.log N := by
      nlinarith only [hs1, Real.sq_sqrt (Real.log_natCast_nonneg N)]
    nlinarith only [hsL, Real.log_le_sub_one_of_pos hN0, hN1]
  calc
    _ ≤ C * c ^ 6 / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hc (by norm_num : 2 ≤ 6)) hC) (sq_nonneg _)
    _ ≤ C * c ^ 6 / Real.sqrt (Real.log N) :=
      div_le_div_of_nonneg_left (by positivity) hs0 hsN
    _ = C * (c ^ 6 / Real.sqrt (Real.log N)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) hC

/-- Every literal residual term is paid on one simultaneous overlap-horizon domain. -/
theorem exists_completeWeil_polynomial_residual_bound {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 / 3 →
      linearPrimeStrip c ≤ N → 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          C * weilResidualScale c N := by
  obtain ⟨Cp, hCp, hp⟩ := exists_normalizedPrimeResidual_inverse_log_bound hm
  obtain ⟨Cs, hCs, hs⟩ := exists_completeWeilSelfError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cz, hCz, hz⟩ := exists_fullWeilCenter_norm_sq_polynomial_bound φ hm
  obtain ⟨Cx, hCx, hx⟩ := exists_separatedCrossError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cq, hCq, hq⟩ := exists_fullWeilPoleError_norm_sq_polynomial_bound hφ hsupp hM hm
  obtain ⟨Cd, hCd, hd⟩ := exists_fullNearGammaDownward_norm_sq_polynomial_bound hφ hsupp hM m
  obtain ⟨Cn, hCn, hn⟩ := exists_nearCenterVector_norm_sq_polynomial_bound hM hm
  obtain ⟨Cu, hCu, hu⟩ := exists_actualUpward_polynomial_payment hφ hsupp hM hm
  let a := (Real.sqrt (m.totient : ℝ))⁻¹
  let T := Cp + Cs + Cz + Cx + Cq + a ^ 2 * Cd + Cn + a ^ 2 * Cu
  refine ⟨8 * T + 1, by dsimp only [T]; positivity, ?_⟩
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hs, hu, eventually_ge_atTop 1, hlog.eventually_ge_atTop 1] with N hsN huN hN hL
  intro c hc hw hBN hlarge
  have hc0 : 0 < c := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw1 : c / N ≤ 1 := hw.trans (by norm_num)
  have hcN : c ≤ (N : ℝ) := by simpa only [one_mul] using (div_le_iff₀ hN0).mp hw1
  have h2c : 2 * c ≤ (N : ℝ) := by
    have h := (div_le_iff₀ hN0).mp hw
    linarith only [h, hc0]
  have hp' := (hp N).trans (by
    simpa only [pow_zero, mul_one] using
      lower_power_div_log_le_scale hCp hc hL (by norm_num : 0 ≤ 6))
  have hs' := (hsN c hc0 hcN).trans (width_sq_le_scale hCs hc hN hL)
  have hz' := (hz c N).trans (lower_power_div_log_le_scale hCz hc hL (by norm_num : 2 ≤ 6))
  have hx' := (hx c hc0 N hN).trans (lower_power_div_log_le_scale hCx hc hL (by norm_num : 4 ≤ 6))
  have hq' := (hq c hc0 N hN hcN).trans (lower_power_div_log_le_scale hCq hc hL (by norm_num : 4 ≤ 6))
  have hn' := (hn c hc N hN h2c).trans (lower_power_div_log_le_scale hCn hc hL (by norm_num : 5 ≤ 6))
  have hd' : ‖a • normalizedFullNearGammaDownwardVector φ c N m‖ ^ 2 ≤
      (a ^ 2 * Cd) * weilResidualScale c N := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_left
      ((hd c hc N hN hw).trans (lower_power_div_log_le_scale hCd hc hL (by norm_num : 5 ≤ 6)))
        (sq_nonneg a)).trans_eq (by ring)
  have hu' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
        (a ^ 2 * Cu) * weilResidualScale c N := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    exact (mul_le_mul_of_nonneg_left (huN c hc hw1 hBN hlarge) (sq_nonneg a)).trans_eq (by ring)
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc0 hN hm]
  have hsum := norm_eight_residuals_sq_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (a • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  dsimp only [T]
  nlinarith only [hsum, hp', hs', hz', hx', hq', hd', hn', hu', weilResidualScale_nonneg c N]

/-- The actual tilted-spline complete matrix has the same polynomial residual law. -/
theorem exists_tiltedWeil_polynomial_residual_bound {m : ℕ} (hm : 0 < m) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c / N ≤ 1 / 3 →
      linearPrimeStrip c ≤ N → 2 * ((Real.exp 1 + 3) * c) * linearPrimeStrip c ≤ (N : ℝ) →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
          (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
          C * weilResidualScale c N :=
  exists_completeWeil_polynomial_residual_bound contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hm

#print axioms exists_normalizedPrimeResidual_inverse_log_bound
#print axioms exists_completeWeil_polynomial_residual_bound
#print axioms exists_tiltedWeil_polynomial_residual_bound

end GaloisForLFunctions.CompletedArithmeticForms
