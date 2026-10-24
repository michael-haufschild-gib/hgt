import GaloisForLFunctions.TransHorizonIncidenceMechanics.PMCofactorRowRamanujanTruncation
import GaloisForLFunctions.BezoutValuationIncidence.CompletePronicVaughanCalibration
import GaloisForLFunctions.BezoutValuationIncidence.BirthDelayedInteriorJumpCenteringAndUniformPairBounds
import GaloisForLFunctions.BezoutValuationIncidence.ArbitraryDepthBezoutShellsAndRoutePMSecondLayerProfile
import GaloisForLFunctions.BezoutValuationIncidence.UniversalSawtoothInteriorMartingaleAndPostStepCalculus
import GaloisForLFunctions.BezoutValuationIncidence.RoutePMCofactorSieveBridgeAndUnifiedEnergyEquivalence
import GaloisForLFunctions.BezoutValuationIncidence.BeurlingGibbsCotangentTransportAndSchurCollarWallOneBridge
import GaloisForLFunctions.BezoutValuationIncidence.CompletePeriodQuadraticFormsSignInvarianceAndTransHorizonSeparation
import GaloisForLFunctions.BezoutValuationIncidence.AllDampingVinogradovKorobovBandAndInteriorGrowth

/-!
# Complete Signed Trans-Horizon Energy, Growing-Cutoff Cofactor Transfer, and Selectivity of the Conservation and Dissipation Laws

This module resolves Open Problem 7.1 (together with research topics 7.9.2 and 7.9.4) of
`TransHorizonIncidenceMechanics` by establishing the complete signed trans-horizon pronic energy
calculus with means, endpoints, active-pair boundaries, mixed Vaughan covariances, Ramanujan
truncation errors, and growing cutoffs retained at fixed sub-half damping `ε ∈ (0, 1/2)`, and by
classifying the selectivity of the theory's conservation and dissipation laws across abstract
Beurling systems, `(ℤ/2ℤ)^N` sign-character orbits, and the additive `ℤ`-lattice successor
structure of `ℕ`.

## Main results

1. **Exact Mean Preservation, Cumulative Ramanujan Truncation, and Growing-Cutoff Pronic Energy
   Transfer for the Cofactor Row (§1)**:
   - Unlike the naive truncated Möbius row (whose finite-horizon harmonic sum differs from
     `Re(1/ζ(1+ε))` by the harmonic tail `τ_N(ε)`), the actual Route PM cofactor row
     `pmCofactorRealWeight ε Q` satisfies the **exact finite-horizon mean identity**
     `finiteHarmonicSum Q (pmCofactorRealWeight ε Q) = (pmPowerDampedDivisorDensity ε).re` and
     `selbergMultiplesCoord Q (pmCofactorRealWeight ε Q) 1 = (pmPowerDampedDivisorDensity ε).re`
     at every horizon `Q ≥ 1` (`finiteHarmonicSum_pmCofactorRealWeight`,
     `selbergMultiplesCoord_one_pmCofactorRealWeight`).
   - Consequently, the cofactor row's centered prefix discrepancy
     `sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q)` has **zero linear mean-drift dipole**
     against `pmPowerDampedCenteredDivisorPrefix ε n`, and their difference is the pure cumulative
     Ramanujan truncation sum:
     `sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) - pmPowerDampedCenteredDivisorPrefix ε n
       = ∑_{k=1}^n (sieveSeq Q (pmCofactorRealWeight ε Q) k - pmPowerDampedDivisorCoeff ε k)`
     (`sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_eq`), bounded pointwise by
     `((1 + ε) / ε) * (∑_{k=1}^n τ(k)) * Q^{-ε} ≤ ((1 + ε) / ε) * n² * Q^{-ε}`
     (`abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_le`) and against the
     pure-interior prefix `pmBezoutInteriorPrefix ε n` by `1 / 2 + ((1 + ε) / ε) * n² * Q^{-ε}`
     (`abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_interiorPrefix_le`).
   - Defining the finite-cutoff pronic discrepancy energy
     `sieveTruncatedPronicEnergy Q T c = ∑_{n=1}^T (sievePrefixDiscrepancy Q n c)² / pronicSeq n`,
     the general pronic `ℓ²` triangle inequality (`abs_sqrt_pronicSum_sub_sqrt_le`) yields the
     explicit growing-cutoff square-root transfer bounds:
     `|√(sieveTruncatedPronicEnergy Q T (pmCofactorRealWeight ε Q)) - √(pmPowerDampedDivisorDiscreteEnergy ε T)|
       ≤ ((1 + ε) / ε) * T * √T * Q^{-ε}` and
     `|√(sieveTruncatedPronicEnergy Q T (pmCofactorRealWeight ε Q)) - √(pmBezoutInteriorPronicEnergy ε T)|
       ≤ 1 / 2 + ((1 + ε) / ε) * T * √T * Q^{-ε}`
     (`abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_discreteEnergy_le`,
     `abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_interiorPronic_le`). Along any growing
     horizon schedule `Q(T) ≥ 1` with `T * √T * Q(T)^{-ε} ≤ M`, boundedness of the cofactor row's
     truncated pronic energy is two-sided equivalent to boundedness of `pmBezoutInteriorPronicEnergy ε T`
     (`growingCutoff_cofactorPronicEnergy_bounded_iff_interiorPronicEnergy_bounded`).

2. **Complete Signed Interior Energy Calibration, 25-Entry Vaughan Gram Matrix, Birth-Delayed
   Growing-Cutoff Envelope, and All-Damping Vinogradov–Korobov Band (§2)**:
   - Unifies the exact polarization between `pmPowerDampedDivisorDiscreteEnergy` and
     `pmBezoutInteriorPronicEnergy`, the non-circular interior gradient + local-impulse conservation
     law (`complete_signed_interior_energy_and_conservation_identity`), the 25-entry signed Vaughan
     pronic Gram matrix with moving endpoints retained (`pmInteriorPronicEnergy_eq_diagonal_add_mixed`,
     `pmPronicVaughan_flip_diagonal`, `pmPronicVaughan_flip_energy_gap`,
     `not_summable_pmPronicLogMajorant`), and an explicit coefficient-free `5 / 2 * N` bound on the
     birth-delayed compensated progression at growing cutoff `N = (d + 2) * L`
     (`abs_pmBezoutInteriorPrefix_birthDelayed_compensated_le_five_halves_mul`).
   - Synthesizes the 6-way equivalence of all signed receiver formulations at every `ε > 0`, their
     unconditional admission on the exact zero-width half-line `ε > Θ - 1 / 2`, common accumulation
     threshold `Θ - 1 / 2`, iterated zero translation with multiplicity, and the all-damping
     Vinogradov–Korobov band and sub-half-damping growth laws (`0 < ε < 1 / 2`)
     (`complete_signed_receiver_equivalence_and_all_damping_vk_laws`).

3. **Selectivity of the Conservation and Dissipation Laws (§3, Topic 7.9.4)**:
   - **Class I (Beurling-universal multiplicative laws)**: generalized Möbius inversion, strict
     transverse Gibbs log-submodularity, divided-log prime-power completion, depth-zero Gamma gauge
     enclosure in `[1, 2]`, and the three-sector zero/one/higher large-label Buchstab decomposition
     hold on every abstract `BeurlingSystem` (`selectivity_class_I_beurling_universal_laws`).
   - **Class II (Sign-blind / `(ℤ/2ℤ)^N` shifted-pair invariant laws)**: all centered and uncentered
     complete-period quadratic forms and lag covariances are invariant under `(ℤ/2ℤ)^N` Selberg
     coordinate sign flips (and characterize the sign-character orbit up to equality of means),
     diagonal Vaughan pronic Gram entries are invariant under component sign flips, and first-octave
     step-defect nonpositivity holds for every `{-1, 0, 1}`-valued sequence including `μ²` and `1`
     (`selectivity_class_II_signBlind_and_parityOrbit_laws`).
   - **Class III (`ℤ`-lattice Bézout-selective laws)**: consecutive coprimality `gcd(n, n + 1) = 1`
     and `pa - qb = 1` force the zero-diagonal square-increment and pronic Abel identities, complete
     centering-density cancellation and pronic multiplicativity of the active sawtooth martingale,
     arbitrary-depth `(2r - 1)`-step Bézout shell midpoint annihilation, the conditional jump-orbit
     mean classification, least Bézout successor-seed resonance, and trans-horizon separation of
     parity-isometric rows (`selectivity_class_III_bezout_successor_selective_laws`).
-/

open Finset Filter Topology ArithmeticFunction Complex MeasureTheory Set
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.NymanMellin GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Mean Preservation, Cumulative Ramanujan Truncation, and Growing-Cutoff Pronic Energy Transfer -/

/-- **[New formulation] Exact Finite-Horizon Harmonic Mean of the Cofactor Row
(`finiteHarmonicSum_pmCofactorRealWeight`):**
For every `ε > 0` and horizon `Q ≥ 1`, the finite harmonic sum of `pmCofactorRealWeight ε Q`
equals the exact infinite-horizon divisor density `(pmPowerDampedDivisorDensity ε).re`, with zero
harmonic-tail truncation error. -/
theorem finiteHarmonicSum_pmCofactorRealWeight {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) :
    finiteHarmonicSum Q (pmCofactorRealWeight ε Q) =
      (pmPowerDampedDivisorDensity ε).re := by
  have h := congrArg Complex.re (pmPowerDampedRamanujanCofactor_density hε hQ)
  rw [Complex.re_sum] at h
  rw [← h]
  unfold finiteHarmonicSum pmCofactorRealWeight
  refine Finset.sum_congr rfl fun d _ => ?_
  exact (Complex.div_ofReal_re (pmPowerDampedRamanujanCofactor ε Q d) (d : ℝ)).symm

/-- **[New formulation] Exact Selberg Mean Coordinate of the Cofactor Row
(`selbergMultiplesCoord_one_pmCofactorRealWeight`):**
For every `ε > 0` and `Q ≥ 1`, `selbergMultiplesCoord Q (pmCofactorRealWeight ε Q) 1` equals
`(pmPowerDampedDivisorDensity ε).re`. -/
theorem selbergMultiplesCoord_one_pmCofactorRealWeight {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) :
    selbergMultiplesCoord Q (pmCofactorRealWeight ε Q) 1 =
      (pmPowerDampedDivisorDensity ε).re := by
  rw [selbergMultiplesCoord_one_eq_finiteHarmonicSum,
    finiteHarmonicSum_pmCofactorRealWeight hε hQ]

/-- **[New formulation] Dipole-Free Cumulative Ramanujan Truncation Identity for the Cofactor Row
(`sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_eq`):**
Because `finiteHarmonicSum Q (pmCofactorRealWeight ε Q) = (pmPowerDampedDivisorDensity ε).re` holds
identically for every `Q ≥ 1`, the linear mean-drift dipole cancels completely between the cofactor
row's prefix discrepancy and `pmPowerDampedCenteredDivisorPrefix ε n`, leaving the pure cumulative
sum of pointwise Ramanujan truncation errors. -/
theorem sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_eq
    {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
      pmPowerDampedCenteredDivisorPrefix ε n =
      ∑ k ∈ Icc 1 n,
        (sieveSeq Q (pmCofactorRealWeight ε Q) k - pmPowerDampedDivisorCoeff ε k) := by
  rw [sievePrefixDiscrepancy_eq_sum_sub_drift,
    ← sum_Icc_sieveSeq_eq_sum_sievedDivisorSum,
    finiteHarmonicSum_pmCofactorRealWeight hε hQ,
    pmPowerDampedCenteredDivisorPrefix_eq,
    Finset.sum_sub_distrib]
  ring

/-- **[New formulation] Cofactor Prefix Discrepancy Decomposition into Pure-Interior Prefix,
Active-Pair Boundary, and Cumulative Ramanujan Truncation
(`sievePrefixDiscrepancy_pmCofactorRealWeight_sub_interiorPrefix_eq`):**
For every `ε > 0`, `Q ≥ 1`, and `n : ℕ`, the difference between the cofactor row's prefix
discrepancy and the horizon-free Bézout interior prefix `pmBezoutInteriorPrefix ε n` equals the
active-pair boundary `addDiff (pmActiveSawtoothComponent ε) n` plus the cumulative Ramanujan
truncation sum. -/
theorem sievePrefixDiscrepancy_pmCofactorRealWeight_sub_interiorPrefix_eq
    {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
      pmBezoutInteriorPrefix ε n =
      addDiff (pmActiveSawtoothComponent ε) n +
        ∑ k ∈ Icc 1 n,
          (sieveSeq Q (pmCofactorRealWeight ε Q) k - pmPowerDampedDivisorCoeff ε k) := by
  have h1 := sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_eq hε hQ n
  have h2 := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
  linarith

/-- Every positive integer `k` has at most `k` divisors: `(k.divisors.card : ℝ) ≤ k`. -/
private theorem card_divisors_le_self_real (k : ℕ) :
    (k.divisors.card : ℝ) ≤ (k : ℝ) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · have hsub : k.divisors ⊆ Icc 1 k := fun d hd =>
      mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.le_of_dvd hk (Nat.dvd_of_mem_divisors hd)⟩
    have hcard : k.divisors.card ≤ k := by
      simpa [Nat.card_Icc] using Finset.card_le_card hsub
    exact_mod_cast hcard

/-- **[New formulation] Cumulative Divisor-Sum and Quadratic Pointwise Truncation Bounds for the
Cofactor Prefix Discrepancy (`abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_le`):**
For every `ε > 0`, `Q ≥ 1`, and `n : ℕ`, the discrepancy between the cofactor row's centered prefix
and `pmPowerDampedCenteredDivisorPrefix ε n` is bounded both by the cumulative divisor sum
`((1 + ε) / ε) * (∑_{k=1}^n τ(k)) * Q^{-ε}` and by `((1 + ε) / ε) * n² * Q^{-ε}`. -/
theorem abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_le
    {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    |sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
        pmPowerDampedCenteredDivisorPrefix ε n| ≤
      (1 + ε) / ε * (∑ k ∈ Icc 1 n, (k.divisors.card : ℝ)) * (Q : ℝ) ^ (-ε) ∧
    |sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
        pmPowerDampedCenteredDivisorPrefix ε n| ≤
      (1 + ε) / ε * (n : ℝ) ^ 2 * (Q : ℝ) ^ (-ε) := by
  have hdiv :
      |sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
          pmPowerDampedCenteredDivisorPrefix ε n| ≤
        (1 + ε) / ε * (∑ k ∈ Icc 1 n, (k.divisors.card : ℝ)) * (Q : ℝ) ^ (-ε) := by
    rw [sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_eq hε hQ n]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc
      (∑ k ∈ Icc 1 n, |sieveSeq Q (pmCofactorRealWeight ε Q) k - pmPowerDampedDivisorCoeff ε k|)
        ≤ ∑ k ∈ Icc 1 n, (1 + ε) / ε * (k.divisors.card : ℝ) * (Q : ℝ) ^ (-ε) :=
          Finset.sum_le_sum fun k hk =>
            abs_sieveSeq_pmCofactor_sub_divisorCoeff_le hε hQ (mem_Icc.mp hk).1
      _ = (1 + ε) / ε * (∑ k ∈ Icc 1 n, (k.divisors.card : ℝ)) * (Q : ℝ) ^ (-ε) := by
          rw [Finset.mul_sum, Finset.sum_mul]
  refine ⟨hdiv, hdiv.trans ?_⟩
  have hsum_le : (∑ k ∈ Icc 1 n, (k.divisors.card : ℝ)) ≤ (n : ℝ) ^ 2 := by
    calc
      (∑ k ∈ Icc 1 n, (k.divisors.card : ℝ))
        ≤ ∑ k ∈ Icc 1 n, (n : ℝ) := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact (card_divisors_le_self_real k).trans (by exact_mod_cast (mem_Icc.mp hk).2)
      _ = (n : ℝ) ^ 2 := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, sq]
  have hnonneg : 0 ≤ (1 + ε) / ε * (Q : ℝ) ^ (-ε) := by positivity
  calc
    (1 + ε) / ε * (∑ k ∈ Icc 1 n, (k.divisors.card : ℝ)) * (Q : ℝ) ^ (-ε)
      = ((1 + ε) / ε * (Q : ℝ) ^ (-ε)) * ∑ k ∈ Icc 1 n, (k.divisors.card : ℝ) := by ring
    _ ≤ ((1 + ε) / ε * (Q : ℝ) ^ (-ε)) * (n : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = (1 + ε) / ε * (n : ℝ) ^ 2 * (Q : ℝ) ^ (-ε) := by ring

/-- **[New formulation] Pointwise Comparison Between the Cofactor Prefix Discrepancy and
`pmBezoutInteriorPrefix` (`abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_interiorPrefix_le`):**
For every `ε > 0`, `Q ≥ 1`, and `n : ℕ`:
`|sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) - pmBezoutInteriorPrefix ε n|
  ≤ 1 / 2 + ((1 + ε) / ε) * n² * Q^{-ε}`. -/
theorem abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_interiorPrefix_le
    {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) (n : ℕ) :
    |sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
        pmBezoutInteriorPrefix ε n| ≤
      1 / 2 + (1 + ε) / ε * (n : ℝ) ^ 2 * (Q : ℝ) ^ (-ε) := by
  have heq :
      sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) - pmBezoutInteriorPrefix ε n =
        addDiff (pmActiveSawtoothComponent ε) n +
          (sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
            pmPowerDampedCenteredDivisorPrefix ε n) := by
    have h := pmPowerDampedCenteredDivisorPrefix_eq_bezout_active_pair_add_interior ε n
    linarith
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add
    (abs_addDiff_pmActiveSawtoothComponent_le_half hε.le n)
    (abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_le hε hQ n).2)

/-- The finite-cutoff pronic discrepancy energy of a divisor-sieve weight `c` at horizon `Q` and
observation cutoff `T`:
`sieveTruncatedPronicEnergy Q T c = ∑_{n=1}^T (sievePrefixDiscrepancy Q n c)² / pronicSeq n`. -/
def sieveTruncatedPronicEnergy (Q T : ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ n ∈ Icc 1 T, (sievePrefixDiscrepancy Q n c) ^ 2 / (pronicSeq n : ℝ)

theorem sieveTruncatedPronicEnergy_nonneg (Q T : ℕ) (c : ℕ → ℝ) :
    0 ≤ sieveTruncatedPronicEnergy Q T c :=
  Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)

/-- **[New formulation] Universal Pronic `ℓ²` Triangle Inequality (`abs_sqrt_pronicSum_sub_sqrt_le`):**
For any two sequences `A, B : ℕ → ℝ` and any cutoff `T : ℕ`, the square roots of their pronic
energies on `Icc 1 T` differ by at most the square root of the pronic energy of `A - B`. -/
theorem abs_sqrt_pronicSum_sub_sqrt_le (A B : ℕ → ℝ) (T : ℕ) :
    |Real.sqrt (∑ n ∈ Icc 1 T, A n ^ 2 / (pronicSeq n : ℝ)) -
      Real.sqrt (∑ n ∈ Icc 1 T, B n ^ 2 / (pronicSeq n : ℝ))| ≤
      Real.sqrt (∑ n ∈ Icc 1 T, (A n - B n) ^ 2 / (pronicSeq n : ℝ)) := by
  have hstep : ∀ U V : ℕ → ℝ,
      Real.sqrt (∑ n ∈ Icc 1 T, U n ^ 2 / (pronicSeq n : ℝ)) ≤
        Real.sqrt (∑ n ∈ Icc 1 T, V n ^ 2 / (pronicSeq n : ℝ)) +
          Real.sqrt (∑ n ∈ Icc 1 T, (U n - V n) ^ 2 / (pronicSeq n : ℝ)) := by
    intro U V
    set EU := ∑ n ∈ Icc 1 T, U n ^ 2 / (pronicSeq n : ℝ)
    set EV := ∑ n ∈ Icc 1 T, V n ^ 2 / (pronicSeq n : ℝ)
    set ED := ∑ n ∈ Icc 1 T, (U n - V n) ^ 2 / (pronicSeq n : ℝ)
    have hEV0 : 0 ≤ EV := Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    have hED0 : 0 ≤ ED := Finset.sum_nonneg fun _ _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
    have hcs := sum_mul_sq_le_sq_mul_sq (Icc 1 T)
      (fun n => V n / Real.sqrt (pronicSeq n : ℝ))
      (fun n => (U n - V n) / Real.sqrt (pronicSeq n : ℝ))
    have hV2 : (∑ n ∈ Icc 1 T, (V n / Real.sqrt (pronicSeq n : ℝ)) ^ 2) = EV := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have hD2 : (∑ n ∈ Icc 1 T, ((U n - V n) / Real.sqrt (pronicSeq n : ℝ)) ^ 2) = ED := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    rw [hV2, hD2] at hcs
    set S := ∑ n ∈ Icc 1 T,
      (V n / Real.sqrt (pronicSeq n : ℝ)) * ((U n - V n) / Real.sqrt (pronicSeq n : ℝ))
    have hS_le : S ≤ Real.sqrt EV * Real.sqrt ED := by
      have hsq : S ^ 2 ≤ (Real.sqrt EV * Real.sqrt ED) ^ 2 := by
        rwa [mul_pow, Real.sq_sqrt hEV0, Real.sq_sqrt hED0]
      have hsqrt := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq_eq_abs,
        Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg EV) (Real.sqrt_nonneg ED))] at hsqrt
      exact (le_abs_self S).trans hsqrt
    have hdecomp : EU = EV + 2 * S + ED := by
      dsimp only [EU, EV, ED, S]
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hpr : 0 ≤ (pronicSeq n : ℝ) := Nat.cast_nonneg _
      rw [div_mul_div_comm, Real.mul_self_sqrt hpr]
      ring
    have hEU_le : EU ≤ (Real.sqrt EV + Real.sqrt ED) ^ 2 := by
      rw [hdecomp, add_sq, Real.sq_sqrt hEV0, Real.sq_sqrt hED0]
      linarith
    have hsqrt := Real.sqrt_le_sqrt hEU_le
    rwa [Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg EV) (Real.sqrt_nonneg ED))] at hsqrt
  have h1 := hstep A B
  have h2 := hstep B A
  have hsymm : (∑ n ∈ Icc 1 T, (B n - A n) ^ 2 / (pronicSeq n : ℝ)) =
      ∑ n ∈ Icc 1 T, (A n - B n) ^ 2 / (pronicSeq n : ℝ) :=
    Finset.sum_congr rfl fun n _ => by ring
  rw [hsymm] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **[New formulation] Growing-Cutoff Square-Root Transfer Between `sieveTruncatedPronicEnergy` of
the Cofactor Row and `pmPowerDampedDivisorDiscreteEnergy`
(`abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_discreteEnergy_le`):**
For every `ε > 0`, horizon `Q ≥ 1`, and observation cutoff `T : ℕ`:
`|√(sieveTruncatedPronicEnergy Q T (pmCofactorRealWeight ε Q)) - √(pmPowerDampedDivisorDiscreteEnergy ε T)|
  ≤ ((1 + ε) / ε) * T * √T * Q^{-ε}`. -/
theorem abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_discreteEnergy_le
    {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) (T : ℕ) :
    |Real.sqrt (sieveTruncatedPronicEnergy Q T (pmCofactorRealWeight ε Q)) -
      Real.sqrt (pmPowerDampedDivisorDiscreteEnergy ε T)| ≤
      (1 + ε) / ε * (T : ℝ) * Real.sqrt (T : ℝ) * (Q : ℝ) ^ (-ε) := by
  rw [pmPowerDampedDivisorDiscreteEnergy_eq_sum_pronicSeq]
  unfold sieveTruncatedPronicEnergy
  refine (abs_sqrt_pronicSum_sub_sqrt_le
    (fun n => sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q))
    (pmPowerDampedCenteredDivisorPrefix ε) T).trans ?_
  set K := (1 + ε) / ε * (Q : ℝ) ^ (-ε)
  have hK0 : 0 ≤ K := by positivity
  have hsum_le :
      (∑ n ∈ Icc 1 T,
        (sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
          pmPowerDampedCenteredDivisorPrefix ε n) ^ 2 / (pronicSeq n : ℝ)) ≤
      ((1 + ε) / ε * (T : ℝ) * Real.sqrt (T : ℝ) * (Q : ℝ) ^ (-ε)) ^ 2 := by
    calc
      (∑ n ∈ Icc 1 T,
          (sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
            pmPowerDampedCenteredDivisorPrefix ε n) ^ 2 / (pronicSeq n : ℝ))
        ≤ ∑ _n ∈ Icc 1 T, K ^ 2 * (T : ℝ) ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          obtain ⟨hn1, hnT⟩ := mem_Icc.mp hn
          have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
          have hnTR : (n : ℝ) ≤ T := by exact_mod_cast hnT
          have hpt := (abs_sievePrefixDiscrepancy_pmCofactorRealWeight_sub_centeredPrefix_le
            hε hQ n).2
          have hptK : |sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
              pmPowerDampedCenteredDivisorPrefix ε n| ≤ K * (n : ℝ) ^ 2 := by
            simpa only [K, mul_comm, mul_left_comm, mul_assoc] using hpt
          have hsq :
              (sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
                pmPowerDampedCenteredDivisorPrefix ε n) ^ 2 ≤ K ^ 2 * (n : ℝ) ^ 4 := by
            have h1 := pow_le_pow_left₀ (abs_nonneg _) hptK 2
            rw [sq_abs] at h1
            exact h1.trans (le_of_eq (by ring))
          have hpr_ge : (n : ℝ) ^ 2 ≤ (pronicSeq n : ℝ) := by
            simp only [pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            nlinarith
          calc
            (sievePrefixDiscrepancy Q n (pmCofactorRealWeight ε Q) -
                pmPowerDampedCenteredDivisorPrefix ε n) ^ 2 / (pronicSeq n : ℝ)
              ≤ (K ^ 2 * (n : ℝ) ^ 4) / (pronicSeq n : ℝ) :=
                div_le_div_of_nonneg_right hsq (Nat.cast_nonneg _)
            _ ≤ (K ^ 2 * (n : ℝ) ^ 4) / (n : ℝ) ^ 2 :=
                div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hnR) hpr_ge
            _ = K ^ 2 * (n : ℝ) ^ 2 := by field_simp
            _ ≤ K ^ 2 * (T : ℝ) ^ 2 :=
                mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hnR.le hnTR 2) (sq_nonneg K)
      _ = (T : ℝ) * (K ^ 2 * (T : ℝ) ^ 2) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      _ = ((1 + ε) / ε * (T : ℝ) * Real.sqrt (T : ℝ) * (Q : ℝ) ^ (-ε)) ^ 2 := by
          have hT0 : 0 ≤ (T : ℝ) := Nat.cast_nonneg T
          dsimp only [K]
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hT0]
          ring
  have hsqrt := Real.sqrt_le_sqrt hsum_le
  rwa [Real.sqrt_sq (by positivity)] at hsqrt

/-- **[New formulation] Growing-Cutoff Square-Root Transfer Between `sieveTruncatedPronicEnergy` of
the Cofactor Row and `pmBezoutInteriorPronicEnergy`
(`abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_interiorPronic_le`):**
For every `ε > 0`, horizon `Q ≥ 1`, and observation cutoff `T : ℕ`:
`|√(sieveTruncatedPronicEnergy Q T (pmCofactorRealWeight ε Q)) - √(pmBezoutInteriorPronicEnergy ε T)|
  ≤ 1 / 2 + ((1 + ε) / ε) * T * √T * Q^{-ε}`. -/
theorem abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_interiorPronic_le
    {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : 1 ≤ Q) (T : ℕ) :
    |Real.sqrt (sieveTruncatedPronicEnergy Q T (pmCofactorRealWeight ε Q)) -
      Real.sqrt (pmBezoutInteriorPronicEnergy ε T)| ≤
      1 / 2 + (1 + ε) / ε * (T : ℝ) * Real.sqrt (T : ℝ) * (Q : ℝ) ^ (-ε) := by
  have h1 := abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_discreteEnergy_le hε hQ T
  have h2 := abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half hε.le T
  obtain ⟨h1_lo, h1_hi⟩ := abs_le.mp h1
  obtain ⟨h2_lo, h2_hi⟩ := abs_le.mp h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **[New formulation] Equivalence of Growing-Cutoff Cofactor Pronic Energy Boundedness and
Pure-Interior Pronic Energy Boundedness (`growingCutoff_cofactorPronicEnergy_bounded_iff_interiorPronicEnergy_bounded`):**
For any fixed `ε > 0` and any growing horizon schedule `Q : ℕ → ℕ` with `Q(T) ≥ 1` and
`T * √T * Q(T)^{-ε} ≤ M` for all `T : ℕ`, uniform boundedness of the cofactor row's truncated pronic
energy `sieveTruncatedPronicEnergy (Q T) T (pmCofactorRealWeight ε (Q T))` across all `T : ℕ` is
equivalent to uniform boundedness of `pmBezoutInteriorPronicEnergy ε T` across all `T : ℕ`. -/
theorem growingCutoff_cofactorPronicEnergy_bounded_iff_interiorPronicEnergy_bounded
    {ε M : ℝ} (hε : 0 < ε) (hM : 0 ≤ M) {Q : ℕ → ℕ}
    (hQ1 : ∀ T : ℕ, 1 ≤ Q T)
    (hQT : ∀ T : ℕ, (T : ℝ) * Real.sqrt (T : ℝ) * (Q T : ℝ) ^ (-ε) ≤ M) :
    (∃ B : ℝ, ∀ T : ℕ,
      sieveTruncatedPronicEnergy (Q T) T (pmCofactorRealWeight ε (Q T)) ≤ B) ↔
    (∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy ε T ≤ B) := by
  set δ := 1 / 2 + (1 + ε) / ε * M
  have hδ0 : 0 ≤ δ := by positivity
  have hgap : ∀ T : ℕ,
      |Real.sqrt (sieveTruncatedPronicEnergy (Q T) T (pmCofactorRealWeight ε (Q T))) -
        Real.sqrt (pmBezoutInteriorPronicEnergy ε T)| ≤ δ := by
    intro T
    refine (abs_sqrt_sieveTruncatedPronicEnergy_pmCofactor_sub_sqrt_interiorPronic_le
      hε (hQ1 T) T).trans ?_
    have hmul : (1 + ε) / ε * (T : ℝ) * Real.sqrt (T : ℝ) * (Q T : ℝ) ^ (-ε) ≤
        (1 + ε) / ε * M := by
      calc
        (1 + ε) / ε * (T : ℝ) * Real.sqrt (T : ℝ) * (Q T : ℝ) ^ (-ε)
          = (1 + ε) / ε * ((T : ℝ) * Real.sqrt (T : ℝ) * (Q T : ℝ) ^ (-ε)) := by ring
        _ ≤ (1 + ε) / ε * M := mul_le_mul_of_nonneg_left (hQT T) (by positivity)
    dsimp only [δ]
    linarith
  constructor
  · rintro ⟨B, hB⟩
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    refine ⟨(Real.sqrt (max B 0) + δ) ^ 2, fun T => ?_⟩
    have hint0 := pmBezoutInteriorPronicEnergy_nonneg ε T
    have hsqrt_cof :
        Real.sqrt (sieveTruncatedPronicEnergy (Q T) T (pmCofactorRealWeight ε (Q T))) ≤
          Real.sqrt (max B 0) :=
      Real.sqrt_le_sqrt ((hB T).trans (le_max_left _ _))
    have hlo := (abs_le.mp (hgap T)).1
    have hsqrt_int : Real.sqrt (pmBezoutInteriorPronicEnergy ε T) ≤
        Real.sqrt (max B 0) + δ := by linarith
    calc
      pmBezoutInteriorPronicEnergy ε T
        = (Real.sqrt (pmBezoutInteriorPronicEnergy ε T)) ^ 2 := (Real.sq_sqrt hint0).symm
      _ ≤ (Real.sqrt (max B 0) + δ) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_int 2
  · rintro ⟨B, hB⟩
    have hB0 : 0 ≤ max B 0 := le_max_right _ _
    refine ⟨(Real.sqrt (max B 0) + δ) ^ 2, fun T => ?_⟩
    have hcof0 := sieveTruncatedPronicEnergy_nonneg (Q T) T (pmCofactorRealWeight ε (Q T))
    have hsqrt_int :
        Real.sqrt (pmBezoutInteriorPronicEnergy ε T) ≤ Real.sqrt (max B 0) :=
      Real.sqrt_le_sqrt ((hB T).trans (le_max_left _ _))
    have hhi := (abs_le.mp (hgap T)).2
    have hsqrt_cof :
        Real.sqrt (sieveTruncatedPronicEnergy (Q T) T (pmCofactorRealWeight ε (Q T))) ≤
          Real.sqrt (max B 0) + δ := by linarith
    calc
      sieveTruncatedPronicEnergy (Q T) T (pmCofactorRealWeight ε (Q T))
        = (Real.sqrt (sieveTruncatedPronicEnergy (Q T) T (pmCofactorRealWeight ε (Q T)))) ^ 2 :=
          (Real.sq_sqrt hcof0).symm
      _ ≤ (Real.sqrt (max B 0) + δ) ^ 2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) hsqrt_cof 2

/-! ## §2. Complete Signed Interior Energy Calibration, 25-Entry Vaughan Gram Matrix, Birth-Delayed Envelope, and All-Damping Vinogradov–Korobov Laws -/

/-- **[New formulation] Explicit Coefficient-Free Bound on the Birth-Delayed Growing-Cutoff
Interior Sawtooth Progression (`abs_pmBezoutInteriorPrefix_birthDelayed_compensated_le_five_halves_mul`):**
For every `ε ≥ 0`, `d, T, L : ℕ`, at the growing cutoff `N = (d + 2) * L`, the birth-delayed
compensated progression of `pmBezoutInteriorPrefix ε` with harmonic density tail and
`birthDelayedInteriorJumpDrift` retained is bounded by `(5 / 2) * (d + 2) * L`. -/
theorem abs_pmBezoutInteriorPrefix_birthDelayed_compensated_le_five_halves_mul
    {ε : ℝ} (hε : 0 ≤ ε) (d T L : ℕ) :
    let N := (d + 2) * L
    |∑ k ∈ range L, interiorJumpCompensatedWeight ⟨d + 2, by omega⟩ T k *
      (pmBezoutInteriorPrefix ε (d + 2 - 1 + (d + 2) * k) -
        ((d + 2 - 1 + (d + 2) * k : ℕ) : ℝ) *
          (selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 -
            (RHTower.pmPowerDampedDivisorDensity ε).re) -
        birthDelayedInteriorJumpDrift N (d + 2) k (pmPowerDampedRealWeight ε))| ≤
      (5 / 2 : ℝ) * ((d + 2 : ℕ) : ℝ) * (L : ℝ) := by
  dsimp only
  refine (abs_pmBezoutInteriorPrefix_birthDelayed_compensated_le ε d T L).trans ?_
  calc
    (∑ e ∈ Icc 1 ((d + 2) * L), |pmPowerDampedRealWeight ε e| *
        (1 / ((d : ℝ) + 2) + 2 / (Nat.gcd (d + 2) e : ℝ)))
      ≤ ∑ _e ∈ Icc 1 ((d + 2) * L), (5 / 2 : ℝ) := by
        refine Finset.sum_le_sum fun e he => ?_
        have he1 : 1 ≤ e := (mem_Icc.mp he).1
        have hmu : |moebiusReal e| ≤ 1 := abs_moebiusReal_le_one' e
        have hrpow : (e : ℝ) ^ (-ε) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast he1) (by linarith)
        have hc : |pmPowerDampedRealWeight ε e| ≤ 1 := by
          unfold pmPowerDampedRealWeight
          rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _)]
          exact mul_le_one₀ hmu (Real.rpow_nonneg (Nat.cast_nonneg e) _) hrpow
        have hd_le : 1 / ((d : ℝ) + 2) ≤ 1 / 2 :=
          one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) d])
        have hgcd_pos : 1 ≤ Nat.gcd (d + 2) e := Nat.gcd_pos_of_pos_left e (by omega)
        have hgcd_le : 2 / (Nat.gcd (d + 2) e : ℝ) ≤ 2 := by
          have h1 : (1 : ℝ) ≤ (Nat.gcd (d + 2) e : ℝ) := by exact_mod_cast hgcd_pos
          exact div_le_self (by norm_num) h1
        have hpair : 1 / ((d : ℝ) + 2) + 2 / (Nat.gcd (d + 2) e : ℝ) ≤ 5 / 2 := by linarith
        calc
          |pmPowerDampedRealWeight ε e| *
              (1 / ((d : ℝ) + 2) + 2 / (Nat.gcd (d + 2) e : ℝ))
            ≤ 1 * (5 / 2) :=
              mul_le_mul hc hpair (by positivity) zero_le_one
          _ = 5 / 2 := one_mul _
    _ = (5 / 2 : ℝ) * ((d + 2 : ℕ) : ℝ) * (L : ℝ) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, Nat.cast_mul]
        ring

/-- **[New formulation] Complete Signed Interior Energy, Non-Circular Gradient Conservation, and
25-Entry Vaughan Gram Calibration (`complete_signed_interior_energy_and_vaughan_calibration`):**
Unifies at fixed sub-half damping `ε ∈ (0, 1/2)`:
1. The exact polarization between `pmPowerDampedDivisorDiscreteEnergy` and
   `pmBezoutInteriorPronicEnergy` and the uniform `O_ε(1)` summability of their difference,
2. The exact non-circular interior gradient + local-impulse conservation law,
3. The 25-entry signed Vaughan pronic Gram decomposition `E_T^{int}(ε) = ∑_i G_{i,i} + R_T^{mix}`,
   diagonal invariance under component sign flips, the `4 * (∑_j G_{k,j} - G_{k,k})` flip gap, and
   nonsummability of the squared pointwise logarithmic source majorant `pmPronicLogMajorant ε`. -/
theorem complete_signed_interior_energy_and_vaughan_calibration
    (ε : Set.Ioo (0 : ℝ) (1 / 2)) (U V : ℕ) {T : ℕ} (hT : 1 ≤ T) (k i : Fin 5) :
    (pmPowerDampedDivisorDiscreteEnergy (ε : ℝ) T - pmBezoutInteriorPronicEnergy (ε : ℝ) T =
      2 * (∑ n ∈ Icc 1 T,
        (pmBezoutInteriorPrefix (ε : ℝ) n / Real.sqrt (pronicSeq n : ℝ)) *
          (addDiff (pmActiveSawtoothComponent (ε : ℝ)) n / Real.sqrt (pronicSeq n : ℝ))) +
      pmActivePairPronicEnergy (ε : ℝ) T) ∧
    (|Real.sqrt (pmBezoutInteriorPronicEnergy (ε : ℝ) T) -
        Real.sqrt (pmPowerDampedDivisorDiscreteEnergy (ε : ℝ) T)| ≤ 1 / 2) ∧
    (∃ K : ℝ, 0 ≤ K ∧ ∀ T₀ : ℕ,
      |pmBezoutInteriorPronicEnergy (ε : ℝ) T₀ -
        pmPowerDampedDivisorDiscreteEnergy (ε : ℝ) T₀| ≤ K) ∧
    (pmBezoutInteriorGradientSum (ε : ℝ) T + 2 * pmBezoutLocalImpulseCrossSum (ε : ℝ) T =
      pmActiveDeletedCovarianceDiagonal (ε : ℝ) T +
        2 * pmPredecessorPeakMartingaleSum (ε : ℝ) T -
        pmActivePairPronicEnergy (ε : ℝ) T -
        pmInteriorActivePotential (ε : ℝ) 1 * (1 - 1 / ((T : ℝ) + 1))) ∧
    (pmBezoutInteriorPronicEnergy (ε : ℝ) T =
      (∑ j : Fin 5, pmPronicVaughanGram (ε : ℝ) U V T j j) +
        pmPronicVaughanMixedRemainder (ε : ℝ) U V T) ∧
    ((∑ n ∈ Icc 1 T,
      (if i = k then -pmPronicVaughanPiece (ε : ℝ) U V n i
       else pmPronicVaughanPiece (ε : ℝ) U V n i) ^ 2 / (pronicSeq n : ℝ)) =
      pmPronicVaughanGram (ε : ℝ) U V T i i) ∧
    (pmBezoutInteriorPronicEnergy (ε : ℝ) T -
      (∑ n ∈ Icc 1 T,
        (pmBezoutInteriorPrefix (ε : ℝ) n - 2 * pmPronicVaughanPiece (ε : ℝ) U V n k) ^ 2 /
          (pronicSeq n : ℝ)) =
      4 * ((∑ j : Fin 5, pmPronicVaughanGram (ε : ℝ) U V T k j) -
        pmPronicVaughanGram (ε : ℝ) U V T k k)) ∧
    ¬ Summable (pmPronicLogMajorant (ε : ℝ)) :=
  ⟨pmPowerDampedDivisorDiscreteEnergy_sub_interiorPronic_eq (ε : ℝ) T,
   abs_sqrt_pmBezoutInteriorPronicEnergy_sub_sqrt_le_half ε.property.1.le T,
   pmInteriorPronicEnergy_sub_source_uniformly_bounded ε,
   pmBezoutInteriorGradient_add_two_mul_localImpulse_eq_activeDeleted_add_predecessorPeak
     (ε : ℝ) hT,
   pmInteriorPronicEnergy_eq_diagonal_add_mixed (ε : ℝ) U V T,
   pmPronicVaughan_flip_diagonal (ε : ℝ) U V T k i,
   pmPronicVaughan_flip_energy_gap (ε : ℝ) U V T k,
   not_summable_pmPronicLogMajorant ε⟩

/-- **[New formulation] Complete Signed Receiver Equivalence, Zero-Width Admission, and All-Damping
Vinogradov–Korobov Band & Sub-Half-Damping Growth Laws
(`complete_signed_receiver_equivalence_and_all_damping_vk_laws`):**
Packages the complete resolution of the signed trans-horizon energy landscape in
`TransHorizonIncidenceMechanics`:
1. All five interior receiver formulations (`receiverDampings`, `interiorReceiverDampings`,
   `strictContractionDampings`, `strictInteriorContractionDampings`, `compensatedMartingaleDampings`)
   coincide at every `ε > 0`, hold unconditionally for all `ε > Θ - 1 / 2`, have common derived-set
   infimum `Θ - 1 / 2`, and are each necessary and sufficient (for all `ε > 0` or cofinally as
   `ε → 0⁺`) for `RiemannHypothesis`.
2. For every damping floor `ε₀ > 0`, both `pmBezoutInteriorPronicEnergy ε T` and
   `pmPowerDampedDivisorDiscreteEnergy ε T` are uniformly bounded across all `T : ℕ` and all
   `ε ∈ [ε₀, 1 / 2]` on the Vinogradov–Korobov band `ε ≥ 1 / 2 - κ σ(T) / (480 log T)`, while the
   Ramanujan-isometric parity twin diverges at least as `c_{ε₀} (log(T + 1) - log 100)`.
3. For every fixed `ε ∈ (0, 1 / 2)`, `pmBezoutInteriorPronicEnergy ε T` is bounded by
   `C_ε T^{1 - 2ε} exp(-κ σ(T) / 270)` for all large `T`, and its ratio against the complete-period
   primitive energy `sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)` decays as
   `O_ε(exp(-κ σ(N) / 270))`. -/
theorem complete_signed_receiver_equivalence_and_all_damping_vk_laws
    {ε₀ : ℝ} (hε₀ : 0 < ε₀) {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ((ε ∈ receiverDampings ↔ ε ∈ interiorReceiverDampings) ∧
      (ε ∈ receiverDampings ↔ ε ∈ strictContractionDampings) ∧
      (ε ∈ receiverDampings ↔ ε ∈ strictInteriorContractionDampings) ∧
      (ε ∈ receiverDampings ↔ ε ∈ compensatedMartingaleDampings)) ∧
    (sInf (derivedSet interiorReceiverDampings) = zetaZeroAbscissa - 1 / 2) ∧
    (RiemannHypothesis ↔
      ∀ η : ℝ, 0 < η → ∃ B : ℝ, ∀ T : ℕ, pmBezoutInteriorPronicEnergy η T ≤ B) ∧
    (∃ E : ℝ, 0 ≤ E ∧ ∀ (T : ℕ) (η : ℝ), ε₀ ≤ η → η ≤ 1 / 2 →
      1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ η →
        pmBezoutInteriorPronicEnergy η T ≤ E) ∧
    ((∀ η : ℝ, 0 < η → ∀ e : ℕ, 0 < e →
        |weightRamanujanCoeff (parityTwinWeight η) e| =
          |weightRamanujanCoeff (pmPowerDampedRealWeight η) e|) ∧
      ∃ E c : ℝ, 0 < c ∧ ∀ (T : ℕ) (η : ℝ), ε₀ ≤ η → η ≤ 1 / 2 →
        1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ η →
          weightPronicEnergy (pmPowerDampedRealWeight η) (dampedDensity η) T ≤ E ∧
          c * (Real.log ((T : ℝ) + 1) - Real.log 100) ≤
            weightPronicEnergy (parityTwinWeight η) (dampedDensity η) T) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, pmBezoutInteriorPronicEnergy ε T ≤
      C * (T : ℝ) ^ (1 - 2 * ε) * Real.exp (-(vkKappa * vkScale T / 270))) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, pmBezoutInteriorPronicEnergy ε N ≤
      C * Real.exp (-(vkKappa * vkScale N / 270)) *
        sievePrimitiveEnergy N (pmPowerDampedRealWeight ε)) :=
  ⟨mem_receiverDampings_iff_all_interior_forms,
   sInf_derivedSet_interiorReceiverDampings_eq_zetaZeroAbscissa_sub_half,
   riemannHypothesis_iff_forall_pos_pmBezoutInteriorPronicEnergy_bounded,
   exists_interiorPronic_le_on_vinogradovKorobovBand_of_pos hε₀,
   parityPair_separated_on_vinogradovKorobovBand_of_pos hε₀,
   eventually_interiorPronic_le_growth_of_pos hε hε2,
   eventually_interiorPronic_le_mul_periodEnergy_of_pos hε hε2⟩

/-! ## §3. Selectivity of the Conservation and Dissipation Laws (Topic 7.9.4) -/

/-- **[New formulation] Class I Selectivity — Beurling-Universal Multiplicative Laws
(`selectivity_class_I_beurling_universal_laws`):**
On **every** abstract Beurling generalized prime system `B : BeurlingSystem` (free commutative
monoid `Multiset B.Label` with `1 < B.labelNorm p`), five conservation and decomposition laws hold
purely from multiplicative divisor geometry, without any additive integer-lattice or successor
structure:
1. Generalized Möbius divisor inversion `∑_{d ∣ g} B.moebius d = δ_{g,0}`,
2. Strict transverse log-submodularity of the squarefree Gibbs weight `B.gibbsWeight`,
3. Divided-log prime-power completion `log N(p) / log N(p^k) = 1 / k`,
4. Uniform depth-zero Gamma gauge enclosure in `[1, 2]` after truncating labels below `2`, and
5. The exact three-sector zero/one/higher large-label Buchstab decomposition of `B.phi x`. -/
theorem selectivity_class_I_beurling_universal_laws
    (B : BeurlingSystem) [DecidableEq B.Label]
    (hdisc : B.IsDiscrete) {C : ℝ} (hC : B.HasLinearCounting C)
    (g : Multiset B.Label) {x : ℝ} (hx : 0 < x) (z : ℝ)
    {A D : Finset B.Label} (hAD : (A \ D).Nonempty) (hDA : (D \ A).Nonempty)
    (p : B.Label) {k : ℕ} (hk : k ≠ 0) (q : (B.truncate 2).Label) :
    ((∑ d ∈ g.powerset.toFinset, B.moebius d = if g = 0 then 1 else 0) ∧
      (B.gibbsWeight x (A ∪ D) * B.gibbsWeight x (A ∩ D) <
        B.gibbsWeight x A * B.gibbsWeight x D) ∧
      (Real.log (B.labelNorm p) / Real.log (B.intNorm (Multiset.replicate k p)) = 1 / (k : ℝ)) ∧
      ((B.truncate 2).gammaGauge q ∈ Set.Icc (1 : ℝ) 2)) ∧
    (B.phi x = B.apertureSum z x + B.oneLargeSum z x + B.higherLargeSum z x ∧
      B.oneLargeSum z x =
        -∑' p : {p : B.Label // z < B.labelNorm p},
          B.apertureSum z (B.labelNorm (p : B.Label) * x) ∧
      B.phi x =
        B.apertureSum z x -
          (∑' p : {p : B.Label // z < B.labelNorm p},
            B.apertureSum z (B.labelNorm (p : B.Label) * x)) +
          B.higherLargeSum z x) :=
  ⟨beurling_universal_gibbs_and_gauge_package B g hx hAD hDA p hk q,
   beurling_zero_one_higher_large_label_decomposition B hdisc hC hx z⟩

/-- **[New formulation] Class II Selectivity — Sign-Blind and `(ℤ/2ℤ)^N` Parity-Orbit Invariant Laws
(`selectivity_class_II_signBlind_and_parityOrbit_laws`):**
On `ℕ`, the following quadratic and first-octave laws depend only on squared Selberg coordinates
`Y_{N,c}(q)²` or pointwise magnitudes `|f(k)|`, and are therefore invariant under `(ℤ/2ℤ)^N`
sign twists (cannot distinguish a paid row from its unpaid parity twin):
1. All eleven complete-period quadratic functionals (`selbergTotientDiagonalForm`, `sieveVariance`,
   `bezoutCoprimeQuadraticForm`, `sieveSuccessorCovariance`, `sieveSuccessorReserve`,
   `successorPhaseLoss`, `sievePrimitiveEnergy`, `franelGcdQuadraticForm`,
   `sieveVarianceAboveParity`, `TwoLagSieve.periodCovariance N _ h` at every lag `h`, and
   `tupleVariance N _ H` for every tuple `H`) are invariant under `scaledSelbergRow N c ε` for any
   sign pattern `ε(q)² = 1`.
2. Conversely, two rows at cutoff `N` with equal complete-period means have equal complete-period
   lag covariances on `Icc 1 N` **if and only if** they lie in the same `(ℤ/2ℤ)^{N-1}` Selberg
   sign-character orbit.
3. Every diagonal entry `pmPronicVaughanGram ε U V T i i` of the 25-entry Vaughan pronic Gram
   matrix is invariant under flipping the sign of any Vaughan piece `k : Fin 5`.
4. The first-octave step defect `f(k)f(k + 1) - f(k)² ≤ 0` holds for every sequence with
   `f(k)² = |f(k)|`, regardless of whether `∑ f(k)` cancels (`μ`) or drifts linearly (`μ²`, `1`). -/
theorem selectivity_class_II_signBlind_and_parityOrbit_laws
    {N : ℕ} (hN : 1 ≤ N) (c c₁ c₂ : ℕ → ℝ)
    (hmean : finiteHarmonicSum N c₁ = finiteHarmonicSum N c₂)
    {εs : ℕ → ℝ} (hεs : ∀ q ∈ Finset.Icc 1 N, εs q ^ 2 = 1)
    (ε : ℝ) (U V T : ℕ) (k i : Fin 5)
    {a b : ℝ} (ha : a ^ (2 : ℕ) = |a|) (hb : |b| ≤ 1) :
    (selbergTotientDiagonalForm N (scaledSelbergRow N c εs) = selbergTotientDiagonalForm N c ∧
      sieveVariance N (scaledSelbergRow N c εs) = sieveVariance N c ∧
      bezoutCoprimeQuadraticForm N (scaledSelbergRow N c εs) = bezoutCoprimeQuadraticForm N c ∧
      sieveSuccessorCovariance N (scaledSelbergRow N c εs) = sieveSuccessorCovariance N c ∧
      sieveSuccessorReserve N (scaledSelbergRow N c εs) = sieveSuccessorReserve N c ∧
      successorPhaseLoss N (scaledSelbergRow N c εs) = successorPhaseLoss N c ∧
      sievePrimitiveEnergy N (scaledSelbergRow N c εs) = sievePrimitiveEnergy N c ∧
      franelGcdQuadraticForm N (scaledSelbergRow N c εs) = franelGcdQuadraticForm N c ∧
      sieveVarianceAboveParity N (scaledSelbergRow N c εs) = sieveVarianceAboveParity N c ∧
      (∀ h : ℕ, TwoLagSieve.periodCovariance N (scaledSelbergRow N c εs) h =
        TwoLagSieve.periodCovariance N c h) ∧
      (∀ H : Finset ℕ, tupleVariance N (scaledSelbergRow N c εs) H = tupleVariance N c H)) ∧
    ((∀ g ∈ Finset.Icc 1 N,
        TwoLagSieve.periodCovariance N c₁ g = TwoLagSieve.periodCovariance N c₂ g) ↔
      ∃ ε' : ℕ → ℝ, ε' 1 = 1 ∧ (∀ q, ε' q ^ 2 = 1) ∧
        ∀ d ∈ Finset.Icc 1 N, c₂ d = scaledSelbergRow N c₁ ε' d) ∧
    ((∑ n ∈ Finset.Icc 1 T,
      (if i = k then -pmPronicVaughanPiece ε U V n i
       else pmPronicVaughanPiece ε U V n i) ^ 2 / (pronicSeq n : ℝ)) =
      pmPronicVaughanGram ε U V T i i) ∧
    (a * b - a ^ (2 : ℕ) ≤ 0) := by
  refine ⟨completePeriodQuadraticForms_scaledSelbergRow hN c hεs,
    periodCovariance_eq_iff_exists_scaledSelbergRow hmean,
    pmPronicVaughan_flip_diagonal ε U V T k i, ?_⟩
  have hprod : a * b ≤ |a| * |b| := by
    rw [← abs_mul]
    exact le_abs_self (a * b)
  have hle : |a| * |b| ≤ |a| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg a)
  linarith

/-- **[New formulation] Class III Selectivity — `ℤ`-Lattice Bézout-Selective Laws Specific to `ℕ`
(`selectivity_class_III_bezout_successor_selective_laws`):**
In contrast to Class I (Beurling-universal) and Class II (sign-blind), the following laws require
consecutive coprimality `gcd(n, n + 1) = 1` and the additive Bézout identity `pa - qb = 1` on `ℕ`,
and directly read the signed Selberg coordinates:
1. **Zero-diagonal pronic Abel summation
   (`sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_bezout_interior`)**:
   Because no `d ≥ 2` divides both `n` and `n + 1`, the diagonal square `(s_{N,c}(n + 1) - Y_N(1))²`
   cancels identically out of `W_{N,c}(n + 1)² - W_{N,c}(n)²`, expressing the pronic energy of
   `W_{N,c}` purely in terms of successor covariances, harmonic-divided forward differences, and
   twice the doubly-inactive Bézout interior martingale.
2. **Horizon-free two-layer Bézout shell decomposition
   (`pmPowerDampedCenteredDivisorPrefix_eq_first_and_second_layer_add_fourStep`)**:
   `pmPowerDampedCenteredDivisorPrefix ε n` splits into the first active-pair layer
   `addDiff (pmActiveSawtoothComponent ε) n`, the second Bézout shell
   `pmSecondLayerSawtoothComponent ε (n - 1) - pmSecondLayerSawtoothComponent ε (n + 2)` (which
   vanishes at `m = 1, 2`), and `pmFourStepBezoutInteriorPrefix ε n`.
3. **Conditional jump-orbit mean classification (`interiorJumpOrbitMean_eq_zero_iff`,
   `interiorJumpOrbitMean_double`)**:
   Along `n_k = d - 1 + dk`, the interior modulus `e` has zero conditional mean iff
   `gcd(d, e) = 1 ∨ gcd(d, e) = e`, while `e = 2(d + 2)` has positive mean `1 / (8(d + 2))`.
4. **Least Bézout successor-seed coupling (`beurling_invariance_vs_bezout_successor_seed_wall1_bridge`)**:
   Coprime scales `p, q > 1` couple through the least Bézout seed `pa = qb + 1` in the continuous
   Hilbert dilation profile.
5. **Trans-horizon sign separation of parity-isometric rows
   (`primePairWeights_completePeriod_coincide`, `primePairWeights_transHorizon_separated`)**:
   `primePairPlusWeight N` and `primePairMinusWeight N` (`N ≥ 3`) have identical complete-period
   quadratic forms at every lag and tuple, yet separate in pointwise response at `k = N + 1`, prefix
   discrepancy at `M = 3N + 1`, von Mangoldt readout (`log 2 + log 3` vs. `log 2 - log 3`), and
   renormalized prefix defect (`-4` vs. `0`). -/
theorem selectivity_class_III_bezout_successor_selective_laws
    {N : ℕ} (hN : 3 ≤ N) (c : ℕ → ℝ) {T : ℕ} (hT : 1 ≤ T)
    (ε : ℝ) (n d : ℕ) (d₀ e₀ : ℕ+)
    {pCop qCop : ℕ} (hpCop : 1 < pCop) (hqCop : 1 < qCop) (hcop : Nat.Coprime pCop qCop) :
    ((∑ m ∈ Finset.Icc 1 T,
        weightedCenteredSawtoothSum N c m ^ (2 : ℕ) / (pronicSeq m : ℝ)) +
      weightedCenteredSawtoothSum N c T ^ (2 : ℕ) / ((T : ℝ) + 1) =
      weightedCenteredSawtoothSum N c 1 ^ (2 : ℕ) +
      (∑ m ∈ Finset.Icc 1 (T - 1),
        ((sieveSeq N c m - selbergMultiplesCoord N c 1) *
          (sieveSeq N c (m + 1) - selbergMultiplesCoord N c 1)) / ((m : ℝ) + 1)) +
      (∑ m ∈ Finset.Icc 1 (T - 1),
        ((sieveSeq N c (m + 1) - selbergMultiplesCoord N c 1) *
          addDiff (sieveSeq N (fun j => c j / (j : ℝ))) m) / ((m : ℝ) + 1)) +
      2 * ∑ m ∈ Finset.Icc 1 (T - 1),
        (sieveSeq N c (m + 1) - selbergMultiplesCoord N c 1) *
          bezoutInteriorSawtoothSum N c m / ((m : ℝ) + 1)) ∧
    (pmPowerDampedCenteredDivisorPrefix ε n =
      addDiff (pmActiveSawtoothComponent ε) n +
        (pmSecondLayerSawtoothComponent ε (n - 1) -
          pmSecondLayerSawtoothComponent ε (n + 2)) +
        pmFourStepBezoutInteriorPrefix ε n ∧
      pmSecondLayerSawtoothComponent ε 1 = 0 ∧
      pmSecondLayerSawtoothComponent ε 2 = 0) ∧
    ((interiorJumpOrbitMean d₀ e₀ = 0 ↔ Nat.gcd d₀ e₀ = 1 ∨ Nat.gcd d₀ e₀ = e₀) ∧
      interiorJumpOrbitMean (d + 2) (2 * (d + 2)) = 1 / (8 * ((d : ℝ) + 2))) ∧
    (1 ≤ (leastSuccessorSeed pCop qCop).1 ∧ (leastSuccessorSeed pCop qCop).1 ≤ qCop ∧
      1 ≤ (leastSuccessorSeed pCop qCop).2 ∧
      pCop * (leastSuccessorSeed pCop qCop).1 = qCop * (leastSuccessorSeed pCop qCop).2 + 1) ∧
    ((∀ h : ℕ, TwoLagSieve.periodCovariance N (primePairPlusWeight N) h =
        TwoLagSieve.periodCovariance N (primePairMinusWeight N) h) ∧
      sieveSeq N (primePairPlusWeight N) (N + 1) ≠
        sieveSeq N (primePairMinusWeight N) (N + 1) ∧
      sievePrefixDiscrepancy N (3 * N + 1) (primePairPlusWeight N) -
        sievePrefixDiscrepancy N (3 * N + 1) (primePairMinusWeight N) = -2 ∧
      vonMangoldtReadout N (primePairPlusWeight N) -
        vonMangoldtReadout N (primePairMinusWeight N) = 2 * Real.log 3 ∧
      sieveRenormalizedPrefixDefect N 1 (primePairPlusWeight N) = -4 ∧
      sieveRenormalizedPrefixDefect N 1 (primePairMinusWeight N) = 0) := by
  have hcoinc := primePairWeights_completePeriod_coincide hN
  have hsep := primePairWeights_transHorizon_separated hN
  have hseed := (beurling_invariance_vs_bezout_successor_seed_wall1_bridge 0 0 0 0 hpCop hqCop hcop).2.2.1
  refine ⟨sum_weightedCenteredSawtoothSum_sq_div_pronicSeq_add_terminal_eq_bezout_interior N c hT,
    ⟨pmPowerDampedCenteredDivisorPrefix_eq_first_and_second_layer_add_fourStep ε n,
     pmSecondLayerSawtoothComponent_one ε,
     pmSecondLayerSawtoothComponent_two ε⟩,
    ⟨interiorJumpOrbitMean_eq_zero_iff d₀ e₀,
     interiorJumpOrbitMean_double d⟩,
    hseed,
    ⟨hcoinc.2.2.2.2.2.2.2.1.2.2.2.2,
     hsep.2.1,
     hsep.2.2.2.1,
     by linarith [hsep.2.2.2.2.1, hsep.2.2.2.2.2.1],
     hsep.2.2.2.2.2.2.2.2.2.1,
     hsep.2.2.2.2.2.2.2.2.2.2⟩⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
