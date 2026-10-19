import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiSelectedCoefficientTransportAndRecovery
import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonRadicalStateAndDefectNormalForm
import GaloisForLFunctions.BiScaleUncertainty.RoutePMVarianceToWitnessSynthesisAndCriticalStripBridge

/-!
# Cofactor Squarefree Fermi Sampling, Fixed-Point Transport Characterization, and Pronic Observability

This module resolves Research Question 2 of `TransHorizonIncidenceMechanics/README.md` (§4) by
proving that the actual Route PM power-damped Ramanujan cofactor row
`pmCofactorRealWeight ε Q d := (pmPowerDampedRamanujanCofactor ε Q d).re` is strictly supported on
squarefree divisors, lies in the fixed-point subspace of the dyadic coefficient transport
`fermiSelectedCoefficient N`, and therefore achieves exact horizon-independent Fermi boundary pair
recovery and the uniform constant-`4` pronic energy sandwich without valuation-depth loss.

## Main Results

1. **Exact Fixed-Point Subspace Characterization of `fermiSelectedCoefficient N`**:
   - `fermiSelectedCoefficient_eq_self_of_four_dvd_zero` and
     `fermiAliasResidual_eq_self_of_four_dvd_zero`: whenever `c` vanishes on multiples of `4`, both
     `fermiSelectedCoefficient N c` and `fermiAliasResidual N c` coincide identically with `c`.
   - `fermiSelectedCoefficient_eq_self_iff_four_dvd_zero`: on `Icc 1 N`,
     `∀ d ∈ Icc 1 N, fermiSelectedCoefficient N c d = c d` holds **if and only if**
     `∀ d ∈ Icc 1 N, 4 ∣ d → c d = 0`.
   - `fermiSelectedCoefficient_energy_isometry_of_four_dvd_zero` and
     `fermiSelectedReading_eq_sieveSeq_of_four_dvd_zero`: on the four-free subspace, the `3/2`
     inverse coefficient-transport constant collapses to `1` (exact `L²` coefficient isometry) and
     `fermiSelectedReading N c n = sieveSeq N c (n + 1)` holds directly.

2. **Exact Fermi Sampling & Pronic Observability on the Route PM Cofactor Row**:
   - `pmCofactorRealWeight_eq_zero_of_not_squarefree`,
     `pmCofactorRealWeight_eq_zero_of_four_dvd`, and
     `fermiFourFreeWeight_pmCofactorRealWeight`: `pmCofactorRealWeight ε Q` is strictly
     squarefree-supported and four-free (`fermiFourFreeWeight c = c`).
   - `fermiSelectedCoefficient_pmCofactorRealWeight` and
     `fermiSelectedReading_pmCofactorRealWeight`: the dyadic transport acts as the identity on
     `pmCofactorRealWeight ε Q` at every horizon `N` and cutoff `Q`.
   - `fermiBoundaryJump_four_pmCofactorRealWeight` and
     `fermiBoundaryJump_pair_recovery_pmCofactorRealWeight`: exact trans-horizon pair recovery of
     all odd and even sieve values of the cofactor row.
   - `pmCofactorRealWeight_pronic_energy_bounds` and
     `four_mul_fermiSelectedPronicEnergy_pmCofactorRealWeight_sub_eq`: uniform constant-`4` pronic
     energy equivalence and exact positive slack identity at every horizon `N` and cutoff `Q`.
   - `sieveSeq_pmCofactorRealWeight_horizonRadicalState`: all cofactor sieve observations factor
     through the finite primorial radical state `horizonRadicalState N k`.
-/

open Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BezoutValuationIncidence
open RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Fixed-Point Subspace Characterization of `fermiSelectedCoefficient N` -/

/-- If `2 ∣ d`, then `4 ∣ 2 * d`. -/
private theorem four_dvd_two_mul_of_two_dvd {d : ℕ} (hd : 2 ∣ d) : 4 ∣ 2 * d := by
  rcases hd with ⟨k, rfl⟩
  exact ⟨k, by ring⟩

/-- **Fixed-Point Property on Four-Free Weights (`fermiSelectedCoefficient_eq_self_of_four_dvd_zero`):**
If `c` vanishes on multiples of `4` up to `N` (`∀ d ∈ Icc 1 N, 4 ∣ d → c d = 0`), then for every
`d ∈ Icc 1 N`, `fermiSelectedCoefficient N c d = c d`. -/
theorem fermiSelectedCoefficient_eq_self_of_four_dvd_zero (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d ∈ Finset.Icc 1 N, 4 ∣ d → c d = 0) {d : ℕ} (hd : d ∈ Finset.Icc 1 N) :
    fermiSelectedCoefficient N c d = c d := by
  unfold fermiSelectedCoefficient
  by_cases h2 : 2 ∣ d
  · rw [if_pos h2]
    have h2d_zero : (if 2 * d ≤ N then c (2 * d) else 0) = 0 := by
      split_ifs with h2N
      · have hmem : 2 * d ∈ Finset.Icc 1 N :=
          Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hd).1; omega, h2N⟩
        exact hc (2 * d) hmem (four_dvd_two_mul_of_two_dvd h2)
      · rfl
    rw [h2d_zero, sub_zero]
    split_ifs with h4
    · rw [hc d hd h4, mul_zero]
    · ring
  · rw [if_neg h2]

/-- Global version: if `∀ d, 4 ∣ d → c d = 0`, then `fermiSelectedCoefficient N c d = c d` for all
`N, d : ℕ`. -/
theorem fermiSelectedCoefficient_eq_self_of_forall_four_dvd_zero (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, 4 ∣ d → c d = 0) (d : ℕ) :
    fermiSelectedCoefficient N c d = c d := by
  unfold fermiSelectedCoefficient
  by_cases h2 : 2 ∣ d
  · rw [if_pos h2]
    have h2d : c (2 * d) = 0 := hc (2 * d) (four_dvd_two_mul_of_two_dvd h2)
    rw [h2d, ite_self, sub_zero]
    split_ifs with h4
    · rw [hc d h4, mul_zero]
    · ring
  · rw [if_neg h2]

/-- If `∀ d, 4 ∣ d → c d = 0`, then `fermiAliasResidual N c d = c d` for all `N, d : ℕ`. -/
theorem fermiAliasResidual_eq_self_of_forall_four_dvd_zero (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d : ℕ, 4 ∣ d → c d = 0) (d : ℕ) :
    fermiAliasResidual N c d = c d := by
  unfold fermiAliasResidual
  by_cases h2 : 2 ∣ d
  · rw [if_pos h2]
    have h2d : c (2 * d) = 0 := hc (2 * d) (four_dvd_two_mul_of_two_dvd h2)
    rw [h2d, ite_self, mul_zero, sub_zero]
    split_ifs with h4
    · rw [hc d h4, mul_zero]
    · ring
  · rw [if_neg h2]

/-- **Exact Fixed-Point Subspace Characterization (`fermiSelectedCoefficient_eq_self_iff_four_dvd_zero`):**
At any horizon `N : ℕ`, a coefficient vector `c` is fixed by `fermiSelectedCoefficient N` on
`Icc 1 N` if and only if `c` vanishes on all multiples of `4` in `Icc 1 N`. -/
theorem fermiSelectedCoefficient_eq_self_iff_four_dvd_zero (N : ℕ) (c : ℕ → ℝ) :
    (∀ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d = c d) ↔
      ∀ d ∈ Finset.Icc 1 N, 4 ∣ d → c d = 0 := by
  constructor
  · intro hfix d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro hd h4
      obtain ⟨k, rfl⟩ := h4
      have hd1 := (Finset.mem_Icc.mp hd).1
      have hdN := (Finset.mem_Icc.mp hd).2
      let e := 2 * k
      have he_mem : e ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have he2 : 2 ∣ e := ⟨k, rfl⟩
      have h2e_eq : 2 * e = 4 * k := by dsimp [e]; ring
      have h2e_le : 2 * e ≤ N := by omega
      have hfe := hfix e he_mem
      unfold fermiSelectedCoefficient at hfe
      rw [if_pos he2, if_pos h2e_le, h2e_eq] at hfe
      by_cases h4e : 4 ∣ e
      · have he_lt : e < 4 * k := by dsimp [e]; omega
        have hce0 : c e = 0 := ih e he_lt he_mem h4e
        rw [if_pos h4e, hce0] at hfe
        linarith
      · rw [if_neg h4e] at hfe
        linarith
  · exact fun hc d hd => fermiSelectedCoefficient_eq_self_of_four_dvd_zero N hc hd

/-- **Exact `L²` Coefficient Isometry on the Four-Free Subspace
(`fermiSelectedCoefficient_energy_isometry_of_four_dvd_zero`):**
Whenever `c` vanishes on multiples of `4` in `Icc 1 N`, the `3/2` transport bound becomes an exact
equality of `L²` coefficient energies. -/
theorem fermiSelectedCoefficient_energy_isometry_of_four_dvd_zero (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d ∈ Finset.Icc 1 N, 4 ∣ d → c d = 0) :
    (∑ d ∈ Finset.Icc 1 N, fermiSelectedCoefficient N c d ^ 2) =
      ∑ d ∈ Finset.Icc 1 N, c d ^ 2 := by
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [fermiSelectedCoefficient_eq_self_of_four_dvd_zero N hc hd]

/-- On the four-free subspace, the physical selected trace `fermiSelectedReading N c n` equals the
literal sieve value `sieveSeq N c (n + 1)` without coefficient transport distortion. -/
theorem fermiSelectedReading_eq_sieveSeq_of_four_dvd_zero (N : ℕ) {c : ℕ → ℝ}
    (hc : ∀ d ∈ Finset.Icc 1 N, 4 ∣ d → c d = 0) (n : ℕ) :
    fermiSelectedReading N c n = sieveSeq N c (n + 1) := by
  rw [fermiSelectedReading_eq_sieveSeq]
  unfold sieveSeq
  refine Finset.sum_congr rfl fun d hd => ?_
  exact fermiSelectedCoefficient_eq_self_of_four_dvd_zero N hc (Finset.mem_filter.mp hd).1

/-! ## §2. Squarefree Support & Fixed-Point Transport on the Route PM Cofactor Row -/

/-- The real divisor weight of the Route PM power-damped Ramanujan cofactor at cutoff `Q`. -/
def pmCofactorRealWeight (ε : ℝ) (Q d : ℕ) : ℝ :=
  (pmPowerDampedRamanujanCofactor ε Q d).re

/-- **Strict Squarefree Support of `pmCofactorRealWeight`
(`pmCofactorRealWeight_eq_zero_of_not_squarefree`):**
For every `ε : ℝ`, cutoff `Q : ℕ`, and non-squarefree `d : ℕ`, `pmCofactorRealWeight ε Q d = 0`. -/
theorem pmCofactorRealWeight_eq_zero_of_not_squarefree (ε : ℝ) (Q : ℕ) {d : ℕ}
    (hd : ¬ Squarefree d) :
    pmCofactorRealWeight ε Q d = 0 := by
  unfold pmCofactorRealWeight pmPowerDampedRamanujanCofactor
  have hsum :
      (∑ m ∈ Finset.Icc 1 (Q / d),
        (ArithmeticFunction.moebius m : ℂ) * pmPowerDampedRamanujanWeight ε (d * m)) = 0 := by
    refine Finset.sum_eq_zero fun m _ => ?_
    have hdm : ¬ Squarefree (d * m) := fun hs => hd hs.of_mul_left
    rw [pmPowerDampedRamanujanWeight_eq_zero_of_not_squarefree ε hdm, mul_zero]
  rw [hsum, mul_zero, Complex.zero_re]

/-- **Four-Divisible Annihilation of `pmCofactorRealWeight`
(`pmCofactorRealWeight_eq_zero_of_four_dvd`):**
For every `ε : ℝ`, `Q : ℕ`, and `d : ℕ` with `4 ∣ d`, `pmCofactorRealWeight ε Q d = 0`. -/
theorem pmCofactorRealWeight_eq_zero_of_four_dvd (ε : ℝ) (Q : ℕ) {d : ℕ} (h4 : 4 ∣ d) :
    pmCofactorRealWeight ε Q d = 0 := by
  refine pmCofactorRealWeight_eq_zero_of_not_squarefree ε Q ?_
  intro hsq
  have h22 : 2 * 2 ∣ d := by simpa using h4
  exact Nat.prime_two.not_isUnit (hsq 2 h22)

/-- `pmCofactorRealWeight ε Q` is a fixed point of `fermiFourFreeWeight`. -/
@[simp]
theorem fermiFourFreeWeight_pmCofactorRealWeight (ε : ℝ) (Q : ℕ) :
    fermiFourFreeWeight (pmCofactorRealWeight ε Q) = pmCofactorRealWeight ε Q := by
  funext d
  unfold fermiFourFreeWeight
  split_ifs with h4
  · exact (pmCofactorRealWeight_eq_zero_of_four_dvd ε Q h4).symm
  · rfl

/-- **Exact Transport Identity on `pmCofactorRealWeight`
(`fermiSelectedCoefficient_pmCofactorRealWeight`):**
At every observation horizon `N : ℕ` and cofactor cutoff `Q : ℕ`, the dyadic coefficient transport
`fermiSelectedCoefficient N` acts as the exact identity on `pmCofactorRealWeight ε Q`. -/
@[simp]
theorem fermiSelectedCoefficient_pmCofactorRealWeight (ε : ℝ) (N Q d : ℕ) :
    fermiSelectedCoefficient N (pmCofactorRealWeight ε Q) d = pmCofactorRealWeight ε Q d :=
  fermiSelectedCoefficient_eq_self_of_forall_four_dvd_zero N
    (fun _ h4 => pmCofactorRealWeight_eq_zero_of_four_dvd ε Q h4) d

/-- The valuation alias residual `fermiAliasResidual N` on `pmCofactorRealWeight ε Q` coincides
identically with `pmCofactorRealWeight ε Q`. -/
@[simp]
theorem fermiAliasResidual_pmCofactorRealWeight (ε : ℝ) (N Q d : ℕ) :
    fermiAliasResidual N (pmCofactorRealWeight ε Q) d = pmCofactorRealWeight ε Q d :=
  fermiAliasResidual_eq_self_of_forall_four_dvd_zero N
    (fun _ h4 => pmCofactorRealWeight_eq_zero_of_four_dvd ε Q h4) d

/-- The selected Fermi reading trace of `pmCofactorRealWeight ε Q` equals its literal sieve trace
at every horizon `N` and cutoff `Q`. -/
theorem fermiSelectedReading_pmCofactorRealWeight (ε : ℝ) (N Q n : ℕ) :
    fermiSelectedReading N (pmCofactorRealWeight ε Q) n =
      sieveSeq N (pmCofactorRealWeight ε Q) (n + 1) :=
  fermiSelectedReading_eq_sieveSeq_of_four_dvd_zero N
    (fun _ _ h4 => pmCofactorRealWeight_eq_zero_of_four_dvd ε Q h4) n

/-! ## §3. Exact All-Horizon Pair Recovery, Constant-`4` Pronic Energy Bounds, & Radical State -/

/-- **All-Horizon Even Sieve Recovery at Multiples of Four (`fermiBoundaryJump_four_pmCofactorRealWeight`):**
For every `ε : ℝ`, observation horizon `N : ℕ`, cofactor cutoff `Q : ℕ`, and `m : ℕ`:
`fermiBoundaryJump N (pmCofactorRealWeight ε Q) (4 * m + 4) = sieveSeq N (pmCofactorRealWeight ε Q) (2 * m + 2)`. -/
theorem fermiBoundaryJump_four_pmCofactorRealWeight (ε : ℝ) (N Q m : ℕ) :
    fermiBoundaryJump N (pmCofactorRealWeight ε Q) (4 * m + 4) =
      sieveSeq N (pmCofactorRealWeight ε Q) (2 * m + 2) := by
  have h := fermiBoundaryJump_four_fourFreeWeight N (pmCofactorRealWeight ε Q) m
  simpa only [fermiFourFreeWeight_pmCofactorRealWeight] using h

/-- **Exact All-Horizon Pair Recovery on `pmCofactorRealWeight`
(`fermiBoundaryJump_pair_recovery_pmCofactorRealWeight`):**
Odd Fermi boundaries and four-divisible Fermi boundaries recover all odd and even sieve values of
the Route PM cofactor row at every horizon `N` and cutoff `Q`. -/
theorem fermiBoundaryJump_pair_recovery_pmCofactorRealWeight (ε : ℝ) (N Q m : ℕ) :
    (-fermiBoundaryJump N (pmCofactorRealWeight ε Q) (2 * m + 1),
      fermiBoundaryJump N (pmCofactorRealWeight ε Q) (4 * m + 4)) =
    (sieveSeq N (pmCofactorRealWeight ε Q) (2 * m + 1),
      sieveSeq N (pmCofactorRealWeight ε Q) (2 * m + 2)) := by
  rw [fermiBoundaryJump_odd, neg_neg, fermiBoundaryJump_four_pmCofactorRealWeight]

/-- **Uniform Constant-`4` Pronic Energy Sandwich on `pmCofactorRealWeight`
(`pmCofactorRealWeight_pronic_energy_bounds`):**
Resolving Research Question 2 of `TransHorizonIncidenceMechanics/README.md`: for every `ε : ℝ`,
observation horizon `N : ℕ`, cofactor cutoff `Q : ℕ`, and finite pair set `S : Finset ℕ`:
`fermiSelectedPronicEnergy N (pmCofactorRealWeight ε Q) S ≤ sievePairedPronicEnergy N (pmCofactorRealWeight ε Q) S ≤ 4 * fermiSelectedPronicEnergy N (pmCofactorRealWeight ε Q) S`. -/
theorem pmCofactorRealWeight_pronic_energy_bounds (ε : ℝ) (N Q : ℕ) (S : Finset ℕ) :
    fermiSelectedPronicEnergy N (pmCofactorRealWeight ε Q) S ≤
        sievePairedPronicEnergy N (pmCofactorRealWeight ε Q) S ∧
      sievePairedPronicEnergy N (pmCofactorRealWeight ε Q) S ≤
        4 * fermiSelectedPronicEnergy N (pmCofactorRealWeight ε Q) S := by
  have h := fermiFourFree_pronic_energy_bounds N (pmCofactorRealWeight ε Q) S
  simpa only [fermiFourFreeWeight_pmCofactorRealWeight] using h

/-- For every squarefree integer `d`, `moebiusReal d * moebiusReal d = 1`. -/
private theorem moebiusReal_mul_self_of_squarefree' {d : ℕ} (hd : Squarefree d) :
    moebiusReal d * moebiusReal d = 1 := by
  unfold moebiusReal
  rw [ArithmeticFunction.moebius_apply_of_squarefree hd]
  push_cast
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- `pmCofactorRealWeight ε Q` admits the canonical Möbius-twist representation
`d ↦ moebiusReal d * (moebiusReal d * pmCofactorRealWeight ε Q d)`. -/
private theorem pmCofactorRealWeight_eq_moebius_twist (ε : ℝ) (Q : ℕ) :
    pmCofactorRealWeight ε Q =
      fun d => moebiusReal d * (moebiusReal d * pmCofactorRealWeight ε Q d) := by
  funext d
  by_cases hd : Squarefree d
  · rw [← mul_assoc, moebiusReal_mul_self_of_squarefree' hd, one_mul]
  · rw [pmCofactorRealWeight_eq_zero_of_not_squarefree ε Q hd, mul_zero, mul_zero]

/-- **Exact Pronic Observation Slack on `pmCofactorRealWeight`
(`four_mul_fermiSelectedPronicEnergy_pmCofactorRealWeight_sub_eq`):**
For every `ε : ℝ`, `N, Q : ℕ`, and `S : Finset ℕ`, `4 * fermiSelectedPronicEnergy - sievePairedPronicEnergy`
on `pmCofactorRealWeight ε Q` equals the exact positive odd-plus-even pronic slack sum. -/
theorem four_mul_fermiSelectedPronicEnergy_pmCofactorRealWeight_sub_eq
    (ε : ℝ) (N Q : ℕ) (S : Finset ℕ) :
    4 * fermiSelectedPronicEnergy N (pmCofactorRealWeight ε Q) S -
      sievePairedPronicEnergy N (pmCofactorRealWeight ε Q) S =
    ∑ m ∈ S,
      (3 * sieveSeq N (pmCofactorRealWeight ε Q) (2 * m + 1) ^ 2 /
        (pronicSeq (2 * m + 1) : ℝ) +
      sieveSeq N (pmCofactorRealWeight ε Q) (2 * m + 2) ^ 2 /
        ((pronicSeq (2 * m + 2) : ℝ) * (4 * (m : ℝ) + 5))) := by
  have h := four_mul_fermiSelectedPronicEnergy_sub_sievePaired_eq N
    (fun d => moebiusReal d * pmCofactorRealWeight ε Q d) S
  simpa only [← pmCofactorRealWeight_eq_moebius_twist ε Q] using h

/-- **Primorial Radical State Factorization of the Cofactor Sieve
(`sieveSeq_pmCofactorRealWeight_horizonRadicalState`):**
At every observation horizon `N : ℕ` and cofactor cutoff `Q : ℕ`, the sieve response of
`pmCofactorRealWeight ε Q` at `k` equals its response at the canonical squarefree state
`horizonRadicalState N k = gcd(k, primorial N)`. -/
theorem sieveSeq_pmCofactorRealWeight_horizonRadicalState (ε : ℝ) (N Q k : ℕ) :
    sieveSeq N (pmCofactorRealWeight ε Q) (horizonRadicalState N k) =
      sieveSeq N (pmCofactorRealWeight ε Q) k :=
  sieveSeq_horizonRadicalState N k (fun _ hd => pmCofactorRealWeight_eq_zero_of_not_squarefree ε Q hd)

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
