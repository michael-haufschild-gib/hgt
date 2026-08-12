import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalKotheTopologySeparation
import GaloisForLFunctions.RHTower.ArithmeticSchurRenormalizationLaw

/-!
# Gamma-valuation Schur Köthe-vector no-go and dual survivor

Finite coherent Gamma-valuation Schur prefixes are placed on their literal positive Kummer axes.
Each newly exposed valuation coordinate has exactly the same strictly positive first Deninger
height-seminorm cost.  The prefix sequence is therefore not Köthe-Cauchy: the completed coherent
state cannot be a rapid source vector.

The same infinite coordinate family nevertheless defines a continuous functional on the Köthe
source, bounded by the zeroth seminorm.  Thus the exact positive survivor is a mixed rigging:
Gamma-Schur completion belongs in `K_H'`, acting on `K_H`, rather than inside `K_H` itself.

No Xi zero, RH premise, numerical computation, fitted parameter, or added axiom enters.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions

def gammaValuationKothePrefix (p : Nat.Primes) (N : ℕ) : DeningerHeightKothe :=
  ∑ e ∈ Finset.range N,
    (xiTransversePrimeHalfShiftedValuationCoordinate p e : ℂ) •
      deningerKotheDelta deningerHeightKotheData
        (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))

theorem deningerHeight_gammaValuationAxis (p : Nat.Primes) (e : ℕ) :
    deningerHeight (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e)) =
      (p : ℝ) ^ (e + 1) := by
  have habs : deningerAbsExponent
      (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e)) =
        Finsupp.single p (e + 1) := by
    ext q
    by_cases hqp : q = p
    · subst q
      simp [gammaSewnMobiusApertureStokesPrimePowerAxis, deningerAbsExponent]
      omega
    · simp [gammaSewnMobiusApertureStokesPrimePowerAxis, deningerAbsExponent, hqp]
  rw [deningerHeight, deningerHeightNat, habs]
  unfold primeProduct
  rw [Finsupp.prod_single_index (by simp)]
  simp

theorem xiTransversePrimeHalfShiftedValuationCoordinate_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < xiTransversePrimeHalfShiftedValuationCoordinate p e := by
  rw [xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement]
  exact mul_pos
    (Real.sqrt_pos.2 (xiTransversePrimeApertureDiskNode_pos 1 p))
    (mul_pos
      (sub_pos.mpr (xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p))
      (pow_pos (xiTransversePrimeApertureDiskNode_pos 1 p) e))

theorem gammaValuationKothePrefix_succ_sub (p : Nat.Primes) (N : ℕ) :
    gammaValuationKothePrefix p (N + 1) - gammaValuationKothePrefix p N =
      (xiTransversePrimeHalfShiftedValuationCoordinate p N : ℂ) •
        deningerKotheDelta deningerHeightKotheData
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, N)) := by
  rw [gammaValuationKothePrefix, gammaValuationKothePrefix,
    Finset.sum_range_succ]
  abel

theorem deningerHeightSeminorm_one_gammaValuationKothePrefix_succ_sub
    (p : Nat.Primes) (N : ℕ) :
    deningerHeightSeminorm 1
        (gammaValuationKothePrefix p (N + 1) - gammaValuationKothePrefix p N) =
      (p : ℝ) * Real.sqrt ((p : ℝ)⁻¹) * (1 - (p : ℝ)⁻¹) := by
  rw [gammaValuationKothePrefix_succ_sub, map_smul_eq_mul,
    show deningerHeightSeminorm 1
        (deningerKotheDelta deningerHeightKotheData
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, N))) =
        deningerHeightKotheData.w 1
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, N)) by
      exact deningerKotheSeminorm_delta deningerHeightKotheData 1 _,
    deningerHeightKotheData_w, deningerHeight_gammaValuationAxis, pow_one,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (xiTransversePrimeHalfShiftedValuationCoordinate_pos p N),
    xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [pow_succ, inv_pow]
  field_simp [hp0]

def gammaValuationKotheStepSize (p : Nat.Primes) : ℝ :=
  (p : ℝ) * Real.sqrt ((p : ℝ)⁻¹) * (1 - (p : ℝ)⁻¹)

theorem gammaValuationKotheStepSize_pos (p : Nat.Primes) :
    0 < gammaValuationKotheStepSize p := by
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.one_lt
  rw [gammaValuationKotheStepSize]
  exact mul_pos (mul_pos hp0 (Real.sqrt_pos.2 (inv_pos.mpr hp0)))
    (sub_pos.mpr ((inv_lt_one₀ hp0).2 hp1))

theorem not_deningerKotheCauchy_gammaValuationKothePrefix (p : Nat.Primes) :
    ¬ DeningerKotheCauchy deningerHeightKotheData
      (gammaValuationKothePrefix p) := by
  intro h
  let c := gammaValuationKotheStepSize p
  have hc : 0 < c := gammaValuationKotheStepSize_pos p
  obtain ⟨N, hN⟩ := h 1 (c / 2) (by positivity)
  have hsmall := hN (N + 1) (by omega) N le_rfl
  change deningerHeightSeminorm 1
    (gammaValuationKothePrefix p (N + 1) - gammaValuationKothePrefix p N) < c / 2 at hsmall
  rw [deningerHeightSeminorm_one_gammaValuationKothePrefix_succ_sub] at hsmall
  change c < c / 2 at hsmall
  linarith

theorem xiTransversePrimeHalfShiftedValuationCoordinate_lt_one
    (p : Nat.Primes) (e : ℕ) :
    xiTransversePrimeHalfShiftedValuationCoordinate p e < 1 := by
  let q := xiTransversePrimeApertureDiskNode 1 p
  have hq0 : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hq1 : q < 1 := xiTransversePrimeApertureDiskNode_lt_one (by norm_num) p
  have hsqrt : Real.sqrt q < 1 := by
    nlinarith [Real.sq_sqrt hq0.le, Real.sqrt_nonneg q]
  have hgap : 0 < (1 - q) * q ^ e ∧ (1 - q) * q ^ e ≤ 1 := by
    constructor
    · positivity
    · exact mul_le_one₀ (by linarith) (pow_nonneg hq0.le _)
        (pow_le_one₀ hq0.le hq1.le)
  rw [xiTransversePrimeHalfShiftedValuationCoordinate,
    xiTransversePrimeValuationIncrement]
  change Real.sqrt q * ((1 - q) * q ^ e) < 1
  calc
    Real.sqrt q * ((1 - q) * q ^ e) < 1 * ((1 - q) * q ^ e) :=
      mul_lt_mul_of_pos_right hsqrt hgap.1
    _ ≤ 1 := by simpa using hgap.2

def gammaValuationKotheDualPairing
    (p : Nat.Primes) (a : DeningerHeightKothe) : ℂ :=
  ∑' e : ℕ, (xiTransversePrimeHalfShiftedValuationCoordinate p e : ℂ) *
    (a : DeningerPrimeLattice → ℂ)
      (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))

theorem gammaValuationAxis_injective (p : Nat.Primes) :
    Function.Injective
      (fun e : ℕ => gammaSewnMobiusApertureStokesPrimePowerAxis (p, e)) := by
  intro e f h
  have hpair := gammaSewnMobiusApertureStokesPrimePowerAxis_injective h
  exact congrArg Prod.snd hpair

theorem summable_gammaValuationKotheDualPairing
    (p : Nat.Primes) (a : DeningerHeightKothe) :
    Summable (fun e : ℕ =>
      (xiTransversePrimeHalfShiftedValuationCoordinate p e : ℂ) *
        (a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))) := by
  have hbase : Summable (fun e : ℕ =>
      ‖(a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      (gammaValuationAxis_injective p)
  refine Summable.of_norm_bounded hbase fun e => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (xiTransversePrimeHalfShiftedValuationCoordinate_pos p e)]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (xiTransversePrimeHalfShiftedValuationCoordinate_lt_one p e).le

theorem norm_gammaValuationKotheDualPairing_le
    (p : Nat.Primes) (a : DeningerHeightKothe) :
    ‖gammaValuationKotheDualPairing p a‖ ≤ deningerHeightSeminorm 0 a := by
  have hpair := summable_gammaValuationKotheDualPairing p a
  have haxis : Summable (fun e : ℕ =>
      ‖(a : DeningerPrimeLattice → ℂ)
        (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖) :=
    (deningerHeightKothe_summable_norm a).comp_injective
      (gammaValuationAxis_injective p)
  calc
    ‖gammaValuationKotheDualPairing p a‖ ≤
        ∑' e : ℕ, ‖(xiTransversePrimeHalfShiftedValuationCoordinate p e : ℂ) *
          (a : DeningerPrimeLattice → ℂ)
            (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖ :=
      norm_tsum_le_tsum_norm hpair.norm
    _ ≤ ∑' e : ℕ, ‖(a : DeningerPrimeLattice → ℂ)
          (gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))‖ := by
      refine Summable.tsum_le_tsum (fun e => ?_) hpair.norm haxis
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (xiTransversePrimeHalfShiftedValuationCoordinate_pos p e)]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (xiTransversePrimeHalfShiftedValuationCoordinate_lt_one p e).le
    _ ≤ ∑' m : DeningerPrimeLattice, ‖(a : DeningerPrimeLattice → ℂ) m‖ := by
      exact haxis.tsum_le_tsum_of_inj
        (fun e : ℕ => gammaSewnMobiusApertureStokesPrimePowerAxis (p, e))
        (gammaValuationAxis_injective p) (fun _ _ => norm_nonneg _)
        (fun _ => le_rfl) (deningerHeightKothe_summable_norm a)
    _ = deningerHeightSeminorm 0 a := (deningerHeightSeminorm_zero_eq a).symm

end

end RHTower
