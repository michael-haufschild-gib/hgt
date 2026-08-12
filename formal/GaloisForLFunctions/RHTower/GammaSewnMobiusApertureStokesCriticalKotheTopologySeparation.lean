import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesCriticalClockNonclosability
import GaloisForLFunctions.RHTower.GammaSewnMobiusApertureStokesPositiveChamber

/-!
# Critical Hardy--Köthe topology separation

P-G74's actual-prime graph-null witnesses are embedded into the Deninger prime-log height Köthe
source on the two corresponding positive Kummer axes.  Although their reciprocal-prime Hardy
images tend to zero, their first Köthe height seminorm is uniformly greater than `1/14`.

Thus the stronger source topology retains exactly the critical half-height information erased by
Hardy compression.  The proposed graph/Köthe survivor is thereby validated against the killing
sequence itself, rather than merely postulated.

No Xi zero, RH premise, numerical computation, fitted parameter, or added axiom enters.
-/

open Filter Topology

namespace RHTower

noncomputable section

open GaloisForLFunctions

def primeCriticalStokesKotheWitness (p : Nat.Primes) : DeningerHeightKothe :=
  (((p.1 : ℝ) /
      gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p : ℝ) : ℂ) •
    (deningerKotheDelta deningerHeightKotheData
        (gammaSewnMobiusApertureStokesPrimePowerAxis (p, 0)) -
      deningerKotheDelta deningerHeightKotheData
        (gammaSewnMobiusApertureStokesPrimePowerAxis (farPrime p, 0)))

theorem farPrime_ne (p : Nat.Primes) : farPrime p ≠ p := by
  intro h
  have hsq := farPrime_sq_lt p
  rw [h] at hsq
  nlinarith [p.2.two_le]

theorem criticalStokesPrimeAxis_ne_farAxis (p : Nat.Primes) :
    gammaSewnMobiusApertureStokesPrimePowerAxis (p, 0) ≠
      gammaSewnMobiusApertureStokesPrimePowerAxis (farPrime p, 0) := by
  exact gammaSewnMobiusApertureStokesPrimePowerAxis_injective.ne
    (by intro h; exact farPrime_ne p (congrArg Prod.fst h).symm)

theorem deningerHeight_criticalStokesPrimeAxis (p : Nat.Primes) :
    deningerHeight (gammaSewnMobiusApertureStokesPrimePowerAxis (p, 0)) = (p : ℝ) := by
  simp [gammaSewnMobiusApertureStokesPrimePowerAxis, deningerHeight,
    deningerHeightNat, deningerAbsExponent, primeProduct,
    Finsupp.prod_single_index]

theorem primeCriticalStokesKotheWitness_primeAxis (p : Nat.Primes) :
    ((primeCriticalStokesKotheWitness p : DeningerHeightKothe) :
        DeningerPrimeLattice → ℂ)
      (gammaSewnMobiusApertureStokesPrimePowerAxis (p, 0)) =
      ((p.1 : ℝ) /
        gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p : ℝ) := by
  simp [primeCriticalStokesKotheWitness, deningerKotheDelta_coe,
    criticalStokesPrimeAxis_ne_farAxis p]

theorem one_fourteenth_lt_deningerHeightSeminorm_one_primeCriticalStokesKotheWitness
    (p : Nat.Primes) :
    1 / 14 < deningerHeightSeminorm 1 (primeCriticalStokesKotheWitness p) := by
  let P : ℝ := p.1
  let r : ℝ := criticalStokesNode p
  let W : ℝ := gammaSewnMobiusApertureStokesInverseTilt (1 / 2) p
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hP1 : 1 < P := by dsimp [P]; exact_mod_cast p.2.one_lt
  have hr0 : 0 < r := criticalStokesNode_pos p
  have hr1 : r < 1 :=
    (criticalStokesNode_lt_five_sevenths p).trans (by norm_num)
  have hr2 : r ^ 2 = P⁻¹ := by simpa [r, P] using criticalStokesNode_sq p
  have hW0 : 0 < W := gammaSewnMobiusApertureStokesInverseTilt_pos (by norm_num) p
  have hW : W ≤ 14 * Real.log P / r := by
    simpa [W, P, r] using criticalStokesInverseTilt_upper p
  have hlog : Real.log P ≤ P := Real.log_le_sub_one_of_pos hP0 |>.trans (by linarith)
  have hWcoarse : W ≤ 14 * P / r := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hlog (by norm_num)) hr0.le |>.trans' hW
  have hPr : 1 < P * r := by
    have hPrr : P * r ^ 2 = 1 := by
      rw [hr2]
      exact mul_inv_cancel₀ hP0.ne'
    nlinarith [mul_pos hP0 hr0]
  have hratio : 1 / 14 < P ^ 2 / W := by
    rw [div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 14) hW0]
    have hmul := mul_le_mul_of_nonneg_left hWcoarse (by norm_num : (0 : ℝ) ≤ 14)
    have hscaled := mul_lt_mul_of_pos_left hPr (mul_pos (by norm_num : (0 : ℝ) < 14) hP0)
    field_simp [hr0.ne'] at hmul hscaled
    nlinarith
  have hcoord := deningerHeightSeminorm_coord_le 1
    (primeCriticalStokesKotheWitness p)
    (gammaSewnMobiusApertureStokesPrimePowerAxis (p, 0))
  rw [deningerHeight_criticalStokesPrimeAxis, pow_one,
    primeCriticalStokesKotheWitness_primeAxis,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hP0 hW0)] at hcoord
  change P * (P / W) ≤ _ at hcoord
  calc
    1 / 14 < P ^ 2 / W := hratio
    _ = P * (P / W) := by ring
    _ ≤ _ := hcoord

theorem not_deningerKotheTendsto_primeCriticalStokesKotheNullSequence_zero :
    ¬ DeningerKotheTendsto deningerHeightKotheData
      (fun n => primeCriticalStokesKotheWitness (nthPrimePoint n)) 0 := by
  intro h
  obtain ⟨N, hN⟩ := h 1 (1 / 14) (by norm_num)
  have hsmall := hN N le_rfl
  rw [sub_zero] at hsmall
  change deningerHeightSeminorm 1
    (primeCriticalStokesKotheWitness (nthPrimePoint N)) < 1 / 14 at hsmall
  have hlarge :=
    one_fourteenth_lt_deningerHeightSeminorm_one_primeCriticalStokesKotheWitness
      (nthPrimePoint N)
  linarith

end

end RHTower
