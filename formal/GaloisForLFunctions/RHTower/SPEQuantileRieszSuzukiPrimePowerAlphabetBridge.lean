import GaloisForLFunctions.RHTower.CCM.CCMFirstClockPrimePowerTowerCollapse
import GaloisForLFunctions.RHTower.Suzuki.SuzukiExteriorWienerAlphabet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiRootPortObservationGram

/-!
# SP-E prime-power atoms on Suzuki's labelled alphabet

The SP-E critical Mellin source and Suzuki's seam alphabet carry exactly the same
prime-power coefficient.  This module transports both the first-grade root-port Gram and the
finite oriented Wiener evaluation to literal SP-E atom weights, retaining each prime and depth
label.  It is a finite, coefficient-faithful source identification; it supplies neither a
cofinal bound nor a completed-current/P-Julia transport.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-- A literal SP-E atom at `p^e` is exactly Suzuki's labelled prime-power alphabet weight. -/
theorem criticalMellinAtomWeight_prime_pow_eq_suzukiPrimePowerWeight
    (p : Nat.Primes) (e : ℕ) (he : e ≠ 0) :
    criticalMellinAtomWeight ((p : ℕ) ^ e) = suzukiPrimePowerWeight (p, e) := by
  rw [criticalMellinAtomWeight_prime_pow p.property he]
  unfold criticalPrimeTowerRadius suzukiPrimePowerWeight
  have hp0 : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  rw [← Real.rpow_natCast]
  rw [← Real.rpow_mul hp0]
  have hexp : (-1 / 2 : ℝ) * (e : ℝ) = -((e : ℝ) / 2) := by ring
  rw [hexp, Real.rpow_neg hp0]
  rfl

/-- **Label-faithful first-grade SP-E observation law.**  For every finite visible prime-power
alphabet, Suzuki's two-root observation has exactly the squared SP-E source-mass Gram.  No
prime-power is merged with another: the right side remains indexed by the original labelled
finite set. -/
theorem suzukiRootPortObservation_primePower_norm_sq_eq_spEAtomWeights
    (a : ℝ) {s : Finset (Nat.Primes × ℕ)}
    (hj : ∀ pj ∈ s, 1 ≤ pj.2)
    (hvis : ∀ pj ∈ s, (((pj.1 : ℕ) : ℝ)) ^ (pj.2 : ℕ) < Real.exp (2 * a))
    (βleft βright : ℂ) :
    ‖suzukiRootPortObservation a suzukiPrimePowerStep suzukiPrimePowerWeight s
        βleft βright‖ ^ 2 =
      (∑ pj ∈ s, criticalMellinAtomWeight ((pj.1 : ℕ) ^ pj.2) ^ 2) *
        (‖βleft‖ ^ 2 + ‖βright‖ ^ 2) := by
  rw [suzukiRootPortObservation_primePower_norm_sq a hj hvis βleft βright]
  apply congrArg (fun x : ℝ => x * (‖βleft‖ ^ 2 + ‖βright‖ ^ 2))
  apply Finset.sum_congr rfl
  intro pj hpj
  rw [← suzukiPrimePowerWeight_sq,
    ← criticalMellinAtomWeight_prime_pow_eq_suzukiPrimePowerWeight pj.1 pj.2
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hj pj hpj)))]

/-- **Label-faithful SP-E Wiener source law.**  Suzuki's oriented finite Wiener alphabet is
exactly the two-sided Fourier evaluation of the finite SP-E prime-power cosine source.  The
identity is before any absolute value, scalar energy, or label quotient. -/
theorem suzukiWienerEval_atoms_eq_spEPrimePowerCosine
    {S : Finset (Nat.Primes × ℕ)} (hj : ∀ pj ∈ S, 1 ≤ pj.2) (ξ : ℝ) :
    suzukiWienerEval ξ (suzukiWienerAtoms S) =
      -2 * ∑ pj ∈ S, (criticalMellinAtomWeight ((pj.1 : ℕ) ^ pj.2) : ℂ) *
        Complex.cos ((ξ * Real.log ((pj.1 : ℕ) ^ pj.2) : ℝ)) := by
  rw [suzukiWienerEval_atoms hj ξ]
  congr 1
  apply Finset.sum_congr rfl
  intro pj hpj
  rw [← criticalMellinAtomWeight_prime_pow_eq_suzukiPrimePowerWeight pj.1 pj.2
      (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one (hj pj hpj))),
    primeSeamCoordinate_primePowerStep, ← real_log_prime_pow]

end RHTower
