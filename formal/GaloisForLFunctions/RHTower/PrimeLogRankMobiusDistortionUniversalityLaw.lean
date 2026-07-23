import GaloisForLFunctions.RHTower.CriticalPrimePoissonGCDMobiusVacuum
import GaloisForLFunctions.RHTower.PrimeLogPhaseBudget

/-!
# Prime-log rank versus Möbius phase-distortion universality law

Below a finite cutoff, independent prime logarithms give the exact phase-budget rank.  The same
prime set controls critical Poisson--GCD Möbius anisotropy.  Since every prime below `X+1` is at
most `X`, the prime-harmonic distortion lower bound dominates prime-counting rank divided by the
cutoff.  Thus one finite prime packet simultaneously has free logarithmic phase rank and a
quantitative antipodal/vacuum energy distortion forced by that rank.
-/

namespace RHTower

noncomputable section

/-- Prime-harmonic mass below `X+1` dominates prime-counting rank divided by `X`. -/
theorem primeCounting_div_le_primesBelow_primeHarmonicSum
    (X : ℕ) (hX : 2 ≤ X) :
    (Nat.primeCounting' (X + 1) : ℝ) / (X : ℝ) ≤
      ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ := by
  let S := Nat.primesBelow (X + 1)
  have hsum :
      ∑ _p ∈ S, ((X : ℝ))⁻¹ ≤ ∑ p ∈ S, ((p : ℝ))⁻¹ := by
    apply Finset.sum_le_sum
    intro p hp
    have hpPrime : p.Prime := Nat.prime_of_mem_primesBelow hp
    have hpLe : p ≤ X := by
      have hpLt : p < X + 1 := (Nat.mem_primesBelow.mp hp).1
      omega
    simpa only [one_div] using
      one_div_le_one_div_of_le (by exact_mod_cast hpPrime.pos)
        (by exact_mod_cast hpLe : (p : ℝ) ≤ X)
  have hcard : S.card = Nat.primeCounting' (X + 1) := by
    simpa only [S] using GaloisForLFunctions.primesBelow_card_eq_primeCounting' (X + 1)
  calc
    (Nat.primeCounting' (X + 1) : ℝ) / (X : ℝ) =
        ∑ _p ∈ S, ((X : ℝ))⁻¹ := by
          rw [Finset.sum_const, nsmul_eq_mul, hcard]
          simp only [Nat.cast_ofNat, div_eq_mul_inv]
    _ ≤ ∑ p ∈ S, ((p : ℝ))⁻¹ := hsum
    _ = ∑ p ∈ Nat.primesBelow (X + 1), ((p : ℝ))⁻¹ := by rfl

/-- Critical finite-prime Möbius distortion dominates one plus four times phase-budget rank per
cutoff. -/
theorem one_add_four_mul_primeCounting_div_le_primesBelow_phaseDistortion
    (X : ℕ) (hX : 2 ≤ X) :
    1 + 4 * ((Nat.primeCounting' (X + 1) : ℝ) / (X : ℝ)) ≤
      finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (X + 1)) := by
  have hprime : ∀ p ∈ Nat.primesBelow (X + 1), p.Prime :=
    fun p hp => Nat.prime_of_mem_primesBelow hp
  have hsum := primeCounting_div_le_primesBelow_primeHarmonicSum X hX
  have hdist := one_add_four_mul_primeHarmonicSum_le_phaseDistortion hprime
  nlinarith

/-- **Prime-log rank/Möbius-distortion universality law.**  Every cutoff `X ≥ 2` carries an
integer-linearly independent prime-log phase family of exact prime-counting cardinality, while
the critical antipodal/vacuum distortion of the same packet is bounded below by that rank per
cutoff. -/
theorem primeLogRank_and_mobiusPhaseDistortion
    (X : ℕ) (hX : 2 ≤ X) :
    LinearIndependent ℤ
        (fun p : ((X + 1).primesBelow : Finset ℕ) => Real.log (p : ℕ)) ∧
      1 + 4 * ((Nat.primeCounting' (X + 1) : ℝ) / (X : ℝ)) ≤
        finiteCriticalPrimeMobiusPhaseDistortion (Nat.primesBelow (X + 1)) := by
  exact ⟨GaloisForLFunctions.primeLog_primesBelow_linearIndependent (X + 1),
    one_add_four_mul_primeCounting_div_le_primesBelow_phaseDistortion X hX⟩

end

end RHTower
