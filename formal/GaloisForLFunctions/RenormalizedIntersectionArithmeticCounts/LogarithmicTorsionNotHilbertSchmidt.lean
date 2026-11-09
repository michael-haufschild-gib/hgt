import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.LogarithmicTorsionCompletion
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.TorsionHilbertSchmidtBoundary
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# Infinite square mass of logarithmic torsion

Even prime conductors force a divergent tame-diagonal square sum at every
logarithmic exponent. The comparison uses Euler's prime reciprocal divergence
through the existing prime-log divergence theorem. Consequently every bounded
logarithmic torsion operator lies outside the Hilbert–Schmidt class.
-/

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open HeightHomotopyArithmeticCounts ArithmeticIntersectionTheory

/-- The normalized torsion diagonal is the original tame different divided by logarithmic mass. -/
theorem logarithmicTorsionKernel_self (α : ℝ) (n : ℕ) :
    logarithmicTorsionKernel α n n=tameDifferent n/(logConductor n)^α := by
  rw [logarithmicTorsionKernel,spacingLimitKernel_self,←pow_two,logProbeWeight_sq]

/-- Squaring the diagonal doubles the logarithmic exponent. -/
theorem logarithmicTorsionKernel_self_sq (α : ℝ) (n : ℕ) :
    (logarithmicTorsionKernel α n n)^2=(tameDifferent n)^2/(logConductor n)^(2*α) := by
  rw [logarithmicTorsionKernel_self,div_pow,pow_two ((logConductor n)^α),
    ←Real.rpow_add (lt_of_lt_of_le zero_lt_one (one_le_logConductor n)),←two_mul]

/-- Even prime conductors already force infinite diagonal square mass at every logarithmic exponent. -/
theorem logarithmicTorsionDiagonal_not_summable (α : ℝ) :
    ¬Summable (fun n : ℕ => (logarithmicTorsionKernel α (n+1) (n+1))^2) := by
  intro hs
  obtain ⟨N,hN⟩ := exists_nat_gt (2*α)
  let c : ℝ := 2+Real.log 2
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < c := by dsimp only [c]; linarith only [hl2]
  let A : ℝ := (Real.log 2)^2/c^N
  have hA : 0 < A := div_pos (sq_pos_of_pos hl2) (pow_pos hc N)
  have hi : Function.Injective (fun p : Nat.Primes => 2*(p:ℕ)-1) := by
    intro p q h
    apply Subtype.ext
    have hp := p.property.pos
    have hq := q.property.pos
    omega
  have he : Summable (fun p : Nat.Primes =>
      (logarithmicTorsionKernel α (2*(p:ℕ)) (2*(p:ℕ)))^2) := by
    have h := hs.comp_injective (i := fun p : Nat.Primes => 2*(p:ℕ)-1) hi
    exact h.congr (fun p => by rw [Nat.sub_add_cancel (by have := p.property.pos; omega)])
  have ht : Tendsto (fun p : Nat.Primes => Real.log p) cofinite atTop :=
    Real.tendsto_log_atTop.comp RHTower.tendsto_prime_coe_real_cofinite_atTop
  have hbound : ∀ᶠ p : Nat.Primes in cofinite,
      A*(1/(Real.log p)^N) ≤ (logarithmicTorsionKernel α (2*(p:ℕ)) (2*(p:ℕ)))^2 := by
    filter_upwards [ht.eventually_ge_atTop 1] with p hp
    have hp0 : (0:ℝ) < p := by exact_mod_cast p.property.pos
    have hl : 0 < Real.log p := by linarith only [hp]
    have hL : 0 < logConductor (2*(p:ℕ)) :=
      lt_of_lt_of_le zero_lt_one (one_le_logConductor _)
    have hLc : logConductor (2*(p:ℕ)) ≤ c*Real.log p := by
      rw [logConductor,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ)≠0) hp0.ne']
      dsimp only [c]
      nlinarith only [hp,mul_nonneg hl2.le (sub_nonneg.mpr hp)]
    have hpow : (logConductor (2*(p:ℕ)))^(2*α) ≤ c^N*(Real.log p)^N := by
      have h := Real.rpow_le_rpow_of_exponent_le (one_le_logConductor (2*(p:ℕ))) hN.le
      rw [Real.rpow_natCast] at h
      exact h.trans (by simpa only [mul_pow] using pow_le_pow_left₀ hL.le hLc N)
    have hd := spacing_tameDifferent_double_lower (p:ℕ) p.property.pos
    have hd2 : (Real.log 2)^2 ≤ (tameDifferent (2*(p:ℕ)))^2 :=
      pow_le_pow_left₀ hl2.le hd 2
    rw [logarithmicTorsionKernel_self_sq]
    calc A*(1/(Real.log p)^N) = (Real.log 2)^2/(c^N*(Real.log p)^N) := by
          dsimp only [A]
          ring
         _ ≤ (Real.log 2)^2/(logConductor (2*(p:ℕ)))^(2*α) :=
          div_le_div_of_nonneg_left (sq_nonneg _) (Real.rpow_pos_of_pos hL _) hpow
         _ ≤ _ := div_le_div_of_nonneg_right hd2 (Real.rpow_nonneg hL.le _)
  have hsum : Summable (fun p : Nat.Primes => A*(1/(Real.log p)^N)) := by
    apply Summable.of_norm_bounded_eventually he
    filter_upwards [hbound] with p hp
    rwa [Real.norm_of_nonneg (mul_nonneg hA.le (one_div_nonneg.mpr
      (pow_nonneg (Real.log_pos (by exact_mod_cast p.property.one_lt)).le N)))]
  exact RHTower.prime_log_pow_not_summable N ((summable_mul_left_iff hA.ne').mp hsum)

/-- No bounded logarithmic torsion operator is Hilbert–Schmidt. -/
theorem logarithmicTorsionOperator_not_hilbertSchmidt (α : ℝ) (hα : 2 < α) :
    ¬(logarithmicTorsionOperator α hα).IsHilbertSchmidt := by
  intro hs
  have hh := hs.summable (weightedProbeBasis 0)
  apply logarithmicTorsionDiagonal_not_summable α
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hh
  have hi := norm_inner_le_norm (𝕜 := ℝ)
    (logarithmicTorsionOperator α hα (weightedProbeBasis 0 n)) (weightedProbeBasis 0 n)
  rw [logarithmicTorsionOperator_matrix,(weightedProbeBasis 0).orthonormal.norm_eq_one,mul_one] at hi
  simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hi 2

#print axioms logarithmicTorsionKernel_self
#print axioms logarithmicTorsionKernel_self_sq
#print axioms logarithmicTorsionDiagonal_not_summable
#print axioms logarithmicTorsionOperator_not_hilbertSchmidt
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
