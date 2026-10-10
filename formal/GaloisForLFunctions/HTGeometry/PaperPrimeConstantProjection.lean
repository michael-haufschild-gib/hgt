import GaloisForLFunctions.HTGeometry.PaperPrimeTerminatingUnits
import GaloisForLFunctions.HTGeometry.PrimeRadialTwoPacketPrimitiveRigidity

/-!
# Retraction onto the full prime constants

The existing prime-packet algebra map, at the complement of one prime,
is the literal constant-coefficient retraction for the source slice theorem.
It acts on all arithmetic functions, without a finite-prime support condition.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Excluding one prime from all prime factors is exactly nondivisibility. -/
theorem paperPrimeFactorsIn_compl_singleton_iff (p : Nat.Primes) (n : ℕ) :
    PrimeFactorsIn ({p}ᶜ : Set Nat.Primes) n ↔ ¬ (p : ℕ) ∣ n := by
  constructor
  · intro h hn
    exact h.2 p hn (Set.mem_singleton p)
  · intro hn
    refine ⟨fun h => hn (h ▸ dvd_zero _), ?_⟩
    intro q hq heq
    have hqp : q = p := heq
    subst q
    exact hn hq

/-- The native packet restriction corestricts to the actual ambient prime constants. -/
def paperPrimeConstantProjection (p : Nat.Primes) :
    ArithmeticFunction ℂ →ₐ[ℂ] paperPrimeConstants p :=
  (primePacketRestrictAlgHom ({p}ᶜ : Set Nat.Primes)).codRestrict
    (paperPrimeConstants p) (by
      intro f
      apply (paperPrimeConstants_mem_iff p _).mpr
      intro n hn
      exact primePacketRestrictAlgHom_apply_of_not_mem _ f n
        (by simpa only [paperPrimeFactorsIn_compl_singleton_iff, not_not] using hn))

/-- Projection deletes precisely the coefficients at multiples of the chosen prime. -/
@[simp] theorem paperPrimeConstantProjection_apply (p : Nat.Primes)
    (f : ArithmeticFunction ℂ) (n : ℕ) :
    (paperPrimeConstantProjection p f : ArithmeticFunction ℂ) n =
      if (p : ℕ) ∣ n then 0 else f n := by
  classical
  change primePacketRestrictAlgHom ({p}ᶜ : Set Nat.Primes) f n = _
  by_cases hn : (p : ℕ) ∣ n
  · rw [if_pos hn, primePacketRestrictAlgHom_apply_of_not_mem]
    simpa only [paperPrimeFactorsIn_compl_singleton_iff, not_not] using hn
  · rw [if_neg hn, primePacketRestrictAlgHom_apply_of_mem]
    exact (paperPrimeFactorsIn_compl_singleton_iff p n).mpr hn

/-- The projection fixes every prime constant. -/
@[simp] theorem paperPrimeConstantProjection_constant (p : Nat.Primes)
    (a : paperPrimeConstants p) :
    paperPrimeConstantProjection p (a : ArithmeticFunction ℂ) = a := by
  apply Subtype.ext
  ext n
  rw [paperPrimeConstantProjection_apply]
  split_ifs with hn
  · exact ((paperPrimeConstants_mem_iff p _).mp a.property n hn).symm
  · rfl

/-- The constant projection annihilates the literal slice coordinate. -/
@[simp] theorem paperPrimeConstantProjection_coordinate (p : Nat.Primes) :
    paperPrimeConstantProjection p (paperPrimeCoordinate p) = 0 := by
  apply Subtype.ext
  ext n
  rw [paperPrimeConstantProjection_apply]
  change (if (p : ℕ) ∣ n then 0 else paperPrimeCoordinate p n) = 0
  by_cases hn : (p : ℕ) ∣ n
  · simp [hn]
  · rw [if_neg hn]
    by_contra h
    have hp := paperPrimeCoordinate_support p h
    have hnp : (⟨n, hp⟩ : Nat.Primes) ≠ p := by
      intro heq
      have he : n = (p : ℕ) := congrArg (fun q : Nat.Primes => (q : ℕ)) heq
      exact hn (he.symm ▸ dvd_refl (p : ℕ))
    exact h ((paperPrimeCoordinate_apply_prime p ⟨n, hp⟩).trans (if_neg hnp))

/-- Projecting the exact Möbius–zeta inverse gives inverse coefficients in the constant ring. -/
theorem paperPrimeConstantProjection_moebius_mul_zeta (p : Nat.Primes) :
    paperPrimeConstantProjection p (ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
      paperPrimeConstantProjection p (ArithmeticFunction.zeta : ArithmeticFunction ℂ) = 1 := by
  rw [← map_mul, ArithmeticFunction.coe_moebius_mul_coe_zeta, map_one]

end

end GaloisForLFunctions.HTGeometry
