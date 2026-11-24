import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.StridedDigits.Block
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Radix

/-! # The unique complement of one strided prime digit -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems

open InverseSpectrum.ShellMixing

def strideLabel (q : Nat.Primes) (a d : ℕ+) (i : Fin d.val) := primeRayLabel q (a.val*i.val)

def strideTail (q : Nat.Primes) (a d : ℕ+) := Set.range (liftLabel q (blockStart a d))

theorem stride_exact (q : Nat.Primes) (a d : ℕ+) :
    exactLabelProduct (strideLabel q a d) (fun n : strideTail q a d => n.val) := by
  have h : Function.Bijective
      (fun v : Fin d.val × (Fin a.val × ℕ) => a.val*v.1.val+blockStart a d v.2) := by
    rw [← funext (strideEquiv_apply a d)]
    exact (strideEquiv a d).bijective
  exact exact_range_right (lift_exact q (a := fun i : Fin d.val => a.val*i.val) (c := blockStart a d) h)

theorem stride_complement_iff (q : Nat.Primes) (a d : ℕ+) (B : Set ℕ+) :
    exactLabelProduct (strideLabel q a d) (fun n : B => n.val) ↔ B = strideTail q a d :=
  ⟨fun h => complement_unique h (stride_exact q a d),fun h => h ▸ stride_exact q a d⟩

theorem strideTail_ray (q : Nat.Primes) (a d : ℕ+) (k : ℕ) :
    primeRayLabel q k ∈ strideTail q a d ↔ k ∈ Set.range (blockStart a d) := by
  constructor
  · rintro ⟨⟨v,c⟩,he⟩
    have hc := congrArg (primeCoordinates q) he
    change primeCoordinates q ((primeCoordinates q).symm (blockStart a d v,c)) = _ at hc
    rw [Equiv.apply_symm_apply,primeCoordinates_ray] at hc
    exact ⟨v,congrArg Prod.fst hc⟩
  · rintro ⟨v,rfl⟩
    refine ⟨(v,⟨0,rfl⟩),(primeCoordinates q).injective ?_⟩
    change primeCoordinates q ((primeCoordinates q).symm _) = _
    rw [Equiv.apply_symm_apply,primeCoordinates_ray]

#print axioms stride_exact
#print axioms stride_complement_iff
#print axioms strideTail_ray

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems
