import GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicPrimeFrequencyRigidity
import GaloisForLFunctions.HTGeometry.ExponentialSeriesFiberwise

/-! Positive algebraic prime atoms separate the top degree of an exponential-series product.
At a frequency on distinct primes, shorter tuples contribute nothing and equal-length tuples
are exactly the permutations of the target atoms. -/

open Finset
open scoped Classical
set_option autoImplicit false
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicPrimeFrequency
noncomputable section

/-- The signed frequency appearing on physical vertical lines. -/
def tuplePhase {N : ℕ} (u : Fin N → PrimeAtom) : ℝ := -∑ i, atomFrequency (u i)

/-- The frequency fiber on distinct primes consists exactly of permuted target atoms. -/
def permutationFiberEquiv {D : ℕ} (v : Fin D → PrimeAtom)
    (hv : Function.Injective (fun j => (v j).1)) :
    Equiv.Perm (Fin D) ≃ {u : Fin D → PrimeAtom // tuplePhase u = tuplePhase v} := by
  let f : Equiv.Perm (Fin D) → {u : Fin D → PrimeAtom // tuplePhase u = tuplePhase v} :=
    fun e => ⟨fun i => v (e i),congrArg Neg.neg
      (Fintype.sum_equiv e _ _ (fun _ => rfl))⟩
  apply Equiv.ofBijective f
  constructor
  · intro e g h
    apply Equiv.ext
    intro i
    exact hv (congrArg (fun u => (u.val i).1) h)
  · intro u
    obtain ⟨e,he⟩ := (atom_tuple_frequency_iff le_rfl u.val v hv).mp
      (neg_injective u.property)
    exact ⟨e,Subtype.ext (funext (fun i => (he i).symm))⟩

theorem permutationFiberEquiv_apply {D : ℕ} (v : Fin D → PrimeAtom)
    (hv : Function.Injective (fun j => (v j).1)) (e : Equiv.Perm (Fin D)) :
    (permutationFiberEquiv v hv e).val = fun i => v (e i) := rfl

/-- No lower-degree product contributes to a frequency on `D` distinct primes. -/
theorem fiberAmplitude_eq_zero_of_shorter {N D : ℕ} (hND : N < D)
    (B : (Fin N → PrimeAtom) → ℂ) (v : Fin D → PrimeAtom)
    (hv : Function.Injective (fun j => (v j).1)) :
    fiberAmplitude B tuplePhase (tuplePhase v) = 0 := by
  letI : IsEmpty {u : Fin N → PrimeAtom // tuplePhase u = tuplePhase v} :=
    ⟨fun u => atom_tuple_frequency_ne_of_shorter hND u.val v hv
      (neg_injective u.property)⟩
  unfold fiberAmplitude
  exact tsum_empty

/-- The top-degree coefficient is the exact finite permutation sum. -/
theorem fiberAmplitude_eq_sum_permutations {D : ℕ}
    (B : (Fin D → PrimeAtom) → ℂ) (v : Fin D → PrimeAtom)
    (hv : Function.Injective (fun j => (v j).1)) :
    fiberAmplitude B tuplePhase (tuplePhase v) =
      ∑ e : Equiv.Perm (Fin D), B (fun i => v (e i)) := by
  unfold fiberAmplitude
  rw [← (permutationFiberEquiv v hv).tsum_eq
    (fun u : {u : Fin D → PrimeAtom // tuplePhase u = tuplePhase v} => B u.val)]
  rw [tsum_fintype]
  rfl

#print axioms permutationFiberEquiv
#print axioms fiberAmplitude_eq_zero_of_shorter
#print axioms fiberAmplitude_eq_sum_permutations
end
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.AlgebraicPrimeFrequency
