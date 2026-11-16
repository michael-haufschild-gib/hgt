import GaloisForLFunctions.RepresentationLifting.TruncatedResolution
import GaloisForLFunctions.RepresentationLifting.OperatorKernels.IndependentPreimages

/-!
# Independent division in truncated polynomial modules

The common image must vanish, but independent preimages can have arbitrary
terminal coefficients. At depth at least the truncation length all coefficients
are free. In contrast, the only coherent backward orbit is the zero orbit.
-/

namespace GaloisForLFunctions.RepresentationLifting

open OperatorKernels ArithmeticHodgeTheoryOfDegenerations.HodgeWitt

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The truncation horizon kills the root without any compatibility assumption. -/
theorem truncatedShift_independentRoot_eq_zero (N : ℕ)
    (x : independentPreimages (truncatedShift (R := R) (M := M) N 1)) :
    x.1 0 = 0 :=
  independentRoot_eq_zero_of_pow_eq_zero _ N
    (by rw [truncatedShift_pow, truncatedShift_horizon]) x

/-- Exact coefficient classification of all independent preimages, including a zero-length jet. -/
theorem truncatedShift_independentPreimages_iff (N : ℕ) (x : ℕ → Fin N → M) :
    x ∈ independentPreimages (truncatedShift (R := R) N 1) ↔
      x 0 = 0 ∧ ∀ n (i : Fin N), i.val + n < N → x n i = 0 := by
  constructor
  · intro hx
    have hzero := truncatedShift_independentRoot_eq_zero N ⟨x, hx⟩
    refine ⟨hzero, fun n => ?_⟩
    apply (truncatedShift_eq_zero_iff N n (x n)).mp
    rw [← truncatedShift_pow]
    exact (hx n).trans hzero
  · rintro ⟨hzero, hx⟩ n
    rw [truncatedShift_pow, hzero]
    exact (truncatedShift_eq_zero_iff N n (x n)).mpr (hx n)

/-- Compatibility removes all the independent terminal-coefficient freedom. -/
theorem truncatedShift_backwardOrbit_eq_zero (N : ℕ)
    (x : backwardOrbits (truncatedShift (R := R) (M := M) N 1)) : x = 0 := by
  apply (backwardOrbits_uniform_torsion_iff _ x N).mp
  intro n
  rw [truncatedShift_pow, truncatedShift_horizon]
  rfl

#print axioms truncatedShift_independentRoot_eq_zero
#print axioms truncatedShift_independentPreimages_iff
#print axioms truncatedShift_backwardOrbit_eq_zero

end GaloisForLFunctions.RepresentationLifting
