import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Nilpotence of Laurent polynomials is coefficientwise

A Laurent polynomial with exponents in an arbitrary product of copies of
`ℤ` is nilpotent exactly when all its coefficients are nilpotent. For
necessity, reduce coefficients modulo each prime ideal: the resulting
Laurent ring is a domain, so the image vanishes. The prime-intersection
criterion then gives coefficient nilpotence. Conversely, the finite sum of
nilpotent monomials is nilpotent.

Thus this Laurent ring is reduced exactly when its coefficient ring is
reduced. The coefficient ring is an arbitrary commutative ring, and the
coordinate index need not be finite.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {A ι : Type*} [CommRing A]

/-- Nilpotence forces every coefficient to vanish modulo every prime ideal. -/
theorem laurent_isNilpotent_coeff (f : AddMonoidAlgebra A (ι → ℤ))
    (hf : IsNilpotent f) (q : ι → ℤ) : IsNilpotent (f.coeff q) := by
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  letI := hJ
  let F := AddMonoidAlgebra.mapRingHom (ι → ℤ) (Ideal.Quotient.mk J)
  have hz : F f = 0 := (hf.map F).eq_zero
  have he := congrArg (fun p : AddMonoidAlgebra (A ⧸ J) (ι → ℤ) => p.coeff q) hz
  change (AddMonoidAlgebra.mapRingHom (ι → ℤ) (Ideal.Quotient.mk J) f).coeff q = _ at he
  rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero] at he
  exact Ideal.Quotient.eq_zero_iff_mem.mp he

/-- Laurent nilpotence is exactly coefficientwise nilpotence. -/
theorem laurent_isNilpotent_iff (f : AddMonoidAlgebra A (ι → ℤ)) :
    IsNilpotent f ↔ ∀ q, IsNilpotent (f.coeff q) := by
  classical
  constructor
  · exact fun h q => laurent_isNilpotent_coeff f h q
  · intro h
    have he : f = ∑ q ∈ f.coeff.support, AddMonoidAlgebra.single q (f.coeff q) :=
      (AddMonoidAlgebra.sum_coeff_single f).symm
    rw [he]
    apply isNilpotent_sum
    intro q _
    obtain ⟨n, hn⟩ := h q
    refine ⟨n, ?_⟩
    rw [AddMonoidAlgebra.single_pow, hn, AddMonoidAlgebra.single_zero]

/-- Laurent extension of a reduced commutative ring is reduced. -/
theorem laurent_isReduced [IsReduced A] : IsReduced (AddMonoidAlgebra A (ι → ℤ)) := by
  constructor
  intro f hf
  ext q
  exact (laurent_isNilpotent_coeff f hf q).eq_zero

/-- Laurent extension both preserves and reflects reducedness. -/
theorem laurent_isReduced_iff : IsReduced (AddMonoidAlgebra A (ι → ℤ)) ↔ IsReduced A := by
  constructor
  · intro h
    letI := h
    constructor
    intro a ha
    have hz : (AddMonoidAlgebra.singleZeroRingHom a : AddMonoidAlgebra A (ι → ℤ)) = 0 :=
      (ha.map AddMonoidAlgebra.singleZeroRingHom).eq_zero
    have he := congrArg (fun f : AddMonoidAlgebra A (ι → ℤ) => f.coeff 0) hz
    simpa using he
  · intro h
    letI := h
    exact laurent_isReduced

end GaloisForLFunctions.ArithmeticHarmonicAnalysis

#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.laurent_isNilpotent_iff
#print axioms GaloisForLFunctions.ArithmeticHarmonicAnalysis.laurent_isReduced_iff
