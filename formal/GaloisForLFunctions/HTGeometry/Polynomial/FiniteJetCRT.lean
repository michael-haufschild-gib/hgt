import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Polynomial Chinese remainder interpolation over a field

Powers of the point ideals at distinct scalars are pairwise coprime.
Consequently, one polynomial realizes arbitrary residue classes at all
points of a finite family, in any characteristic.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open Polynomial Function
variable {K ι : Type*} [Field K] [Finite ι]

/-- Simultaneous polynomial residues modulo powers of distinct point ideals. -/
theorem exists_polynomial_sub_mem_power_linear_ideal
    (w : ι → K) (hw : Function.Injective w) (m : ι → ℕ) (target : ι → K[X]) :
    ∃ B : K[X], ∀ i,
      B - target i ∈ Ideal.span ({(X - C (w i)) ^ m i} : Set K[X]) := by
  let I : ι → Ideal K[X] := fun i => Ideal.span {(X - C (w i)) ^ m i}
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (pairwise_coprime_X_sub_C hw hij).pow
  simpa only [I] using Ideal.exists_forall_sub_mem_ideal hI target

/-- Divisibility form of simultaneous finite polynomial interpolation. -/
theorem exists_polynomial_power_linear_dvd_sub
    (w : ι → K) (hw : Function.Injective w) (m : ι → ℕ) (target : ι → K[X]) :
    ∃ B : K[X], ∀ i, (X - C (w i)) ^ m i ∣ B - target i := by
  obtain ⟨B, hB⟩ := exists_polynomial_sub_mem_power_linear_ideal w hw m target
  exact ⟨B, fun i => Ideal.mem_span_singleton.mp (hB i)⟩

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.exists_polynomial_power_linear_dvd_sub
