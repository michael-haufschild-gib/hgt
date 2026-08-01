import GaloisForLFunctions.HTGeometry.RadicalBaseChangeEvenCapstone
import GaloisForLFunctions.HTGeometry.RadicalRootExists
import GaloisForLFunctions.HTGeometry.RadicalRootFieldDegree

/-!
# The odd base change step from the exponent alone

An irreducible radical polynomial at an odd exponent generates an extension of odd degree, so the
quadratic subextension cut out by the discriminant cannot lie inside it and no square-class
computation is needed.

A root of the radical polynomial exists in the ambient splitting field, so the caller only has to
supply the irreducibility, the parity, and the degree of a root.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **The odd base change step, from the irreducibility and the parity of the exponent.** -/
noncomputable def radicalBaseChangeOddFromDegree {p : Polynomial F} {c : F} {n : ℕ}
    (hp : p ≠ 0) (hn : 0 < n)
    [Polynomial.IsSplittingField F L (p * (Polynomial.X ^ n - Polynomial.C c))]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    {L₀ : Type*} [Field L₀] [Algebra F L₀] [Polynomial.IsSplittingField F L₀ p]
    (ψ : (L₀ ≃ₐ[F] L₀) ≃* Equiv.Perm γ)
    (hζ : (primitiveRoots n F).Nonempty)
    (hirr : Irreducible (Polynomial.X ^ n - Polynomial.C c : Polynomial F))
    (hodd : ¬ 2 ∣ n)
    (hdeg : ∀ α : L, α ^ n = algebraMap F L c → n ≤ Module.finrank F F⟮α⟯) :
    (L ≃ₐ[rootField F (L := L) (Polynomial.X ^ n - Polynomial.C c)] L) ≃* Equiv.Perm γ := by
  have hq : (Polynomial.X ^ n - Polynomial.C c : Polynomial F) ≠ 0 :=
    (Polynomial.monic_X_pow_sub_C c (by omega)).ne_zero
  have hsplitq := splits_of_splits_mul_right (L := L) hp hq
    (Polynomial.IsSplittingField.splits' (K := F) (L := L)
      (f := p * (Polynomial.X ^ n - Polynomial.C c)))
  have hex := exists_pow_eq_mem_rootField hn hsplitq
  have hαpow : (Classical.choose hex) ^ n = algebraMap F L c := (Classical.choose_spec hex).2
  exact radicalBaseChangeOdd hp hn ψ hζ hαpow (hdeg _ hαpow)
    (not_two_dvd_finrank_rootField hp hn hζ hirr hodd)

end GaloisForLFunctions.HTGeometry
