import GaloisForLFunctions.HTGeometry.CenteredPolynomialOverCoefficients
import GaloisForLFunctions.HTGeometry.PolynomialBaseChange

/-!
# The centered polynomial generates the whole centered field

The roots of the centered polynomial in the centered field are exactly the centered roots, and those
generate the centered field over the coefficient field.  So the root field of the centered
polynomial is everything.

Consequently the Galois group of the centered polynomial, in the form the base change step consumes
it, is the symmetric group on the roots.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

variable {K : Type*} [Field K] [CharZero K] {d : ℕ}

/-- **The roots of the centered polynomial are the centered roots.** -/
theorem rootSet_centeredMonicE :
    (centeredMonicE K d).rootSet (centeredField K d) = Set.range (centeredRootIn K d) := by
  ext a
  rw [Polynomial.mem_rootSet']
  constructor
  · rintro ⟨-, ha⟩
    have hev : Polynomial.eval a (centeredMonicL K d) = 0 := by
      rw [← map_centeredMonicE, Polynomial.eval_map, ← Polynomial.aeval_def]
      exact ha
    rw [centeredMonicL, Polynomial.eval_prod] at hev
    obtain ⟨i, -, hi⟩ := Finset.prod_eq_zero_iff.1 hev
    exact ⟨i, (sub_eq_zero.1 (by simpa using hi)).symm⟩
  · rintro ⟨i, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [map_centeredMonicE]
      exact monic_centeredMonicL.ne_zero
    · rw [Polynomial.aeval_def, ← Polynomial.eval_map, map_centeredMonicE]
      exact eval_centeredMonicL_root i

/-- **The root field of the centered polynomial is the whole centered field.** -/
theorem rootField_centeredMonicE_eq_top :
    rootField (centeredCoeffField K d) (L := centeredField K d) (centeredMonicE K d) = ⊤ := by
  rw [rootField, rootSet_centeredMonicE]
  exact adjoin_centeredRootIn_over_coeff_eq_top

/-- The root field, identified with the centered field. -/
noncomputable def centeredRootFieldEquiv (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    rootField (centeredCoeffField K d) (L := centeredField K d) (centeredMonicE K d) ≃ₐ[
      centeredCoeffField K d] centeredField K d :=
  by
  rw [rootField_centeredMonicE_eq_top]
  exact IntermediateField.topEquiv

/-- **The Galois group of the centered polynomial is the symmetric group on its roots**, in the form
the base change step consumes. -/
noncomputable def centeredRootFieldPermEquiv (K : Type*) [Field K] [CharZero K] (d : ℕ) :
    (rootField (centeredCoeffField K d) (L := centeredField K d) (centeredMonicE K d) ≃ₐ[
        centeredCoeffField K d]
      rootField (centeredCoeffField K d) (L := centeredField K d) (centeredMonicE K d)) ≃*
      Equiv.Perm (Fin d) :=
  (AlgEquiv.autCongr (centeredRootFieldEquiv K d)).trans (centeredGaloisEquiv K d).symm

end GaloisForLFunctions.HTGeometry
