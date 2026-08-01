import GaloisForLFunctions.HTGeometry.KummerBaseChangeEven
import GaloisForLFunctions.HTGeometry.EvenKummerSqrt

/-!
# Base change over a Kummer extension of even degree

The square root the even case needs is not an extra hypothesis: it is the half power of the Kummer
generator.  It squares into the base because the full power does, it lies in the extension because
the generator does, and it stays out of the base because a power below the degree cannot fall into
the base field.

So over a Kummer extension of even degree the base change step needs only the degree of the
generator and one square-class computation.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

/-- **Base change over an even Kummer extension preserves the symmetric Galois group.**  The square
root is produced from the Kummer generator rather than assumed. -/
noncomputable def kummerBaseChangeEvenGenEquiv {E M : IntermediateField F L}
    [Normal F E] [FiniteDimensional F E] [IsGalois F E]
    [FiniteDimensional F M] [IsGalois F M]
    [FiniteDimensional M L] [IsGalois M L]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm γ)
    (hEM : E ⊔ M = ⊤)
    (hnorm : (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup.Normal)
    (habel : ∀ x y : (E ≃ₐ[F] E) ⧸
      (IntermediateField.comap E.val (E ⊓ M)).fixingSubgroup, x * y = y * x)
    (hcyc : IsCyclic (M ≃ₐ[F] M))
    {β : L} {e : F} (hβE : β ∈ E) (hβsq : β * β = algebraMap F L e)
    (hβbot : β ∉ (⊥ : IntermediateField F L))
    {α : L} {c : F} {m : ℕ} (hm : 0 < m) (hαM : α ∈ M)
    (hαpow : α ^ (2 * m) = algebraMap F L c)
    (hdeg : 2 * m ≤ Module.finrank F F⟮α⟯)
    (hclass : ¬ ∃ t : F, e * c = t * t) :
    (L ≃ₐ[M] L) ≃* Equiv.Perm γ :=
  kummerBaseChangeEvenEquiv φ hEM hnorm habel hcyc hβE hβsq hβbot
    (sq_pow_half hαpow) (pow_mem hαM m)
    (pow_notMem_bot_of_finrank_le hm (by omega) hdeg) hclass

end GaloisForLFunctions.HTGeometry
