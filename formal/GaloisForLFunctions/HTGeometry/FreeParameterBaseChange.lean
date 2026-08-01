import GaloisForLFunctions.HTGeometry.BaseChangeRelativeClosure
import GaloisForLFunctions.HTGeometry.FractionRingConstantsEmbedding

/-!
# Adjoining a free parameter does not change the Galois group

Take the rational functions in one variable over a splitting field.  The rational functions over the
base sit inside them, and together with the splitting field they generate everything: the constants
and the variable generate every polynomial, hence every quotient of two.

The rational functions over the base carry no algebraic element beyond the base, so they meet the
splitting field in the base and restriction is an isomorphism.  So the Galois group of a separable
polynomial is unchanged when a free parameter is adjoined to the base.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The rational functions over the base, inside the rational functions over the splitting field. -/
noncomputable def fracSub (F E : Type*) [Field F] [Field E] [Algebra F E] :
    IntermediateField F (FractionRing (Polynomial E)) :=
  (fracEmbed F E).fieldRange

theorem fracEmbed_fracX : fracEmbed F E (fracX F) = fracX E := by
  show fracEmbedRingHom F E
      (algebraMap (Polynomial F) (FractionRing (Polynomial F)) Polynomial.X) = _
  rw [fracEmbedRingHom_algebraMap, Polynomial.map_X]
  rfl

theorem fracX_mem_fracSub : fracX E ∈ fracSub F E :=
  ⟨fracX F, fracEmbed_fracX⟩

/-! ## Generation -/

theorem algebraMap_polynomial_mem
    {S : IntermediateField F (FractionRing (Polynomial E))}
    (hE : ∀ a : E, algebraMap E (FractionRing (Polynomial E)) a ∈ S)
    (hX : fracX E ∈ S) (f : Polynomial E) :
    algebraMap (Polynomial E) (FractionRing (Polynomial E)) f ∈ S := by
  have himg : algebraMap (Polynomial E) (FractionRing (Polynomial E)) f =
      ∑ i ∈ f.support,
        algebraMap E (FractionRing (Polynomial E)) (f.coeff i) * (fracX E) ^ i := by
    conv_lhs => rw [Polynomial.as_sum_support_C_mul_X_pow f]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_pow]
    congr 1
  rw [himg]
  exact sum_mem fun i _ => mul_mem (hE _) (pow_mem hX i)

/-- **The constants and the variable generate the rational functions.** -/
theorem eq_top_of_mem_of_mem {S : IntermediateField F (FractionRing (Polynomial E))}
    (hE : ∀ a : E, algebraMap E (FractionRing (Polynomial E)) a ∈ S)
    (hX : fracX E ∈ S) : S = ⊤ := by
  refine le_antisymm le_top fun x _ => ?_
  obtain ⟨f, g, -, rfl⟩ := IsFractionRing.div_surjective (A := Polynomial E) x
  exact div_mem (algebraMap_polynomial_mem hE hX f) (algebraMap_polynomial_mem hE hX g)

/-! ## The splitting field inside the rational functions -/

theorem algebraMap_mem_rootSet {p : Polynomial F} (hp : p ≠ 0) {x : E}
    (hx : x ∈ p.rootSet E) :
    algebraMap E (FractionRing (Polynomial E)) x ∈
      p.rootSet (FractionRing (Polynomial E)) := by
  rw [Polynomial.mem_rootSet] at hx ⊢
  refine ⟨hp, ?_⟩
  rw [Polynomial.aeval_algebraMap_apply, hx.2, map_zero]

/-- **The splitting field lies in the root field of the ambient rational functions.** -/
theorem algebraMap_mem_rootField {p : Polynomial F} (hp : p ≠ 0)
    (hgen : IntermediateField.adjoin F (p.rootSet E) = ⊤) (a : E) :
    algebraMap E (FractionRing (Polynomial E)) a ∈
      rootField F (L := FractionRing (Polynomial E)) p := by
  have hle : IntermediateField.adjoin F (p.rootSet E) ≤
      IntermediateField.comap
        (IsScalarTower.toAlgHom F E (FractionRing (Polynomial E)))
        (rootField F (L := FractionRing (Polynomial E)) p) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    exact IntermediateField.subset_adjoin _ _ (algebraMap_mem_rootSet hp hx)
  rw [hgen] at hle
  exact hle (IntermediateField.mem_top (x := a))

end GaloisForLFunctions.HTGeometry
