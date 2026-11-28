import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field

/-! A nonzero root of a degree-`d` irreducible over a finite
field of size `q` is a root of unity of order dividing `q^d - 1`. -/

noncomputable section

open Polynomial

namespace WindowedLandauTheory.CyclotomicNorms

theorem pow_card_pow_sub_one_of_aeval_eq_zero {K L : Type} [Field K] [Fintype K] [Field L] [Algebra K L]
    (P : K[X]) (hP : Irreducible P) (hmon : P.Monic) (x : L) (hx : aeval x P = 0) (hx0 : x ≠ 0) :
    x ^ (Fintype.card K ^ P.natDegree - 1) = 1 := by
  have hint : IsIntegral K x := ⟨P, hmon, hx⟩
  have hmin : P = minpoly K x := minpoly.eq_of_irreducible_of_monic hP hx hmon
  let E := IntermediateField.adjoin K {x}
  let z : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
  haveI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite E := Module.finite_of_finite K
  letI : Fintype E := Fintype.ofFinite E
  have hcard : Fintype.card E = Fintype.card K ^ P.natDegree := by
    rw [Module.card_eq_pow_finrank (K := K), IntermediateField.adjoin.finrank hint, ← hmin]
  have hz : z ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have hp := FiniteField.pow_card_sub_one_eq_one z hz
  rw [hcard] at hp
  exact congrArg (fun t : E => (t : L)) hp

end WindowedLandauTheory.CyclotomicNorms

#print axioms WindowedLandauTheory.CyclotomicNorms.pow_card_pow_sub_one_of_aeval_eq_zero
