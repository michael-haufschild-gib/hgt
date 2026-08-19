import GaloisForLFunctions.HTGeometry.CotangentPresentationCokernel
import Mathlib.RingTheory.Extension.Presentation.Basic

/-!
# The critical fibre as a square presentation

The truncated compatibility equation `X^(m+n) ∣ (A + P)(B + Q) - 1` is `m + n` polynomial equations
in the `m + n` unknown low coefficients — `m` raw and `n` reciprocal — so the critical fibre is a
square presentation in the sense of `Algebra.PreSubmersivePresentation`, with the identity matching
of relations to variables.

```text
horizonRawCoeff, horizonRecipCoeff   an unknown below the depth, an observed tail above
horizonRelation k                    the k-th truncated compatibility equation
horizonFibreAlgebra                  the quotient by those equations
horizonPresentation                  ** the square presentation, with map = id **
```

`map = id` is exactly the hypothesis that `JacobianKaehlerAnnihilator.jacobian_smul_kaehler_eq_zero`
and `CotangentPresentationCokernel.annihilator_kaehler_eq_span_jacobian` consume, so this is the
datum that turns the abstract Jacobian–different bridge into a statement about the horizon map.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Polynomial MvPolynomial

variable (A : Type*) [CommRing A] (m n : ℕ) (P Q : A[X])

/-- Raw coefficient of the completed jet: an unknown below the depth, an observed tail above. -/
noncomputable def horizonRawCoeff (i : ℕ) : MvPolynomial (Fin (m + n)) A :=
  if h : i < m then MvPolynomial.X ⟨i, by omega⟩ + MvPolynomial.C (P.coeff i)
  else MvPolynomial.C (P.coeff i)

/-- Reciprocal coefficient of the completed jet. -/
noncomputable def horizonRecipCoeff (j : ℕ) : MvPolynomial (Fin (m + n)) A :=
  if h : j < n then MvPolynomial.X ⟨m + j, by omega⟩ + MvPolynomial.C (Q.coeff j)
  else MvPolynomial.C (Q.coeff j)

/-- The `k`-th truncated compatibility relation of the critical horizon. -/
noncomputable def horizonRelation (k : Fin (m + n)) : MvPolynomial (Fin (m + n)) A :=
  (∑ i ∈ Finset.range ((k : ℕ) + 1),
      horizonRawCoeff A m n P i * horizonRecipCoeff A m n Q ((k : ℕ) - i))
    - (if (k : ℕ) = 0 then 1 else 0)

/-- The critical fibre algebra: the truncated compatibility equations in the low unknowns. -/
noncomputable abbrev horizonFibreAlgebra :=
  MvPolynomial (Fin (m + n)) A ⧸ (Ideal.span <| Set.range (horizonRelation A m n P Q))

/-- **The critical fibre as a square presentation.**  There are exactly as many truncated
compatibility equations as low unknowns, and the relation-to-variable matching is the identity. -/
noncomputable def horizonPresentation :
    Algebra.PreSubmersivePresentation A (horizonFibreAlgebra A m n P Q)
      (Fin (m + n)) (Fin (m + n)) where
  __ := Algebra.Presentation.naive (v := horizonRelation A m n P Q)
  map := _root_.id
  map_inj := Function.injective_id

theorem horizonPresentation_map : (horizonPresentation A m n P Q).map = _root_.id := rfl

theorem horizonPresentation_relation (k : Fin (m + n)) :
    (horizonPresentation A m n P Q).relation k = horizonRelation A m n P Q k := rfl

end

end GaloisForLFunctions.HTGeometry
