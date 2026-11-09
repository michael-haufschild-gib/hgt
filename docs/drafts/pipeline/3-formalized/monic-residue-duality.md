# Residue duality for monic quotient algebras

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [Prime-quadratic orientation cover](../1-in-progress/riac-prime-quadratic-orientation-cover.md)

## Statement

Let `f=X^d+Σ_(k<d)a_kX^k` over a commutative ring `R`,
`A=R[X]/(f)`, and `t=[X]`. Write `λ(x)` for the coefficient of
`t^(d−1)` in the canonical remainder. Put
`q_i=Σ_(k>i)a_kt^(k−i−1)`, including `a_d=1`.
Then

`λ(t^j q_i)=δ_ij`, `Σ_(i<d)t^i q_i=f'(t)`,
and `Tr_(A/R)(x)=λ(xf'(t))`.

Thus the residue pairing is perfect even when the trace pairing degenerates.
The identities require neither irreducibility nor separability.
Under this integral duality the trace map is multiplication by `f'(t)`.
Consequently its actual cokernel is `R[X]/(f,f')` as an `R`-module,
including when this quotient is infinite.

## Proof

The defining equation gives `tq_0=−a_0` and
`tq_(i+1)=q_i−a_(i+1)`. Also `λ(q_i)=δ_i0` and
`λ(t^j)=0` for `j<d−1`. Induction on `i,j<d` gives the duality.
Expanding any element in the monomial basis recovers its `i`th coordinate
as `λ(xq_i)`, proving perfection.

In `Σ_i t^i q_i`, the term `a_kt^(k−1)` occurs exactly `k` times.
The sum is therefore `f'(t)`. Taking the diagonal entries of multiplication
by `x` in the monomial basis gives
`Tr(x)=Σ_i λ(xt^iq_i)=λ(xf'(t))`. For `d=0`, the quotient is the zero ring
and all identities are empty.

The residue equivalence carries the image of multiplication by `f'(t)`
onto the image of the trace map. It therefore induces a cokernel
equivalence. The former image is the principal ideal `(f'(t))` in `A`;
the third isomorphism theorem identifies its quotient with `R[X]/(f,f')`.

Over `ℤ`, the dual basis identifies the cokernel of a bilinear form with
the cokernel of an endomorphism whose matrix is the transposed Gram matrix.
The integral determinant-cardinality theorem therefore identifies its
cardinality with the absolute Gram determinant, including cardinal zero
for infinite singular cokernels. Applied to the trace form and the actual
different quotient, this gives `|disc_trace(f)|=|disc(f)|`. The finite-place
factorization of this common positive integer gives the same product-formula
height for both presentations.

## Relation to the target

This identifies the different element inside the actual trace pairing of
the prime-quadratic order, including repeated factors. It supplies no
uniform bound for the signed sum `1−M(N)`.
The absolute discriminant comparison alone does not identify the signs
of the trace and polynomial discriminants.

## Lean statements

| Module | Main declarations |
|---|---|
| [MonicResiduePairing](../../../../formal/GaloisForLFunctions/HTGeometry/MonicResiduePairing.lean) | `monicResidue_root_pow_mul_dual`, `monicResidue_casimir`, `monicResidueEquiv`, `monic_traceForm_eq_residueMap_comp` |
| [MonicTraceCokernel](../../../../formal/GaloisForLFunctions/HTGeometry/MonicTraceCokernel.lean) | `monicTraceCokernelEquivDifferent` |
| [IntegralTraceCokernel](../../../../formal/GaloisForLFunctions/HTGeometry/IntegralTraceCokernel.lean) | `card_bilinearCokernel_eq_natAbs_det`, `card_traceCokernel_eq_natAbs_discr` |
| [PrimeQuadraticTraceCounts](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeQuadraticTraceCounts.lean) | `monic_trace_discriminant_natAbs`, `primeQuadraticTraceQuotientEquivDifferent`, `primeQuadraticTrace_productFormula` |

Four direct module checks pass. All 18 printed axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
