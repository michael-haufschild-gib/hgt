# Residue duality for monic quotient algebras

- **Stage:** 2-fully-proven
- **Parent:** [Prime-quadratic orientation cover](../1-in-progress/riac-prime-quadratic-orientation-cover.md)
- **Lean:** `HTGeometry/MonicResiduePairing.lean` — verification in progress.

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

## Relation to the target

This identifies the different element inside the actual trace pairing of
the prime-quadratic order, including repeated factors. It supplies no
uniform bound for the signed sum `1−M(N)`.
