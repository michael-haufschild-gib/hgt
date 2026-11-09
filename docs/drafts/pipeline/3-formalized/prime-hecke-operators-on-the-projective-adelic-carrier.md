# Prime adjacency on the projective adelic carrier

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133, global operator construction.

For each prime `p`, construct the local prime correspondence on
`PGL₂(ℚ_p)/PGL₂(ℤ_p)` from translates of `(K_p,diag(1,p)K_p)`.
Its neighbours are distinct, number `p+1`, and form a symmetric, loopless
relation invariant under `PGL₂(ℚ_p)`.

For the already constructed arithmetic carrier `X=Γ\(ℍ³×V)`, set

`(A_p F)([x]) = Σ_{w∼x_p} F([x with p-coordinate replaced by w])`.

This sum is well-defined on actual arithmetic orbits, preserves multiplicity,
is linear and order-preserving, satisfies `A_p 1=p+1`, and commutes with `A_q`.
No Weil kernel or diagonal enters its definition.

## Proof

Let `t=diag(1,p)` and `r_b=[[p,-b],[0,1]]`, `b∈𝔽_p`.
For `h=[[a,b],[c,d]]∈GL₂(ℤ_p)`, if `c=0 mod p`, then `t⁻¹ht` is integral
with unit determinant. Otherwise choose `u=-a/c mod p`; then `r_u⁻¹ht` has
integral entries because `a+uc=0 mod p`, and again unit determinant.
Thus the integral stabilizer orbit of `tK_p` has these `p+1` representatives.

If two representatives agree projectively, the norm bound
`‖Mᵢⱼ‖²≤‖det M‖` for their relative matrix forces equal residue labels;
the remaining mixed case would force `‖p⁻¹‖≤1`. The integral Weyl element
reverses the standard edge after a scalar rescaling. Translation gives the
local correspondence at every vertex, independent of the chosen frame.

Equivariance permutes the neighbour sum, so it descends through `Γ`.
Distinct prime updates commute; exchanging the two finite sums proves
`A_p A_q=A_q A_p`. Summing prequotient neighbours retains their multiplicities
when arithmetic classes coincide.

## Formalization

[ThePrimeAdjacencyOnTheAdelicCarrier.lean](../../../../formal/GaloisForLFunctions/HyperbolicArakelovTheory/ThePrimeAdjacencyOnTheAdelicCarrier.lean),
namespace `GaloisForLFunctions.HyperbolicArakelovTheory.AdelicAdjacency`.
Capstones: `card_neighbors`, `neighbors_smul`, `adjacent_symm`,
`not_adjacent_self`, `primeOperator`, `primeOperator_one`,
`primeLinearOperator`, `primeOperator_comm`, and `primeOperator_nonneg`.
Direct source audit passed; all nine capstones depend only on `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella import added.

## Scope

This constructs the finite-place Hecke operators on the actual carrier.
Their local Green identity, an analytic domain, the global Green kernel,
and Weil's Robin diagonal remain open. One contribution: geometric prime
operators with multiplicity-preserving arithmetic descent and commutation.
