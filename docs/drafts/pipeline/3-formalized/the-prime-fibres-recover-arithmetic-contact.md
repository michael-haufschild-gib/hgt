# The prime fibres recover arithmetic contact

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: recover prime contact geometrically without the contact-erasing product.
- **Statement:** On the actual restricted product of finite vertices, extend each
  critical local Green kernel by zero between distinct fibres of the other
  coordinates. The normalized sum recovers Weil's prime channel on the degree
  configuration; its cutoff diagonal is exactly the sum of the prime logarithms.

## Proof

For prime `p`, put
`K_p(v,w)=log p·(p−1)/√p·G_p(v_p,w_p)` when `v_q=w_q` for every `q≠p`,
and zero otherwise. This condition is geometric and invariant under simultaneous
adelic action. Replacing the `p` coordinate preserves the fibre condition. Thus
the local source equation becomes the point-source equation on the whole finite
product for the operator changing only coordinate `p`. Restrict any nonnegative
supersolution to the source fibre: local minimality bounds it below by `G_p`.
On every other fibre the zero extension is already a lower bound. This proves
global minimality for the individual prime operator.

For distinct vertices at most one `K_p` is nonzero. Thus the off-diagonal sum
needs no convergence choice. At equal vertices `K_p(v,v)=log p`, so subtracting
`Σ_{p∈S}log p` from a finite cutoff removes exactly its diagonal. The remainder
eventually stabilizes exactly on each pair of vertices.

The normalized local Green kernel equals `sqrt(localRatio)`, hence the existing
invariant matrix factor. Its degree restriction is `p^(−|v_p(m)−v_p(n)|/2)`.
Since `0<p^(−1/2)<1`, local degree vertices coincide exactly when their prime
exponents agree. Agreement away from `p` therefore means equality of `ordCompl[p]`.
Each subtracted geometric entry is the existing arithmetic `ladderKernel`.
The corpus's exact ladder decomposition identifies the finite sum with
`weilPrimeKernel` for all positive `m,n`, including the zero diagonal.

## Boundary

This is a kernel on marked pairs in the finite product. Simultaneous invariance
does not imply separate descent to the arithmetic quotient. No periodization,
archimedean diagonal, positivity after subtraction, or full Weil realization is
claimed. The accepted obstruction to operator-only gluing remains in force.
Ignoring the archimedean coordinate lifts its finite point source to a cylinder,
not a point source on the full global carrier.

## Verification

`HyperbolicArakelovTheory/ThePrimeFibresRecoverArithmeticContact.lean`,
namespace `PrimeFibres`:

- `fibreGreen_source`, `fibreGreen_isLeast`: actual finite-product source and minimality.
- `degree_vertex_eq_iff`, `sameFibre_degree`: geometric fibres are arithmetic ladders.
- `primeTerm_degree`, `primeGreen_degree`: exact prime-channel comparison for all degrees.
- `primeTermNat_finite_support`, `primeGreen_smul`: finite support and adelic invariance.
- `cutoff_diagonal`, `cutoff_stabilizes`: exact prime-logarithm subtraction and stabilization.

Plain `lake --old env lean` passes without warnings. All eight audited
declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The arithmetic ladder decomposition was already formalized; the new result
identifies it with minimal Green sources on actual finite adelic vertices.
