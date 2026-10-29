# The arithmetic parity tower has a unique secular root

- **ID:** ACP-PARITY-SECULAR-DATA
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Parent:** ../2-fully-proven/arithmetic-counting-small-prime-secular-gap.md
- **Source:** ../3-formalized/arithmetic-counting-parity-spectral-mass.md
- **Statement:** The explicit parity coefficients have squared sum one; their arithmetic diagonal has a unique secular root strictly below the two-mode value `p log(p)/(p+3)`.

## Objects and scope

For prime p put `c=(p-1)/(p+1)`, `a_0=c`,
`a_(k+1)=2c(-1)^(k+1)/sqrt(phi(p^(k+1)))`, `D_0=0`, and
`D_(k+1)=(k+1)log p+log p/(p-1)`. These are the already proved limiting
parity coefficients and prime-power energies above gamma.

The exact root alpha is the existing `infiniteSecularRoot D a`, so its
defining expression is `sum a_k^2/(D_k-alpha)=0`. This card proves the
arithmetic data and root properties. Identification with the actual finite
matrix gap remains on the parent card.

## Closed proof

The proved coefficient mass formula gives

`a_0^2+sum_(k<K) a_(k+1)^2=1-4p/((p+1)^2 p^K) -> 1`.

All summands are nonnegative, so convergence of these partial sums gives
`HasSum (a_k^2) 1`, hence square summability. The prime is greater than
one, so `D_0<D_1<D_2<=D_(j+2)` and every coefficient is nonzero.
The existing general infinite secular theorem therefore supplies a unique
root in `(D_0,D_1)` at or below its two-mode trial value.

Using `phi(p)=p-1`, the first two squared coefficients are `c^2` and
`4c^2/(p-1)`, while `D_1=p log p/(p-1)`. Their trial value is exactly
`c^2 D_1/(c^2+4c^2/(p-1))=p log p/(p+3)`.

At that trial value the two head terms cancel. The remaining series is
strictly positive: its first term has nonzero squared coefficient and
positive denominator, and every other term is nonnegative. The root
therefore lies strictly below the trial value. Strict monotonicity of
the full secular function on `(D_0,D_1)` gives uniqueness.

Finally `tameDifferent_prime_pow` and the logarithm power identity show
`D_k=ramanujanAdjunctionEnergy(p^k)-gamma`, including k=0. Every input is
an inspected theorem or explicit finite/infinite algebraic calculation.

## Audit

The infinite-series mechanism is existing corpus infrastructure in
`ConstrainedProlateInfiniteSecular.lean`, including root existence,
uniqueness, continuity, summability and the two-mode bound. The contribution
is its exact arithmetic specialization, connected to the counted parity
mass. No claim of a new abstract secular theorem is made.

## Gates

- [x] Exact data, closed proof and existing-source audit.
- [x] Lean proof, transitive axiom audit and canonical source check.
- [x] Umbrella, README, durable evidence and scratch cleanup.

## Lean endpoints and evidence

The installed leaf is `TheParityTowerHasAUniqueSecularRoot.lean`. Its five
public theorems are `primeParityTowerEnergy_eq`,
`primeParityTowerCoefficient_sq_succ`,
`hasSum_primeParityTowerCoefficient_sq`, `primeParitySecularRoot_spec`,
and `primeParitySecularRoot_unique`. Scratch check 71369 and canonical
check 68241 exited zero. The canonical check had no diagnostics; every
transitive axiom audit uses only `propext`, `Classical.choice`, `Quot.sound`.
The adjacent audit file preserves commands, source hash and actual output.
The umbrella and foundational README are updated. The actual matrix gap
identity remains open on the parent card.
