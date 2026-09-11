# Route L coherent marginal covariance

- **ID:** L-COHERENT-MARGINAL-2026-09-10
- **Stage:** 3-formalized
- **Type:** Exact finite-source decomposition and annihilator classification
- **Source:** [completion attack](../1-in-progress/route-l-source-selected-completion-attack.md), C5
- **Lean:** `GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentMarginal`

## Statement

For a finite set of primes `S`, the literal complete coherent packet has coefficient
`conj(a(p)-a(q))` on every distinct ordered pair. Let `E_c` read each left-prime
label with real weight `c(p)`. Then

`E_c(R(a,S)) = |S| sum c(p)conj(a(p)) - (sum c(p))(sum conj(a(p)))`,

with every sum over `S`. Furthermore,

`(forall a S, E_c(R(a,S))=0) iff (exists z, forall p, c(p)=z)`.

For reciprocal weights `c(p)=A/p`, universal coherent annihilation is equivalent
to `A=0`.

## Dependency-closed paper proof

1. Extend the defining ordered-pair sum to the diagonal; diagonal terms vanish.
2. Distribute the weighted conjugate difference. Summing the first term over the
   second label gives the cardinality factor; the second term factors as a product
   of the two marginal sums.
3. If every packet is annihilated, choose any two distinct primes and set the
   profile to one at the first and zero elsewhere. The covariance reads the
   difference of the two weights. Hence all weights are equal.
4. Conversely, constant weights cancel in the exact covariance formula.
5. A reciprocal weight constant on all primes has coefficient zero by the
   previously verified prime-reciprocal classification. Zero coefficient suffices.

## Positive survivor and limits

The surviving result is the exact weighted cancellation law. Retaining a whole
left-prime marginal avoids the old identification of distinct fixed-prime rows,
but it does not give coherent annihilation under nonconstant weights.
A source-selected profile family would need its own covariance cancellation
proof. Arbitrary test profiles are not asserted to be Xi-selected profiles.
No RH proof or existence of an off-line zero is asserted.

## Verification

- Scratch: `lake env lean /tmp/route_l_coherent_marginal.lean` passed.
- All three theorem axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- Module wired into `GaloisForLFunctions.RHTower`; no umbrella build.
- Scoped final audit: `lake build GaloisForLFunctions.RHTower.XiGammaSixWoldJordanCoherentMarginal` passed. Only the new module compiled; existing dependency diagnostics were replayed.
- Final repository audit: `scripts/formal_tools.py lint` passed; no owned Lean process remains.
