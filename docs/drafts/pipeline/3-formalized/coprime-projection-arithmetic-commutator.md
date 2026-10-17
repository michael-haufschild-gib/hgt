# Arithmetic classification of coprime tent projection commutators

- **ID:** coprime-projection-arithmetic-commutator
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Actual infinite tent projections commute iff their spacings
  have gcd≥2; all range intersections use the lcm, and coprime spacings admit
  an explicit commutator trace of 1/2.

Let m=d+2 and n=e+2. Use the actual L² projections P_m and P_n constructed
by the infinite coprime extension package. Proved exact laws:

1. For unnormalized tent velocities H_a,H_b at active integer centers,
   ⟨H_a,H_b⟩=2 when a=b, −1 when |a−b|=1, and 0 otherwise.
2. The intersection of the closed extension ranges is the extension range
   for spacing lcm(m,n), including when m,n are coprime.
3. P_m and P_n commute exactly when gcd(m,n)≥2. In that case their product
   is P_lcm(m,n). When gcd(m,n)=1, construct an actual finite tent velocity
   witnessing a nonzero commutator; do not assume a leakage or operator premise.

Mechanism: a shared divisor at least two excludes adjacent centers,
so cross-family pairing retains only coincident multiples. For coprime
spacings, positive adjacent multiples follow from a modular inverse; projecting
their tents creates forbidden neighboring traces. Intersection rigidity uses
every integer trace and the actual convergent series, not an inference from
intersection of index sets.

This exposes an arithmetic source of noncommutativity inside the constructed
continuum domain. It is distinct from a unitary affine-group representation.
All three assertions are proved and formalized as one connected contribution.
The proof includes m=2 boundary cases, where one tent can couple to two adjacent
centers of the other family.

Fresh query `coprime tent projections gcd commutation adjacent centers least
common multiple` inspected all 20 candidate lemmas and 20 source arguments.
It returned the current single-family construction and unrelated finite Gram
and collar results; no cross-family projection classifier found. Current package
9 entries were source-indexed during implementation, not certified by that
search alone. No partial stages or errors; snapshot older than index, semantic
coverage unavailable, refresh incomplete.

Current paper proof: `docs/reports/BiScaleUncertainty/CoprimeProjectionCommutator.md`.
Fresh focused query inspected all 20 candidate lemmas and 20 source arguments;
single-family projection and finite trace results found, no matching classifier.
No errors/partial stages; semantic coverage unmeasured and refresh incomplete.
Primary Hilbert projection and Bezout sources checked. No external novelty claim
for those parent tools. Certified count is 10/100, goal remains active.

Completed: (1) cross-tent Gram law and bundled self-adjoint projections;
(2) separated-family projection action, nested absorption and lcm product;
(3) all-spacings intersection and explicit coprime trace witness;
(4) direct serial leaf checks, all public axiom/signature audits, imports/index
and repository lint. Global lint limitations are recorded in the fact ledger.

Proof detail worth preserving: choose positive multiples a of m and b of n with
a=b+1 using an inverse of m modulo n. Input H_a is fixed by P_m. At b,
primitive(P_m P_n H_a)=0 and primitive(P_n P_m H_a)=−1/2. Thus the commutator
has exact primitive value +1/2, requiring no finite truncation or operator premise.

Lean leaves: `CoprimeProjectionCrossGram.lean` (112 lines),
`CoprimeProjectionLattice.lean` (122), `CoprimeProjectionCommutator.lean` (101).
All direct checks pass without diagnostics; all 30 public declarations audited,
only standard axioms, nine main signatures inspected. All three imports and
all 30 generated API entries verified. No added axiom, heartbeat increase,
numerical experiment, full/umbrella build, or analytic admission premise.

The relocated `formal/GaloisForLFunctions/BiScaleUncertainty/README.md` was
read fully and treated as read-only. Package module map lives in the fact ledger.
Next falsifiable candidate: `../0-backlog/coprime-projection-angle-gap.md`;
sharp operator norm identities remain unproved and uncounted.
