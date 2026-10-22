# Family prime-balance physical-orientation universality law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.FamilyPrimeBalancePhysicalOrientationUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`FamilyPrimeBalanceDiagonalScaleUniversalityLaw` proves that equality of aggregate positive and
negative prime products is equivalent to coordinatewise cancellation of every signed prime
exponent, equality of all diagonal monomials, and universal disappearance of shared scale.

`PhysicalDefectOrientationAnomaly` proves that a balanced finite source has only rank parity as its
full reversal anomaly, and that even rank removes that anomaly entirely.  Reading the two theorem
bodies shows that every fixed prime coordinate of a balanced exponent family is exactly such a
balanced physical source.  The corpus contains no arithmetic-to-physical transport of this fact.

## Statement

For a finite signed prime-exponent family `m`, equality of aggregate positive and negative prime
products is equivalent to one certificate containing:

1. zero aggregate balance and zero sum in every prime coordinate;
2. equality of positive/negative diagonal Dirichlet monomials at every complex exponent;
3. cancellation of every shared scale in every commutative-group twisted product;
4. for every prime coordinate, full reversal of its physical defect germ changes it only by
   `(-1)^|ι|`;
5. if family cardinality is even, every prime-coordinate defect germ is exactly reversal-invariant.

## Dependency-closed proof

1. Apply family prime-balance diagonal-scale universality to obtain the first three fields.
2. For each prime `p`, cast the coordinate identity `Σ_i m_i(p) = 0` from `ℤ` to `ℂ`.
3. Regard `i ↦ m_i(p)` as a finite complex physical source on `Finset.univ`.
4. Apply balanced-source reversal parity to obtain the exact anomaly.
5. Apply the even-balanced reversal theorem when `|ι|` is even.
6. Conversely, the certificate includes aggregate balance zero, which the existing family
   equivalence sends back to prime-product equality.

No computation, logarithm branch, or encoding of an entire prime vector into one scalar is used;
the law is coordinatewise and exact.

## Novelty audit

Corpus audit: arithmetic family balance and analytic physical reversal anomaly exist separately.
No theorem transports every prime-coordinate balance into a simultaneous family of physical germ
parity laws.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Exact source check passed:
  `lake env lean GaloisForLFunctions/RHTower/FamilyPrimeBalancePhysicalOrientationUniversalityLaw.lean`.
- Wired into `GaloisForLFunctions.RHTower`.
