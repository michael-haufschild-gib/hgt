# Universal hybrid Krein/Xi-Hurwitz observable nonuniformity law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.UniversalHybridKreinXiHurwitzObservableNonuniformityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`UniversalHybridBlindXiZeroHurwitzFaithfulObservableNonuniformityLaw` proves that one finite
differential observable-field functor is blind on universal orientation/prime chambers but
order-faithful and factorizing on injective Xi-zero Hurwitz nets.  Its blind-side discriminator is
an integer orientation index plus prime-chamber Hamming distance.

`MinimalHTCompletionArchitecture` independently proves that all prime orientations have the same
completed ring while the relative prime Krein form has exact negative and positive inertia.  At
the reference chamber `∅`, the exact negative inertia dimension is `|J|`, which is also the Hamming
term in the hybrid defect.  The corpus does not identify these two discriminator mechanisms inside
the Xi-Hurwitz nonuniformity law.

## Statement

For orientation index `k`, finite prime chamber `J`, finite observable resolution, and an injective
Xi-zero-labelled Hurwitz family, one certificate simultaneously asserts:

1. orientation and prime chambers have the same finite differential observable field;
2. every pair of prime-orientation completed rings is equal;
3. the relative Krein form from `J` to `∅` has exact negative and positive inertia;
4. hybrid dephasing defect is exactly `k + |J|`, so its prime term is the exact negative-inertia
   dimension;
5. both Herglotz signs hold exactly in the trivial chamber `k = 0`, `J = ∅`;
6. the Xi-Hurwitz observable net reflects resolution order, reconstructs equal resolutions, and
   factorizes disjoint coordinate sectors.

## Dependency-closed proof

1. Extract observable-field equality, Herglotz/defect equivalence, and Xi-Hurwitz
   order/factorization from the existing hybrid theorem.
2. Extract completed-ring equality and exact relative Krein inertias from prime-orientation
   blindness/polarization in the minimal HT architecture.
3. Specialize relative chamber to `(J, ∅)`.
4. Simplify
   `primeChamberHammingDistance J ∅ = |∅ \ J| + |J \ ∅| = |J|`.
5. Compose the Herglotz/defect equivalence with the existing zero-defect classification.

No computation, new field hypothesis, or additional source assumption is introduced.

## Novelty audit

Corpus audit: hybrid observable nonuniformity and exact Krein polarization exist separately.  No
theorem equates hybrid defect’s prime contribution with exact negative-inertia dimension while
retaining completed-ring blindness and Xi-Hurwitz faithfulness.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Exact source check passed:
  `lake env lean GaloisForLFunctions/RHTower/UniversalHybridKreinXiHurwitzObservableNonuniformityLaw.lean`.
- Wired into `GaloisForLFunctions.RHTower`.
