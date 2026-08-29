# JAS Gamma Boolean closed creation

- **ID:** JAS-GAMMA-BOOLEAN-CLOSED-CREATION
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Lean-corpus synthesis from `gammaSewnSynchronizedLcmWeight_insert`, `gammaSewnSynchronizedLcmInsertionGain_cocycle`, `maximalRealDiagonal_isSelfAdjoint`, `lpReindexCLM_single`, `jasGammaInsertionPacket_operator_not_surjective`, and the JAS frontier requirement for a closed support-cutting completion realized as a compression/correspondence/corner rather than a unital prime-torus action

## Goal

Construct, unconditionally, the first closed densely defined support-raising operator on the full Boolean Hilbert completion `ell^2(Finset Primes)` carrying the literal Gamma-sewn state-dependent coefficients.

For `x > 0` and prime `p`, define the all-support gain

`g(x,p,P) = W_x(P insert {p}) / W_x(P)`,

where `W_x(P) = gammaSewnSynchronizedLcmWeight x P`. Define a real diagonal weight that equals `g(x,p,P)` when `p` is absent and zero when `p` is present, then postcompose its maximal diagonal operator with the unitary that toggles `p` in the finite support.

Formalized package:

1. every `W_x(P)` is positive, including the Boolean vacuum;
2. `g` agrees with the corpus insertion gain on every nonempty face and satisfies the two-prime cocycle from the vacuum onward;
3. the resulting prime-creation partial operator is densely defined and closed;
4. on each basis state with `p` absent it sends `e_P` exactly to `g(x,p,P) e_(insert p P)`, while it kills the `p`-occupied sector;
5. it is non-surjective and genuinely support-cutting;
6. two distinct prime creations agree on every admissible Boolean basis square, with the literal Gamma-sewn coefficient.

This is not a bounded prime-torus representation and does not contradict `not_JASPrimeSupportCoordinateRaisingRepresentation`.

## Full RH proof chain

Gamma Boolean closed creation (this target) -> combine its finite-support closed graph with `jasActualThetaClosedUnboundedGradeSynthesisRelation` on a common insertion-stable domain -> replace scalar grade norms by the literal `exp(plus/minus x)` completed-theta derivative/higher-compound currents -> prove the resulting corner/correspondence is source-linear for the forward and reflected prime-Poisson multiplication families, uniformly in every Xi divisor -> `XiPrimePoissonReflectionSewing rho` for every `rho` -> `xiPrimePoissonReflectionSewing_iff_internalOnly` -> `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half` -> RH.

This target closes only the support-cutting closed-operator and finite-Boolean-face part of that chain. Actual-theta tensoring, source-linearity, completion provenance, and Xi landing remain explicit downstream burdens.

## Proof

1. Extend the original nonempty-face gain by the exact ratio `W(insert p P) / W(P)`. Positivity of every synchronized weight makes the ratio defined, and cancellation proves the insertion law and two-prime cocycle even at the vacuum.
2. Toggle membership of `p` by an involutive permutation of `Finset Primes`; its `ell^2` reindexing is unitary.
3. Put the ratio on the `p`-absent coordinates and zero on the `p`-present coordinates. Maximal real diagonal multiplication is self-adjoint, hence closed and densely defined.
4. Postcomposition by the toggle unitary preserves graph closedness. Basis evaluation proves exact support raising with the Gamma coefficient and annihilation of the occupied sector.
5. Every output coordinate whose support omits `p` is zero, so the vacuum basis vector is not in the range. Hence creation is a genuine non-surjective corner operator.
6. The all-support ratio cocycle plus exact basis action proves equality of the actual partial-operator paths around each admissible two-prime square. On nonempty faces the ratios are definitionally identified with the original Gamma-sewn insertion gains.

Formal capstones:

- `jasGammaSynchronizedLcmWeight_insert_boolean`
- `jasGammaBooleanInsertionGain_cocycle`
- `dense_jasGammaBooleanCreation_domain`
- `jasGammaBooleanCreation_closed`
- `jasGammaBooleanCreation_not_surjective`
- `jasGammaBooleanCreation_twoPrime_operator_paths`
- `jasGammaBooleanCreation_twoPrime_gamma_operator_paths`

Formal certificate:

- module `GaloisForLFunctions.RHTower.JointAncestryGammaBooleanClosedCreation`
- `lake env lean GaloisForLFunctions/RHTower/JointAncestryGammaBooleanClosedCreation.lean` — PASS, 2026-08-29
- `lake build GaloisForLFunctions.RHTower.JointAncestryGammaBooleanClosedCreation` — PASS, 2026-08-29
- axiom audit — only `propext`, `Classical.choice`, `Quot.sound`

## No-go closure

- **Killed mechanism:** support insertion need not be represented by an invertible prime-torus unit. A closed dense support-raising corner exists and is necessarily non-surjective.
- **Strongest positive survivor:** exact Gamma-sewn coefficient transport extends from finite nonempty faces through the Boolean vacuum to closed partial operators on the full `ell^2(Finset Primes)` completion, with literal two-prime path independence.
- **Remaining hard burden:** couple this support corner to the actual-theta unbounded grade graph on one insertion-stable domain, then prove prime-Poisson source-linearity and Xi landing. This theorem does not supply those claims.

## Falsifiers

- If the all-support weight has a zero for some `x > 0`, ratio construction fails; prove the zero or pivot to rooted nonempty faces.
- If postcomposition by support toggle does not preserve graph closedness, build the graph-homeomorphism lemma directly; do not weaken to an algebraic finite-support map.
- If two-prime basis paths do not agree exactly, retire this completion: it fails the corpus three-prime falsifier.
- Do not claim an everywhere-defined bounded action, a `C(PrimeTorus)` representation, source-linearity, or Xi sewing.

## Novelty audit

Internal `formal_tools.py research` found generic maximal diagonal operators, unitary reindexing, and the finite Gamma cocycle, but no closed Boolean-lattice creation operator carrying these Gamma-sewn weights. External search found general closed weighted shifts on directed trees and multishifts on Cartesian products of trees, but no completed-theta, synchronized-lcm, prime-Poisson, RFHM, or RH application. `[NOVELTY UNVERIFIED]`: closed weighted-shift mechanism is classical; exact arithmetic coefficient system and JAS role appear corpus-new.

## Log

- 2026-08-29 — conjecture frozen after Lean-corpus search and literature audit; exact JAS-to-RH chain recorded before proof work.
- 2026-08-29 — proved all-support positivity and ratio cocycle, constructed closed dense Boolean creation operators, proved exact Gamma basis action, corner support, non-surjectivity, and actual two-operator square flatness; leaf build and axiom audit passed; promoted to stage 3.
