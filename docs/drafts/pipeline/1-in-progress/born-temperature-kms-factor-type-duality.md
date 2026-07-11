# Born temperature aligns the critical line with the Bost--Connes factor-type transition

- **ID:** `born-temperature-kms-factor-type-duality`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE / PAPER THEOREM WITH PUBLISHED OPERATOR-ALGEBRA INPUT
- **Source:** prime coherent scale factor; Bost--Connes KMS classification; separate from RHTower
  Routes A--D
- **Statement:** For the prime-number wavefunction `n^(-s)`, the physical inverse temperature is
  `beta=2 Re(s)` by the Born rule. Functional-equation reflection becomes `beta -> 2-beta`, and the
  two reflected Bost--Connes GNS factors have the same type exactly at `beta=1`, i.e.
  `Re(s)=1/2`.

## Goal

Replace the older dictionary `beta=Re(s)`, which leaves an unexplained mismatch between FE
self-duality at `1/2` and the Bost--Connes phase transition at `1`, by the temperature actually seen
by the Hilbert-space state. Then ask whether the completed Euler--Gamma constraint supplies a normal
duality of the two reflected KMS sectors at its zeros.

## Gates

- [x] 0 -> 1 in-progress: normalization, factor-type invariant, RH equivalence, source requirement,
  and failure tests are explicit.
- [ ] 1 -> 2 fully-proven: exact original-source audit of the Bost--Connes KMS classification and a
  complete operator-algebra proof with all representation choices fixed.
- [ ] 2 -> 3 formalized: formalize the Born-temperature and phase-type selector; the von Neumann
  factor classification is presently outside mathlib and must not be hidden as an axiom.
- [ ] 3 -> 4 publication-ready: requires a source-derived normal FE duality, not merely the selector.

## 1. The normalization correction `[PROVED HERE]`

On the integer basis, let

```text
Psi_s = sum_(n>=1) n^(-s) |n>.
```

Whenever `sigma=Re(s)>1/2`, its Born probabilities are

```text
Prob_s(n) = |n^(-s)|^2 / ||Psi_s||^2
          = n^(-2 sigma) / zeta(2 sigma).
```

For the Bost--Connes Hamiltonian `H|n>=(log n)|n>`, a Gibbs state has weights
`exp(-beta log n)=n^(-beta)`. Therefore

```text
beta = 2 sigma,                                      (1)
```

not `beta=sigma`. The factor `2` is forced by the Born rule and is not a chosen rescaling.

Under FE--Schwarz reflection `tau(s)=1-conj(s)`,

```text
beta(tau(s)) = 2(1-sigma) = 2-beta(s).               (2)
```

Thus the temperature duality has fixed point `beta=1`, exactly the Bost--Connes critical inverse
temperature. The old `{0,1/2,1}` mismatch was caused by identifying an amplitude exponent with a
probability exponent.

## 2. Factor-type wall `[PUBLISHED INPUT + PROVED COMPOSITION]`

The Bost--Connes KMS phase diagram supplies the faithful categorical invariant:

```text
0 < beta <= 1 : the unique KMS_beta GNS factor is type III_1;
beta > 1      : extremal KMS_beta states are type I and symmetry is spontaneously broken.
```

The high-temperature type-`III_1` result for number-field Bost--Connes systems is proved by
[Neshveyev](https://arxiv.org/abs/0907.1456). The phase transition, low-temperature extremal Gibbs
states, and symmetry breaking are part of the Bost--Connes classification; a modern summary states
the type-I/type-III split explicitly in the introduction of
[Abouamal](https://arxiv.org/abs/2211.07778).

For `0<beta<2`, put `beta*=2-beta`. If `beta<1`, the `beta` factor is type `III_1` while the
`beta*` extremal factors are type I. If `beta>1`, the roles reverse. Von Neumann factor type is
preserved by normal spatial isomorphism and unitary equivalence. Hence

```text
the beta and beta* KMS sectors can be normally equivalent
  iff
beta=1.                                               (3)
```

At `beta=1` the two parameters coincide, so equivalence is the identity. This proves (3), conditional
only on the published KMS classification.

## 3. RH reformulation `[PROVED COMPOSITION]`

Combining `(1)`--`(3)` gives

```text
RH
  iff
for every rho with xi(rho)=0, the Bost--Connes KMS sectors at
beta=2 Re(rho) and beta*=2-2 Re(rho) have no factor-type mismatch.
```

Equivalently, every zero lies where FE reflection can be a **normal thermodynamic duality**, rather
than only an equality of analytically continued scalar partition functions.

This is pointwise and therefore is not the measured-trace route killed by
`f1-hodge-riemann-modular-route`: one hypothetical off-line zero already pairs a type-I factor with a
type-`III_1` factor and is detected. The missing step is not faithfulness of the invariant; it is the
existence of the source-derived normal duality.

## 4. Source-forcing conjecture `[CONJECTURE]`

`[CONJECTURE]` The completed Euler--Gamma constraint defines, at every `xi` zero `rho`, a normal
clock-perspective equivalence between the KMS reductions at `beta=2 Re(rho)` and `2-beta`.

If constructed without inserting `xi`, its divisor, or a square-summability assumption, this
conjecture proves RH immediately by (3). It is stronger than scalar FE: an off-line zero pair obeys
the scalar functional equation but its KMS factors have different types.

## 5. Kill tests

- A scalar equality of partition functions is insufficient; analytic continuation does not preserve
  positivity or GNS factor type.
- Group-averaging an off-line reflected pair gives an invariant superposition but not a normal
  equivalence of its type-I and type-`III_1` fibers.
- A measured modular trace remains density-blind; factor type is used pointwise instead.
- Simply declaring FE to be a gauge symmetry is circular. The normal functor between KMS reductions
  must be built from the completed Euler--Gamma source.
- The result is a selector until that functor exists. It is not a proof of RH.

## 6. Novelty status

The `beta=2 sigma` correction and the resulting exact alignment

```text
FE self-duality = BC phase transition = prime-clock metric wall
```

were not found in the initial literature search and repair a concrete normalization defect in the
existing project KMS card. Nevertheless `(1)` is the Born rule and `(3)` is a short composition of
the published phase classification with invariance of factor type. Strict new-science promotion is
withheld until the source-derived normal duality is constructed or the exact combination passes a
deeper parent-literature audit.

## Log

- 2026-07-11 — opened from the user's claim that an inner scale factor forces the external clock.
  Corrected the physical temperature to `beta=2 Re(s)`, aligned FE self-duality with the
  Bost--Connes transition at `beta=1`, and isolated normal KMS-sector duality at `xi` zeros as the
  source-forcing conjecture.
