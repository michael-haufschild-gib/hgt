# Floquet emergence of hypertranscendental orbifold memory

- **ID:** `floquet-orbifold-tail-emergence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Two rational coarse-grainings can each erase every nonconstant HT observable when
  repeated alone, while their alternating periodic protocol retains a complete nonconstant
  orbifold-current field.  The topology lives in the time cycle, not in either static map.

## Theorem: emergent memory under alternation

Let `C` be the complex numbers with trivial derivation and let `y` be differentially
transcendental over `C`.  Define

```text
R_1(z)=z^2+1,
R_2(z)=(z-1)^2.
```

Then:

```text
Tail(R_1)=C,
Tail(R_2)=C,                                                 (1)
```

but the two phase-rotated period maps are

```text
P_0=R_2 composed with R_1,       P_0(z)=z^4,
P_1=R_1 composed with R_2,       P_1(z)=(z-1)^4+1,           (2)
```

and have exact nonconstant tails

```text
Tail(P_0)=C<delta y/y>,
Tail(P_1)=C<delta y/(y-1)>.                                  (3)
```

The phase currents

```text
tau_0=dz/z,
tau_1=dz/(z-1)
```

are transported rather than fixed by the individual steps:

```text
R_1^* tau_1=2 tau_0,
R_2^* tau_0=2 tau_1.                                        (4)
```

Thus one full period returns the current with multiplier `4`.

## Proof

The identities in (2) and (4) are direct symbolic identities.  In evaluated differential form,
they are

```text
delta(R_1(y))/(R_1(y)-1)=2 delta y/y,
delta(R_2(y))/R_2(y)=2 delta y/(y-1).                        (5)
```

The autonomous tail classification applied to the two period maps gives (3): `P_0` is the fourth
power map and `P_1` is its conjugate by `h(z)=z+1`.

It remains to justify (1).  Every rational map with a nonconstant tail is, up to homography, a
power, Chebyshev, or Lattes map.

- `R_1` is the centered quadratic polynomial `z^2+1`.  Its finite critical orbit starts
  `0,1,2,5,...` and is strictly increasing on the real line from `1` onward, hence infinite.  Every
  power, Chebyshev, and Lattes map is postcritically finite, so `R_1` is not exceptional.
- Translating the critical point of `R_2` to zero conjugates it to `z^2-1`.  Its finite critical
  point lies on a superattracting cycle of exact period two.  A quadratic power map has fixed
  critical points; a quadratic Chebyshev map has a strictly preperiodic finite critical point; and
  a Lattes map has no periodic critical point.  Critical orbit portrait is preserved by
  homographic conjugacy, so `R_2` is not exceptional.

The classification theorem therefore forces both static tails to be `C`, proving (1).

## General periodic transport law

Let phase-labelled rational maps `R_j : P1_(j-1) -> P1_j` form a period-`m` protocol.  Suppose
there are nonzero rational `k`-tensors `tau_j` and scalars `lambda_j != 0` such that

```text
R_j^* tau_j=lambda_j tau_(j-1)                              (6)
```

with phase indices read cyclically.  Then the rotated period map at every phase preserves its
phase tensor with multiplier

```text
Lambda=product_j lambda_j.                                  (7)
```

Evaluation on a free HT jet gives a cyclic family of eigenobservables and hence a nonconstant
stroboscopic tail at every phase.  When each phase tensor is minimal and the period composite is a
parabolic-orbifold map, the autonomous tail theorem identifies these as the complete phase tails.

Conversely, if one period composite has a nonconstant tail, its parallel tensor pulls backward
through the factors to a cyclic tensor chain satisfying (6).  Factorization of the corresponding
orbifold cover supplies the phase orbifolds.  Thus nontrivial periodic memory is equivalent to a
closed parabolic-orbifold transport cycle, even when no individual step preserves an orbifold in
the static frame.

## Physical interpretation

This is a genuinely time-dependent topology.  Each static law is in the complete-erasure phase,
but the ordered protocol has a protected stroboscopic current.  The singular support of the
current alternates between `0` and `1`; only after a full period does the topology close.

The closest physical analogy is an anomalous Floquet phase: a protected boundary quantity exists
for the period evolution although it is absent from every repeated snapshot rule.  Here the
statement is exact algebraic differential geometry, not a claim that the HT source is a quantum
system.  The mathematical object is a parabolic-orbifold bundle over a discrete time circle, with
the HT tail as its stroboscopic boundary field.

## Novelty and significance gate

- Non-autonomous rational dynamics is established, and Floquet topology is established in physics,
  but the checked searches found no result about differential-substitution tail fields or the
  emergence of a complete HT orbifold current from individually tail-trivial rational maps.
- The example is not merely existential: both static tails and both phase tails are classified
  exactly.
- The theorem changes the ontology of the topology.  It belongs to an ordered protocol, not to a
  single rational coarse-graining.
- The construction is elementary once the autonomous classification exists.  It is therefore a
  significant new consequence and research direction, but not by itself claimed to clear the
  medal-level gate.

## RH impact audit

There is no direct RH implication.  The result warns that testing one candidate zeta
coarse-graining at a time is incomplete: a periodic family could have a protected tail even if
each autonomous tail is trivial.  An RH application would still need an actual source-pure cycle
of rational transformations of the completed zeta differential field; none is known or supplied
here.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/FloquetOrbifoldTail.lean` formalizes the symbolic identities
(2), (4), and (5), together with both phase-rotated two-step eigenobservables.  It now also proves
the general finite periodic transport law (6)--(7):
`finitePhasePullbackComposite_apply_of_transport` composes an arbitrary finite chain of linear
pullbacks and multiplies its local transport scalars, while `finitePeriodicTransport_multiplier`
closes the phase chain and obtains the product Floquet eigenvalue.  Direct elaboration uses the
existing cache, and the axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
The static-tail triviality and exact-tail completeness assertions still use the paper-level
autonomous classification, so the card remains in step 2.

## Gates

- [x] 0 -> 1: exact time-dependent phenomenon and explicit protocol isolated
- [x] 1 -> 2: static triviality, phase tail identities, and general transport law proved
- [x] general finite periodic transport law formalized unconditionally
- [ ] 2 -> 3: symbolic transport is formalized; assemble with the autonomous tail classification
- [ ] 3 -> 4: independent novelty audit and standalone exposition

## 2026-08-14 — the phase tails contain their currents, unconditionally

The shared layer `formal/GaloisForLFunctions/HTGeometry/OrbifoldCurrentTailInclusion.lean`
(unconditional, axiom-clean) supplies the containment half of `(3)` for both phases of this
protocol:

- `HTGeometry.differentialAdjoin_logDeriv_le_stableRangeCore_of_pow` applied to the phase-zero
  period map `P₀(z) = z⁴` gives `C⟨δy/y⟩ ≤ Tail(P₀)` — the phase-zero current is stable at every
  depth, with multiplier `4`, which is exactly the Floquet eigenvalue this card's
  `phaseZeroCurrent_twoStep` computes;
- `HTGeometry.differentialAdjoin_logDeriv_sub_le_stableRangeCore_of_pow` applied to
  `P₁(z) = (z-1)⁴ + 1` gives `C⟨δy/(y-1)⟩ ≤ Tail(P₁)`, the phase-one current.

So the *emergence* half of the theorem — that the alternating protocol retains a nonconstant
orbifold current although neither static step does — is now formal on the side that asserts
retention.  What still rests on the paper-level autonomous classification is the complementary
assertion `(1)`, that each static tail is exactly `C`, and the exactness (rather than containment)
of `(3)`.
