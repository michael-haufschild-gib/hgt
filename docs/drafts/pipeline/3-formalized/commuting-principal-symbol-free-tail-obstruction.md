# Commuting principal symbols cannot have a free hypertranscendental tail

- **ID:** `commuting-principal-symbol-free-tail-obstruction`
- **Stage:** 3-formalized
- **Type:** THEOREM / PARTIAL DIFFERENTIAL ALGEBRA / SYMBOL PROLONGATION / NO-GO
- **Scientific status:** `[LEAN-PROVEN] [NOVELTY PROVISIONAL] [SIGNIFICANCE CONDITIONAL]`
- **Paper lane:** *Before There Was Time: Holographic Universality and the Integrability Barrier*

## Statement

Let `delta_i` be pairwise commuting derivations of a field `L/K`. Suppose the derivative of a
boundary state `z` has terminal principal law

```text
delta_i z = sum_j a_(i,j) y_j.                              (1)
```

Commutativity one step beyond the boundary forces the first-prolongation identities

```text
sum_j a_(i,j) delta_k y_j = sum_j a_(k,j) delta_i y_j       (2)
```

for every pair of law directions `i,k`.

If law space has at least two directions and the first tail packet

```text
{delta_k y_j : (k,j)}                                       (3)
```

is linearly independent over `K`, then every coefficient `a_(i,j)` is zero. Algebraic
independence of `(3)` is more than sufficient.

Thus a nonzero terminal principal symbol cannot be followed by the disjoint algebraically
independent tail used in the free-word universality theorem when the basis derivations commute.

## Proof

Apply `delta_k` and `delta_i` to the two instances of `(1)`. Pairwise commutativity gives `(2)`.
For `i != k`, the left side of `(2)` is supported on the free tail block `(k,j)` and the right side
on the disjoint block `(i,j)`. Linear independence makes both coefficient rows zero. Choosing
`k != i` for every `i` kills the whole terminal matrix.

The unconditional Lean theorems are in
`formal/GaloisForLFunctions/HTGeometry/CommutingPrincipalSymbolProlongation.lean`:

- `commutingDerivations_principalSymbol_firstProlongation`;
- `commutingDerivations_freeTail_forces_zeroSymbol`;
- `commutingDerivations_algebraicallyIndependentTail_forces_zeroSymbol`.

## Meaning for the universality theorem

The ordered-word construction realizes every common-degree projective algebraic horizon because
its derivations need not commute. The naive replacement of ordered words by symmetric occupation
states does not preserve that proof: a free terminal tail violates `(2)` unless the horizon symbol
is zero.

The abelian realization problem is therefore not a multinomial-normalization exercise. It is a
module-prolongation problem. A valid commuting realization must replace the free tail by a
prolonged module whose syzygies satisfy every cross-derivative compatibility identity while still
keeping the selected one-parameter jet tower algebraically independent away from the horizon.

This identifies the missing external law in the commuting/QFT lane: not an arbitrary homogeneous
ideal alone, but a homogeneous ideal together with an involutive or formally integrable
prolongation module.

## Physics interpretation `[CONJECTURE]`

If commuting law directions model compatible pretemporal observables, `(2)` is a zero-curvature
compatibility law before a time direction is chosen. A nontrivial holographic horizon must then be
carried by correlated descendant sectors. Independent Fock descendants are too free to be
integrable. In QFT language this points toward Ward identities, gauge constraints, or equations of
motion as necessary prolongation syzygies; no such physical identification is proved here.

## Novelty and anti-theatre gate

The cross-derivative mechanism is classical parent theory, not claimed as new: Janet--Riquier
completion, Spencer symbol prolongation, formal integrability of PDE systems, and differential
algebra with several commuting derivations all impose compatibility conditions under
prolongation. Exact searches found no formulation connecting that mechanism to an algebraically
independent terminal tail or to varying-direction ordinary hypertranscendence horizons.

Primary parent references checked:

- E. Rosen, *Prolongations in differential algebra* (2005), for higher prolongations with
  commuting Hasse--Schmidt derivations: `https://arxiv.org/abs/math/0510235`;
- D. Pierce, *Fields with several commuting derivations* (2007), for the geometric theory of
  partial differential fields: `https://arxiv.org/abs/0708.2769`;
- V. Gerdt and Y. Blinkov, *Involutive Bases of Polynomial Ideals* (1999), for Janet/Pommaret
  involutive completion: `https://arxiv.org/abs/math/9912027`.

The elementary no-go theorem is therefore only provisionally novel in formulation. It is not
Fields-level alone. Its significance is as the sharp boundary in a larger classification:

```text
free noncommuting laws  -> arbitrary projective horizons;
commuting laws          -> prolonged/involutive horizon modules only.
```

The medal-level question is to classify which projective schemes admit a prolongation module that
retains complete one-direction hypertranscendence off the scheme.

## RH impact

Any RH model using several commuting arithmetic derivations cannot import the free-word universal
tail. It must exhibit explicit cross-derivative syzygies. This strengthens the anti-redressing
gate: arbitrary horizon topology is available only before arithmetic integrability is imposed.

## Verification

- [x] unconditional Lean proof of first prolongation
- [x] unconditional Lean proof of linear-independent-tail no-go
- [x] unconditional Lean proof of algebraically-independent-tail no-go
- [x] direct source check
- [x] targeted module build
- [x] complete axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [ ] classify non-free prolonged modules that escape the no-go
- [ ] independent expert literature audit of the exact hypertranscendence formulation
