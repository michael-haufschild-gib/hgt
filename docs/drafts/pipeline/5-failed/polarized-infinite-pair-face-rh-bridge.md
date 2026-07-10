# Polarized infinite pair-face realization at the archimedean boundary

- **ID:** `polarized-infinite-pair-face-rh-bridge`
- **Stage:** 5-failed
- **Type:** REFUTED BRIDGE ARCHITECTURE
- **Date:** 2026-07-10
- **Verdict:** `[REFUTED AS STATED]` The complete pair-face invariant cannot be functorially lifted
  to translation-equivariant finite-support or Hilbert potentials while retaining the nontrivial
  prime-period action. The proposed pair-potential Sonin mechanism therefore fails before the RH
  negative-index identity is reached.
- **Formal endpoint:**
  `formal/GaloisForLFunctions/OrbitQuotientLiftNoGo.lean`

## Proposed bridge

For prime periods

```text
tau_p=i log(p)/(2 pi),
```

the route sought a Hilbert space `V`, local potentials `a_p in V`, and a functorial lift of every
finite compatible pair-face family to coefficients `a_p-a_q`. These coefficients were to act on
two-particle Sonin corners. Uniform Calkin control would force all `a_p` to coincide, an
archimedean anchor would force their common value to vanish, and a further index identity was
intended to identify that vanishing with RH.

The one-particle and quotient-level versions were already excluded: the canonical positive Euler
sum is unbounded modulo compacts, and a representation factoring through the dense period quotient
kills the nontrivial Mellin dilation action. The suggested repair was to lift pair-face divisors
before quotienting, using a transformation groupoid or crossed product.

## Exact algebraic mismatch

For a pair of directions, the residue module is a finite-support orbit quotient

```text
A_H=C[delta][G/H],
```

where `G` is the translation group and `H` contains the period subgroup. Triple compatibility in
the all-depth theorem is an equalizer condition: pair charges have equal pushforwards to every
triple quotient.

The simultaneous finite-divisor lifting lemma therefore produces vertex lifts `B_p` satisfying

```text
q_pq(B_p)=D_pq=q_qp(B_q).
```

The native relation is equality of restrictions. It is not the gradient relation

```text
D_pq=a_p-a_q.
```

Differences `B_p-B_q` belong to kernels of quotient maps and depend on the choice of lifts. They
are gauge discrepancies, not the pair-face invariant. In particular, a nonzero common lift has
all pair differences equal to zero while its pair-face charge remains nonzero.

## Equivariant lift obstruction `[LEAN PROVED]`

Let `G` be a commutative group, `H` an infinite subgroup, and `R` a nontrivial commutative
semiring. Orbit pushforward is the `G`-equivariant linear map

```text
q:R[G] -> R[G/H].
```

There is no `G`-equivariant linear section of `q`.

Indeed, let `e_[H]` be the basis vector of the identity orbit. Every `h in H` fixes `e_[H]`. An
equivariant section would lift it to an `H`-invariant finite-support vector in `R[G]`. If one
coefficient at `x` were nonzero, invariance would put the same nonzero coefficient at every
`h*x`. The orbit is infinite, contradicting finite support. Hence the lift is zero, contradicting
that it pushes forward to `e_[H]`.

Lean theorem:

```text
no_equivariant_orbitPushforward_section
```

The Hilbert version is equally rigid. If `f:G -> E` has summable squared norm and is invariant under
an infinite subgroup, then `f=0`: a nonzero coefficient would give a positive constant summable
over an infinite index set. Lean theorem:

```text
eq_zero_of_infinite_subgroup_leftInvariant_summable_normSq
```

Thus an orbit basis vector has no nonzero invariant lift in the finite-support regular module or
in its `l2` completion.

## Why a crossed product does not repair this card

A groupoid or crossed product can retain the nontrivial `H`-action by replacing a scalar orbit
coefficient with fiber data transforming under a representation of `H`. But the original
pair-face coefficient is scalar and has trivial stabilizer action. A canonical map from that
scalar to a nontrivial fiber is an intertwiner from the trivial representation, hence requires an
`H`-fixed fiber vector. The regular/Mellin Hilbert representation has no such nonzero vector by the
summable-norm theorem.

Choosing a noninvariant fiber vector or a decaying orbit weight adds an origin, phase, or fiber
state not contained in the pair-face invariant. The resulting object may be studied, but it is not
a functorial lift of `Comp_S` and the existing pair-face completeness theorem supplies no canonical
choice. Distributional orbit averages avoid `l2` vanishing but leave the Hilbert-potential setting
required by the Sonin coherence theorem.

## Functional equation and the common mode

Pair differences always annihilate constant potential families:

```text
(a_p-a_q)=0 when every a_p=a.
```

The functional equation supplies a reflection involution and parity grading, not a vanishing
anchor. The reflection-graded pair-face theorem permits nonzero reflection-fixed signatures.
Consequently FE symmetry does not remove the common pair-face mode.

An additional archimedean source map could be postulated, but proving that it is injective on the
common mode and has the required bounded/index sign is exactly a new source-built RH theorem. It
is not produced by the finite pair-face invariant. Defining it through `kappa_-(m_xi)`, zero
locations, Herglotz positivity, or the repaired index would be circular.

## Final conclusion

The target identity

```text
kappa_-(Pi_Sonin(Omega_xi))=kappa_-(m_xi)
```

is not merely unproved downstream. The proposed `Omega_xi` cannot be constructed functorially from
the stated pair-face data in the required Hilbert representation. Gate `0 -> 1` fails, so no
positive Lean formalization is warranted.

This does not prove that every HGT/RH bridge is impossible. A different route would need a new
source-defined groupoid-valued or distributional invariant, a replacement for pair-potential
coherence outside `l2`, and an independently constructed faithful index map. None of those objects
is supplied by this card.

## Gates

- [x] finite pair-face equalizer structure audited
- [x] equality-of-restrictions versus pair-gradient mismatch isolated
- [x] algebraic equivariant-section obstruction proved in Lean
- [x] square-summable invariant-lift obstruction proved in Lean
- [x] common-potential blindness recorded in Lean
- [x] crossed-product escape tested against stabilizer intertwiners
- [x] functional-equation anchor tested and rejected as insufficient
- [x] route retired before an RH-equivalent index shell was introduced

## Log

- 2026-07-10 -- Opened as the surviving pair-potential architecture after the direct quotient and
  one-particle routes failed.
- 2026-07-10 -- Re-read the pair-face realization theorem: its finite lift gives equal vertex
  restrictions, not edge gradients.
- 2026-07-10 -- Proved that infinite-orbit pushforward has no equivariant algebraic section and no
  nonzero square-summable invariant lift. This triggers the card's lift/continuity falsifiers and
  closes the proposed architecture.
