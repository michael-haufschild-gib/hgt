# Every finite projective horizon admits a maximally noncommutative realization

- **ID:** `free-horizon-maximal-commutator-rank`
- **Stage:** 3-formalized
- **Type:** THEOREM / DIFFERENTIAL ALGEBRA / NONCOMMUTATIVE REALIZATION
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [NOVELTY PROVISIONAL]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FreeHorizonMaximalCommutatorRank`

## The theorem

Let `K` be a characteristic-zero field, let `V=K^ι` be a finite law space, and let `X⊂P(V)` be
the common zero locus of any finite homogeneous polynomial family.  If the lifted terminal
equation packet is nonempty, then there are a rational differential field `L/K`, one observable
`x∈L`, and a linear law map

```text
rho : V -> Der_K(L)
```

such that:

1. `X` is exactly the set of nonzero directions where the complete ordinary jet of `x` is
   algebraically dependent;
2. outside `X`, the jet is algebraically independent;
3. the exterior commutator map

```text
B_rho : Λ²V -> Der_K(L),       v∧w |-> [rho(v),rho(w)]
```

is injective.

Thus every finite projective hypertranscendence horizon has at least one realization with the
largest possible linear commutator rank `dim(Λ²V)`.

## Proof mechanism

The complete horizon realization propagates every terminal equation into an infinite free-word
tail.  Fix one terminal root.  Evaluating `[rho(e_i),rho(e_j)]` on that root produces the
difference of the two oriented length-two tail variables

```text
y_(i,j)-y_(j,i).
```

Those variables are algebraically independent.  A linear decoder sends each oriented variable to
one half of `e_i∧e_j`.  Evaluation followed by the decoder is the identity on `Λ²V`, so `B_rho`
has a left inverse and is injective.  Lean proves the decoder identity and combines it with the
universal exact-horizon theorem in one existential result.

## Holographic sandwich

For any horizon `X`, let `chi_HT(X)` be the projective line-contact kernel-avoidance index from the
main holographic-horizon card.  Every realization obeys

```text
chi_HT(X) ≤ rank(B_rho) ≤ dim(Λ²V),                                   (1)
```

and the upper endpoint is always attained.  For a general plane curve of degree at least four,
`chi_HT(X)=dim(Λ²V)=3`; hence every realization is already maximal.

The lower endpoint need not yet be attained.  Constructing a realization with
`rank(B_rho)=chi_HT(X)` is the sharp horizon--Lie-kernel realization problem.

## Novelty and significance gate

Known ingredients not claimed as novelty:

- free associative words and shifts;
- algebraically independent polynomial generators;
- exterior-power factorization of alternating maps;
- left inverses as injectivity certificates.

Exact searches found no external theorem stating that every finite homogeneous projective variety
is simultaneously an exact complete hypertranscendence horizon and the horizon of a realization
with injective derivation-commutator symbol.  This is an absence-of-hit result, not a priority
certificate.

The free maximal endpoint alone is not Fields-scale: it is an explicit universal construction.
Its scientific role is to prove that the projective horizon imposes a lower quantum-complexity
floor but never obstructs maximal noncommutativity.  The potentially major classification problem
is the exact set of kernels and intermediate ranks compatible with a fixed horizon.

## QFT interpretation gate

The theorem supplies derivations of a commutative field.  The canonical Heisenberg module embeds
them faithfully as noncommuting linear operators and preserves their commutators.  A physical QFT
interpretation still requires a star representation, Hilbert completion, state, positivity,
domains, and locality.

## RH impact

If an arithmetic construction produces a finite projective horizon for a completed `L`-function,
this theorem guarantees an algebraic realization with maximal commutator rank.  It does not select
an arithmetic realization, supply positivity, or prove that the `L`-function has the proposed
horizon, so it is not an RH source theorem.

## Lean verification

The touched module direct-checks and its narrow build target passes.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  The repository formal lint gate passes with no
active `sorry`, `admit`, project `axiom`, `opaque`, or `unsafe` declaration.
