# The Fermat cubic qutrit is an information-complete hypertranscendence horizon

- **ID:** `fermat-cubic-qutrit-maximal-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM / GENERALIZED CLIFFORD ALGEBRA / EXTERIOR PRINCIPAL SYMBOL
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [NOVELTY PROVISIONAL]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FermatCubicWeylRepresentation`

## The theorem

Let `K` be a characteristic-zero field containing `omega` with

```text
omega^2 + omega + 1 = 0.
```

On the three-state space `M=K^(Fin 3)`, explicit clock, shift, and third Weyl operators define a
linear pencil `A : K^3 -> End_K(M)` such that

```text
A(c)^3 = (c0^3+c1^3+c2^3) I.
```

After generalized-Clifford shift suspension to the rational observable field, the complete
ordinary differential jet is algebraically dependent exactly on

```text
c0^3+c1^3+c2^3=0.
```

Simultaneously, the exterior differential commutator symbol

```text
Lambda^2(K^3) -> Der_K(L),   u wedge v |-> [rho(u),rho(v)]
```

is injective.  Thus every nonzero oriented two-plane of laws survives as a nonzero horizon
commutator.

## Exact decoder

The proof does not appeal to a dimension count.  Three matrix-coefficient readouts of an internal
endomorphism separate `[X,Y]`, `[X,Z]`, and `[Y,Z]`.  After normalization by the nonzero
cyclotomic factors, they define a linear decoder

```text
D : End_K(M) -> Lambda^2(K^3)
```

with

```text
D o B_A = id.
```

The general principal-symbol faithfulness theorem then transports this exact kernel statement
unchanged through double shift, symmetric observables, and the fraction field.

## Physical meaning and limit

This is a finite pre-temporal packet with lossless two-directional boundary data: the scalar
Fermat horizon records where complete differential dependence occurs, while its qutrit
commutators retain the full oriented bivector incident on that horizon.  This is an algebraic
information-completeness theorem, not yet a Hilbert-space or local-QFT model.

## Novelty gate

Clock/shift matrices, finite Heisenberg groups, qutrit Weyl algebras, root-of-unity multinomial
cancellation, and generalized Clifford linearization are known parent theory.  The claim under
novelty audit is their coupling to an exact ordinary hypertranscendence horizon with a proved
left inverse for the complete exterior commutator symbol.  No priority claim is made from an
absence of a search hit.

## RH impact

The result proves that a nonlinear cubic horizon can be realized with finite transverse width and
maximal noncommutative rank.  It does not select an arithmetic pencil or constrain the Xi
function, so it is an architectural input rather than an RH source theorem.

## Lean verification

The theorem `fermatCubicWeyl_maximalHorizon` combines the exact dependence locus with maximal
commutator rank.  The touched module direct-checks and its narrow build target passes.  Axiom
audits of the decoder identity, internal injectivity theorem, and maximal-horizon theorem report
only `propext`, `Classical.choice`, and `Quot.sound`.
