# Before There Was Time: the linear holographic horizon theorem

- **ID:** `before-time-linear-holographic-horizon`
- **Stage:** 3-formalized
- **Type:** THEOREM / HYPERTRANSCENDENCE / GENERALIZED CLIFFORD / HOLOGRAPHIC WIDTH
- **Scientific status:** `[PROVED HERE] [LEAN-PROVEN] [UNCONDITIONAL RELATIVE TO STATED ALGEBRAIC HYPOTHESES] [NOVELTY PROVISIONAL]`

## Main theorem

Let `K` be a characteristic-zero field containing a primitive `d`th root of unity, let `d >= 3`,
and suppose

```text
A_0 : K^n -> End_K(M)
```

is a finite linear pencil satisfying

```text
A_0(v)^d = F(v) I.
```

There is an explicit completion

```text
A : K^n -> End_K(M')
```

such that

```text
A(v)^d = F(v) I
```

and the full principal-symbol map

```text
Lambda^2 K^n -> End_K(M'),  u wedge v |-> [A(u),A(v)]
```

is injective.  The added clocked detector has exactly

```text
d(2n+1)
```

`M`-valued coordinate slots.  The complete-jet hypertranscendence horizon is still exactly
`F=0`, and shift suspension transports the injective principal symbol to the rational differential
observable field.

The result is uniform in `F` and in the initial representation `A_0`.  It assumes no smoothness,
Waring decomposition, concision, positivity, or arithmetic structure.

## The membrane construction

The unclocked detector has only

```text
n lower states + 1 membrane state + n upper states.
```

For every law coordinate `i`, its generator acts by

```text
lower(i) -> membrane -> upper(i) -> 0
```

and kills the other coordinate channels.  For a coefficient vector `v`, the aggregate detector
`N(v)` satisfies

```text
N(v)^3 = 0.
```

For `i < j`, the commutator `[N_i,N_j]` has a private matrix coefficient from `lower(j)` to
`upper(i)`.  Reading those coefficients gives a literal left inverse on every coordinate
bivector, hence on the entire exterior square.

The scalar pencil and detector are placed on the same cyclic phase clock.  Their aggregate values
obey

```text
X(v)Y(v) = q Y(v)X(v).
```

Primitive-root binomial cancellation and `N(v)^d=0` for `d>=3` then give

```text
(X(v)+Y(v))^d = X(v)^d = F(v)I.
```

No pairwise quantum-commutation relation among the detector generators is used.  Only aggregate
cubic nilpotence and the one clock/detector phase relation are required.

## General principal-symbol law

The proof separates the representation from the exterior algebra.  For any finite pencil, linear
independence of its coordinate commutators gives an explicit decoder on their span; extending that
decoder produces a left inverse to the full exterior commutator map.  Thus the true hypothesis is
not a quantum-torus presentation but independent coordinate brackets.

## External structure and its laws

Unconstrained maximal noncommutativity is now cheap: a single all-to-all membrane stores every
two-plane in the operator algebra without changing the scalar constraint.  Therefore neither the
scalar horizon nor maximal principal-symbol rank selects a physical universe.

The missing external structure must constrain the representation itself.  The live candidates are:

1. a star operation identifying the lower and upper dual horizons;
2. a positive state selecting which operators are observable;
3. a locality law bounding how many law directions may meet one membrane channel;
4. an arithmetic covariance law selecting a distinguished representation rather than an arbitrary
   completion;
5. a minimality principle for the resulting constrained width.

The membrane construction is deliberately nonlocal: one central state couples to all `n`
directions.  A bounded-valence locality law is therefore capable of turning the presently
universal completion into a nontrivial width invariant.

## Novelty gate

Known parent theory includes root-of-unity quantum binomial identities, generalized Clifford
linearization, nilpotent representations, and faithful representations of the free two-step
nilpotent Lie algebra.  Cagliero and Rojas prove

```text
mu(L_{n,2}) = ceil(sqrt(2n(n-1))) + 2,  n >= 4,
```

so a linear-size commutator-faithful nilrepresentation is not itself new.  Their theorem also shows
that the present `2n+1` detector is not an unconstrained minimal representation.

The provisional residue is the exact conjunction of four properties:

1. arbitrary scalar-law preservation;
2. linear coordinate width for every degree `d>=3`;
3. a full exterior principal-symbol decoder;
4. the exact hypertranscendental complete-jet horizon after shift suspension.

Searches of generalized-Clifford, free-nilpotent-representation, root-of-unity, and operator-pencil
literature have not located this scalar-preserving completion theorem.  Absence of a hit is not a
priority claim.  The result does not clear the Fields-Medal significance gate until a constrained
star/positivity/locality invariant is proved to classify or obstruct important horizons.

## Anti-theatre gates

1. **Completed:** prove the exact detector cardinality `2n+1` in Lean.
2. **Completed:** prove aggregate cube-zero for every detector-pencil value.
3. **Completed:** construct an explicit pair readout and prove full exterior commutator injectivity.
4. **Completed:** prove the exact clocked cardinality `d(2n+1)`.
5. **Completed:** couple to an arbitrary scalar pencil and prove exact scalar-law preservation.
6. **Completed:** prove the exact complete-jet dependence horizon and rational-field commutator
   theorem.
7. **Completed:** targeted module builds pass; the capstones use only `propext`,
   `Classical.choice`, and `Quot.sound`.
8. **Open:** formulate and prove the first nontrivial constrained-width theorem under locality or
   positive-star axioms.

## Lean declarations

Files:

- `formal/GaloisForLFunctions/HTGeometry/GeneralExteriorPrincipalSymbolDecoder.lean`
- `formal/GaloisForLFunctions/HTGeometry/LinearWidthThreeStepDetector.lean`
- `formal/GaloisForLFunctions/HTGeometry/LinearWidthPrincipalSymbolCompletion.lean`

Principal declarations:

- `endomorphismCommutatorMap_injective_of_principalBracketPair_linearIndependent`
- `linearWidthDetectorIndex_card`
- `linearWidthDetectorSymbol_cube_zero`
- `linearWidthDetector_endomorphismCommutatorMap_injective`
- `linearPrincipalCompletionCoordinate_card`
- `linearWidthPrincipalSymbolCompletion_pow`
- `linearWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective`
- `linearWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol`

## Physical statement

Before time, the construction has no trajectory and no clock reading that propagates a state.  It
has two boundary copies of possible directions and one membrane through which incompatibilities
are composed.  The quadratic number of oriented two-planes is stored holographically in matrix
coefficients of a linear-size state boundary.  The cyclic phase is introduced only to couple this
pre-temporal packet to a scalar reality constraint without changing that constraint.

The theorem therefore gives a no-go principle for algebraic models of reality: scalar law plus
maximal noncommutativity is insufficient, because both can be manufactured uniformly.  Physical
content must enter through the external gluing, positivity, locality, or minimality law.

## RH impact

The theorem is adverse to any RH strategy based only on finite scalar linearization plus maximal
principal-symbol rank: those properties are generic at linear detector overhead for every
represented law of degree at least three.  A viable Xi invariant must instead be a distinguished
arithmetic constrained width or an obstruction imposed by positivity, star structure, or locality.
RH remains secondary; no RH implication is claimed.
