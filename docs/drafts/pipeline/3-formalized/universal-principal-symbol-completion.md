# Before There Was Time: universal principal-symbol completion by a nilpotent detector

- **ID:** `universal-principal-symbol-completion`
- **Stage:** 3-formalized
- **Type:** THEOREM / GENERALIZED CLIFFORD / HYPERTRANSCENDENCE / QUANTUM DETECTOR
- **Scientific status:** `[LEAN-PROVEN] [UNCONDITIONAL RELATIVE TO STATED ALGEBRAIC HYPOTHESES] [NOVELTY PROVISIONAL]`

## Main theorem

Let `K` be a characteristic-zero field containing a primitive `d`th root of unity, `d>1`, and let
`V` be finite-dimensional.  Suppose a finite linear pencil

```text
A_0 : V -> End_K(M_0)
```

satisfies

```text
A_0(v)^d = F(v) I
```

for a degree-`d` form `F`, with no smoothness or concision assumption.  Then there is an explicit
finite extension `M` and a new pencil

```text
A : V -> End_K(M)
```

such that

```text
A(v)^d = F(v) I
```

and

```text
Lambda^2 V -> End_K(M),  u wedge v |-> [A(u),A(v)]
```

is injective.

Thus every finite generalized-Clifford linearization admits a finite maximal-principal-symbol
completion without changing its scalar form.  Combined with finite linearizability, every
homogeneous form would possess a maximally noncommutative exact hypertranscendence horizon; smooth
Waring geometry would no longer be needed for existence.

The formal theorem also proves the rational differential-field consequence: the complete-jet
dependence horizon remains exactly `F = 0`, while the full exterior derivation commutator map is
injective.

## Proposed construction

Let `C,S` be a finite clock/shift pair with

```text
C S = q S C,   C^d=S^d=I.
```

Let `N(v)` be the regular finite representation of a generalized Grassmann packet with

```text
N(v)^d=0
```

and injective exterior commutator map.  On a finite tensor state space define

```text
X(v)=A_0(v) tensor C tensor I,
Y(v)=I tensor S tensor N(v),
A(v)=X(v)+Y(v).
```

Because `X(v)Y(v)=qY(v)X(v)`, primitive-order quantum binomial cancellation gives

```text
A(v)^d=X(v)^d+Y(v)^d=F(v)I.
```

Grade the Grassmann state space by nilpotent degree.  Applied to the vacuum, the commutator of
`A(u),A(v)` has three disjoint components:

```text
degree 0: [X(u),X(v)],
degree 1: the two cross commutators,
degree 2: I tensor S^2 tensor [N(u),N(v)].
```

Projection to degree two therefore decodes the detector commutator and proves injectivity.

## External object and its laws

The only external object is the nilpotent detector packet.  It must be constructed, not assumed,
with all of the following laws:

1. finite state space with a vacuum and exact degree projections;
2. pairwise ordered `q`-commuting generators;
3. each generator has `d`th power zero;
4. every linear combination has `d`th power zero;
5. ordered quadratic monomials send the vacuum to distinct degree-two states;
6. the degree-two readout kills the scalar and cross sectors exactly.

These laws are realized on the finite representative phase space `(I -> Z/dZ)` by boundary-killed
shifts with the same tail-charge cocycle as the cyclic quantum torus.  The modules
`GaloisForLFunctions.HTGeometry.FiniteQuantumGrassmannRepresentation` and
`GaloisForLFunctions.HTGeometry.UniversalPrincipalSymbolCompletion` prove all six laws, the clocked
coupling, exact scalar preservation, the pair decoder, exterior commutator injectivity, and the
field-horizon theorem.

## Novelty gate

Known parent theory includes generalized Grassmann algebras, their finite representations,
clock/shift tensor constructions, polynomial sum linearization, and generalized-Clifford
representations in fractional supersymmetry.  The construction of a zero-form nilpotent sector is
therefore not new by itself.

The provisional residue is the **principal-symbol completion theorem**: adjoining the nilpotent
sector while preserving an arbitrary scalar form and proving that a degree-two decoder makes the
entire canonical bivector map injective.  Searches have not located this theorem or its exact
hypertranscendence-horizon consequence.  Absence of a hit is not a priority claim.

## Anti-theatre gates

1. **Completed:** construct the truncated detector and prove its `d`th-power-zero law in Lean.
2. **Completed:** prove ordered quadratic independence by an explicit vacuum readout.
3. **Completed:** construct the clocked extension in Lean; no abstract existence hypotheses remain.
4. **Completed:** prove exact separation of degree zero, one, and two terms.
5. **Completed:** the narrow module build and final scalar/horizon/commutator axiom audit pass;
   dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.
6. **Open novelty gate:** audit generalized-Clifford sum/product constructions from 1969--1998 for
   an equivalent faithful-bivector statement.

## Lean declarations

File:
`formal/GaloisForLFunctions/HTGeometry/UniversalPrincipalSymbolCompletion.lean`

- `quantumPrincipalSymbolCompletion_pow`
- `quantumPrincipalCompletionPairReadout_principalBracketPair`
- `quantumPrincipalSymbolCompletion_principalBracketPair_linearIndependent`
- `quantumPrincipalSymbolCompletion_endomorphismCommutatorMap_injective`
- `quantumPrincipalSymbolCompletion_dependenceHorizon_eq_zeroLocus`
- `quantumPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol`

The reusable minimal-hypothesis decoder is in
`formal/GaloisForLFunctions/HTGeometry/GeneralExteriorPrincipalSymbolDecoder.lean` as
`endomorphismCommutatorMap_injective_of_principalBracketPair_linearIndependent`.

## Physical meaning

The scalar law `F` is unchanged, while a finite nilpotent boundary sector is added solely to make
every oriented two-plane observable.  This is a precise algebraic model of a holographic detector
that exists before time: it changes no scalar reality constraint and introduces no evolution
flow, yet it retains all incompatibility data.  It is not a QFT until a star structure, positivity,
locality, and a state-selection law are supplied.

## RH impact

If the completion theorem holds for every form, maximal principal-symbol rank becomes entirely
nonselective and cannot imply RH.  For Xi, only a distinguished arithmetic completion, positivity,
or an extremal minimal detector width could carry RH content.  The theorem would sharply rule out
generic finite linearization and generic commutator faithfulness as missing RH sources.
