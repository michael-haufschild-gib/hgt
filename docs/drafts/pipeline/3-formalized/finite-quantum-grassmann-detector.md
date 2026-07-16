# A finite nilpotent quantum-Grassmann packet is a faithful exterior detector

- **ID:** `finite-quantum-grassmann-detector`
- **Stage:** 3-formalized
- **Type:** THEOREM / GENERALIZED GRASSMANN / PRINCIPAL SYMBOL
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [KNOWN OBJECT, NOVEL ROLE PROVISIONAL]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FiniteQuantumGrassmannRepresentation`

## The theorem

Let `K` be a characteristic-zero field, `d>1`, and `q` a primitive `d`th root of unity.  On the
finite state space

```text
K^((I -> Z/dZ))
```

there are explicit boundary-killed generators `Theta_i` such that

```text
Theta_i Theta_j = q Theta_j Theta_i  for i<j,
Theta_i^d = 0.
```

For every coefficient vector `c`,

```text
(sum_i c_i Theta_i)^d = 0.
```

Nevertheless, the exterior commutator map

```text
Lambda^2(K^I) -> End(K^((I -> Z/dZ)))
```

is injective.

## Construction and proof

Use the cyclic quantum-torus tail-charge cocycle, but set a generator action to zero whenever its
shifted coordinate is already zero.  Boundary killing is coordinatewise, so it preserves ordered
`q`-commutation.  A state of coordinate height `r` is killed after `r+1` applications; since every
representative has height below `d`, each generator has `d`th power zero.  Quantum multinomial
cancellation makes every linear combination `d`-nilpotent.

The ordered product `Theta_j Theta_i` sends the vacuum delta state to the distinct pair state with
ones in coordinates `i,j`.  These readouts prove quadratic monomial independence.  The canonical
quantum-torus decoder then reconstructs every bivector from its commutator image.

## Significance and novelty gate

Finite generalized Grassmann algebras and boundary-nilpotent root-of-unity representations are
known parent theory.  The object and nilpotence laws are not claimed as new.  Its provisional new
role is as a **zero-scalar, information-complete principal-symbol detector**: it changes no
degree-`d` scalar form but retains all exterior two-plane data.  The universal completion theorem
still requires an explicit clocked coupling and a proof that degree-two readout kills every scalar
and cross term.

## Physical interpretation gate

This is a finite detector sector with no scalar classical law: its entire degree-`d` horizon is
zero, yet its pairwise incompatibility channel is lossless.  It is a candidate pre-temporal
boundary sector, not a Hilbert-space QFT or probability model.

## RH impact

The detector is universal and arithmetic-free.  If it completes arbitrary scalar pencils, generic
commutator faithfulness cannot be an RH source; only arithmetic selection, positivity, or minimal
detector width can remain relevant.

## Lean verification

Direct check and narrow build pass.  Principal declarations are
`finiteQuantumGrassmannGenerator_mul_of_lt`,
`finiteQuantumGrassmannGenerator_pow_degree`,
`finiteQuantumGrassmannPairOperator_linearIndependent`,
`finiteQuantumGrassmannSymbol_pow_degree_zero`, and
`finiteQuantumGrassmann_endomorphismCommutatorMap_injective`.  Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; the nilpotence theorem itself uses only `propext` and
`Quot.sound`.
