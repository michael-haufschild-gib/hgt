# Quantum-torus principal symbols are information-complete

- **ID:** `quantum-torus-principal-symbol`
- **Stage:** 3-formalized
- **Type:** THEOREM / QUANTUM TORUS / EXTERIOR PRINCIPAL SYMBOL / HYPERTRANSCENDENCE
- **Scientific status:** `[LEAN-PROVEN] [AXIOM-AUDITED] [NOVELTY PROVISIONAL]`
- **Lean module:** `GaloisForLFunctions.HTGeometry.QuantumTorusPrincipalSymbol`

## The theorem

Let `K` be a characteristic-zero field, `I` a finite linearly ordered coordinate set, and
`G_i` finite-dimensional internal operators satisfying

```text
G_i G_j = q G_j G_i    for i<j,     q != 1.
```

Assume the ordered quadratic monomials

```text
G_j G_i,   i<j
```

are linearly independent.  Then the exterior commutator symbol of the canonical pencil

```text
A(c)=sum_i c_i G_i
```

is injective.  More generally, for every injective linear coefficient map `L : V -> K^I`, the
symbol of `A o L` has injective commutator map

```text
Lambda^2 V -> End(M).
```

The generalized-Clifford shift suspension transports this injectivity unchanged to the exterior
commutator map of rational-field derivations.

## Proof

For every increasing pair `i<j`, linear independence supplies a coordinate decoder on the span of
the monomials `G_jG_i`.  Extend it linearly to all endomorphisms and prescribe

```text
G_jG_i |-> (q-1)^(-1) (e_i wedge e_j).
```

Because `[G_i,G_j]=(q-1)G_jG_i`, decoder after commutator is the identity on the canonical basis of
`Lambda^2(K^I)`.  This is a literal left inverse, not a rank count.  Naturality of exterior powers
and injectivity of `Lambda^2 L` transport the result to `V`.  The general principal-symbol kernel
theorem then transports it to the differential field.

## Significance gate

The theorem identifies the exact algebraic datum responsible for a lossless holographic
two-plane channel: independence of ordered quadratic quantum-torus monomials.  Higher power
relations determine the scalar horizon; quadratic monomial independence determines whether all
oriented incident two-planes remain observable.  These are logically separate constraints.

This theorem is a central reusable mechanism, but the universal smooth-hypersurface theorem still
requires unconditional construction of the finite quantum torus, its monomial basis, the
root-of-unity power identity, and a spanning Waring packet.

## Physical interpretation gate

The decoder is an exact algebraic tomography map: horizon commutators reconstruct every incoming
bivector.  It does not by itself provide a star operation, positivity, locality, a vacuum state,
or a Hilbert completion.  Those remain physical axioms rather than consequences of maximal
principal-symbol rank.

## RH impact

The theorem can certify maximal rank once an arithmetic coefficient map and quantum packet have
been constructed.  Since the criterion is generic and nonselective, it is not an RH source by
itself; RH relevance must enter through a distinguished arithmetic representation or positivity
constraint.

## Lean verification

The touched module direct-checks and its narrow build target passes.  Its principal results are
`decodedQuantumCommutatorMap_eq_id`,
`quantumTorus_endomorphismCommutatorMap_injective`, and
`quantumTorus_derivationCommutatorMap_injective`.  Their axiom audits report only `propext`,
`Classical.choice`, and `Quot.sound`.
