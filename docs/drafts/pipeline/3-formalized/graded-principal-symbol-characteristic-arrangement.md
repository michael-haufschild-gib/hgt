# Before There Was Time: the graded characteristic arrangement

- **ID:** `graded-principal-symbol-characteristic-arrangement`
- **Stage:** 3-formalized / intrinsic application open
- **Type:** THEOREM / FILTERED DIFFERENTIAL ALGEBRA / LAW-SPACE GEOMETRY
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED] [NOVELTY UNVERIFIED] [APPLICATION OPEN]`
- **Statement:** For a derivation acting triangularly on an algebraically free cyclic filtration,
  with possibly different principal raising symbol at every layer, the complete jet is
  algebraically independent exactly when no layer symbol vanishes. For a linear law family, the
  non-hypertranscendental locus is the union of all layer-symbol kernels.

## Claim

Let `k subset K subset L` be fields, let `D` be a `k`-derivation of `L` compatible with a
derivation of `K`, and let `(u_n)` be algebraically independent over `K`. Suppose

```text
D u_n = s_n u_(n+1) mod span_K{u_0,...,u_n}.
```

Then

```text
{D^n u_0 : n >= 0} is algebraically independent over K
    iff
s_n != 0 for every n.
```

More generally, for a linear space `g` of compatible derivations and layer symbols
`sigma_n : g -> K`, the characteristic locus is

```text
Char(u_0) = union_n ker(sigma_n),
```

and its complement is exactly the hypertranscendental law locus.

## Proof route

Write `p_n=product_(j<n) s_j`. Induction through the filtration gives

```text
D^n u_0 = p_n u_n mod span_K{u_0,...,u_(n-1)}.
```

If every `s_j` is nonzero, every finite jet packet is an invertible lower-triangular transform of
the corresponding source packet, so all finite packets and hence the complete jet are
algebraically independent.

If `s_m=0`, the finite subspace `span_K{u_0,...,u_m}` is stable under `D`: the lower layers raise
within it and the top layer has zero raising coefficient. Every later jet therefore lies in this
finite-dimensional subspace. The first `m+2` jets are linearly dependent and hence algebraically
dependent. This proves the converse without a genericity assumption.

## Lean formalization

`formal/GaloisForLFunctions/HTGeometry/GradedPrincipalSymbolHorizon.lean` proves the complete claim
without placeholders:

- `gradedPrincipalJet_sub_product_smul_mem` proves the all-order prefix-product leading term;
- `gradedPrincipalJet_algebraicIndependent` proves the noncharacteristic direction;
- `derivation_principalFiltration_invariant_of_gradedSymbol_eq_zero` proves exact filtration
  trapping after a vanished layer;
- `not_algebraicIndependent_gradedPrincipalJet_of_symbol_eq_zero` converts trapping into an
  unconditional finite-dimensional linear relation;
- `gradedPrincipalJet_algebraicIndependent_iff` proves the exact equivalence;
- `gradedPrincipalSymbol_unique` proves that every layer symbol is determined by the law action;
- `gradedPrincipalSymbolLawSpace_characteristicSet_eq_iUnion_ker` and its complement theorem prove
  the complete law-space arrangement statement.

The targeted leaf build passed. The terminal axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; the invariant-subspace theorem itself does not use
`Classical.choice`. Repository formal lint passed. No numerical experiment was used.

## Significance and anti-theatre gates

The constant-symbol theorem is the special case `s_n=s`, whose characteristic locus is one
kernel. The graded theorem produces a countable characteristic arrangement and can distinguish
laws which cross some observable layers but not others. The abstract triangular argument alone is
not Fields-level. Scientific significance requires an intrinsic filtration whose layer symbols
encode a central special function or observable theory and whose source packet is independently
proved algebraically free.

The physical reading remains `[CONJECTURE]`: before a time ray is selected, the constraint law
space carries a stratified horizon. Crossing every layer produces an infinite algebraically free
history; touching one characteristic layer traps the entire future jet in a finite observable
sector. No claim about cosmology or QFT is made until an actual observable algebra realizes the
hypotheses.

## Novelty gate

External parents are filtered modules and associated graded symbols, characteristic varieties of
cyclic D-modules, differential type and typical dimension, and hypertranscendence under changes of
derivation. Malgrange proves filtration-independence and generic integrability properties for
characteristic varieties of analytic differential systems. Dreyfus--Hardouin--Roques and
Adamczewski--Dreyfus--Hardouin prove algebraic independence of successive derivatives for fixed
difference-equation solutions through parametrized difference Galois theory. Lower-triangular
transfer of algebraic independence is also standard.

Exact searches across those parent vocabularies found no source identifying a parameterized
ordinary differential-algebraic law spectrum with the union of layer-symbol kernels. This is an
absence-of-hit report, not a priority claim. Candidate novelty is only that exact spectrum identity
and its intrinsic special-function realization, not the triangular proof, filtered-symbol
language, or characteristic-variety analogy.

## RH impact

No direct RH implication is known. The theorem would become relevant only if a completed
`L`-function admits an intrinsic multi-law filtration whose characteristic arrangement interacts
with its functional-equation or critical-line constraints.

## Lean obligations

- [x] all-order prefix-product principal-term congruence
- [x] algebraic independence when every layer symbol is nonzero
- [x] invariant finite-filtration theorem after one symbol vanishes
- [x] exact algebraic-independence equivalence
- [x] law-space union-of-kernels theorem
- [x] uniqueness of the graded symbol
- [x] targeted build, formal lint, and terminal axiom audit
