# Before There Was Time: quadratic-width holographic completion

- **ID:** `quadratic-width-principal-symbol-completion`
- **Stage:** 1-in-progress
- **Type:** THEOREM / PRINCIPAL SYMBOL / REPRESENTATION WIDTH / HOLOGRAPHIC DETECTOR
- **Scientific status:** `[MAIN THEOREM LEAN-PROVEN] [WIDTH CARDINALITY FORMULA LEAN-PENDING] [NOVELTY PROVISIONAL]`

## Main theorem

Let `K` be a characteristic-zero field containing a primitive `d`th root `q`, with `d > 1`, and
let

```text
A_0 : K^n -> End_K(M)
```

satisfy `A_0(v)^d = F(v) I`.  There is a scalar-preserving completion with injective exterior
commutator symbol whose detector has only the three grades

```text
K  +  K^n  +  Lambda^2 K^n.
```

Consequently, when `M` is finite-dimensional, the completed state-space dimension is

```text
d * (1 + n + binomial(n,2)) * dim(M),
```

rather than the `d^(n+1) * dim(M)` width of the full representative-phase-space detector.

## Construction

For each coordinate `i`, define a generator `N_i` on grades zero, one, and two by

```text
N_i(1) = e_i,
N_i(e_j) = q e_{i,j}  if i < j,
N_i(e_j) =   e_{j,i}  if j < i,
N_i(Lambda^2) = 0.
```

Then

```text
N_i^2 = 0,
N_i N_j = q N_j N_i  for i < j,
N(v)^d = 0,
```

and `N_j N_i(1) = e_{i,j}` gives an exact pair decoder.  A cyclic clock shift couples this
three-grade packet to `A_0`; root-of-unity cancellation preserves `F` exactly.

## Novelty gate

The three-grade packet is a truncated quantum exterior algebra and is not claimed as new by
itself.  Minimal faithful representations of the free two-step nilpotent Lie algebra are also
known: for rank `n >= 4`, Cagliero--Rojas prove
`mu(L_{n,2}) = ceil(sqrt(2n(n-1))) + 2`.

The provisional residue is the **scalar-constrained completion bound**: a uniform quadratic-width
construction that simultaneously preserves an arbitrary represented degree-`d` scalar form and
makes its canonical exterior commutator faithful.  Literature search has not located this exact
constraint-preserving theorem.  Absence of a hit is not a priority claim.

## Anti-theatre gates

1. **Completed:** construct the three-grade detector and prove square-zero and ordered
   `q`-commutation in Lean.
2. **Completed:** prove all linear combinations have `d`th power zero using the primitive-root
   multinomial theorem.
3. **Completed:** prove pair readout and exterior commutator injectivity in Lean.
4. **Completed:** couple to the cyclic clock and prove scalar preservation for arbitrary `A_0`.
5. **Completed:** prove the exact complete-jet horizon and rational-field principal-symbol theorem.
6. Formalize the finite-dimensional width formula and compare it to the full detector.
7. Audit constrained nilrepresentations, generalized Clifford sums, and Ulrich-bundle literature.

## Lean declarations

Files:

- `formal/GaloisForLFunctions/HTGeometry/QuadraticQuantumDetectorRepresentation.lean`
- `formal/GaloisForLFunctions/HTGeometry/QuadraticWidthPrincipalSymbolCompletion.lean`

Principal declarations:

- `quadraticQuantumDetectorGenerator_sq`
- `quadraticQuantumDetectorGenerator_mul_of_lt`
- `quadraticQuantumDetectorSymbol_pow_degree_zero`
- `quadraticQuantumDetector_endomorphismCommutatorMap_injective`
- `quadraticWidthPrincipalSymbolCompletion_pow`
- `quadraticWidthPrincipalSymbolCompletion_endomorphismCommutatorMap_injective`
- `quadraticWidthPrincipalSymbolCompletion_fieldHorizon_and_maximalPrincipalSymbol`

Both narrow module builds pass.  The final capstones depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## Physical meaning

The detector stores only vacuum, one-event, and two-event data.  It has no bulk evolution and no
higher-grade memory, yet it sees every oriented two-plane while changing no scalar law.  This is a
literal finite holographic boundary model: pairwise incompatibility is stored in an area-like
grade, before the shift suspension introduces an emergent time direction.

This is not yet a QFT.  A star operation, positivity, locality, and a selected state are still
external constraints.

## RH impact

Quadratic-width completion would strengthen the no-go result: even low-width exterior faithfulness
is generic and therefore cannot by itself select Xi or imply RH.  The potentially arithmetic
invariant is the *minimal scalar-constrained width* under a distinguished star/positivity/locality
structure, not unconstrained commutator rank.
