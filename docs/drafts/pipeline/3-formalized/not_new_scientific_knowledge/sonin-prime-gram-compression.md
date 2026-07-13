# Finite prime Sonin Gram compression modulo compacts

- **ID:** `sonin-prime-gram-compression`
- **Stage:** 3-formalized
- **Type:** THEOREM / FORMALIZATION / TOP-DOWN SIMPLIFICATION / BRIDGE
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SoninPrimeGramCompression.lean`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
  `[NOT AN RH PROOF]`

## Statement

For an injective finite prime family `p_i`, let `L_i` be the corresponding even Sonin dilation
corners and let

```text
T_A=sum_(i,j) A_(i,j)L_i^*L_j
```

for a complex matrix `A` with zero diagonal.  Lean proves that every finite matrix coefficient
compression survives every compact perturbation simultaneously.  For all coefficient vectors
`x,y` and every compact `K`,

```text
|sum_(l,k)conj(y_l)x_k A_(l,k)|
 <= ||y||_2 ||x||_2 ||T_A-K||.                           (1)
```

Writing `Ax` for the finite matrix-vector product gives the full operator-norm consequence

```text
||Ax||_2 <= ||x||_2 ||T_A-K||.                           (2)
```

There is no factor depending on the number of primes.

## Mechanism

The existing common-shell theorem supplies paired inputs for each scale.  Ratio separation also
separates the inverse-dilated input shells themselves.  Lean proves that these raw shells form an
orthonormal finite family at every shell index, while their Sonin projections converge back to the
raw shells.  Hence finite projected combinations converge in norm to their coefficient `l2` norm,
remain weakly null, and are annihilated in norm by every compact operator.

The already formalized prime-ratio table identifies the limiting Gram coefficient with `A_(l,k)`
off the diagonal.  The zero-diagonal hypothesis kills the complete diagonal collision tail.  Finite
summation then gives `(1)`, and testing with `y=Ax` gives `(2)`.

## Top-down consequence

For prime potentials `a_p`, take

```text
A_(p,q)=(a_p-a_q)/sqrt(pq),
x_p=1/sqrt(p).
```

The finite weighted-variance identity yields

```text
||Ax||_2^2=(sum_p 1/p) *
  (sum_(p,q)|a_p-a_q|^2/(pq))/2.
```

Thus `(2)` gives a one-particle Calkin lower bound for half the complete pair energy.  This removes
the Hilbert tensor product and the paper-only two-particle Calkin estimate from the prime-seam route.
The remaining source theorem is an upper estimate for one concrete zero-diagonal Gram coboundary.

The reciprocal-prime specialization is also formalized.  With `w_i=1/p_i`, the difference matrix
and square-root weight vector satisfy

```text
||x||_2^2=sum_i w_i,
||D_w(u)x||_2^2=(sum_i w_i) E_w(u)/2,
sqrt(E_w(u)/2) <= ||T_(D_w(u))-K||
```

for every compact `K`.

## Formal declarations

```text
RHTower.inverseDilatedEvenShellEven_orthonormal_scales_of_ratioSeparation
RHTower.norm_finitePairedEvenSoninInputCombination_tendsto
RHTower.finitePairedEvenSoninInputCombination_weakly_tendsto_zero
RHTower.finitePrimeGram_pairedCombination_inner_tendsto_bilinear
RHTower.norm_finiteMatrixBilinear_le_norm_finitePrimeEvenDilationGram_sub_compact
RHTower.finiteCoefficientL2Norm_matrixMulVec_le_norm_finitePrimeEvenDilationGram_sub_compact
RHTower.finiteCoefficientL2Norm_weightedDifference_mulVec_sq
RHTower.sqrt_half_finiteWeightedDifferenceEnergy_le_norm_primeGram_sub_compact
RHTower.sqrt_half_finitePrimeDifferenceEnergy_le_norm_primeGram_sub_compact
```

## Verification

- [x] exact leaf-module build
- [x] full finite sesquilinear compression
- [x] full matrix-vector lower estimate
- [x] every compact perturbation allowed
- [x] no cardinality loss
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] add the leaf import to the umbrella after concurrent umbrella edits settle
- [x] package the reciprocal-prime difference-matrix algebra as a final Lean corollary
- [ ] prove the source-side cofinal upper estimate
- [ ] RH
