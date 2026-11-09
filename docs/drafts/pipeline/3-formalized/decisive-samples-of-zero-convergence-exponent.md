# Decisive samples of zero convergence exponent

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B136, quantitative sampling boundary.

## Result

There exists one set D of prime powers with both properties:

1. For every s>0, ∑_{d∈D} d^{−s}<∞. In particular #D∩[1,X]≤C_s X^s for every s>0.
2. For every tempered zero configuration Z without real zeros, a uniform lower bound
   `2 Re lagStructure(Z,B,log d) ≥ −T` on D forces every zero onto Re s=½.
   Here B is the cubic box spline; no top-attainment assumption is used.

Counting growth therefore does not determine whether a sample decides purity. The
corpus's very-smooth sample and this decisive sample both have zero counting exponent.
The theorem supplies no bound for ζ's traces on D.

## Proof

Every positive prime-power mesh is decisive by gap iteration. For each k and each
member of compact impure chart k, some prime p has trace below −k at lag
(k+1)log p. These are open conditions because the actual trace is continuous on the
chart. Compactness gives a finite detecting block F_k of primes. Set
D=⋃_k {p^{k+1}:p∈F_k}.

Every impure tempered configuration without real zeros has a doubled encoding in
all sufficiently large charts. A lower bound −T on D contradicts a detecting block
with k>2T. Thus D decides purity.

Fix s>0 and choose N with (N+1)s>1. The blocks k<N are finite. For k=N+j and p≥2,

    p^{−(k+1)s} ≤ (2^{−s})^j p^{−(N+1)s}.

The right side has a convergent double sum: a geometric series times a p-series.
Hence the series over all detecting-block occurrences converges. Selecting one
occurrence per degree transfers convergence to D even if representations overlap.
For any finite F⊂D∩[1,X], each d∈F satisfies 1≤X^s d^{−s}; summing gives the
counting bound with C_s=∑_{d∈D}d^{−s}.

## Lean

`SurfaceOfSpecZ/DecisiveSamplesOfZeroConvergenceExponent.lean`, namespace
`GaloisForLFunctions.SurfaceOfSpecZ.ZeroExponentSample`:

- `exists_finite_power_block`
- `onLine_of_bddBelow`
- `summable_sample`
- `finite_count_le_rpow`, `count_le_rpow`
- `exists_decisive_sample_of_zero_convergence_exponent`

Verified by plain `lake --old env lean` on the leaf. Capstone axiom audits contain
only `propext`, `Classical.choice`, `Quot.sound`. Imported through the SurfaceOfSpecZ
umbrella into MainTheorems; no umbrella build.
