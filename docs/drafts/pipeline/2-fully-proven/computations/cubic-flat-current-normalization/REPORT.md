# Flat cubic source: normalization discriminator

2026-09-05. Numerical exploration, followed by exact reconstruction; placement
under `computations` does not make numerical evidence a proof.

## Question and outcome

For orthogonal projections P,Q,R, set S=P+Q+R and
K=[P,Q]+[Q,R]+[R,P]. Does source flatness `[S,K]=0` force
`K(3K²+S²(3I−S)²)=0`, the active spectral relation of the known
two-channel charged loop?

**No.** The search found violations in dimension three. Exact reconstruction
uses projections onto `(1,0,1)/√2`, `(1,1,0)/√2`, `(0,1,1)/√2`.
They have rational entries, S=(I+J)/2, K=circ(0,1/4,-1/4), and the
proposed left side equals K≠0. This is not a finite-dimensional nonzero
cubic trace: its source cubic is zero. Boundary charge arises only after
Hardy compression and passage to infinite-dimensional operators.

## What ran

- Authorized RunPod `157.157.221.29:27094`; isolated directory
  `/tmp/hgt-cubic-flat-QjUw71`.
- Python 3.8.10, NumPy 1.24.4, SciPy 1.10.1; 16 worker processes,
  one BLAS thread each. No GPU needed.
- 32 independent seeded Grassmann-chart fits: eight each in dimensions
  2,3,4,6, ranks 1,1,2,3. Seeds `52000+100*dimension+i`, `0≤i<8`.
- P fixed diagonal; Q,R represented as exact-form orthogonal projectors
  `V(V*V)⁻¹V*`. Least squares minimizes the full flatness commutator.
  Analytic Jacobians checked by directional central differences (step 10⁻⁶).
  Tolerances 10⁻¹²; at most 400 objective evaluations per fit.
- Recorded compute wall time 0.0954 s, excluding SSH and interpreter setup.
  The question resolved at small dimension; no larger sweep was run.

| Dimension | Strong numerical violations / 8 |
|---|---:|
| 2 | 0 |
| 3 | 6 |
| 4 | 3 |
| 6 | 3 |

“Strong” here means flat residual <10⁻⁹ and polynomial residual >10⁻⁴;
these reporting thresholds do not certify exact feasibility. Largest flat,
projection, adjoint, and Jacobian-check residuals were respectively
2.29×10⁻¹⁰, 1.79×10⁻¹², 7.67×10⁻¹³, 8.65×10⁻¹⁰.
Example: dimension 3, seed 52303, flat residual 7.68×10⁻¹⁴,
polynomial residual 3.2532. Raw matrices are retained in `results.json`.
No experiment workers remained after completion.

Reproduce on RunPod:

```sh
python3 experiment.py --output results.json
```

## Positive consequence

A three-column cyclic source frame supplies a different normalization law.
Writing G=circ(1,x,y), K=circ(0,x−y²,x²−y), exact algebra gives

`Tr(G dK)=d[2(x³−y³)]+3(y dx−x dy)`.

For y=conj(x), the curvature is 12i times planar area. Thus source flatness
does not force the two-channel spectral curve or its normalization.
For x=r·u, |u|=1, two copies with 6r²=1 give a unit logarithmic
phase current modulo an explicit polynomial derivative. A real amplitude
graph retains the full complex source value without changing this first-jet
pairing. These exact bridges, not larger numerical cutoffs, are the useful
continuation. Detailed statements and proof obligations are on
`../../../1-in-progress/cubic-flat-current-normalization.md`.

**Limit:** this does not establish arithmetic Hardy admission, equality of
the resulting operator trace with a Xi divisor index, any subunit nuclear
budget, or a law annihilating off-line charge. Scalar source winding and
its multiplicity normalization already exist in the corpus. The experiment
does not itself derive the requested arithmetic charge or prove RH.

Known parents are Toeplitz commutator/area and relative-index theory; see
[Blower–Doust, IEOT 98 (2026), Prop. 3.13](https://link.springer.com/article/10.1007/s00020-025-02818-6)
and [Thiang–Xia, arXiv:2401.07449](https://arxiv.org/abs/2401.07449).
Corpus and targeted arXiv/journal searches through 2026-09-05 did not locate
this exact projection-frame bridge. No literature-priority claim is certified.

## Artifacts

Downloaded hashes matched remote originals:

```text
2402192fa45df9137d01f00779df28236d1844e50e565618bdfabaf16a3fc9cd  experiment.py
f0d7dc5cc5a8d71bf4336f101d34cb07accec1b351e1d2f058d057231afec5fb  results.json
```
