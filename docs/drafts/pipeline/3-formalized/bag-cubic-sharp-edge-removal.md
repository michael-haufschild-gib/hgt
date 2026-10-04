# BAG cubic sharp-edge removal

- **ID:** C28.56s
- **Stage:** 3-formalized
- **Route:** BAG, full signed C28.44 cubic; the RH goal is unchanged.
- **Status:** paper proof and unconditional Lean producer complete. Direct leaf
  and all three public axiom audits pass; standard logical axioms only.

## Mathematical target

Remove all three sharp prime-band edges at a growing width H=N^(1/4), with
error o(N/log^2 N) in the complete noncontracting cubic, along integer band
scales. This resolves literal endpoint transfer in the signed zero/stationary-trace attack. It does
not estimate the remaining interior cubic or its growing rational modes.

The preceding zero-form card identified nonzero endpoint amplitudes. Assigning
rapid Fourier decay to the sharp band or to fixed-width interpolation is wrong.
The audited repair estimates the actual edge contribution before smoothing.

## Source basis

ChiDegreeTwoRootMatrix supplies a verified finite Gram/Schur proof pattern,
Sieve.KuzminLandauInterval the full-integer prefix bound,
Sieve.AlmostOrthogonality finite Schur duality,
Sieve.SeparatedRowSum and HarmonicLogBound the harmonic row sum.
LogPhasePhysicalWindow constructs the actual W; its derivative has a uniform
bound on [0,4] by smoothness and compactness, as already used in
ChiPrimeGaussianProgressionProfile. The root-phase matrix itself is NOT the
matrix needed here and must not be substituted as though it were.

## Formalized paper proof

For any one fixed original-band index, prove the complete other-two-variable
bilinear bound C*sqrt(N*(1+log(N+1))). Permit arbitrary coefficients of modulus
at most one in each of those variables, while retaining the literal V, W and
1/r. This is compatible with the known full trilinear obstruction: only the
fixed-index slice is being bounded.

1. For fixed numerator p, take columns r and full integer samples q. The column
   is W(p*q/(r*N))*exp(2*pi*i*p*q/r). For r,r' within the same quarter-band,
   0<d=|r-r'|<=N/4, the frequency gap Delta=p*d/(r*r') satisfies
   d/(4N)<=Delta<=1/2. Thus every full integer prefix correlation of the pure
   phase is O(N/d), by Kuzmin–Landau in one integer band.
2. The actual weighted Gram correlation has sample weight
   W(p*q/(r*N))*W(p*q/(r'*N)). Its modulus is at most one and its discrete total
   variation is bounded by an N-independent constant: each derivative is
   O(1/N) and there are O(N) samples. Complex Abel summation therefore retains
   the same O(N/d) correlation bound. No two-dimensional amplitude separation
   or replacement of W is necessary.
3. The diagonal is O(N); harmonic row summation gives O(N*log(N+1)) Gram norm.
   Finite Schur and Cauchy give the bilinear estimate. The row prime mask is
   removed only AFTER Cauchy, by enlarging a nonnegative squared norm to all
   integer samples. Column prime masks are zero coefficients. Four disjoint
   quarter-bands cover the columns, with a fixed constant loss.
4. For fixed denominator r, interchange the role of the sampled numerator and
   the column numerator. The frequency gap is d/r; on a quarter-band it lies
   [d/(2N),1/4]. The same window-product variation and Schur proof apply. The
   fixed-q case follows from the literal p,q symmetry.
5. V is bounded on the source band and 1/r<=1/N. The two coefficient squared
   norms are O(N) and O(1/N), respectively, so the slice bound above follows
   even without a prime-count asymptotic. The removed p=r or q=r contraction
   sums in a fixed slice are O(1), hence obey the same bound.
6. An endpoint strip contains O(H+1) integers. A telescoping difference of
   products of three cutoff values, each in [0,1], expresses the complete
   sharp-minus-smoothed off-diagonal using three such edge slices. Therefore
   its norm is at most C*(H+1)*sqrt(N*(1+log(N+1))). For H=N^(1/4), its ratio
   to N/log^2 N tends to zero. Both contraction exclusions remain throughout.

The new smooth cutoff must equal one outside the edge strips, vanish smoothly
at the outer endpoints and have values in [0,1]. A fixed ContDiffBump/step
construction supplies it. Its derivative costs still belong in the subsequent
stationary estimate; this theorem alone does not promise scale-free derivatives.

## Required completion evidence

Actual weighted phase correlations, all fixed-variable slice bounds and the
full three-edge comparison are proved in
`formal/GaloisForLFunctions/RHTower/ChiPrimeGaussianCubicSharpEdges.lean`.
The public little-o theorem assumes no analytic estimate. Public declarations:

- `primeGaussianCubicSmoothedOffDiagonal`
- `exists_primeGaussianCubic_smooth_band_comparison`
- `exists_primeGaussianCubic_smooth_band_negligible_error`

Direct production audit53962, `lake --old env lean` on the leaf with its output
olean, exits0 without diagnostics. Axiom audit96616 exits0; all three public
declarations depend only on propext, Classical.choice and Quot.sound. Wired into
RHTower; no umbrella/full build. Lint68844 exits1 on 14 unrelated unreachable
modules, with no error for this leaf. Logs:
`/tmp/bag-cubic-sharp-edges-{final,axioms,lint}-01a0.log`.

## Construction record

Scratch `/tmp/BagCubicEdgeBilinear01a0.lean`, check20283 exit0: actual window
variation, full weighted Gram/Schur operator, four-block assembly, reciprocal
and linear frequency geometry, prime-mask reindexing and literal Gaussian
factorization all checked. The resulting fixed-index complete prime slice has
squared norm O(N*(1+log(N+1))) for arbitrary bounded separate weights. This
instantiates the actual source and assumes no analytic cancellation premise.

Check56098 exit0 additionally verifies both noncontracting exclusions, all three
edge slices, the exact telescoping comparison, and an explicit smooth bump
equal to one on [N+H,2N-H], zero outside (N,2N), with values in [0,1]. The actual
sharp-minus-smooth squared norm is bounded by C*(H+1)^2*N*(1+log(N+1)).
Prime masks, the coupled W and every original triple remain. The source's
denominator-first order was explicitly permuted in the exact identity.

The H=N^(1/4) little-o capstone is now production-audited as recorded above.
It follows from the squared comparison and log^5(N)/N^(1/2) tending to zero.

## Exact frontier contribution and surviving problem

The actual sharp source can now be replaced by an explicitly constructed smooth
full-band source at the contraction scale, with growing boundary strips. This
is a new analytic producer, not an assumed slice estimate or an identity alone.
It does NOT produce the interior cubic main/cancellation, growing moments or
positive self-return. C28.44 and RH remain open.

The cutoffs are scale dependent. Their derivative costs remain in any later
uniform stationary/zero-trace estimate; this theorem does not justify treating
those derivatives as bounded independently of N, or dropping boundary Fresnel
terms. Next hard target: the complete signed interior zero-pair/prime-mode
aggregate with these costs retained.
