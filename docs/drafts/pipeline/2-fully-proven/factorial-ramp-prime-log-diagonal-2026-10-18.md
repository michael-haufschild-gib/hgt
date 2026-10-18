# Exact factorial ramp diagonal: logarithmic prime field and signed pole

- **Stage:** 2-fully-proven; Lean verification in progress.
- **Route:** RW, actual factorial sources from WL.
- **Parent:** `../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md`.
- **Claim:** Evaluate the complete prime quadratic pairing of the actual ramp, prove the pole nonpositive, and express the literal Weil diagonal without von Mangoldt weights.
- **Not claimed:** Nonnegative ramp diagonal, nonnegative optimized Gram margin, or RH.

## Exact statements

Write N=n+1, epsilon=sourceFactorialCollar N, f=factorialRampSource n, H=harmonicCorrection N, and

    C_N = log binomial(4N,2N) - 2 log binomial(2N,N),
    L_(epsilon,K)(u)
      = exp(u/2) sum_(1<=j<=K) log(j) clampedRamp epsilon (j exp(u)/K),
    G_N = (L_(epsilon,4N)-4 L_(epsilon,2N)+4 L_(epsilon,N))/sqrt N.

Then, for every n, without arithmetic or regularity premises:

1. The actual translated prime field equals G_N on u>=0 whenever its atom cutoff covers 4N.
2. The literal infinite prime quadratic sum equals integral f(u) G_N(u) du. This integrand is integrable.
3. The full half-line polar integral is

       P_N = -(1+epsilon/2) H C_N / N <= 0,
       |P_N| <= 2(5 log(4N+1)+1)/N.

4. The actual reflected-ramp Weil diagonal is

       factorialSpanWeil n 1 0
         = gammaBracket(0) autocorr(f,0) + biScaleLevyEnergy(f)
           - 2 integral f(u) G_N(u) du - 2(1+epsilon/2) H C_N/N.

## Dependency-closed paper proof

For a weight w supported on integers <=K and M>=K, discard all products j*m>K in the finite rectangle. Reindex the remaining hyperbola by k=j*m. Each divisor fibre has total weight sum_(m|k) Lambda(m)=log k. Thus sum_m Lambda(m) sum_j w(j*m)=sum_k log(k) w(k).

The clamped weight w(k)=clampedRamp epsilon (k/v) vanishes beyond K when v>0 and (1+epsilon)v<=K+1. The collar endpoint is included because the clamp is zero there. For v=K exp(-u), u>=0, the actual collar budget epsilon K<=1 establishes this condition at K=N,2N,4N. Hence the actual prime field equals G_N on the entire support of f. Outside that half-line f is zero. Integrating the product gives the exact quadratic prime sum; compact support supplies the literal infinite-sum cutoff.

For any compact continuous real source, factor its autocorrelation Fourier transform at i/2 and use evenness. The half-line polar integral equals the product of the source's positive and negative exponential moments. The already-proved exact ramp moments evaluate that product to P_N. No C² assumption is used.

Factorial logarithms give chebyshevBiNullProducer N=C_N. Vandermonde gives binomial(4N,2N)=sum_j binomial(2N,j)^2>=binomial(2N,N)^2, hence C_N>=0. The existing harmonic-correction sign yields P_N<=0. Existing moment bounds yield its stated envelope.

Reflection preserves autocorrelation. Substitute the prime and polar identities into the verified compact finite-jump Weil formula. This proves the displayed diagonal identity with both polar branches retained.

## Lean files and verification

- `formal/GaloisForLFunctions/BiScaleUncertainty/ClampedPrimeLogResummation.lean`: passed direct `lake --old env lean -j 1` compilation.
- `formal/GaloisForLFunctions/BiScaleUncertainty/CompactAutocorrelationPolarMoment.lean`: passed direct compilation.
- `formal/GaloisForLFunctions/BiScaleUncertainty/FactorialBiNullPolarSign.lean`: passed direct compilation.
- `formal/GaloisForLFunctions/BiScaleUncertainty/FactorialRampDiagonalIdentity.lean`: direct verification running.
- Nineteen public endpoints prepared for `/tmp/biscale_ramp_diagonal_axioms.lean`; final audit, umbrella wiring, index and lint pending.

## Remaining obstacle

The diagonal sign is now an explicit archimedean/logarithmic inequality. The pole lowers the diagonal. The Gram result still requires a lower bound strong enough to dominate M²/(4D); no such bound is supplied here. Corpus-only work; no numerical experiment or external novelty claim.
