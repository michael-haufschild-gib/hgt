# Route L: cofinal cubic source criterion

- **ID:** L-COFINAL-CUBIC-SOURCE-CRITERION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Lean status:** Closed in [MobiusCofinalCubicEnergyCriterion.lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusCofinalCubicEnergyCriterion.lean), including cofinal-shift, explicit canonical-sequence, and bounded-return implications.

## Theorem

For `k>=0`, set `delta_k=2/(k+2)` and

```text
E_k(N) = sum_(m,n<=N) mu(m)mu(n) m²n²/(m+n)^(5+delta_k).
```

If, for every `k`, there is a finite real `C_k` such that `E_k(N)<=C_k` for every natural cutoff `N`, then RH holds. The constants may depend arbitrarily on `k`. Neither an estimate at `delta=0` nor one bound uniform in `k` is required.

## Proof

The Lean theorem `generalReciprocalMomentKernel_three_add_delta` identifies `E_k(N)` with `finiteGeneralReciprocalEnergy (3+delta_k) delta_k N`. The closed two-order comparison gives, for every `delta>0`,

```text
finiteGeneralReciprocalEnergy (1+delta) delta N
 <= A(delta) * finiteGeneralReciprocalEnergy (3+delta) delta N,
A(delta) = [4(2+delta)/(1+delta)] [4(4+delta)/(3+delta)] > 0.
```

The finite reciprocal/Gamma bridge then identifies

```text
finiteMobiusGammaHankelEnergy N (1+delta)
 = Gamma(1+delta) * finiteGeneralReciprocalEnergy (1+delta) delta N.
```

Thus the assumed `C_k` gives a cutoff-independent upper bound for the concrete Gamma--Hankel energy at exponent `1+delta_k`. Since `1+delta_k=2*(1/2+1/(k+2))`, the exact finite logarithmic `L²` identity transfers this to the canonical abscissa `sigma_k=1/2+1/(k+2)`. The closed theorem `mobiusLaplaceCanonicalFiniteSectionEnergyBounded_iff_riemannHypothesis` then gives RH. All factors in the transfer are finite and positive for every fixed `k`; no uniformity as `k→infinity` is used.

## Stronger bounded-return criterion

Even an all-cutoff ceiling is unnecessary. Suppose that for every `epsilon>0` there is some `delta` with `0<delta<2*epsilon` and a real `C_delta` such that

```text
E_delta(N) <= C_delta
```

holds at **arbitrarily large natural cutoffs** `N`, where `E_delta` is the same literal cubic signed form with exponent `5+delta`. Then RH holds. The two-order inequality and finite Gamma--Hankel bridge above hold at each individual cutoff, so they carry every bounded-return cutoff to a bounded return of the base Gamma--Hankel energy at `sigma=(1+delta)/2`. Its signed off-diagonal covariance is at most that energy because the diagonal is nonnegative. The corpus's closed Fatou-subsequence receiver `mobiusLaplaceCofinalGammaHankelOffDiagonalFrequentlyUpperBounded_iff_riemannHypothesis` finishes the proof. This is formalized as `riemannHypothesis_of_routeLCofinalCubicEnergyFrequentlyBounded`.

## Arithmetic producer now required

The remaining problem is to bound these *literal signed* cubic forms at arbitrarily large cutoffs on positive shifts cofinal at zero. The [Abel-prefix sign atlas](../2-fully-proven/l-abel-prefix-mixed-gram-sign.md) rewrites each form as the weighted log-Fourier energy of frozen Mertens prefixes. Existing unconditional twisted-Möbius estimates in the corpus give an `o(N)` coefficient bound over a broad frequency window; after half-power weighting this still permits growth of order `o(sqrt N)` and does not establish a bounded return. The next source argument may choose both a favorable shift and favorable cutoffs, and its ceiling may deteriorate rapidly as the shift approaches zero.
