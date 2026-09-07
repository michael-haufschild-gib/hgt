# Complete EDQ flux: logarithmic Fourier truncation error

Stage: formalized in Lean; the complete frequency-truncation error is closed.
This closes a correction to the full signed flux, not the missing RH upper bound.
The frontier map is read-only.

Use the actual primitive U_N and reciprocalFlux from
`EulerDeletionFluxWeightReplacement`. For positive e and Q define

```
P_(e,Q)(k)=e/(2*pi^2)*sum_(m=1..Q)
  (cos(2*pi*m*k/e)-1)/m^2,
U_(N,Q)(k)=sum_(e=1..N)mu(e)*P_(e,Q)(k).
```

Replace only U_N by U_(N,Q) in each complete divisor channel
k=d*(floor(N/d)+j+1), j>=0. Denote the resulting full flux by R_(N,Q).
Every time tail remains present. Q truncates the Bernoulli frequency m;
it does not truncate the product m*j appearing after channel expansion.

The existing cosine series of the periodic primitive gives
`P_e(k)=e/(2*pi^2)*sum_(m>=1)(cos(2*pi*m*k/e)-1)/m^2`.
Since |cos-1|<=2 and the reciprocal-square tail beyond Q is at most 1/Q,

```
|P_e(k)-P_(e,Q)(k)| <= e/(pi^2*Q),
|U_N(k)-U_(N,Q)(k)| <= N*(N+1)/(2*pi^2*Q).
```

For 1<=d<=N and q=floor(N/d)>=1, the full channel reciprocal mass is
at most 1/(d^2*q)<=2/(d*N), by telescoping 1/[j(j-1)]. Both the
truncated channel and the error channel are absolutely convergent.
Summing the error over the actual coefficients gives

```
|reciprocalFlux(N)-R_(N,Q)| <= (N+1)*harmonic(N)/(pi^2*Q).
```

At Q=N+1 this is harmonic(N)/pi^2 for every N, including N=0.
No numerical estimate, RH premise or assumed Möbius cancellation enters.
The retained finite-frequency arithmetic sum still needs its own bound.

## Lean statements and verification

Module: `GaloisForLFunctions.RHTower.EulerDeletionFluxFourierTruncation`.
Namespace: `RHTower.DeletionFlux`.

- `fourierPrimitive`, `truncatedPrimitive`, `truncatedReciprocalFlux` define
  the literal finite-frequency primitives and full divisor-channel sum.
- `flux_fourier_error N Q` proves the bound with positive cutoff Q+1 for
  every natural N,Q, without an arithmetic hypothesis.
- `flux_fourier_cutoff_error N` proves the harmonic(N)/pi^2 bound for every N.

The scratch check passed. Final single-module build passed in 5.6 seconds;
only the new leaf compiled, with dependency oleans reused. The new module
is wired into RHTower; no umbrella or full build ran. The five new public
declarations were audited in a separate scratch file: each uses only
`propext`, `Classical.choice`, and `Quot.sound`. No numerical input or new
axiom occurs. Source and error-channel summability are proved before any
subtraction of infinite sums.

Repository lint returned one error: the separately present untracked module
`GaloisForLFunctions.RHTower.RealSphericalComplementaryWeights` is not reachable
from its theorem-area umbrella. No lint error names the new EDQ module. This
unrelated module was left untouched. The three owned scratch files were removed;
all owned Lean processes completed. The frontier map remains read-only.
