# EDQ compensated moment feedback

- **ID:** EDQ-COMPENSATED-MOMENT-FEEDBACK
- **Stage:** 1-in-progress
- **Type:** ATTEMPT
- **Target:** Bound the complete signed physical source by every positive cutoff power on cofinal cutoffs, then use the existing off-line exclusion theorem.
- **Status:** No stronger source bound. The scalar update below is an exact paper calculation; its apparent contraction retains an uncontrolled arithmetic forcing. No new Lean theorem is asserted.

## Exact moment update

Use the moments and divisor sum from
[the complete Estermann transfer](edq-estermann-inverse-frequency-transfer.md):

```
H_N = sum_(n<=N) mu(n)/n,
J_N = sum_(n<=N) mu(n)*log(n)/n,
D_N = sum_(n<=N) tau(n).
```

For integers `N>=1`, put

```
K_N = 1 + J_N - log(N)*H_N,
a_N = D_N/N - log(N),
r_N = K_N - a_N*H_N,
lambda_N = log((N+1)/N),
u_N = mu(N+1)/(N+1).
```

The previous compensated-frequency identity at `L=N` gives
`N*r_N = sum_(l<=N) U_N(l)`. Finite sum increments give exactly

```
H_(N+1) = H_N + u_N,
K_(N+1) = K_N - lambda_N*H_N.
```

The two occurrences of `mu(N+1)*log(N+1)/(N+1)` cancel when deriving the
second equation. Thus, whenever `a_N != 0`,

```
K_(N+1) = (1-lambda_N/a_N)*K_N + (lambda_N/a_N)*r_N.
```

This would be a convex averaging step if `0<lambda_N<=a_N`, but `r_N`
is not an independently bounded input. Retaining its full update gives

```
r_(N+1) = r_N
  + (D_N/N - tau(N+1))/(N+1)*H_N
  - a_(N+1)*u_N.
```

Indeed `D_(N+1)=D_N+tau(N+1)`, so
`lambda_N+a_(N+1)-a_N=(tau(N+1)-D_N/N)/(N+1)`.
These identities require neither a divisor-error asymptotic nor RH.

## Corrector test

The homogeneous update in the original `(K,H)` coordinates is the shear
`(K,H) -> (K-lambda*H,H)`. It retains the neutral direction `(K,0)`.
A fixed positive definite quadratic corrector cannot make this update a
strict contraction on every state: that nonzero fixed vector would have
to lose energy while remaining unchanged. This is a test of the proposed
source-independent inference, not an obstruction to an estimate for the
actual forced Möbius trajectory.

More explicitly, for
`E(K,H)=K^2+2*b*K*H+c*H^2`, with `c>b^2`, its complete increment is

```
E(K-lambda*H,H+u)-E(K,H)
 = -2*lambda*K*H + (lambda^2-2*b*lambda)*H^2
   + 2*b*K*u + 2*(c-b*lambda)*H*u + c*u^2.
```

The arithmetic source `u=mu(N+1)/(N+1)` and both mixed source pairings
remain. Dropping them or treating `r_N` as an independent small forcing
does not establish a decay estimate. A variable corrector must retain its
own variation and quantitative comparison with the original energy.

## Squared harmonic transform: exact inverse, unchanged required scale

The next conjecture tested was that the signed transform

```
Z_N = sum_(d<=N) mu(d)/d^2 * H_(floor(N/d))^2
```

admits an upper bound `C_alpha*N^(-alpha)` for every `0<alpha<1`.
This is a one-sided bound on a signed quantity. It would control the
critical harmonic scale, but no independent estimate for `Z_N` was found.

Its exact inverse has positive weights:

```
H_N^2 = sum_(d<=N) 1/d^2 * Z_(floor(N/d)).
```

To prove the identity, expand the finite double sum, use
`floor(floor(N/d)/e)=floor(N/(d*e))`, and group by `k=d*e`.
The coefficient is `k^(-2)*sum_(e|k) mu(e)`, which vanishes unless `k=1`.
No infinite rearrangement or convergence premise is needed.

For `d<=N`, `floor(N/d)>=N/(2*d)`. Consequently an all-cutoff upper
bound `Z_n<=C*n^(-alpha)` implies

```
H_N^2 <= C*2^alpha*N^(-alpha) * sum_(d<=N) d^(alpha-2)
      <= C*2^alpha*(1+1/(1-alpha))*N^(-alpha).
```

Conversely, a bound of that scale on `H_n^2` gives the same displayed
upper bound for `abs(Z_N)` by `abs(mu(d))<=1`. Thus this transformation
preserves the power-bound problem; its positive inverse does not improve
the exponent. The sharper guess that `Z_N` is eventually nonpositive is
not proved or assumed. It would demand an additional sign theorem for
the complete arithmetic expression.

The complete increment also retains the mixed forcing. Since only
divisors of `N` change a floor quotient,

```
Z_N-Z_(N-1)
 = (2/N)*sum_(d|N) mu(d)*mu(N/d)/d * H_(N/d-1)
   + (1/N^2)*sum_(d|N) mu(d)*mu(N/d)^2.
```

At a prime `p`, this reduces exactly to `-2*H_(p-1)/p`: the two diagonal
terms cancel. Their cancellation therefore leaves a signed harmonic
quantity; it does not provide the required upper bound. The known corpus
statement that `N*H_N^2` cannot tend to zero also prevents replacing the
critical target by decay strictly faster than that scale.

## Sources and scope

Four cached deep/method searches covered compensated scale contraction,
the single word `Bellman`, harmonic/logarithmic moment evolution, and
Möbius convolution of harmonic squares. Candidate statements, source
arguments and method obligations were inspected with the proof-idea and
ingredient lanes. Results were partial with pending/source-only compiler
metadata. `MoebiusFloorInversion` supplies finite divisor regrouping;
`CoprimeMoebiusHarmonic` supplies an exact inversion identity, not a
square bound. Bellman subsolution bounds retain the missing subsolution
condition. `HarmonicTailResolvent` already identifies its invertible
logarithmic tail transform without supplying a favorable spectral sector.
No existing theorem was rebuilt or re-audited.

Broad arXiv searches used avalanche, observability and hypocoercivity.
The concrete new transfer test used Carrillo--Koo--Song,
[Conditional hypocoercivity for nonlinear kinetic Fokker--Planck equations](https://arxiv.org/html/2607.26616v1)
(submitted 29 July 2026; the displayed manuscript is dated 24 August).
Section 2.2 pairs momentum with an inverse-Poisson density correction;
its estimates use the actual kinetic equation, positive density bounds
and entropy dissipation. The equations above supply neither that density
model nor its dissipation. Only the corrector mechanism was tested;
no paper estimate or constant is imported into Lean.

These are paper deductions and failed estimate attempts. No new Lean
theorem, complete no-go package, stronger EDQ energy bound, or RH proof
is claimed. The arithmetic mixed terms remain the required next target.
No computations, builds or axiom checks ran. The frontier map and
route-independent ledger were left unchanged.
