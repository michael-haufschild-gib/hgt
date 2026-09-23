# Route L: one integer-order source target

- **Status:** paper proofs below are complete; Lean formalization and the stated arithmetic bound are open.
- **Hard target:** for one fixed order, prove a power-sharp block mean square of the literal Möbius source

```
T_3(t) = sum_(n>=1) mu(n) n^(-3) exp(-2t/n),
A_3(K) = integral_K^(2K) T_3(t)^2 dt.
```

The exact source estimate sought is `A_3(K) <<_eta K^(-4+eta)` for **every** `eta>0`, with `K` dyadic. A bound `A_3(K) << K^(-4) (log(2K))^A` for one fixed `A` would suffice. The absolute-value estimate is only `O(K^(-3))`; one power of arithmetic cancellation remains.

## Fractional source transport

For `R>r>1`, `alpha=R-r>0`, and `t>0`, termwise Gamma integration gives the unconditional identity

```
T_r(t) = (2^alpha/Gamma(alpha))
  * integral_t^infinity (u-t)^(alpha-1) T_R(u) du.     (1)
```

Absolute Fubini is valid: after taking absolute values, the integral of the `n`th term is `Gamma(alpha) 2^(-alpha) n^(-r)`, and `sum n^(-r)<infinity`. This identity retains every literal Möbius coefficient; it is not an assumed decay law.

**Single-order sufficiency.** Suppose `A_3(U) <= C_eta U^(-4+eta)` for every dyadic `U>=1` and every `eta>0`. Fix `1<r<2`, choose `0<eta<r-1`, and put `alpha=3-r>1`. For `K<=t<=2K`, split (1) into `[t,4K]` and dyadic intervals `[U,2U]` with `U=2^j K`, `j>=2`. Cauchy--Schwarz and the assumed block bound give

```
integral_(U)^(2U) |T_3(u)| du <= C_eta U^(-3/2+eta/2).
```

On `[t,4K]`, `(u-t)^(alpha-1)<= (4K)^(alpha-1)`; the two block bounds give `O_(r,eta)(K^(alpha-5/2+eta/2))`. On each later dyadic interval the bound is `O_(r,eta)(U^(alpha-5/2+eta/2))`. Since `alpha-5/2+eta/2=1/2-r+eta/2<0`, the dyadic tail is summable. Thus

```
|T_r(t)| <= C_(r,eta) K^(1/2-r+eta/2)
  for every K<=t<=2K,
integral_K^(2K) T_r(t)^2 dt <= C_(r,eta) K^(2-2r+eta). (2)
```

The [geometric-to-continuous comparison](l-reciprocal-exponential-packet-reduction.md) changes this energy by only `O_r(K^(2-2r))`. Equation (2) therefore gives the actual geometric packet bound at every `1<r<2`. As `eta<r-1`, the weighted packet-energy series converges; exponents `r` can approach `1`, so the existing strict-right source-energy criterion excludes off-line zeros and proves RH. **No hypothesis on RH enters (1); the unproved input is the order-three arithmetic estimate.**

## Small shifts are already within the target

Let `H^c_(r,K)` be the continuous pair kernel in the preceding note and

```
O^c_(r,K,H) = sum_(1<=m<n<=m+H) mu(m)mu(n) H^c_(r,K)(m,n).
```

For every integer `H>=0` and `K>=1`,

```
|O^c_(r,K,H)| <= H D^c_(r,K) <= C_r H K^(2-2r),      (3)
```

where `D^c_(r,K)=sum_n mu(n)^2 H^c_(r,K)(n,n)`. Indeed at each time put `a_n(t)=|mu(n)|n^(-r)exp(-2t/n)` and apply `a_m a_n <= (a_m^2+a_n^2)/2`; each index occurs in at most `H` pairs on each side. Integrate and use the diagonal estimate. At order three, shifts `H<= (log(2K))^A` cost at most the proposed polylog budget. Thus the unproved part of the order-three bound concerns long-range signed correlations, not fixed-shift Chowla estimates.

## Finite one-large-prime window at the RH scale

The Gamma transport above works with any fixed `R>r`, so order three is not forced. For each fixed integer `R>=3`, write `T_R=Q_(R,N)+E_(R,N)`, where `Q_(R,N)` sums only `n<=N`. Uniformly in `t>=0`,

```
|E_(R,N)(t)| <= sum_(n>N) n^(-R) <= N^(1-R)/(R-1).       (4)
```

Set `N=ceil(K^(1+1/(2(R-1))))` and `Y=ceil(sqrt N)`. Then `N<=Y^2`, and (4) is `O_R(K^(1/2-R))`, exactly the desired root-mean-square amplitude. Its block energy is `O_R(K^(2-2R))`. Every squarefree `1<=n<=N` has at most one prime factor exceeding `Y`; for a real weight `w(n)`, the exact finite identity is

```
sum_(1<=n<=N) mu(n) w(n)
  = sum_(1<=n<=N, P+(n)<=Y) mu(n) w(n)
    - sum_(Y<p<=N, p prime) sum_(m<=N/p) mu(m) w(p*m).   (5)
```

Indeed `m<=N/p<Y<p`, so `p` is coprime to `m`; each nonfriable squarefree `n` occurs once, indexed by its unique prime factor above `Y`. Taking `w(n)=n^(-R)exp(-2t/n)` gives `Q_(R,N)=F_(R,Y,N)-P_(R,Y,N)` with literal source signs. Therefore an `L²[K,2K]` bound `O_(R,eta)(K^(2-2R+eta))` for this *finite signed difference* is sufficient for the order-`R` source target and hence RH via Gamma transport. The existing Lean coefficient identity `mobiusZero_add_oneLargePrimeCoefficient_eq_mobius_of_le_sq` verifies the finite sector split through `Y²`; reciprocal weighting and sharp tail cutoff are paper-level here.

At `R=3`, this uses `N≈K^(5/4)` and `Y≈K^(5/8)`. Increasing `R` moves the one-prime threshold toward `K^(1/2)`, aligning the finite source with a prime/cofactor bilinear split. The estimate is **not** obtained by bounding `F` and `P` separately: their signed covariance is still the one-power arithmetic obstacle. The short-interval Möbius mean-square theorem in `Sieve.MoebiusMeanSquare` gives vanishing normalized variance, but its available rate does not pay this power.

## Corpus check

`MobiusRenewalPacketCorrelation` supplies the finite geometric pair split. `MobiusLaplaceMellinPlancherelBridge` supplies the closed Lean strict-right energy-to-RH endpoint. The corpus searches for reciprocal-Laplace mean-square saving, higher fixed order, and long shifted correlations returned conditional interfaces or subpower zero-free-region rates, not the order-three source estimate. Deep search reported complete staged execution with incomplete source-index coverage; applicability was checked in source where a plausible candidate appeared. No numerical computation was used.
