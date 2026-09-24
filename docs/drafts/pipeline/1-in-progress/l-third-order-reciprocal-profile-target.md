# Route L: one integer-order source target

- **Status:** finite source isometry, primitive-ratio sign localization, stationary-kernel algebra, exact Gamma-weighted finite Möbius-polynomial identity, source-order comparison, and the direct finite Gamma--Hankel identity are formalized in Lean. Infinite analytic reductions for the fixed cubic target remain paper-level; the signed arithmetic bound is open.
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

## Exact reciprocal/original source isometry and sharpened target

Let `Phi(x)=sum_(n>=1) mu(n) exp(-nx)` be the original Möbius--Laplace source. For every real `R>2`, absolute Fubini on the double series gives the **source-specific exact identity**

```
integral_0^infinity x^(R-1) Phi(x)^2 dx
  = 2^R integral_0^infinity t^(R-1) T_R(t)^2 dt
  = Gamma(R) sum_(m,n>=1) mu(m)mu(n)/(m+n)^R.       (6)
```

The double series converges absolutely because `sum_(m,n) (m+n)^(-R)<infinity` for `R>2`. For the reciprocal integral, the `(m,n)` atom equals

```
(mn)^(-R) * Gamma(R) * [2(1/m+1/n)]^(-R)
  = 2^(-R) Gamma(R)/(m+n)^R.
```

Thus the transform preserves the *signed* additive covariance exactly; it does not lose it to absolute values. At `R=3`, `integral x^2 Phi(x)^2 dx = 8 integral t^2 T_3(t)^2 dt`. Both sides are finite unconditionally. This global energy alone only yields `A_3(K)=O(K^(-2))`; it is not the required one-power arithmetic gain.

The precise strengthening is a near-endpoint positive moment. Dyadic decomposition and positivity show that the order-three target for every `eta>0` is **equivalent** to

```
integral_1^infinity t^(4-delta) T_3(t)^2 dt < infinity
  for every delta>0.                                  (7)
```

Indeed (7) bounds each `A_3(K)` by `K^(-4+delta)`; conversely, on dyadic blocks use the target with `eta<delta` and sum the resulting geometric series. Hence the next source argument may aim at a fractional moment of the exact isometry, but must prove new signed cancellation: (6) itself controls only weight `t^2`.

For a finite cutoff `N`, a direct Gamma calculation rewrites the near-endpoint quadratic form without an integral. For `0<delta<5`,

```
integral_0^infinity t^(4-delta) Q_(3,N)(t)^2 dt
  = Gamma(5-delta)/2^(5-delta)
    * sum_(m,n<=N) mu(m)mu(n)
        (mn)^(2-delta)/(m+n)^(5-delta).               (8)
```

Equation (8) is positive as a whole despite signed entries. For `0<delta<1`, the absolute kernel sum on comparable-index dyadic blocks has size `N^(1-delta)`; controlling its signed total uniformly as `N→infinity` is the genuine new arithmetic estimate behind (7). The finite `N` identity is unconditional; passing to the infinite weighted moment cannot be inferred from the global isometry.

In particular, a finite **signed quadratic criterion** suffices for RH: for every `0<delta<1`, prove a bound independent of `N` for the double sum on the right of (8). The finite energy is nonnegative, and `Q_(3,N)(t)→T_3(t)` pointwise by absolute convergence. Fatou then yields (7), which gives the order-three block bound, fractional transport, packet energy, and RH. This asks for uniform control of one explicit arithmetic matrix along natural integer sections; no limit interchange or unproved regularity premise is hidden in the implication. Necessity of uniform *sharp-cutoff* energy is not asserted.

### Primitive-ratio localization of the signed obstacle

For `0<delta<1`, put `k_delta(m,n)=(mn)^(2-delta)/(m+n)^(5-delta)` and let `B_delta(N)` denote the double sum in (8), without its positive Gamma factor. Group every off-diagonal pair uniquely as `(m,n)=(da,db)` with `d=gcd(m,n)`, `(a,b)=1`, and `a!=b`. Möbius multiplicativity and squarefreeness give the exact identity

```
mu(da)mu(db)
  = 1_((d,ab)=1) mu(d)^2 mu(a)mu(b),
k_delta(da,db) = d^(-1-delta) k_delta(a,b).
```

Consequently the **finite** signed form is

```
B_delta(N)
  = 2^(-(5-delta)) sum_(d<=N) mu(d)^2 d^(-1-delta)
    + sum_(a!=b, (a,b)=1, a,b<=N)
        mu(a)mu(b) k_delta(a,b) W_(delta,N)(a,b),
W_(delta,N)(a,b)
  = sum_(d<=N/max(a,b), (d,ab)=1) mu(d)^2 d^(-1-delta).
                                                               (9)
```

The inner scale weight is nonnegative and at most `zeta(1+delta)`; **all arithmetic sign cancellation has moved to primitive coprime ratios**. `MobiusReciprocalPrimitiveRatio.finiteCubicMomentOffDiagonal_eq_primitiveScaleWeight` proves the finite off-diagonal form in Lean, using the existing generic gcd reindexing in `Sieve.PrimitiveRatioDecomposition` and Möbius coprime factorization in `Sieve.MoebiusScaledReindex`. The displayed diagonal separation and the uniform upper bound on the scale weight are paper-level here.

Two large sectors of (9) are already uniformly controlled without any cancellation. The diagonal is bounded by `2^(-(5-delta)) zeta(1+delta)`. Divisibility pairs have `a=1` or `b=1`; since `k_delta(1,b)<=b^(-3)`, their total absolute contribution is at most `2 zeta(1+delta) sum_(b>=2)b^(-3)`. More generally, fix `q>(3-delta)/2`; for `a<=b` with `b>=a^q`,

```
sum_(a>=1) sum_(b>=a^q) k_delta(a,b)
  <= sum_(a>=1) a^(2-delta) sum_(b>=a^q) b^(-3)
  <<_q sum_(a>=1) a^(2-delta-2q) < infinity.         (10)
```

The symmetric far-separated sector obeys the same bound. In particular the **same cutoff `b>=a^(3/2)` works for every `delta>0`**, because (10) then reduces to `sum_a a^(-1-delta)`. The unresolved band can therefore be fixed once and for all as primitive coprime pairs `2<=a<b<a^(3/2)`, together with its transpose. A uniform signed bound for that band for every `delta>0` would establish the finite criterion and RH. Formula (9) keeps the actual Möbius signs and the positive gcd-scale weights; replacing those signs by absolute values on this band loses a power.

### Stationary ratio and localized frequency form

Put `p=5-delta` and `sigma=(1+delta)/2`. The same finite kernel has the exact factorization

```
k_delta(m,n)
 = m^(-sigma)n^(-sigma) F_p(log(m/n)),
F_p(u)=(2 cosh(u/2))^(-p).
```

In particular `F_p(log(da/db))=F_p(log(a/b))`: the normalized kernel is stationary in logarithmic index and unchanged by common scaling. `MobiusReciprocalPrimitiveRatio.cubicMomentFiniteEnergy_eq_stationary` and `reciprocalMomentStationaryKernel_scale` prove the corresponding finite algebraic identities in Lean. This gives a second exact view of the primitive-band problem, through the literal Dirichlet polynomial `P_N(s)=sum_(n<=N) mu(n)n^(-s)`.

For `p>0`, the substitution `z=exp(u)` in the beta integral gives

```
integral_R F_p(u) exp(-i t u) du
  = Gamma(p/2+it) Gamma(p/2-it) / Gamma(p).
```

Fourier inversion and finite summation yield the exact identity

```
B_delta(N)
 = [1/(2 pi Gamma(5-delta))]
   integral_R |Gamma((5-delta)/2+it)|^2
              |P_N((1+delta)/2+it)|^2 dt.              (11)
```

`MobiusReciprocalGammaFrequency.cubicMomentFiniteEnergy_eq_realGammaIntegral` proves (11) in Lean in the normalized-density form `B_delta(N)=2^(-p) integral gammaHeightDensity(p,t) |P_N(sigma-it)|^2 dt`; the sign of `t` is immaterial because coefficients and density are real and even. The same module proves `B_delta(N)>=0` for every finite cutoff. Its exact coefficient exponent shows why a generic Dirichlet-polynomial mean square is insufficient: this is a **localized multiplicative-frequency** estimate at `sigma` just to the right of `1/2`. By Stirling's bound and the trivial `|P_N(sigma+it)|<<_delta N^((1-delta)/2)`, the part of (11) with `|t|>log(2N)/pi` is `O_delta(N^(-delta) (log(2N))^(4-delta))`. Thus a uniform bound for the remaining Gamma-weighted interval `|t|<=log(2N)/pi` would suffice for RH. This cuts the frequency search to logarithmic height without replacing the required signed cancellation. The corpus's additive-phase orthogonality in `HeatEnergyBridge` is in `n theta`, not `t log n`, and does not supply this bound; the Ramaré local-moment interface gives an explicit cost budget, not the required uniform estimate.

**Order-independent arithmetic exponent.** The same derivation works for every fixed real source order `R>2`. Weight the finite `T_R` square by `t^(2R-2-delta)`; its Gamma integral has `p_R=2R-1-delta` and pair kernel

```
k_(R,delta)(m,n)
 = (mn)^(R-1-delta)/(m+n)^(2R-1-delta)
 = m^(-sigma)n^(-sigma) F_(p_R)(log(m/n)),
sigma=(1+delta)/2.
```

Moreover `k_(R,delta)(da,db)=d^(-1-delta)k_(R,delta)(a,b)` for every positive `d,a,b`. Both algebraic laws are now proved in Lean as `generalReciprocalMomentKernel_eq_stationary` and `generalReciprocalMomentKernel_scale`. The Lean theorem `finiteGeneralMomentOffDiagonal_eq_primitiveScaleWeight` also proves that the full finite off-diagonal for every `R` has the **same** nonnegative scale weight `W_(delta,N)(a,b)` in (9) and the **same** primitive Möbius signs; only `k_(R,delta)(a,b)` changes. Higher order changes the positive ratio profile and the Gamma-frequency weight, but **neither the Möbius coefficient abscissa nor the gcd scale exponent**. The corresponding Fourier identity has `|Gamma(p_R/2+it)|²` in (11). This identifies one order-independent arithmetic cancellation target across the entire fixed-order reciprocal family; no bound for that target follows from the identities.

**Order-transfer law.** The normalized Gamma density obeys the exact shape recurrence

```
rho_(p+2)(t) = (p^2+4t^2)/(p(p+1)) rho_p(t),
rho_p(t) <= (p+1)/p rho_(p+2)(t)       (p>0).       (12)
```

`MobiusReciprocalGammaFrequency.gammaHeightDensity_add_two` and `gammaHeightDensity_le_succ_two` prove (12) in Lean. Since the Möbius polynomial has the same coefficient abscissa at every reciprocal order, `MobiusReciprocalOrderTransfer.finiteGeneralReciprocalEnergy_eq_realGammaIntegral` and `finiteGeneralReciprocalEnergy_le_succ` prove the finite comparison

```
B_(R,delta)(N) <= 4 (p_R+1)/p_R * B_(R+1,delta)(N),
p_R=2R-1-delta>0.                              (13)
```

Here `B_(R,delta)(N)` is the finite signed quadratic form with kernel `k_(R,delta)`. The factor `4` comes from the `2^(-p_R)` Fourier normalization. Thus a uniform bound at **any one fixed higher integer order** transfers to order three by finitely many positive comparisons, without assuming cancellation during transport. This makes source order an arithmetic design choice: a higher-order ratio profile may be attacked if it exposes a useful correlation law. No fixed order is bounded by (12) alone; the uniform Möbius-polynomial estimate remains the hard step.

**Direct integer-numerator source to the closed Laplace endpoint.** Set `R_0=1+delta` and `R_2=3+delta`, with `0<delta<1`. At the lower order, the numerator exponent `R_0-1-delta` vanishes, so the original finite Möbius Gamma--Hankel energy is exactly

```
H_N(1+delta) = Gamma(1+delta) B_(1+delta,delta)(N).
```

Two applications of (13) give the unconditional finite inequality

```
H_N(1+delta)
 <= Gamma(1+delta) * 16 (2+delta)(4+delta)/((1+delta)(3+delta))
      * B_(3+delta,delta)(N).                         (14)
```

At the upper order, `k_(3+delta,delta)(m,n)=(mn)^2/(m+n)^(5+delta)`: its numerator is an integer polynomial. Thus one may target the literal finite signed additive form

```
B_(3+delta,delta)(N)
 = sum_(m,n<=N) mu(m)mu(n) m^2 n^2/(m+n)^(5+delta).   (15)
```

If, for `delta` arbitrarily close to zero from above, (15) has one finite upper ceiling on an unbounded subsequence of `N`, then (14), the nonnegative Gamma--Hankel diagonal, and the already formalized bounded-return Fatou criterion imply RH. This avoids the paper-level fractional-source and geometric-packet transport for this parameter-coupled target. `MobiusReciprocalGammaHankelBridge` formalizes the exact finite identity, the two-step comparison, and the integer-numerator kernel. The substantive open estimate remains a one-power cancellation of the comparable-index Möbius pairs; the unconditional absolute pair sum grows at scale `N^(1-delta)`. Existing additive-triangle criteria in the corpus retain different coefficients and do not prove (15).

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
