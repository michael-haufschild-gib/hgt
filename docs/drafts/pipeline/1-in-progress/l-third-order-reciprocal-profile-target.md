# Route L: one integer-order source target

- **Status:** finite source isometry, primitive-ratio sign localization, stationary-kernel algebra, exact Gamma-weighted finite Möbius-polynomial identity, source-order comparison, the direct finite Gamma--Hankel identity, the power-balanced source reduction, and the cubic discrete packet second-difference identity are formalized in Lean. Paper proofs now give an unconditional `E(N)^2` stretched-exponential *relative* saving for the full signed reciprocal energy, near-complete prime/composite compensation inside a shrinking interval, an exact short-interval rank-one/covariance approximation, quadratic-Mertens and opposite-sign-transport sufficient criteria, an exact prefix-current transport construction and Gamma cost, two-adic localization of a weaker one-sided RH receiver, the signed unbalanced endpoint, fixed-factor prime-insertion laws, a macroscopic source-compatible dyadic signed-dipole contraction followed by a literal prime-band compensator, and an all-order discrete packet identity for the full signed source. The cutoff-independent signed power-balanced bound needed for RH is open.
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

The [all-order discrete Möbius packet identity](../2-fully-proven/l-discrete-mobius-packet-sobolev.md) gives a second exact form of (15). If `b_k=sum_(n≤N) mu(n)(n+1)^(-1-delta)((n-1)/(n+1))^k`, then

```text
B_(3+delta,delta)(N) = 2^(delta-3) * sum_(k≥0)
  binom(4+delta+k,k) * (b_k-2b_(k+2)+b_(k+4))^2.       (15a)
```

The generic positive packet expansion and the source-specific step-two second-difference bridge are proved in [Lean](../../../../formal/GaloisForLFunctions/RHTower/MobiusReciprocalDiscretePacketBridge.lean). Formula (15a) locates the hard arithmetic estimate in one weighted sequence norm. The paper-level [finite packet horizon theorem](../2-fully-proven/l-discrete-mobius-packet-sobolev.md#unconditional-finite-packet-horizon-paper-proof) bounds the omitted range `k≥C_P N log N` by `O_P(N^(-P))` for any fixed `P>0`, uniformly in `0≤delta≤1`; hence the global arithmetic problem is entirely inside a finite `O(N log N)` packet range. Neither identity nor horizon bounds that range.

The paper-level [source-index aperture theorem](../2-fully-proven/l-discrete-mobius-packet-sobolev.md#source-index-aperture-at-the-cubic-threshold-paper-proof) narrows this finite range further. For `0≤delta≤1` and all sufficiently large packet indices `k`, the source indices below `floor(4k/log k)` and above `ceil(k^((5+delta)/(4+2delta)))` have a weighted `ℓ²` contribution bounded independently of `N` and `delta`. Integrating the exact exponential kernel controls every lower cutoff `A*k/log k` with `A<4`; at `A=4`, finite Abel summation and the corpus's stretched-exponential Mertens saving make the endpoint summable. The same saving controls the upper endpoint, where absolute values would give harmonic packet energy. Thus bounded returns of (15) are equivalent to bounded returns of the literal Möbius packet norm on the finite wedge `k<O(N log N)` and `4k/log k<n≤k^((5+delta)/(4+2delta))`. Only signed cancellation in this two-sided critical wedge remains; its bound is open.

**Unconditional global signed saving (paper proof; Lean theorem open).** Write `E(x)=deningerMertensSaving x=exp(-((log x)^(1/3))/108)` and `F_N(t)=sum_(n<=N) mu(n)*n^2*exp(-n*t)`. The corpus's `deningerMertensM_rate`, with its finite initial exceptions absorbed into one constant, gives `|M(x)| << x*E(x)` for real `x>=1`. Ordinary finite Abel summation gives the exact formula

```
F_N(t) = M(N)*N^2*exp(-N*t)
       - integral_1^N M(x)*(2*x-t*x^2)*exp(-x*t) dx.       (16a)
```

Split the integral at `sqrt N` when `t<=1/N`, and at `1/sqrt t` when `1/N<=t<=1/2`. Since `E` decreases and decays more slowly than every negative power, these two splits give, with one constant independent of `N,t`,

```
|F_N(t)| << N^3*E(sqrt N)               (0<t<=1/N),
|F_N(t)| << t^(-3)*E(1/sqrt t)          (1/N<=t<=1/2).   (16b)
```

For `t>=1/2`, the absolute sum is `O(exp(-t))`, uniformly in `N`. The exact Gamma--Laplace square behind (15) is

```
B_(3+delta,delta)(N) = Gamma(5+delta)^(-1)
   * integral_0^infinity t^(4+delta)*F_N(t)^2 dt >= 0.
```

For every fixed `0<=delta<1`, the first range in (16b) contributes `O_delta(N^(1-delta)*E(sqrt N)^2)`. In the second range, `u=1/t` reduces the bound to `integral_2^N u^(-delta)*E(sqrt u)^2 du`; splitting at `sqrt N` gives the preliminary bound `O_delta(1+N^(1-delta)*E(N))`. A dyadic source decomposition retains both Mertens savings and sharpens this. Partition `1<n<=N` into intervals `I_j=(2^j,min(2^(j+1),N)]` and keep `n=1` separate. The interval estimate (17b) below, which applies also to a truncated final interval, gives `||F_(I_j)||_delta <<_delta 2^(j*(1-delta)/2)*E(2^j)` in the Gamma-weighted Hilbert norm whose square is (15). Minkowski's inequality and the subadditivity of the cube root give

```
sum_(j<=log_2 N) 2^(j*(1-delta)/2)*E(2^j)
  <<_delta N^((1-delta)/2)*E(N),
```

because after indexing blocks downward from the largest, the summands are bounded by a constant times `2^(-k*(1-delta)/2)*exp(((k+1)*log 2)^(1/3)/108)`, a summable sequence. The `n=1` atom is absorbed since `N^((1-delta)/2)*E(N)` tends to infinity. Thus the stronger unconditional estimate is

```
0 <= B_(3+delta,delta)(N) <<_delta 1+N^(1-delta)*E(N)^2
       (fixed 0<=delta<1),                              (16c)
sup_N B_(4,1)(N) < infinity.                            (16d)
```

For (16d), the middle integral is `integral_2^infinity E(sqrt u)^2 du/u < infinity` after the substitution `v=(log u)^(1/3)`. The already bounded signed unbalanced correction in (17) transfers the subpower saving (16c) to the signed power-balanced sector. This is a bound on the **entire literal signed quadratic**, not an absolute or packetwise estimate. It still grows as a positive power of `N` for every fixed `delta<1`, so it does not imply the bounded-return criterion for RH.

**Quadratic Mertens source criterion (paper proof; Lean theorem open).** The same Abel identity (16a) gives a route from a *mean-square* source estimate, without assuming a pointwise square-root bound. Let `M(x)=sum_(n<=x) mu(n)` and `Q(X)=sum_(n<=X) M(n)^2`. Scaling the Gamma norm of `N^2*exp(-N*t)` and of `(2*x-t*x^2)*exp(-x*t)` in (16a), then applying Minkowski, gives the exact-type bound

```
sqrt(B_(3+delta,delta)(N)) <<_delta
  |M(N)|/N^((1+delta)/2)
  + integral_1^N |M(x)|/x^((3+delta)/2) dx.             (16e)
```

Conjecture `Q(X) <<_epsilon X^(2+epsilon)` for every `epsilon>0`. If it holds for one `epsilon<delta`, Cauchy--Schwarz on each dyadic interval makes the integral in (16e) uniformly bounded: its `2^j<=x<=2^(j+1)` contribution is `O_(delta,epsilon)(2^(-j*(delta-epsilon)/2))`. The same mean-square bound selects an integer `N_X in [X,2X]` with `|M(N_X)| <<_epsilon X^((1+epsilon)/2)`, so the endpoint term in (16e) is `O(X^(-(delta-epsilon)/2))`. Consequently `B_(3+delta,delta)(N_X)` has one cutoff-independent upper ceiling on a cofinal sequence. If the conjecture holds for every positive `epsilon`, this works for every `0<delta<1`; the already formalized bounded-return Gamma--Hankel criterion then proves RH.

The corpus's `MobiusBlockDefectEnergy` gives the finite prefix-energy/gradient Cauchy interface, and `MobiusBlockDefectEnergyInterpolation` explains how critical mesh energy reaches the full Mertens mean-square scale. Neither supplies this arithmetic `Q` estimate. This criterion changes the target from pointwise Mertens control to a quadratic cumulative-defect law that can be attacked by the corpus's block-energy and opposite-sign transport tools; its proof remains the arithmetic obstacle, not an added Lean premise for a claimed RH theorem.

**Dyadic opposite-sign transport criterion (paper proof; Lean theorem open).** The corpus's `MobiusBoundaryOppositeSignTransport` already formalizes parity-flipping prime-factor replacement edges, Hall and fractional-flow consumers for the unweighted Laplace source. The exact cost for the order-three Gamma source can be stated separately. In a dyadic interval `I subset (X,2X]`, pair some `mu=+1` indices with distinct `mu=-1` indices, leave `U_I` nonzero indices unpaired, and let `D_I=sum_(m,n paired)|m-n|`. The mean-value formula for `g_t(u)=u^2*exp(-u*t)` and the Gamma norm calculation behind (16e) give

```
sqrt(B_delta(I)) <<_delta
  D_I/X^((3+delta)/2) + U_I/X^((1+delta)/2).          (16f)
```

Thus a source-faithful pairing on every dyadic block with `D_I <<_epsilon X^(3/2+epsilon)` and `U_I <<_epsilon X^(1/2+epsilon)` for every `epsilon>0` would make the block Gamma norms `O_(delta,epsilon)(X^(-delta/2+epsilon))`. Their dyadic sum converges whenever `epsilon<delta/2`, so the finite energies are uniformly bounded and the formal Gamma--Hankel criterion yields RH. This is an actionable matching/flow target: prove both the near-square-root total displacement and the near-square-root unmatched mass from the actual Möbius source. The existing factor-replacement consumer supplies the sign and cost algebra but does not prove such a matching or its Hall inequalities.

The critical edge scale forces a concrete graph design. If `m=a*u` and `n=a*v` are distinct integer atoms with `X<m<=2X`, then `|m-n|=a*|u-v|>=a>X/u`. Hence every same-cofactor replacement edge of displacement at most `H` must remove a token `u>X/H`; at the desired `H=O(sqrt X)`, its token must have size `Omega(sqrt X)`. The corpus's `MobiusBoundaryOppositeSignTransport.le_pow_four_mul_dist_of_boundaryFactorReplacementAdjacent_of_primeFactors_le` makes this obstruction exact for the fixed `one prime ↔ two/four primes` graph: a sufficiently friable endpoint can only replace tokens below `y^4`, so it has no critical-width edge when `y^4*H<X`.

There is a positive factorization repair for the token *size*. Every squarefree `y`-friable `m in (X,2X]` has a divisor `u` formed by a greedily chosen prefix of its distinct prime factors with `sqrt X <= u < y*sqrt X`: multiply factors until the product first crosses `sqrt X`, possible because their full product is `m>X`; the previous product is below `sqrt X` and the last factor is at most `y`. The complementary coprime cofactor `a=m/u` is at most `2*sqrt X`, so replacing `u` by an integer `v` with `|u-v|=1` would stay within displacement `2*sqrt X`. A viable transport producer must now find enough such near-token replacements with `mu(v)=-mu(u)` and `gcd(v,a)=1`, and control their Hall capacity. This variable-arity square-root token construction repairs the fixed graph's size failure but does not supply the missing parity and matching theorem; cross-interval covariance remains the alternate mechanism.

**Canonical one-dimensional transport and exact prefix-current cost (paper proof; Lean theorem open).** The unrestricted matching problem has a direct construction, so its Hall inequalities need not be proved separately. Let `I=(L,R]` be an integer interval, `a_j=mu(j)`, `C_k=sum_(L<j<=k) a_j`, and `S=C_R`. Add `|S|` fictitious atoms of sign opposite to `S` at `R`. The resulting signed configuration is balanced. Any matching must transport net charge `C_k` across the unit edge `(k,k+1)`, so its total distance is at least `sum_(k=L+1)^(R-1)|C_k|`. Routing exactly `C_k` signed units across each edge conserves charge at every vertex; decomposing this acyclic integer flow into source-to-sink paths attains the bound. The paths ending at the fictitious atoms leave exactly `|S|` original atoms unmatched. Hence one can choose an opposite-sign pairing with

```
U_I=|S|,
D_I + sum_(j unmatched)(R-j) = sum_(k=L+1)^(R-1)|C_k|.    (16g)
```

The same prefix current gives the exact source decomposition, without constructing a pairing:

```
F_I(t) = S*g_t(R)
       + sum_(k=L+1)^(R-1) C_k*(g_t(k)-g_t(k+1)),
g_t(u)=u^2*exp(-u*t).                                     (16h)
```

For the normalized Gamma norm whose square is `B_delta`, direct integration gives

```
||g_.(u)||_delta = 2^(-(5+delta)/2)*u^(-(1+delta)/2),
||d/du g_.(u)||_delta
  = 2^(-(7+delta)/2)*sqrt(delta^2+3*delta+6)
      *u^(-(3+delta)/2).
```

Thus, whenever `X<L<R<=2X`, Minkowski and the fundamental theorem of calculus yield the explicit source-specific estimate

```
sqrt(B_delta(I)) <= 2^(-(5+delta)/2)*|S|/R^((1+delta)/2)
  + 2^(-(7+delta)/2)*sqrt(delta^2+3*delta+6)
      *sum_(k=L+1)^(R-1)|C_k|/X^((3+delta)/2).          (16i)
```

Consequently the transport criterion (16f) can be produced from a bound on the literal prefix-current `L^1` mass, with no prime-factor graph or Hall theorem. The outstanding producer is the RH-scale arithmetic estimate `sum_k|C_k| <<_epsilon X^(3/2+epsilon)` together with `|S| <<_epsilon X^(1/2+epsilon)` on the relevant blocks. This identity also shows exactly which quantity any restricted factor-replacement graph must control; its graph-specific role is to establish the arithmetic current estimate, not to make the matching exist.

**Two-adic localization of a weaker one-sided RH receiver (prime-window and tent identities already formal; expanded band estimate open).** The corpus's `RHTower.mobiusAdditiveTriangleSecondCesaroSubpowerUpperBound_implies_riemannHypothesis` already closes RH from the one-sided estimate `Re C_N <<_epsilon N^(2+epsilon)` for every positive `epsilon`, where `C_N` is its second-Cesàro additive Möbius triangle. Crucially, `MobiusMertensPrimeRemovalTentLaw` already proves the exact one-prime window identity, the flattened signed prime-free kernel double sum, the nonnegative four-hinge tent kernel, its support and bounds, and the prime-2 minimality law. Formula (16j) below is that formal double-sum law at `p=2` written with odd indices and real signs; only the subsequent sector budget is paper-level. In real arithmetic, writing `W_N(s)=max(N-s+1,0)` for nonnegative integer `s`, its exact finite kernel form is `C_N=sum_(m,n>=1) mu(m)*mu(n)*W_N(m+n)`. Every positive integer with nonzero Möbius value is uniquely an odd `u` or twice an odd `u`, and `mu(2*u)=-mu(u)` for odd `u`. Therefore, with `u,v` ranging over positive odd integers,

```
C_N = sum_(u,v odd >=1) mu(u)*mu(v)*D_N(u,v),
D_N(u,v) = W_N(u+v)-W_N(2*u+v)
             -W_N(u+2*v)+W_N(2*u+2*v).                (16j)
```

These sums are finite because every displayed `W_N` vanishes when its argument exceeds `N`. The mixed finite difference has an exact counting form:

```
D_N(u,v) = #{i in {0,...,u-1} : u+v+i <= N < u+2*v+i}.
```

Hence `0<=D_N(u,v)<=min(u,v)`, and it vanishes unless `u+v<=N<=2*(u+v)-2`. In particular all deep-interior contributions `u+v<=(N+1)/2` cancel **exactly**, rather than merely being small. If `K=floor(sqrt N)`, the part with `min(u,v)<=K` is absolutely bounded, even after removing the odd restriction, by

```
2 * sum_(u=1)^K sum_(v=1)^N u
  = N*K*(K+1) <= 2*N^2                    (N>=1).     (16k)
```

Thus the only unsigned-cost-unresolved source for this already formal RH receiver is the signed odd-Möbius band `u,v>sqrt N` and `(N+2)/2<=u+v<=N`. Its required bound is one-sided `O_epsilon(N^(2+epsilon))`; at each cutoff it permits cancellation between the two reversal eigenspaces that the nonnegative quadratic-Mertens bound `Q(N)<<N^(2+epsilon)` would discard. At the all-`epsilon` level both estimates are RH-equivalent through the existing corpus receivers and Littlewood's Mertens criterion. The doubling identity supplies an exact boundary-layer producer and pays the small-index sector without a new hypothesis. The balanced signed band remains open.

The same two-adic identity gives a more direct producer for the original `Q` target. Splitting `sum_(m<=n)mu(m)` into odd `m=u` and even squarefree `m=2*u` cancels every odd `u<=n/2`, leaving the exact half-window law, already formal as `RHTower.mobiusMertensPartialSum_eq_primeWindow` specialized to `p=2`,

```
M(n) = sum_(n/2<u<=n, u odd) mu(u).                       (16l)
```

For odd `u>1`, let `omega(u)` be its number of distinct prime factors. If `mu(u) != 0`, each odd prime divisor `p` contributes `-mu(u/p)/omega(u)=mu(u)/omega(u)`; if `mu(u)=0`, the terms with `p` dividing `u` only once also vanish because the cofactor remains squareful. Consequently, for every `n>=2`, (16l) becomes the exact prime--cofactor identity

```
M(n) = -sum_(p odd prime, a odd, p does not divide a,
             n/2 < p*a <= n) mu(a)/omega(p*a).          (16m)
```

No rough or square-multiple remainder survives: `u=1` lies outside the half-window when `n>=2`, and `p` dividing `a` is excluded. This is the additive half-window counterpart of the corpus's `Sieve.NonRoughBilinearExact` Ramaré factorization. Squaring (16m) and summing `n<=X` produces a literal prime--cofactor covariance whose `O_epsilon(X^(2+epsilon))` bound would close RH by (16e); the existing Ramaré and Type II source files provide factorization and frequency budgets, but no such bound for this additive half-window covariance. The next mathematical attack is on this specific signed covariance, retaining both cofactor Möbius signs and the shared moving window.

More precisely, expanding (16l) before any prime factorization gives the exact positive-overlap kernel

```
Q(X) = sum_(u,v odd >=1) mu(u)*mu(v)*H_X(u,v),
H_X(u,v) = #{n<=X : u<=n<2*u and v<=n<2*v}
         = max(0, min(X+1,2*min(u,v))-max(u,v)).       (16n)
```

The kernel vanishes unless `max(u,v)<2*min(u,v)` and obeys `H_X(u,v)<=min(u,v)`. Thus the entire sector `min(u,v)<=floor(sqrt X)` is absolutely at most `2*sum_(u<=floor(sqrt X))u^2<=2*X^(3/2)`: for a fixed smaller index `u`, at most `u` larger integer indices `v` have nonzero overlap, each at cost at most `u`. The same bound survives exact prime--cofactor expansion (16m), since for each squarefree `u>1` the absolute Ramaré weights over its prime divisors sum to one, and for squareful `u` they all vanish. The unresolved covariance is therefore confined to comparable odd products `u,v>sqrt X`, with literal cofactor signs retained.

The off-diagonal can also be written exactly as a **single signed sum over even shifts**, without a fixed-window boundary error. This shift expansion is paper-proved here and has not been formalized. For positive even `h` and odd `u`, put

```
w_(X,h)(u) = max(0, min(u-h, X+1-u-h)).
```

Then `(16n)` gives

```
Q(X) = sum_(u odd<=X) mu(u)^2*min(u,X+1-u)
     + 2*sum_(0<h<X/2, h even) sum_(u odd) mu(u)*mu(u+h)*w_(X,h)(u).
                                                               (16o)
```

The first term is at most `X^2`; for `h<=H`, the entire second term is absolutely `O(H*X^2)`, so every fixed or subpower-width shift sector already fits an `X^(2+epsilon)` budget. There is also a power-width paid sector at the other end. Ignoring odd parity, when `m=X-2*h>=1` the tent weights sum exactly to `floor((m+1)^2/4)`; therefore all shifts `X/2-R<h<X/2` contribute at most `O(R^3)` absolutely. Taking `R=X^(2/3)` costs only `O(X^2)`. The remaining target is the **combined signed long-shift tent correlation** with `X^eta<h<X/2-X^(2/3)`, keeping cancellation across shifts. The corpus's `Sieve.MoebiusUnweighted.sum_normSq_window_moebius_le_of_correlation` bounds fixed-length window squares from per-shift correlations, but at half-length `L~X` its explicit `O(L^3)` boundary term is too large even if its correlation premise were zero. The exact overlap identity (16o) avoids that artificial boundary cost. Corpus search returned this declaration as source-only with applicability unverified; no Lean compilation of the new expanded formulas (16m), (16n), or (16o) was attempted under shared-memory pressure.

**Exact box factorization of the unresolved tent (paper proof; Lean theorem open).** For an even shift `h` in (16o), put `m=X-2*h>=1`, `a=floor((m+1)/2)`, `b=ceil((m+1)/2)`, so `a+b=m+1`. On writing `v=u-h`, the tent is `w_(X,h)(u)=min(v,m+1-v)` for `1<=v<=m` and zero otherwise. Its coefficient polynomial factors exactly:

```
sum_(v=1)^m min(v,m+1-v)*z^(v-1)
  = (sum_(i=0)^(a-1) z^i)*(sum_(j=0)^(b-1) z^j).       (16p)
```

Indeed the coefficient of `z^(v-1)` counts pairs `i+j=v-1` in the `a`-by-`b` rectangle and equals `min(v,m+1-v)`. Thus the **entire signed correlation at shift `h`** is the literal two-variable average

```
sum_(u odd) mu(u)*mu(u+h)*w_(X,h)(u)
  = sum_(0<=i<a, 0<=j<b, h+1+i+j odd)
      mu(h+1+i+j)*mu(2*h+1+i+j).                       (16q)
```

The parity restriction is essential: `u=h+1+i+j` must remain odd. The box factorization identifies a concrete arithmetic producer for the remaining bound: a **combined signed two-linear-form estimate** over the moving rectangles indexed by even `h`, with forms `h+1+i+j` and `2*h+1+i+j`. At `z=1`, the polynomial has mass `a*b=floor((m+1)^2/4)`; its constant/low-frequency mode is large, so the already formal high-ordinate Route-T estimates cannot alone pay this source. Any use of the corpus's prime--cofactor phase or bilinear machinery must retain the cancellation across `h`, `i`, and `j` at this low-frequency scale. The exact statement (16q) is a proof-level target, not an established estimate, and the RH-scale `O_epsilon(X^(2+epsilon))` bound for its aggregate remains open.

**Unconditional prime/composite cancellation at its first scale (paper proof; Lean theorem open).** Let `P(n)` count odd primes in `(n/2,n]`, and let `C(n)` be the sum of `mu(u)` over odd nonprimes (including `u=1` when it lies in the window). Equation (16l) gives the exact source decomposition `M(n)=C(n)-P(n)`. The prime-counting asymptotic already present as `RHTower.tendsto_primeCounting_nat_ratio` gives `P(n)~n/(2*log n)`, hence, by summation,

```
sum_(n<=X) P(n)^2 ~ X^3/(12*log(X)^2).                 (16r)
```

Equivalently, the full odd-prime/odd-prime sector of (16n) has this asymptotic. The constant `1/12` is the exact overlap integral `integral_(0)^1 (t/2)^2 dt`: at scale `t`, the half-window `(t/2,t]` has length `t/2`. The corpus's unconditional sharp Möbius saving `RHTower.Sieve.exists_norm_sum_moebius_kappa_two_rate` gives `|M(n)| <= B*n*exp(-(log n)^(1/3)/108)` for all large `n`; splitting the sum at `sqrt X` proves, for every fixed `A>0`,

```
sum_(n<=X) (C(n)-P(n))^2 = Q(X) = o(X^3/log(X)^A).     (16s)
```

Therefore the signed pairs in (16n) with **at least one nonprime index** already have the unconditional asymptotic `-X^3/(12*log(X)^2)`: their contribution is `Q(X)-sum P(n)^2`. More positively, the complete odd-composite source `C` shadows the odd-prime count `P` in mean square with relative error smaller than every fixed reciprocal log power, `||C-P||_(2,[1,X])=o(X^(3/2)/log(X)^A)` for each fixed `A`. Cauchy--Schwarz then gives both `sum_(n<=X) C(n)*P(n) ~ X^3/(12*log(X)^2)` and `sum_(n<=X) C(n)^2 ~ X^3/(12*log(X)^2)`. The RH-scale target asks for the new, genuinely stronger relative error `O_epsilon(X^(-1/2+epsilon)*log X)` against `||P||_2~X^(3/2)/(sqrt(12)*log X)`. This precisely locates the missing power saving **inside the already-existing prime/composite cancellation**, rather than in either sector alone. The derivation is analytical, uses the literal source and existing corpus estimates, and has not yet been formalized as this combined theorem.

**Exact prime-scale split of the source Ramaré loads (paper proof; Lean theorem open).** For `n>=2` and every odd prime `p`, define the literal normalized load

```
L_p(n) = sum_(n/2<u<=n, u odd, p|u) mu(u)/omega(u),       (16t)
```

with a zero contribution when `mu(u)=0`. The corpus's `RHTower.Sieve.routeE_sum_normalizedIncidenceBlock` supplies the finite load-sum identity after choosing all odd primes through `n`. On the actual half-window the loads split **exactly at one third of the cutoff**:

```
sum_(p>n/3) L_p(n) = -P(n),
sum_(p<=n/3) L_p(n) =  C(n),
sum_p L_p(n) = M(n).                                      (16u)
```

For `p>n/3`, an odd multiple `p*a<=n` with `a>1` would require `a>=3`, a contradiction; the sole possible nonzero term is `u=p` and has weight `mu(p)/omega(p)=-1`. For `p<=n/3`, no prime `u=p` is in `(n/2,n]`; every nonzero odd composite `u` in that window has all prime factors at most `u/3<=n/3`, and their normalized weights sum to `mu(u)`. Thus (16u) is literal arithmetic, with no asymptotic or centering premise.

In the squared load energy, the high--high, low--low and twice high--low blocks are respectively `sum P(n)^2`, `sum C(n)^2`, and `-2*sum C(n)*P(n)`. Equations (16r)--(16s) prove their unconditional leading asymptotic ratio `1 : 1 : -2`, each unit being `X^3/(12*log(X)^2)`. This localizes the remaining half-power saving to a **cross-scale prime/cofactor interference law** between loads above and below `n/3`; the high and low blocks are separately supercritical. The generic centered-cofactor contraction and conditional-negative incidence-complement theorems found by deep corpus search do not by themselves control this literal scalar mode, which is `M(n)`. A viable producer must preserve the negative high--low cross term while upgrading the residual `||C-P||_2` to `O_epsilon(X^(1+epsilon))`.

**Least-factor Volterra identity and its semiprime scale (paper proof; Lean theorem open).** The normalized loads in (16t) overcount each composite by `omega(u)` and then divide it back out. Peeling instead by its *unique least prime factor* removes that denominator. For an odd integer `a>1`, put

```
K_n(a) = #{p odd prime : p < minFac(a), n/2 < p*a <= n}.
```

Terms with `mu(a)=0` vanish. For every `n>=2`, squarefree odd composites `u` in the half-window correspond bijectively to pairs `u=p*a` counted by `K_n(a)`: `p=minFac(u)`, every prime factor of `a` exceeds `p`, and `mu(u)=-mu(a)`. Since `p>=3`, necessarily `a<=n/3`; also `p<=sqrt n` for every such composite. Hence the exact disjoint scale recursion is

```
M(n) = -P(n) - sum_(2<=a<=n/3, a odd) mu(a)*K_n(a).       (16v)
```

This is a literal finite Volterra/Buchstab decomposition of the same half-window source, with cofactors at most one third of `n`. The corpus has the least-factor squarefree peeling lemmas `RHTower.Sieve.primeFactors_card_div_minFac` and `RHTower.Sieve.minFac_pow_le_of_squarefree`; neither supplies a signed bound for the displayed cofactor sum.

The part with `p>n^(1/3)` is particularly rigid. For fixed `1/3<=alpha<1/2`, define

```
B_alpha(n) = #{p<q odd primes : p>n^alpha, n/2<p*q<=n},
R_alpha(n) = sum_(n/2<u<=n, u odd composite squarefree,
                   minFac(u)<=n^alpha) mu(u).
```

Three distinct prime factors all exceeding `n^alpha` would have product greater than `n`, so this upper least-factor sector consists **exactly** of positive semiprimes. Thus `M(n)=R_alpha(n)+B_alpha(n)-P(n)` with no remainder. The existing prime-number theorem `RHTower.tendsto_primeCounting_nat_ratio`, applied uniformly for `p` between `n^alpha` and `sqrt(n/2)`, gives

```
B_alpha(n) ~ c_alpha*n/(2*log n),
c_alpha = integral_[alpha,1/2] dt/(t*(1-t))
        = log((1-alpha)/alpha).                             (16w)
```

Indeed for `p<=sqrt(n/2)` the larger prime `q` is counted by `pi(n/p)-pi(n/(2*p)) ~ n/(2*p*log(n/p))`; prime partial summation turns its sum into the displayed integral. The short edge `sqrt(n/2)<p<=sqrt n` contains `O(n/log^2 n)` pairs by the prime-count upper bound. The sharp unconditional Möbius saving in (16s) and `P(n)~n/(2*log n)` therefore imply

```
R_alpha(n) ~ (1-c_alpha)*n/(2*log n).
```

At the sharp semiprime onset `alpha=1/3`, the semiprimes above the cutoff contribute `log 2` times the prime-window main term; the signed composites with least factor at most `n^(1/3)` contribute the remaining positive fraction `1-log 2`. In particular that latter signed sum is eventually positive. The three-channel Gram matrix of `(P,B_alpha,R_alpha)` over `n<=X`, divided by `X^3/(12*log^2 X)`, tends to the rank-one matrix generated by `(1,c_alpha,1-c_alpha)`. Its signed vector `(-1,1,1)` annihilates the leading mode. This gives a quantitative **scale profile of the actual prime/composite interference** and confines the unresolved signed arithmetic to least primes at most `n^(1/3)` coupled to an explicit semiprime sector. The rank-one limit and all existing superlogarithmic Mertens estimates still leave the required `O_epsilon(X^(2+epsilon))` residual energy open; a separate power-saving estimate on the coupled source is necessary.

**Fixed-aperture dyadic version (paper proof; Lean theorem open).** For an integer `X>=2`, freeze `Y=floor((2X)^(1/3))` throughout `X<=n<=2X`. Define `B_Y(n)` and `R_Y(n)` by the preceding semiprime and low least-factor conditions with `p>Y` and `minFac(u)<=Y`, respectively. Since every prime `p>Y` has `p^3>2X`, every squarefree composite `u<=2X` with least prime above `Y` has exactly two prime factors. Therefore, simultaneously at every cutoff in the dyadic block,

```
M(n)=R_Y(n)+B_Y(n)-P(n),
R_Y(n)=-sum_(p<=Y, p odd prime)
           sum_(a>1, p<minFac(a), n/2<p*a<=n) mu(a).       (16x)
```

This is a fixed-prime-set identity, so the same aperture can be used in every bilinear covariance term across the entire block. Uniform prime-number-theorem estimates in the region `n in [X,2X]`, `p in (Y,sqrt n]` strengthen (16w) to

```
sup_(X<=n<=2X) | B_Y(n)/(n/(2*log n)) - log 2 | -> 0,
sup_(X<=n<=2X) | R_Y(n)/(n/(2*log n)) - (1-log 2) | -> 0.
```

The proof uses `log Y/log n -> 1/3` uniformly, the same prime partial-summation integral, and the uniform form of the corpus's Mertens saving. This fixed aperture matches the corpus's `routeELowPrimeFactors` / `routeERoughPrimeFactors` split and its exact Ramaré bilinear interfaces. It removes a varying-cutoff mismatch when searching for a coupled estimate, but supplies no power gain by itself: the required block estimate remains the square norm of the *combined* right side of (16x), of order `O_epsilon(X^(2+epsilon))`, while each component alone has order `X^3/log^2 X` in squared norm.

**Prime-3 single-channel reconstruction (paper proof; Lean theorem open).** The smallest least-prime channel in (16x) is itself an exact complete-source coordinate across two dilations. Let `g(a)=mu(a)` when `gcd(a,6)=1`, and `g(a)=0` otherwise; put `G(x)=sum_(a<=x)g(a)` and

```
U_3(n) = G(n/3)-G(n/6)
       = sum_(n/6<a<=n/3, gcd(a,6)=1) mu(a).             (16y)
```

For `n>=6`, `U_3(n)` is exactly the unsigned-in-`p` inner cofactor sum of (16x) at `p=3`: `a=1` is outside the window, and `gcd(a,6)=1` means every prime factor of `a` exceeds `3`. Coefficientwise inclusion--exclusion of the Euler primes `2` and `3` gives `mu=g-dil_2(g)-dil_3(g)+dil_6(g)`, including squareful integers. Summing to `n` therefore gives the **exact identity at every integer cutoff**

```
M(n)=G(n)-G(n/2)-G(n/3)+G(n/6)
    =U_3(3*n)-U_3(n).                                    (16z)
```

This supplies a smaller RH-scale target than the whole low-prime covariance: if `E_3(X)=sum_(n<=X) U_3(n)^2`, then `Q(X)<=4*E_3(3X)`. Conversely, inverting the two finite Euler removals gives `G(x)=sum_(i,j>=0) M(floor(x/(2^i*3^j)))`, and subtracting its half-scale copy telescopes the powers of `2`:

```
U_3(n)=sum_(k>=1) M(floor(n/3^k)).                     (16aa)
```

The sum is finite because `M(0)=0`. For every finite `X`, Minkowski and the fact that each integer `m` has at most `3^k` preimages under `n |-> floor(n/3^k)` give the unconditional energy inequality

```
sqrt(E_3(X)) <= sum_(1<=k<=floor(log_3 X))
                  sqrt(3^k * Q(floor(X/3^k))).          (16ab)
```

If `Q(X)=O_epsilon(X^(2+epsilon))`, the right side is `O_epsilon(X^(1+epsilon/2))` by a geometric sum `sum_k 3^(-k*(1+epsilon)/2)`. Together with `Q(X)<=4*E_3(3X)`, this proves that the *all-epsilon critical energy bounds for `Q` and `E_3` are equivalent by finite scale inequalities*, without invoking an analytic converse. The existing quadratic-Mertens receiver then makes `E_3(X)=O_epsilon(X^(2+epsilon))` for every positive `epsilon` an RH-equivalent producer. This single fixed prime-3 rough half-window is not merely one summand to be paid separately. The formal prime-removal law `RHTower.mobiusMertensPartialSum_eq_primeWindow` already supplies the one-prime step; the displayed two-dilation reconstruction and its energy inequalities remain paper-level. Existing short-window mean-square results found by deep corpus search concern windows of subpower length and do not give the proportional-length bound for `U_3`.

**Power-unbalanced pairs are already absolutely paid.** For each `n>=1`, set `D=floor((n^2)^(1/3))`. Then `sum_(m<=D) m^2 <= D^3 <= n^2`, so, for every `delta>0`,

```
sum_(n<=N) sum_(m<=N, m^3<=n^2)
  m^2 n^2/(m+n)^(5+delta)
  <= sum_(n<=N) n^(-1-delta) <= sum_(n>=1) n^(-1-delta) < infinity. (16)
```

The signed Möbius contribution `U_delta(N)` of this sector obeys the same cutoff-independent absolute bound. The transposed sector does too, and the two sectors intersect only at `(m,n)=(1,1)`. Thus, for `N>=1`, the complete form in (15) decomposes exactly as

```
B_(3+delta,delta)(N)
 = C_delta(N) + 2 U_delta(N) - 2^(-(5+delta)),
C_delta(N) = sum_(m,n<=N, m^3>n^2, n^3>m^2)
  mu(m)mu(n) m^2 n^2/(m+n)^(5+delta).             (17)
```

Consequently bounded returns of (15) are equivalent to bounded returns of the **power-balanced signed energy** `C_delta(N)`, for each fixed `delta>0`; the correction is uniformly bounded. `MobiusReciprocalUnbalancedTail` proves (16), the signed-sector bound, and the singleton-overlap law in Lean. `MobiusReciprocalBalancedCore` proves the exact finite partition, and `MobiusReciprocalBalancedGammaBridge` proves (17) for the same reciprocal energy used by the Gamma--Hankel endpoint; both passed targeted `lake --old build`. The arithmetic task is now restricted to pairs whose smaller index exceeds the two-thirds power of the larger, and whose separation is beyond the already controlled fixed or polylogarithmic shifts. Existing Type-II corpus lemmas classify prime-factor scales or control oscillatory reciprocal phases; their hypotheses do not give the signed additive-kernel estimate for `C_delta(N)`.

**Signed endpoint sharpening (paper proof; Lean theorem open).** The bound in (16) grows like `1/delta` as `delta` tends to zero, but the literal signed `U_delta(N)` has one bound valid for all `N` and `0<=delta<=1`. Put `D_n=floor(n^(2/3))` and `A(D)=sum_(m<=D) mu(m)m^2`. The source's Mertens estimate `|M(x)| <<_q x/log^q(2x)` for every fixed `q` (formalized as `Sieve.deningerMertensM_log_pow_rate`) and finite Abel summation give `|A(D)| <<_q D^3/log^q(2D)`: split the Abel remainder at `sqrt(D)` to use the trivial bound on small indices and the uniform logarithmic bound on the rest. For `q=3` and `D_n` comparable to `n^(2/3)`, this is `|A(D_n)| << n^2/log^3(2n)`.

For `p=5+delta` in `[5,6]`, the mean-value theorem yields `0 <= n^(-p)-(n+m)^(-p) <= 6m/n^6`. Consequently the exact split

```
U_delta(N)
  = sum_(n<=N) mu(n) A(D_n)/n^(3+delta) + R_delta(N),
|R_delta(N)| <= 6 sum_(n>=1) n^(-4) sum_(m<=D_n) m^3
             <= 6 sum_(n>=1) n^(-4/3) < infinity
```

has a remainder bound independent of `N` and `delta`; here `D_n^3<=n^2` and `D_n<=n^(2/3)`. The main term is absolutely bounded, uniformly in those parameters, by a constant times `sum_(n>=1) 1/(n log^3(2n))`. Both grouped series converge uniformly for `0<=delta<=1`, so `U_delta(N)` tends to a limit continuous at `delta=0`. This removes the artificial `1/delta` loss from the unbalanced correction in (17): any unbounded critical behavior of the full source must occur in the signed power-balanced sector. It does **not** bound `C_delta(N)` or prove RH. No Lean or large build was run for this sharpening while the shared machine was under memory pressure.

**Every fixed integer order has the same signed endpoint gain (paper proof; Lean theorem open).** For an integer `J>=3`, the coupled order `R=J+delta` has the literal kernel

```
k_(J,delta)(m,n) = m^(J-1)n^(J-1)/(m+n)^(2J-1+delta).
```

Define `U_(J,delta)(N)` by restricting its signed double sum to `m^J<=n^(J-1)` and put `D_(J,n)=floor(n^((J-1)/J))`. The positive mass is at most `sum_n n^(-1-delta)`, since `sum_(m<=D) m^(J-1)<=D^J<=n^(J-1)`. At `delta=0` the signed sector still converges, uniformly for `0<=delta<=1`: with `A_(J-1)(D)=sum_(m<=D) mu(m)m^(J-1)`, Mertens plus Abel gives `|A_(J-1)(D)| <<_(J,q) D^J/log^q(2D)` for any fixed `q>1`. The main grouped term `sum_n mu(n) A_(J-1)(D_(J,n))/n^(J+delta)` is therefore dominated by `sum_n 1/(n log^q(2n))`. Taylor's bound for `p=2J-1+delta` makes the remainder at most `2J sum_n n^(-J-1-delta) D_(J,n)^(J+1) <= 2J sum_n n^(-1-1/J)`, also independent of `delta` and `N`. Thus the only unresolved pairs at this order satisfy both `m^J>n^(J-1)` and `n^J>m^(J-1)`. Their power boundary approaches the diagonal as fixed `J` grows. The already formalized finite order-transfer inequality (13) sends a bounded-return estimate for this signed sector at any chosen fixed `J` back to order three. The order may depend on `delta`, but the existing estimate gives no bound for that sector by itself.

**Product-index sign and forced composite compensation (paper proof; Lean theorem open).** The coprime primitive-ratio identity extends to the coupled kernel at every fixed `J`: write an off-diagonal pair as `(m,n)=(da,db)` with `(a,b)=1`. Then `mu(da)mu(db)=1_((d,ab)=1)mu(d)^2 mu(ab)`. In particular, every primitive factorization `ab=k` has the *same* sign `mu(k)`, while its kernel and admissible gcd scales are nonnegative. The balanced off-diagonal is exactly `sum_(k<=N^2) mu(k) H_(J,delta,N)(k)`, where

```
H_(J,delta,N)(k) = k^(J-1) sum_(ab=k, (a,b)=1, a!=b)
  (a+b)^(-(2J-1+delta))
  * sum_(d<=N/max(a,b), (d,k)=1,
         d*a^J>b^(J-1), d*b^J>a^(J-1)) mu(d)^2/d^(1+delta) >= 0.
```

The two inequalities involving `d` matter: the power-balanced mask is not invariant under common scaling. Thus the unresolved sign is a one-dimensional squarefree-product parity sum with an explicit positive divisor weight; rearranging factorizations of one product cannot cancel it.

The scale of required parity compensation is already visible without estimates on composite pairs. For `0<delta<1`, fixed `J`, and sufficiently large `X>2^(J-1)`, restrict the original balanced source to **distinct** primes `X<p,q<=2X`; every such pair meets the balanced inequalities and is primitive with product sign `mu(pq)=+1`. Every kernel atom is at least `4^(-(2J-1+delta)) X^(-1-delta)`. The corpus's unconditional dyadic prime lower bound (`RHTower.DeletionPrimePacket.upperPrime_card_eventually_lower`) gives `# {X<p<=2X} >> X/log X`; hence this prime--prime off-diagonal block is `>>_(J,delta) X^(1-delta)/log^2 X`. Any cutoff-independent upper bound for the full signed energy must compensate this power-sized positive packet through pairs with opposite total prime-factor parity (for example prime--squarefree-semiprime pairs). The global Mertens saving above already proves almost complete *relative* compensation at the cubic order; the open problem is its bounded absolute residual.

**Asymptotically complete composite compensation is already unconditional (paper proof; Lean theorem open).** Specialize the preceding prime block to `J=3`, take an integer `X` tending to infinity, call its positive mass `P_(delta,X)`, and let `N=2X`. The corpus's `upperPrimes N` is then exactly the window `(X,2X]`. Define the exact complementary signed contribution `R_(delta,X)=B_(3+delta,delta)(N)-P_(delta,X)`. The global signed estimate (16c) and `P_(delta,X)>>_delta X^(1-delta)/log^2 X` imply

```
R_(delta,X) = -P_(delta,X)
  + O_delta(X^(1-delta)*E(X)^2)
  = -P_(delta,X)*(1+o(1))                 (0<delta<1).   (17a)
```

Indeed `E(X)^2*log^2 X -> 0`. Thus *all remaining literal pair sectors together* cancel asymptotically the entire positive distinct-prime packet, far beyond the fixed-factor `2p` and `3p` compensations below. This is a source-specific quantitative cancellation law, but its residual can still grow like `X^(1-delta)*E(X)^2`; RH requires a bounded residual for arbitrarily small positive `delta`. The next mathematical question is which signed **composite subfamilies** realize the cancellation in (17a) and whether their remainder has an additional power saving. The current Mertens estimate controls their total only, not their separate contributions.

The signed unbalanced sector is uniformly bounded by (17). Consequently, if `D^-_(delta,N)` denotes the *positive magnitude* of all balanced terms with `mu(m)*mu(n)=-1`, while same-parity balanced terms are left nonnegative, then at `N=2X` the exact balanced partition gives `D^-_(delta,N) >= P_(delta,X)-O_delta(1+X^(1-delta)*E(X)^2) = (1-o(1))*P_(delta,X)`. Hence the compensating mass really occurs among opposite-parity **power-balanced** pairs; it cannot be assigned to the absolutely controlled unbalanced tail. This lower bound does not identify a particular composite subfamily or bound the final signed remainder.

**Compensation inside one shrinking interval (paper proof; Lean theorem open).** The compensation can be localized much further without a short-interval prime theorem. Fix `0<=delta<1`. For any integer interval `I=(Y,Z]` contained in `(X,2X]`, let `F_I(t)=sum_(n in I) mu(n)*n^2*exp(-n*t)` and define `B_delta(I)` by restricting both indices of (15) to `I`. The Mertens bound behind (16a) gives `|sum_(Y<n<=u) mu(n)| << X*E(X)` for every `Y<=u<=Z`. Finite Abel summation of `x^2*exp(-x*t)` on `I`, using `Z-Y<=X`, gives uniformly in `I` and `t>0`

```
|F_I(t)| << X^3*E(X)*(1+X*t)*exp(-X*t),
0 <= B_delta(I) = Gamma(5+delta)^(-1)
   * integral_0^infinity t^(4+delta)*F_I(t)^2 dt
   <<_delta X^(1-delta)*E(X)^2.                         (17b)
```

More generally, if an interval `I` has `p_I` primes, its distinct ordered prime-pair mass is `>>_delta p_I^2/X^(1+delta)` once `p_I>=2`. Thus (17b) forces `(1-o(1))` compensation inside **every** family of intervals for which `p_I/(X*E(X)) -> infinity`. To guarantee one such shrinking interval without a short-interval prime theorem, choose an integer length `H_X<=X` with `X*E(X)*log X=o(H_X)`, and partition `(X,2X]` into `O(X/H_X)` intervals of length at most `H_X`. The unconditional dyadic prime lower bound places `>> H_X/log X` primes in at least one interval `I_X`. Their distinct ordered prime-pair mass satisfies

```
P_delta(I_X) >>_delta H_X^2/(X^(1+delta)*log^2 X).
```

By (17b), `B_delta(I_X)/P_delta(I_X) <<_delta (X*E(X)*log X/H_X)^2 -> 0`. All same-parity terms in `B_delta(I_X)` are nonnegative and include the prime pairs. Hence the magnitude `D^-_delta(I_X)` of opposite-parity pairs **with both indices in the same interval of length `H_X`** obeys

```
D^-_delta(I_X) >= P_delta(I_X)-B_delta(I_X)
                 = (1-o(1))*P_delta(I_X).              (17c)
```

For example `H_X=ceil(X*E(X)*log^2 X)` satisfies the condition and is `o(X)`. At least one index in each such negative pair is composite. This proves nearly complete relative prime/composite compensation at a stretched-exponentially shrinking additive scale, not merely in the power-balanced region. The remaining obstacle is absolute control of the local and cross-interval residuals; (17b) still permits growth like `X^(1-delta)*E(X)^2`.

**Short-interval rank-one Gamma profile (paper proof; Lean theorem open).** The local bound (17b) has a sharper structural form. For `I=(Y,Z] subset (X,2X]`, write `H=Z-Y`, `S_I=sum_(n in I) mu(n)`, and use the Gamma-weighted norm `||.||_delta` from (16c). With `phi_Y(t)=Y^2*exp(-Y*t)`, finite Abel summation applied to `g_t(x)-g_t(Y)`, where `g_t(x)=x^2*exp(-x*t)`, gives

```
F_I(t)=S_I*phi_Y(t)+R_I(t),
|R_I(t)| << H*X^2*E(X)*(1+X*t)*exp(-X*t),
||R_I||_delta <<_delta H*E(X)/X^((1+delta)/2).        (17d)
```

Indeed every partial interval sum of `mu` is `O(X*E(X))`, `g_t(Y)-g_t(Y)=0`, and both the Abel endpoint term and the derivative integral cost at most `H*X*(1+X*t)*exp(-X*t)` before multiplication by that partial-sum bound. Since the exact norm of the constant-profile component is

```
||S_I*phi_Y||_delta
  = 2^(-(5+delta)/2)*|S_I|/Y^((1+delta)/2),
```

the reverse triangle inequality yields the quantitative rank-one law

```
|sqrt(B_delta(I))
  - 2^(-(5+delta)/2)*|S_I|/Y^((1+delta)/2)|
    <<_delta H*E(X)/X^((1+delta)/2).                     (17e)
```

For two such intervals `I=(Y_I,Z_I]` and `J=(Y_J,Z_J]`, write `K_delta(x,y)=x^2*y^2/(x+y)^(5+delta)`. The exact inner product of their constant profiles is `K_delta(Y_I,Y_J)`. Expanding (17d) and applying Cauchy--Schwarz therefore gives a source-faithful covariance comparison:

```
|sum_(m in I,n in J) mu(m)*mu(n)*K_delta(m,n)
  - S_I*S_J*K_delta(Y_I,Y_J)|
  <<_delta X^(-1-delta)*E(X)*
       (H_J*|S_I| + H_I*|S_J| + H_I*H_J*E(X)).          (17f)
```

For the shrinking interval used in (17c), the shape error has an extra factor `H/X=o(1)` relative to the maximal Mertens count scale. Thus the nearly complete prime/composite cancellation there is already visible in its *net Möbius count*. A blockwise route to an RH-scale global bound would need square-root-scale control of these counts together with their covariance; alternatively, stronger negative cross-interval covariance could compensate larger individual counts. Equation (17e) specifies the local quantity and error to attack, rather than treating all composite-pair terms as an undifferentiated residue.

**A two-adic composite compensation law (paper proof; Lean theorem open).** For positive real `x,y`, `0<=delta<=1`, and `K_delta(x,y)=x^2*y^2/(x+y)^(5+delta)`, set

```
D_delta(x,y) = K_delta(x,y)-K_delta(2*x,y)-K_delta(x,2*y)+K_delta(2*x,2*y).
```

This is exactly the four-term covariance obtained when an odd-prime source atom `mu(p)=-1` is paired with its squarefree semiprime atom `mu(2*p)=+1`. Put `h=5+delta`, `A=(x+y)/(2*x+y)`, and `B=(x+y)/(x+2*y)`. Direct scaling and one exact rational identity give

```
D_delta/K_delta = 1+2^(-1-delta)-4*(A^h+B^h),
A+B = 3*(x+y)^2/((2*x+y)*(x+2*y)) >= 4/3,
9*(x+y)^2-4*(2*x+y)*(x+2*y) = (x-y)^2.
```

Convexity of `u |-> u^h` on nonnegative reals yields `A^h+B^h >= 2*((A+B)/2)^h >= 2*(2/3)^h`. Thus the **sharp pointwise upper factor**, attained at `x=y`, is

```
D_delta(x,y) <= c_delta*K_delta(x,y),
c_delta = 1+2^(-1-delta)-8*(2/3)^(5+delta)
        <= 3/2-8*(2/3)^6 = 1163/1458 < 4/5.     (18)
```

For any finite positive base atoms `x_i` with nonnegative weights `w_i`, the paired energy `E=sum_(i,j) w_i*w_j*D_delta(x_i,x_j)` is nonnegative by the exact Gamma--Laplace square

```
E = Gamma(5+delta)^(-1) * integral_(0,infinity) t^(4+delta)
      * (sum_i w_i*(x_i^2*exp(-x_i*t)-(2*x_i)^2*exp(-2*x_i*t)))^2 dt
  <= (4/5)*sum_(i,j) w_i*w_j*K_delta(x_i,x_j).
```

For an odd-prime packet `X<p<=2X`, this says the literal prime plus `2p`-semiprime four-term block removes at least one fifth of the all-prime energy, including its diagonal. If `X>16` and `N>=4X`, every atom in this block lies in the power-balanced sector of (17), so the compensation occurs inside the unresolved sector itself. The distinct-prime lower bound above then makes the *amount removed* `>>_delta X^(1-delta)/log^2 X`. This is a fixed-factor, source-specific cancellation theorem, not the scale-dependent saving needed to bound (15); cross-terms with other source atoms remain uncontrolled.

The same mechanism has a sharp general-order formula. For `J>=3`, `q>=2`, `h=2*J-1+delta`, and `K_(J,delta)(x,y)=x^(J-1)*y^(J-1)/(x+y)^h`, its `q`-insertion difference satisfies

```
D_(q,J,delta)(x,y)/K_(J,delta)(x,y)
  <= 1+q^(-1-delta)-2*q^(J-1)*(2/(q+1))^h,       (19)
```

again with equality at `x=y`. Indeed `A_q=(x+y)/(q*x+y)`, `B_q=(x+y)/(x+q*y)` satisfy `A_q+B_q>=4/(q+1)`, since the numerator of the cleared inequality is `(q-1)^2*(x-y)^2`; convexity gives (19). For the cubic order, `q=2,3,5` each has an upper factor below one for every `delta>=0`, because the equivalent inequality at `delta=0` is `2*q^3*(2/(q+1))^5>1` and its left side gains the factor `(2*q/(q+1))^delta`. These individual cone contractions cannot simply be multiplied after the first insertion: its output has signed coefficients. The next arithmetic target is a quantitative multi-prime energy law for the **actual** squarefree Möbius packet that preserves enough cancellation across successive insertions to obtain scale decay, or a replacement invariant that does so.

There is an exact design tradeoff with the higher-order narrowing above. At `q=2` and `delta=0`, the condition that (19) contract is `3*(8/9)^J>1`: it holds for integer `3<=J<=9` and fails for every `J>=10` (check `3*8^9>9^9` and `3*8^10<9^10`, then use monotonicity). For prime insertions, the full critical-endpoint menu is `q in {2,3,5}` at `J=3`, `q in {2,3}` at `J=4`, `q=2` at `5<=J<=9`, and none at `J>=10`. Indeed the criterion is `2*q^J*(2/(q+1))^(2J-1)>1`, decreasing in `q>=2` and in `J>=3`; at `q=3` it is `4*(3/4)^J>1`, and at `q=5` it is `6*(5/9)^J>1`. Thus arbitrarily increasing order cannot be combined with this pointwise prime-insertion contraction near the RH endpoint. If the multi-prime law uses this local mechanism, it should first be sought at `J=3` or `4`, where more than one prime dilation is available and the order-transfer to the cubic target is already formalized.

**The first composite packet has a positive but non-monotone law (paper proof; Lean theorem open).** At the cubic critical endpoint `delta=0`, let `L_x(t)=x^2*(exp(-x*t)-4*exp(-2*x*t)-9*exp(-3*x*t)+36*exp(-6*x*t))`. Its Gamma--Laplace Gram kernel `G(x,y)=Gamma(5)^(-1)*integral_(0,infinity) t^4*L_x(t)*L_y(t) dt` is the full 16-term `2`-and-`3` insertion of `K_0`; for a prime `p>3`, the literal Möbius source on `{p,2*p,3*p,6*p}` is `-L_p`. Writing `a_1=1`, `a_2=-4`, `a_3=-9`, `a_6=36`, exact integration gives the scale-independent diagonal ratio

```
G(x,x)/K_0(x,x) = C_23 = 32 * sum_(d,e in {1,2,3,6}) a_d*a_e/(d+e)^5
  = 32*(1/16-32/729-27/1024+72/16807+72/3125),
3/5 < C_23 < 13/20.                                    (20)
```

For the lower bound in (20), bound the four nonconstant fractions respectively by `32/729<7/159`, `27/1024<53/2000`, `72/16807>1/240`, and `72/3125>23/1000`; the resulting lower estimate exceeds `3/160` before multiplication by `32`. The reverse estimates `32/729>7/160`, `27/1024>1/38`, `72/16807<1/230`, and `72/3125<1/43` give an upper estimate below `13/640`. In particular `C_23>3/5`, whereas the single-`2` ratio is `217/486<1/2`: inserting `3` after `2` **raises** the energy of a single prime atom. The one-prime contraction cannot be multiplied as a stepwise monotone rule. The positive survivor is a two-prime packet contraction on one dyadic interval. For `X<=x,y<=2X`,

```
K_0(x,y)/sqrt(K_0(x,x)*K_0(y,y))
  = (2*sqrt(x*y)/(x+y))^5 >= (2*sqrt(2)/3)^5 > 13/18.
```

Gram Cauchy--Schwarz and (20) therefore give the pointwise bound `G(x,y) < (9/10)*K_0(x,y)`. Define `G_delta` by replacing `t^4/Gamma(5)` in the displayed integral with `t^(4+delta)/Gamma(5+delta)`. Its diagonal ratio `G_delta(x,x)/K_delta(x,x)` and the dyadic correlation floor `(2*sqrt(2)/3)^(5+delta)` vary continuously with `delta`; the strict inequality persists with factor `9/10` for all `0<=delta<=epsilon` for some `epsilon>0`. Thus any finite nonnegative base packet in `[X,2X]` retains a nonnegative `2,3`-inserted energy below `9/10` of its original energy. For odd primes `X<p<=2X`, `X>144`, and `N>=12X`, every atom of this 16-term block lies in the cubic power-balanced sector. This establishes composite compensation after two prime insertions, but it is weaker than the single-`2` bound and does not produce decay with the number of inserted primes. The corpus's `EulerDeletionCompositeInterference` proves a related exact overlap law in a different Dirichlet Gram; the additive Gamma--Hankel calculation here does not follow from that theorem.

The complementary signed local mode is now quantified by the [prime-insertion dipole-jet theorem](../2-fully-proven/l-prime-insertion-dipole-jet.md). For a near-cancelling pair `f_(x+h)-f_x`, the energy ratio after inserting `q` tends to `1+1/q-256*q²*(-q²+3*q-1)/(q+1)^7`: it is `4513/4374>1` for `q=2` and `283/192>1` for `q=3`. Infinitely many literal prime/semiprime pairs `p,2r` approach this `q=3` jet, with the source signs intact. A positive counterweight also survives: two equally oriented dipoles at dyadic scales `x,2x` telescope under `2`-insertion to `v_x-v_(4x)`, whose exact energy is below `4/5` of that of `v_x+v_(2x)`. PNT supplies `≫R/log R` disjoint, aligned literal prime/semiprime precursors in four fixed relative-width intervals. Their *combined* signed source packet retains the `4/5` contraction and has energy `≫_delta R^(1-delta)/log²R` for sufficiently small `delta≥0`; every atom lies in the unresolved balanced sector for large `R`. A second disjoint band of literal prime atoms near half the base jet scale compensates the inserted packet further: exact rational Gamma covariance gives its squared energy below `2/3` of the inserted energy, hence below `8/15` of precursor energy. The surviving producer must globalize this cross-packet compensation across the full Möbius source, including unmatched atoms. The paper theorem is closed; its Lean formalization is open.

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

`MobiusRenewalPacketCorrelation` supplies the finite geometric pair split. `MobiusLaplaceMellinPlancherelBridge` supplies the closed Lean strict-right energy-to-RH endpoint. `RHTower.deningerMertensM_rate` in `DeningerMertensSummatory` supplies the unconditional saving used in (16a)--(16d), and `RHTower.DeletionPrimePacket.upperPrime_card_eventually_lower` supplies the prime lower bound used in (17a). Broad, deep, and method-view corpus searches for reciprocal-Laplace mean-square saving, antidiagonal Möbius convolution, second-derivative source bounds, higher fixed order, long shifted correlations, positive-kernel prime insertions, and prime--cofactor covariance recover conditional interfaces, the distinct unweighted additive-triangle criterion, the Ramaré prime off-diagonal identity, and convexity tools (`convexOn_rpow` and `Real.pow_arith_mean_le_arith_mean_pow`). The Ramaré bound leaves its low-frequency signed covariance and an error too large for (15); the corpus's short-interval Möbius mean square is a vanishing normalized variance, without the needed power rate. None supplies the power-sharp signed bound (15). Cached hybrid searches had nearly complete source coverage; goal-directed deep searches were partial, and many candidate declarations were source-only. No numerical computation was used.
