# Cubic Möbius prime insertion: dipole amplification and dyadic compensation

- **ID:** L-PRIME-INSERTION-DIPOLE-JET
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** Literal cubic Gamma--Hankel atom and squarefree prime insertion
- **Lean status:** Closed in `MobiusPrimeInsertionDipoleJet`, `MobiusPrimeInsertionLiteralPackets`, `MobiusPrimeInsertionMacroscopicPacket` and `MobiusCubicSourceMertensEnergy` (shared layers `MobiusCubicGammaNorm`, `MobiusCubicGammaAtomJets`, `MobiusAbelPrefixGramIntegral`).
- **Formalized companion:** [l-prime-insertion-dipole-jet-formalized.md](l-prime-insertion-dipole-jet-formalized.md)

## Theorem

For `delta≥0`, use the cubic Gamma--Hankel Hilbert norm and source atom

```text
||F||_delta² = (1/Gamma(5+delta))
               integral_(0,infinity) t^(4+delta) F(t)² dt,
f_x(t) = x² exp(-x t),
U_q F(t) = q² F(q t),
D_q = I-U_q,   so D_q f_x = f_x - f_(q x),
```

The change of variable `u=q*t` gives `||U_q F||_delta²=q^(-1-delta)||F||_delta²` whenever `F` has finite norm; in particular `||D_q||≤1+q^(-(1+delta)/2)`.

At the endpoint `delta=0`, let `q≥2` be an integer. For the signed near-collision packet `f_(x+h)-f_x`, `x>0`,

```text
lim_(h→0+) ||D_q f_(x+h)-D_q f_x||_0² / ||f_(x+h)-f_x||_0²
  = R_q
  = 1 + 1/q - 256 q² (-q²+3q-1)/(q+1)^7.                 (1)
```

The ratio is independent of `x`. In particular,

```text
R_2 = 4513/4374 > 1,
R_3 = 283/192 > 1,
R_q > 1+1/q   for every integer q≥3.                        (2)
```

Thus the same literal insertion that contracts nonnegative mass packets amplifies the first cancellation jet. The distinction persists for finite packets: for each `q≥2` there is `epsilon_q>0` such that every `0<h/x<epsilon_q` has insertion-energy ratio greater than one.

For comparison, the zero-jet (single-atom mass) ratios are `217/486` at `q=2` and `37/48` at `q=3`. The `q=3` insertion therefore contracts local mass by `11/48` but amplifies local first-jet energy by `91/192`. These are two distinct modes of the *same* source kernel, with no change of normalization.

There also exist arbitrarily high literal four-atom Möbius precursor packets, built from two prime/semiprime dipoles, whose `q=2`-inserted eight-atom packets have squared energy **less than `4/5`** of the precursor. Their analytic limiting pattern and prime realization are proved below.

This extends to a macroscopic packet: for some fixed `delta_0>0` and every `0≤delta≤delta_0`, arbitrarily large scales `R` admit `≫R/log R` disjoint such precursors whose *combined* inserted energy is less than `4/5` of their combined precursor energy. The latter is `≫_delta R^(1-delta)/log² R`, the scale of the unresolved prime-pair sector.

A second, disjoint prime band at half the base jet scale supplies a literal source compensator. For some possibly smaller `delta_1>0`, its inclusion lowers the combined squared energy below `2/3` of the inserted packet, and hence below `8/15` of the precursor packet. This remains a subpacket statement, not a full-source bound.

## Proof

By scaling it suffices to take `x=1`. Differentiation in the displayed weighted `L²` space gives

```text
g(t) = (2-t) exp(-t),
h_q(t) = q²(2-q t) exp(-q t),
(f_(1+h)-f_1)/h → g,
(D_q f_(1+h)-D_q f_1)/h → g-h_q.
```

The convergence follows from the mean-value theorem and domination by a polynomial times `exp(-t/2)` for `0<h≤1/2`. The elementary Gamma integrals `integral_0^infinity t^k exp(-a t) dt = k!/a^(k+1)` yield, before dividing by the common `Gamma(5)`,

```text
integral t⁴ g² = 9/8,
integral t⁴ h_q² = 9/(8q),
integral t⁴ g h_q = 144 q² (-q²+3q-1)/(q+1)^7.
```

Polarization proves (1). For `q=2`, `1/2-1024/2187=139/4374>0`; for integer `q≥3`, `-q²+3q-1<0`, proving (2). Continuity of the positive finite-difference norm gives the final assertion.

The same integral calculation supplies an exact *cross-scale* law. For `g_x=partial_x f_x` and the `delta=0` inner product,

```text
Gamma(5) <g_x,g_y> =
  144 x y (3xy-x²-y²)/(x+y)^7.                          (3)
```

Hence two equally oriented first-jet packets have negative covariance whenever their scale ratio exceeds `(3+sqrt(5))/2`; they have positive covariance between the two reciprocal thresholds. This sign change fixes where packet aggregation can help or hurt. The adjacent dyadic positive chamber below gives an explicit compensating mechanism; the aggregate source covariance remains open.

## Positive two-dipole compensation

Set `v_x=x g_x`. Dilation acts exactly as `D_2 v_x=v_x-v_(2x)`. Consequently

```text
D_2(v_x+v_(2x)) = v_x-v_(4x).                         (4)
```

This telescoping *does* contract the signed two-dipole energy, unlike a single dipole. By (3) and scaling,

```text
x Gamma(5) ||v_x+v_(2x)||_0² = 27/16 + 128/243,
x Gamma(5) ||v_x-v_(4x)||_0² = 45/32 + 23040/78125.  (5)
```

In fact the second value is less than `4/5` of the first. The elementary bounds `128/243>1/2` and `23040/78125<1/3` give

```text
45/32 + 23040/78125 < 45/32 + 1/3 = 167/96
  < 7/4 = (4/5)(27/16+1/2)
  < (4/5)(27/16+128/243).
```

Thus a dyadically coherent *signed* packet saves more than one fifth of its energy under insertion. The positive covariance between adjacent dipoles is converted by dilation into cancellation of their shared middle scale. Cross-packet covariance, rather than a cone argument on each packet, is the constructive mechanism exposed by this calculation.

## Literal Möbius occurrence

Let `r` run through primes tending to infinity. The prime number theorem supplies primes `p_r>2r` with `p_r/(2r)→1`. For large `r`, the four squarefree integers `p_r, 2r, 3p_r, 6r` have Möbius signs `-1,+1,+1,-1`. Their exact cubic source packet is

```text
-f_(p_r)+f_(2r)+f_(3p_r)-f_(6r)
  = -(D_3 f_(p_r)-D_3 f_(2r)).
```

Consequently this *literal four-atom subpacket* has insertion-energy ratio tending to `283/192` relative to its two-atom prime/semiprime precursor. It occurs at arbitrarily large source scales. This statement concerns a subpacket; cross terms with all other Möbius atoms remain decisive for the full source.

Because `p_r>2r`, these prime/semiprime precursors all approach the same orientation `-(p_r-2r)g_(2r)`. Pairs whose `r`-scales differ by more than `(3+sqrt(5))/2` therefore have negative leading covariance by (3), whereas neighboring dyadic scales have positive leading covariance. Which chamber dominates in the full source is an arithmetic question; the local sign law alone does not decide it.

There is also a literal realization of the **positive** dyadic mechanism (4)–(5). The PNT permits, for a sequence `epsilon_j→0`, primes `r_(0,j), r_(1,j), p_(0,j), p_(1,j)` such that

```text
r_(1,j)/(2 r_(0,j)) = 1+o(epsilon_j),
p_(k,j)/(3 r_(k,j)) = 1+epsilon_j+o(epsilon_j)  (k=0,1).
```

For each fixed `j`, take `epsilon_j=1/j`, then choose `r_(0,j)` sufficiently large that `GaloisForLFunctions.prime_between` applies with width `epsilon_j²` at `2r_(0,j)` and at `(1+epsilon_j)3r_(k,j)`. Choose `r_(1,j)` in `(2r_(0,j), (1+epsilon_j²)2r_(0,j))` and `p_(k,j)` in `((1+epsilon_j)3r_(k,j), (1+epsilon_j²)(1+epsilon_j)3r_(k,j))`. This diagonal choice gives the displayed asymptotics; all four primes can be taken arbitrarily large and distinct. With `x_(k,j)=3r_(k,j)`, the literal two-dipole precursor

```text
B_j = (f_(x_(0,j))-f_(p_(0,j))) +
      (f_(x_(1,j))-f_(p_(1,j)))
```

has exactly the Möbius signs `+,-,+,-`. The `2`-inserted packet `D_2 B_j` has the eight corresponding squarefree Möbius signs. Divide each by `epsilon_j` and rescale the weighted norm to `x_(0,j)=1`. The pair converges in that Hilbert space to `-(v_1+v_2)` and `-(v_1-v_4)`, respectively. Therefore the exact finite source-packet energy ratio converges to the quotient in (5), strictly below `4/5`. In particular, arbitrarily high literal signed packets save more than one fifth of their energy through *cross-packet covariance*. This does not control their interaction with the remaining Möbius source.

## Macroscopic aligned source packet

The strict inequality in (5) persists in the weighted norm with exponent `4+delta` for all `0≤delta≤delta_0`, with some `delta_0>0`: the two fixed exponential-polynomial profiles and their norms depend continuously on `delta`. Choose a sufficiently small fixed `epsilon>0` so the **finite** central packet

```text
B_epsilon = f_3-f_(3*(1+epsilon))+f_6-f_(6*(1+epsilon))
```

obeys `||D_2 B_epsilon||_delta² < c ||B_epsilon||_delta²` for a common `c<4/5` throughout that delta interval. Its norm is bounded below by a positive multiple of `epsilon`. By continuity of `a |-> f_a` in the weighted Hilbert norm, choose a fixed `eta>0`, much smaller than `epsilon`, so every packet formed by selecting one prime from each of

```text
(R,(1+eta)R],
(2R,2(1+eta)R],
(3(1+epsilon)R,3(1+epsilon)(1+eta)R],
(6(1+epsilon)R,6(1+epsilon)(1+eta)R]
```

has, after the scale change `t -> R*t`, a precursor vector within `tau*||B_epsilon||_delta` of `B_epsilon` in every norm `||.||_delta`, uniformly for `0≤delta≤delta_0`. Here `tau>0` may be made arbitrarily small by shrinking `eta`. Since `||D_2||≤1+2^(-(1+delta)/2)<2`, a sum of `M` packets has precursor norm at least `M(1-tau)||B_epsilon||_delta` and inserted norm at most `M(sqrt(c)+2*tau)||B_epsilon||_delta`. Choose `tau` so `(sqrt(c)+2*tau)/(1-tau)<sqrt(4/5)`. The nonzero central inserted profile also gives a positive lower bound for the inserted norm when `tau` is smaller still. Thus **any sum** of such aligned packets has inserted-to-precursor squared-energy ratio below `4/5`.

For fixed `epsilon,eta`, the corpus prime-number theorem gives `~(beta-alpha)R/log R` primes in each interval `(alpha R,beta R]`. Hence each interval contains at least `c_0 R/log R` primes for some `c_0>0` and all large `R`. Fix any sufficiently small `0<c<c_0`, select `M_R=floor(c R/log R)` distinct primes from each interval, and match them arbitrarily. The intervals are disjoint; all eight Möbius atoms per matched tuple are squarefree, carry the signs displayed above, and remain distinct across tuples. Let `P_R` be their combined four-atom precursor and `D_2 P_R` their combined eight-atom source packet. Scale homogeneity and the uniform alignment give

```text
||D_2 P_R||_delta² < (4/5)||P_R||_delta²,
||P_R||_delta² >= c_delta * M_R² * R^(-1-delta)
                >>_delta R^(1-delta)/log² R,
||D_2 P_R||_delta² >= c'_delta * M_R² * R^(-1-delta).  (6)
```

All packet indices lie between fixed positive multiples of `R`, so for sufficiently large `R` every pair of them lies in Route L's power-balanced sector. Thus (6) is a source-literal, macroscopic signed cancellation at the correct *size* of the hard sector. It is a subpacket identity: cross terms with the unselected Möbius atoms may offset this saving, and no cutoff-uniform bound for the full source follows.

The existing global Mertens energy saving determines the **orientation** of that unselected remainder. Fix `C>12(1+epsilon)(1+eta)`, put `N_R=ceil(CR)`, let `F_(N_R)` be the full literal cubic Möbius source, and set `Q_R=F_(N_R)-D_2P_R`. The already proved bound `||F_(N_R)||_delta² <<_delta R^(1-delta) E(R)²`, where `E(R)=exp(-(log R)^(1/3)/108)`, and (6) imply

```text
||F_(N_R)||_delta / ||D_2P_R||_delta <<_delta E(R) log R -> 0,
<D_2P_R,Q_R>_delta / ||D_2P_R||_delta²
    = -1 + O_delta(E(R) log R),
||Q_R||_delta / ||D_2P_R||_delta
    = 1 + O_delta(E(R) log R).                            (7)
```

The first estimate uses the lower bound for `D_2P_R` in (6); contraction alone would not give it. The latter two are polarization and the triangle inequality. Thus the *actual complement* of this selected macroscopic packet is asymptotically antiparallel to it in the Gamma Hilbert space: their normalized inner product tends to `-1`. The next arithmetic task is to identify and control a source-defined subfamily of `Q_R` that realizes this cancellation with a power-sharp residual; (7) identifies its direction but supplies only the known stretched-exponential saving.

## A literal second-stage prime compensator

The inserted dyadic first jet has a negative covariance with a *prime* atom at half its base scale. At `delta=0`, direct Gamma integration gives

```text
<v_x,f_z>_0 = x² z² (2z-3x)/(x+z)^6.
```

Put `H_x=v_x-v_(4x)` and `z=x/2`. Substitution in this identity and (5) gives exact rational values

```text
x <H_x,f_(x/2)>_0 = -20512/531441 < -77/2000,
x ||f_(x/2)||_0² = 1/16,
x ||H_x||_0² = (45/32+23040/78125)/24 < 71/1000.
```

The first inequality follows from `20512*2000>77*531441`; the last uses `23040/78125<59/200`. Consequently, taking the rational coefficient `3/5`,

```text
x (||H_x+(3/5)f_(x/2)||_0²-||H_x||_0²)
  = 9/400 + (6/5)x <H_x,f_(x/2)>_0
  < 9/400-(6/5)*(77/2000) = -237/10000
  < -(1/3) x ||H_x||_0²,                         (8)
```

where the final inequality follows from `237/10000>71/3000`. This proves a strict `2/3` energy reduction with a rational margin. Dominated continuity of the fixed exponential-polynomial profiles extends (8) to `0≤delta≤delta_1` for some `delta_1>0`.

This compensator has the correct *literal Möbius sign*. In the macroscopic construction above, the central precursor `B_epsilon` divided by `-epsilon` tends to `v_3+v_6`, and its insertion divided by `-epsilon` tends to `H_3`. Choose an additional narrow prime band centered at `(3/2)R`, disjoint from the four earlier bands. Select `L_R` primes from it with `L_R/(epsilon M_R) -> 3/5`, and set

```text
S_R = D_2 P_R - sum_(p in selected half-scale primes) f_p.
```

Every added coefficient is the literal prime Möbius value `-1`. First shrink `delta_1` so both strict limiting inequalities (5) and (8) hold uniformly on `0≤delta≤delta_1`. Next choose fixed `epsilon>0` small enough that the finite central precursor and its prime-corrected insertion retain both margins. Choose the widths of all five bands sufficiently small for uniform Hilbert alignment and disjointness. Finally take `M_R=floor(c R/log R)` with `c>0` small enough that the four precursor bands contain `M_R` primes each and the half-scale band contains `L_R=floor((3/5)epsilon M_R)` primes. The fixed-relative-interval PNT supplies these counts. After `t -> R*t`, the combined profiles are uniformly close to their central profiles, while `L_R/(epsilon M_R)->3/5`. Thus for all sufficiently large `R` and all `0≤delta≤delta_1`,

```text
||S_R||_delta² < (2/3)||D_2 P_R||_delta²
               < (8/15)||P_R||_delta².            (9)
```

All selected atoms are distinct squarefree source atoms, and they remain in the power-balanced sector at large `R`. This identifies an explicit macroscopic subfamily of the complement `Q_R` from (7) that cancels part of the inserted packet. The other unselected atoms still determine whether the full source admits a power-sharp residual bound.

## Consequence for Route L

The positive-packet insertion contraction in the Route L card controls its mass mode, whereas (1) gives the exact opposite response of its first signed dipole mode. A cutoff-uniform energy bound cannot follow by iterating packetwise contraction after the source has developed near-cancelling prime/composite pairs. Equations (4)–(9) exhibit two stages of literal source-compatible compensation at the scale of the unresolved sector. The next open theorem is a *global* dyadic pairing/covariance law for actual Möbius atoms, including unmatched packets and interactions between different pairs. The first explicit local debt is `R_3-1=91/192` times the precursor dipole energy.

The paper theorem is dependency-closed. Lean formalization should use the existing cubic kernel `K_0(x,y)=x²y²/(x+y)^5`: mixed differentiation at `(1,1)` of its four-term insertion gives (1) with rational algebra, avoiding a new improper-integral development. A complete Lean theorem must include the finite-difference limit, not merely the rational inequality. The PNT-based literal-packet corollary is separate from that algebraic core.

## Corpus audit

Broad hybrid and goal-directed deep searches for dipole, jet, dilation, prime insertion and reciprocal energy found the Route L positive-packet insertion law and general Laplace-dipole modules, but no cubic insertion first-jet ratio, dyadic signed compensation or macroscopic aligned packet. A separate deep search located `GaloisForLFunctions.prime_between` for the literal-packet realization; `RHTower.tendsto_primeCounting_nat_ratio` supplies fixed-relative-interval counts. Search results were partially returned; this is an internal corpus observation, not an external priority claim.
