# All-cutoff orientation of the literal divisor source

- **Stage:** 3-formalized.
- **Type:** unconditional source theorem; no novelty claim.
- **Chain:** completed Guinand–Weil source -> marked rectangular current -> affine Suzuki checkpoints -> signed curvature -> coherent prime–polar–Gamma/unit-Riesz boundary -> Xi-screw Green -> RH.
- **Scope:** U1 and U2 are closed. The complete Möbius-signed SD1 inequality and RH remain open.

## Exact statements

For the literal source

`D(N)=log(N!)-sum_(d=1..N)floor(N/d)+2 gamma N`,
`A(N)=sum_(k=1..N)D(k)`,
`K_d(M)=sum_(k=d..M-1)(sqrt(k+1)-sqrt k)D(floor(k/d))`,

Lean proves, without arithmetic or analytic premises,

**U1:** `A(N)>=0` for every natural N.

**U2:** `K_d(M)>=0` for every natural M,d.

It also proves every floor-repeated ordinary prefix is nonnegative. Empty prefixes, zero dilation, births and clipped final blocks are included. The [earlier affine and square-root growth floors](ccm-fu-divisor-positive-prefix.md) remain valid. No numerical experiment is used as a proof premise. Unsigned orientation alone does not establish SD1.

## Dependency-closed paper proof

1. For x>=1,
   `log x<=2(x-1)/(x+1)+(x-1)^3/(6x(x+1))`.
   The derivative of the right side minus the left side is
   `(x-1)^4/(6x²(x+1)²)>=0`, and the difference vanishes at one.
2. The preceding upper bound and the existing Padé lower bound give, for x>0,
   `2/(x+1)<=log(x+2)-log x<=2/(x+1)+2/(3x(x+1)(x+2))`.
   Therefore `H_s-(log s+log(s+1))/2` decreases to gamma, while subtracting `1/(6s(s+1))` makes it increase to gamma. The harmonic limit and the vanishing logarithmic and reciprocal corrections identify both limits. Consequently
   `0<=H_s-gamma-(log s+log(s+1))/2<=1/(6s(s+1))` for s>=1.
3. Freeze the harmonic index s and put c=s(s+1). The sandwich gives
   `log c<=2(H_s-gamma)<=log(c+1)`.
   For the frozen smooth expression
   `F_s(k)=log(k!)-(2k+1)H_s+s²+s+2 gamma k`,
   the exact increment is `F_s(k+1)-F_s(k)=log(k+1)-2(H_s-gamma)`.
   It is nonpositive before c and nonnegative after c. Thus the discrete minimum is at c. Throughout the square block `s²<=k<(s+1)²`, the frozen expression is the literal smooth remainder R(k).
4. The corpus Stirling floor `log(c!)>=c log c-c+(log c)/2+11/12` yields
   `F_s(c)>=7/12-gamma-1/(6c)`.
   For s>=5, c>=30 and the existing analytic bound `gamma<577216/1000000` make this nonnegative. Hence `R(N)>=0` whenever N>=25.
5. Pair the two sides of the center. Exact factorial increments give
   `F_s(c-j)+F_s(c+j)-2F_s(c) = sum_(i=1..j)(log(c+i)-log(c-i+1))`.
   The logarithm lower bound gives each increment at least `(2i-1)/(s+1)²` for j<=s. Thus the paired difference is at least `j²/(s+1)²`. Summing the pairs and the nonnegative central term proves
   `sum_(k=s²..(s+1)²-1)R(k)>=s(s+1)(2s+1)/(6(s+1)²)>=(s+1)/4` for s>=5.
6. The initial interval is analytic. The harmonic half-error at 16 and an analytic log-two bound give `gamma>=5768/10000`. Rational logarithm inequalities at nearby ratios give lower bounds for log 7, 11, 13, 17, 19 and 23; product identities reduce composite logarithms to these and log 2, 3 and 5. Kernel-checked rational arithmetic then proves `A(N)>=0` for N<=24 and `sum_(k=1..24)R(k)>=7/2`. The finite rational simplification is factored into reusable exact identities; no experiment or external numerical certificate enters it.
7. Induct over complete square blocks starting at s=5. Step 5 pays exactly the increase in `(s(s+1)-2)/8`. Step 4 makes the terminal partial block nonnegative. Therefore
   `sum_(k<=N)R(k)>=(s(s+1)-2)/8`, s=floor(sqrt N), N>=25.
8. The exact centered-prefix identity is
   `sum_(k<=N)E(k)=sum_(d=1..s)P_d(N+1)`, with `P_d(T)=r(r-d)/(2d)`, r=T mod d.
   The modulus-one term is zero. Summing `P_d>=-d/8` only from d=2 gives
   `sum_(k<=N)E(k)>=-(s(s+1)-2)/16` for N>=1.
   Since D=R+2E, steps 6-8 prove U1 at every cutoff.
9. For any sequence f with nonnegative range prefixes, write N=dq+r with 0<=r<d. Complete quotient blocks and the clipped final block give exactly
   `sum_(k<N)f(floor(k/d))=(d-r)sum_(j<q)f(j)+r sum_(j<q+1)f(j)>=0`.
   Apply this to D, whose zero term vanishes. Thus every ordinary prefix of the floor-repeated source is nonnegative.
10. Discrete Abel summation against the nonnegative decreasing half-order weight writes each weighted prefix as a sum of these nonnegative ordinary prefixes times nonnegative weight differences, plus the nonnegative final endpoint. Terms before birth vanish. This proves U2 for every natural M,d; d=0 and empty channels are handled directly.

## Lean certificates and audit

All public declarations are in namespace `RHTower`.

- [HarmonicGeometricBounds.lean](../../../../formal/GaloisForLFunctions/RHTower/HarmonicGeometricBounds.lean): rational logarithm upper bound and geometric harmonic sandwich.
- [DivisorHyperbolaSharpBlocks.lean](../../../../formal/GaloisForLFunctions/RHTower/DivisorHyperbolaSharpBlocks.lean): slope sandwich, nonnegative smooth remainder from 25, and sharp complete-block mass.
- [DivisorHyperbolaSmallPrefixes.lean](../../../../formal/GaloisForLFunctions/RHTower/DivisorHyperbolaSmallPrefixes.lean): analytic base through 24 and initial smooth mass.
- [DivisorUnsignedChannelPositivity.lean](../../../../formal/GaloisForLFunctions/RHTower/DivisorUnsignedChannelPositivity.lean): sharp smooth and centered prefix allowances, `sum_primeFreeDivisorDefect_nonneg`, `sum_primeFreeDivisorDefect_floor_nonneg`, and `divisorUnsignedDilationChannel_nonneg`.

All four files pass individual foreground `lake env lean` checks. Only their exact oleans are produced, and all four are wired once into `RHTower.lean`; no large or umbrella build is run. One scratch audit of only these 12 new public declarations reports exactly `propext`, `Classical.choice`, and `Quot.sound`, with no added or computational certificate axiom. Formal lint passed with existing file-size warnings, the declaration index was refreshed, and completed task scratch files were removed.

## Remaining arithmetic boundary

The [SD1 card](../1-in-progress/mobius-divisor-source-diagonal-dominance.md) retains the single aggregate inequality
`(sum_d mu(d)K_d(M))²<=sum_d mu(d)²K_d(M)²`.
The unsigned signs, complete quadratic diagonal ceiling and exact homothety are closed source information. They do not prove this aggregate cancellation. Separate gcd-component nonpositivity and generic decreasing-weight producers are already refuted. The remaining producer must use genuine compensation in the complete arithmetic signed sum.
