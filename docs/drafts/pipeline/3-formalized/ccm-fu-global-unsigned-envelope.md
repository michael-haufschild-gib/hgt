# CCM-FU: global unsigned envelope and large-prime pairs

- **Stage:** 3-formalized; exact-file proof checks passed, Lake packaging audit pending
- **Type:** [BRIDGE], unconditional actual-source bounds
- **Parents:** [signed smooth blocks](ccm-fu-signed-smooth-block-ceiling.md), [bounded quotient profiles](../1-in-progress/ccm-fu-bounded-quotient-profiles.md).
- **Goal:** Uniform signed Abel bound, arbitrary processed-state extension, and RH remain open.

## Closed statements

Let `R(n)` be the literal smooth divisor-hyperbola remainder,
`a=log(2*pi)/2-gamma-1/6`, `w(n)=sqrt(n+1)-sqrt(n)`,
and `K_d(M)=divisorUnsignedDilationChannel M d`.
Lean proves all of the following without conjectural premises:

- `R(n)>=0` for every natural n, including the initial blocks.
- `sum_(n=s^2..(s+1)^2-1) R(n)w(n)<=a` for every s>=1.
- `SmoothAbel(M)<=a*sqrt(M)` and `K_d(M)<=a*sqrt(M)` for every M,d.
- There exists N0 such that `K_d(N)<=2K_1(N)` for every N>=N0 and every d, with no quotient restriction.
- There exists P0 such that `K_(pd)(M)<=2K_d(M)` for every integer p>=P0 and every cutoff M and cofactor d.
- There exists P0 such that the actual two-prime energy satisfies `Q_M({p,q})<=Q_M(empty)` for every pair of distinct active primes p,q>=P0, at every parent cutoff M and every prime ratio.

The thresholds are proved to exist; no explicit numerical threshold is claimed.
The analytic margin is `a<9/50`, while the existing unit limit is
`c_unit=log(2*pi)/2-gamma-1/4>9/100`.
The stronger candidate envelope with coefficient one eighth remains unproved
and is unnecessary for these factor-two conclusions.

## Dependency-closed paper proof

Put c=s(s+1). The first source-specific ingredient is the orientation
`R(c-j)<=R(c+j)` for s>=1 and 0<=j<=s. Its exact difference is

`sum_(i=1..j) [log(c-i+1)+log(c+i)] -4j(H_s-gamma)`.

Since `(c-i+1)(c+i)=c^2+c-i(i-1)`, set
`x=(c-i(i-1))/c^2`, with `0<=x<=1/c`.
The analytic Padé bound `2x/(x+2)<=log(1+x)` gives
`log(1+x)>=(1-1/(2c))*x`. Summing, using
`sum i(i-1)=j(j^2-1)/3` and j<=s, leaves

`(1-1/(2c))*(j/c-j(s^2-1)/(3c^2))
 =2j/(3c)+j(2s^2-1)/(6c^2*s)>=2j/(3c)`.

The existing upper harmonic correction
`H_s-gamma-log(c)/2<=1/(6c)` pays the harmonic slope.

For the clock, define `V_c(t)=(w(c-t)+w(c+t))/2`, extending w to
nonnegative real arguments. For c>0 and 0<=i<=j<=c/3, Lean proves

`V_c(j)-V_c(i)<=(j^2-i^2)/(4*c^(5/2))`.

Convexity bounds `(1-t)^(-3/2)-(1+t)^(-3/2)` by 4t on [0,1/3];
its endpoint estimate follows from exact square inequalities. Scaling and
two derivative comparisons give the displayed slope. The finite covariance
identity

`sum_i sum_j (q_i-q_j)(w_i-w_j)
 =2m*sum_i q_i*w_i-2(sum_i q_i)(sum_i w_i)`

then applies with `q_i=(n-c)^2`. The exact uniform moments are
`mu2=c/3`, `mu4=c(3c-1)/15`, and the block clock mass is one.
The clock excess is bounded by

`(2s+1)*(4c^2/45-c/15)/(4*c^(5/2))
 <=(2s+1)/(45*sqrt(c))<=1/18`,

so `sum (n-c)^2*w(n)<=c/3+1/18` for s>=2.

The source orientation and decreasing clock let each reflected pair be
bounded by the product of pair averages. The existing quadratic source bound
is `R(c-j)+R(c+j)<=2B+A*j^2`, where

`B=log(2*pi)/2-gamma-(2c+1)*(1/(6c)-1/(30c^2))+1/(12s^2)`,
`A=1/c-1/(2c^2)+1/(6cs(s+2))>=0`.

The weighted block is at most `B+(A/2)*(c/3+1/18)`. Its excess above a is

`-[48(s-2)^3+372(s-2)^2+742(s-2)+153]
 /[1080s^2(s+1)^2(s+2)]<=0`.

For s=1, analytic bounds `R(1)<=4/25`, `R(2)<=1/100`, `R(3)<=13/50`
and clock bounds 1/2,1/2,3/10 give the strict ceiling below 1/6<a.

The exact block minimum occurs at c. Existing source positivity from n>=25,
together with analytic positivity of the four initial centers 2,6,12,20,
proves R>=0 everywhere. Those initial estimates use exact factorial log
identities and proved logarithm/Euler-constant bounds, with no computed source
values. Thus SmoothAbel is monotone. Complete blocks give
`SmoothAbel((s+1)^2)<=a*s`. Completing the terminal partial block and taking
s=floor(sqrt(M)) gives the global smooth ceiling without an additive or
logarithmic loss. The initial missing square-root unit is retained.

The centered Abel contribution is nonpositive, giving the unit envelope.
Exact clipped interpolation transfers it to all dilations. The analytic
margins `a<9/50<2*c_unit` and the existing unit asymptotic give simultaneous
factor-two comparison for all d at every N>=N0. For p>=N0 and N<N0, the
p-channel is inactive. The existing unit/cofactor equivalence therefore gives
the comparison for every cutoff and cofactor once p is sufficiently large.

Finally, an existing exact two-prime failure theorem would expose
r in {p,q} and r<N<=M with `K_r(N)>2K_1(N)`. If p,q>=N0, the uniform unit
comparison contradicts that witness. This proves the actual two-prime ceiling.

## Exact remaining boundary

Unit factor-two failures are confined to finitely many unit cutoffs N<N0.
An original two-prime energy failure must involve at least one prime from a
fixed finite head. Its parent cutoff can still be unbounded; the result does
not reduce all energy states to a finite list.

The all-cofactor theorem concerns raw unsigned channels. It does not assert
that a large prime is an admissible successor for an arbitrary processed
signed field. Uniform control of those mixed signed states, the growing
exhaustive prime order, the complete signed Abel bound, SD1/PE4, and RH remain
open. The next source obstruction is the mixed interaction after processing
primes, rather than middle quotient profiles of a large unit cutoff.

## Lean surface and validation

All module paths below are under `GaloisForLFunctions/RHTower/`.

| Module | New public declarations |
|---|---|
| DivisorHyperbolaSharpBlocks.lean | divisorHyperbolaSmoothRemainder_center_le |
| DivisorSmoothSignedBlockCeiling.lean | divisorHyperbolaSmoothRemainder_pair_le_geometric_quadratic |
| DivisorSmoothBlockOrientation.lean | divisorHyperbolaSmoothRemainder_reflection_le |
| SymmetricSqrtClockBounds.lean | symmetricSqrtStep_quadratic_lipschitz |
| SquareBlockSqrtClockMoment.lean | sum_square_block_sqrtStep_quadratic_le |
| DivisorSmoothWeightedBlockCeiling.lean | sum_divisorHyperbolaSmooth_square_block_mul_sqrtStep_le_mean |
| DivisorSmoothSourcePositivity.lean | divisorHyperbolaSmoothRemainder_nonneg |
| DivisorUnsignedGlobalEnvelope.lean | divisorHyperbolaSmoothAbel_le_exact_mean_sqrt; divisorUnsignedDilationChannel_le_smoothMean_sqrt; exists_divisorUnsignedDilationChannel_uniform_unit_double; exists_divisorUnsignedDilationChannel_large_multiplier_double; exists_mobiusDivisorSelectionEnergy_two_large_primes_le_empty |

All names are in namespace RHTower. Complete scratch checks and exact-file
`lake env lean` checks passed. Only required leaf oleans were emitted, one
owned foreground process at a time. All six new modules are wired into
RHTower.lean; no umbrella build ran. The twelve new public declarations were
axiom-audited once from an external scratch file and depend only on `propext`,
`Classical.choice`, and `Quot.sound`. No old capstone was re-audited, no added
axiom or numerical premise was used, and no numerical experiment ran.

The declaration index refreshed, `scripts/formal_tools.py lint` passed with
existing large-file warnings, and `git diff --check` passed. All owned
Lean/Lake handles ended. Concurrent source changes were preserved.

The targeted Lake packaging audit remains pending. The known prerequisite
rebuild path was not repeated. These are passing exact-file proof checks,
not a claimed passing Lake build. The frontier map remained read-only.
