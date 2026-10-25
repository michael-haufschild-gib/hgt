# The balanced physical CRT defect

- **ID:** twin-prime-balanced-crt-compensation
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CLASSICAL DEDUCTION
- **Source:** [RH-language reformulation](../1-in-progress/twin-prime-rh-language-reformulation.md), finite-horizon defect (6).
- **Statement:** The balanced physical CRT defect is `O(Y^(2-1/400))`, uniformly for bounded complex product weights and therefore for every nonnegative damping of the actual Möbius weights. This is a paper deduction from Bettin--Chandee; no Lean certificate for that analytic input is claimed.

## Exact first estimate

For integers `Y>=2`, `Y^2<=X<=4Y^2`, and `0<=epsilon<=1`, put

`D_Y = {d : Y<d<=2Y, d odd}`,

`N_X(d,e) = #{n : 2<=n<=X, d|n, e|n+2}`,

`S_epsilon(X,Y) = sum_(d,e in D_Y, gcd(d,e)=1)
 mu(d)mu(e)(de)^(-epsilon) [N_X(d,e)-(X-1)/(de)]`.

The estimate proved below has `delta=1/400`: there is an absolute `C>0` such that

`|S_epsilon(X,Y)| <= C Y^(2-delta)`

for all displayed parameters. In fact the proof replaces
`mu(d)d^(-epsilon)` and `mu(e)e^(-epsilon)` by arbitrary complex
coefficients `alpha_d,beta_e` of magnitude at most one, supported on
the displayed odd dyadic interval. Thus its damping uniformity holds
for all `epsilon>=0`. No analytic premise is introduced into Lean.

The bound would pay this block after division by `X epsilon_X^2`, at
the already-certified schedule `epsilon_X=log^(-4)(X+4)`. It would not
pay the remaining divisor blocks or their cofactor tails. The task's
completion criterion remains unconditional twin-prime infinitude.

## Exact Fourier reading

For odd coprime `d,e`, choose `dbar` inverse to `d` modulo `e`.
The compatible residue modulo `de` is `r=d*(-2*dbar mod e)`.
For `E(z)=exp(2 pi i z)`, finite character orthogonality gives

`N_X(d,e)-(X-1)/(de)
 = (1/(de)) sum_(1<=k<de) E(2k*dbar/e)
     sum_(2<=n<=X) E(kn/(de))`.

This retains both the changing modulus and the coupled interval
factor. The latter is bounded by a constant times
`min(1,1/min(k,de-k))` in the displayed balanced range.
Its absolute Fourier sum therefore does not produce a power saving.
A low-frequency truncation requires a proved endpoint remainder;
an arbitrary sharp cutoff in frequency does not supply one.

## Competing attacks

1. A varying-modulus inverse-phase estimate could pay the balanced
   head, where the two cofactor weights are unweighted interval
   indicators. Its precise coefficient and endpoint norms must be
   checked. A fixed-modulus Kloosterman bound is not this estimate.
2. A prime-dilation argument might exploit the actual Möbius source.
   Any such reduction must preserve the physical determinant equation
   and account for primes dividing coefficients and modulus. It cannot
   silently substitute fixed-affine-form cancellation for a theorem
   uniform in growing coefficients.
3. Reciprocity and exchanging `d,e` can make the Fourier expression
   real, but a real expression need not be small. The signed sum is
   still the quantity to bound.

The sharp endpoint is handled by physical smoothing below, with its
entire error counted. The analytic inverse-phase estimate is an existing
theorem, not a new conjectural input.

## Checked analytic input

[Bettin--Chandee, Theorem 1](https://arxiv.org/pdf/1502.00769), with
the third coefficient supported at `1`, implies the following special
case. For `1<=|k|<=Y^(1/100)`, arbitrary bounded coefficients on
`(Y,2Y]`, and arbitrary two upper cutoffs in that interval,

`|sum_(d,e, gcd(d,e)=1) alpha_d beta_e exp(-4 pi i k dbar/e)|
 << Y^(39/20+1/1000)`.

The constant is uniform in `k`, cutoffs, and coefficients. This follows
by setting both dyadic lengths to `2Y`; the coefficient norms are
`O(sqrt(Y))`, and the displayed frequency factor in Theorem 1 is
bounded. Odd support and cutoff indicators belong to the coefficients.
The primary theorem statement was checked directly. No implementation
of this varying-modulus bound was located in the corpus searches.

## Complete paper deduction

The following proof applies to arbitrary bounded complex product
weights. Write `S` for the corresponding defect and take `Y` sufficiently
large; finitely many smaller horizons are absorbed into the constant.
Set

`K=floor(Y^(1/100))`, `W=X Y^(-1/200)`.

Choose a fixed nonnegative smooth function `psi`, supported on `[-1,1]`
and of integral one. Put `psi_W(t)=psi(t/W)/W` and

`f = 1_[3/2,X+1/2] * psi_W`.

Then `0<=f<=1`, `integral f=X-1`, and the integer values of `f` differ
from the indicator of `[2,X]` only within distance `W` of the two
endpoints. Its support lies in an interval of size `O(X)`, with
`|t|=O(X)` throughout, because `W<=X`.

### 1. The complete smoothing error

For an integer `n` other than `0,-2`, the number of possible divisor
pairs is at most `tau(|n|)tau(|n+2|)`. At `n=0,-2` there are no pairs:
one of the odd divisors greater than `Y>=2` would have to divide `2`.
There are `O(W+1)` integer arguments in the endpoint strips and both
nonzero arguments have magnitude `O(Y^2)`.

For completeness, `tau(n)<=C_a n^a` for any fixed `a>0`: for primes
`p>=2^(1/a)`, `b+1<=2^b<=p^(ab)`; for each of the finitely many smaller
primes, `sup_b (b+1)/p^(ab)` is finite. Multiplying these bounds over
the prime factorization proves the assertion with one finite constant.

Use `a=1/3200`. The product of divisor counts is `O(Y^(1/800))`.
Consequently, if `S_f` is the smoothed defect,

`|S-S_f| << W Y^(1/800) << Y^(2-3/800)`.

No stationary main-term error is present: the integral of `f` is
exactly `X-1`. All coefficient magnitudes are at most one.

### 2. Exact nonzero-frequency expansion

Use the Fourier convention `fhat(xi)=integral f(t) exp(-2 pi i xi t) dt`.
Periodizing the smooth compactly supported function `f` modulo `de`
gives a smooth periodic function. Its Fourier coefficients are
`fhat(k/(de))/(de)`; its absolutely convergent Fourier series therefore
gives

`S_f = sum_(k in Z, k!=0) sum_(d,e in D_Y, gcd(d,e)=1)
 alpha_d beta_e A_k(d,e) exp(-4 pi i k dbar/e)`,

where `A_k(u,v)=fhat(k/(uv))/(uv)`. The zero frequency is exactly the
subtracted mean. The phase sign follows from the compatible residue
`r/(de)=-2*dbar/e (mod 1)`.

### 3. Frequencies at most K

The moment bounds
`|fhat^(j)(xi)| <<_j X^(j+1)` for `j=0,1,2` follow by differentiating
the compactly supported Fourier integral. On `[Y,2Y]^2`, with `X`
comparable to `Y^2`, differentiating `A_k` gives

`|A_k| << 1`,
`|partial_u A_k|+|partial_v A_k| << (1+|k|)/Y`,
`|partial_u partial_v A_k| << (1+|k|)^2/Y^2`.

The two-dimensional partial-summation formula expresses the weighted
sum using one corner value, two boundary derivative integrals, and
one mixed-derivative integral against rectangular partial sums of the
inverse phase. Their total variation cost is `O((1+|k|)^2)`.
Applying the checked input to each rectangular partial sum and summing
over `0<|k|<=K` therefore gives

`O(Y^(39/20+1/1000) K^3) = O(Y^(1981/1000))`.

The damping never enters these derivative bounds: its two separated
factors are part of `alpha,beta`.

### 4. Every discarded frequency

The transform factors as `fhat=1hat_[3/2,X+1/2] * psihat(W xi)`.
The interval transform has magnitude at most `1/(pi |xi|)` for
nonzero `xi`. Four integrations by parts in the fixed smooth bump give
`|psihat(t)| << (1+|t|)^(-4)`. Hence

`|A_k(d,e)| << |k|^(-1) (1+|k| W/(de))^(-4)`.

Here `W/(de)>=Y^(-1/200)/4`. Since
`K>=Y^(1/100)/2` eventually, the complete tail is bounded by

`sum_(|k|>K) |A_k(d,e)| << (Y^(1/200)/K)^4 << Y^(-1/50)`.

There are `O(Y^2)` divisor pairs, so the discarded contribution is
`O(Y^(2-1/50))`. Absolute convergence also justifies exchanging the
finite divisor sums and this Fourier series.

### 5. Assembly and scope

The three exponents are `2-3/800`, `1981/1000`, and `2-1/50`.
Each is strictly less than `2-1/400`. This proves

`|S| << Y^(2-1/400)`.

For `epsilon>=0`, the actual coefficients satisfy the required unit
bound because `d,e>=1`. Dividing by `X epsilon_X^2` on the certified
schedule leaves `O(X^(-1/800) log^8(X+4))`, which tends to zero.

This pays the balanced divisor block. It neither estimates the
complete divisor sum nor pays the cofactor tail. In particular the
argument uses the unweighted interval in the cofactor coordinate;
an additional arithmetic cofactor coefficient changes the Fourier
transform and the derivative bounds in step 3.

## Audit and next decision

- Previous goal turn: **progress**. Two unconditional bridge leaves
  and nine capstone axiom audits completed; the explicit damping
  schedule now fixes the required normalization of this estimate.
- **Verdict: CLASSICAL DEDUCTION / BRIDGE.** The balanced head does
  admit a power saving from an existing theorem. This is not a new
  source-specific cancellation theorem or a novelty claim.
- Corpus source checks: `KloostermanPhysicalResidueModulusBilinear`
  retains the full kernel but supplies a fixed-modulus baseline;
  `KloostermanHybridModulusBilinear` also states only baseline bounds.
  `RoutePTerminalModularPowerSaving` concerns ordinary reciprocal
  phases and absolutely summable Bernoulli coefficients, a different
  observation from this sharp inverse-residue defect.
- **Lean status:** the analytic input and the deduction above are
  not certified in this task. No theorem assuming that input has
  been added. A complete formal proof would need the input proved
  in the kernel, plus the smoothing and summation argument.
- **Next research decision:** the genuine new endpoint is compensation
  with arithmetic cofactor weights. Do not treat a saving for this
  two-weight block as a solution of the four-weight determinant sum.

## Gates

- [x] Exact arithmetic sum, parameter order, and required saving.
- [x] Input audit at the actual coefficient and endpoint norms.
- [x] Dependency-closed paper deduction from the cited proved theorem.
- [ ] Unconditional Lean certificate for a proved surviving result.

## Log

- 2026-10-23 — Began the balanced CRT attack after completing the
  quantitative damping bridge. Infinitude remains unproved.
- 2026-10-23 — Completed the sharp-endpoint smoothing argument and
  obtained exponent `1/400`, uniformly for bounded complex product
  weights. The retained phases use the checked classical theorem;
  all discarded frequencies and boundary strips are included in
  explicit power-saving errors. No Lean certificate or novel
  arithmetic estimate claimed.
