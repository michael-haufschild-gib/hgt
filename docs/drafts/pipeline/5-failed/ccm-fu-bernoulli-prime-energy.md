# CCM-FU: Bernoulli prime-merger energy

- **ID:** CCM-FU-PE5
- **Stage:** 5-failed
- **Type:** FALSIFIED; actual-source unbounded-growth survivor formalized
- **Source:** [actual adaptive ceiling](../1-in-progress/ccm-fu-adaptive-prime-ceiling.md)
- **Goal:** test whether averaging literal prime mergers supplies the complete signed diagonal bound without selecting an order.

## Frozen statement

At cutoff M retain the literal signed channels `C_d(M)=mu(d)K_d(M)` and the retained energies `Q_P(M)` for processed prime sets P. Let Pi be all primes below M. Process each prime independently with probability t. Define

`E_t(M)=sum_(P subset Pi) t^|P| (1-t)^(|Pi|-|P|) Q_P(M)`.

**PE5:** for every M and every real `0<=t<=1`, `E_t(M)<=Q_empty(M)`.

This is distinct from PE4's existence of one complete ordered path. At t=1, PE5 is SD1. The initial and final energy, source and factor-one ceiling remain fixed.

## Exact finite structure

Two squarefree source labels d,e belong to the same retained cofactor exactly when every prime in their symmetric difference is processed. Thus finite subset counting gives

`sum_(d,e<=M) C_d C_e t^(omega(d)+omega(e)-2 omega(gcd(d,e)))`.

Its retained cofactor-one mean is

`H_t(M)=sum_(d<=M) C_d(M) t^omega(d)`,

with `H_t(M)^2<=E_t(M)` by the finite variance identity. The half-probability case, the literal merger recurrence, exact conservation, both endpoints and the actual divisor-Abel landing are [formal and audited](../3-formalized/ccm-fu-bernoulli-prime-energy-identities.md). The generic t formulas are finite counting identities on paper; their full-parameter Lean generalization is not needed for the half-probability obstruction. A large mean is enough to reject PE5, but not adaptive PE4 or final SD1.

## Protocol and analytic direction

First reuse saved subset-state energies through32, then evaluate the cofactor-one mean and original diagonal at a short, predetermined dyadic range. Computations are guidance only. Never infer an all-scale ceiling from a finite pass.

The mean replaces mu(d) by `mu(d)t^omega(d)` before the divisor convolution. At t=1/2 its local Euler factor is `1-X/2`; its square factors as `(1-X)*(1+X^2/(4*(1-X)))`. The second factor has nonnegative coefficients and begins at prime-square order. This exposes a possible analytic obstruction at the pole of zeta, rather than a missing estimate at its zeros. Establish the exact coefficient factorization and source landing before asserting any asymptotic or no-go. The corpus's fractional convolution modules expose their Tauberian premise explicitly; do not treat that premise as proved.

Any negative closure must retain the strongest proved positive survivor: exact averaged-energy kernel, variance gap, or the actual source's forced fractional-deformation growth. PE4, SD1 and RH remain open unless independently closed.

## Current finite evidence

The stored full subset averages through32 meet the diagonal ceiling at t=1/2. A separate, predetermined dyadic mean-head screen through `2^18` first violates the necessary mean-square bound at M=1024. An independent 80-digit evaluation of the literal half-order sums gives

`H_(1/2)(1024) = -41.315533040000500392858073555446...`,
`Q(1024) = 1249.109767690844815361248296555...`,
`H_(1/2)(1024)^2-Q(1024) = 457.863502688528174234073139716...`.

The ratio is about1.36655; the complete signed endpoint ratio there is about0.11031. At `2^18` the mean-square/diagonal ratio is about30.4082. These are guidance, not Lean certificates. The first dyadic obstruction is not asserted to be the first integer obstruction. Both new runs took under one second each; no exponential subset enumeration or greedy-order rerun was performed. Data: [screen and direct audit](../2-fully-proven/computations/ccm-fu-bernoulli-prime-energy-2026-09-07/README.md).

## Analytic paper obstruction: the mean cannot have linear growth

This argument concerns the literal source and uses the pole at1, independently of RH. The actual divisor source is now holomorphic on `Re(s)>1/2`, has value at least `1/30` at1 and agrees with its `LSeries` on `Re(s)>3/2`, all in Lean. The [literal deformed Euler product, its holomorphic correction and the no-continuation theorem for the actual convolution](../3-formalized/ccm-fu-half-selection-euler-pole-obstruction.md) are formal. The [closed discrete transfer and growth certificate](../3-formalized/ccm-fu-half-selection-growth-obstruction.md) turns a hypothetical linear bound on H into that forbidden continuation. The actual mean and energy obstructions are unconditional Lean theorems.

Set `a(n)=mu(n)/2^omega(n)` and `b(n)=log(n)-tau(n)+2 gamma`, for positive integers n. Then `D(q)=sum_(n<=q)b(n)`. Put `g=a*b` (Dirichlet convolution) and `G_0(x)=sum_(n<=x)g(n)`. Exact finite interchange gives

`G_0(k)=sum_(d<=k)a(d)D(floor(k/d))`,
`H(M)=sum_(k<M)(sqrt(k+1)-sqrt(k))G_0(k)`.

For real x>=1 define `W(x)=integral_1^x G_0(floor(u))/(2 sqrt(u)) du`. At integers it is H; between adjacent integers W lies between its endpoint values. If H(M)=O(M), therefore W(x)=O(x). Twice integrating the summatory Dirichlet series by parts on `Re(s)>1` gives

`L(g,s)=2s(s+1/2) integral_1^infinity W(x)x^(-s-3/2) dx`.

Under that linear bound, the integral is holomorphic on `Re(s)>1/2`. All boundary terms vanish: W(1)=0 and W(x)=O(x). Uniform majorants on compact subsets justify holomorphic differentiation.

On `Re(s)>1`, absolute Euler multiplication gives `L(g,s)=L(a,s)B(s)`, where

`B(s)=-zeta'(s)-zeta(s)^2+2 gamma zeta(s)`.

The proved bound `abs_primeFreeDivisorDefect_le`, namely `|D(n)|<=24 sqrt(n)` also gives the holomorphic integral `B(s)=s integral_1^infinity D(floor(x))x^(-s-1) dx` on `Re(s)>1/2`. In particular B is regular at1. It is strictly positive there without any numerical Stieltjes-constant input: put `A(n)=sum_(k<=n)D(k)` and `w_n=1/n-1/(n+1)`. The proved all-cutoff prefix positivity and D(1)>0 give

`B(1)=sum_(n>=1)A(n)(w_n-w_(n+1)) >= D(1)/3 > 0`.

The boundary term `A(N)w_(N+1)` tends to zero by the hyperbola bound; the series converges absolutely after that bound. The [formal harmonic-boundary and Dirichlet-source certificate](../3-formalized/ccm-fu-divisor-source-harmonic-boundary.md) proves the stronger floor `B(1)>=1/30`, ordinary source convergence on `Re(s)>1/2`, holomorphy there and equality with the literal `LSeries` on `Re(s)>3/2`. It obtains the continuation directly from the corpus's polynomial Abel theorem, so no new Mellin-integral theorem is needed for this factor.

The squared Euler product for a has the exact local identity

`(1-X/2)^2=(1-X)*(1+X^2/(4*(1-X)))`.

Consequently `L(a,s)^2=R(s)/zeta(s)`, where `R(s)=prod_p(1+p^(-2s)/(4*(1-p^(-s))))`. The product is holomorphic near1: on every closed smaller half-plane `Re(s)>=sigma>1/2`, its deviations from1 are bounded by a constant times `p^(-2sigma)`. At s=1 all factors are positive and the absolutely convergent product satisfies R(1)>0. Lean proves the stronger explicit statements `Im R(1)=0` and `Re R(1)>=1`, together with holomorphy on the full strict half-plane and the exact source Euler identity.

If H had linear growth, its holomorphic continuation would therefore satisfy

`L(g,s)^2=B(s)^2 R(s)/zeta(s)`

near1 by identity continuation. The right side has a simple zero at1: zeta has residue1 and `B(1)^2 R(1)>0`. A square of a holomorphic function cannot have a simple zero. Equivalently its value zero forces L(g,1)=0 and hence derivative of its square zero, while the right derivative is `B(1)^2 R(1)>0`. Contradiction.

Thus `H(M)` is not O(M), and deleting any finite prefix preserves that failure. The finite variance inequality gives `H(M)^2<=E_(1/2)(M)`. Together with the proved `Q(M)<=722M^2`, this excludes every fixed multiple of the original diagonal as an all-cutoff ceiling for the half-probability averaged energy. No precise Selberg–Delange asymptotic or fractional Tauberian premise is needed.

## Closed Lean refutation and positive survivor

PE5 is refuted by the half-probability case alone. For every real K and every cutoff M₀, the actual source has some M>=M₀ with

`K*Q(M)<E_(1/2)(M)`.

No fixed multiplier or deleted finite prefix repairs the average-energy ceiling. This is a consequence of the stronger positive survivor: for every real C and M₀ there is M>=M₀ with

`C*M<|H(M)|`.

Thus the literal normalized deformed mean is unbounded in magnitude on every tail. This does not assert either sign or a precise asymptotic. Its dependency-closed paper proof is the discrete construction below; that exact construction and the unconditional growth/budget consequences are formal and audited. The [growth certificate](../3-formalized/ccm-fu-half-selection-growth-obstruction.md) records all25 new public theorems. The earlier finite identities, divisor-source boundary and Euler/pole certificates remain closed.

The refutation applies to independent averaging. Actual adaptive PE4, final SD1 and RH remain open.

## Closed discrete continuation transfer

The continuation is constructed by two finite Abel summations and locally uniform series bounds, with the original arithmetic convolution, integer indexing and square-root clock retained.

Write `G_n=sum_(j<=n)g(j)`, `h_n=(sqrt(n+1)-sqrt(n))*G_n` and `A_N=sum_(n<=N)h_n=H(N+1)`. Suppose the actual mean has a linear bound. Then `|A_N|<=C(N+1)` after enlarging a nonnegative constant. For positive n put

`u_n=sqrt(n)+sqrt(n+1)`,
`f_s(n)=u_n*(n^(-s)-(n+1)^(-s))`.

The exact identity `u_n*(sqrt(n+1)-sqrt(n))=1` and two finite Abel summations give

`sum_(n<=N)g(n)n^(-s)=G_N*(N+1)^(-s)+A_N*f_s(N+1)+sum_(n<=N)A_n*(f_s(n)-f_s(n+1))`.

For `sigma=Re(s)>0`, the corpus's `norm_cpow_unit_diff_le` and `norm_second_difference_cpow_le` give

`|f_s(n)|<=3|s| n^(-sigma-1/2)`,
`|f_s(n)-f_s(n+1)|<=(3|s||s+1|+|s|) n^(-sigma-3/2)`.

Indeed `u_n<=3 sqrt(n)` and `u_(n+1)-u_n=sqrt(n+2)-sqrt(n)<=1/sqrt(n)`. Expand the difference as `u_n` times the second difference of `n^(-s)`, minus `(u_(n+1)-u_n)` times its next first difference. These estimates are uniform on compact subsets after bounding `|s|` and choosing a lower real part greater than1/2.

Consequently `F(s)=sum_(n>=1)A_n*(f_s(n)-f_s(n+1))` is locally uniformly absolutely convergent and holomorphic on `Re(s)>1/2`: its majorant is a constant times `n^(-sigma-1/2)`. The boundary `A_N*f_s(N+1)` tends to zero there. Also `h_N=A_N-A_(N-1)=O(N)`, so `G_N=u_N*h_N=O(N^(3/2))`; hence `G_N*(N+1)^(-s)` tends to zero for `Re(s)>3/2`. On `Re(s)>3/2`, the already absolute source series therefore equals F, in particular on the safe half-plane `Re(s)>2`. This is exactly the continuation excluded by the formal `not_exists_analytic_halfSelectionDivisor_extension`. No Tauberian premise or numerical estimate enters the transfer.

The exact finite source landing and the polynomial/second-difference Dirichlet APIs retain the original integer indexing and square-root clock. Neither an ordinary unweighted prefix bound nor a different convolution may be substituted for the assumed bound on H.

Reusable corpus evidence: `differentiableOn_dirichletSum` in `DirichletUniformAbel.lean` and the proof of `not_exists_bound_squarefreeHalfDirichletPartialSum_boundaryExteriorPoint` in `SquarefreeConvolutionHalfCofinalScheduleNoGo.lean` demonstrate the bounded-partial-sum/holomorphic-root contradiction method. Their coefficient system differs from this one, so their source identities cannot be substituted here. No fractional Wiener–Ikehara premise is required.
