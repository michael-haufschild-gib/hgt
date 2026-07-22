# Suzuki positive-arch Mangoldt quadrature deficit

- **ID:** `suzuki-positive-arch-mangoldt-quadrature-deficit`
- **Stage:** 1 — in progress
- **Type:** RH-BEARING CONJECTURE / POSITIVE TRANSPORT / RESTRICTED QUADRATURE
- **Scientific status:** `[OPEN] [SOURCE-SPECIFIC] [DIRECT RH CONNECTOR FORMALIZED]`
- **Parent:** `suzuki-rectangular-positive-arch-lag-completion.md`
- **RH used in target proof:** forbidden
- **Computation used:** no

## Exact frontier

For fixed `L>0`, define

```text
C_a(h)=R_(L,a)(h),
A_a(t)=exp(t/4)C_a(t/2),
K_a(t)=A_a(t)
 +exp(-t)/[1-exp(-t)] [C_a(0)-exp(-t/4)C_a(t/2)].
```

Parent theorem proves `K_a(t)>0`, `0<=A_a(t)<=K_a(t)`, and

```text
PrimeWall(L,a)=sum_(2<=n<=exp(2a)) Lambda(n)/n A_a(2 log n).
```

Actual unsolved statement is

```text
D_L(a):=integral_0^infinity K_a(t)dt
 -2 sum_(2<=n<=exp(2a)) Lambda(n)/n A_a(2 log n)
 -(gamma+log pi)2L >= 0                              (Q)
```

on every sufficiently large logarithmic aperture.  Lean proves `(Q)` on any admissible cofinal
tail is equivalent to RH.  No Gamma sign problem remains inside `(Q)`.

## Scientific method: competing mechanisms

### Q1. Restricted-Weil Robin defect square `[PRIMARY CONJECTURE]`

Actual finite restricted-Weil resolvent and Robin boundary observation should produce an exact
source-to-observer identity

```text
D_L(a)=WardBoundaryNorm(L,a)^2 + HolonomySchurRemainder(L,a),
```

with second term positive semidefinite after marked half-gap completion.  This is preferred because
S64 identifies observer-response orientation, S65 identifies correct compact prime source, and
S66 identifies exact continuous/atomic channels.  Proof must derive both terms from existing
restricted-Weil operator, not define them from `D_L(a)`.

### Q2. Source-adapted lag-cell transport `[COMPETITOR]`

Construct positive cells `I_n` and source-derived transport densities `rho_n(t)` satisfying

```text
2 Lambda(n)/n A_a(2 log n)
 <= integral_(I_n) rho_n(t) K_a(t)dt,
sum_n rho_n(t) <= 1,
```

with leftover mass paying fixed boundary charge.  Cells and densities must arise from sharp
restricted-Weil/Robin kernel.  Arbitrary fitted cells would merely rename target inequality.

### Q3. Universal integer-log quadrature `[FALSIFIED]`

Corpus proves actual archimedean seam functional does not factor through integer-log or prime-power
samples on arbitrary continuous tests.  Therefore no universal sampling reconstruction can prove
`(Q)`.  Only special rectangular-family transport can survive.

## Exact falsifiers and gates

1. **No target-defined square.**  Any `WardBoundaryNorm := sqrt(max(D,0))` is circular.
2. **Source degree.**  Prime term is quadratic gated bare wall Gram; linear observer ray is wrong.
3. **Sharp support.**  Prime source vanishes beyond `log n=2a`; observer response need not.
4. **No universal sampling.**  Seam gap-tent no-go kills family-independent factorization.
5. **Boundary charge sign.**  Target requires `+ (gamma+log pi)2L` on atomic side; dropping or
   reversing it proves wrong inequality.
6. **No duplicate polar mass.**  `A_a` is already first summand of `K_a`; transport cannot add its
   polar square a second time.
7. **No asymptotic estimate substitution.**  Desired advance is exact positive operator/transport
   decomposition, not another scalar upper bound.

## S67 transport advance: monotone bulk discharged

The first source-derived transport now exists.  Put

```text
F_n=2 sum_(d<=n) Lambda(d)/d,   tau_n=2 log n.
```

Ramaré--Zuniga Alterman's known log-Haar capacity theorem gives `F_n<=tau_n`.  A new
endpoint-retaining divisor/factorial argument gives `tau_n-2<=F_(n-1)`.  Therefore

```text
P_n=(F_(n-1),F_n] subset (tau_n-2,tau_n],
Q_n=(F_(n-1)+2,F_n+2] subset (tau_n,tau_n+2],
length(P_n)=length(Q_n)=2 Lambda(n)/n.
```

Each family is pairwise disjoint.  Past cells pay decreasing branches; future cells pay increasing
branches.  Lean also contains a fully unconditional wider-cell version using in-tree Mertens
constant, so transport geometry does not depend on the unformalized external capacity theorem.

For Suzuki channel, transported atom is definitionally the exact prime-wall cell

```text
2 Lambda(n)/sqrt(n) R_(L,a)(log n).
```

Hence every moving-tent atom outside two lag units of its turning point is discharged by a
capacity-one Lebesgue cell once elementary branch monotonicity is instantiated.  Remaining
arithmetic debt is no longer whole window: it is splice layer where future and past cell families
would overlap.

### S68 hostile verdict: pointwise seam cells are impossible

`SUZUKI-TURNING-SEAM-BICAUSAL-SPLICE` is **falsified in its per-atom pointwise form**.  Put

```text
L=log 2,  a_n=(1/2)log(2n),  tau_n=2log n.
```

Lean proves for every `n>=4` that `tau_n` is the unique positive-lag maximizer of
`A_(L,a_n)`.  Hence every set on which `A(tau_n)<=A(t)` holds pointwise is Lebesgue null.  At every
prime power its required mass `2Lambda(n)/n` is positive.  Powers of two give a cofinal family, so
no tail restriction repairs the route.

The obstruction is stronger than past/future overlap: even arbitrary non-interval adaptive cells
cannot put positive mass inside a singleton superlevel.  Bulk transport remains valid away from
turning layer.

### New exact open core

`SUZUKI-APEX-BLOCK-TRANSPORT`:

Construct capacity-one source-canonical **blocks**, not individual cells, grouping each apex atom
with flank atoms before comparison.  Prove aggregate sampled `A_a` mass of every block is at most
aggregate completed-kernel mass on its target block, with disjoint target blocks and unused mass
paying `(gamma+log pi)2L`.  Required new object is nonnegative block surplus.  Defining that surplus
from target deficit is circular.

## Next proof target

Attack `SUZUKI-APEX-BLOCK-TRANSPORT` first.  Derive exact two-sided block surplus in cumulative-mass
coordinates and test whether restricted-Weil Robin current equals this surplus.  Do not attempt
another pointwise cell assignment and do not return to global prime estimates.

## Gates

- [x] exact RH-equivalent deficit isolated
- [x] both variable sides represented as related positive lag channels
- [x] universal sampling route killed by corpus theorem
- [x] exact bi-causal Mangoldt transport cells
- [x] monotone branch discharge and exact Suzuki prime-cell weld
- [x] RH-bearing debt localized to bounded moving turning seam
- [x] pointwise capacity-one future/past seam splice falsified cofinally
- [x] exact Mangoldt/Suzuki apex-lock rigidity formalized
- [ ] capacity-one apex/flank block transport
- [ ] source-derived restricted-Weil/Robin transport identity
- [ ] positive residual after prime assembly
- [ ] `(Q)`
- [ ] RH
