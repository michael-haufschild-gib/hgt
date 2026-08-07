# Suzuki rectangular positive archimedean lag completion

- **ID:** `suzuki-rectangular-positive-arch-lag-completion`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-rectangular-positive-arch-lag-completion-formalized.md`
- **Type:** EXACT SOURCE COMPLETION / POINTWISE POSITIVITY / FRONTIER REDUCTION
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [SOURCE-SPECIFIC]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Formal module:**
  `GaloisForLFunctions.RHTower.SuzukiRectangularPositiveArchLagCompletion`
- **Parents:** `complete-sharp-rectangular-guinand-weil-prime-gamma-law.md`,
  `suzuki-rectangular-wall-gram-gate.md`
- **RH used:** no
- **Computation used:** no

## Actual frontier

Write the sharp two-edge autocorrelation as

```text
C(h)=R_(L,a)(h),       C(0)=2L,
```

and the exact Gamma cancellation kernel as

```text
G(t)=[exp(-t)C(0)-exp(-t/4)C(t/2)]/[1-exp(-t)].
```

The corpus knew that `G` is integrable and uniformly bounded after integration, and knew that the
two polar resolvents integrate to `2 P_(L,a)^2`.  It did not determine whether the polar and Gamma
channels have a common pointwise sign.  Treating Gamma sign as a separate global compensation
problem therefore left a larger frontier than necessary.

## Theorem A: zero-lag contraction `[PROVED HERE]`

If `0<=L<=a` and `h>=0`, then

```text
0 <= C(h) <= C(0)=2L.                                  (1)
```

### Proof

The fixed-plus-moving-tent formula is

```text
C(h)=2 max(0,L-h)+M(h),
M(h)=max(0,L-|h-(2a-L)|),
```

and the corpus proves `0<=M(h)<=min(L,h)`.  If `h<=L`, then
`C(h)<=2(L-h)+h=2L-h<=2L`.  If `L<h`, fixed tent vanishes and
`C(h)=M(h)<=L<=2L`.  Nonnegativity and `C(0)=2L` follow from exact tent identities.

## Theorem B: positive completed archimedean lag `[PROVED HERE]`

For `t>0`, define

```text
K_arch(t)=2 cosh(t/4) C(t/2)+G(t).
```

Then exact algebra gives

```text
K_arch(t)
 = exp(t/4) C(t/2)
   + exp(-t)/[1-exp(-t)] [C(0)-exp(-t/4)C(t/2)].         (2)
```

Consequently, if `0<=L<=a`, then `K_arch(t)>=0`.  If additionally `L>0`, then
`K_arch(t)>0` for every `t>0`.

### Proof

Expand `2 cosh(t/4)=exp(t/4)+exp(-t/4)` and put the second summand over the Gamma
denominator; this is `(2)`.  Its first term is nonnegative by `(1)`.  Also
`exp(-t)/[1-exp(-t)]>0` and

```text
C(0)-exp(-t/4)C(t/2)
 >= C(0)(1-exp(-t/4)) >= 0.
```

When `L>0`, `C(0)=2L>0` and `1-exp(-t/4)>0`, so the bracket and second term are strictly positive.

## Theorem C: exact integral and full Weil balance `[PROVED HERE]`

The polar-lag part is integrable and its integral is exactly the known polar square:

```text
integral_(0,infinity) 2 cosh(t/4) C(t/2) dt = 2 P_(L,a)^2.  (3)
```

Hence `K_arch` is integrable and

```text
normalizedArch(L,a)+(gamma+log pi)2L
  = integral_(0,infinity) K_arch(t) dt.                 (4)
```

Combining `(4)` with the sharp prime--archimedean formula yields

```text
Weil(L,a)+(gamma+log pi)2L
  = integral_(0,infinity) K_arch(t) dt
      - 2 PrimeAutocorrelationSum(L,a).                 (5)
```

### Proof

For `H(h)=C(h)exp(h/2)`, evenness of `C` gives

```text
2 cosh(t/4)C(t/2)=H(t/2)+H(-t/2).
```

The corpus proves `H` integrable, its whole-line integral is `P_(L,a)^2`, and positive/negative
half-line rescaling turns the displayed sum into twice that whole-line integral.  This proves
`(3)`.  Add the exact Gamma cancellation integral and use the corpus archimedean identity for
`(4)`.  Substitute `(4)` into the exact finite prime--archimedean formula for `(5)`.

## Theorem D: prime wall is exact positive-channel Mangoldt quadrature `[PROVED HERE]`

Let

```text
A_(L,a)(t)=exp(t/4) C(t/2),
```

the first positive channel in `(2)`.  For every positive integer `n`,

```text
Lambda(n)/sqrt(n) C(log n)
  = Lambda(n)/n A_(L,a)(2 log n).                       (6)
```

Therefore the entire finite prime wall is exactly

```text
PrimeAutocorrelationSum(L,a)
 = sum_(2<=n<=exp(2a)) Lambda(n)/n A_(L,a)(2 log n).    (7)
```

Moreover `0<=A_(L,a)(t)<=K_arch(t)` for `t>0`, so the prime wall is bounded by the
same-node Mangoldt quadrature of the completed kernel.

### Proof

At `t=2 log n`,

```text
A_(L,a)(t)=exp(log(n)/2)C(log n)=sqrt(n)C(log n).
```

Multiplication by `Lambda(n)/n` and `n=sqrt(n)^2` gives `(6)`; finite summation gives `(7)`.
The difference `K_arch-A` is exactly the second nonnegative term in `(2)`.

## Hostile audit

1. **No asymptotics.**  Every identity is finite-aperture and exact.
2. **No hidden RH.**  Only tent geometry, exponential algebra, integrability, and exact Weil formula
   are used.
3. **No separate-sign fallacy.**  Gamma kernel need not be nonnegative by itself; positivity holds
   only after addition of the polar lag at the same `t`.
4. **Strictness source exposed.**  Strict positivity comes from the zero-lag mass
   `C(0)(1-exp(-t/4))`, not from an unproved prime estimate.
5. **Prime sign remains visible.**  Equation `(5)` still subtracts twice a nonnegative finite prime
   wall.  Pointwise archimedean positivity does not imply Weil positivity.
6. **No computation.**  Sign proof is symbolic and unconditional.
7. **Sampling no-go respected.**  Corpus proves general archimedean seam functionals do not factor
   through integer-log samples on arbitrary continuous tests.  Equations `(6)--(7)` concern the
   special sharp rectangular autocorrelation family and only identify its prime wall; they do not
   claim universal reconstruction of archimedean mass from samples.

Verdict: `SURVIVES HOSTILE ATTACK`.

## Novelty audit

- Internal research search found the separate Gamma cancellation kernel, its limiting-minus-moving
  decomposition, and the separate polar resolvent square, but no common-lag positive completion or
  contraction theorem `(1)`.  It also found dyadic Mellin quadrature estimates, but no exact
  identification `(6)--(7)` of the sharp prime wall as samples of the positive completed-arch split.
- Suzuki arXiv:2606.09096 and Groskin arXiv:2607.02828 contain related restricted-Weil and positive
  archimedean structures, but targeted inspection found no formula matching `(2)--(5)`.
- Candidate novelty is the exact common-lag completion and resulting frontier reduction, not generic
  positivity of autocorrelation or elementary hyperbolic-function algebra.  Independent priority
  audit remains required.

## New frontier exposed

### `SUZUKI-POSITIVE-LAG-QUADRATURE-DEFICIT` `[CONJECTURE]`

For fixed `L>0`, prove on a cofinal aperture set

```text
integral_(0,infinity) K_arch(L,a,t) dt
  >= 2 sum_(2<=n<=exp(2a)) Lambda(n)/n A_(L,a)(2 log n)
       + (gamma+log pi)2L.                              (8)
```

Equations `(5)` and `(7)` make `(8)` exactly sharp rectangular Weil positivity.  New content is that
both variable sides are now evaluations of explicitly related positive lag channels: Lebesgue mass
of `K_arch` versus the finite Mangoldt atomic quadrature of its first positive summand `A`.
Gamma sign, polar growth, and prime-cell source type are no longer separate unknowns.  General
sampling cannot solve this by the corpus seam no-go; remaining RH-bearing problem is a
source-restricted positive quadrature discrepancy, to be attacked through actual restricted-Weil/
Robin transport rather than a universal sampling claim.

## Gates

- [x] actual corpus frontier identified
- [x] exact source-pure conjecture and hostile falsifiers
- [x] dependency-closed paper proof
- [x] internal/current-primary-literature collision audit
- [x] unconditional Lean formalization
- [ ] positive-lag quadrature deficit
- [ ] RH

### Lean progress — Theorem D's lower half and audit item 4 FORMALIZED

Audit of Theorems A--D against `RHTower/SuzukiRectangularPositiveArchLagCompletion.lean`.
Theorem A (`(1)`, through `rectangularTwoEdgeAutocorrelation_le_zeroLag` with the corpus
`..._nonneg` and `..._zero`), Theorem B (`(2)`, nonnegativity, strict positivity), Theorem C
(`(3)`, `(4)`, `(5)`) and Theorem D's `(6)`--`(7)` each had a declaration. Two things did not.

1. Theorem D asserts `0 <= A_(L,a)(t) <= K_arch(t)`. Only the **upper** half was formalized.
2. Hostile-audit item 4 asserts that strictness comes from the zero-lag mass `C(0)(1-exp(-t/4))`.
   The corpus proved only the bare `0 < K_arch`, which does not exhibit that source.

Both closed [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `suzukiRectangularPositiveArchSampleChannel_nonneg` : `0 <= A`, with no window hypotheses (the
  unconditional autocorrelation nonnegativity suffices).
- `suzukiRectangularPositiveArchSampleChannel_mem_Icc` : `A ∈ Icc 0 K_arch`, the displayed
  two-sided claim.
- `suzukiRectangularCompletedArchLagKernel_zeroLag_lower_bound` :
  `exp(-t)/(1-exp(-t)) * (C(0) * (1 - exp(-t/4))) <= K_arch(t)` — a **quantitative** lower bound,
  which is audit item 4 as a theorem: the whole strictness is carried by the zero-lag term, and the
  bound survives when `C(t/2) = 0`.
- `suzukiRectangularCompletedArchLagKernel_two_mul_lower_bound` : the same with `C(0)` replaced by
  its exact value `2L`.

The second bound is the quantitative form the deficit conjecture `(8)` needs on the left-hand side:
it bounds the Lebesgue mass of `K_arch` from below by an explicit elementary integrand, with no
appeal to the autocorrelation profile.
