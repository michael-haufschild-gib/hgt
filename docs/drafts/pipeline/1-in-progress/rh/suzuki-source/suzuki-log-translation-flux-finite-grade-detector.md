# Suzuki logarithmic translation flux and finite-grade detector

- **ID:** `suzuki-log-translation-flux-finite-grade-detector`
- **Stage:** 1 — in progress
- **Type:** THEOREM (paper) + THEOREM (Lean) + CONJECTURE
- **Scientific status:** `[PAPER-PROVED LOCAL THEOREM] [LEAN-PROVED FINITE DETECTOR]`
  `[SOURCE-SPECIFIC CONJECTURE] [NOVELTY UNVERIFIED] [NOT RH]`
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 2--4 and 8
- **Analytic sources:** S. M. Djitte, M. M. Fall, and T. Weth,
  *A fractional Hadamard formula and applications*, arXiv:2002.07719;
  S. M. Djitte and F. Sueur, *Pointwise Hadamard variational formula for the fractional
  Laplacian*, arXiv:2602.07214
- **Statement:** Critical renormalized translation energy extracts every one-sided inverse-log
  coefficient exactly.  Since Suzuki's completion-safe square-Evans packet is finite-dimensional,
  joint separation by all log grades automatically collapses to a finite grade cutoff.  Full
  convergence of the countable seam state is therefore not needed for kernel exclusion.

> **2026-07-22 scope correction.** `suzuki-corona-regular-two-scale-boundary-law.md` proves that
> inverse-log grades do not jointly separate the whole packet: a nonzero power-scale `H1` solution
> and an intermediate inverse-log-flat non-`H1` solution evade all grades. The theorem here remains
> valid conditionally and applies to any already separated **corona quotient**. Finite-dimensional
> compression never supplies its own separation premise.

## Goal and actual RH frontier

The corpus reduces RH to

```text
ker A_a={0} for every a>0,
```

or equivalently nonvanishing of the completion-safe square-Evans section `det N_(a,0)` at every
aperture.  Suzuki's Section 8 does not place the derivative variable in raw `L2`; a first zero mode
may live in the completion corona.  Existing work derives the critical endpoint germ

```text
u(a-r)=beta_+(u)(log(1/r))^(-1/2)+lower inverse-log orders
```

and prime propagation raises the exponent by one at every seam.  Two questions remained mixed:

1. how to observe a half-log or higher-grade coefficient in a Hilbert metric;
2. whether one must construct a convergent infinite dense-seam state before proving no-return.

The first is solved below for every finite log-conormal packet.  The second is answered negatively:
finite-dimensionality of the square-Evans source means arbitrary finite-order residual identities
plus joint infinite-order separation already imply one finite certificate. The later hostile test
shows that the required separation is false on the whole reconstructed packet. The live analytic
core is now a **source-specific no-intermediate-scale theorem** identifying the zero-corona-trace
sector with `H1_0`, followed by finite-grade no-return on the corona quotient and raw Evans
injectivity on the regular sector. Countable graded summability is not a prerequisite for the
corona half of kernel exclusion.

## 1. Critical one-sided translation-flux theorem

Let `alpha>0`, `c in C`, and choose `epsilon<1`.  Let `chi` be a `C^1` cutoff on the positive
half-line, supported in `[0,epsilon)` and equal to one near zero.  Extend by zero to the line the
one-sided germ

```text
f_(alpha,c)(x)=c chi(x)(log(1/x))^(-alpha),  x>0.       (1)
```

Write `(tau_h f)(x)=f(x-h)` and `L_h=log(1/h)`.

`[PROVED HERE]` The exact critical translation flux is

```text
lim_(h downarrow 0) L_h^(2 alpha)/h * ||tau_h f-f||_2^2 = |c|^2.  (2)
```

Thus the ordinary translation derivative does not exist when the germ is present, but its unique
critical renormalization recovers the squared one-sided coefficient.

### Proof

The newly exposed strip is exact:

```text
I_0(h)=integral_0^h |f(x)|^2 dx.
```

With `x=ht`,

```text
L_h^(2 alpha) I_0(h)/h
 =|c|^2 integral_0^1
   (1+log(1/t)/L_h)^(-2 alpha) dt -> |c|^2             (3)
```

by dominated convergence.

On the near-overlap strip `h<x<2h`, put `x=h(1+t)`.  After multiplication by
`L_h^alpha`, the two logarithmic profiles converge pointwise to the same value one.  They are
uniformly bounded for small `h`, so dominated convergence gives

```text
integral_h^(2h)|f(x-h)-f(x)|^2 dx=o(h L_h^(-2 alpha)). (4)
```

For `2h<x<epsilon_0`, where the cutoff is one, the mean-value theorem gives

```text
|f(x-h)-f(x)|
 <=C_alpha h/[x(log(1/x))^(alpha+1)].                  (5)
```

Split at `sqrt(h)`.  On `(2h,sqrt(h))`, `log(1/x)>=L_h/2`, and on
`(sqrt(h),epsilon_0)` the factor `h^2/x^2` is integrable with total `O(h^(3/2))`.
Consequently the square integral in `(5)` is

```text
O(h L_h^(-2 alpha-2))+O(h^(3/2))
 =o(h L_h^(-2 alpha)).                                  (6)
```

The cutoff region lies away from zero and is `H^1`; its translation difference is `O(h^2)` in
squared `L2`, also negligible after the normalization in `(2)`.  Equations `(3)`--`(6)` prove
`(2)`. `QED`

## 2. Endpoint, seam, and collision laws

For a zero-extended interval function having endpoint expansions

```text
u(a-r)=beta_+ L^(-alpha)+o_controlled(L^(-alpha)),
u(-a+r)=beta_- L^(-alpha)+o_controlled(L^(-alpha)),     (7)
```

with an `H^1` remainder away from the two endpoints and the derivative control used in `(5)`, the
two exposed strips are disjoint.  Applying `(2)` at both ends gives

```text
lim_(h downarrow 0) L_h^(2 alpha)/h * ||tau_h u-u||_2^2
 =|beta_+|^2+|beta_-|^2.                                (8)
```

At Suzuki grade `k`, `alpha=k+1/2`, hence

```text
Flux_k(u)
 :=lim_(h downarrow 0) L_h^(2k+1)/h * ||tau_h u-u||_2^2 (9)
```

recovers the squared grade-`k` coefficient after lower grades are removed.  A finite family of
separated oriented seams contributes the sum of coefficient squares.

At a collision point with left and right germs `c_- L^(-alpha)` and `c_+ L^(-alpha)`, the
unlocalized strip crosses the seam and records

```text
|c_+-c_-|^2,                                             (10)
```

not their separate masses.  Multiplying by smooth one-sided cutoffs before taking `(2)` recovers
`|c_-|^2` and `|c_+|^2` separately.  This is the metric counterpart of the already proved
opposite-orientation collision law.  Same-end collisions are first classified by the formalized
prime-valuation coordinate, then localized by orientation.

For the critical endpoint exponent `alpha=1/2`, `(8)` becomes

```text
lim_(h downarrow 0) log(1/h)/h * ||tau_h u-u||_2^2
 =|beta_+|^2+|beta_-|^2.                                (11)
```

This is a positive trace metric on the completion corona.  It is not an ordinary Sobolev normal
derivative: indeed `||tau_hu-u||_2/h` diverges like
`h^(-1/2)log(1/h)^(-alpha)` when a coefficient is nonzero.

## 3. Finite-grade compression of the infinite hierarchy

Let `F_a` be the finite-dimensional characteristic packet in the square-Evans reduction.  Any
finite-order endpoint/seam construction gives scalar linear residual coordinates

```text
ell_i:F_a -> C,  i in I.                                (12)
```

Here `I` may include grade, prime-valuation location, orientation, parity, and a coordinate in a
finite-dimensional residual target.

`[PROVED; LEAN]` If the full family is jointly separating,

```text
intersection_(i in I) ker ell_i={0},                    (13)
```

then there are at most `dim F_a` indices `i_1,...,i_m` such that

```text
intersection_(j=1)^m ker ell_(i_j)={0}.                 (14)
```

If coordinates are enumerated by natural log grade, there exists one `N_a<infinity` such that
vanishing of all coordinates through grade `N_a` forces the characteristic packet to vanish.

### Proof

Condition `(13)` says the span of the functionals `ell_i` is the full algebraic dual `F_a^*`.
Because `F_a^*` has dimension `dim F_a`, that span has a basis consisting of at most `dim F_a`
members selected from the family.  Their common kernel is zero, proving `(14)`.  For a natural
hierarchy, take `N_a` larger than every selected grade. `QED`

Lean proves the theorem without an assumed basis in

```text
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFiniteGradeTraceDetector.lean
```

as `exists_finite_trace_detector` and `exists_finite_grade_trace_cutoff`.

### Strategic consequence

The earlier program required construction and convergence of a countable dense-seam state before
kernel exclusion.  That is stronger than necessary.  It suffices to prove:

```text
for every finite N:
  exact endpoint/seam expansion and residual recursion exist through grade N;

corona separation:
  a corona class flat in every residual grade is zero.                       (15)
```

Then `(14)` supplies an aperture-dependent finite `N_a` for the corona proof. No interchange of an
infinite seam sum, no global enumeration of the dense orbit, and no convergence of a completed
transport series enters this implication. Dense seam geometry remains relevant to proving `(15)`,
but not as an analytic summation obligation. A packet with zero corona class is not forced to be
zero; it must instead be lifted to `H1_0` and tested by the raw Evans map.

## 4. Fractional-to-logarithmic Hadamard bridge

Suzuki's exact form has principal Fourier multiplier `log|xi|` and an exact locally bounded
polar--prime--Gamma remainder.  Write on compactly supported functions

```text
A=L_0+B,
widehat(L_0 f)(xi)=log|xi| hat f(xi).                    (16)
```

The source-faithful small-order regularization changes only the universal principal block:

```text
L_s=((−Delta)^s-I)/(2s),
A_(a,s)=zero-exterior compression of (L_s+B) to (-a,a). (17)
```

For fixed `s>0`, fractional Hadamard formulas identify domain derivatives with the squared
fractional trace `q_s=u_s/delta^s`.  The normalization in `(17)` predicts a finite limit only if
`q_s` is of order `sqrt(s)`, exactly the scale obtained by matching `delta^s=exp(-sL)` to the
outer half-log layer at `L` of order `1/s`.

### `SUZUKI-FRACTIONAL-LOG-HADAMARD-BRIDGE` `[CONJECTURE]`

For every isolated finite-multiplicity eigencluster of `A_a`:

1. `A_(a,s)` converges in norm resolvent to `A_a` as `s downarrow 0` on a neighborhood of the
   cluster;
2. eigenvectors admit a universal boundary-layer profile and

   ```text
   q_(s,+)/sqrt(s) -> C_log beta_+,
   q_(s,-)/sqrt(s) -> C_log beta_-,                    (18)
   ```

   for one source-independent `C_log>0` fixed by the normalization in `(16)`;
3. the exact polar--prime--Gamma remainder has no leading boundary-creation term under the
   zero-exterior shape variation;
4. the aperture crossing form on a zero eigenspace is

   ```text
   H_cross(v,w)
    =-(C_log^2/2)
      [beta_+(v)conj(beta_+(w))+beta_-(v)conj(beta_-(w))]. (19)
   ```

The factor `1/2` is forced by `(17)` and the fractional Hadamard coefficient
`Gamma(1+s)^2/(2s)`.  A different normalization of the principal log multiplier changes
`C_log`, not definiteness of `(19)`.

This bridge would turn `(11)` from a metric coefficient extractor into the exact first-crossing
form.  Higher-grade versions should recover the first nonzero flat descendant using the scale in
`(9)`.

### Hostile direction check

Formula `(19)` alone does **not** prove RH.  It gives a negative crossing velocity when the trace
is nonzero, which is compatible with the first crossing forced by false RH.  Its value is sharper:

- it would prove transversality and multiplicity from an explicit boundary Gram;
- it would turn any failure of trace separation into an infinitely log-flat packet;
- together with `(14)`, a proof that exact prime--Gamma transport residuals jointly separate the
  corona quotient would immediately collapse that half of the obstruction to a finite certificate.

The RH-bearing statement remains source-specific finite-grade no-return, not generic Hadamard
monotonicity.

## 5. Primary-literature audit and falsifiers

Djitte--Fall--Weth prove the fractional eigenvalue Hadamard formula with boundary trace
`u/delta^s` and coefficient `Gamma(1+s)^2`.  Djitte--Sueur prove the corresponding 2026 pointwise
Green/resolvent shape formula.  A targeted arXiv audit found no logarithmic-Laplacian Hadamard or
boundary-trace formula.  The one arXiv item advertising a logarithmic Pohozaev identity,
arXiv:2411.15985, is withdrawn by its authors because of a crucial error in that proof.  Therefore
`(18)`--`(19)` must be proved from the small-order boundary layer; it cannot be imported.

Kill or revise the bridge if any of the following occurs:

1. the matched trace has scale different from `sqrt(s)`;
2. `B` contributes a nonzero leading shape term at order one;
3. the boundary-layer constant depends on the eigenvector or aperture;
4. norm-resolvent convergence fails on the source-faithful regularization;
5. a nonzero corona class is flat in every exact finite-grade residual coordinate.

The decisive scientific tests are:

1. prove `(18)` first for the pure logarithmic Dirichlet operator on an interval;
2. prove stability under the exact finite-aperture Suzuki remainder, retaining all visible
   `Lambda(n)/sqrt(n)` shifts and the polar--Gamma kernel;
3. derive arbitrary finite-order endpoint/seam recursions without assuming convergence of an
   infinite series;
4. prove zero corona trace implies an `H1_0` regular lift, excluding intermediate flat scales;
5. prove joint separation on the corona quotient and apply the Lean finite-detector theorem;
6. prove raw Evans injectivity on the complementary `H1_0` sector.

## Gates

- [x] actual completed-kernel frontier retained
- [x] critical one-sided translation flux proved
- [x] two-endpoint half-log trace metric proved under explicit remainder control
- [x] graded oriented seam extractor identified
- [x] collision difference and one-sided localization law proved
- [x] infinite separating hierarchy collapsed to at most `dim F_a` coordinates
- [x] natural hierarchy collapsed to one finite grade cutoff
- [x] finite detector formalized unconditionally in Lean
- [x] countable seam convergence removed as a necessary kernel-exclusion gate
- [x] fractional Hadamard and current source literature audited
- [x] whole-packet log-quasianalytic separation falsified; finite detector restricted to corona
- [ ] prove arbitrary finite-order exact Suzuki boundary/seam expansion
- [ ] prove source-faithful small-order norm-resolvent convergence
- [ ] prove `q_s/sqrt(s) -> C_log beta`
- [ ] prove logarithmic Hadamard crossing form `(19)`
- [ ] prove zero-corona-trace `H1_0` lift and exclude intermediate flat scales
- [ ] prove joint separation of exact residual coordinates on the corona quotient
- [ ] extract finite `N_a` and prove finite-grade corona no-return for every aperture
- [ ] prove raw Evans Gram positivity for every aperture
- [ ] `det N_(a,0)!=0` for every aperture
- [ ] RH

## Log

- 2026-07-22 — Proved critical translation-flux coefficient extractor; proved and formalized
  finite-grade compression; replaced countable graded-summation gate by arbitrary finite-order
  expansion plus log-quasianalytic separation; opened source-faithful fractional/log Hadamard test.
