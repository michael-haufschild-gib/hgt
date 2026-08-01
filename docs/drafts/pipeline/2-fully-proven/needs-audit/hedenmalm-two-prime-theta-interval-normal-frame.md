# Two prime theta-interval anomalies generate the complete Xi normal module

- **ID:** `hedenmalm-two-prime-theta-interval-normal-frame`
- **Stage:** 2-fully-proven / needs literature and Lean audit
- **Type:** THEOREM / SOURCE-NORMAL PRIME FRAME / ESSENTIAL COMPACT-BOUNDARY SYMBOL
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  `hedenmalm-prime-translation-rank-one-anomaly.md`;
  `hedenmalm-theta-source-compressed-inverse-determinant.md`;
  `../../1-in-progress/perspective-neutral-prime-clock-rigging.md`;
  `../../4-publication-ready/riemann-source-modular-superselection/main.tex`.

## Question closed

The updated source-modular synthesis separates a scalar Xi conormal from the independent
prime-labelled normal frame required by a genuine boundary consumer.  The Hedenmalm translation
commutator gives such a frame after taking the source-normal class, but not before it.

Let `k` be the positive even Hedenmalm theta source, normalized by

\[
 \widehat k(z)=\Xi_C(z),
 \qquad
 \widehat f(z)=\int_{\mathbb R}f(x)e^{izx}\,dx.
 \tag{1}
\]

Use the exponential source core, the compact-source inverse `B`, the normalized integer shifts

\[
 (T_nf)(x)=n^{-1/2}f(x+\log n),
 \tag{2}
\]

and the rank-one anomaly vectors

\[
 r_n=V(T_nk-n^{-1/2}k),
 \qquad
 (Vg)(x)=i\int_{-\infty}^xg(y)\,dy.
 \tag{3}
\]

## Theorem

### 1. Exact interval transgression and divisor factorization

Put `L_n=log n`.  Direct integration gives

\[
 r_n(x)=i n^{-1/2}\int_x^{x+L_n}k(t)\,dt.
 \tag{4}
\]

Consequently

\[
 \widehat r_n(z)
 =q_n(z)\Xi_C(z),
 \qquad
 q_n(z)=n^{-1/2}\frac{1-e^{-izL_n}}{z},
 \tag{5}
\]

where the apparent singularity at zero is removable.  Thus the nonzero core commutator anomaly is
zero in the analytic divisor cokernel `O(C)/XiC O(C)`.  It is a source coboundary, not an extension
class on the divisor fibre.

The anomaly satisfies the exact multiplicative Wess--Zumino law

\[
 r_{mn}=n^{-1/2}r_m+T_mr_n,
 \qquad
 q_{mn}(z)=n^{-1/2}q_m(z)+m^{-1/2-iz}q_n(z).
 \tag{5a}
\]

This follows either from `[B,T_mT_n]=[B,T_m]T_n+T_m[B,T_n]` or directly from `(5)`.
Thus the finite integer-shift anomaly is a flat, exact monoid cocycle.  Any RH-bearing anomaly must
survive the source-normal all-prime completion; finite cocycle curvature cannot supply it.

Center the interval by defining

\[
 c_n=-iS_{L_n/2}r_n,
 \qquad
 c_n(x)=n^{-1/2}\int_{x-L_n/2}^{x+L_n/2}k(t)\,dt.
 \tag{6}
\]

Then `c_n` is positive, real, even, and rapidly decreasing, and

\[
 \widehat c_n(z)=a_n(z)\Xi_C(z),
 \qquad
 a_n(z)=2n^{-1/2}\frac{\sin(zL_n/2)}{z},
 \qquad
 a_n(0)=n^{-1/2}L_n.
 \tag{7}
\]

The multiplier `a_n` is even and Real:

\[
 a_n(-z)=a_n(z),
 \qquad
 a_n(\overline z)=\overline{a_n(z)}.
 \tag{8}
\]

### 2. Two literal primes frame every normal direction

The entire functions `a_2` and `a_3` have no common zero in `C`.

Indeed, zero is not a zero of either function.  Every other zero of `a_n` is real and satisfies

\[
 z\log n=2\pi k
 \quad\text{for some nonzero }k\in\mathbb Z.
 \tag{9}
\]

A common zero would give nonzero integers `k,l` with

\[
 \frac{\log2}{\log3}=\frac{k}{l},
 \tag{10}
\]

and hence an equality between positive powers of `2` and `3`, contradicting unique factorization.

Let `I=(XiC)` in `O(C)`.  The conormal module is

\[
 I/I^2\simeq \bigl(O(C)/(\Xi_C)\bigr)[\Xi_C].
 \tag{11}
\]

Equations `(7)` and the no-common-zero theorem show that

\[
 [\widehat c_2]=a_2[\Xi_C],
 \qquad
 [\widehat c_3]=a_3[\Xi_C]
 \tag{12}
\]

generate `I/I^2` everywhere.  Equivalently, Cartan's theorem B on `C` gives entire functions
`b_2,b_3` with

\[
 b_2a_2+b_3a_3=1,
 \tag{13}
\]

so

\[
 (\widehat c_2,\widehat c_3)=(\Xi_C)
 \quad\text{as ideals of }O(C).
 \tag{14}
\]

This is a source-defined two-prime resolution before any zero is selected.

### 3. Multiplicity and source-normal nonannihilation

Let `zeta` be a zero of `XiC` of order `m`.  For `0 <= j < m`,

\[
 \widehat c_n^{(j)}(\zeta)=0,
 \tag{15}
\]

while

\[
 \widehat c_n^{(m)}(\zeta)
 =a_n(\zeta)\Xi_C^{(m)}(\zeta).
 \tag{16}
\]

At least one of the values `a_2(zeta),a_3(zeta)` is nonzero.  Hence the pair of first nonzero
normal jets in `(16)` retains every Xi point and its exact analytic multiplicity.  The value-level
anomaly is invisible on the divisor, but its source-normal class is nowhere zero.

This closes the nonvanishing half of the defect-factorization question

```text
source covariance defect = XiC * on-shell normal frame.
```

It does not produce a normal CCR intertwiner or a positive invariant metric.

### 4. Positive-kernel self-adjoint source channels, but no Hilbert spectrum

Convolution by `c_2` and `c_3` defines two bounded self-adjoint operators on ordinary
`L2(R)`, because both kernels are real, even, and integrable.  Their analytic multiplier row has
cokernel

\[
 \operatorname{coker}\left(
  O(C)^2\xrightarrow{(f_2,f_3)\mapsto
    \widehat c_2f_2+\widehat c_3f_3}O(C)
 \right)
 \simeq O(C)/(\Xi_C).
 \tag{17}
\]

Thus two positive-kernel, self-adjoint source channels recover the complete Xi divisor analytically.
The convolution operators themselves are not claimed positive: their real Fourier multipliers can
change sign.
They do **not** realize it as ordinary Hilbert spectrum: on the real Fourier axis their common zero
set has Lebesgue measure zero, so the corresponding reduced `L2` defect is zero.  This is an exact
positive realization of source incidence, not Hedenmalm's missing positive spectral realization.

### 5. Essential singularity in compact reciprocal coordinates

For a Hedenmalm root block, the compact Grushin inverse has eigenvalue

\[
 \mu=-\frac1\zeta.
 \tag{18}
\]

The normal multiplier `(7)` becomes

\[
 A_n(\mu)=a_n(-1/\mu)
 =2n^{-1/2}\mu\sin\left(\frac{L_n}{2\mu}\right).
 \tag{19}
\]

It has an essential singularity at the compact spectral boundary `mu=0`.  Nevertheless, on every
Xi root block,

\[
 A_n(-1/\zeta)=a_n(\zeta),
 \tag{20}
\]

and `(a_2(zeta),a_3(zeta))` is nonzero.  If `f_zeta` is the source-normalized global right mode,
then

\[
 \bigl(A_2(-1/\zeta)f_\zeta,
       A_3(-1/\zeta)f_\zeta\bigr)\ne(0,0).
 \tag{21}
\]

Equation `(21)` is the requested essential-singular, source-pointed, multiplicity-faithful
root-block landing at the algebraic boundary level.  A closed operator with symbol `(19)` on the
whole compact root expansion is not asserted.

## Ordinary-multiplier instability theorem

The analytic frame `(12)` cannot be promoted to a bounded Bezout corona by ordinary bounded
Fourier multipliers on the real axis.  Already

\[
 |a_2(t)|+|a_3(t)|\longrightarrow0
 \quad(|t|\longrightarrow\infty)
 \tag{22}
\]

because the sine factors are bounded.  More sharply, after removing the common first-order decay,

\[
 t a_n(t)=2n^{-1/2}\sin(tL_n/2),
 \tag{23}
\]

there is a sequence `t_j -> infinity` for which both terms in `(23)` tend to zero.  Choose
integers `q_j -> infinity` with `q_j log(3)/log(2)` approaching integers and put
`t_j=2 pi q_j/log(2)`.  Then the prime-2 term is zero and the prime-3 term tends to zero.

Therefore no Bezout pair in `(13)` is jointly bounded on the real axis, and even the
first-normalized two-prime frame has no uniform lower frame bound.  Pointwise conormal
nonannihilation and closed Hilbert descent are genuinely different theorems.

### Finite-versus-Hilbert prime-rank fracture

The instability is not special to the pair `2,3`.  For every prime `p`, put

\[
 b_p(t)=t a_p(t)=2p^{-1/2}\sin(t\log p/2).
 \tag{24}
\]

Let `P` be any finite nonempty set of primes.  Unique factorization makes
`(log p)_(p in P)` linearly independent over `Q`.  Kronecker recurrence therefore gives
arbitrarily large real `t` for which every phase `t log p/2` is simultaneously as close as desired
to an integral multiple of `2 pi`.  Hence

\[
 \liminf_{t\to+\infty}\sum_{p\in P}|b_p(t)|^2=0.
 \tag{25}
\]

More generally, let `omega_p >= 0` and assume

\[
 \sum_p\frac{\omega_p}{p}<\infty.
 \tag{26}
\]

Then

\[
 \boxed{\quad
 \liminf_{t\to+\infty}
 \sum_p\omega_p|b_p(t)|^2=0.
 \quad}
 \tag{27}
\]

To prove `(27)`, first choose a finite prime head so that the uniformly bounded tail
`4 sum omega_p/p` is arbitrarily small.  Apply finite-dimensional Kronecker recurrence to make the
head arbitrarily small simultaneously.  The recurrence times can be taken arbitrarily large.

Thus the Xi normal line has **algebraic prime rank two** but no finite or summably weighted
diagonal **Hilbert frame rank**.  Any uniformly coercive source completion must use at least one of:

1. a nonsummable all-prime weight requiring renormalization;
2. genuinely non-diagonal cross-prime coupling;
3. a singular graph/bornological topology not controlled by an ordinary frame lower bound.

This is the exact finite-to-infinite boundary.  Merely adding a countable `l2` direct sum leaves the
same near-resonance obstruction.

## What this changes

The source-modular paper said that a scalar conormal cannot generate the independent
prime-labelled normal frame required downstream.  Equations `(6)`--`(16)` now construct that frame
from two literal prime translations of the theta source.  They also explain why it was absent in
regular categories:

```text
core commutator anomaly: nonzero but divisor-exact;
source-normal blow-up: two-prime frame is everywhere nonzero;
analytic category: complete Xi cokernel recovered;
ordinary Hilbert category: cokernel disappears;
compact reciprocal chart: frame becomes essential-singular;
bounded corona: fails by high-frequency simultaneous resonance.
```

The missing RH theorem has consequently moved.  It is no longer conormal acquisition or
nonannihilation.  It is a strict completion theorem which makes the essential pair `(19)` a closed
reflection-compatible boundary operator while retaining the unsymmetrized prime phase.  Equations
`(25)`--`(27)` force that completion to be nonsummable/renormalized or genuinely cross-prime.  Any
proof must overcome this rank fracture rather than assume a bounded frame estimate.

The child bridge `prime-log-jump-sonin-mellin-grade-frame.md` makes this compatibility explicit.
It does not close another frontier gate: two-window BV conormal faithfulness and Sonin aperture
grade were already proved elsewhere in the corpus.  The inverse
Fourier transforms of the coefficients `a_p` are literal prime-log windows; a two-prime difference
is a discontinuous annulus packet.  Essential modulation sends that packet to the already
constructed cofinal Sonin partial-unitary face, while its first rescaled Mellin trace is a globally
coprime two-channel entire frame.  Dilation changes the trace by `r^(1/2-s)`.  Thus conormal landing
and the exact critical-line grade are explicit in one theta/Sonin chart.  Remaining open theorem is
continuity of this jump-Mellin normal in the same canonical closed boundary topology as the Hilbert
adjoint, together with the undeconvolved theta-to-Sonin action intertwiner.

## Hostile audit

1. **Not an RH proof.**  A positive Real frame can exist at nonreal divisor points; it does not
   make multiplication by the spectral coordinate symmetric.
2. **No false extension class.**  The raw anomaly is divisible by `XiC` and vanishes in the
   analytic divisor cokernel.  Only its class after deformation to the normal cone is nonzero.
3. **No contradiction with finite-frame no-gos.**  This frame generates the divisor normal line;
   it does not factor the horizontal Xi orientation current into a positive finite local Gram.
4. **No bounded corona.**  Equation `(13)` is analytic, not `H-infinity`, `L2`, or operator-norm
   controlled.
5. **No hidden zero selection.**  `c_2,c_3`, their factorization, and their Bezout ideal are defined
   before evaluating a zero.
6. **No simplicity assumption.**  Equation `(16)` uses the first nonzero jet of arbitrary order.
7. **Divisor-universal normal geometry.**  Multiplying any entire function by the same coprime
   interval frame gives an analogous normal resolution.  Arithmetic force must enter the strict
   all-prime/Gamma completion, not the two-prime frame alone.
8. **Only the ordinary bounded-multiplier route is excluded.**  Equations `(22)`--`(23)` do not
   exclude every singular graph topology; such a topology is exactly the remaining target.
9. **No zero-subsequence inference.**  Equation `(27)` concerns coercivity on the full real
   boundary.  Its recurrence sequence is not asserted to contain Xi zeros.

## Preliminary literature boundary

Hedenmalm constructs the theta differential pencil, its complex zero modes, and the pair
self-adjointness question, but does not state `(4)`--`(21)`:
<https://arxiv.org/abs/2606.17494>.

Interval Fourier transforms, coprime sine zero sets, Cartan--Bezout generation on `O(C)`, and
self-adjoint convolution by real even kernels are classical.  Targeted searches found no primary
source combining them with the Hedenmalm translation commutator, the Xi conormal module, and the
essential compact reciprocal symbol.  Novelty remains unverified and attaches only to that exact
conjunction.

## Gates

- [x] exact rank-one anomaly integrated to a theta interval
- [x] centered positive even prime-window source constructed
- [x] exact `a_n XiC` factorization proved
- [x] exact multiplicative anomaly cocycle proved
- [x] prime-2/prime-3 no-common-zero theorem proved
- [x] global analytic conormal generation proved
- [x] arbitrary multiplicity retained by first nonzero normal jets
- [x] two bounded self-adjoint source channels constructed
- [x] ordinary-`L2` spectral defect shown to vanish
- [x] essential compact-boundary symbol identified
- [x] bounded-corona/high-frequency frame obstruction proved
- [x] arbitrary finite-prime frame obstruction proved
- [x] summably weighted all-prime diagonal frame obstruction proved
- [x] preliminary corpus noncollision audit
- [x] preliminary external noncollision search
- [ ] independent specialist literature audit
- [ ] closed strict boundary realization of `(19)`
- [ ] positive self-adjoint divisor spectrum
- [ ] RH
