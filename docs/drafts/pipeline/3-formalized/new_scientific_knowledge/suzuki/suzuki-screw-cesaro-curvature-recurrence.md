# Suzuki Screw Cesaro Curvature Recurrence

- **ID:** suzuki-screw-cesaro-curvature-recurrence
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper)
- **Source:** Suzuki 2023 screw profile; Suzuki 2026 finite-aperture operator; corpus one-sided Carleman/Stieltjes selector
- **Statement:** Suzuki's initial screw average crosses the central Xi curvature strictly in both directions at arbitrarily large apertures.
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`

## Goal

Prove, without RH, that for every `A0 > 0` there are `A+, A- > A0` such that

```text
(1/A-) integral_0^(A-) g(t)dt < c_Xi
  < (1/A+) integral_0^(A+) g(t)dt,
c_Xi = (XiC''(0)/XiC(0)).re.
```

The left crossing supplies an actual fixed aperture at which the far-negative dyadic shift
selector satisfies the necessary central Herglotz residue sign.  It avoids the corpus ground-edge
Cayley-universality collapse because neither shift approaches the finite-aperture spectral floor.
This is not RH positivity: it is a signed recurrence theorem for the primitive centered at the
mean curvature.

## Gates

- [x] 0 -> 1 in-progress: source-pure exact statement, transform attack, hostile alternatives
- [x] 1 -> 2 fully-proven: complete Landau paper proof, exact normalization and boundary regularity audited
- [x] 2 -> 3 formalized: `xiScrewCesaroMean_cofinallyCrosses_centralCurvature` proved
      unconditionally with the centering constant identified as `(XiC''(0)/XiC(0)).re`;
      module build, axiom audit, and lint pass
- [ ] 3 -> 4 publication-ready: standalone theorem + proof + novelty audit

## Competing hypotheses

- **C1 (target):** the centered primitive changes sign cofinally in both directions.
- **C2:** the primitive is eventually one-signed under RH because infinitely many real frequencies
  can conspire despite zero Bohr mean.
- **C3:** off-line zeros create a dominant exponential layer with fixed eventual sign.
- **C4:** the Laplace transform has an uncancelled singularity at the real convergence abscissa,
  so Landau gives no contradiction.

## Theorem [PROVED HERE]

Let `Psi` be Suzuki's screw profile, `g=-Psi`, and

```text
c_Xi = (XiC''(0)/XiC(0)).re.
```

Then both strict inequalities

```text
(1/A) integral_0^A g(t)dt < c_Xi,
(1/A) integral_0^A g(t)dt > c_Xi
```

hold for arbitrarily large positive `A`.

Equivalently, the curvature-centered primitive

```text
h(A)=integral_0^A(g(t)-c_Xi)dt
```

changes sign cofinally in both directions.

## Proof

### 1. Exact divisor normalization

Let `gamma` range over the zeros of `xi(1/2-iz)`, with analytic multiplicity.  Suzuki's
unconditional expansion is

```text
Psi(t)=sum_gamma (1-cos(gamma t))/gamma^2.               (1)
```

The centered Hadamard product for `XiC(z)=xi(1/2+iz)` gives

```text
c_Xi=-sum_gamma 1/gamma^2.                               (2)
```

Both sums are multiplicity-exact and the reciprocal-square sum is absolutely convergent.  Since
`g=-Psi`, equations `(1)`--`(2)` give

```text
g(t)-c_Xi=sum_gamma cos(gamma t)/gamma^2.                (3)
```

The centered divisor stays a positive distance from zero and its reciprocal squares are
summable, so its reciprocal cubes are summable.  On every compact `t`-interval,
`|sin(gamma t)| <= exp(|Im gamma| |t|)` gives normal convergence.  Termwise integration in `(3)`
therefore yields

```text
h(A)=sum_gamma sin(gamma A)/gamma^3.                     (4)
```

This checks the decisive sign: `h(A)<0` is exactly the desired average-below-curvature event.

### 2. Exact Laplace continuation

Put

```text
F(s)=xi(1/2+s),
delta=sup_gamma |Im gamma|,       0<=delta<=1/2.
```

Suzuki's one-sided transform, evaluated at `z=is`, is

```text
integral_0^infinity Psi(t)e^(-st)dt
  =(1/s^2) F'(s)/F(s),                 Re s>1/2.         (5)
```

Integrating the definition of `h` once gives

```text
H(s):=integral_0^infinity h(A)e^(-sA)dA
 =-F'(s)/(s^3 F(s))-c_Xi/s^2
 =sum_gamma 1/(gamma^2(s^2+gamma^2)).                   (6)
```

The last equality also follows directly from `(4)`.  Thus `(6)` is a meromorphic continuation
of `H`; its poles are precisely `s=+-i gamma`.  They are genuine: the logarithmic derivative has
residue equal to the positive zero multiplicity, and no `gamma` is zero.

At `s=0`, the displayed singularity is removable.  Indeed `F` is even, `F(0)!=0`, and
the central Xi curvature ratio is real (XiC is real on the real axis), so

```text
(F'/F)'(0)=F''(0)/F(0)=-c_Xi.
```

Hence the odd analytic function `F'/F+c_Xi s` vanishes to order at least three, and

```text
H(s)=-(F'(s)/F(s)+c_Xi s)/s^3                         (7)
```

extends holomorphically through zero.

### 3. Exact convergence abscissa under either one-sign hypothesis

From `(4)` and reciprocal-cube summability,

```text
|h(A)| <= C exp(delta A),       A>=0.                   (8)
```

Suppose first that `h` is eventually nonnegative.  Choose `T` beyond its last negative point and
set `h_T(u)=h(T+u)`.  Its Laplace transform is

```text
H_T(s)=e^(sT)[H(s)-integral_0^T h(u)e^(-su)du].         (9)
```

The compact integral is entire, so `(9)` has exactly the same genuine divisor poles as `(6)`.
Bound `(8)` puts its convergence abscissa `sigma_c` at most `delta`.  It cannot be smaller.  If
`sigma_c<delta`, the definition of the supremum supplies a zero whose corresponding right-hand
pole has real part strictly greater than `sigma_c`; the nonnegative Laplace integral would be
holomorphic there, contradicting `(9)`.  This also covers `delta=0`: any divisor pole on the
imaginary axis lies strictly to the right of a hypothetical negative abscissa.  Therefore

```text
sigma_c=delta.                                           (10)
```

No attainment of `delta` is used.

### 4. Missing real boundary singularity

The function `F(delta)=xi(1/2+delta)` is nonzero.  For `0<=delta<1/2`, this is the standard
zero-free real interval; for `delta=1/2`, the completed value at `1` is nonzero.  If `delta>0`,
formula `(6)` is consequently holomorphic near the real point `delta`.  If `delta=0`, the
removable-singularity argument `(7)` says the same.  Divisor poles of unbounded height cannot
accumulate in a bounded neighborhood, and the Xi divisor is discrete.  Thus `(9)` is holomorphic
near its real convergence boundary `sigma_c=delta`.

Landau's boundary theorem for a nonnegative Laplace carrier says its transform must be singular at
its finite real convergence abscissa.  This contradicts the preceding paragraph.  Hence `h` is
not eventually nonnegative.

Apply the identical argument to `-h`.  Its transform is `-H`, with the same abscissa, poles, and
real-boundary regularity.  Thus `h` is not eventually nonpositive either.  Since `h` is continuous,
for every `A0` there are `A-,A+>A0` with

```text
h(A-)<0<h(A+).                                           (11)
```

Dividing by the positive apertures proves both asserted average crossings.  QED.

## Fixed-aperture Carleman corollary [PROVED HERE]

Choose one `A=2a` from the negative side of `(11)` and let

```text
ell_a=(1/(2a)) integral_0^(2a) g(t)dt<c_Xi.             (12)
```

For the normalized Euler--Gamma edge jet `q_a(lambda)`, the corpus source theorem gives

```text
q_a(lambda)->ell_a,              lambda->-infinity.
```

Therefore its dyadic affine intercept satisfies

```text
2q_a(-L)-q_a(-2L)->ell_a<c_Xi.                           (13)
```

So every sufficiently large finite `L` supplies two actual admissible negative shifts whose
central sewn source flux has the required strict Herglotz residue sign.

**Formalized**, in `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiLargeNegativeShiftCentralFlux.lean`
rather than in this card's own module: `suzukiDyadicNegativeShiftIntercept` is the intercept,
`tendsto_suzukiDyadicNegativeShiftIntercept_atTop` is `(13)`'s limit, and
`eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept` is the strict-sign conclusion.  Unlike the ground-edge
selector, `(13)` stays away from the spectral floor and does not trigger Cayley universality.

## Remaining RH frontier after this theorem

Central residue sign and shift existence are no longer open.  Actual unsolved theorem is:

```text
at one fixed aperture satisfying (12), select a sufficiently negative finite dyadic pair
 -> prove the full normalized Euler--Gamma jump quotient is Herglotz on C_+
 -> its nonreal Xi poles are impossible
 -> RH.
```

This is strictly stronger than checking the central residue.  It requires a full-frequency
prime--Gamma Gram/Pick law for the selected actual triangles; corpus presently has neither that
law nor a counterexample to it.

## Attack derivation

Let `Psi=-g` be Suzuki's unconditional screw profile and put

```text
h(A) = integral_0^A (g(t)-c_Xi)dt.
```

Suzuki's multiplicity-exact zero expansion and the centered Hadamard identity should give

```text
h(A) = sum_gamma sin(gamma A)/gamma^3,
Lh(s) = sum_gamma 1/(gamma^2 (s^2+gamma^2))
      = -(1/s^3) xi'/xi(1/2+s) - c_Xi/s^2.       (T1)
```

If `delta = sup_gamma |Im gamma|`, reciprocal-cube summability gives exponential type `delta`,
while the genuine poles `s=+-i gamma` force the Laplace abscissa to equal `delta`.  The apparent
singularity at zero in `(T1)` is removable by evenness and the definition of `c_Xi`.  At the real
point `s=delta`, `xi(1/2+delta)` is nonzero for `0 <= delta <= 1/2`, so `(T1)` is holomorphic there.
Landau's theorem contradicts either eventual nonnegativity of `h` or of `-h`, proving cofinal
two-sided crossings.  Sections 1--4 above close every dependency in this outline.

## Hostile tests

- Check all signs against Suzuki's convention `g=-Psi` and corpus `c_Xi<0`.
- Treat `delta=0` separately: convergence abscissa must still be exactly zero, forced by genuine
  imaginary-axis poles, and cancellation at `s=0` must be explicit.
- Do not assume supremum `delta` is attained; use poles with real parts cofinal below `delta`.
- Prove no pole cancellation: logarithmic-derivative residue is multiplicity and `gamma != 0`.
- Tail shift needed for “eventually”: subtracting a compact initial integral changes the transform
  by an entire function and cannot remove a boundary pole/regularity contradiction.
- Verify paper/literature has no existing Cesaro-crossing theorem; Suzuki only discusses pointwise
  liminf under RH plus simplicity and rational independence.
- Central sign is only one connector.  Full Euler--Gamma jump Pick positivity remains open.

## Novelty boundary

Inputs are classical/Suzuki: exact screw zero expansion, one-sided transform, zero strip,
reciprocal-square convergence, and Landau's theorem.  Claimed new content is their application to
the curvature-centered primitive, yielding unconditional cofinal crossings and a non-ground-edge
fixed-aperture selector for the Carleman program.

Primary-source audit:

- [Suzuki 2023](https://arxiv.org/abs/2206.03682), Theorem 1.1, supplies `(1)` and `(5)` and uses
  the same classical nonnegative-Laplace boundary theorem for pointwise screw positivity.
- Suzuki 2023 discusses pointwise `liminf Psi` only under RH, simplicity, and rational independence;
  it does not state curvature-centered Cesaro recurrence.
- [Suzuki 2026](https://arxiv.org/abs/2606.09096) supplies the finite-aperture operator setting but
  no screw-average crossing theorem.
- Targeted searches for screw-function Cesaro/mean crossings found no parent statement.

Priority remains **unverified**, not claimed as literature-certified novelty.

## Lean status

- **Formal modules:**
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCesaroCurvatureRecurrence.lean` (consumer layers);
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiScrewCesaroLandauRecurrence.lean` (analytic core).

### The analytic core is closed

Sections 3--4 of the proof -- the exact convergence abscissa and the missing real boundary
singularity, i.e. the Landau half -- are now formalized unconditionally.  They arrive as the
constant-weight case of the universal wave-trace recurrence built for
`suzuki-zero-trace-cofinal-convex-recurrence.md`.

- `xiCopyWaveSpectrum` : the Xi zero ordinates **counted with analytic multiplicity** as an
  admissible wave spectrum.  Conjugation stability is `xiSpectralPoint_lineConj` (critical-line
  reflection is ordinary conjugation in centered coordinates); the reciprocal-square condition
  is the corpus's multiplicity-copy summability `xiSpectralPoint_inv_sq_summable`; the lower
  modulus bound, horizontal width `1/2`, local finiteness, absence of a purely imaginary
  ordinate and infinitude of the distinct squares all factor through the support spectrum.
- `xiCopyWaveSpectrum_waveTrace_one` : the constant weight `P = 1` gives exactly
  `∑_gamma sin (gamma A) / gamma ^ 3`, which is equation `(4)`.
- `xiScrewPrimitive_cofinal_sign_change` : **no hypotheses.**  For every aperture bound there
  are strictly larger apertures at which that primitive is negative and at which it is
  positive.  This is `(11)`.

The three hostile tests that bear on this half are discharged structurally rather than by
hand: `delta = 0` needs no separate treatment because the abscissa march never inspects the
supremum; no attainment of `delta` is used, since the pole-free strip comes from a uniform
real-part gap; and pole cancellation is impossible because the coefficient of a resolvent term
depends on the frequency only through its square, so every frequency of a common square fibre
contributes the identical term.

### Section 1 and the crossing theorem are closed

- `xiScrewCurvature` : the centered curvature constant in its divisor form
  `-Re sum 1/gamma^2`, equation `(2)`.
- `xiScrewDivisorTerm_eq`, `xiScrewDivisor_eq` : the corpus screw summand
  `(cosh (t i gamma) - 1)/(i gamma)^2` is literally `1/gamma^2 - cos (gamma t)/gamma^2`, so the
  screw divisor splits as `sum 1/gamma^2 - sum cos(gamma t)/gamma^2`.  This is Suzuki's
  expansion `(1)`.
- `xiSuzukiScrewProfile_sub_curvature` : hence `g(t) - c_Xi = Re sum cos(gamma t)/gamma^2`,
  equation `(3)`.
- `integral_xiScrewCosTerm`, `summable_integral_norm_xiScrewCosTerm`,
  `suzukiCurvatureCenteredPrimitive_eq_realWaveTrace` : termwise integration on `[0,A]` gives
  `h(A) = sum sin(gamma A)/gamma^3`, equation `(4)`, identified with the constant-weight wave
  trace.
- `continuous_xiScrewCosSum`, `continuous_xiSuzukiScrewProfile` : the interval integrability the
  Cesaro bridge needs.
- `xiScrewCesaroMean_cofinallyCrosses` : **the card's theorem.**
  `CofinallyCrosses (suzukiScrewCesaroMean xiSuzukiScrewProfile) xiScrewCurvature` -- the initial
  screw average crosses the central Xi curvature strictly in both directions at arbitrarily large
  apertures.  No hypotheses.

### The centering constant is the central Xi curvature

Equation `(2)` is now proved, so the theorem holds with the constant named exactly as the card
names it.

- `xiSquareResolventSum`, `continuousAt_xiSquareResolventSum_zero`,
  `xiSquareResolventSum_zero` : the paired reciprocal-square resolvent sum is continuous at the
  origin, where it equals `sum 1/gamma^2`.  Continuity is all that is needed -- the corpus's
  paired identity already exhibits the relative resolvent trace as `-z` times this sum, so the
  derivative at the origin is a *slope* limit, not a differentiation under the sum.
- `hasDerivAt_logDeriv_canonical_zero` : hence
  `(logDeriv P)'(0) = -sum 1/gamma^2`, using the corpus identities
  `logDeriv_xiCanonicalProduct_eq_relativeResolventTrace` and
  `xiRelativeResolventTrace_eq_reciprocalSquareResolvent`.
- `deriv_xiCanonicalProduct_zero`, `secondDeriv_xiCanonicalProduct_zero` : `P'(0) = 0` and
  therefore `P''(0) = -sum 1/gamma^2`.
- `xiScrewCurvature_eq_central_curvature` : with the unconditional Hadamard product
  `XiC_eq_constant_mul_canonicalProduct`, `XiC''(0)/XiC(0) = P''(0)`, so
  `xiScrewCurvature = (XiC''(0)/XiC(0)).re`.
- `xiScrewCesaroMean_cofinallyCrosses_centralCurvature` : **the card's theorem verbatim.**
  `CofinallyCrosses (suzukiScrewCesaroMean xiSuzukiScrewProfile) ((XiC''(0)/XiC(0)).re)`.
  No hypotheses.

## Log

- 2026-07-22 — created in 1-in-progress after corpus and primary-source audit; C1 selected for proof.
- 2026-07-22 — C2--C4 killed; exact two-sided recurrence and fixed-aperture dyadic corollary proved.
- 2026-07-22 — added axiom-clean Lean consumer layer and continuous Landau contrapositive in
  `SuzukiScrewCesaroCurvatureRecurrence`; analytic Xi recurrence remains paper-proved, not claimed
  formally closed.
