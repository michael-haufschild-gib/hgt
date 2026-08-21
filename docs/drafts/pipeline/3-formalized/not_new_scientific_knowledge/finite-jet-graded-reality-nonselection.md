# No finite completed-flux jet selects the symmetry axis

- **ID:** finite-jet-graded-reality-nonselection
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / finite-passport no-go
- **Date:** 2026-07-10
- **Scientific status:** `[NOVELTY UNVERIFIED]` — the quartet-flat construction appears absent from
  the local corpus and survives the parent-theory attack below.  Its proof uses elementary
  entire-function theory and Hermite-flat multiplication, so scientific novelty is not claimed
  without a broad literature audit and independent expert review.
- **Statement:** For every finite jet depth `N`, there is a real even entire function of exact order
  one, with no nonzero period, whose functional-equation normalization has a nonreal off-axis zero
  quartet strictly inside the critical strip and has no real zeros.  At one zero, the
  residue-filled negative-logarithmic-derivative germs based at its functional-equation and Schwarz
  partners have identical Taylor coefficients through order `N` but are not equal as germs.
  Consequently FE symmetry, Schwarz reality, critical-strip location, absence of real zeros,
  order-one growth, and aperiodicity cannot turn any fixed finite completed-flux jet into a
  critical-axis selector.

## Why this is the correct attack

`CompletedFluxGradedReality.lean` proves that the complete coefficient sequence detects the
critical line.  That leaves open a dangerous simplification: perhaps a universal finite depth
suffices once the elementary global features of `xi` are imposed.  The theorem below rules this
out constructively, including the known fact that the actual nontrivial zeros are not real.  The
missing selector must use a genuinely global Euler constraint, not a fixed finite passport guarded
only by the standard entire-function envelope.

## Construction

Fix `N` and put

\[
a=b=\frac14,\qquad
\alpha=a+ib=\frac{1+i}{4},\qquad
\lambda=\frac{\pi}{2b}=2\pi,\qquad
M=2N+1.
\]

Define

\[
B(z)=\cosh(\lambda(z-a))\cosh(\lambda(z+a)),
\]

\[
Q(z)=(z^2-\alpha^2)(z^2-\bar\alpha^2),\qquad
P_M(z)=1+Q(z)^M,\qquad
F_M(z)=B(z)P_M(z).
\]

Both `B` and `P_M` are real even entire functions.  The four points

\[
\alpha,\quad -\alpha,\quad \bar\alpha,\quad -\bar\alpha
\]

are simple zeros of `B`: at each point exactly one shifted `cosh` factor has argument congruent
to \(\pi i/2\) modulo \(\pi i\), while the other factor is nonzero.  Since `Q` vanishes at all four
points and `P_M=1` there, they remain simple zeros of `F_M`.

The base factor has the exact imaginary period

\[
B(z+2ib)=B(z).
\]

In particular, the two centers

\[
c=-\alpha,\qquad d=-\bar\alpha=c+2ib
\]

have identical residue-filled logarithmic-flux germs for `B`.

## Exact delayed partner defect

For a simple zero `w` of an entire function `F`, write

\[
G_w^F(x)=
\begin{cases}
-1,&x=0,\\[2mm]
-x\dfrac{F'(w+x)}{F(w+x)},&x\ne0.
\end{cases}
\]

The multiplier contribution at a quartet point `w` is

\[
C_w(x)=-x\frac{P_M'(w+x)}{P_M(w+x)}.
\]

If \(q_w=Q'(w)\), then \(Q(w+x)=q_wx+O(x^2)\), and hence

\[
C_w(x)=-M q_w^M x^M+O(x^{M+1}).                              \tag{1}
\]

Thus every multiplier correction vanishes to exact order `M`.  At the two partner centers,
putting \(\Delta=\alpha^2-\bar\alpha^2\ne0\), direct differentiation gives

\[
q_c=-2\alpha\Delta,\qquad q_d=2\bar\alpha\Delta.
\]

Because `M` is odd,

\[
q_c^M-q_d^M
=-(2\Delta)^M(\alpha^M+\bar\alpha^M).                         \tag{2}
\]

The argument of \(\alpha\) is \(\pi/4\).  For every odd `M`,
\(\cos(M\pi/4)=\pm\sqrt2/2\), so

\[
\alpha^M+\bar\alpha^M=2\operatorname{Re}(\alpha^M)\ne0.
\]

Equations (1)--(2), together with the exact equality of the two base germs, yield

\[
[x^n]G_c^{F_M}=[x^n]G_d^{F_M}\quad(0\le n<M),
\qquad
[x^M]G_c^{F_M}\ne[x^M]G_d^{F_M}.                             \tag{3}
\]

Since `M=2N+1>N`, the partner germs agree through the prescribed depth and disagree at a later odd
order.

## Functional-equation normalization and the zero-free real axis

Put

\[
X_M(s)=F_M\!\left(-i\left(s-\tfrac12\right)\right).
\]

Real even symmetry becomes

\[
X_M(1-s)=X_M(s),\qquad X_M(\bar s)=\overline{X_M(s)}.
\]

The quartet above becomes

\[
\frac14+\frac{i}{4},\quad
\frac34-\frac{i}{4},\quad
\frac14-\frac{i}{4},\quad
\frac34+\frac{i}{4}.
\]

All four points lie strictly inside \(0<\operatorname{Re}s<1\), and none is on the critical line or
the real axis.  For the selected zero \(\rho=1/4+i/4\), the FE partner \(1-\rho\) maps to
\(c=-\alpha\), and the Schwarz partner \(\bar\rho\) maps to \(d=-\bar\alpha\).  The affine local
coordinate multiplies every order-`n` coefficient in (3) by the same nonzero scalar
\((-i)^n\), so finite agreement and the order-`M` failure are preserved.

There are no real zeros of `X_M`.  Indeed, a real `s` corresponds to \(z=iy\).  Neither shifted
`cosh` factor can vanish there because its argument has nonzero real part.  Moreover

\[
Q(iy)=(-y^2-\alpha^2)(-y^2-\bar\alpha^2)
=|y^2+\alpha^2|^2>0,
\]

so \(P_M(iy)=1+Q(iy)^M>0\).  Hence \(F_M(iy)\ne0\) for every real `y`.

## Exact order and aperiodicity

The product `B` has exact entire order one, and multiplication by the nonconstant polynomial
`P_M` does not change that order.  The affine change of variable preserves exact order.

Suppose \(F_M(z+h)=F_M(z)\) for every `z`.  Along positive real `x`,

\[
\frac{B(x+h)}{B(x)}\longrightarrow e^{2\lambda h},
\qquad
\frac{P_M(x+h)}{P_M(x)}\longrightarrow1.
\]

Therefore \(e^{2\lambda h}=1\), so \(h=\pi i k/\lambda=2ibk\) for some integer `k`.  Every such
`h` is a period of `B`.  Cancelling `B` away from its discrete zero set and applying the
identity theorem gives \(P_M(z+h)=P_M(z)\).  A nonconstant polynomial has no nonzero period: the
coefficient of \(z^{d-1}\) in \(P_M(z+h)-P_M(z)\) is \(d\,\mathrm{lc}(P_M)\,h\), where `d` is its
degree.  Thus `h=0`, so `F_M` and `X_M` are aperiodic.

## Consequence

There is no universal `N` for which the first `N` completed-flux coefficients select the
critical line in the class of aperiodic, order-one, FE-even, Schwarz-real entire functions, even
when the tested zero is nonreal and strictly inside the critical strip and the whole real axis is
zero-free.  Any successful finite-depth theorem for `xi` must consume genuinely arithmetic
Euler-source structure not present in this envelope.

This does not rule out a finite theorem using a global Euler invariant.  It rules out a finite local
passport whose global guards are only the six conditions above.

## Parent-theory and literature attack

- The mechanism is high-order Hermite interpolation by multiplication with a real even polynomial
  flat on a zero quartet.  That mechanism is classical in spirit and prevents a confident novelty
  claim based only on the explicit formula.
- Classical Laguerre--Pólya theory already requires an infinite hierarchy of conditions in general,
  and finite initial inequalities do not characterize real-rootedness without additional
  restrictive hypotheses.
- Initial exact-phrase and mechanism searches across AMS, Project Euclid, and arXiv results located
  classical Laguerre inequalities and specialized coefficient criteria, but not this simultaneous
  FE/Schwarz/critical-strip/nonreal-zero/order-one/aperiodic finite-jet nonselection theorem.  That
  negative search is not a completed literature gate.

## Lean formalization status

`RHTower/FiniteJetGradedRealityNoGo.lean` formalizes the load-bearing local analytic core.  It
constructs the shifted even multiplier `1+(z^2-α^2)^(2N+1)`, proves the exact logarithmic-flux
correction identity, proves that the correction has analytic order exactly `2N+1`, realizes it as
the residue-filled negative logarithmic derivative of an explicit simple-zero factor, and proves
that the germ and its reflection have identical iterated derivatives through order `N` but differ
at order `2N+1`.

The exact module and exact Lake target build pass.  The load-bearing declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.  The real-even quartet multiplier, shifted
`cosh` base, critical-strip normalization, global zero-free real-axis statement, exact order, and
aperiodicity remain paper-only; therefore the card remains at stage 2.

## Gates

- [x] 0 → 1: the finite-passport claim was stated and attacked by an explicit family
- [x] 1 → 2: symmetry, quartet zeros, exact jet contact, later failure, real-axis zero-freeness,
  order, and aperiodicity were proved
- [ ] independent mathematical audit of the quartet coefficient calculation, coordinate conversion,
  zero-free real-axis argument, and aperiodicity proof
- [x] formalize the one-pair polynomial-flatness and completed-germ coefficient theorem in Lean
- [ ] 2 → 3: formalize the real-even quartet multiplier and global shifted-`cosh` realization
- [ ] literature and parent-theory audit sufficient for any scientific-novelty promotion

## Lean formalization — COMPLETE (2026-08-21)

The three items the previous status note left "paper-only" — the real-even quartet multiplier, the
shifted `cosh` base with its critical-strip normalization, and the global zero-free real axis,
exact order and aperiodicity — are now all formalized, together with the completed-flux germ
statement for the **actual** realizing function (not only its local model).

New modules:

* `formal/GaloisForLFunctions/HTGeometry/ResidueFilledFluxGerm.lean` — a reusable layer:
  - `fluxGerm f w x = if x = 0 then -(ord_w f) else -x f'(w+x)/f(w+x)`;
  - **`fluxGerm_analyticAt_zero`** — the residue-filled germ is analytic at its centre, via the
    factorization `f z = (z-w)^m g z`;
  - `eventually_ne_zero_of_analyticOrderAt_eq` — a zero of finite order is isolated;
  - **`fluxGerm_mul`** — the germ of a product is the sum of the germs.
* `formal/GaloisForLFunctions/RHTower/GradedRealityQuartetRealization.lean` — the realization.

Both are wired into their umbrellas, and every capstone has axiom footprint
`propext, Classical.choice, Quot.sound`.

### The construction, in the corpus's own normalization

Instead of rescaling the function by `λ = 2π`, the scaling is moved into the coordinate change,
which leaves the corpus's `coshQuartetEnvelope` machinery directly applicable:

```text
B(w)   = cosh (w - π/2) · cosh (w + π/2)          -- gradedEnvelope
Q(w)   = w⁴ + π⁴/4                                 -- quartetPoly, roots ±α, ±conj α
α      = π(1+i)/2                                  -- quartetPoint
P_N(w) = 1 + Q(w)^{2N+1}                           -- flatMultiplier
F_N    = B · P_N                                   -- gradedRealityFn
X_N(s) = F_N(-2πi(s - 1/2))                        -- gradedRealityXi
```

`Q(w) = w⁴ + π⁴/4` is the *closed form* of the card's `(w²-α²)(w²-conj α²)`; the quartet
`±α, ±conj α` maps under `s = 1/2 + iw/(2π)` to exactly `1/4 ± i/4`, `3/4 ± i/4`.

### Correspondence with the card

| Card item | Lean declaration |
|---|---|
| `B`, `Q`, `P_M`, `F_M`, `X_M` | `gradedEnvelope`, `quartetPoly`, `flatMultiplier`, `gradedRealityFn`, `gradedRealityXi` |
| `X_M(1-s) = X_M(s)` | `gradedRealityXi_functional_equation` |
| `X_M(conj s) = conj X_M(s)` | `gradedRealityXi_conj` |
| the four points are zeros of `X_M` | `gradedRealityXi_quartet_one` … `_four` |
| they lie strictly inside the strip, off the line and off the axis | `quartet_strictly_inside_strip` |
| they are **simple** zeros | `analyticOrderAt_gradedRealityFn_fePartner`, `..._schwarzPartner` |
| no real zero | `gradedRealityXi_ne_zero_of_real` |
| `B(z + 2ib) = B(z)` and the partner centres | `gradedEnvelope_add_pi_mul_I`, `schwarzPartnerCentre_eq` |
| exact order one (two-sided sandwich) | `gradedRealityFn_exact_order_one_bounds` |
| aperiodicity | `gradedRealityFn_periodic_iff` |
| `(1)` the multiplier correction vanishes to exact order `M` | `multFlux`, `analyticOrderAt_multFlux_sub` |
| `(2)` `q_c^M ≠ q_d^M` | `four_mul_fePartnerCentre_cube`, `four_mul_schwarzPartnerCentre_cube`, `multUnit_zero_ne` |
| `(3)` equal jets through `N`, failure at `2N+1` | `feGerm_iteratedDeriv_eq_schwarz_of_le`, `feGerm_iteratedDeriv_ne_schwarz_at_escape` |
| the whole theorem | **`finite_jet_graded_reality_nonselection`** |

### Proof mechanisms

1. **Simple zeros.** `analyticOrderAt (B · P_N) c = analyticOrderAt B c + analyticOrderAt P_N c`.
   The second is `0` because `Q(c) = 0` forces `P_N(c) = 1`; the first is `1` because at `c` one
   `cosh` factor is nonzero (its argument has real part `-π`) and the other has a zero with nonzero
   derivative `sinh(∓πi/2) = ∓i`.
2. **The germ split.** `fluxGerm_mul` reduces the partner comparison to the multiplier alone. The
   base germs at `c` and `d = c + πi` are *literally equal*, because `π i` is a period of `B` and
   hence of `B'` (`deriv_gradedEnvelope_add_pi_mul_I`).
3. **The multiplier germ.** With `Q(w+x) = x · (4w³ + 6w²x + 4wx² + x³)` at a root `w`, the
   multiplier factors as `hermiteFlatFactor M u` with `u(0) = (4w³)^M`, so the corpus's
   `hermiteFlatFluxCorrection` applies verbatim. The difference of the two corrections is
   `x^M · (unit_c - unit_d)` with `(unit_c - unit_d)(0) = -M((4c³)^M - (4d³)^M)`.
4. **The separation `(2)`.** `4c³ = π³(1-i)` and `4d³ = π³(1+i)`, and `1-i = -i(1+i)`, so equality
   of the `M`-th powers would force `(-i)^M = (-1)^N(-i) = 1`, which is impossible for a purely
   imaginary number. This replaces the card's `cos(Mπ/4) ≠ 0` computation by an exact algebraic
   identity — **no numerical evaluation is used anywhere**.
5. **Coefficient form.** `analyticOrderAt (multFlux_c - multFlux_d) 0 = 2N+1` gives vanishing of
   every iterated derivative below `2N+1` and non-vanishing at `2N+1`; since both germs are
   analytic, `iteratedDeriv_sub` converts this into the card's coefficientwise statement.

The remaining unchecked gate is the card's own "independent mathematical audit"; the literature /
novelty gate is likewise unaffected by formalization.
