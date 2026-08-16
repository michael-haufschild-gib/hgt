# Finite true-prime cone and mass-shell quadrature defect

- **ID:** C42
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** The mass-shifted spectral-face criterion for RH is unchanged when the finite
  centered all-integer cone is replaced by a finite cone supported only on valuation-one primes;
  exact Bessel geometry reduces the raw-source cone to a sharp entropy--action threshold, while
  graded rigidity identifies every asymptotically caustic finite cone modulo type-zero tails.

## Goal

Remove every deterministic integer atom and every nonprimitive Euler valuation from the finite
light-cone criterion.  This makes the exact arithmetic face genuinely prime-supported, so the
prime-sieve and prime Dirichlet-polynomial corpus become type-correct inputs.  Then classify the
exact Bessel raw-source caustic, use `PNTPlus` to remove the strongest currently justified
subcaustic discrepancy layer, and match cone slope to the corpus graded vertical type.  None of
these reductions claims the remaining type-zero discrepancy estimate.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, exact cone and candidate decomposition identified
- [x] 1 → 2 fully-proven: complete paper proof below, `[PROVED HERE]`, no open mathematical dependency
- [ ] 2 → 3 formalized: intentionally not attempted in this paper-only pass
- [ ] 3 → 4 publication-ready: standalone novelty and exposition audit still required

## Status labels

- Main equivalence: `[PROVED HERE]`
- Prime-square cone-tail lemma: `[PROVED HERE]`
- True-prime Dirichlet face: `[PROVED HERE]`
- Prime-log quadrature-defect face: `[PROVED HERE]`
- Outgoing-current bounded-coboundary bridge: `[PROVED HERE]`
- Moving true-prime annulus cancellation: `[PROVED HERE]`
- Closed minimal strip-limited cone: `[PROVED HERE]`
- Sharp Bessel entropy--action cone and endpoint tail: `[PROVED HERE]`
- Subthreshold raw prime-annulus divergence: `[PROVED HERE]`
- `PNTPlus` subcaustic discrepancy-layer reduction: `[PROVED HERE]`
- Asymptotically caustic type-zero criterion: `[PROVED HERE; LEAN-PROVED]`
- Caustic-null polynomial jet hierarchy and timelike identity wall: `[PROVED HERE; LEAN PENDING]`
- Jordan-floor spectral-resolution no-go: `[PROVED HERE; LEAN PENDING]`
- Harmonic-floor transform and critically stable `mu(n)/n` inverse: `[PROVED HERE; LEAN-PROVED]`
- Graded Bessel cone/type phase diagram: `[PROVED HERE]`
- External novelty: `[NOVELTY-CANDIDATE]`; no matching theorem was found in the searches recorded
  below, but this is not a priority claim.
- RH: `[OPEN]`; the new true-prime pairing remains RH-equivalent.

## 1. Definitions

Fix real parameters

\[
 \frac12<c<a,\qquad \sigma>0,\qquad \frac12<d<a.
\]

For `u>=0`, put

\[
 H=H_d(u):=\frac{du}{d-\frac12},\qquad
 M=M_d(u):=\lfloor e^H\rfloor,
\]

and define the actual mass Fourier profile

\[
 F_u(h):=\int_{\mathbb R}
 e^{-(\sigma+iu)\sqrt{x^2+a^2}}e^{-ihx}\,dx.
\]

The three finite faces used below are

\[
 C_u:=\sum_{2\le n\le M}(\Lambda(n)-1)n^{-1/2}F_u(\log n),
\]

\[
 L_u:=\sum_{2\le n\le M}\Lambda(n)n^{-1/2}F_u(\log n),
\]

and the true-prime cone

\[
 P_u:=\sum_{p\le M}\frac{\log p}{\sqrt p}F_u(\log p).
\]

All sums are finite.  No convergence convention is hidden in these definitions.

We use the positive finite constant

\[
 J_\sigma:=\int_{\mathbb R}e^{-\sigma|x|}\,dx.
\]

## 2. Closed corpus inputs

Only the following already-proved unconditional results are used.

1. **Centered finite-cone criterion.** For the displayed legal parameters,

   \[
   \mathrm{RH}\iff \sup_{u\ge0}|C_u|<\infty.
   \]

2. **Bounded integer face.** With

   \[
   I_u:=\sum_{2\le n\le M}n^{-1/2}F_u(\log n),
   \]

   there is a constant depending only on `a,sigma,d` such that
   `|I_u|` is bounded for all `u>=0`.

   Its paper mechanism is exact.  If `K_u(h)=e^{-h/2}F_u(h)`, `N=M-1`, and
   `W=log(M+1)`, logarithmic-cell FTC and finite Abel summation give

   \[
   I_u=\int_0^W e^{h/2}F_u(h)\,dh
       +\int_0^W S_u(h)\,dh-K_u(W),                                      \tag{2.1}
   \]

   where

   \[
   S_u(h)=e^{-h/2}(\lfloor e^h\rfloor-e^h)
          \left(\frac12F_u(h)-F'_u(h)\right).
   \]

   The polar identity

   \[
   2\cosh(h/2)F_u(h)=e^{h/2}F_u(h)+e^{-h/2}F_u(h)
   \]

   and the exact polar-source evaluation bound the first integral at every `W>=H`.
   The inequality `|floor(e^h)-e^h|<=1`, the actual outgoing integral bound, and
   `e^{-h/2}` bound the second.  Finally `|K_u(W)|<=J_sigma`.  Since
   `e^H<M+1`, one has `W>H`, so all three estimates apply.  Thus (2.1) is a
   dependency-closed proof of the required uniform integer-face bound.

3. **Full square layer.** The actual infinite valuation-two layer

   \[
   S_{2,u}:=\sum_p\frac{\log p}{p}F_u(2\log p)
   \]

   converges and is uniformly bounded in `u`.  The proved mechanism is the adaptive-depth
   pole-residue decomposition of the zeta logarithmic derivative; it assumes neither RH nor a
   zero-free half-plane.

4. **Strip shift.** For `0<=y<a`, `u>=0`, and `h>=0`, contour translation through the actual
   holomorphic mass strip gives

   \[
   |F_u(h)|\le J_\sigma e^{yu-yh}.                                      \tag{2.2}
   \]

These are theorem dependencies, not conjectural assumptions.

## 3. Integer-face removal

### Lemma 3.1 `[PROVED HERE]`

Uniform boundedness of `C_u` for `u>=0` is equivalent to uniform boundedness of `L_u`.

### Proof

Term by term,

\[
 L_u=C_u+I_u.
\]

The integer face `I_u` is uniformly bounded by §2.2.  Therefore each of `C_u` and `L_u` differs
from the other by one uniformly bounded family.  This proves both implications. ∎

In particular,

\[
 \mathrm{RH}\iff\sup_{u\ge0}|L_u|<\infty.                              \tag{3.1}
\]

## 4. Prime-square truncation does not reopen the critical layer

Write

\[
 Q_u:=\sum_{p^2\le M}\frac{\log p}{p}F_u(2\log p).
\]

The full square layer is bounded, but this alone does not formally imply boundedness of its moving
prefix.  The omitted tail must be controlled uniformly.

### Lemma 4.1: cone half-decay `[PROVED HERE]`

If `h>=H_d(u)`, then

\[
 du-dh\le-\frac h2.                                                     \tag{4.1}
\]

### Proof

Since `d-1/2>0`, the inequality `H_d(u)<=h` is equivalent to

\[
 du\le (d-\tfrac12)h.
\]

Subtracting `dh` gives (4.1). ∎

### Lemma 4.2: uniform square tail `[PROVED HERE]`

The family

\[
 T_u:=\sum_{p^2>M}\frac{\log p}{p}F_u(2\log p)
\]

is absolutely convergent and uniformly bounded for `u>=0`.

### Proof

If `p^2>M=floor(e^H)`, integrality gives `e^H<p^2`, hence
`H<2 log p`.  Apply (2.2) with `y=d`, then Lemma 4.1 with `h=2 log p`:

\[
 |F_u(2\log p)|
 \le J_\sigma e^{du-2d\log p}
 \le J_\sigma e^{-\log p}
 =\frac{J_\sigma}{p}.
\]

Consequently

\[
 \left|\frac{\log p}{p}F_u(2\log p)\right|
 \le J_\sigma\frac{\log p}{p^2}.
\]

The majorant is summable.  For `x>=1`, write `y=x^(1/4)`.  The elementary inequality
`log y<=y` gives `log x<=4x^(1/4)`, hence

\[
 \frac{\log p}{p^2}\le 4p^{-7/4}.
\]

The prime sum is bounded by the corresponding convergent integer sum.  This majorant is
independent of `u`. ∎

### Corollary 4.3 `[PROVED HERE]`

`Q_u` is uniformly bounded.

### Proof

The absolutely convergent full layer splits exactly as

\[
 S_{2,u}=Q_u+T_u.
\]

Use the full-layer theorem and Lemma 4.2. ∎

The important structural fact is (4.1): past the moving cone, any legal strip depth automatically
produces one additional critical half-decay.  At square frequencies this changes the nonsummable
critical envelope `(log p)/p` into the summable envelope `(log p)/p^2`.

## 5. Higher prime powers are uniformly harmless

Put

\[
 R_u:=\sum_{\substack{p^r\le M\\r\ge3}}
       \frac{\log p}{p^{r/2}}F_u(r\log p).
\]

### Lemma 5.1 `[PROVED HERE]`

`R_u` is uniformly bounded for `u>=0`.

### Proof

The zero-depth case of (2.2) gives `|F_u(h)|<=J_sigma`.  Therefore

\[
 |R_u|\le J_\sigma\sum_p\sum_{r\ge3}\frac{\log p}{p^{r/2}}.             \tag{5.1}
\]

For every prime `p>=2`, the inner sum is geometric:

\[
 \sum_{r\ge3}p^{-r/2}
 =\frac{p^{-3/2}}{1-p^{-1/2}}
 \le \frac{p^{-3/2}}{1-2^{-1/2}}.
\]

Also `log x=4 log(x^{1/4})<=4x^{1/4}` for `x>=1`, using `log y<=y`.  Hence the
right side of (5.1) is at most

\[
 \frac{4J_\sigma}{1-2^{-1/2}}\sum_p p^{-5/4}
 \le \frac{4J_\sigma}{1-2^{-1/2}}\sum_{n\ge2}n^{-5/4}<\infty.
\]

This constant is independent of `M` and `u`. ∎

## 6. Finite true-prime cone criterion

### Theorem 6.1 `[PROVED HERE]`

For every legal `a,c,sigma,d`,

\[
 \boxed{\quad
 \mathrm{RH}\iff
 \exists C\ \forall u\ge0:\
 \left|\sum_{p\le\lfloor\exp(H_d(u))\rfloor}
       \frac{\log p}{\sqrt p}F_u(\log p)\right|\le C.
 \quad}                                                               \tag{6.1}
\]

### Proof

The von Mangoldt function is supported exactly on prime powers and satisfies
`Lambda(p^r)=log p`.  Unique factorization therefore gives the exact finite identity

\[
 L_u=P_u+Q_u+R_u.                                                       \tag{6.2}
\]

No rearrangement of an infinite series occurs.  Corollary 4.3 and Lemma 5.1 show that
`Q_u+R_u` is uniformly bounded.  Hence `L_u` is uniformly bounded exactly when `P_u` is.
Combine this with (3.1). ∎

This is strictly smaller than the previous centered cone: its support consists only of true primes,
not all integers and not prime powers.

## 7. Exact prime-supported Dirichlet face

Define the finite prime Dirichlet polynomial

\[
 D^{\mathbb P}_{d,u}(x):=
 \sum_{p\le M_d(u)}\frac{\log p}{\sqrt p}e^{-ix\log p}.
\]

### Theorem 7.1 `[PROVED HERE]`

For every `u>=0`,

\[
 P_u=\int_{\mathbb R}
 e^{-(\sigma+iu)\sqrt{x^2+a^2}}D^{\mathbb P}_{d,u}(x)\,dx.             \tag{7.1}
\]

Consequently RH is equivalent to a uniform bound for the right side of (7.1).

### Proof

Expand the finite polynomial in the integral.  Finite linearity gives

\[
 \int_{\mathbb R}e^{-(\sigma+iu)\sqrt{x^2+a^2}}
 \sum_{p\le M}\frac{\log p}{\sqrt p}e^{-ix\log p}\,dx
 =\sum_{p\le M}\frac{\log p}{\sqrt p}F_u(\log p).
\]

Each summand is integrable because its norm is bounded by `e^{-sigma|x|}` times a fixed finite
coefficient.  The last assertion is Theorem 6.1. ∎

This is the first exact face in the route to which the prime-supported sieve theorems apply without
a support mismatch.

## 8. Exact rapidity form and phase geometry

### Proposition 8.1 `[PROVED HERE]`

The mass profile has the exact hyperbolic representation

\[
 F_u(h)=a\int_{\mathbb R}\cosh t\,e^{-a\sigma\cosh t}
 e^{-ia(u\cosh t+h\sinh t)}\,dt.                                      \tag{8.1}
\]

For `0<=h<u`, put `q=sqrt(u^2-h^2)` and choose `eta>=0` with
`cosh eta=u/q`, `sinh eta=h/q`.  Then

\[
 u\cosh t+h\sinh t=q\cosh(t+\eta),                                   \tag{8.2}
\]

so the phase has one real stationary point `t=-eta`.  For `h>u`, put
`r=sqrt(h^2-u^2)` and choose `eta>=0` with `sinh eta=u/r`,
`cosh eta=h/r`.  Then

\[
 u\cosh t+h\sinh t=r\sinh(t+\eta),                                   \tag{8.3}
\]

whose derivative never vanishes.  At `h=u`, the phase is `u e^t`.

### Proof

In the defining integral for `F_u`, substitute `x=a sinh t`.  Then
`sqrt(x^2+a^2)=a cosh t` and `dx=a cosh t dt`, which proves (8.1).
Equations (8.2) and (8.3) are the hyperbolic addition formulas.  Differentiating their right sides
gives the stationary and nonstationary assertions. ∎

The light cone is therefore intrinsic to the actual kernel, not an artifact of contour estimates.
The unresolved cancellation lives in the stationary prime range `log p<u` together with its
turning layer near `log p=u`; ordinary absolute or mean-square estimates erase precisely this
geometry.

## 9. Prime-log quadrature defect

Let

\[
 \Theta(h):=\sum_{\log p\le h}\log p,
 \qquad \Delta_\Theta(h):=\Theta(h)-e^h,
 \qquad K_u(h):=e^{-h/2}F_u(h),
\]

and put `W_u=log(M_d(u)+1)`.  We use the half-open interval `[0,W_u)` so an atom at
`log(M+1)` is not accidentally included.

### Theorem 9.1 `[PROVED HERE]`

There is an exact decomposition

\[
 P_u=\int_0^{W_u}e^{h/2}F_u(h)\,dh
     +\int_{[0,W_u)}K_u(h)\,d\Delta_\Theta(h).                          \tag{9.1}
\]

The first term is uniformly bounded in `u`.  Hence

\[
 \boxed{\quad
 \mathrm{RH}\iff
 \sup_{u\ge0}\left|
   \int_{[0,W_u)}K_u(h)\,d\Delta_\Theta(h)
 \right|<\infty.
 \quad}                                                               \tag{9.2}
\]

### Proof

The Stieltjes measure `dTheta` is exactly

\[
 d\Theta=\sum_p(\log p)\,\delta_{\log p}.
\]

Because `e^H<M+1`, every prime `p<=M` lies in `[0,W_u)`, while every prime represented there is
at most `M`.  Therefore

\[
 \int_{[0,W_u)}K_u\,d\Theta
 =\sum_{p\le M}(\log p)e^{-\log p/2}F_u(\log p)=P_u.
\]

Since `d(e^h)=e^h dh`, subtracting and adding the continuum measure gives (9.1).

The continuum integral is the growing-profile integral from §2.2.  Here `W_u>H_d(u)`, so the
proved polar partial-source estimate bounds it uniformly.  Thus the defect term differs from `P_u`
by a uniformly bounded family, and (9.2) follows from Theorem 6.1. ∎

This is the higher interpretation of the route: RH-strength source is a critical quadrature defect
between true-prime logarithmic measure and its continuum density, tested only against one outgoing
Klein--Gordon mass family.  Integer-face and prime-power obstructions were shadows of using the
wrong reference measure.

## 10. Conjecture / proof-or-failure loop

### C42-A — moving truncation might reactivate prime squares

**Verdict:** false; Lemma 4.2 proves a stronger positive result.  Cone geometry generates an extra
half-decay and makes the omitted square tail absolutely summable.  This was the only missing step
between the bounded infinite square layer and a finite true-prime cone.

### C42-B — higher valuations might accumulate inside the growing cone

**Verdict:** false; Lemma 5.1 gives one support-independent absolute majorant.  No cone geometry or
prime counting is needed once `r>=3`.

### C42-C — affine prime-sieve mean square closes (7.1)

**Verdict:** failed quantitatively, despite now being type-correct.  Encode
`D^P(x)` as a prime-supported Dirichlet polynomial with coefficients `a_p=log p` on the line
`Re s=1/2`.  The affine sieve rate contains the nonnegative term

\[
 \kappa\ \ge\ \frac{5\pi}{2}z
 \sum_{p\le M}\frac{(\log p)^2}{p},\qquad z\ge2.                        \tag{10.1}
\]

The sum in (10.1) diverges with `M`.  Every current Perron/kernel consequence charges at least
`sqrt(kappa)`, so its stated bound cannot be uniform.  This does not show that the actual pairing is
large; it proves that the present norm-first sieve theorem cannot close the exact face.

**Positive survivor:** Theorem 7.1 removes the previous support mismatch.  A future
phase-sensitive strengthening can now target the correct prime polynomial directly.

### C42-D — current unconditional PNT error closes the quadrature defect absolutely

**Verdict:** failed at the exact critical exponent.  A bound of the available shape

\[
 |\Delta_\Theta(h)|\ll e^h e^{-c\sqrt h}
\]

combined with zero-depth bounds for `K_u` or `K'_u` leaves

\[
 e^{h/2-c\sqrt h},
\]

which grows and is not integrable on the cofinal cone.  Stieltjes integration by parts merely puts
the same factor in the boundary term and the derivative integral.  The new sharp Chebyshev theorem
therefore reduces constants but not the missing exponent.

**Positive survivor:** (9.2) identifies exact object a nonclassical PNT input would have to bound:
the mass-shell quadrature defect, not pointwise `theta(x)-x`.

### C42-E — integral Lipschitz plus the connected prime graph recovers constant mode

**Verdict:** failed by exact inverse incidence.  The actual integral Lipschitz theorem uniformly
bounds adjacent frequency differences, but Abel inversion weights them by cumulative prime mass
and adds a terminal flux.  Those terms are not controlled by local edge bounds.  Passing from a
matching to the full connected prime graph does not change this boundary class.

**Positive survivor:** Theorems 7.1 and 9.1 show two possible genuinely nonlocal targets:
mass-coupled prime-polynomial pairing or prime-log quadrature defect.

### C42-F — exact rapidity geometry supplies a new phase-sensitive avenue

**Verdict:** open, but type-correct and nonclassical.  Proposition 8.1 divides the arithmetic face
at `log p=u` into stationary, turning, and nonstationary regimes.  Recent generic large-value and
additive-prime exponential-sum estimates do not preserve this mixed hyperbolic/logarithmic phase.
A useful next theorem must couple the prime polynomial to `exp(-iau cosh t)` before taking norms.

## 11. Hostile circularity audit

1. No step assumes a bound on `P_u`, `L_u`, the centered cone, a zeta reciprocal on the critical
   half-plane, or a zero-free region equivalent to RH.
2. Square-tail proof uses only strip holomorphy, cone algebra, and a convergent `log(p)/p^2`
   majorant.
3. Higher-power proof is absolute and independent of the moving cutoff.
4. Unique factorization is used only in a finite sum.
5. Quadrature-defect identity subtracts the explicit continuum measure; it does not insert a PNT
   estimate.
6. The statement remains RH-equivalent.  It is a strict proof-burden and support reduction, not an
   RH proof.
7. The bounded-coboundary bridge is derived from pointwise identities before any boundedness
   proposition is invoked.  It does not infer a pointwise relation merely because both sides are
   RH-equivalent.
8. Each term removed in (14.1) has an independent unconditional uniform majorant.  No difference
   is declared bounded by subtracting two open-core representatives.
9. The stationary-phase diagnosis uses only the exact phase, its derivative, and the actual
   damping factor.  It claims no unproved asymptotic expansion for the prime sum.

## 12. External state-of-the-art audit

Broad arXiv searches were run with combinations of: `prime-supported Dirichlet polynomial`,
`large values`, `prime exponential sums`, `logarithmic phase`, `moving truncation`, `Klein-Gordon`,
`mass shell`, `Fourier RH criterion`, `Hedenmalm`, `co-Poisson`, `modified Bessel K imaginary
parameter`, `light-cone asymptotics`, and `Bessel Dirichlet polynomial`, emphasizing 2024--2026.

Relevant results found:

- Guth--Maynard, *New large value estimates for Dirichlet polynomials*, arXiv:2405.20552, revised
  2026: large-value and zero-density estimates, not a pointwise mass-coupled bound.
- Srivastav, *Log-free bounds on exponential sums over primes*, arXiv:2505.07803, revised 2026:
  additive phases `e(alpha n)`, not the multiplicative mass-shell phase in (7.1).
- Bazin, *Exponential sums over primes are unbounded*, arXiv:2508.18394, revised 2026: a warning
  that generic prime exponential-sum boundedness is impossible; it does not address the completed
  mass pairing.
- Hedenmalm--Montes-Rodriguez, *The Klein-Gordon equation, the Hilbert transform, and dynamics of
  Gauss-type maps*, arXiv:1503.04038: Klein--Gordon uniqueness on hyperbolic geometry, but no
  von-Mangoldt/true-prime cone criterion.
- Berndt--Dixit--Gupta--Zaharescu, *Two General Series Identities Involving Modified Bessel
  Functions and a Class of Arithmetical Functions*, arXiv:2204.09887: arithmetic `K`-Bessel
  identities from functional equations, but no complex-time prime entropy--action threshold or
  moving-cone classification.

No searched source states Theorem 6.1, the cone half-decay square-tail mechanism, the exact
quadrature-defect criterion (9.2), the bounded-coboundary identity (14.1), or the cofinally
vanishing prime-birth jump law (15.2).  No matching moving prime-annulus cancellation theorem of
the form (14.9), discrete endpoint-closure theorem of the form (14.10), sharp Bessel cone theorem
of the form (17.11), subthreshold coherent-annulus lower bound of the form (17.17),
`PNTPlus`-scale subcaustic law (19.7), or graded cone/type duality (20.3), was found.
Novelty remains a candidate pending expert literature review.

## 13. Next hard theorem

This was the hard theorem before the later Bessel and `PNTPlus` reductions; §19 gives the final
shortened window.

Prove a phase-retaining estimate for either exactly equivalent face:

\[
 \sup_{u\ge0}\left|
 \int_{\mathbb R}e^{-(\sigma+iu)\sqrt{x^2+a^2}}D^{\mathbb P}_{d,u}(x)\,dx
 \right|<\infty,
\]

or

\[
 \sup_{u\ge0}\left|
 \int_{[0,W_u)}e^{-h/2}F_u(h)\,d\Delta_\Theta(h)
 \right|<\infty.
\]

Any proof obtained by applying Cauchy--Schwarz before coupling the two phases is rejected by
(10.1).  Any proof using only the current pointwise PNT remainder is rejected by C42-D.

## 14. Exact bounded-coboundary bridge to the outgoing current

The true-prime cone and the outgoing Chebyshev current are not merely equivalent because both are
equivalent to RH.  They differ pointwise by an explicitly decomposed uniformly bounded family.
This gives a stronger structural identification.

Retain

\[
 K_u(h)=e^{-h/2}F_u(h),\qquad
 R(N)=\psi(N)-N,
\]

and define the discrete remainder density

\[
 \rho_u(h)=e^{-h/2}R(\lfloor e^h\rfloor)
 \left(\frac12F_u(h)-F'_u(h)\right).
\]

Let

\[
 \mathcal O_u=\int_0^\infty e(h)
 \left(\frac12F_u(h)-F'_u(h)\right)\,dh,
 \qquad
 e(h)=\frac{\psi(e^h)-e^h}{e^{h/2}},
\]

be the exact outgoing current.  Write

\[
 \mathcal A_u=\int_0^\infty e^{-h/2}
   (\lfloor e^h\rfloor-e^h)
   \left(\frac12F_u(h)-F'_u(h)\right)\,dh
\]

for the floor-sawtooth current, and put

\[
 \mathcal T_u=\int_H^\infty\rho_u(h)\,dh,
 \qquad
 \mathcal E_u=\int_H^W\rho_u(h)\,dh,
 \qquad W=\log(M+1).
\]

Finally define the terminal Abel flux and the valuation-at-least-two prefix

\[
 Z_u=R(M)K_u(W),
\]

\[
 V_u=\sum_{\substack{p^r\le M\\r\ge2}}
      \frac{\log p}{p^{r/2}}F_u(r\log p)=Q_u+R_u.
\]

### Theorem 14.1: exact bounded-coboundary identity `[PROVED HERE]`

For every `u>=0`,

\[
 \boxed{
 P_u-\mathcal O_u
 =\mathcal E_u+K_u(0)+Z_u+I_u-V_u-\mathcal T_u-\mathcal A_u .
 }                                                                    \tag{14.1}
\]

Moreover every term on the right is uniformly bounded in `u`.  In particular, there is a constant
`B=B(a,sigma,d)` such that

\[
 |P_u-\mathcal O_u|\le B\qquad(u\ge0).                                \tag{14.2}
\]

### Proof

The corpus provides three exact, unconditional identities.  First, splitting normalized Chebyshev
error into the discrete remainder and floor sawtooth gives

\[
 \mathcal O_u=\int_0^\infty\rho_u(h)\,dh+\mathcal A_u.                \tag{14.3}
\]

Second, splitting the infinite discrete current at the geometric cone edge gives

\[
 \int_0^\infty\rho_u(h)\,dh
 =\int_0^H\rho_u(h)\,dh+\mathcal T_u.                                 \tag{14.4}
\]

Third, completing the last logarithmic cell and applying finite Abel summation gives

\[
 \int_0^H\rho_u(h)\,dh+\mathcal E_u
 =-K_u(0)+C_u-Z_u.                                                     \tag{14.5}
\]

Solving (14.5) for `C_u`, using `L_u=C_u+I_u` and the finite prime-power decomposition
`L_u=P_u+V_u`, yields

\[
 P_u=\int_0^H\rho_u(h)\,dh+\mathcal E_u+K_u(0)+Z_u+I_u-V_u.          \tag{14.6}
\]

Subtract (14.3)--(14.4) from (14.6).  This is exactly (14.1).

Uniform bounds are already dependency-closed: `mathcal A_u` is the bounded floor-sawtooth current;
`mathcal T_u` is the bounded superluminal tail; `mathcal E_u` is the bounded cell overflow; `Z_u`
is the bounded terminal Abel flux; `K_u(0)` is bounded by `J_sigma`; `I_u` is the bounded integer
face; and `V_u=Q_u+R_u` is bounded by Corollary 4.3 and Lemma 5.1.  Summing these seven bounds proves
(14.2). ∎

### Corollary 14.2: one open-core quotient class `[PROVED HERE]`

Let `X` be the vector space of complex-valued functions on `[0,infinity)`, and let

\[
 \mathcal B=\{f\in X:\sup_{u\ge0}|f(u)|<\infty\}.
\]

In the algebraic quotient \(X/\mathcal B\),

\[
 [P]=[\mathcal O]=[\text{discrete remainder current}]
 =[\text{finite cone current}]=[C]=[L].                               \tag{14.7}
\]

The quadrature defect in (9.2) represents the same class because its continuum face is uniformly
bounded.  Thus every completed, discrete, conic, centered, prime-power, true-prime, and quadrature
form found by this route is one arithmetic boundary class modulo bounded coboundaries.

This is the higher principle behind the prior obstructions.  Integer removal, floor correction,
cone truncation, finite-cell completion, and nonprimitive Euler valuations only change the
representative.  They cannot solve or worsen the open core.  RH is exactly the assertion that this
class is zero in \(X/\mathcal B\).

### Theorem 14.3: uniform prime-annulus cancellation `[PROVED HERE]`

For any two legal depths `1/2<d_1,d_2<a`, let `P_u^(d_i)` denote the true-prime cone with cutoff
`H_(d_i)(u)`.  Then

\[
 \sup_{u\ge0}|P_u^{(d_1)}-P_u^{(d_2)}|<\infty.                        \tag{14.8}
\]

If `d_1<d_2`, the cone slopes satisfy

\[
 \frac{d_1}{d_1-1/2}>\frac{d_2}{d_2-1/2},
\]

so (14.8) is the nontrivial moving-annulus estimate

\[
 \sup_{u\ge0}\left|
 \sum_{M_{d_2}(u)<p\le M_{d_1}(u)}
   \frac{\log p}{\sqrt p}F_u(\log p)
 \right|<\infty.                                                       \tag{14.9}
\]

### Proof

Apply Theorem 14.1 at `d_1` and `d_2`.  The outgoing current `mathcal O_u` is independent of cone
depth, so

\[
 P_u^{(d_1)}-P_u^{(d_2)}
 =(P_u^{(d_1)}-\mathcal O_u)-(P_u^{(d_2)}-\mathcal O_u).
\]

Both parenthesized families are uniformly bounded by (14.2), proving (14.8).  When `d_1<d_2`,
monotonicity of `d/(d-1/2)` makes the two prime prefixes nested, and their exact difference is
(14.9). ∎

Consequently every fixed slope

\[
 \kappa>\kappa_a:=\frac{a}{a-1/2}
\]

is an admissible true-prime cone slope, and changing `kappa` only adds a uniformly bounded prime
annulus.  Indeed `d=kappa/(2(kappa-1))` satisfies `d/(d-1/2)=kappa`; the inequality
`kappa>kappa_a` is exactly `d<a`, while `kappa>1` gives `d>1/2`.  This narrows the intrinsic
unresolved region to arbitrarily small fixed enlargements of
`0<=h<=kappa_a u`.  The next theorem closes the apparent endpoint gap without shifting a contour
onto the boundary of the mass strip.

### Theorem 14.4: closed strip-limited cone `[PROVED HERE]`

Define

\[
 H_a^\partial(u)=\frac{au}{a-1/2},\qquad
 M_a^\partial(u)=\left\lfloor e^{H_a^\partial(u)}\right\rfloor,
\]

and

\[
 P_u^\partial=\sum_{p\le M_a^\partial(u)}
   \frac{\log p}{\sqrt p}F_u(\log p).
\]

Then

\[
 \sup_{u\ge0}|P_u^\partial-\mathcal O_u|<\infty,                     \tag{14.10}
\]

and hence

\[
 \boxed{
 \mathrm{RH}\iff\sup_{u\ge0}|P_u^\partial|<\infty.
 }                                                                    \tag{14.11}
\]

Moreover, for every legal `d<a`, the complete moving annulus between `H_a^partial(u)` and
`H_d(u)` is uniformly bounded.

### Proof

Fix one `d_0` with `1/2<d_0<a` and inspect the seven majorants in Theorem 14.1 for
`d_0<=d<a`.

- Floor-sawtooth current, `K_u(0)`, and terminal Abel flux are independent of `d`.
- Superluminal tail and final-cell overflow are bounded by a constant multiple of
  `J_(sigma,d)/(d-1/2)`, where `J_(sigma,d)` is affine in `d` through the actual first-moment
  integral.  This is bounded on `[d_0,a)`.
- Integer-face bound has the form `C_0+C_1/(d-1/2)` and is bounded on `[d_0,a)`.
- Square-prefix bound is the fixed full square-layer bound plus the `d`-independent majorant
  `J_sigma sum_p log(p)/p^2`; higher valuations have the `d`-independent majorant from Lemma 5.1.

Thus (14.2) holds with one constant `B_*` simultaneously for every `d_0<=d<a`.

For fixed `u`, the function `d/(d-1/2)` decreases to `a/(a-1/2)` as `d` increases to `a`.
Therefore

\[
 e^{H_d(u)}\downarrow e^{H_a^\partial(u)}.
\]

Put `N=floor(exp(H_a^partial(u)))`.  Since `exp(H_a^partial(u))<N+1`, for all `d<a`
sufficiently close to `a` one has

\[
 N\le e^{H_d(u)}<N+1.
\]

Hence `M_d(u)=N=M_a^partial(u)` and `P_u^(d)=P_u^partial` eventually.  The uniform estimate
`|P_u^(d)-mathcal O_u|<=B_*` passes to this stabilized value and proves (14.10) for every `u` with
the same constant.  The outgoing-current RH criterion gives (14.11).

Finally, subtract (14.10) from Theorem 14.1 at any fixed legal `d`.  Because `H_d(u)` is at least
`H_a^partial(u)`, the difference is exactly the prime annulus between their two cutoffs, and it is
uniformly bounded. ∎

The distinction is important: no analytic estimate is asserted on the forbidden contour
`Im x=-a`.  Endpoint closure comes from uniform interior bounds plus stabilization of a finite
arithmetic prefix.  The canonical endpoint of the fixed-mass strip-shift reduction is therefore
the **closed** cone

\[
 0\le\log p\le\frac{a}{a-1/2}u,                                      \tag{14.12}
\]

not an unspecified supercritical enlargement.  This is minimal within the present strip-shift
family; it does not rule out a future phase-sensitive theorem that removes an additional inner
annulus.

### Corollary 14.5: closed-cone quadrature defect `[PROVED HERE]`

Put `W_a^partial(u)=log(M_a^partial(u)+1)`.  Then

\[
 P_u^\partial
 =\int_0^{W_a^\partial(u)}e^{h/2}F_u(h)\,dh
 +\int_{[0,W_a^\partial(u))}K_u(h)\,d\Delta_\Theta(h),                \tag{14.13}
\]

the first integral is uniformly bounded, and therefore

\[
 \mathrm{RH}\iff
 \sup_{u\ge0}\left|
 \int_{[0,W_a^\partial(u))}K_u(h)\,d\Delta_\Theta(h)
 \right|<\infty.                                                       \tag{14.14}
\]

### Proof

The Stieltjes atomization proof of Theorem 9.1 is finite and applies verbatim at the endpoint
cutoff, giving (14.13).  It remains only to bound the continuum integral.  For each fixed `u`,
strict inequality `H_a^partial(u)<W_a^partial(u)` allows a depth `d<a`, arbitrarily close to `a`,
with `H_d(u)<W_a^partial(u)`.  The existing polar partial-source estimate then applies.  Its bound
is uniform for `d_0<=d<a` by the same constant audit used in Theorem 14.4, so the resulting
continuum bound is independent of `u` and of the selected interior depth.  Combine this with
(14.11). ∎

## 15. Further conjecture / proof-or-failure loops

### C42-G — moving cutoff jumps obstruct any pointwise argument

**Verdict:** false; the jumps are explicit, uniformly bounded, and vanish cofinally.

For a prime `p`, put

\[
 u_p=\frac{d-1/2}{d}\log p.
\]

Then `H_d(u_p)=log p`.  The left limit of `P_u` at `u_p` omits `p`, while `P_{u_p}` includes it, so

\[
 P_{u_p}-\lim_{v\uparrow u_p}P_v
 =\frac{\log p}{\sqrt p}F_{u_p}(\log p).                              \tag{15.1}
\]

The depth-`d` strip shift and the cone-edge identity give

\[
 |F_{u_p}(\log p)|
 \le J_\sigma e^{du_p-d\log p}=\frac{J_\sigma}{\sqrt p}.
\]

Therefore

\[
 \left|P_{u_p}-\lim_{v\uparrow u_p}P_v\right|
 \le J_\sigma\frac{\log p}{p}\longrightarrow0.                       \tag{15.2}
\]

**Positive survivor:** cutoff discontinuity is not the source of possible unboundedness.  Any
large-value-to-pointwise argument may treat the cone trace as a continuous orbit plus cofinally
vanishing jumps.

### C42-H — bounded jumps plus a generic mean-square estimate give a supremum bound

**Verdict:** failed quantitatively.  Between two birth heights the prime support is fixed, and
differentiation under the actual integral gives

\[
 |P'_u|\le J^{(1)}_\sigma
   \sum_{p\le M}\frac{\log p}{\sqrt p},
 \qquad
 J^{(1)}_\sigma=\int_{\mathbb R}\sqrt{x^2+a^2}
                      e^{-\sigma\sqrt{x^2+a^2}}\,dx.
\]

The corpus sharp prime-mass estimate bounds the sum only by a constant times `sqrt(M)`.  Since
`M` has scale `exp(H_d(u))`, the resulting chamber Lipschitz constant has scale

\[
 \exp(H_d(u)/2)=\exp\!\left(\frac{d}{2d-1}u\right).                   \tag{15.3}
\]

Thus bounded jumps do not upgrade an average estimate to a uniform pointwise estimate unless the
averaging window is exponentially short or the derivative estimate retains the joint phase.
Current affine mean-square theorems do neither.

### C42-I — exact Klein--Gordon energy conservation closes the outgoing observation

**Verdict:** fails at the observation map, not at propagation.  The HTGeometry corpus proves the
free Klein--Gordon orbit is isometric in its energy space.  To infer a uniform bound for
`mathcal O_u` from that theorem, one still needs the source functional

\[
 v\longmapsto\int_0^\infty e(h)\left(\frac12v(h)-v'(h)\right)\,dh     \tag{15.4}
\]

to extend continuously to that energy space, or at least to the cyclic mass-profile subspace.
No current theorem supplies this source-to-state map.  Declaring (15.4) bounded on the required
orbit would directly imply the open core.  Exponential weighting makes the source pairing
well-defined, but the radiation-corona theorem then gives the conjugated propagator exact norm
`exp(d|u|)`; the same critical growth reappears.

**Positive survivor:** a restricted cyclic-observation theorem is a type-correct new avenue.  It
need only control the closed orbit generated by the actual mass profile, not every
Klein--Gordon state.  Ordinary full-space energy conservation alone is insufficient.

### C42-J — Hilbert coherence, Hedenmalm trace kernels, or QEC projection remove the class

**Verdict:** failed by direction or type.

- `SpectralBandwidthFano` and related HilbertMetric results are finite-frame nonnegative
  decompositions and lower bounds.  They provide neither a source-side upper Bessel bound nor a
  map from prime-log discrepancy to the mass orbit.
- Hedenmalm's trace kernel calibrates a positive double-kernel invariant to source variance, while
  the prime-frame obstruction proves finite and summably weighted diagonal prime frames have no
  lower frame bound.  Neither controls the non-diagonal class (14.7).
- QEC stabilizer projectors and QuantumAlg finite circuits have no analytic map from the cofinal
  prime-log source into a code space.  Every finite projector can remove only a finite-dimensional
  representative; all such changes lie in the bounded coboundary already removed in (14.1).

The surviving requirement is a cofinal, non-diagonal source observation.  Importing a
finite-dimensional projector without constructing that map is a type error, not a conjectural RH
argument.

### C42-K — stationary phase supplies adjacent-prime cancellation in the bulk

**Verdict:** false; the exact mass geometry shows why classical prime oscillation is the wrong
mechanism.

For `0<h<u`, the rapidity phase has stationary value

\[
 \Phi_u(h)=a\sqrt{u^2-h^2}.
\]

At the stationary point,

\[
 |\partial_h\Phi_u(h)|=\frac{ah}{\sqrt{u^2-h^2}},\qquad
 e^{-a\sigma\cosh\eta}
 =\exp\!\left(-\frac{a\sigma u}{\sqrt{u^2-h^2}}\right).              \tag{15.5}
\]

If `h=alpha u` with fixed `0<alpha<1`, the logarithmic phase frequency in (15.5) is independent of
`u`.  Adjacent prime logs are exponentially closer than this phase scale, so they become more
coherent, not more separated, as the cone grows.  Near `h=u` the phase frequency diverges, but the
second factor in (15.5) decays faster than every power of that frequency: after putting
`y=a sigma u/sqrt(u^2-h^2)`, this is the elementary boundedness of `y^N exp(-y)`.

**Positive survivor:** vertical mass oscillation produces propagation across logarithmic space,
not increasingly fine oscillation at prime spacing.  The continuum prime density must cancel
first.  The genuine source is therefore the quadrature defect `dTheta-e^h dh`, exactly as (9.2)
and (14.7) assert.

### C42-L — Möbius/Euler critical-clock transport transfers the open estimate

**Verdict:** the new corpus theorem is type-compatible but quantitatively insufficient.

Let `epsilon=d-1/2>0` and define the contour-shifted profile

\[
 \widetilde F_{u,d}(h)=e^{dh}F_u(h).
\]

If

\[
 A(s)=\sum_{n\ge2}\frac{\Lambda(n)}{n^s},
\]

and `nu_(1+epsilon)` is the probability law with mass
`Lambda(n)n^(-1-epsilon)/A(1+epsilon)`, then the complete prime-power source has the exact
probability form

\[
 \sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}F_u(\log n)
 =A(1+\epsilon)\,
  \mathbb E_{\nu_{1+\epsilon}}
  [\widetilde F_{u,d}(H_E)].                                         \tag{15.6}
\]

The newly formalized critical-clock theorem couples `H_E` to the squarefree Möbius clock `H_P`
with

\[
 \epsilon\,\mathbb E|H_E-H_P|\longrightarrow0.                      \tag{15.7}
\]

This is precisely the right macroscopic logarithmic scale: under a schedule
`epsilon approximately 1/u`, both `epsilon H` and the mass cone remain order one.  However the
actual shifted profile satisfies only

\[
 \operatorname{Lip}(\widetilde F_{u,d})\le C_{a,\sigma,d}e^{du},
\]

while `A(1+epsilon)` has scale `1/epsilon`.  Applying the Wasserstein estimate to (15.6) therefore
produces only

\[
 A(1+\epsilon)\operatorname{Lip}(\widetilde F_{u,d})
 \mathbb E|H_E-H_P|
 =e^{du}\,o(\epsilon^{-2}).                                          \tag{15.8}
\]

For `epsilon approximately 1/u`, this retains the fatal factor `e^(u/2)`.  The corpus `W_2`
transport does not repair the issue: a second-order Taylor estimate still charges the exponentially
amplified mass-profile derivatives and only polynomially small transport cost.

**Positive survivor:** the two-clock law discovers the correct transport geometry but not the
required topology.  A viable new avenue would prove a **complex phase-coupled transport law** for
the particular observable `widetilde F_(u,d)`, with its cancellation retained inside the coupling,
together with a source-side bound for the transported squarefree observable.  Ordinary `W_1`,
`W_2`, Gini, or positive packet energy cannot close the scalar open core.

## 16. Revised hard theorem and universal interpretation

This intermediate formulation is superseded quantitatively by §§17--19 but retained to record the
conjecture loop that exposed the bounded-coboundary class.

The corpus and loops now reject four broad strategies: norm-first prime mean square, full-space
Hilbert energy, adjacent-prime stationary phase, and metric-only critical-clock transport.  The
narrow surviving theorem is a
phase-retaining **restricted observation law** for the single bounded-coboundary class (14.7):

\[
 W_a^\partial(u)=\log(M_a^\partial(u)+1),
\]

\[
 \sup_{u\ge0}\left|
  \int_{[0,W_a^\partial(u))}K_u(h)\,d\bigl(\Theta(h)-e^h\bigr)
 \right|<\infty.                                                       \tag{16.1}
\]

Equivalently one may bound the outgoing current `mathcal O_u`.  A useful proof must exploit the
fixed prime discrepancy and the actual Klein--Gordon orbit jointly.  It cannot obtain its gain
from increasingly rapid oscillation between adjacent primes, because (15.5) proves that gain is
absent in the bulk.

## 17. Exact Bessel entropy--action cone

The strip-shift cone in Theorem 14.4 is not intrinsic.  It uses only holomorphy of the carrier and
throws away the exact real part of the Bessel action.  The following loop keeps that geometry.

### C42-M — exact nonstationary Bessel decay shrinks the raw prime cone

**Verdict:** proved, including endpoint and sharp subthreshold failure.

Put

\[
 \tau_u=\sigma+iu,\qquad
 z_u(h)=\sqrt{\tau_u^2+h^2},
\]

where the square root is principal.  The Fourier--Bessel identity is

\[
 F_u(h)=\frac{2a\tau_u}{z_u(h)}K_1\!\left(az_u(h)\right).             \tag{17.1}
\]

Define the Bessel balance slope

\[
 \kappa_B:=\frac{a}{\sqrt{a^2-1/4}}>1.                               \tag{17.2}
\]

It is strictly smaller than the strip threshold:

\[
 \kappa_B<\frac{a}{a-1/2},
\]

because `a-1/2<sqrt(a^2-1/4)` is equivalent after squaring to `a>1/2`.

For `kappa>1`, let

\[
 M_\kappa(u)=\lfloor e^{\kappa u}\rfloor,\qquad
 P_u^{(\kappa)}=
 \sum_{p\le M_\kappa(u)}\frac{\log p}{\sqrt p}F_u(\log p),           \tag{17.3}
\]

and let the complementary true-prime tail be

\[
 R_u^{(\kappa)}=
 \sum_{p>M_\kappa(u)}\frac{\log p}{\sqrt p}F_u(\log p).              \tag{17.4}
\]

For each fixed `u`, (17.4) is absolutely convergent by any strip shift with
`1/2<y<a`.

### Lemma 17.1: principal-root exterior geometry `[PROVED HERE]`

For every fixed `kappa>1`, there is `C_kappa<infinity` such that, whenever
`u>=0` and `h>=kappa u`,

\[
 \operatorname{Re}z_u(h)\ge\sqrt{h^2-u^2+\sigma^2}
 \ge\sqrt{h^2-u^2},
 \qquad
 \left|\frac{\tau_u}{z_u(h)}\right|\le C_\kappa.                    \tag{17.5}
\]

#### Proof

Write

\[
 w=\tau_u^2+h^2=A+iB,\qquad
 A=\sigma^2+h^2-u^2>0.
\]

For the principal square root,

\[
 (\operatorname{Re}\sqrt w)^2=\frac{|w|+A}{2}\ge A,
\]

which proves the first assertion.  Also

\[
 |z_u(h)|^2=|w|\ge A\ge\sigma^2+(\kappa^2-1)u^2.
\]

Therefore

\[
 \left|\frac{\tau_u}{z_u(h)}\right|^2
 \le\frac{\sigma^2+u^2}{\sigma^2+(\kappa^2-1)u^2}
 \le \max\left\{1,\frac1{\kappa^2-1}\right\}.
\]

This proves (17.5). ∎

### Lemma 17.2: uniform exterior Bessel envelope `[PROVED HERE]`

For every fixed `kappa>1`, constants `C_0,C_1` depending only on
`a,sigma,kappa` satisfy

\[
 |F_u(h)|\le C_0e^{-a\sqrt{h^2-u^2}}                                \tag{17.6}
\]

for `u>=0`, `h>=kappa u`, and

\[
 |F_u(h)|\le C_1u^{-1/2}e^{-a\sqrt{h^2-u^2}}                         \tag{17.7}
\]

for `u>=1`, `h>=kappa u`.

#### Proof

For `Re z>0`, the standard integral representation gives

\[
 K_1(az)=\int_0^\infty e^{-az\cosh t}\cosh t\,dt.
\]

Consequently, with `X=Re z`,

\[
 |K_1(az)|
 \le e^{-aX}\int_0^\infty e^{-aX(\cosh t-1)}\cosh t\,dt.             \tag{17.8}
\]

Lemma 17.1 gives `X>=sigma`, so the integral after the exponential is bounded uniformly; this
proves an envelope `C exp(-aX)`.  A sharper elementary estimate is available when `X>=1`.
After `s=sinh t`, the integral before factorization is

\[
 \int_0^\infty e^{-aX\sqrt{1+s^2}}\,ds.
\]

The inequality

\[
 \sqrt{1+s^2}\ge1+c\min(s^2,s)\qquad(s\ge0)
\]

holds for one absolute `c>0`; splitting at `s=1` then gives

\[
 |K_1(az)|\le C_aX^{-1/2}e^{-aX}.                                   \tag{17.9}
\]

Combine (17.8)--(17.9) with (17.1), (17.5), and
`X>=sqrt(h^2-u^2)`.  Once `u>=max(1,(kappa^2-1)^(-1/2))`, one has both
`X>=1` and `X^(-1/2)<=C_kappa u^(-1/2)`.  The remaining compact `u`-interval is absorbed into
the constant using (17.8), while `u^(-1/2)` is bounded below there.  This proves
(17.6)--(17.7). ∎

### Theorem 17.3: closed sharp Bessel cone `[PROVED HERE]`

For `kappa>=kappa_B`, define

\[
 \eta_\kappa=a\sqrt{\kappa^2-1}-\frac{\kappa}{2}\ge0.              \tag{17.10}
\]

Then the exterior tail is absolutely bounded uniformly in `u`, and for `u>=1`,

\[
 \sum_{p>M_\kappa(u)}
 \frac{\log p}{\sqrt p}|F_u(\log p)|
 \le C_{a,\sigma,\kappa}u^{-1/2}e^{-\eta_\kappa u}.                 \tag{17.11}
\]

In particular `R_u^(kappa)->0`.  At the exact endpoint `kappa=kappa_B`, the rate in
(17.11) is `O(u^(-1/2))`; for `kappa>kappa_B`, it is exponential.

Moreover,

\[
 \boxed{
 \mathrm{RH}\iff\sup_{u\ge0}|P_u^{(\kappa)}|<\infty
 \qquad(\kappa\ge\kappa_B).
 }                                                                  \tag{17.12}
\]

Thus (17.2), not the larger strip slope `a/(a-1/2)`, is the closed raw-source cone threshold.

#### Proof

For `h>u`, set

\[
 g_u(h)=\frac h2-a\sqrt{h^2-u^2}.
\]

It satisfies

\[
 g_u'(h)=\frac12-\frac{ah}{\sqrt{h^2-u^2}}
 \le-\left(a-\frac12\right).                                      \tag{17.13}
\]

At `h=kappa u`,

\[
 g_u(\kappa u)=-\eta_\kappa u.
\]

Let `theta(x)=sum_(p<=x) log p`.  The unconditional prime number theorem
`theta(x)~x` implies the global Chebyshev majorant `theta(x)<=C x`; only this upper
majorant is used for (17.11).  Partition `log p>kappa u` into the unit blocks

\[
 \kappa u+j<\log p\le\kappa u+j+1\qquad(j\ge0).
\]

By (17.7), monotonicity of both decay factors, and the Chebyshev majorant, the contribution of
the `j`-th block is at most

\[
 C u^{-1/2}
 \exp\!\left(g_u(\kappa u+j)\right)
 \le C u^{-1/2}e^{-\eta_\kappa u}
       e^{-(a-1/2)j}.                                                \tag{17.14}
\]

The geometric sum proves (17.11).  For `0<=u<=1`, choose a fixed `y` with
`1/2<y<a` in the strip estimate (2.2).  It majorizes the complete tail by a constant times

\[
 \sum_p\frac{\log p}{p^{1/2+y}}<\infty,
\]

uniformly on this compact height interval.  This proves absolute uniform boundedness and the
claimed `C_0` conclusion.

To prove (17.12), choose a legal strip depth `d` whose slope
`d/(d-1/2)` is larger than `kappa`; such a `d` exists because those slopes tend to infinity as
`d` decreases to `1/2`.  The difference `P_u^(d)-P_u^(kappa)` is a subseries of the exterior
tail in (17.11), hence is uniformly bounded.  Theorem 14.1 gives
`sup_u |P_u^(d)-mathcal O_u|<infinity`.  Therefore

\[
 \sup_{u\ge0}|P_u^{(\kappa)}-\mathcal O_u|<\infty.
\]

The outgoing-current criterion now proves (17.12). ∎

### Corollary 17.4: endpoint quadrature-defect criterion `[PROVED HERE]`

Let

\[
 W_\kappa(u)=\log(M_\kappa(u)+1),
\]

and

\[
 D_u^{(\kappa)}=
 \int_{[0,W_\kappa(u))}e^{-h/2}F_u(h)\,d\bigl(\Theta(h)-e^h\bigr).
\]

For every `kappa>=kappa_B`,

\[
 \boxed{
 \mathrm{RH}\iff\sup_{u\ge0}|D_u^{(\kappa)}|<\infty.
 }                                                                  \tag{17.15}
\]

#### Proof

The same exponent controls the continuum tail.  From (17.7), (17.13), and
`W_kappa(u)>kappa u`,

\[
 \int_{W_\kappa(u)}^\infty e^{h/2}|F_u(h)|\,dh
 \le C u^{-1/2}e^{-\eta_\kappa u}\qquad(u\ge1).                    \tag{17.16}
\]

Small `u` is handled by the fixed interior strip estimate as above.  Choose a legal `d` with
slope larger than `kappa`.  The corpus polar-source estimate bounds the continuum prefix through
`W_d(u)`, and (17.16) bounds the difference of that prefix with the one through
`W_kappa(u)`.  Hence

\[
 \sup_{u\ge0}\left|\int_0^{W_\kappa(u)}e^{h/2}F_u(h)\,dh\right|<\infty.
\]

The exact finite Stieltjes identity (9.2), now at `M_kappa(u)`, says that
`P_u^(kappa)` is this bounded continuum prefix plus `D_u^(kappa)`.  Apply (17.12). ∎

### Theorem 17.5: subthreshold raw-annulus divergence `[PROVED HERE]`

Let

\[
 1<\kappa<\kappa_B,
 \qquad
 \gamma_\kappa=\frac{\kappa}{2}-a\sqrt{\kappa^2-1}>0.
\]

For every fixed `lambda>kappa`, define

\[
 A_{\kappa,\lambda}(u)=
 \sum_{M_\kappa(u)<p\le M_\lambda(u)}
 \frac{\log p}{\sqrt p}F_u(\log p).
\]

There are constants `c>0` and `u_0` such that

\[
 |A_{\kappa,\lambda}(u)|
 \ge c\,u^{-1/2}e^{\gamma_\kappa u}
 \qquad(u\ge u_0).                                                   \tag{17.17}
\]

Thus every raw linear cone below `kappa_B` has an unbounded annular difference from every larger
cone.  The threshold in Theorem 17.3 is sharp for bounded-coboundary equivalence of unrenormalized
prime prefixes.

#### Proof

Set

\[
 q=\sqrt{\kappa^2-1},\qquad
 \mu=\frac12+\frac{a\kappa}{q},\qquad
 B_\kappa=i\sqrt{2\pi a}\,q^{-3/2}e^{-ia\sigma/q}\ne0.              \tag{17.18}
\]

Fix `L>0`.  Uniformly for `0<=s<=L`, principal-root expansion gives

\[
 z_u(\kappa u+s)
 =qu+\frac{\kappa s+i\sigma}{q}+O_L(u^{-1}).                         \tag{17.19}
\]

These points remain in a closed subsector of the right half-plane.  The standard uniform
large-argument expansion

\[
 K_1(w)=\sqrt{\frac\pi{2w}}e^{-w}\bigl(1+O(|w|^{-1})\bigr)
\]

inserted in (17.1) and (17.19) yields

\[
 e^{-(\kappa u+s)/2}F_u(\kappa u+s)
 =B_\kappa u^{-1/2}e^{-(\kappa/2+aq)u}e^{-\mu s}
   \bigl(1+o_L(1)\bigr),                                             \tag{17.20}
\]

uniformly on the fixed shell.

The corpus PNT theorem `theta(x)~x`, followed by finite-interval Stieltjes partial summation,
gives

\[
 \sum_{\kappa u<\log p\le\kappa u+L}
   \log p\,e^{-\mu(\log p-\kappa u)}
 =e^{\kappa u}\left(J_L+o(1)\right),                                \tag{17.21}
\]

where

\[
 J_L=\int_0^L e^{(1-\mu)s}\,ds>0.
\]

Therefore the first fixed logarithmic shell has the phase-coherent asymptotic

\[
 S_{u,L}=B_\kappa J_Lu^{-1/2}e^{\gamma_\kappa u}(1+o_L(1)).          \tag{17.22}
\]

It remains to exclude cancellation by later primes.  The proof of (17.14) did not use
`eta_kappa>=0`; with `g_u(kappa u)=gamma_kappa u`, it gives

\[
 \sum_{\log p>\kappa u+L}
 \frac{\log p}{\sqrt p}|F_u(\log p)|
 \le C u^{-1/2}e^{\gamma_\kappa u}e^{-(a-1/2)L}.                    \tag{17.23}
\]

As `L` tends to infinity, `J_L` tends to the positive number
`(mu-1)^(-1)`, while the last factor in (17.23) tends to zero.  Choose one fixed `L` for which
the right side of (17.23) is less than one half of the leading modulus in (17.22).  For large `u`,
the interval through `kappa u+L` lies below `lambda u`.  The reverse triangle inequality applied
to this shell and the remaining part of `A_(kappa,lambda)` proves (17.17). ∎

### 17.6 Hostile collision and endpoint audit

1. **No collision with finite-aperture radiation.**  The falsified uniform-aperture route uses
   `u=(log X)^4`, hence `h/u->0`.  Its coherent shell is deep inside the timelike cone.  Lemmas
   17.1--17.2 concern `h/u>=kappa>1`, the disjoint spacelike regime.

2. **Endpoint is a theorem, not a limiting handwave.**  The termwise majorant at `kappa_B`
   resembles `log p/p` and is not summable.  The proof instead groups primes into logarithmic
   blocks and uses `theta(x)<=Cx`.  The negative derivative in (17.13) then makes block masses
   geometric.  No constant is obtained by sending `kappa` down to `kappa_B`.

3. **No RH input.**  Tail upper bounds need only the unconditional Chebyshev estimate; sharpness
   uses the unconditional PNT already present in `PNTPlus`.  Neither zero cancellation nor a
   critical-line estimate enters.

4. **No claim at the physical light cone.**  The proof requires fixed `kappa>1`.  The transition
   `h-u=o(u)` has different square-root scaling and remains part of the inner open core.

5. **Formalization boundary.**  The Lean corpus supplies the PNT/Chebyshev and finite-cone sides,
   but not the complex modified-`K_1` identity, its integral envelope, or its sectorial asymptotic.
   This pass deliberately makes no Lean edit while the corpus is being refactored.

### 17.7 Higher universal principle

The earlier strip slope was a shadow of a source-entropy/action competition.  One logarithmic
prime block has Chebyshev mass on scale `e^h`; after the critical coefficient `p^(-1/2)` and
Bessel damping, its scalar action is

\[
 g_u(h)=\frac h2-a\sqrt{h^2-u^2}.                                   \tag{17.24}
\]

The equation `g_u(kappa u)=0` is exactly `kappa=kappa_B`.  Outside this caustic, action beats
prime entropy and the whole exterior source is a `C_0` coboundary.  Inside it, entropy wins and a
fixed logarithmic prime shell grows with a common Bessel phase.  This explains both previous
failures at once:

- strip shifting saw only analyticity width and therefore retained too large a cone;
- finite-aperture completion sampled the opposite, timelike coherent regime and therefore could
  never prove exterior suppression.

The raw-source cone is now classified sharply.  Any further reduction must subtract continuum
prime entropy before estimating, so the remaining object must be a prime-discrepancy current,
not an unrenormalized positive prime source.

## 18. Sharpened hard theorem

The smallest closed raw-source representative found by the paper proof is now

\[
 W_B(u)=\log\!\left(\lfloor e^{\kappa_Bu}\rfloor+1\right).
\]

The exact unresolved statement is

\[
 \sup_{u\ge0}\left|
  \int_{[0,W_B(u))}e^{-h/2}F_u(h)\,d\bigl(\Theta(h)-e^h\bigr)
 \right|<\infty.                                                      \tag{18.1}
\]

By Corollary 17.4, (18.1) is equivalent to RH.  Compared with (16.1), it deletes an entire
linear annulus unconditionally and reaches the exact entropy--action caustic.  The remaining
problem is phase-retaining observation of prime discrepancy in the timelike/transition region;
raw-source tail estimates cannot reduce it further by Theorem 17.5.

## 19. `PNTPlus` shaves a subcaustic discrepancy layer

Theorem 17.5 blocks smaller **raw** prime cones, but it leaves open a different question: after
subtracting continuum entropy, can the prime-discrepancy cutoff move slightly inside the caustic?
The newest `PNTPlus` error theorem answers yes on a growing sublinear scale.

### C42-N — medium PNT error may penetrate the Bessel caustic

**Verdict:** proved for a `u^(1/10)` boundary layer; fixed linear penetration remains impossible
for the available modulus estimate.

Put

\[
 \alpha=\frac1{10},\qquad
 E(h)=\Theta(h)-e^h,\qquad
 G_u(h)=e^{-h/2}F_u(h).
\]

The formal corpus theorem `MediumPNT`, combined with the standard prime-power comparison between
`psi` and `theta`, gives constants `c,C,h_0>0` such that

\[
 |E(h)|\le Ce^h e^{-c h^\alpha}\qquad(h\ge h_0).                    \tag{19.1}
\]

Indeed `MediumPNT` proves this scale for `psi(e^h)-e^h`, while
`|psi(e^h)-Theta(h)|<=C e^(h/2)h`; the latter is absorbed by the right side of (19.1) after
decreasing `c`.

### Lemma 19.1: differentiated exterior envelope `[PROVED HERE]`

Fix `kappa_0>1`.  There is `C_0` such that, for `u>=1` and `h>=kappa_0 u`,

\[
 |G_u(h)|+|G_u'(h)|
 \le C_0u^{-1/2}e^{-h/2-a\sqrt{h^2-u^2}}.                           \tag{19.2}
\]

#### Proof

The estimate for `G_u` is Lemma 17.2.  For the derivative, differentiate (17.1).  Principal-root
geometry gives

\[
 z_u'(h)=\frac h{z_u(h)},
\]

and both `h/z_u(h)` and `tau_u/z_u(h)` are uniformly bounded on
`h>=kappa_0 u`.  Differentiating the integral representation in Lemma 17.2 gives

\[
 K_1'(az)=-\int_0^\infty e^{-az\cosh t}\cosh^2t\,dt.
\]

After `s=sinh t`, the extra hyperbolic factor is at most polynomial in `s`; the same split at
`s=1` proves the envelope `C X^(-1/2)e^(-aX)` for `X=Re z>=1`.  Derivatives of `1/z` contribute
only additional bounded factors or powers of `u^(-1)`.  The remaining compact `u`-interval is
absorbed exactly as in Lemma 17.2.  Finally differentiating `e^(-h/2)` adds `|G_u|/2`.
This proves (19.2). ∎

### Lemma 19.2: exterior prime-discrepancy tail `[PROVED HERE]`

Fix `kappa_0>1`.  After possibly decreasing the constant `c` in (19.1), for all sufficiently
large `u` and every `H>=kappa_0 u`,

\[
 \left|\int_{[H,\infty)}G_u(h)\,dE(h)\right|
 \le C u^{-1/2}
 \exp\!\left(g_u(H)-cH^\alpha\right),                               \tag{19.3}
\]

where `g_u` is (17.24).

#### Proof

Stieltjes integration by parts on `[H,T]` gives boundary terms `G_uE` and the ordinary integral
of `E G_u'`.  Equations (19.1)--(19.2) bound both by the envelope

\[
 C u^{-1/2}\exp\!\left(g_u(h)-ch^\alpha\right).
\]

By (17.13), the exponent has derivative at most `-(a-1/2)`.  Its boundary at infinity therefore
vanishes, and its integral from `H` to infinity is at most a fixed multiple of its value at `H`.
Letting `T` tend to infinity proves (19.3). ∎

### Theorem 19.3: coefficient-sharp growing subcaustic reduction `[PROVED HERE]`

Fix one admissible constant `c>0` in (19.1), and put

\[
 m_B=2a^2-\frac12,
 \qquad
 L_c=\frac{c\kappa_B^{1/10}}{m_B}.                                 \tag{19.4}
\]

For every fixed `L` with `0<L<=L_c`, define

\[
 H_*(u)=\kappa_Bu-Lu^{1/10},\qquad
 M_*(u)=\lfloor e^{H_*(u)}\rfloor,\qquad
 W_*(u)=\log(M_*(u)+1).                                             \tag{19.5}
\]

the exterior discrepancy is a vanishing family:

\[
 \int_{[W_*(u),\infty)}G_u(h)\,dE(h)\longrightarrow0.               \tag{19.6}
\]

Consequently

\[
 \boxed{
 \mathrm{RH}\iff
 \sup_{u\ge0}\left|
  \int_{[0,W_*(u))}e^{-h/2}F_u(h)\,d\bigl(\Theta(h)-e^h\bigr)
 \right|<\infty.
 }                                                                  \tag{19.7}
\]

#### Proof

At the caustic, (17.10) gives

\[
 \frac{\kappa_B}{\sqrt{\kappa_B^2-1}}=2a,
 \qquad
 -g_u'(\kappa_Bu)=m_B.                                              \tag{19.8}
\]

Taylor's theorem on any fixed exterior ratio neighborhood of `kappa_B` gives

\[
 g_u(\kappa_Bu-Lu^\alpha)
 =m_BL u^\alpha+O(u^{2\alpha-1}),                                  \tag{19.9}
\]

while

\[
 (\kappa_Bu-Lu^\alpha)^\alpha
 =\kappa_B^\alpha u^\alpha+O(u^{2\alpha-1}).                       \tag{19.10}
\]

Here `2alpha-1<0`.  Choose any fixed `kappa_0` with
`1<kappa_0<kappa_B`.  For all sufficiently large `u`, `H_*(u)>=kappa_0u`; also
`H_*(u)<W_*(u)<kappa_Bu`, because `W_*(u)-H_*(u)=O(exp(-H_*(u)))` while the
caustic gap is `L u^alpha`.  Replacing `H_*` by `W_*` changes (19.9)--(19.10) by `o(1)`.
Apply (19.3).  If `L<L_c`, its exponent is

\[
 -(c\kappa_B^\alpha-m_BL)u^\alpha+o(1),
\]

which gives stretched-exponential decay.  If `L=L_c`, the exponential factor is `e^(o(1))`, and
the prefactor `u^(-1/2)` in (19.3) still tends to zero.  This proves (19.6) throughout the closed
coefficient chamber.

The difference between the endpoint defect in (18.1) and the prefix in (19.7) is the discrepancy
annulus from `W_*(u)` to `W_B(u)`.  It is the difference of two exterior tails: (19.6) and the
endpoint discrepancy tail.  The latter is the difference of the absolute prime tail in Theorem
17.3 and the continuum tail in Corollary 17.4, so it also tends to zero.  Thus both defects
differ by a `C_0` family.  Equation (18.1) proves (19.7).  Boundedness on the finite initial
height interval is automatic from local absolute convergence and continuity. ∎

### 19.4 Failure boundary and universal margin law

The modulus argument behind (19.3) compares

\[
 g_u(\kappa_Bu-r(u))\asymp r(u)
 \quad\text{against}\quad
 c(\kappa_Bu)^\alpha.
\]

For the canonical retreat `r(u)=L u^(1/10)`, the exact modulus exponent is

\[
 (m_BL-c\kappa_B^{1/10})u^{1/10}+o(1).
\]

Thus the available proof closes the full coefficient chamber `0<L<=L_c`.  Above `L_c` its
majorant grows; more generally it cannot close `r(u)/u^(1/10)->infinity`.  This is a sharp wall for
the available PNT modulus method, not a divergence theorem for the discrepancy current.  Theorem
17.5 separately proves genuine divergence only for unrenormalized raw cones with fixed linear
retreat.

The higher principle is general.  A source remainder

\[
 |\Theta(h)-e^h|\lesssim e^h e^{-c h^\alpha}
\]

penetrates a simple entropy--action caustic by distance `O(u^alpha)`.  A zero-free margin of scale
`(log T)^(-m)` classically produces `alpha=1/(m+1)`; the corpus exponent `m=9` therefore appears
geometrically as the new `u^(1/10)` caustic layer.  Zero-free information is not acting as a global
RH substitute here.  It pays for one precisely quantified exterior discrepancy layer and no more.

## 20. Graded Bessel cone/type phase diagram

The corpus receiver is graded: for every `lambda>=0`, growth
`O(exp(lambda u))` of the complete literal source is equivalent to the corresponding transverse
mass-displacement bound.  Bessel cone localization has an exact matching grading.

### C42-O — each vertical type has its own sharp cone

**Verdict:** proved for `0<=lambda<1/2`, with the unconditional endpoint obtained as a limit of
the formula rather than as an RH statement.

For `0<=lambda<=1/2`, define

\[
 \kappa_{a,\lambda}
 =\frac{a\sqrt{4a^2+4\lambda^2-1}-\lambda}
        {2(a^2-1/4)}.                                                \tag{20.1}
\]

Then

\[
 \frac{\kappa_{a,\lambda}}2
 -a\sqrt{\kappa_{a,\lambda}^2-1}=\lambda,                           \tag{20.2}
\]

with

\[
 \kappa_{a,0}=\kappa_B,\qquad \kappa_{a,1/2}=1.
\]

For `0<=lambda<1/2` and every `kappa>=kappa_(a,lambda)`, one has the exact graded criterion

\[
 \boxed{
 P_u^{(\kappa)}=O(e^{\lambda u})
 \iff
 \text{every transverse mass displacement has modulus at most }\lambda.
 }                                                                  \tag{20.3}
\]

At `lambda=0`, (20.3) is Theorem 17.3 and hence RH.  As `lambda` tends to `1/2`, the critical
cone slope tends to the physical light cone `kappa=1`.

The slope is sharp in the quotient by type-`lambda` families.  If
`1<kappa<kappa_(a,lambda)` and `mu>kappa`, then

\[
 \sum_{M_\kappa(u)<p\le M_\mu(u)}
 \frac{\log p}{\sqrt p}F_u(\log p)
 \ne O(e^{\lambda u}).                                              \tag{20.4}
\]

#### Proof

For any fixed `kappa>1`, the logarithmic-block proof of (17.14), without assuming a sign for
`eta_kappa`, gives

\[
 \sum_{p>M_\kappa(u)}
 \frac{\log p}{\sqrt p}|F_u(\log p)|
 \le C u^{-1/2}
 \exp\!\left[
   \left(\frac\kappa2-a\sqrt{\kappa^2-1}\right)u
 \right].                                                           \tag{20.5}
\]

The function

\[
 \Gamma_a(\kappa)=\frac\kappa2-a\sqrt{\kappa^2-1}
\]

is strictly decreasing from `1/2` to `-infinity` on `1<kappa<infinity`.  Solving
`Gamma_a(kappa)=lambda` gives (20.1).  Hence `kappa>=kappa_(a,lambda)` makes the exterior tail in
(20.5) a type-`lambda` family.

The corpus graded source theorem says that the complete literal von-Mangoldt source is
`O(e^(lambda u))` exactly when every transverse mass displacement is at most `lambda`.  Removing
valuation two and all higher valuations changes that source by a uniformly bounded family, so the
same equivalence holds for the complete valuation-one source.  Equation (20.5) then permits its
replacement by `P_u^(kappa)`, proving (20.3).

If `kappa<kappa_(a,lambda)`, then
`Gamma_a(kappa)>lambda`; in particular `kappa<kappa_B`.  Theorem 17.5 gives an annulus lower bound
`c u^(-1/2)exp(Gamma_a(kappa)u)`, which cannot be `O(exp(lambda u))`.  This proves (20.4). ∎

### 20.1 Interpretation

Source pole, zero displacements, and Bessel propagation are not separate mechanisms.  They form
one Legendre-type phase diagram:

\[
 \text{allowed vertical type }\lambda
 \quad\longleftrightarrow\quad
 \text{minimal raw cone slope }\kappa_{a,\lambda}.
\]

The continuum pole occupies `lambda=1/2`; RH occupies `lambda=0`.  Bessel action converts vertical
type into spatial aperture without loss, and Theorem 17.5 proves the conversion is coefficient
sharp.  The former strip endpoint was therefore not merely nonoptimal: it hid a complete graded
duality already latent in the corpus receiver.

## 21. Bessel prefactor budget and logarithmic caustic penetration

The preceding caustic analysis used the factor `u^(-1/2)` only to close the endpoint.  A hostile
constant audit shows that this factor is itself a spendable geometric budget.  It buys a second,
logarithmic retreat after the exponential action and the `PNTPlus` remainder have cancelled.

### C42-P — the fixed-slope caustic is also sharp under sublinear retreat

**First conjecture:** no.  The fixed-slope threshold misses a logarithmic boundary layer.

For `q>=0`, put

\[
 H_q^{\rm raw}(u)=\kappa_Bu-q\log u.
\]

Uniformly for fixed `q`, Taylor's theorem at the simple caustic gives

\[
 g_u(H_q^{\rm raw}(u))=m_Bq\log u+o(1).                            \tag{21.1}
\]

The exterior block proof of Theorem 17.3 is uniform when
`H/u -> kappa_B`.  Consequently

\[
 \sum_{\log p>H_q^{\rm raw}(u)}
 \frac{\log p}{\sqrt p}|F_u(\log p)|
 \le C_q u^{m_Bq-1/2}.                                             \tag{21.2}
\]

Hence the raw exterior tail tends to zero for `q<1/(2m_B)` and is uniformly bounded at

\[
 q_{\rm raw}=\frac1{2m_B}.                                         \tag{21.3}
\]

This endpoint is sharp for the raw source.  For every fixed `L>0`, the moving first-shell argument
from Theorem 17.5 gives

\[
 \left|\sum_{H_q^{\rm raw}(u)<\log p\le H_q^{\rm raw}(u)+L}
 \frac{\log p}{\sqrt p}F_u(\log p)\right|
 \asymp_{a,\sigma,L}u^{-1/2}e^{g_u(H_q^{\rm raw}(u))}.              \tag{21.4}
\]

Choosing `L` large makes the remaining exterior absolute tail a strict fraction of this shell.
Thus every `q>1/(2m_B)` produces a raw annulus of size at least
`c u^(m_B q-1/2)`, while at equality the annulus stays bounded away from zero along all sufficiently
large heights.  The true raw caustic therefore has a coefficient-sharp logarithmic boundary
layer, not merely a sharp linear slope.

#### Proof

On an exterior ratio neighborhood of `kappa_B`,

\[
 g_u''(h)=\frac{au^2}{(h^2-u^2)^{3/2}}=O(u^{-1}).                  \tag{21.5}
\]

Since `g_u(kappa_B u)=0` and `-g_u'(kappa_Bu)=m_B`, Taylor with retreat
`q log u` proves (21.1).  Lemma 17.2 and the logarithmic-block estimate (17.13) give (21.2).

For the reverse bound set `kappa_u=H_q^raw(u)/u`.  Then `kappa_u->kappa_B`; all root and `K_1`
asymptotics in (17.19)--(17.20) are uniform for `kappa_u` in a compact exterior interval.  The PNT
partial-summation law (17.21) is likewise uniform on a fixed logarithmic shell whose left endpoint
tends to infinity.  Its leading coefficient tends to the nonzero coefficient at `kappa_B`.
The later-shell estimate (17.23) remains uniform and gains `exp(-(a-1/2)L)`.  Fixing `L` so that
this is smaller than half the first-shell coefficient proves (21.4) and the sharpness statements.
No discrepancy sign or zero-location input is used. ∎

### C42-Q — the critical `PNTPlus` retreat has no further room

**Verdict:** false.  The same prefactor buys one more sharp logarithmic layer.

Let `alpha=1/10`, `L_c` be (19.4), and for fixed real `q,B` put

\[
 H_{q,B}(u)=\kappa_Bu-L_cu^\alpha-q\log u-B.                       \tag{21.6}
\]

Then

\[
 g_u(H_{q,B}(u))-cH_{q,B}(u)^\alpha
 =m_Bq\log u+m_BB+o(1).                                            \tag{21.7}
\]

Lemma 19.2 therefore gives the coefficient-exact envelope

\[
 \left|\int_{[H_{q,B}(u),\infty)}G_u(h)\,dE(h)\right|
 \le C_{q,B}u^{m_Bq-1/2}.                                          \tag{21.8}
\]

It vanishes for `q<1/(2m_B)` and is uniformly bounded at `q=1/(2m_B)`.  Define

\[
 H_{**}(u)=\kappa_Bu-L_cu^{1/10}-\frac{\log u}{2m_B},\qquad
 W_{**}(u)=\log(\lfloor e^{H_{**}(u)}\rfloor+1).                   \tag{21.9}
\]

After any harmless definition on a bounded initial interval,

\[
 \boxed{
 \mathrm{RH}\iff
 \sup_{u\ge0}\left|
  \int_{[0,W_{**}(u))}e^{-h/2}F_u(h)\,d(\Theta(h)-e^h)
 \right|<\infty.
 }                                                                  \tag{21.10}
\]

More generally, an arbitrary fixed additional retreat `B` in (21.6) changes only the uniform
constant.  An additional retreat `omega(u)->+infinity` makes the current modulus majorant grow by
`exp(m_B omega(u))`; this is the exact closure wall of this majorant, not a lower bound for the
actual discrepancy current.

#### Proof

Write

\[
 r(u)=L_cu^\alpha+q\log u+B.
\]

Equation (21.5) gives

\[
 g_u(\kappa_Bu-r(u))=m_Br(u)+O(r(u)^2/u).                           \tag{21.11}
\]

Because `alpha<1/2`, the error tends to zero.  The mean-value theorem also gives

\[
 (\kappa_Bu-r(u))^\alpha
 =\kappa_B^\alpha u^\alpha+O(r(u)u^{\alpha-1}),                    \tag{21.12}
\]

and this error tends to zero for the same reason.  The defining equality
`m_B L_c=c kappa_B^alpha` cancels the `u^alpha` terms, proving (21.7).  Apply (19.3) to obtain
(21.8).  Rounding from `H_(q,B)` to its logarithmic integer cutoff changes the exponent by `o(1)`.
At `q=1/(2m_B)`, (21.8) is `O(1)`.  The difference between the defect in (19.7) and the one in
(21.10) is therefore uniformly bounded, which proves their equivalent boundedness and hence
(21.10). ∎

### C42-R — Taylor expansion should produce another power correction

**Verdict:** failed, with a sharp positive survivor.  Both curvature remainders have scale

\[
 \frac{r(u)^2}{u},\qquad r(u)u^{\alpha-1}
 =O(u^{2\alpha-1}),                                                 \tag{21.13}
\]

which tends to zero because `alpha=1/10<1/2`.  There is no second growing power layer.  Once action
and PNT exponents cancel, the next nontrivial budget is exactly the logarithm of the Bessel
transport prefactor.

### 21.1 Universal prefactor-to-penetration law

Suppose a simple caustic estimate has the abstract form

\[
 T(u,H)\le Cu^{-\beta}\exp(g_u(H)-cH^\alpha),
 \qquad 0<\alpha<\frac12,
\]

with `g_u(kappa u)=0` and `-g_u'(kappa u)=m>0`.  Put
`L=c kappa^alpha/m`.  Then at

\[
 H=\kappa u-Lu^\alpha-q\log u-O(1)
\]

one has

\[
 T(u,H)=O(u^{mq-\beta}).                                           \tag{21.14}
\]

Thus exponential remainder pays the `u^alpha` layer and polynomial transport prefactor pays the
additional sharp logarithmic layer `q<=beta/m`.  For the mass/Xi kernel, `beta=1/2` and
`m=m_B`.  This three-scale budget—action, arithmetic remainder, transport prefactor—is the higher
principle hidden by the former fixed-slope and coefficient-only caustic statements.

### 21.2 Hostile audit

1. Equation (21.10) is a smaller exact RH criterion, not an RH proof; the retained timelike and
   inner spacelike prime-discrepancy current remains open.
2. Raw sharpness (21.4) does not imply discrepancy sharpness.  Subtracting continuum density may
   cancel the first shell, and current PNT input supplies no matching signed lower bound.
3. The extra logarithmic layer uses the already-proved `u^(-1/2)` kernel envelope.  It does not
   assume square-root cancellation of primes, an RH-strength zero-free region, or a numerical
   asymptotic.
4. Targeted searches across arXiv for moving modified-Bessel prime sums, Chebyshev-discrepancy
   caustics, and mass-shifted Xi traces found no collision.  The standard ingredients—PNT,
   sectorial `K_1` asymptotics, and Taylor expansion—are classical; their coefficient-exact
   caustic budget and RH-equivalent logarithmic retreat are corpus-new pending wider review.

### 21.3 Logarithmically corrected graded cones

The prefactor law applies to every grade in §20.  For `0<=lambda<1/2`, put

\[
 m_{a,\lambda}
 =\frac{a\kappa_{a,\lambda}}
        {\sqrt{\kappa_{a,\lambda}^2-1}}-\frac12>0.                 \tag{21.15}
\]

At the moving boundary

\[
 H_{\lambda,q}(u)=\kappa_{a,\lambda}u-q\log u
\]

one has

\[
 g_u(H_{\lambda,q}(u))
 =\lambda u+m_{a,\lambda}q\log u+o(1).                             \tag{21.16}
\]

Therefore Theorem 20.3 remains true with its fixed cone replaced by the smaller moving cone

\[
 H_{\lambda,*}(u)
 =\kappa_{a,\lambda}u-\frac{\log u}{2m_{a,\lambda}}+O(1).          \tag{21.17}
\]

The exterior is `O(exp(lambda u))`; below this boundary by an additional positive multiple of
`log u`, the moving coherent shell is not `O(exp(lambda u))`.  This proves a coefficient-sharp
logarithmic refinement of the whole cone/type duality.  Equation (21.3) is its `lambda=0` member.

## 22. Caustic-null mass jets and the timelike identity wall

The logarithmic budget suggests changing the test, not the source.  This loop distinguishes two
very different multiplier ideas.

### C42-S — inverse-dispersion damping creates more caustic budget

**Verdict:** failed.  Put `omega(x)=sqrt(x^2+a^2)`.  The exterior saddle at ratio `h/u=kappa>1`
has

\[
 x_\kappa=-\frac{ia\kappa}{\sqrt{\kappa^2-1}},\qquad
 \omega(x_\kappa)=\frac{ia}{\sqrt{\kappa^2-1}}.                   \tag{22.1}
\]

At `kappa=kappa_B` this is a finite nonzero number.  Multiplying the analytic test by
`omega(x)^(-r)` therefore changes only the leading constant; it does not change the
`u^(-1/2)` transport power.

**Positive survivor:** caustic improvement requires a multiplier zero at the caustic saddle, not
ordinary high-frequency damping.  This explains why the corpus damped Klein--Gordon symbols improve
time regularity but do not automatically improve the mass/Xi caustic.

### C42-T — a source-safe caustic-null jet raises the transport power

**Verdict:** proved on paper for every fixed jet order.

Put

\[
 \delta=a^2-\frac14,
 \qquad \Omega_B=2a\sqrt\delta,
 \qquad \omega_B=i\Omega_B,
 \qquad P_N(w)=(w^2+\Omega_B^2)^{2N}.                              \tag{22.2}
\]

The two roots of `P_N` are purely imaginary.  Every mass-shifted Xi point has strictly positive
real part, so

\[
 P_N(p_\rho)\ne0                                                    \tag{22.3}
\]

for every spectral point.  Define the jet-modified analytic test and its Fourier profile by

\[
 g_{N,\tau}(x)=P_N(\omega(x))e^{-\tau\omega(x)},\qquad
 F_{u,N}(h)=\int_{\mathbb R}g_{N,\sigma+iu}(x)e^{-ixh}\,dx.        \tag{22.4}
\]

For each fixed `N`, the complete trace with terms

\[
 P_N(p_\rho)e^{-(\sigma+iu)p_\rho}                                 \tag{22.5}
\]

has exactly the same vertical exponential type as the original trace.  Polynomial weights do not
alter exponential summability, and (22.3) preserves every extreme shell.  Hence boundedness or
subexponential growth of the modified trace still forces, and under RH follows from, reality of
the mass-shifted divisor.

This last assertion needs a weighted shell argument rather than a literal invocation of the
unit-weight abstract theorem.  On the least real-height shell, group equal spectral points.  Every
group has coefficient

\[
 m(p)P_N(p)e^{-\sigma p}\ne0,
\]

because its multiplicity `m(p)` is positive and (22.3) holds.  Distinct points on that shell have
distinct imaginary frequencies, so uniqueness of finite exponential polynomials prevents their
identical cancellation.  The usual shell-dominance proof then applies after absorbing the fixed
polynomial weights into the exponentially summable tail.  Conjugation is preserved because
`P_N` has real even coefficients.  Thus no cancellation or unit-weight assumption is hidden here.

The source-side reduction also survives unchanged in kind.  `P_N(omega(x))` has polynomial growth
on every legal contour, so exponential mass decay still gives all integral, contour, and
prime-power majorants.  The continuum face is the explicit bounded value

\[
 2\pi P_N\!\left(\sqrt{a^2-1/4}\right)
 e^{-(\sigma+iu)\sqrt{a^2-1/4}},                                   \tag{22.6}
\]

and valuation at least two remains uniformly bounded.  Thus the modified primitive-prime
quadrature defect is again an exact RH criterion.

At the Bessel caustic, (22.1) gives `omega(x_(kappa_B))=omega_B`.  The factor in (22.2) has an even
zero of order `2N` along the one-dimensional steepest-descent variable.  Uniform stationary
Laplace expansion therefore replaces the base transport power by

\[
 |F_{u,N}(h)|+|\partial_hF_{u,N}(h)|
 \le C_Nu^{-N-1/2}e^{-a\sqrt{h^2-u^2}}                              \tag{22.7}
\]

through every window `|h-kappa_Bu|=o(sqrt u)`.  The leading coefficient is nonzero: the linear
derivative of `omega(x)^2+Omega_B^2` at the saddle is nonzero, and the resulting even Gaussian
moment is nonzero.

The `PNTPlus` retreat `L_cu^(1/10)+O(log u)` lies inside this window.  Repeating §21 with
`beta=N+1/2` gives

\[
 \left|\int_{[H_{N,q,B}(u),\infty)}
   e^{-h/2}F_{u,N}(h)\,dE(h)\right|
 \le C_{N,q,B}u^{m_Bq-N-1/2},                                     \tag{22.8}
\]

where

\[
 H_{N,q,B}(u)=\kappa_Bu-L_cu^{1/10}-q\log u-B.                    \tag{22.9}
\]

Consequently the endpoint coefficient is

\[
 q_N=\frac{N+1/2}{m_B}.                                            \tag{22.10}
\]

The modified exact core may be cut at `H_(N,q_N,0)` with only a uniformly bounded exterior.
For every prescribed fixed `Q>0`, choosing `N` with `N+1/2>=m_BQ` gives an RH-equivalent
prime-discrepancy window retreated by

\[
 L_cu^{1/10}+Q\log u.                                               \tag{22.11}
\]

This is a genuine hierarchy of receivers, not multiplication of the final scalar trace by a
decaying normalization: the source test itself has a caustic vanishing jet, while all spectral
shell coefficients remain nonzero.

#### Proof audit of the tail estimate

For `h=kappa_Bu+o(sqrt u)`, translate the steepest-descent coordinate by the actual saddle and
scale it by `sqrt u`.  The exponent has a nondegenerate quadratic term.  The saddle displacement
from its caustic limit is `O(|h-kappa_Bu|/u+u^(-1))=o(u^(-1/2))`.
The polynomial in (22.2) is therefore `u^(-N)` times a degree-`2N` polynomial in the scaled
coordinate, plus `o(u^(-N))`.  Dominated Gaussian integration proves (22.7) with a nonzero leading
even moment.

For the complete exterior split at height `H_(N,q,B)`, the action derivative is uniformly at most
`-(a-1/2)`.  A window of width `o(sqrt u)` contains the dominant logarithmic shells and carries
the gain (22.7); beyond it, exponential action decay absorbs every fixed polynomial loss from
`P_N`.  Stieltjes integration by parts with (19.1) then proves (22.8).  Receiver and valuation
claims use only polynomial-times-exponential summability and the same legal contours as §§4--9.

### C42-U — enough fixed caustic jets remove the timelike core

**Verdict:** failed by an analytic identity wall.

On a timelike ray `h=alpha u`, `0<alpha<1`, stationary phase occurs at

\[
 x_\alpha=-\frac{a\alpha}{\sqrt{1-\alpha^2}},\qquad
 \omega(x_\alpha)=\frac{a}{\sqrt{1-\alpha^2}}.                    \tag{22.12}
\]

As `alpha` ranges through `(0,1)`, the saddle dispersion ranges through the whole interval
`(a,infinity)`.  The caustic-null polynomial (22.2) is strictly positive there, so it does not
reduce the `u^(-1/2)` timelike stationary-phase power at any ray.  More generally, a fixed
holomorphic multiplier that kills the leading saddle on every timelike ray vanishes on an
interval and is therefore identically zero.  Such a multiplier also kills the spectral receiver.

This separates boundary refinement from core solution:

- an isolated complex caustic saddle admits arbitrary finite source-safe vanishing jets;
- the timelike core is a continuum of real saddles and admits no nonzero fixed analytic annihilator.

Any multiplier route capable of controlling the remaining core must therefore be cofinal or
growing-degree, with a condition-number/boundary-flux theorem strong enough to preserve every
spectral shell.  This recovers the precise Band--Kaiser synthesis obligation from a new saddle
geometry: fixed-rank packets can shave boundary jets, while only controlled cofinal rank could act
on the timelike velocity continuum.

### 22.1 Scientific boundary

The caustic-jet hierarchy is paper-proved but not Lean-formalized; current corpus refactor forbids
Lean edits in this pass.  It reduces the exterior proof burden by every fixed logarithmic amount
and proves a new fixed-multiplier no-go for the remaining bulk.  It does not provide the required
cofinal multiplier, its conditioning law, or the final RH proof.

## 23. Type-zero collapse of every sublinear caustic layer

The newest graded spectral theorem changes the correct target topology.  Uniform boundedness is
sufficient for RH but not necessary as a proof hypothesis: the corpus theorem
`AbstractSpectralFamily.im_eq_zero_of_subexponential` proves that subexponential growth on a fixed
vertical line already forces every displacement to vanish.

### C42-V — the bounded exact core is the minimal RH obligation

**Verdict:** false.  It is the minimal representative in the bounded quotient, but RH only needs
the weaker type-zero quotient.

Call a height family `A(u)` type zero on the positive ray if

\[
 \forall\varepsilon>0\ \exists C_\varepsilon<\infty\ \forall u\ge0,
 \qquad |A(u)|\le C_\varepsilon e^{\varepsilon u}.                 \tag{23.1}
\]

All moving-boundary formulae below are asserted for `u>=2`; changing a family on the compact
initial interval `0<=u<2` only enlarges `C_epsilon` and never changes type zero.  This also removes
the harmless `log u` and ratio-at-zero conventions in §§21--23.

Let `H(u)` be any eventually exterior moving boundary satisfying

\[
 \frac{H(u)}u\longrightarrow\kappa_B.                             \tag{23.2}
\]

The boundary may approach from either side.  In particular,

\[
 H(u)=\kappa_Bu-r(u),\qquad r(u)=o(u),                             \tag{23.3}
\]

is allowed with no sign, monotonicity, or power-law assumption on `r`.  Put

\[
 M_H(u)=\lfloor e^{H(u)}\rfloor,
 \qquad
 P_H(u)=\sum_{p\le M_H(u)}\frac{\log p}{\sqrt p}F_u(\log p).       \tag{23.4}
\]

Then

\[
 \boxed{
 \mathrm{RH}\iff P_H\text{ has type zero on }u\ge0.
 }                                                                  \tag{23.5}
\]

With `W_H(u)=log(M_H(u)+1)`, the same is true for the quadrature defect:

\[
 \boxed{
 \mathrm{RH}\iff
 \int_{[0,W_H(u))}e^{-h/2}F_u(h)\,d(\Theta(h)-e^h)
 \text{ has type zero.}
 }                                                                  \tag{23.6}
\]

Thus the exact RH core may be shortened by **every** sublinear retreat from the Bessel caustic,
not only `u^(1/10)` and logarithmic layers.  No `PNTPlus` error is needed for this type-zero
reduction.

#### Proof

Choose fixed `kappa_0` with `1<kappa_0<kappa_B`.  Equation (23.2) gives
`H(u)>=kappa_0u` eventually.  The exterior logarithmic-block estimate used in (20.5), now with the
moving ratio `kappa(u)=H(u)/u`, is uniform on a compact neighborhood of `kappa_B` and gives

\[
 \sum_{\log p>H(u)}\frac{\log p}{\sqrt p}|F_u(\log p)|
 \le Cu^{-1/2}\exp\!\left(u\Gamma_a(H(u)/u)\right).                \tag{23.7}
\]

Continuity of `Gamma_a` and `Gamma_a(kappa_B)=0` imply

\[
 \frac1u\log^+\!\left(
 \sum_{\log p>H(u)}\frac{\log p}{\sqrt p}|F_u(\log p)|
 \right)\longrightarrow0.                                        \tag{23.8}
\]

Hence the exterior raw prime tail is type zero.  The complete valuation-one source and `P_H`
differ by this tail.  Valuation at least two and the archimedean face are uniformly bounded, so
the complete literal source has type zero exactly when `P_H` does.  Vertical conjugation reduces
the two-sided hypothesis to `u>=0`.  The corpus graded rigidity theorem then gives RH from type
zero; under RH the complete trace is bounded, and subtracting the type-zero tail makes `P_H` type
zero.  This proves (23.5).

The finite Stieltjes identity (9.1) writes `P_H` as the defect in (23.6) plus a continuum prefix.
The complete continuum integral is uniformly bounded by contour-shift evaluation.  Its exterior
tail from `H(u)` has the same Bessel action estimate as (23.7), without prime entropy, and is
therefore type zero.  Hence the continuum prefix is type zero.  The two families in (23.5)--(23.6)
differ by a type-zero family, proving their equivalent type-zero status and (23.6). ∎

### C42-W — use `PNTPlus` and caustic jets to optimize the type-zero core

**Verdict:** unnecessary for RH, though still meaningful for bounded cohomology.  If
`r(u)=L_cu^(1/10)+Q log u`, §§21--22 can make the exterior bounded.  But (23.7) shows that every
`r=o(u)` already makes it type zero.  Optimizing `L_c`, `Q`, or jet order does not further weaken
the spectral hypothesis needed for RH.

**Positive survivor:** the route has two distinct quotient geometries.

1. **Bounded quotient.**  Representatives are identified modulo `O(1)`.  `PNTPlus`, Bessel
   prefactors, and caustic-null jets produce real coefficient-sharp movement here.
2. **Type quotient.**  Representatives are identified modulo `exp(o(u))`.  Every asymptotically
   caustic boundary is the same class, and RH asks only that this class have type zero.

The former is finer; the latter is the correct minimal target for proving RH.  Earlier insistence
on a uniform bound made sublinear boundary layers look like core obstacles when they are invisible
to the actual spectral rigidity theorem.

### 23.1 Revised exact open core

Choose one explicit aggressive sublinear retreat, for example

\[
 H_\dagger(u)=\kappa_Bu-\frac{u}{\log(u+e)}.                       \tag{23.9}
\]

This deletes much more than every fixed power `u^alpha`, `alpha<1`, while preserving
`H_dagger(u)/u->kappa_B`.  The remaining hard theorem is now:

\[
 \forall\varepsilon>0\ \exists C_\varepsilon:
 \left|\int_{[0,W_\dagger(u))}e^{-h/2}F_u(h)\,d(\Theta(h)-e^h)\right|
 \le C_\varepsilon e^{\varepsilon u}.                             \tag{23.10}
\]

This is strictly weaker than the former uniform bound and retains no arbitrary bounded-caustic
constant.  It remains RH-strength: assuming (23.10) and applying (23.6) proves RH, while no current
corpus theorem proves (23.10).

## 24. Hostile closure of three false type-zero transfers

The weaker target (23.10) makes several older inputs look stronger than they are.  This section
tests them at exponential-type resolution rather than bounded resolution.

### C43-A — integral Lipschitz plus `PNTPlus` gives type zero

**Verdict:** failed; the scalar quotient and light-cone rate both survive.

The actual integral theorem

\[
 |F_u(v)-F_u(w)|\le J_1(\sigma)|v-w|                             \tag{24.1}
\]

is uniform in `u` and proves every adjacent-prime frequency coboundary bounded.  But exact Abel
summation reconstructs the scalar source with cumulative weights, not the adjacent critical
weights.  After continuum subtraction this cumulative coordinate is precisely the normalized
Chebyshev error.  Thus using (24.1) globally gives the already-known Stieltjes formula, not a new
estimate; the one-dimensional scalar quotient proved in C38 remains.

There is also a rate obstruction.  On every fixed timelike ray `h=alpha u`, `0<alpha<1`, the
`PNTPlus` absolute envelope in the centered current has exponential part

\[
 \exp\!\left(\frac{\alpha u}{2}-c(\alpha u)^{1/10}\right).       \tag{24.2}
\]

Letting `alpha` tend to one leaves type `1/2`.  Bessel oscillation is discarded by a Lipschitz or
total-variation estimate, so no argument consuming only (24.1) and the pointwise `PNTPlus` envelope
can certify type zero.  This is sharp as a method statement: a positive continuum measure may be
perturbed on disjoint timelike windows by a real signed density of size
`exp(h-c h^(1/10))`, with sign chosen from one of four phase quadrants.  It obeys the same PNT
envelope and retains positivity because the perturbation is `o(exp h)`, while its selected current
has the rate (24.2).  Prime discreteness or a new signed correlation law is therefore essential.

### C43-B — Selberg recursion contracts the mass current to type zero

**Verdict:** failed by a spectral-resolution mismatch; a Jordan-floor survivor remains.

Write

\[
 (T_0R)(X)=\sum_{d\le X}R(\lfloor X/d\rfloor).
\]

The corpus proves the exceptional critical-scale estimate

\[
 T_0R(X)+2\gamma X=O(\sqrt X).                                  \tag{24.3}
\]

For the continuous Mellin model, however, `T_0` has symbol `zeta(s)`.  Hence a hypothetical power
mode `X^rho` attached to a zeta zero is annihilated at leading order.  The square-root estimate is
strong exactly where its multiplier is blind.  The Tatuzawa--Iseki and second-Selberg estimates
differentiate or invert this relation only with an `O(X polylog X)` budget.  Every mode
`X^beta`, `beta<1`, lies below that resolution, whereas the mass receiver distinguishes the much
finer exponent `beta-1/2`.

The positive survivor is an exact Jordan hierarchy.  For `k>=0` define the logarithmically lifted
floor transform, initially on a continuous step profile supported on `[1,infinity)`, by

\[
 (T_kR)(X)=\sum_{d\le X}(\log d)^kR(\lfloor X/d\rfloor).          \tag{24.4}
\]

With Mellin convention

\[
 \widehat R(s)=\int_1^\infty R(X)X^{-s-1}\,dX,
\]

Tonelli on a right half-plane and the substitution `X=dy` give the exact symbol law

\[
 \widehat{T_kR}(s)=(-1)^k\zeta^{(k)}(s)\widehat R(s).             \tag{24.5}
\]

If `rho` is a zeta zero of multiplicity `m`, the multiplier in (24.5) vanishes for `k<m` but not
for `k=m`.  The zero mode killed by (24.3) is therefore exposed by its first nonzero Jordan lift.
After subtracting the explicit polar polynomial from each `T_kR`, the source theorem

\[
 \forall k\ \forall\varepsilon>0:\qquad
 \widetilde T_kR(X)=O_{k,\varepsilon}(X^{1/2+\varepsilon})        \tag{24.6}
\]

would force RH: (24.6) makes every lifted Mellin transform holomorphic in `Re(s)>1/2`; at an
off-line zero of multiplicity `m`, (24.5) with `k=m` retains the pole of the Chebyshev-error
transform, a contradiction.  Functional-equation reflection handles the opposite half-plane.

Equation (24.6) is not present in the corpus.  Only `k=0` has the square-root budget; the available
log-weighted Tatuzawa combination costs order `X`.  Consequently (24.6) is a genuine new
source-side avenue but not a disguised completed proof.  To remain on the mass route, it must be
used through an adjoint factorization of the outgoing Bessel current; proving (24.6) directly by
critical zeta inversion would merely restate RH.

A shifted version exposes the same condition-number wall.  The weighted transform

\[
 T_tR(X)=\sum_{d\le X}d^{-t}R(\lfloor X/d\rfloor)                \tag{24.7}
\]

has symbol `zeta(s+t)`, which is nonzero at every critical-strip zero when `t=1`.  But comparison
with `T_0` using only `|R(X)|=O(X)` costs

\[
 T_tR-T_0R=O(tX\log^2X).                                        \tag{24.8}
\]

At a zero of multiplicity `m`, the recovered multiplier is only `O(t^m)`.  Subtracting `m-1`
Taylor jets and dividing by `t^m` turns the source remainder back into
`O(X polylog X)`.  Small-shift regularization therefore cannot manufacture the missing critical
bound; the inverse condition number restores exactly the Selberg resolution wall.

The fixed shift `t=1` nevertheless has a stronger positive survivor.  For an arithmetic weight
`a` define the floor transform

\[
 (\mathsf T_a f)(N)=\sum_{d\le N}a(d)f(\lfloor N/d\rfloor).       \tag{24.9}
\]

Floor associativity and finite hyperbola regrouping give

\[
 \mathsf T_a\mathsf T_b=\mathsf T_{a*b}.                         \tag{24.10}
\]

Put `a(d)=1/d` and `b(d)=mu(d)/d`.  Their Dirichlet convolution is the unit, because

\[
 (a*b)(n)=\frac1n\sum_{d\mid n}\mu(d)=\mathbf1_{n=1}.            \tag{24.11}
\]

Hence the harmonic floor average

\[
 Q(N)=\sum_{d\le N}\frac1dR(\lfloor N/d\rfloor)                 \tag{24.12}
\]

has the exact, critically stable inverse

\[
 R(N)=\sum_{d\le N}\frac{\mu(d)}dQ(\lfloor N/d\rfloor).         \tag{24.13}
\]

Indeed, if `Q(N)=O_epsilon(N^(1/2+epsilon))`, then

\[
 |R(N)|\le C_\varepsilon N^{1/2+\varepsilon}
 \sum_{d\ge1}d^{-3/2-\varepsilon}.                              \tag{24.14}
\]

Conversely the same estimate for `R` implies it for `Q` by the identical convergent majorant.
Thus the critical estimates for `Q` and `R` are equivalent by finite floor algebra and an
absolutely convergent majorant.  Classical generalized von Koch then identifies them with RH.  For
this route the sufficient implication is also direct and corpus-native: after critical
normalization the `R` estimate is `e^(-h/2)|R(floor(e^h))|<=C_delta e^(delta h)`.  Shift the actual
mass Fourier kernel by any depth `d` with `delta<d<a`; its outgoing norm is
`O(exp(d u-d h))`.  The complete current is therefore `O(exp(d u))`.  Taking `d` arbitrarily
small gives type zero and invokes (23.6), without zeta inversion.  Hence (23.10) and

\[
 \forall\varepsilon>0:\quad Q(N)=O_\varepsilon(N^{1/2+\varepsilon})
                                                                        \tag{24.15}
\]

are equivalent RH-strength source obligations.  Unlike ordinary floor inversion, (24.13) never
divides by `zeta(s)` on the critical strip: its inverse coefficients gain `d^(-3/2)` after critical
normalization.  This is an exact new avenue for the mass current.  Substitution of (24.13) into the
outgoing current produces translated Bessel kernels with absolutely summable coefficients
`mu(d)/d^(3/2)`.  Missing theorem is now a critical bound for the positive-weight harmonic floor
average `Q`, or a direct type-zero bound for its translated outgoing current.  Existing harmonic
remainder theorem has weight `1/n-1/(n+1) asymp 1/n^2`; after floor-fibre regrouping (24.12) has
weight `asymp 1/n`.  It is one full logarithmic primitive stronger, so the corpus does not yet
prove (24.15).

There is an exact maximal-floor form of that missing primitive.  For `1<=D<=N` put

\[
 A_N(D)=\sum_{d\le D}R(\lfloor N/d\rfloor),
 \qquad B_N(D)=A_N(D)+2\gamma D.                                 \tag{24.16}
\]

Discrete Abel summation gives

\[
 Q(N)=\frac{A_N(N)}N+
 \sum_{D<N}A_N(D)\left(\frac1D-\frac1{D+1}\right).              \tag{24.17}
\]

The polar coordinate telescopes exactly, so with `H_N=sum_(j<=N)1/j`,

\[
 Q(N)+2\gamma H_N
 =\frac{B_N(N)}N+
 \sum_{D<N}B_N(D)\left(\frac1D-\frac1{D+1}\right).              \tag{24.18}
\]

The corpus square-root theorem is precisely the endpoint estimate

\[
 |B_N(N)|\le24\sqrt N.                                          \tag{24.19}
\]

Therefore either of the genuinely stronger source statements

\[
 \sup_{1\le D\le N}|B_N(D)|=O_\varepsilon(N^{1/2+\varepsilon})  \tag{24.20}
\]

or merely

\[
 \sum_{D<N}|B_N(D)|\left(\frac1D-\frac1{D+1}\right)
 =O_\varepsilon(N^{1/2+\varepsilon})                             \tag{24.21}
\]

proves (24.15), hence the type-zero mass core.  This is the **maximal Tatuzawa--Iseki gate**:
extend one already-proved square-root endpoint to its harmonic path average.  Hostile check shows
why current window theorems do not do it.  Grouping `A_N(D)` by floor fibres replaces counts by
`N(1/m-1/(m+1))` only up to discontinuous floor errors; termwise control of those errors costs
order `N`.  The signed harmonic remainder theorem bounds a full `m`-window, but (24.21) needs the
coupled two-parameter signs of those floor errors.  Claiming (24.20) from the existing one-parameter
window bound would therefore be false.

### C43-C — generalized Dirichlet mean square controls every core height

**Verdict:** failed at local type-zero scale; positive aperture law extracted.

The new generalized Dirichlet mean-value theorem gives exact diagonal/off-diagonal separation for
arbitrary real frequencies.  For prime logs below height `H`, elementary integer separation gives

\[
 \min_{p\ne q\le e^H}|\log p-\log q|\gg e^{-H},                 \tag{24.22}
\]

while the number of frequencies is of order `e^H/H`.  The corpus uniform-gap Gram bound therefore
requires an observation aperture at least of order

\[
 U_H\gg \frac{\#\{p\le e^H\}}{\min|\log p-\log q|}
 \asymp \frac{e^{2H}}H                                         \tag{24.23}
\]

to obtain coefficient-uniform almost orthogonality.  At the mass caustic `H asymp u`, this aperture
is exponential in the vertical parameter.  Passing from such a global mean to a local value pays
an exponential constant and cannot prove `exp(o(u))` control.  Prime-log linear independence and
finite-type uniqueness therefore give injectivity but no type-zero-stable sampling inverse.

### C43-D — weighted-floor critical threshold and exact reciprocal-sawtooth gate

**Verdict:** general stable-coordinate idea closes as a no-go; exact two-parameter prime correlation
survives.

The harmonic choice in (24.12) belongs to a full weighted-floor family.  For `theta>=0`, define

\[
 Q_\theta(N)=(\mathsf T_{n^{-\theta}}R)(N)
 =\sum_{d\le N}d^{-\theta}R(\lfloor N/d\rfloor).                \tag{24.24}
\]

Finite floor associativity is exact for real weights.  Since
`n^(-theta)` and `mu(n)n^(-theta)` have Dirichlet convolution equal to the unit,

\[
 R(N)=\sum_{d\le N}\mu(d)d^{-\theta}
 Q_\theta(\lfloor N/d\rfloor).                                 \tag{24.25}
\]

This family has a sharp threshold at `theta=1/2` in the critical type topology.  If
`Q_theta(M)=O_epsilon(M^(1/2+epsilon))`, then (24.25) and `|mu(d)|<=1` give

\[
 |R(N)|\le C_\varepsilon N^{1/2+\varepsilon}
 \sum_{d\ge1}d^{-\theta-1/2-\varepsilon}.                       \tag{24.26}
\]

The same calculation in the forward direction omits `mu`.  Consequently, for every
`theta>=1/2`,

\[
 N^{-1/2}Q_\theta(N)\text{ has type zero}
 \quad\Longleftrightarrow\quad
 N^{-1/2}R(N)\text{ has type zero}.                              \tag{24.27}
\]

Endpoint `theta=1/2` is legal because the extra `d^(-epsilon)` makes the harmonic majorant
summable for each fixed positive `epsilon`.  The threshold is sharp as an operator statement:
for the model `f(N)=sqrt(N)`, elementary comparison on `d<=N/2` gives

\[
 N^{-1/2}(\mathsf T_{n^{-\theta}}f)(N)\asymp
 \begin{cases}
 N^{1/2-\theta},&0\le\theta<1/2,\\
 \log N,&\theta=1/2,\\
 1,&\theta>1/2.
 \end{cases}                                                     \tag{24.28}
\]

Thus ordinary Tatuzawa--Iseki transform `theta=0` lies exactly one-half type below the
invertibility threshold.  Its unconditional square-root endpoint is compatible with a source of
type `1/2` because inversion must repay that missing half-type.  Every `theta>=1/2` is stably
invertible at type zero and therefore cannot, by itself, lower RH proof burden.  In particular,
harmonic coordinate (24.12) is a useful mass-compatible preconditioner, not smoothing that creates
a new estimate.

The apparent discontinuous floor error in (24.21) nevertheless has more structure than the crude
order-`N` audit sees.  Fix `1<=D<N` and put

\[
 M=\left\lfloor\frac{N}{D+1}\right\rfloor,\quad
 \alpha_m=\left\{\frac Nm\right\},\quad
 \eta=D-\left\lfloor\frac{N}{M+1}\right\rfloor,\quad
 S_M=\sum_{m\le M}R(m)\left(\frac1m-\frac1{m+1}\right).          \tag{24.29}
\]

The quotient fibre of `m` has size

\[
 c_m=\left\lfloor\frac Nm\right\rfloor-
 \left\lfloor\frac N{m+1}\right\rfloor
 =N\left(\frac1m-\frac1{m+1}\right)+\alpha_{m+1}-\alpha_m.
\]

All tail fibres below `M` are complete and the `M`-fibre misses exactly `eta` points.  Discrete
summation by parts, `alpha_1=0`, and
`R(m)-R(m-1)=Lambda(m)-1` therefore give the exact identity

\[
 \sum_{d>D}R(\lfloor N/d\rfloor)
 =NS_M+R(M)(\alpha_{M+1}-\eta)
 -\sum_{m=2}^{M}(\Lambda(m)-1)\alpha_m.                          \tag{24.30}
\]

Substitution into (24.16) yields

\[
 \begin{aligned}
 B_N(D)={}&B_N(N)-N(S_M+2\gamma)
 +\sum_{m=2}^{M}(\Lambda(m)-1)\left\{\frac Nm\right\}\\
 &+(\eta-\alpha_{M+1})R(M)+2\gamma D.                           \tag{24.31}
 \end{aligned}
\]

This replaces a fictitious sum of `M` independent floor errors by one exact reciprocal-clock
correlation.  Its variation error is only
`|R(M)|+sum_(m<=M)|Lambda(m)-1|=O(M)`, not `O(M^2)`.  But (24.31) also prevents a false closure:
the `N(S_M+2 gamma)` term and reciprocal-sawtooth correlation cancel at the same critical scale.
Bounding them separately with `PNTPlus` retains type `1/2`; bounding their combination at the
strength required by (24.21) is new RH-strength content.  Actual mass-Fourier Lipschitz control
does not see this term because it is smooth in prime-log frequency, whereas `m -> {N/m}` is
discontinuous in the transverse reciprocal clock.

Strongest non-circular survivor is therefore the **reciprocal-sawtooth mass gate**: after inserting
(24.31) into (24.18), prove type-zero cancellation for the coupled `(N,D,m)` average without taking
absolute values before the harmonic `D`-sum.  This is more precise than asking for overstrong
supremum (24.20), and identifies which signed two-clock statistic a source theorem must control.

A final anchoring check prevents over-selling fractional-part structure.  Because `R(0)=0` and

\[
 R(k)=\sum_{m\le k}(\Lambda(m)-1),
\]

finite Fubini gives the exact triangular transport identity

\[
 \sum_{d>D}R(\lfloor N/d\rfloor)
 =\sum_{m\le M}(\Lambda(m)-1)
   \left(\left\lfloor\frac Nm\right\rfloor-D\right).             \tag{24.32}
\]

Indeed, for fixed `m<=M`, number of `d>D` with `m<=floor(N/d)` is exactly
`floor(N/m)-D`.  Hence (24.31) is equivalent to simpler formula

\[
 B_N(D)=B_N(N)
 -\sum_{m\le M}(\Lambda(m)-1)
   \left(\left\lfloor\frac Nm\right\rfloor-D\right)
 -2\gamma(N-D).                                                   \tag{24.33}
\]

Thus sawtooth is a coordinate description of one triangular hyperbola transport, not an
independent source of cancellation.  Existing corpus transport bounds do not control (24.33):
they take absolute displacement after a bounded-displacement matching, while (24.33) needs signed
`Lambda-1` mass and displacements ranging up to `N-D`.  Absolute application costs order
`N log M`; critical monotone-clock transport has the same scale-loss after this unbounded test.
The correctly centered path defect is the transport in (24.33) plus `2 gamma(N-D)`.  A tempting
surviving obligation is type-zero control of its harmonic signed `D`-average.  C43-F below audits
whether that projection is genuinely reduced.

### C43-E — critical floor Wiener-class closure

**Verdict:** proved general no-go; all subpower-conditioned scalar floor transforms preserve the
open core.

Power weights are not special.  For an arithmetic weight `a : N -> C`, define its truncated
critical condition number

\[
 \|a\|_{1/2;N}=\sum_{d\le N}\frac{|a(d)|}{\sqrt d}.              \tag{24.34}
\]

Call `a` **critically subpower** when, for every `epsilon>0`,
`||a||_(1/2;N)=O_epsilon(N^epsilon)`.  Suppose `a*b=delta_1` and both `a` and `b` are critically
subpower.  Then floor associativity gives `T_a T_b=T_b T_a=Id`.  If
`f(M)=O_delta(M^(1/2+delta))`, choose `delta=epsilon/2`; then

\[
 \begin{aligned}
 |(\mathsf T_a f)(N)|
 &\le C_\delta N^{1/2+\delta}
   \sum_{d\le N}|a(d)|d^{-1/2-\delta}\\
 &\le C_\delta N^{1/2+\delta}\|a\|_{1/2;N}
 =O_\varepsilon(N^{1/2+\varepsilon}).                           \tag{24.35}
 \end{aligned}
\]

Apply same estimate to `b` for reverse implication.  Therefore

\[
 N^{-1/2}\mathsf T_a f(N)\text{ has type zero}
 \quad\Longleftrightarrow\quad
 N^{-1/2}f(N)\text{ has type zero}.                              \tag{24.36}
\]

This **critical floor Wiener lemma** contains (24.27): for `a(n)=n^(-theta)`, critical norm is
bounded for `theta>1/2`, logarithmic at `theta=1/2`, and has positive power
`N^(1/2-theta)` below threshold.  It also contains every finite or cofinal Dirichlet filter for
which both filter and convolution inverse have subpower critical absolute conditioning.  This
qualification is essential: even a finite filter can have inverse coefficients with positive-power
critical growth.

Hence a scalar floor transform can reduce proof burden only by leaving this class.  Ordinary
Tatuzawa--Iseki weight `a=1` does leave it, with critical norm `asymp sqrt(N)`; its Möbius inverse
has same absolute condition.  Replacing absolute conditioning by signed
`sum_(d<=N)mu(d)/sqrt(d)=N^o(1)` would restore critical stability, but that signed estimate is itself
RH-strength.  This closes the entire route “find a better well-conditioned scalar floor average”:
subpower conditioning is information preservation, while stronger smoothing necessarily incurs
positive critical type unless a new arithmetic cancellation theorem pays for inverse.

### C43-F — harmonic triangular projection collapses exactly to original core

**Verdict:** proved exact collision; signed harmonic transport is a coordinate identity, not a
reduction.

Put `a_m=Lambda(m)-1`, `q_m=floor(N/m)`, and

\[
 T_N(D)=\sum_{m\le \lfloor N/(D+1)\rfloor}a_m(q_m-D),\qquad
 w_D=\frac1D-\frac1{D+1}.                                      \tag{24.37}
\]

For fixed `m`, its contribution occurs exactly for `1<=D<=q_m-1`.  The inner harmonic projection
has closed form

\[
 \sum_{D=1}^{q-1}(q-D)w_D=q-H_q.                                \tag{24.38}
\]

Finite Fubini gives two exact identities:

\[
 \sum_{m\le N}a_mq_m=A_N(N)
   =\log(N!)-\sum_{n\le N}\tau(n),\qquad
 \sum_{m\le N}a_mH_{q_m}=Q(N).                                 \tag{24.39}
\]

Indeed first sum counts divisor pairs and uses `sum_(m|n)Lambda(m)=log n`; in second, expanding
`H_(q_m)` and reversing sums leaves `sum_(d<=N)R(floor(N/d))/d`.  Consequently

\[
 \sum_{D<N}w_DT_N(D)=A_N(N)-Q(N)
   =B_N(N)-2\gamma N-Q(N).                                     \tag{24.40}
\]

Thus uncentered transport has deterministic linear harmonic drift.  Define genuinely centered
defect

\[
 C_N(D)=T_N(D)+2\gamma(N-D)=B_N(N)-B_N(D).
\]

Since `sum_(D<N)(N-D)w_D=N-H_N`, (24.40) becomes

\[
 \boxed{\displaystyle
 \sum_{D<N}w_DC_N(D)=B_N(N)-Q(N)-2\gamma H_N.}                  \tag{24.41}
\]

Endpoint bound (24.19) and `H_N=O(log N)` prove left side of (24.41) has critical type zero if and
only if `Q(N)` does.  By (24.13)--(24.15), this is exactly original RH source obligation.  Harmonic
projection performs no cancellation work beyond renaming `Q`.

There is still a nonlinear pre-projection object, but it gives no free energy estimate.  If

\[
 K(q,r)=\sum_{D<\min(q,r)}(q-D)(r-D)w_D,
\]

then, writing `ell=min(q,r)` and `v=max(q,r)`, elementary telescoping gives

\[
 K(q,r)=\ell v+2\ell-(\ell+v+1)H_\ell.                         \tag{24.42}
\]

With `c_1=2γ-1` and `c_m=Lambda(m)-1` for `m>=2`, exact centered path energy is

\[
 \sum_{D<N}w_D C_N(D)^2
   =\sum_{m,n\le N}c_mc_nK(q_m,q_n).                            \tag{24.43}
\]

Kernel is positive semidefinite by construction, but diagonal estimate is catastrophic: each
fixed low-`m` diagonal is order `N^2`, while true path requires cross-term cancellation across
whole source.  Moreover `D=1` term already contains
`C_N(1)=B_N(N)-(R(N)+2γ)`.  Hence an `O_epsilon(N^(1+epsilon))` bound for (24.43), together with
(24.19), directly implies RH-quality bound for `R(N)`.  Quadratic positivity does not reduce burden
either; only a new source-specific proof of its cross cancellation would advance route.

### C43-G — superluminal causal compression retains full radiation type

**Conjecture.**  Because the arithmetic source is supported on positive logarithmic time, compress
the critically gauged half-wave to the causal Hardy subspace and discard the amplified radiation
end.

**Verdict:** failed, with a sharp positive survivor.  Causality can evacuate an amplified packet
only if source aperture does not outrun light speed.  Every superluminal aperture retains exact
full-space radiation norm.

Let `F` be the unitary Fourier transform with
`F f(xi)=integral exp(-i h xi) f(h) dh`, let

\[
 \omega_{a,\lambda}(\xi)=\sqrt{(\xi-i\lambda)^2+a^2},\qquad
 m_u(\xi)=e^{-iu\omega_{a,\lambda}(\xi)},
\]

and put `U_u=F^(-1) M_(m_u) F`.  For `H>0`, let `P_H` be multiplication by the indicator of
`(0,H)`.  Corpus radiation laws give, for `0<lambda<a` and `u>=0`,

\[
 |m_u(\xi)|\le e^{\lambda u},\qquad
 \omega_{a,\lambda}(\xi)+\xi\longrightarrow i\lambda
 \quad(\xi\to-\infty).                                        \tag{24.44}
\]

We claim the exact causal-compression law

\[
 \boxed{\displaystyle
 H>u\ge0\quad\Longrightarrow\quad
 \|P_HU_uP_H\|_{L^2(\mathbb R)\to L^2(\mathbb R)}=e^{\lambda u}.}
                                                                    \tag{24.45}
\]

At `u=0` this is immediate.  Suppose `H>u>0` and choose nonzero
`phi in C_c^infty((u,H))`, normalized in `L^2`.  For `R>0` set
`phi_R(h)=exp(-iRh)phi(h)`.  Then

\[
 \widehat{\phi_R}(\xi)=\widehat\phi(\xi+R).
\]

After changing variable `eta=xi+R`, (24.44) gives pointwise

\[
 m_u(\eta-R)-e^{\lambda u}e^{iu(\eta-R)}\longrightarrow0.
\]

Both terms have modulus at most `e^(lambda u)`, so dominated convergence against
`|hat(phi)(eta)|^2`, followed by Plancherel, proves

\[
 \|U_u\phi_R-e^{\lambda u}\phi_R(\,\cdot+u)\|_2\longrightarrow0. \tag{24.46}
\]

The input is supported in `(u,H)`, while translated limit in (24.46) is supported in
`(0,H-u)`, hence both are fixed by `P_H`.  Contractivity of `P_H` gives lower bound
`||P_H U_u P_H||>=e^(lambda u)`; full-space bound in (24.44) gives reverse inequality.  This proves
(24.45) without Hardy factorization, spectral support assumptions, or asymptotic norm heuristics.

The same proof with any compact interval inside `(u,infinity)` gives

\[
 \|P_+U_uP_+\|=e^{\lambda u},                                  \tag{24.47}
\]

where `P_+` is causal half-line projection.  Thus half-line support is not corona polarization.
The amplified negative-frequency packet is an outgoing translation to left, but a cofinal source
can place it beyond distance `u`, so it remains causal after propagation.

Actual Xi mass test also has fixed real-time damping.  Put

\[
 s_{\sigma,u}(\xi)=e^{-(\sigma+iu)\omega_{a,\lambda}(\xi)},
 \qquad S_{\sigma,u}={\cal F}^{-1}M_{s_{\sigma,u}}{\cal F}.
                                                                    \tag{24.48}
\]

This changes exact norm but not exponential type after causal compression.  For every
`sigma>0`, `kappa>1`, and `0<lambda<a`,

\[
 \boxed{\displaystyle
 \lim_{u\to\infty}\frac1u
  \log\|P_{\kappa u}S_{\sigma,u}P_{\kappa u}\|=\lambda.}       \tag{24.49}
\]

Here is a dependency-closed wave-packet proof.  Uniformly for `eta` in a fixed compact set and
`r` tending to infinity, principal-square-root expansion gives

\[
 \omega_{a,\lambda}(\eta-r)
 =r-\eta+i\lambda+\frac{a^2}{2(r-\eta+i\lambda)}+O(r^{-3}).    \tag{24.50}
\]

Choose `1/2<q<1`, `r=u^q`, and `1<c<kappa`.  Let `hat(psi)` be a nonzero smooth function of compact
frequency support and place corresponding modulated physical packet at `cu`:
`f_u(h)=exp(-irh)psi(h-cu)`.  Its frequency support is a fixed-width interval about `-r`.
Formula (24.50) shows `S_(sigma,u)f_u` is, up to relative `L^2` error tending to zero, a fixed
band-limited profile translated left by `u`, times scalar of logarithmic modulus

\[
 \lambda u-\sigma u^q+O(u^{1-2q})+O(1)=\lambda u-o(u).         \tag{24.51}
\]

Input center `cu` and output center `(c-1)u` stay a linear distance from both endpoints of
`(0,kappa u)`.  Schwartz tails therefore make both causal projections asymptotically invisible,
which proves lower exponential rate `lambda`.  Upper rate follows from
`Re omega>=0` and `|Im omega|<lambda`.

Same packet proves (24.49) after applying actual outgoing factor `1/2-partial_h`: on packet it adds
factor of size `asymp r`, whose logarithm is `O(log u)=o(u)`.  Conversely corpus inequality
`Re omega>|xi|`, fixed `sigma>0`, bounds
`(1+|xi|)exp(-sigma Re omega)` uniformly, so upper rate remains `lambda`.  Thus neither analytic
real-time smoothing nor outgoing Volterra adjoint lowers critical type on superluminal causal
cone.

This has an exact collision with both corpus localizations.  The elementary outgoing cone uses

\[
 H_d(u)=\frac{d}{d-1/2}u>u,
\]

and sharp Bessel aperture uses

\[
 H(u)\sim\kappa_Bu,\qquad
 \kappa_B=\frac{a}{\sqrt{a^2-1/4}}>1.                           \tag{24.52}
\]

Therefore both exact RH cores live strictly in regime (24.45).  Conversely, raw-source exterior
control by Bessel action requires asymptotic slope at least `kappa_B`; a subluminal aperture cannot
meet it.  No support-only Hardy/Wiener--Hopf estimate can simultaneously evacuate amplified corona
and discard prime tail.  A successful causal theorem must use source-specific signed cancellation
inside superluminal strip, not causal projection or compressed operator norm alone.

Read-only audit of newest causal modules does not change this frontier.  The explicit theta
square-rate reader is genuinely causal, but its direct reflected-theta action is Lean-proved
identically zero and its prior RH route is retired; it has no map to centered `Lambda-1` source.
The repaired Xi Wiener--Hopf complement is genuinely entire, but is constructed from complementary
Xi zero divisor and is nonzero at every strict-right zero.  The old totalized complement is
analytic exactly under RH.  Thus first object has no arithmetic coupling and second already uses
zero-side obstruction; neither supplies missing superluminal source cancellation.

### C43-H — fixed causal filters cannot create corona polarization

**Conjecture.**  A nontrivial causal convolution filter, rather than bare Hardy projection, could
notch amplified negative corona while preserving prime source.

**Verdict:** false for every fixed bounded causal filter.  Let `B` be nonzero bounded Hardy
function in half-plane corresponding to sources supported on `h>=0`, and write same letter for
its almost-everywhere boundary multiplier.  For `sigma>0`, `kappa>1`, define

\[
 {\cal W}^{B}_{\kappa,u}
 =P_{\kappa u}{\cal F}^{-1}
   M_{B(\xi)e^{-(\sigma+iu)\omega_{a,\lambda}(\xi)}}
  {\cal F}P_{\kappa u}.                                       \tag{24.53}
\]

Then every `0<lambda<a` satisfies exact type law

\[
 \boxed{\displaystyle
 \lim_{u\to\infty}\frac1u\log\|{\cal W}^{B}_{\kappa,u}\|
 =\lambda.}                                                    \tag{24.54}
\]

Upper bound is immediate from `||B||_infinity`, `Re omega>=0`, and
`|Im omega|<lambda`.  For lower bound, Hardy boundary uniqueness says nonzero `B` cannot vanish
almost everywhere on any negative half-line.  Indeed Cayley-transform to disk and canonical
inner--outer factorization show a nonzero bounded Hardy function has finite boundary
`integral log|B|`; vanishing on set of positive measure would make it minus infinity.  Hence, for
every large `R`, there is a negative Lebesgue point `xi_R<-R` with `B(xi_R) != 0`.

Fix `epsilon>0` and choose such `xi_R` so far negative that

\[
 \operatorname{Im}\omega_{a,\lambda}(\xi_R)>\lambda-\epsilon,
 \qquad
 \partial_\xi\operatorname{Re}\omega_{a,\lambda}(\xi_R)
 =-1+o_R(1).                                                   \tag{24.55}
\]

Take an `L^2` wave packet of spatial width `sqrt(u)`, frequency width `u^(-1/2)` about
`xi_R`, and center `cu` with `1<c<kappa`.  Taylor expansion of dispersion on packet gives:
logarithmic norm growth at least
`u Im(omega(xi_R))-O(sqrt(u))`; group translation left by
`(1+o_R(1))u\); and spatial spreading only `O(sqrt(u))`.  Input and output therefore remain a
linear distance inside `(0,kappa u)`, while damping `exp(-sigma Re(omega(xi_R)))` and nonzero
`B(xi_R)` are fixed constants.  Thus lower exponential rate is at least
`lambda-epsilon`.  Letting `epsilon` tend to zero proves (24.54).

Consequently any moving bounded filter `B_u` that lowers type by `delta>0` must develop an
exponential cofinal notch:

\[
 |B_u(\xi_R)|\le e^{-\delta u+o(u)}
 \quad\text{on every surviving negative-corona packet family}. \tag{24.56}
\]

At critical `lambda=1/2`, a norm-based type-zero proof therefore needs depth
`e^{-u/2+o(u)}`; any stable inverse pays reciprocal critical type.  This is frequency-side twin
of critical floor Wiener lemma (24.36).  Fixed Blaschke/Hardy readers, rational resolvents, finite
outgoing jets, and fixed analytic smoothers cannot work.  Only source-dependent moving notch or
signed scalar cancellation before norms remains.

### C43-I — Selberg small-value anchors lie beyond mass horizon

**Conjecture.**  Use new corpus theorem placing small `R(m)` in every wide multiplicative window,
then actual integral Lipschitz transport that anchor across mass cone.

**Verdict:** failed by exact horizon mismatch.  Corpus theorem says for `delta>0`,

\[
 \log(z/y)>\frac{40}{\delta}+2
 \quad\Longrightarrow\quad
 \exists m\in(y,z]\colon
 |R(m)|\le\delta m+\log z+1.                                  \tag{24.57}
\]

At critical scale `X=e^h`, type-zero target is, for every fixed `epsilon>0`,

\[
 |R(X)|\le X^{1/2+\epsilon}
 \quad\Longleftrightarrow\quad
 \delta=X^{-1/2+\epsilon}=e^{-(1/2-\epsilon)h}.                \tag{24.58}
\]

Putting (24.58) into (24.57) requires

\[
 \log(z/y)>40X^{1/2-\epsilon}+2
 =40e^{(1/2-\epsilon)h}+2.                                   \tag{24.59}
\]

This is exponential in logarithmic height `h`.  Every available mass cone, including sharp
`H(u)~kappa_B u`, has only `O(u)=O(h)` logarithmic horizon.  No choice of endpoints inside cone
can satisfy (24.59) for large `h`.

Conversely if available multiplicative window has `log(z/y)<=C h`, hypothesis (24.57) can force
only

\[
 \delta>\frac{40}{Ch-2}\asymp\frac1h,\qquad
 e^{-h/2}|R(e^h)|\lesssim\frac{e^{h/2}}h,                     \tag{24.60}
\]

up to logarithmic and square-root terms already present in pointwise gain theorem.  This retains
exponential type `1/2`.  One-sided slow variation then propagates anchor only through relative
`rho` window and cannot recover exponential horizon deficit.

**Positive survivor.**  Harmonic window theorem is strong enough to force relative-error small
values and run elementary PNT contraction, but its resolution cost is reciprocal in desired
relative error.  Critical mass receiver asks exponentially small relative error in log-time.
Bridging these requires new signed cancellation that changes `1/delta` horizon law, not more
Lipschitz propagation from same anchors.

### C43-J — harmonic primitive and mass adjoint conserve critical exponent

**Conjecture.**  Feed uniformly bounded harmonic remainder primitive directly into exact mass-cell
sum and close current by Abel variation.

**Verdict:** exact source reduction succeeds, norm closure fails by sharp exponent conservation.
Put

\[
 w_n=\frac1n-\frac1{n+1},\qquad
 J_N=\sum_{n\le N}R(n)w_n,\qquad J_0=0.                        \tag{24.61}
\]

Corpus proves `|J_N|<=20`.  Let
`K_u(h)=e^{-h/2}F_u(h)`; exact cell law gives finite current

\[
 {\cal S}_{u,N}
 =\sum_{n=1}^N R(n)\bigl(K_u(\log n)-K_u(\log(n+1))\bigr).
\]

Define adjoint cell quotient

\[
 A_{u,n}=
 \frac{K_u(\log n)-K_u(\log(n+1))}{w_n}.                      \tag{24.62}
\]

Since `R(n)w_n=J_n-J_(n-1)`, finite Abel summation yields exact identity

\[
 \boxed{\displaystyle
 {\cal S}_{u,N}
 =J_NA_{u,N}
  +\sum_{n=1}^{N-1}J_n(A_{u,n}-A_{u,n+1}).}                   \tag{24.63}
\]

This is genuine use of new harmonic theorem.  It replaces unbounded remainder by bounded
coefficient sequence before any norm.  Moreover Mertens and PNT give exact limit

\[
 J_N
 =\sum_{n\le N}\frac{\Lambda(n)}n-H_N-\frac{R(N)}{N+1}
 \longrightarrow-2\gamma.                                    \tag{24.64}
\]

Writing `E_N=J_N+2\gamma`, constant part telescopes in (24.63):

\[
 {\cal S}_{u,N}
 =-2\gamma A_{u,1}
  +E_NA_{u,N}
  +\sum_{n=1}^{N-1}E_n(A_{u,n}-A_{u,n+1}).                    \tag{24.65}
\]

Fixed boundary `A_(u,1)` is harmless.  Equation (24.65) is smallest signed harmonic-primitive
form found in this audit.  But taking `|E_n|<=O(1)` and total variation of `A` restores full
critical type.  Mean-value expansion of exact cell quotient gives

\[
 A_{u,n}
 =(1+o(1))\,e^{h/2}
   \left(\frac12F_u(h)-F'_u(h)\right),
 \qquad h=\log n,                                               \tag{24.66}
\]

uniformly on fixed timelike rays `h=alpha u`, `0<alpha<1`.  Stationary phase has nonzero outgoing
symbol there, so `|A_(u,n)|=e^(alpha u/2)u^(-1/2)(c_(a,sigma,alpha)+o(1))` with
`c_(a,sigma,alpha)>0`.  Letting `alpha` approach one shows BV/endpoint estimate from
`|J_n|<=20` has type `1/2`, not zero.

Failure is structurally sharp.  A hypothetical zero mode `R(n)~n^beta`, `beta<1`, gives from
tail of (24.61)

\[
 E_n\sim-\frac{n^{\beta-1}}{1-\beta},
 \qquad E_nA_{u,n}\text{ has scale }n^{\beta-1/2}.             \tag{24.67}
\]

Harmonic primitive lowers source exponent by one; mass adjoint quotient raises it by one half after
critical normalization, reproducing exact displacement exponent `beta-1/2`.  Hence primitive is
information-preserving in mass topology.  Remaining opportunity in (24.65) is signed correlation
between actual decaying `E_n` and complex increments of `A_(u,n)`; bounding either separately is
provably type-sharp.

### C43-K — every finite harmonic-primitive ladder is mass-type rigid

**Conjecture.**  Repeat the harmonic primitive before estimating.  Successive exponent drops might
accumulate faster than successive adjoint losses.

**Verdict:** false at every finite depth, by an exact conjugate recursion.  For any sequence for
which the tail converges define

\[
 (\mathcal Hf)_n=-\sum_{m>n}f_mw_m,
 \qquad
 (\mathcal DA)_n=\frac{A_n-A_{n+1}}{w_n}.                    \tag{24.68}
\]

Then
`(\mathcal Hf)_n-(\mathcal Hf)_(n-1)=w_nf_n`.  Consequently, with
`C_M(f,A)=\sum_(n=1)^M f_nw_nA_n`, finite Abel summation gives the exact recursion

\[
 C_M(f,A)
 =(\mathcal Hf)_MA_M-(\mathcal Hf)_0A_1
  +C_{M-1}(\mathcal Hf,\mathcal DA).                          \tag{24.69}
\]

Set `f_j=\mathcal H^jR`, `A_j=\mathcal D^jA_0`, where `A_0=A_(u,\cdot)` from
(24.62).  Since `${\cal S}_{u,N}=C_N(R,A_0)`, induction in (24.69) gives, for every
fixed `k<=N`,

\[
 {\cal S}_{u,N}
 =\sum_{j=0}^{k-1}
   \left(f_{j+1,N-j}A_{j,N-j}-f_{j+1,0}A_{j,1}\right)
  +C_{N-k}(f_k,A_k).                                         \tag{24.70}
\]

This is unconditional sequence algebra once tails converge (as they do here by PNT); no asymptotic
or norm has entered.  The first step is
exactly (24.65), because `f_1=\mathcal HR=E` and `f_(1,0)=2\gamma`.

Now test the recursion on one hypothetical displaced-zero mode `f_0(n)~c n^\beta`, `\beta<1`.
Tail comparison gives at every fixed depth

\[
 f_j(n)
 \sim \frac{(-1)^jc}{\prod_{\ell=1}^j(\ell-\beta)}
       n^{\beta-j}.                                          \tag{24.71}
\]

On a fixed timelike ray `n=e^(\alpha u)`, `0<\alpha<1`, the cell stationary-phase expansion and
(24.68) give, away from isolated symbol zeros,

\[
 A_j(n)=e^{(j+1/2)\alpha u}u^{-1/2}
        \bigl(b_j(\alpha)+o(1)\bigr),
 \qquad b_j(\alpha)\ne0.                                    \tag{24.72}
\]

Indeed one `\mathcal D` divides a log-cell difference of relative size `1/n` by
`w_n~1/n^2`, raising the power by exactly one.  Thus every endpoint in (24.70), and every
multiplicative block of its remainder, has same scale

\[
 |f_{j+1}(n)A_j(n)|,\quad
 \sum_{m\asymp n}|f_j(m)w_mA_j(m)|
 \asymp n^{\beta-1/2}u^{-1/2}.                               \tag{24.73}
\]

Here second comparison is total-variation scale; signed sum may be smaller only by precisely new
cancellation being sought.  Hence no finite ladder of harmonic primitives changes critical
exponent `\beta-1/2` under separate estimates.  It can only
relocate needed signed cancellation between endpoints and interior.  Possible infinite/cofinal
ladder is not finite smoothing: iterated adjoint has growing order and requires a new uniform
analytic structure controlling all depths.  This is discrete counterpart of finite mass-jet
rigidity and closes every fixed number of further Abel integrations as proof-burden reduction.

### C43-L — harmonic primitive is exact critical outgoing resolvent

**Conjecture.**  Exponent conservation in C43-J/K may be accidental power counting; full harmonic
tail could still smooth actual remainder in a topology seen more favorably by mass current.

**Verdict:** false.  Critical normalization makes two operations exact inverses.  Extend remainder
as step function `R_*(x)=R(n)` on `[n,n+1)`, put

\[
 r(h)=e^{-h/2}R_*(e^h),\qquad
 (\mathscr Tr)(h)=-\int_0^\infty e^{-s/2}r(h+s)\,ds,          \tag{24.74}
\]

with improper tail interpretation.  Mertens limit (24.64) guarantees convergence at cell
endpoints.  Direct change of variables gives

\[
 (\mathscr Tr)(h)
 =-e^{h/2}\int_{e^h}^\infty\frac{R_*(x)}{x^2}\,dx,
 \qquad
 (\mathscr Tr)(\log(n+1))=e^{\log(n+1)/2}E_n.                \tag{24.75}
\]

Differentiating improper tail in distributions (classically off cell boundaries) yields exact
resolvent equation

\[
 \boxed{\left(\frac12-\partial_h\right)\mathscr T=-I.}       \tag{24.76}
\]

Equivalently, on log-frequency `e^(i\xi h)`, harmonic-tail symbol is
`-(1/2-i\xi)^(-1)` and outgoing symbol is `1/2-i\xi`; their product is `-1` at every frequency.
There is no favorable spectral sector hidden by power-mode test.

Connection with exact cell receiver is also literal, not heuristic.  Since
`K_u(t)=e^{-t/2}F_u(t)`, fundamental theorem of calculus gives

\[
 A_{u,n}
 =\frac{\displaystyle
   \int_{\log n}^{\log(n+1)}e^{-t}
   e^{t/2}\left(\frac12F_u(t)-F'_u(t)\right)dt}
  {\displaystyle\int_{\log n}^{\log(n+1)}e^{-t}dt}.         \tag{24.77}
\]

Thus `A_(u,n)` is exact `e^(-t)dt` cell average of critically conjugated outgoing inverse in
(24.76).  Pairing bounded tail with cell quotient reconstructs original remainder current because
source smoothing and receiver differentiation are the same resolvent in dual coordinates:

\[
 \text{harmonic tail }\mathscr T
 \quad\longleftrightarrow\quad
 \text{mass outgoing }\left(\frac12-\partial_h\right).       \tag{24.78}
\]

This upgrades finite-depth type rigidity to exact all-frequency obstruction.  Any scalar transform
commuting with log translations and retaining stable inverse can only re-coordinate current.
Potential gain must come from a genuinely noncommuting operation: prime-adaptive or
mass-phase-adapted covariant primitive whose commutator with outgoing operator has favorable sign
or compactness.  That commutator, not another tail norm, is next mathematical target.

### C43-M — smooth Bessel-phase gauge is locally Mellin and type-rigid

**Conjecture.**  Conjugate harmonic primitive by exact Bessel receiver phase.  This makes adjoint
amplitude essentially positive and might expose cancellation hidden by complex cell increments.

**Verdict:** exact conjugation is useful, but smooth phase gauge cannot lower positive type.  Let
`g_n` be any nonzero gauge and retain pairing `C_M` from (24.69).  Algebraically

\[
 C_M(f,A)=C_M(gf,g^{-1}A).                                   \tag{24.79}
\]

Applying (24.69) to right side gives covariant Abel identity

\[
 \begin{aligned}
 C_M(f,A)
  ={}&(\mathcal H(gf))_M g_M^{-1}A_M
      -(\mathcal H(gf))_0 g_1^{-1}A_1\\
    &+C_{M-1}\!\left(\mathcal H(gf),
                 \mathcal D(g^{-1}A)\right).
 \end{aligned}                                               \tag{24.80}
\]

On a cell range where `A_(u,n)\ne0`, choose exact polar gauge
`g_(u,n)=A_(u,n)/|A_(u,n)|`.  Receiver becomes positive amplitude; entire complex oscillation moves
into covariant source tail

\[
 (\mathcal H(g_uR))_n=-\sum_{m>n}g_{u,m}R(m)w_m.             \tag{24.81}
\]

This is precise candidate signed statistic.  However timelike stationary phase on
`h=\alpha u`, `0<\alpha<1`, has smooth phase

\[
 g_u(e^h)=\exp\!\left(iu\phi(h/u)+i\vartheta(h/u)+o(1)\right),
 \qquad
 \partial_h\arg g_u(e^h)=\phi'(\alpha)+O(u^{-1}).            \tag{24.82}
\]

Hence on every fixed multiplicative neighborhood `m=ne^s`, `s=O(1)`,

\[
 g_u(m)=g_u(n)(m/n)^{i\tau_\alpha}(1+O(u^{-1})),
 \qquad \tau_\alpha=\phi'(\alpha).                          \tag{24.83}
\]

Smooth Bessel phase is therefore only a bounded Mellin twist locally.  For displaced mode
`R(m)~cm^\beta`, `\beta<1`, tail comparison gives

\[
 (\mathcal H(g_uR))_n
 \sim-\frac{c\,g_u(n)}{1-\beta-i\tau_\alpha}n^{\beta-1},
 \qquad
 |(\mathcal H(g_uR))_n|\,|A_{u,n}|
 \asymp n^{\beta-1/2}u^{-1/2}.                              \tag{24.84}
\]

Real exponent is unchanged.  Divergent phase frequency near light edge cannot help: every fixed
timelike ray already detects positive `\beta-1/2`, while complex-time Bessel damping suppresses
edge faster than frequency grows.  Thus smooth receiver-phase adaptation merely moves oscillation
from receiver to source.  A successful covariant primitive must have genuinely arithmetic,
scale-growing connection—not stationary Bessel connection—and must prove cancellation without
choosing gauge from unknown sign of `R`.

### C43-N — critical diagonal moving mass is type zero but quotient-null

**Conjecture.**  New critical-diagonal corona theorem may supply missing unconditional mass-source
bound and transport it back to fixed mass.

**Verdict:** first half succeeds sharply; backwards transport fails in exact type quotient.  New
corpus theorem fixes `v>0`, `sigma>0`, `4sigma v=1` and

\[
 a_v(u)=v|u|+2,\qquad
 r_v(u)=2\bigl(a_v(u)-1/2\bigr)+2,\qquad
 P_{\rm diag}(u)=\operatorname{PrimeMass}_{a_v(u),1}(\sigma+iu). \tag{24.85}
\]

Multiplicity-exact injection of critical zero corona into global Xi divisor disc gives

\[
 \|P_{\rm diag}(u)\|
 \le C_1(1+r_v(u))\log(2+r_v(u))+C_2
 =O_{\sigma,v}((1+|u|)\log(2+|u|)).                         \tag{24.86}
\]

No RH or cancellation enters.  Thus with
`Typ(f)=limsup_(u->infinity) u^(-1)log^+|f(u)|`,

\[
 \operatorname{Typ}(P_{\rm diag})=0.                         \tag{24.87}
\]

Let `P_fix` be fixed-mass source used by receiver and
`H_crit=P_fix-P_diag`.  Since each is sum of other and type-zero term, triangle inequality in both
directions gives exact quotient identity

\[
 \boxed{\operatorname{Typ}(H_{\rm crit})
       =\operatorname{Typ}(P_{\rm fix}).}                    \tag{24.88}
\]

Therefore diagonal theorem does not reduce fixed-mass open core: it constructs an unconditional
type-zero element already zero in type quotient.  Spectrally, increasing mass multiplies each
Poisson mode by an exponentially decaying mass semigroup; returning from `a_v(u)` to fixed mass
requires reciprocal exponential amplification.  Corpus oblique high-pass theorem makes same fact
exact in source coordinates.  Positive survivor is still valuable: (24.86) identifies sharp
critical moving face and rules out proving RH by any polynomially conditioned mass-backtransport.

### C43-O — arithmetic connection dichotomy: smooth, exact-node, or RH-strength

Read-only audit of newest prime-seam and Route-J modules attacks arithmetic gauge left by C43-M.
Write `s_p(rho)` for orbitwise prime-seam charge and `C_(2,q)(rho)` for first-prime anchored Euler
compression commutator.  Corpus proves uniform two-sided recovery

\[
 |s_2(\rho)-s_q(\rho)|
 \le \sqrt{2q}\,\|C_{2,q}(\rho)\|_{\rm ess}
 \le 2|s_2(\rho)-s_q(\rho)|.                                \tag{24.89}
\]

As `q->infinity`, `s_q(rho)->0`.  Off critical line `s_2(rho)\ne0`, hence

\[
 \liminf_{q\to\infty\atop q\ {\rm prime}}
 \sqrt{2q}\,\|C_{2,q}(\rho)\|_{\rm ess}>0.                 \tag{24.90}
\]

Cofinal decay of left side on every Xi divisor fibre is formally equivalent to RH, not a weaker
source theorem.  Moving both anchors to infinity would erase fixed seam and therefore lose
faithfulness.

Could exact arithmetic phase gauge force commutator small?  New phase-node classification says at
every nonzero carrier `u`, integer-linear independence of distinct prime logarithms forces

\[
 \#\{p:\text{some active }p^k\text{ is an exact phase node at }u\}\le1. \tag{24.91}
\]

Moreover every such one-prime-ray profile is local Euler data and vanishes in global prime-clock
source quotient:

\[
 [\text{prime-power exact-node profile}]_{\rm global\ clock}=0. \tag{24.92}
\]

Literal von-Mangoldt/Suzuki source has positive atoms on at least prime-two and prime-three rays, so
cannot satisfy exact-node condition.  Combined with C43-M this produces rigorous trichotomy:

1. smooth Bessel gauge has bounded local Mellin frequency and preserves critical type;
2. exact arithmetic phase locking is rank-one/local and disappears globally;
3. approximate many-prime locking must retain quantitative phase errors, whose required
   scale-growing cancellation is itself new RH-strength estimate.

Thus viable connection cannot arise from phase flattening alone.  It must exploit relation-valued
cross-prime structure before scalar clock quotient—most concretely a signed two-prime commutator
estimate not already equivalent to seam decay.

### C43-P — square-root mass is exact information horizon

Newest corpus strengthens C43-N: zero-free edge margin absorbs entire critical corona, proving
`P_diag(u)->0` on `4sigma v=1`; explicit shrinking subcritical schedule also tends to zero.  This
looks closer to closure, so test whether moving mass still sees off-line displacement.

Fix one Poisson point `alpha=R+iJ`, `R>3`, `0<|J|<1/2`, and write

\[
 \beta_a=\sqrt{\alpha^2+a^2}=M_a+iK_a,\qquad M_a>0.
\]

Corpus mass identities give exact and sharp elementary bounds

\[
 |K_a|M_a=R|J|,\qquad a\le M_a\le a+R.                       \tag{24.93}
\]

At `tau=sigma+iu`, dominant member of line-conjugate pair has logarithmic magnitude

\[
 \mathcal E_a(u)=u|K_a|-\sigma M_a
 =\frac{uR|J|}{M_a}-\sigma M_a.                              \tag{24.94}
\]

The pair itself cannot cancel this term: after division by dominant magnitude, reverse member has
relative magnitude `e^(-2u|K_a|)`, hence

\[
 \left|
  \frac{|e^{-\tau\beta_a}+e^{-\tau\bar\beta_a}|}
       {e^{-\sigma M_a+u|K_a|}}-1
 \right|\le e^{-2u|K_a|}.                                   \tag{24.95}
\]

Now let `a=a(u)->infinity`.

**Erasure side.**  From `M_a>=a`,

\[
 \mathcal E_{a(u)}(u)
 \le \frac{uR|J|}{a(u)}-\sigma a(u)\longrightarrow-\infty
 \quad\text{if}\quad \frac{a(u)^2}{u}\to\infty.             \tag{24.96}
\]

Every fixed off-line orbit is then extinguished.  This holds for critical and zero-free
subcritical corpus schedules, where `a(u)\asymp u`; their `C_0` theorem is therefore compatible
with arbitrary off-line zeros and cannot imply RH.

**Faithful side.**  From `M_a<=a+R`,

\[
 \mathcal E_{a(u)}(u)
 \ge \frac{uR|J|}{a(u)+R}-\sigma(a(u)+R)\longrightarrow+\infty
 \quad\text{if}\quad \frac{a(u)^2}{u}\to0.                  \tag{24.97}
\]

Then `u|K_a|->infinity`, and (24.95) shows line-conjugate pair diverges.  At transition
`a(u)~c\sqrt u`,

\[
 \mathcal E_{a(u)}(u)
 =\left(\frac{R|J|}{c}-\sigma c\right)\sqrt u+o(\sqrt u),    \tag{24.98}
\]

with orbit-dependent threshold `c^2=R|J|/sigma`.

This proves new mass-information phase diagram:

\[
 a\gg\sqrt u:\ \text{off-line information erased},
 \qquad
 a\ll\sqrt u:\ \text{every off-line orbit remains unbounded}. \tag{24.99}
\]

**New avenue and exact gap.**  Replace linear co-moving mass by sub-square-root schedule, e.g.
`a(u)=u^theta`, `0<theta<1/2`.  Orbitwise `C_0` mass readout would force critical line while still
gaining growing Bessel smoothing.  What is not yet proved is cross-orbit selector: scalar trace
could in principle cancel different Xi frequencies, and prime side accesses total trace, not one
orbit.  Required new theorem is positive or mean-square separation of line-conjugate mass orbits
uniformly under `a=o(sqrt u)`.  This is strictly different from fixed-mass type-zero core and from
linear diagonal extinction.

### C43-Q — finite-packet sub-square-root chirp separation

**Conjecture.**  Cross-orbit cancellation may destroy faithful side of C43-P even for finite Xi
packet.

**Verdict:** false; finite packets separate by an actual mean-square theorem.  Choose
`1/3<theta<1/2`,

\[
 a(u)=u^\theta,\qquad t(u)=\frac{u}{a(u)}=u^{1-\theta}.
                                                                    \tag{24.100}
\]

For each fixed Poisson point `alpha`, principal-root expansion is uniform on every fixed packet:

\[
 \sqrt{a^2+\alpha^2}
 =a+\frac{\alpha^2}{2a}+O_\alpha(a^{-3}).
\]

Because `u/a(u)^3=u^(1-3theta)->0`, multiplication by `tau=sigma+iu` and exponentiation give genuine
multiplicative asymptotic

\[
 e^{-(\sigma+iu)\sqrt{a(u)^2+\alpha^2}}
 =e^{-\sigma a(u)-iu a(u)}
  \exp\!\left(-\frac{i\alpha^2}{2}t(u)\right)(1+o(1)).       \tag{24.101}
\]

Writing `alpha=R+iJ`,

\[
 -\frac{i\alpha^2}{2}
 =RJ-\frac{i}{2}(R^2-J^2).                                  \tag{24.102}
\]

Let `S` be any nonempty finite multiplicity packet closed under line conjugation, and `T_S(u)` its
mass trace along this schedule.  If some point is off line, let
`c=max_(alpha in S,\ J>0) RJ>0`.  After factoring
`e^(-sigma a-iu a+ct)`, leading part is nonzero trigonometric polynomial

\[
 P(t)=\sum_{\substack{\alpha=R+iJ\in S\\RJ=c}}
       m_\alpha e^{-\,i(R^2-J^2)t/2}.                        \tag{24.103}
\]

Equal frequencies combine with positive multiplicities.  Distinct frequencies are orthogonal in
Cesaro mean, hence actual integral identity

\[
 \lim_{L\to\infty}\frac1L\int_0^L|P(t)|^2\,dt
 =\sum_{\omega}\left|\sum_{\alpha:\,(R^2-J^2)/2=\omega}
     m_\alpha\right|^2>0.                                   \tag{24.104}
\]

Therefore `|P(t)|` is bounded below on a cofinal sequence.  Lower real-exponent terms and `o(1)`
in (24.101) vanish after normalization, while

\[
 ct(u)-\sigma a(u)
 =c\,u^{1-\theta}-\sigma u^\theta\longrightarrow+\infty.
\]

So `T_S` is unbounded.  Conversely, if every `J=0`, each summand has norm at most `e^(-sigma a(u))`
and `T_S(u)->0`.  We have proved exact finite-packet receiver

\[
 T_S(u)\longrightarrow0
 \quad\Longleftrightarrow\quad
 \text{every point of }S\text{ is critical}.                \tag{24.105}
\]

This removes finite cross-orbit cancellation without zero-gap hypothesis and uses genuine integral
mean square, not diagonal theater.  Remaining full-trace obstruction is uniformity as effective
packet grows with `u`: zero-count gives `O(u log u)` points but no lower frequency separation, and
tail may cancel selected finite packet.  Needed theorem is a cofinal chirp projector or positive
energy stable under growing Xi packets and accessible from literal prime source.

### C43-R — parabolic blow-up recovers the complete Gaussian heat divisor

The preceding obstruction is specific to vertical complex time.  Real time admits a different
scaling in which mass is not an erasing aperture but a relativistic regularization of the Gaussian
heat semigroup.

Write

\[
 \alpha_q=\xi\text{-spectral point},\qquad w_q=\alpha_q^2,
 \qquad \beta_{a,q}=\sqrt{a^2+w_q},\quad \Re\beta_{a,q}>0.
\]

The square-root equation gives the exact remainder identity

\[
 2a(\beta_{a,q}-a)
 =w_q-\frac{w_q^2}{(\beta_{a,q}+a)^2}.                       \tag{24.106}
\]

Consequently, for every fixed copy and every `t>0`,

\[
 e^{2a^2t}e^{-2at\beta_{a,q}}
 =e^{-2at(\beta_{a,q}-a)}\longrightarrow e^{-tw_q}.         \tag{24.107}
\]

This limit passes through the complete multiplicity-exact Xi sum.  Here is the needed domination,
not a formal interchange.  Put `alpha=R+iJ`, where the corpus gives `R>3` and `|J|<1/2`, and
`beta=M+iK`.  Then

\[
 (M-a)(M+a)=R^2-J^2+K^2,\qquad M\le a+R,
\]

so

\[
 a(M-a)\ge \frac{a(R^2-1/4)}{2a+R}.                         \tag{24.108}
\]

For `a>=1`, split at `R=a`.  On `R<=a`, the right side is at least
`(R^2-1/4)/3`; on `R>a`, it is at least
`a(R^2-1/4)/(3R)`.  Thus it is bounded below by a fixed positive multiple of
`R`, uniformly in `a>=1`.  Any fixed polynomial in `w_q` is therefore dominated by a polynomial
times `e^{-c_tR}`, which is summable by the corpus zero-count/reciprocal-square divisor bounds.
Dominated convergence proves, locally uniformly for `t` in compact subsets of `(0,infinity)`,

\[
 \lim_{a\to\infty}
 \sum_q P(w_q)^2e^{-2at(\beta_{a,q}-a)}
 =\sum_qP(w_q)^2e^{-tw_q}.                                  \tag{24.109}
\]

This is the first full-divisor receiver in this attack that needs neither a growing-packet
frequency gap nor a cofinal chirp projector.

### C43-S — exact subordination and mass-jet generation of every RH heat test

The previous limit is the tangent of an exact positive subordination law.  The standard
square-root Laplace identity, applied termwise and then justified by Tonelli/dominated convergence,
gives

\[
 e^{2a^2t}e^{-2at\sqrt{a^2+w}}
 =\int_0^\infty K_{a,t}(s)e^{-sw}\,ds,                       \tag{24.110}
\]

where

\[
 K_{a,t}(s)=\frac{at}{\sqrt\pi}s^{-3/2}
 \exp\!\left(-\frac{a^2(s-t)^2}{s}\right),qquad
 K_{a,t}\ge0,qquad \int_0^\infty K_{a,t}(s)\,ds=1.         \tag{24.111}
\]

Thus `K_(a,t)` is a positive approximate identity at `s=t`; massive half-wave propagation has the
Gaussian heat semigroup as its parabolic tangent.

More importantly, no approximate spectral multiplier is needed.  Let

\[
 L_a=\partial_\tau^2-a^2.
\]

Since `beta_(a,q)^2-a^2=w_q`, one has the exact eigenvalue identity

\[
 P(L_a)^2e^{-\tau\beta_{a,q}}=P(w_q)^2e^{-\tau\beta_{a,q}}.  \tag{24.112}
\]

For the mass trace `T_a(tau)=sum_q e^(-tau beta_(a,q))`, define its renormalized polynomial jet

\[
 \mathcal M_{a,P}(t)=
 e^{2a^2t}\,[P(L_a)^2T_a(\tau)]_{\tau=2at}.                  \tag{24.113}
\]

Normal convergence permits differentiation under the sum, and (24.109)--(24.112) yield both

\[
 \mathcal M_{a,P}(t)
 =\int_0^\infty K_{a,t}(s)\,
    \mathcal H_P(s)\,ds,\qquad
 \mathcal H_P(t):=\sum_qP(w_q)^2e^{-tw_q},                  \tag{24.114}
\]

and

\[
 \mathcal M_{a,P}(t)\longrightarrow\mathcal H_P(t).         \tag{24.115}
\]

The new corpus theorem
`riemannHypothesis_iff_forall_xiPolynomialGaussianHeatTraceReal_nonneg` identifies the right side
exactly.  Hence

\[
 \mathrm{RH}\quad\Longleftrightarrow\quad
 \forall P\in\mathbb R[X],\ \forall t>0,
 \quad\lim_{a\to\infty}\Re\mathcal M_{a,P}(t)\ge0.          \tag{24.116}
\]

Equivalently, it is enough that the liminf be nonnegative along any cofinal mass sequence.

There is also an actual integral Lipschitz theorem, which removes all continuum bookkeeping.  For
`s,t>=t_0>0`, the fundamental theorem of calculus gives termwise

\[
 |e^{-tw}-e^{-sw}|
 \le |t-s|\,|w|e^{-t_0\Re w}.
\]

Therefore

\[
 |\mathcal H_P(t)-\mathcal H_P(s)|
 \le |t-s|\,C_{P,t_0},\qquad
 C_{P,t_0}:=\sum_q|P(w_q)|^2|w_q|e^{-t_0\Re w_q}<\infty.    \tag{24.117}
\]

Continuity in polynomial coefficients and (24.117) show that (24.116) needs only
`P in Z[X]` and positive rational `t`: clear denominators after approximating a real coefficient
vector, and approximate time inside `[t_0,infinity)`.  This gives a countable literal target, not a
continuum-valued positivity postulate.

### C43-T — the parabolic limit stays on one absolutely convergent Euler line

The bridge is source-facing.  Fix one legal depth `1/2<c<a` and put

\[
 z_x=x-ci,\qquad s_x=\frac12+c+ix,
\]

Write the completed archimedean logarithmic derivative exactly as it occurs in the corpus:

\[
 \mathcal A_\infty(s):=(\log\operatorname{Der}\operatorname{archFactor})(s)
 =\frac1s+\frac1{s-1}+\frac{\Gamma_\mathbb R'}{\Gamma_\mathbb R}(s),
 \qquad
 \mathcal S_c(x)=-i\bigl(L_\Lambda(s_x)-\mathcal A_\infty(s_x)\bigr).
\]

The two rational polar terms are load-bearing in the exact identity; replacing
`A_infinity` by the bare Gamma logarithmic derivative would not be the mass bottom source.

The corpus identity `xiMassTraceC_eq_normalizedBottomEulerContour` is absolutely convergent on this
line.  Differentiating it by `P(L_a)^2`, using
`L_a exp(-tau sqrt(a^2+z_x^2))=z_x^2 exp(-tau sqrt(a^2+z_x^2))`, gives exactly

\[
 \mathcal M_{a,P}(t)=
 (2\pi i)^{-1}2\int_{\mathbb R}
 P(z_x^2)^2 e^{2a^2t-2at\sqrt{a^2+z_x^2}}
 \mathcal S_c(x)\,dx.                                      \tag{24.118}
\]

The domination behind (24.108), now split into bounded `|x|` and the two tails, is a polynomial
times a fixed exponential in `|x|`.  The von-Mangoldt Dirichlet series is absolutely bounded on
`Re s=1/2+c>1`, while the archimedean logarithmic derivative has only logarithmic growth.
Dominated convergence in (24.118) proves the literal Euler-line Gaussian formula

\[
 \mathcal H_P(t)=
 (2\pi i)^{-1}2\int_{\mathbb R}
 P((x-ci)^2)^2e^{-t(x-ci)^2}\mathcal S_c(x)\,dx.             \tag{24.119}
\]

This removes continued-source rectangles from the proof obligation.  Every term is evaluated in
the absolutely convergent Euler chamber, and the only limit is the positive parabolic approximate
identity.

### C43-U — positivity audit: exact new core, and two false shortcuts

Combining (24.116) and (24.119) gives a genuinely different exact open core:

\[
 \boxed{\quad
 \Re\left[(2\pi i)^{-1}2\int_{\mathbb R}
 P((x-ci)^2)^2e^{-t(x-ci)^2}\mathcal S_c(x)\,dx\right]\ge0
 \quad}                                                     \tag{24.120}
\]

for every `P in Z[X]` and `t in Q_(>0)`, at one fixed `c>1/2`.  By the proved chain, (24.120) is
equivalent to RH.  Unlike the vertical type core, it has Gaussian damping, absolute prime access,
no moving cutoff, no zero-gap input, and no full-packet cancellation problem.

Two tempting closures fail.

1. **Large mass does not make orbit pairs positive.**  If `w=A+iB`, then along the parabolic
   scaling the pair phase tends to `tB`, not zero.  The same phase that detects horizontal
   displacement survives in (24.107); positivity cannot be obtained by declaring the mass large.

2. **Von-Mangoldt positivity is not termwise heat-Hankel positivity.**  Already for `P(X)=X`, the
   real-axis Gaussian test is `x^4e^(-t x^2)`.  With Fourier convention
   `int e^(-ixxi)f(x)dx`, its transform is a positive Gaussian times

\[
 \xi^4-12t\xi^2+12t^2.                                     \tag{24.121}
\]

The polynomial is negative for
`6-2sqrt(6)<xi^2/t<6+2sqrt(6)`.  Hence the explicit prime weights change sign even at the first
nonconstant monomial-square filter.  The corpus's positive von-Mangoldt coefficients cannot prove
(24.120) term by term; the required mechanism is global prime--Gamma compensation.

The all-order burden is also genuine.  The corpus degree-tail polarization theorem shows that
positivity on every polynomial above any fixed degree is already the complete source cone, while
finite-prefix moment positivity admits bad continuations.  Thus no fixed jet order or finite
Hankel block can close (24.120).

### C43-V — exact Hermitian/orientation decomposition of parabolic mass jets

The source inequality has an exact positive defect form.  Write
`w_q=A_q+iB_q` and `beta_(a,q)=M_(a,q)+iK_(a,q)`, and define Hermitian mass

\[
 \mathcal G_{a,P}(t)=\sum_q |P(w_q)|^2
 e^{-2at(M_{a,q}-a)}.                                      \tag{24.122}
\]

For every finite mass, elementary identity
`|z|^2-Re(z^2e^(-2itheta))=2 Im(ze^(-itheta))^2` gives

\[
 \mathcal G_{a,P}(t)-\Re\mathcal M_{a,P}(t)
 =2\sum_q e^{-2at(M_{a,q}-a)}
 \left[\Im\!\left(P(w_q)e^{-iatK_{a,q}}\right)\right]^2
 \ge0.                                                      \tag{24.123}
\]

Dominated convergence, `2a(M-a)->A`, and `aK->B/2` yield

\[
 \mathcal G_P(t):=\sum_q|P(w_q)|^2e^{-tA_q},                \tag{24.124}
\]

\[
 \mathcal D_P(t):=\mathcal G_P(t)-\Re\mathcal H_P(t)
 =2\sum_qe^{-tA_q}
 \left[\Im\!\left(P(w_q)e^{-itB_q/2}\right)\right]^2
 \ge0.                                                      \tag{24.125}
\]

For `P=1`,

\[
 \mathcal D_1(t)=\sum_qe^{-tA_q}(1-\cos(tB_q)),\qquad
 \mathrm{RH}\Longleftrightarrow
 \forall t>0,\ \mathcal D_1(t)=0.                          \tag{24.126}
\]

Every summand in `D_1` is nonnegative, and a nonzero `B_q` fails the identity away from its
discrete phase nodes.  More generally, (24.116) is exactly orientation-budget family

\[
 \mathcal D_P(t)\le\mathcal G_P(t)
 \quad(P\in\mathbb R[X],\ t>0).                             \tag{24.127}
\]

This pinpoints why newest unconditional thermal/KMS and Gaussian Gram modules do not finish the
route.  They supply `G_P>=0`, which remains true with off-line atoms; RH-bearing datum is sharp
cap `D_P<=G_P`, and vanishing of unfiltered orientation defect is even stronger.  Any proposed
positive-state transfer must control this explicit phase square rather than merely construct a
positive ambient Gram.

### C43-W — repaired prime--Gamma split and the first-prime heat horizon

Hostile source audit repairs one omitted term in C43-T.  The exact corpus source contains
`logDeriv archFactor`, not the bare Gamma logarithmic derivative.  With

\[
 \mathcal A_\infty(s)=\frac1s+\frac1{s-1}
   +\frac{\Gamma_\mathbb R'}{\Gamma_\mathbb R}(s)
\]

in the definition of `S_c`, (24.118)--(24.120) remain exact.  Omitting the first two summands would
make those displayed identities false.

The repair exposes a useful exact decomposition.  Put

\[
 F_{P,t}(x)=P(x^2)^2e^{-tx^2},\qquad
 \widehat F_{P,t}(\xi)=\int_{\mathbb R}F_{P,t}(x)\cos(\xi x)\,dx,
\]

and let `vartheta_infinity(x)=gammaHardyPhaseRate(x)`, the real part of the Gamma connection on
`s=1/2+ix`.  Shifting only the completed archimedean integral from `Im z=-c` to the real axis
crosses the single pole `s=1`, or `z=-i/2`.  Its residue is the two-pole term
`2 exp(t/4) P(-1/4)^2`.  On the critical line the real parts of `1/s` and `1/(s-1)` cancel.
Shifting each absolutely convergent Euler monomial separately cancels the depth and replaces
`n^(-1/2-c)` by `n^(-1/2)`.  Therefore

\[
 \boxed{\begin{aligned}
 \Re\mathcal H_P(t)
  ={}&2e^{t/4}P(-1/4)^2
   +\frac1\pi\int_{\mathbb R}F_{P,t}(x)\vartheta_\infty(x)\,dx\\
  &-\frac1\pi\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
       \widehat F_{P,t}(\log n).
 \end{aligned}}                                             \tag{24.128}
\]

This is independent of the legal depth `c`.  It is the literal parabolic source, with polar,
Gamma, and prime faces all retained.

For fixed `P` of degree `d`, `widehat F_(P,t)` is a finite linear combination of even derivatives
of `sqrt(pi/t) exp(-xi^2/(4t))`.  Hence, for `0<t<=1`,

\[
 |\widehat F_{P,t}(\xi)|
 \le C_Pt^{-2d-1/2}(1+|\xi|^{4d})e^{-\xi^2/(4t)}.           \tag{24.129}
\]

Because `log n>=log 2`, split the Gaussian exponent in half and use
`exp(-(log n)^2/(8t))<=n^(-2)` for all sufficiently small `t`.  The elementary bound
`Lambda(n)<=log n` then gives the actual integral estimate

\[
 \sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
   |\widehat F_{P,t}(\log n)|
 =O_P\!\left(t^{-2d-1/2}
   e^{-(\log2)^2/(8t)}\right).                              \tag{24.130}
\]

No PNT or zero count enters.  For every fixed differential-jet order, all arithmetic frequencies
are superexponentially beyond the small-time aperture.  This strengthens the corpus theorem that
the `n`-th prime bump peaks at `t=(log n)^2/2`: before the first-prime horizon the *complete*
fixed-degree prime jet is negligible, not merely each atom separately.

### C43-X — unconditional finite-degree ultraviolet positivity

The Gamma remainder now supplies a positive theorem rather than another equivalence.  Define the
unfiltered complex moments

\[
 h_m(t)=\Re\sum_q w_q^m e^{-tw_q}\qquad(m\ge0).
\]

The corpus asymptotic
`vartheta_infinity(x)-(1/2)log(x/(2 pi))->0`, evenness, (24.128), and (24.130) give

\[
 h_m(t)=\frac{\Gamma(m+1/2)}{4\pi}
 t^{-m-1/2}\log(1/t)+O_m(t^{-m-1/2})
 \qquad(t\downarrow0).                                    \tag{24.131}
\]

This is also a direct source-side Riemann--von Mangoldt heat law, but here it is obtained without
introducing a zero-counting remainder.

For fixed `d`, let `K_d(t)=(h_(j+k)(t))_(0<=j,k<=d)`.  Its anisotropically rescaled matrix satisfies

\[
 \frac{4\pi}{\log(1/t)}
 \bigl(t^{j+k+1/2}h_{j+k}(t)\bigr)_{0\le j,k\le d}
 \longrightarrow
 \bigl(\Gamma(j+k+1/2)\bigr)_{0\le j,k\le d}.              \tag{24.132}
\]

The limiting matrix is strictly positive definite, since for every nonzero real vector `u`,

\[
 \sum_{j,k=0}^du_ju_k\Gamma(j+k+1/2)
 =\int_{\mathbb R}
   \left(\sum_{j=0}^du_jx^{2j}\right)^2e^{-x^2}\,dx>0.     \tag{24.133}
\]

Finite-dimensional stability and congruence by
`diag(1,t^(-1),...,t^(-d))` prove

\[
 \boxed{\quad
 \forall d\ \exists\varepsilon_d>0\ \forall P\in\mathbb R[X],
 \quad P\ne0,\quad \deg P\le d,\quad
 0<t\le\varepsilon_d
 \Longrightarrow \Re\mathcal H_P(t)>0.
 \quad}                                                     \tag{24.134}
\]

Consequently the RH-equivalent open core (24.120) needs testing, in degree at most `d`, only for rational heat times
`t>epsilon_d`.  Small heat time is unconditionally inside the strict source cone, uniformly over
the entire finite-dimensional polynomial space.

The quantifiers cannot be interchanged by Gamma domination.  The corpus proves
`vartheta_infinity(0)<0`; polynomial squares are dense enough in a fixed Gaussian weighted space
to concentrate the archimedean quadratic form near that negative interval as degree grows.  Thus
no fixed small-time aperture makes the Gamma term alone positive in all degrees.  Polar and prime
compensation becomes load-bearing on a degree--time diagonal.  This is a no-go for a uniform
"small `t` solves all jets" shortcut, not a negative statement about the completed trace.

### C43-Y — universal degree--time wedge from oscillator phase-space separation

The fixed-degree constants in (24.134) can be made uniform at the correct parabolic scale.  Write
`q(x)=P(x^2)`, `d=deg P`, and

\[
 M_{P,t}=\int_{\mathbb R}q(x)^2e^{-tx^2}\,dx.
\]

Two coefficient-free Hermite estimates are decisive.  First rescale `y=sqrt(t)x`.  The normalized
function `q(y/sqrt(t))exp(-y^2/2)` belongs to the first `2d+1` oscillator levels.  Mehler's diagonal
identity, with `r=2d/(2d+1)`, gives the universal spectral-projector bound

\[
 \sup_y\sum_{j=0}^{2d}|\psi_j(y)|^2\le C\sqrt{d+1}.
\]

The reproducing-kernel inequality therefore gives, for every fixed `R>0`,

\[
 \int_{|x|\le R}q(x)^2e^{-tx^2}\,dx
 \le C R\sqrt{t(d+1)}\,M_{P,t}.                            \tag{24.135}
\]

Let `g=vartheta_infinity`.  Continuity, evenness, and
`g(x)-(1/2)log(|x|/(2 pi))->0` imply that `g` is bounded below and is uniformly positive outside
some compact interval.  Splitting there and using (24.135) yields constants `c_0,C_0>0`, independent
of `P,d,t`, such that

\[
 \int_{\mathbb R}F_{P,t}(x)g(x)\,dx
 \ge\bigl(c_0-C_0\sqrt{t(d+1)}\bigr)M_{P,t}.               \tag{24.136}
\]

Second, the prime side has a matching coefficient-free aperture estimate.  Put
`Q(y)=q(y/sqrt(t))` and `omega=xi/sqrt(t)`.  Completing the square and shifting the entire Gaussian
contour gives

\[
 \frac{|\widehat F_{P,t}(\xi)|}{M_{P,t}}
 \le e^{-\omega^2/4}
 \frac{\|Q(\mathord\cdot-i\omega/2)\|_{L^2(e^{-y^2}dy)}^2}
      {\|Q\|_{L^2(e^{-y^2}dy)}^2}.
\]

On polynomials of degree at most `N`, differentiation has Gaussian `L^2` operator norm
`sqrt(2N)`, because it lowers the normalized Hermite basis by `sqrt(2j)`.  Since
`Q(y-iu)=exp(-iu partial_y)Q(y)` and `N=2d`,

\[
 \boxed{\quad
 \frac{|\widehat F_{P,t}(\xi)|}{M_{P,t}}
 \le \exp\!\left(-\frac{\xi^2}{4t}
             +2\sqrt d\,\frac{|\xi|}{\sqrt t}\right).
 \quad}                                                     \tag{24.137}
\]

If `t(d+1)` is smaller than a universal constant, every arithmetic frequency
`xi=log n>=log 2` lies beyond the translated oscillator disk, and (24.137) is at most
`exp(-xi^2/(8t))`.  Splitting this last Gaussian in half and using only
`Lambda(n)<=log n` gives

\[
 \sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
   |\widehat F_{P,t}(\log n)|
 \le C M_{P,t}\exp\!\left(-\frac{(\log2)^2}{16t}\right).  \tag{24.138}
\]

The polar term in (24.128) is nonnegative.  Choosing the wedge small enough that (24.136) is at
least `c_0 M_(P,t)/2` and (24.138) is smaller proves the uniform strengthening

\[
 \boxed{\quad
 \exists\eta>0\ \forall d\ \forall P\in\mathbb R[X],\qquad
 P\ne0,\quad\deg P\le d,\quad 0<t,\quad t(d+1)\le\eta
 \Longrightarrow \Re\mathcal H_P(t)>0.
 \quad}                                                     \tag{24.139}
\]

Thus the completed source is unconditionally positive throughout a universal parabolic wedge,
not merely on a degree-dependent unspecified neighbourhood.  The boundary `td asymp 1` is forced
twice: it is where a degree-`d` oscillator can concentrate inside the negative Gamma interval and
where the first prime modulation enters its phase-space disk.  The earlier two difficulties are
the same aperture transition.

### C43-Z — polynomial-filtered Turan curvature is already RH-complete

Recent corpus work on the Gaussian heat Turan defect exposes a second reduction.  For a real
polynomial `Q`, define the three filtered moments

\[
 H_{Q,k}(t)=\sum_q Q(w_q)^2w_q^k e^{-tw_q}
            =(-\partial_t)^k\mathcal H_Q(t),\qquad 0\le k\le2,
\]

and their adjacent determinant

\[
 \Delta_Q(t)=H_{Q,0}(t)H_{Q,2}(t)-H_{Q,1}(t)^2
 =\mathcal H_Q(t)\mathcal H_Q''(t)-(\mathcal H_Q'(t))^2.  \tag{24.140}
\]

All three moments are real unconditionally by line conjugation.  Then

\[
 \boxed{\qquad
 \mathrm{RH}\Longleftrightarrow
 \Delta_Q(t)\ge0\quad
 (Q\in\mathbb R[X],\ t>0).
 \qquad}                                                    \tag{24.141}
\]

The forward implication is the variance determinant of the positive measure
`sum_q Q(w_q)^2 exp(-t w_q) delta_(w_q)` on the positive real axis.  For the converse, assume an
off-line copy exists and choose the least shell coordinate `A=Re w` among off-line copies; shell
finiteness makes this minimum and the next-shell gap actual.  Every lower shell is real.  Finite
Schwarz-real interpolation supplies a real polynomial `Q` which vanishes on all real squared
points with `Re w<=A` and equals `1` on every nonreal squared point with `Re w=A`.  This is exactly
the interpolation interface already present in `FiniteHermiteCRT` and `TraceHankelConverse`.

Write the surviving bottom shell as `w_j=A+iB_j`, with multiplicity, where the nonzero `B_j` form
a conjugation-symmetric finite multiset.  Simultaneous phase recurrence gives arbitrarily large
`t_l` for which every `exp(-it_l B_j)` tends to `1`.  For the bottom packet alone,

\[
 e^{2At_l}\Delta_Q^{\rm bot}(t_l)
 \longrightarrow -m\sum_{j=1}^m B_j^2<0,                 \tag{24.142}
\]

equivalently
`2e^(2At)Delta_Q^bot(t)=-sum_(j,k)(B_j-B_k)^2 exp(-it(B_j+B_k))`.
The positive shell gap and Gaussian-damped polynomial summability give

\[
 e^{2At}\bigl(\Delta_Q(t)-\Delta_Q^{\rm bot}(t)\bigr)
 \longrightarrow0.                                        \tag{24.143}
\]

Hence `Delta_Q(t_l)<0` for a large recurrence time, proving the converse.  Strict negativity and
coefficient/time continuity reduce (24.141) to integer `Q` and positive rational `t`.

This is a genuine proof-burden reduction.  Put

\[
 F_{Q,k,t}(x)=x^{2k}Q(x^2)^2e^{-tx^2}.
\]

The repaired source formula gives each factor of (24.140) on one legal Euler line:

\[
 \begin{aligned}
 H_{Q,k}(t)={}&2e^{t/4}(-1/4)^kQ(-1/4)^2
 +\frac1\pi\int_{\mathbb R}F_{Q,k,t}(x)g(x)\,dx\\
 &-\frac1\pi\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
       \widehat F_{Q,k,t}(\log n),\qquad 0\le k\le2.
 \end{aligned}                                              \tag{24.144}
\]

Therefore exact open core may be replaced by one structured two-replica inequality
`H_(Q,0)H_(Q,2)-H_(Q,1)^2>=0`, rather than direct positivity of every scalar polynomial-square
trace.  `XiHeatTuranBottomDetection` proved the unfiltered simple-bottom case; finite interpolation
plus recurrence remove simple-pair and lowest-shell assumptions.  New Gamma-conductor Schur
strict-definiteness has precisely covariance architecture needed for (24.144), but current corpus
does not identify its Mercer residual with this completed heat source.  That missing identification,
not another full-Hankel theorem, is the new avenue.

### C43-AA — parabolic prime information cone

Estimate (24.137) also gives a global finite-prefix reduction, with no small-time assumption.  For
`0<=k<=2` put

\[
 R_{Q,k}(x)=x^kQ(x^2),\qquad
 M_{Q,k,t}=\int_{\mathbb R}R_{Q,k}(x)^2e^{-tx^2}\,dx.
\]

The same imaginary-translation proof, now in polynomial degree `N=2 deg Q+k`, gives

\[
 |\widehat F_{Q,k,t}(\xi)|
 \le M_{Q,k,t}\exp\!\left(-\frac{\xi^2}{4t}
       +\sqrt{2N}\frac{|\xi|}{\sqrt t}\right).             \tag{24.145}
\]

Choose

\[
 L_{d,k}(t)=\log2+16\sqrt{(d+k+1)t}+32t.
\]

For `log n>=L_(d,k)(t)`, the translated oscillator factor in (24.145) is at most
`exp(-(log n)^2/(8t))`; the `32t` term makes half of that Gaussian at most `n^(-2)`.  Hence

\[
 \boxed{\quad
 \sum_{\log n\ge L_{d,k}(t)}\frac{\Lambda(n)}{\sqrt n}
   |\widehat F_{Q,k,t}(\log n)|
 \le C M_{Q,k,t}
   \exp\!\left(-\frac{L_{d,k}(t)^2}{16t}\right).
 \quad}                                                     \tag{24.146}
\]

Thus every factor in filtered Turan core (24.144) has an unconditional **prime information cone**:
up to an explicit relative tail, it sees only prime powers

\[
 n\le\exp\!\bigl(O(t+\sqrt{(d+1)t})\bigr).                \tag{24.147}
\]

This is not a numerical truncation.  It is a coefficient-uniform analytic theorem derived from
oscillator phase-space separation and `Lambda(n)<=log n`.  It says exactly which finite arithmetic
packet a degree--time heat probe can access.  In wedge (24.139), even `log 2` lies outside
oscillator disk and whole prime side is tail-small; beyond it prime frequencies enter in increasing
logarithmic shells.

### C43-AB — independent-prime covariance fails; coherent double-prime kernel survives

Conjecture that (24.140) is a positive sum of one-prime KMS covariances fails.  Split (24.144) as
`H_(Q,k)=A_(Q,k)-P_(Q,k)`, with `A` polar plus Gamma and `P` the positive-coefficient prime sum.
Then exact curvature is

\[
 \Delta_Q=(A_0A_2-A_1^2)
 -(A_0P_2+A_2P_0-2A_1P_1)
 +(P_0P_2-P_1^2).                                         \tag{24.148}
\]

Even diagonal prime curvature has wrong sign.  For `Q=1`, writing
`phi_t(xi)=sqrt(pi/t)exp(-xi^2/(4t))`, one has
`widehat F_(1,0,t)=phi_t`, `widehat F_(1,1,t)=-phi_t''`, and
`widehat F_(1,2,t)=phi_t''''`.  Direct differentiation gives

\[
 \widehat F_{1,0,t}(\xi)\widehat F_{1,2,t}(\xi)
 -\widehat F_{1,1,t}(\xi)^2
 =\frac{\pi(t-\xi^2)}{2t^4}e^{-\xi^2/(2t)}.               \tag{24.149}
\]

It is negative for every prime frequency with `(log n)^2>t`.  Thus neither one-prime determinants
nor termwise positive KMS completion can prove (24.148).

New corpus makes obstruction structural.  `GammaConductorSchurCapacity` proves that independent
diagonal prime channels coupled to one scalar Gamma conductor incur Schur cost at least
`9/(512p)` per prime, whose sum diverges; every nonzero diagonal damping cancels from that cost.
Gaussian heat damping therefore cannot repair this independent-channel ansatz.  At same time
`PrimeLogKMSHermitianCompletion` identifies reflected carrier as exact orientation defect discarded
by Hermitian completion.

Positive survivor is forced and concrete.  Last term of (24.148) is coherent double-prime kernel

\[
 P_0P_2-P_1^2
 =\frac12\sum_{m,n\ge2}a_ma_n
 [f_0(m)f_2(n)+f_2(m)f_0(n)-2f_1(m)f_1(n)],               \tag{24.150}
\]

where `a_n=Lambda(n)/(pi sqrt n)` and `f_k(n)=widehat F_(Q,k,t)(log n)`.  Any successful source
proof must retain this cofinal cross-prime covariance together with mixed polar--Gamma term in
(24.148).  Finite cone (24.146) makes it a finite coherent packet plus certified tail at every
`(d,t)`.  This precisely replaces failed scalar-conductor route; no independent-prime or
norm-first positivity remains plausible.

### C43-AC — eventual filtered log-convexity already forces RH

Phase recurrence in C43-Z can be strengthened to a signed Bohr mean, eliminating all arithmetic
relations among bottom frequencies.  For the same shell-killing filter `Q`, pair expansion gives

\[
 2e^{2At}\Delta_Q^{\rm bot}(t)
 =-\sum_{j,k}(B_j-B_k)^2e^{-it(B_j+B_k)}.                 \tag{24.151}
\]

Cesaro averaging retains exactly pairs with `B_j+B_k=0`.  Conjugation symmetry and absence of a
zero bottom frequency imply

\[
 \lim_{T\to\infty}\frac1T\int_1^T e^{2At}Delta_Q(t)\,dt
 =-\frac12\sum_{B_j+B_k=0}(B_j-B_k)^2<0.                 \tag{24.152}
\]

The shell-gap tail contributes zero to this limit.  Consequently

\[
 \boxed{\qquad
 \mathrm{RH}\Longleftrightarrow
 \forall Q\in\mathbb R[X]\ \exists T_Q\ \forall t>T_Q,
 \quad\Delta_Q(t)\ge0.
 \qquad}                                                   \tag{24.153}
\]

So completed source need only prove **eventual** log-convexity for each filtered heat trace; no
uniform threshold in `Q` is required.  This removes entire ultraviolet/mid-time range from
two-replica route.  Tradeoff is real and must not be hidden: shell-killing interpolant is
zero-adaptive and may have genuinely real coefficients.  Rational approximation preserves one
strict negative time, hence countable criterion (24.141), but does not preserve exact annihilation
of lower shells for all late times.  Eventual formulation is therefore a structural contradiction
tool, not yet a countable prime-side test.

### C43-AD — countable exponential-height repair of shell adaptivity

The continuum tradeoff in C43-AC has an exact quantitative repair.  Let
`ht(Q)=max(1,max_j |Q_j|)` for an integer polynomial.  If `Q_*` is shell-killing interpolant and
`a_*<A` is least lower real shell, a coefficient perturbation of size `epsilon` loads every killed
shell with weight `O(epsilon^2)`.  After normalization by `e^(-2At)`, worst lower--target and
lower--lower determinant terms are

\[
 O\!\left(\varepsilon^2e^{(A-a_*)t}
          +\varepsilon^4e^{2(A-a_*)t}\right).             \tag{24.154}
\]

Choose `epsilon_t=e^(-ct)` with `c>(A-a_*)/2`.  Rounding finitely many coefficients with common
denominator `D_t asymp epsilon_t^(-1)` gives a rational filter with same negative recurrent
curvature for all sufficiently late selected times.  Clearing denominator multiplies `Delta` by
`D_t^4`, preserving sign, and produces fixed-degree integer `Q_t` with
`ht(Q_t)<=e^(Ct)` for some `C`.

If no lower shell exists, a fixed sufficiently accurate rational approximation already preserves
late negativity; same conclusion follows with no exponential accuracy cost.  Real points on shell
`A` contribute only `O(epsilon^2)` after normalization and are absorbed in either case.

Consequently fully countable criterion is

\[
 \boxed{\begin{aligned}
 \mathrm{RH}\Longleftrightarrow{}&
 \forall d\in\mathbb N\ \forall C>0\ \exists T>0\
 \forall t\in\mathbb Q_{>T}\ \forall Q\in\mathbb Z[X],\\
 &Q\ne0,\quad\deg Q\le d,\quad\operatorname{ht}(Q)\le e^{Ct}
 \Longrightarrow\Delta_Q(t)\ge0.
 \end{aligned}}                                           \tag{24.155}
\]

Forward implication is immediate from RH.  Under false RH, preceding rationalized shell filter
violates displayed condition for one fixed `d,C` along arbitrarily late rational times; continuity
supplies rational time after each strict negative recurrence interval.

This is sharper endpoint for source attack.  It asks for eventual completed curvature uniformly on
a **fixed-degree, exponential-coefficient cone**.  By (24.147), same probe sees only prime powers
up to `exp(O(t))`.  Filter-conditioning scale and arithmetic-information scale therefore match:
remaining theorem is finite coherent prime--Gamma covariance on two exponentially growing but
commensurate axes.  Subexponential coefficient control would miss exact shell peeling, another
appearance of inverse-conditioning wall rather than proof route.

### C43-AE — finite-degree infrared shell ladder and exact one-shell gap

Order distinct squared-shell coordinates increasingly as `A_1<A_2<...`; call shell critical when
all its points have zero imaginary part.  Let `E_d` mean that every nonzero real `Q` of degree at
most `d` has `Delta_Q(t)>0` for all sufficiently large `t` (threshold may depend on `Q`).  Then

\[
 \boxed{\quad
 [A_1,\ldots,A_{d+2}\ \hbox{critical}]
 \Longrightarrow E_d
 \Longrightarrow[A_1,\ldots,A_{d+1}\ \hbox{critical}].
 \quad}                                                     \tag{24.156}
\]

For left implication, degree-`d` polynomial can vanish at at most `d` distinct real shell points.
At least two of first `d+2` critical shells survive.  Two least surviving shells give strictly
positive leading determinant
`m_jm_k Q(A_j)^2Q(A_k)^2(A_k-A_j)^2 exp(-(A_j+A_k)t)`; every later shell is exponentially smaller.

For right implication, if first noncritical shell has at most `d` lower critical shells, polynomial
`prod_(i<r)(X-A_i)` kills all of them.  Noncritical shell becomes bottom.  Its Bohr mean is strictly
negative because each conjugate pair contributes
`-|Q(A+iB)|^4(2B)^2`; hence `E_d` fails.

Attempt to replace both `d+1,d+2` by same index fails exactly.  If first noncritical shell is
`A_(d+2)`, a degree-`d` filter can leave one lower real shell but cannot in general also kill real
points sharing `A_(d+2)`.  Their positive zero-frequency cross term may mask nonreal oscillation.
No sign estimate removes it.  This one-shell gap is interpolation-rank boundary, not analytic tail
loss.  Closing it requires either one more filter degree or a source identity coupling mixed shell,
which points again to coherent two-replica term (24.148).

### C43-AF — large-time prime--polar superresolution wall

Conjecture that eventual curvature (24.155) follows from `PNTPlus` after saddle expansion fails by
an exponential margin.  Already for `Q=1`, prime Gaussian weight has log-frequency exponent

\[
 \frac L2-\frac{L^2}{4t}
 =\frac t4-\frac{(L-t)^2}{4t}.                             \tag{24.157}
\]

Thus arithmetic information cone is centered at `L=log n=t`, and continuous density main term is

\[
 \sqrt{\frac\pi t}\int_0^\infty
 e^{L/2-L^2/(4t)}\,dL
 =2\pi e^{t/4}(1+o(1)).                                  \tag{24.158}
\]

After factor `1/pi` this is exactly size `2e^(t/4)` of polar residue in (24.128), with opposite
sign.  Filtered moments inherit polynomial saddle expansion whose leading analytic value is same
polar evaluation `(-1/4)^kQ(-1/4)^2`.  Actual shell signal after this cancellation is only
`e^(-At)` for least surviving squared shell `A>0`.

`PNTPlus.MediumPNT` gives relative prime discrepancy
`exp(-c (log x)^(1/10))`.  At saddle `log x=t`, even optimal use of that bound leaves absolute
source uncertainty

\[
 \exp\!\left(\frac t4-c't^{1/10}\right)\operatorname{poly}(t),
 \qquad\hbox{whereas target is }e^{-At}.                  \tag{24.159}
\]

Needed relative precision is `exp(-(A+1/4)t)`, not `exp(-c t^(1/10))`.  Hence no modulus PNT,
finite saddle expansion, or one-sided discrepancy estimate can prove eventual filtered curvature.
It must expose exact prime--polar--Gamma cancellation before absolute values, at spectral
superresolution far beyond classical PNT remainder.  This is large-time parabolic analogue of
Bessel caustic and floor-inverse conditioning walls.

### C43-AG — half-density strip maximum principle kills moving polar-null jets

Next conjecture was to apply moving high-order filter `P_m(X)=(X+1/4)^m`.  It annihilates polar
residue exactly and, for `m asymp t`, appears capable of suppressing prime saddle.  This fails at
exponential level for a universal reason.

For any nonzero polynomial `P` and `t>0`, define on open Xi strip `|Im z|<1/2`

\[
 U_{P,t}(z)=2\log|P(z^2)|-t\Re(z^2).                     \tag{24.160}
\]

It is subharmonic, tends to `-infinity` as `|Re z|->infinity`, and its polynomial zeros only add
negative logarithmic singularities.  Maximum principle therefore gives, for every interior `z`,

\[
 U_{P,t}(z)\le
 \max_{\epsilon=\pm1}\sup_{x\in\mathbb R}
 U_{P,t}(x+i\epsilon/2),                                  \tag{24.161}
\]

strictly at every nonzero interior value because `t>0` prevents constant profile.  This holds
pointwise for arbitrary moving sequence `P=P_t`; degree and coefficient height may grow as fast as
desired.

Boundary is not artificial.  For `F_(P,t)(x)=P(x^2)^2e^(-tx^2)` and `L>0`, shifting entire Fourier
contour by `-i/2` gives exact half-density bound

\[
 e^{L/2}|\widehat F_{P,t}(L)|
 \le\int_{\mathbb R}
 |P((x-i/2)^2)|^2e^{-t\Re((x-i/2)^2)}\,dx.                \tag{24.162}
\]

Factor `e^(L/2)` is precisely prime entropy remaining after source coefficient `n^(-1/2)`.
Therefore absolute prime envelope is strip-boundary harmonic majorant of every interior zero-orbit
amplitude.  Special polar-null jet cannot reverse inequality: its zero at `z=+-i/2` removes one
boundary point, but supremum moves elsewhere and still strictly exceeds interior exponent.

This closes all moving holomorphic polynomial mass jets as norm/PNT routes, including degree
`asymp t` and exponential coefficient height.  Positive survivor is stronger than no-go:
**half-density source boundary is universal harmonic envelope of squared-divisor dynamics.**
Only signed cancellation among boundary frequencies can fall below envelope.  Critical floor
Wiener rigidity, causal Hardy rigidity, Bessel caustic, and parabolic superresolution are four
manifestations of same maximum-principle/inverse-conditioning law.

### C43-AH — exact three-prime Lorentz compression

The coherent double-prime survivor is infinite only before passing to the moment packet actually
consumed by Turan curvature.  Put

\[
 \mathbf v_n=\bigl(\widehat F_{Q,0,t}(\log n),
                    \widehat F_{Q,1,t}(\log n),
                    \widehat F_{Q,2,t}(\log n)\bigr)\in\mathbb R^3,
 \qquad
 \mathbf P=\frac1\pi\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\mathbf v_n.
 \tag{24.163}
\]

All coordinates are real, and Gaussian Fourier decay makes
`sum Lambda(n)n^(-1/2)||v_n||` finite.  The following finite-dimensional lemma therefore applies.

**Countable conic compression lemma.**  If `a_i>0`, `v_i in R^r`, and
`sum a_i||v_i||<infinity`, then

\[
 \sum_i a_iv_i=\sum_{j=1}^{m}b_jv_{i_j},
 \qquad b_j>0,\qquad m\le r.                              \tag{24.164}
\]

There is no hidden closed-cone assumption.  Choose a full-support probability `p_i>0` and set
`y_i=a_i v_i/p_i`.  The integrable barycentre `sum p_i y_i` belongs to the relative interior of
the closed convex hull of the `y_i`: a supporting affine functional at the barycentre would have
zero nonnegative mean gap, hence vanish at every `y_i`, contradicting the definition of their
affine hull.  Relative interiors of a convex set and its closure agree, so the barycentre lies in
the actual convex hull.  Finite Caratheodory gives at most `r+1` points.  One linear dependence
among their rays removes a positive coefficient, leaving at most `r`.

Applying (24.164) to (24.163) gives actual prime powers `n_1,...,n_m` and aggregate weights
`b_j>0`, with `m<=3`, such that

\[
 \boxed{\quad \mathbf P=\sum_{j=1}^{m}b_j\mathbf v_{n_j},\qquad m\le3.\quad} \tag{24.165}
\]

Let `q_L(x_0,x_1,x_2)=x_0x_2-x_1^2`, and let `A` be the three-component polar--Gamma packet from
(24.145).  Then the complete curvature is exactly

\[
 \Delta_Q(t)=q_L\!\left(\mathbf A-
                  \sum_{j=1}^{m}b_j\mathbf v_{n_j}\right).               \tag{24.166}
\]

This preserves every cross-prime term: compression occurs before applying the Lorentz quadratic.
It also explains why the divergent independent scalar-conductor audit overpaid.  The open source
packet has moment dimension three, so a moving coherent conductor needs at most three aggregate
prime channels, not one channel for every prime.  Compression is pointwise in `(Q,t)` and its
weights retain the complete arithmetic barycentre; universal positivity for arbitrary triples is
false by the one-prime sign computation (24.149).  Thus this is a genuine proof-burden reduction,
not a finite-prime proof.  A viable finite theorem must preserve the moment-matching selector.

The same argument applied to the finite information-cone prefix gives three actual prime powers
inside that prefix plus the certified tail (24.147).  Enlarging the cutoff by any fixed multiple
of `t` makes the tail exponentially small while keeping all selected prime powers below
`exp(O(t+sqrt(td)))` for fixed degree.  No infinite Schur completion remains after this quotient.

### C43-AI — exact prime-square mean--variance defect

For `Q=1` the compression has additional probability structure.  Write

\[
 \phi_t(L)=\sqrt{\frac\pi t}\,e^{-L^2/(4t)},\qquad
 M_t=\frac1\pi\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\phi_t(\log n),
\]

and define probability law

\[
 \mu_t(n)=\frac{\Lambda(n)n^{-1/2}\phi_t(\log n)}{\pi M_t},
 \qquad Y(n)=(\log n)^2.                                  \tag{24.167}
\]

Direct Gaussian differentiation, without any asymptotic expansion, gives

\[
 \begin{aligned}
 f_1(L)&=\phi_t(L)\left(\frac1{2t}-\frac{L^2}{4t^2}\right),\\
 f_2(L)&=\phi_t(L)\left[
 \left(\frac1{2t}-\frac{L^2}{4t^2}\right)^2
 +\frac1{2t^2}-\frac{L^2}{2t^3}\right].
 \end{aligned}                                             \tag{24.168}
\]

Consequently the entire coherent prime--prime determinant is the single centered defect

\[
 \boxed{\quad
 P_0P_2-P_1^2
 =\frac{M_t^2}{16t^4}
 \left(\operatorname{Var}_{\mu_t}(Y)+8t^2
       -8t\,\mathbb E_{\mu_t}Y\right).\quad}              \tag{24.169}
\]

The continuous prime saddle is exactly the Gaussian law `L~N(t,2t)`.  For this law

\[
 \mathbb E(L^2)=t^2+2t,\qquad
 \operatorname{Var}(L^2)=8t^3+8t^2,                      \tag{24.170}
\]

so the bracket in (24.169) vanishes identically.  Thus the huge continuous prime main term is not
merely approximately cancelled: it lies on the boundary of the three-dimensional Lorentz cone,
and prime--prime curvature is its exact Gaussian Stein/variance defect.  This is the first
phase-preserving centering of the large-time saddle in the route.

The existing critical Mobius Fisher--Stein contact law concerns an exponential boundary clock,
not the tilted von-Mangoldt Gaussian law (24.167), so it does not control (24.169).  Moreover a
`PNTPlus` relative error still leaves `e^(t/2-c t^(1/10))` uncertainty after the quadratic
operation.  The positive survivor is sharper: seek an exact completed prime--Gamma Stein identity
for `Y=(log n)^2`, with the polar Gaussian as the null reference, rather than another modulus PNT.

### C43-AJ — Cartan countertransport is the unsmoothed parabolic mass face

The newly formalized reflected Meyer Gaussian supplies an exact bridge from its uniformly bounded
Cartan orbit to the mass heat orbit.  For a divisor copy `q`, put

\[
 a_q=\rho_q-\frac12,\qquad w_q=-a_q^2,qquad
 t_0=\frac1{4\pi}.
\]

Corpus `DeningerMeyerReflectedGaussianCountertransport` constructs source classes `G_c` with
half-density capacity `p(G_c)<=2` and evaluation

\[
 E_q(c)=\left(e^{ca_q}+e^{-ca_q}\right)e^{t_0a_q^2}.      \tag{24.171}
\]

For `tau>0`, let
`K_tau(c)=(4*pi*tau)^(-1/2)exp(-c^2/(4*tau))`.  Gaussian completion gives the exact Weierstrass
transmutation

\[
 e^{-(t_0+\tau)w_q}
 =\frac12\int_{\mathbb R}K_\tau(c)E_q(c)\,dc.             \tag{24.172}
\]

This is also an honest source identity.  In the half-density completion define

\[
 \mathfrak g_\tau=\frac12\int_{\mathbb R}K_\tau(c)G_c\,dc.
\]

Uniform capacity and positivity of `K_tau` give the unconditional integral bound

\[
 p(\mathfrak g_\tau)\le1.                                \tag{24.173}
\]

Evaluation formula (24.172) is proved before completion by absolute Gaussian Fubini; it does not
commute evaluation with this integral by assuming the RH-equivalent continuity theorem.  If
`Q(X)=sum_(k=0)^d q_kX^k`, then

\[
 \operatorname{ev}_q\bigl(Q(-\partial_\tau)\mathfrak g_\tau\bigr)
 =Q(w_q)e^{-(t_0+\tau)w_q},
\]

and scaling of differentiated heat kernels gives actual source-capacity control

\[
 p\bigl(Q(-\partial_\tau)\mathfrak g_\tau\bigr)
 \le\sum_{k=0}^d|q_k|C_k\tau^{-k},
 \qquad C_k=\int_{\mathbb R}|D_k(u)|du<\infty,            \tag{24.174}
\]

where `(-partial_tau)^kK_tau(c)=tau^(-k-1/2)D_k(c/sqrt(tau))`.

This supplies the missing integral theorem for the actual heat jets, with no computation and no
Lean assumption.  It also turns eventual Turan curvature into one source-generated two-jet
reflection problem.  For heat time `T>2t_0`, set `tau=T/2-t_0` and

\[
 v_{Q,T}(q)=Q(w_q)e^{-Tw_q/2}.
\]

On Schwarz-real divisor vectors use the reflection bilinear form
`[f,g]_#=sum_q f(q)g(q)`.  With `W` denoting multiplication by `w_q`, absolute convergence gives

\[
 H_{Q,0}=[v,v]_\#,qquad H_{Q,1}=[v,Wv]_\#,qquad
 H_{Q,2}=[Wv,Wv]_\#,                                     \tag{24.175}
\]

and hence

\[
 \Delta_Q(T)=\det
 \begin{pmatrix}[v,v]_\#&[v,Wv]_\#\\
                 [v,Wv]_\#&[Wv,Wv]_\#\end{pmatrix}.     \tag{24.176}
\]

By eventual completeness (24.153), RH is equivalent to nonnegative two-jet reflection orientation
on this one Gaussian-averaged cyclic source cone.  Generic capacity cannot prove it: corpus
already shows evaluation on the uniformly capacity-bounded family `G_c` is bounded exactly at
critical-line characters.  Off line, `E_q(c)` grows like `e^(|Re a_q||c|)` and positive Gaussian
averaging turns that escape into complex heat phase; positivity of `K_tau` does not survive the
indefinite reflection trace.  The advance is exact restriction of the missing theorem, not a
claim that source capacity implies RH.

### C43-AK — Gaussian Wronskian is the unsquared mass-curvature charge

Newest RHTower corpus constructs two honest target-free Meyer classes whose line-reflected
Wronskian is

\[
 \mathcal W(q)=\frac{\delta_q}{\pi}
 \left|e^{a_q^2/(4\pi)}\right|^2,
 \qquad \delta_q=\Re\rho_q-\frac12.                      \tag{24.177}
\]

It is line-reflection odd, belongs to the multiplicity-exact divisor `ell^2` carrier, and vanishes
identically exactly under RH.  Writing `w_q=A_q+iB_q`, its norm has the explicit mass-faced energy

\[
 \|\mathcal W\|_2^2
 =\frac1{\pi^2}\sum_q\delta_q^2e^{-A_q/\pi}.              \tag{24.178}
\]

This is not merely parallel to Turan curvature.  For the isolated line-conjugate pair
`{q,q#}`, where `rho_q=1/2+delta+i gamma` and `B_q=-2delta gamma`, the filtered pair determinant at
the natural time `T_0=1/(2*pi)` obeys

\[
 \boxed{\quad
 \Delta^{\{q,q^\#\}}_Q(T_0)
 =-8\pi^2\gamma^2|Q(w_q)|^4
   \left(|\mathcal W(q)|^2+|\mathcal W(q^\#)|^2\right).
 \quad}                                                   \tag{24.179}
\]

Thus the negative bottom-shell Turan signal is exactly an ordinate-weighted squared source
Wronskian.  Parabolic curvature is the exterior-square shadow of an unsquared local horizontal
charge already realized by two literal Meyer sources.

The conjecture that (24.178) is itself one global Turan deficit fails: cross-shell terms in
`Delta_Q` survive, whereas the Wronskian norm is diagonal in line-conjugate pairs.  Polynomial
shell filtering plus Cesaro extraction recovers (24.179) one bottom shell at a time, but does not
annihilate all cross-shell terms in one source identity.  The genuine new avenue is the corpus
factorization gate: express the odd Wronskian through one line-reflection-invariant arithmetic
observation.  Parity would then force it to vanish and prove RH.  Prime--Gamma Cauchy landing now
reconstructs the Gaussian zero-jet unconditionally; the missing non-theatrical step is a matching
moment-jet landing whose exterior determinant factors through an invariant completed observation.

### C43-AL — the moment jet has an unconditional prime--Gamma Cauchy landing

The first half of that proposed gate is not open.  Put

\[
 z_q=-i(\rho_q-1/2),\qquad t_0=\frac1{4\pi},\qquad
 G_0(z)=e^{-t_0z^2},\qquad
 G_1(z)=\frac{iz}{2\pi}e^{-t_0z^2}.                     \tag{24.180}
\]

Then `G_0(z_q)` and `G_1(z_q)` are exactly the corpus zero and first reflected-Gaussian Mellin
jets `u(q)` and `v(q)`.  For `r=0,1` define the two-safe-line boundary field

\[
 B_r(x,q)=\frac1{2\pi i}\left(
   \frac{G_r(x+i)}{z_q-(x+i)}-
   \frac{G_r(x-i)}{z_q-(x-i)}\right).
\]

Both fields are Bochner integrable in the multiplicity-exact Xi divisor `ell^2` carrier and

\[
 \int_{\mathbb R}B_0(x)\,dx=u,\qquad
 \int_{\mathbb R}B_1(x)\,dx=v.                          \tag{24.181}
\]

Indeed the corpus proves (24.181) for `r=0`.  On either safe line,
`|G_1(x+/-i)|` is bounded by `C(1+|x|)exp(-t_0x^2)`, while the completed Cauchy-column norm is
`O(1+x^2)`.  Their product is integrable.  The same rectangle Cauchy formula applies because
`G_1` is entire and its vertical sides have polynomial times Gaussian decay.  Continuous
coordinate evaluation then gives the second identity in (24.181).  This proof uses only the two
absolute-Euler safe lines and corpus Cauchy-column estimates; no evaluation-continuity premise at
a divisor character is inserted.

Consequently the source Wronskian itself has the pointwise absolutely convergent boundary formula

\[
 \boxed{\quad
 \mathcal W(q)=\iint_{\mathbb R^2}
 \bigl(B_1(x,q)B_0(y,q^\#)-B_0(x,q)B_1(y,q^\#)\bigr)\,dx\,dy.
 \quad}                                                  \tag{24.182}
\]

Absolute Fubini is legal because each evaluated boundary column is `L^1`, and the two product
majorants factor.  Thus the conjectured moment-jet infrastructure succeeds: the horizontal
charge is already a literal completed prime--Gamma boundary determinant, not an unevaluated
divisor heat sum.

The stronger conjecture that Cauchy landing itself makes (24.182) reflection invariant fails.
The oriented denominators retain which member of `{q,q#}` is first; exchanging them negates the
determinant, exactly as it must off line.  The sole remaining gate is therefore sharper than a
second landing theorem: factor this explicit double boundary kernel through an arithmetic
observation that forgets line-reflection orientation.  Any argument merely symmetrizing the two
columns kills the desired determinant by definition and supplies no factorization.

### C43-AM — exact Cauchy transgression isolates a one-dimensional obstruction

There is a stronger hostile audit of that gate.  Write

\[
 C_z(x)=B_0(x,z),\qquad
 A(x)=\frac1{2\pi i}\bigl(G_0(x+i)-G_0(x-i)\bigr),
 \qquad k=\frac{i}{2\pi}.
\]

Since `G_1(w)=kwG_0(w)` and `w/(z-w)=z/(z-w)-1`, the first boundary jet has the exact affine
decomposition

\[
 B_1(x,z)=k\bigl(zC_z(x)-A(x)\bigr).                    \tag{24.183}
\]

Therefore its two-point exterior kernel is not opaque:

\[
 \begin{aligned}
 D_{z,z'}(x,y)
 &:=B_1(x,z)C_{z'}(y)-C_z(x)B_1(y,z')\\
 &=k\bigl((z-z')C_z(x)C_{z'}(y)
       +C_z(x)A(y)-A(x)C_{z'}(y)\bigr).                \tag{24.184}
 \end{aligned}
\]

Gaussian contour shift gives `integral A=0`: the integrals of `G_0` on the two horizontal safe
lines are equal, with vanishing vertical sides.  Hence the last two terms in (24.184) are exact
tensor coboundaries and

\[
 \iint D_{z,z'}(x,y)\,dx\,dy
   =k(z-z')G_0(z)G_0(z').                               \tag{24.185}
\]

For `z'=z_(q#)=conj(z_q)`, (24.185) is precisely (24.177).  This proves more than failure of an
automatic symmetry: modulo all consequences of entire Cauchy deformation, the boundary
Wronskian has one surviving class, the horizontal orbit difference `z-z#`.  Analytic contour
manipulation, absolute convergence, or safe-line symmetrization can remove only the `A`
coboundaries; it cannot touch this class.

Newest universal projective-descent corpus confirms the logical boundary: factoring the Gaussian
logarithmic jet through even the finest line-reflection orbit observation is equivalent to RH.
Thus abstract invariant factorization is not a reduced proof burden and is retired.  The positive
survivor is more concrete: a successful source theorem must supply an arithmetic identity that
annihilates the non-coboundary coefficient in (24.184) before Cauchy landing.  Equivalently, it
must prove equality of the prime--Gamma first/zero-jet ratios on the two safe-line transports;
no amount of post-landing invariant packaging can do this.

### C43-AN — oscillator action forbids bootstrapping the ultraviolet wedge

Conjecture: use positivity in `t(deg P+1)<=eta`, approximate
`Q(w)e^{-Tw/2}` by `P_t(w)e^{-tw/2}` as `t` tends to zero, and transport the wedge to one fixed
positive time `T`; all-degree positivity there would prove RH.  This fails for a structural reason.

Let

\[
 \mathcal V_{N,t}=\{P(x^2)e^{-tx^2/2}:\deg P\le N\}
 \subset L^2(\mathbb R).
\]

This is the even part of the first `2N+1` oscillator levels at frequency `t`.  Let `g_(d,T)` be the
normalized even Hermite eigenstate of level `2d` and frequency `T`; it has the required form
`Q_d(x^2)e^{-Tx^2/2}` with `deg Q_d=d`.  Its Fourier momentum moments are

\[
 \mathbb E_{g_{d,T}}\xi^2=T(2d+1/2),\qquad
 \mathbb E_{g_{d,T}}\xi^4
 =\frac{3T^2}{4}\bigl(8d^2+4d+1\bigr).                  \tag{24.186}
\]

Hence Paley--Zygmund gives a universal positive amount of its `L^2` mass in
`xi^2 >= (1/2)T(2d+1/2)`.  Conversely, the oscillator quadratic form gives every
`f in V_(N,t)`

\[
 \int \xi^2|\widehat f(\xi)|^2d\xi
 \le t(4N+1)\|f\|_2^2.                                  \tag{24.187}
\]

Markov's inequality on the same momentum region and the triangle inequality now imply universal
constants `c,delta>0` such that

\[
 t(N+1)\le cT(d+1)
 \quad\Longrightarrow\quad
 \inf_{f\in\mathcal V_{N,t}}\|f-g_{d,T}\|_2\ge\delta.   \tag{24.188}
\]

This is a paper proof, not a semiclassical analogy: (24.186) follows from creation--annihilation
identities; their ratio gives a uniform Paley--Zygmund constant, and (24.187) follows from
`-partial_x^2 <= -partial_x^2+t^2x^2` on the first oscillator block.

Therefore stable Gaussian `L^2` transport of a degree-`d` probe from time `T` to time `t` costs
`tN` of order at least `Td`.  The available wedge spends at most `eta`.  For every fixed `T>0`,
high enough target degree lies outside every transported wedge, even though `N` may tend to
infinity as `t` tends to zero.  Heat-semigroup density does not enlarge the source cone.

Positive survivor: `t deg P` is an invariant oscillator action, not an artifact of estimates
(24.135)--(24.138).  Any continuation beyond the wedge must inject arithmetic information as
prime frequencies enter; a purely analytic squeezing/semigroup argument cannot cross it.  This
returns the route to coherent prime--Gamma covariance, but now with a proof that ultraviolet
positivity cannot be recycled to avoid that theorem.

### C43-AO — positive-root shell filters turn the late prime packet into a probability law

The shell filter used in C43-AC need not be an arbitrary CRT interpolant.  If `A` is the first
noncritical squared shell, let `S_A` be the finite set of real squared divisor points with real
part at most `A`.  They are positive, and

\[
 Q_A(X)=\prod_{\lambda\in S_A}(X-\lambda)
\]

kills every competing real point while remaining nonzero at every nonreal point on shell `A`.
This positive-root choice has a new source consequence.

For any real polynomial `Q` with no zero on `(-infinity,0]`, set
`R(u)=Q(-u^2)^2`.  Completing the Gaussian square gives the exact Fourier factorization

\[
 \widehat{Q(x^2)^2e^{-tx^2}}(\xi)
 =\sqrt{\frac\pi t}e^{-\xi^2/(4t)}
 \left[e^{-(4t)^{-1}\partial_u^2}R(u)\right]_
 {u=\xi/(2t)}.                                           \tag{24.189}
\]

Here the exponential is a finite sum because `R` is polynomial.  Since `R(u)>0` on the real
axis and every ratio `|R^(j)(u)|/R(u)` is bounded (continuous on compact sets and vanishing at
infinity for `j>0`), there is `T_Q` such that

\[
 t\ge T_Q\quad\Longrightarrow\quad
 \widehat{Q(x^2)^2e^{-tx^2}}(\xi)>0
 \quad(\xi\in\mathbb R).                                 \tag{24.190}
\]

Thus the exact off-line-detecting filter `Q_A` makes the entire late prime packet positive, not
merely its finite compression.  Put

\[
 p_n(t)=\frac{\Lambda(n)}{\pi\sqrt n}
   \widehat{Q_A(x^2)^2e^{-tx^2}}(\log n),\qquad
 P=\sum_np_n,qquad \mu_n=p_n/P.
\]

For late `t`, define channel score `s_n=-p_n'/p_n` and channel curvature
`c_n=p_n''/p_n-s_n^2`.  Absolute differentiated convergence gives the exact coherent law

\[
 \frac{P_1}{P}=\mathbb E_\mu s,qquad
 \frac{P_0P_2-P_1^2}{P^2}
 =\mathbb E_\mu c+\operatorname{Var}_\mu(s).             \tag{24.191}
\]

The variance is precisely the cross-prime covariance lost by every independent-channel Schur
ansatz.  It is now a positive scalar statistic; all remaining local sign is isolated in
`E_mu c`.

The polar--Gamma part `A=A_0` is also positive for all sufficiently late `t`, because
`Q_A(-1/4) ne 0`, its polar term grows as `e^(t/4)`, and its fixed-polynomial Gamma integral is
only polynomial in `t`.  Write

\[
 m_A=A_1/A,\quad v_A=A_2/A-m_A^2,\qquad
 m_P=P_1/P,\quad v_P=P_2/P-m_P^2.
\]

Then the whole completed curvature (24.148), with `H=A-P`, is exactly

\[
 \boxed{\quad
 \Delta_{Q_A}=H\,(Av_A-Pv_P)-AP(m_A-m_P)^2,
 \qquad v_P=\mathbb E_\mu c+\operatorname{Var}_\mu(s).
 \quad}                                                   \tag{24.192}
\]

This is a genuine reduction of the surviving source theorem: for the filters that detect every
possible first off-line shell, infinite double-prime covariance is equivalent to one positive
score variance, one mean local curvature, and one prime--Gamma score mismatch.  It also prevents
theatre.  Neither positivity of the prime weights nor the variance term proves (24.192); the
negative mismatch square and local curvature remain load-bearing.  Under a false RH, bottom-shell
Cesaro recurrence forces this exact compensation inequality to fail.  New target is therefore a
late-time Fisher--Stein comparison for the positive-root prime law against the polar--Gamma law,
not arbitrary polynomial Fourier sign control.

### C43-AP — heat covariance is a two-dimensional Floquet Gram difference

Newest Deninger corpus identifies critical prime-circle vacuum subtraction with the exact von
Mangoldt autocorrelation current and proves a universal two-bump sign wall for every nonnegative
diagonal prime weighting.  The mass heat packet fits that theorem exactly after retaining its
half-density repetition damping.

Choose Fourier normalization so cross-correlation satisfies
`C_(f,g)(a)=widehat(U_f conjugate(U_g))(a)`.  For fixed `Q,t`, let `u_0,u_1` be the all-weight Meyer
sources with Fourier profiles

\[
 U_0(x)=Q(x^2)e^{-tx^2/2},\qquad U_1(x)=x^2U_0(x).
\]

Define the half-density damped Floquet form

\[
 \mathfrak F_{1/2}(f,g)
 =\frac1{2\pi}\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
   \left(C_{f,g}(\log n)+\overline{C_{g,f}(\log n)}\right). \tag{24.193}
\]

Gaussian decay makes it absolutely convergent.  Prime-circle unfolding and reindexing
`n=p^m` identify (24.193) with the off-diagonal Floquet current whose repetition `m` carries the
literal half-density monodromy `p^{-m/2}`.  Since
`U_i conjugate(U_j)=F_(Q,i+j,t)`, one obtains the exact matrix identity

\[
 \bigl(\mathfrak F_{1/2}(u_i,u_j)\bigr)_{0\le i,j\le1}
 =\begin{pmatrix}P_0&P_1\\P_1&P_2\end{pmatrix}.          \tag{24.194}
\]

The polar--Gamma terms similarly define a Hermitian source form `mathfrak A` on the same plane,
with matrix `(A_(i+j))`.  Therefore

\[
 \boxed{\quad
 \Delta_Q(t)=\det\left(
   (\mathfrak A-\mathfrak F_{1/2})\big|_{
     \operatorname{span}\{u_0,u_1\}}
 \right).
 \quad}                                                   \tag{24.195}
\]

This is the exact cross-corpus bridge requested by the new Floquet work.  Its sign wall rules out
extending `mathfrak F_(1/2)` to a globally positive diagonal form: compact two-bump Meyer sources
already give both signs, and one negative witness is a literal Euler coboundary.  But it does not
rule out (24.195), because only the source-selected Gaussian jet plane and the non-diagonal
polar--Gamma completion occur.

The resulting avenue is precise.  New four-rate Gamma-sewn Cauchy--Binet corpus already produces
positive boundary-pair Pluecker weights and an exact complementary Fisher/dispersion Schur law.
What remains is not a full Mercer representation: construct a coefficient-faithful map from the
plane `{u_0,u_1}` into that Gamma-sewn boundary cell whose Schur residual is exactly
`mathfrak A-mathfrak F_(1/2)`.  Three-prime Lorentz compression shows at most three aggregate
prime rates need enter each moment packet.  A successful four-rate identification would prove
(24.195); absent the exact residual equality, generic Schur positivity is unrelated and must not
be counted as progress.

### C43-AQ — Suzuki's new second jet forbids the even-Gaussian transplant

`SuzukiXiSecondDefectJet` and `SuzukiXiSecondDefectJetSource` supply a sharp hostile test for the
mass plane.  If `F` is even, then `F(-i)=F(i)` and `F'(-i)=-F'(i)`.  The exact reflected-Fourier
source formula therefore gives

\[
 \left.\partial_w^2\left[
   w\frac{F(\operatorname{Cayley}^{-1}w)}
           {F(-\operatorname{Cayley}^{-1}w)}\right]\right|_{w=0}
 =4i\frac{F'(i)F(-i)+F(i)F'(-i)}{F(-i)^2}=0.             \tag{24.196}
\]

Every mass heat Fourier profile `F(z)=Q(z^2)e^{-tz^2}` is even.  By contrast the normalized Xi
target has the source-only second disk jet

\[
 \kappa_{\Xi,2}=8\left(\frac{2C}{A}-\frac BA-
          \left(\frac BA\right)^2\right)<0,
 \quad A=\Re M_0(1),\ B=\Re M_1(1),\ C=\Re M_2(1).       \tag{24.197}
\]

Hence no family staying inside the even Gaussian-polynomial plane can identify the Suzuki Xi
target locally uniformly.  This is not merely a parity aesthetic: the second derivative is
identically zero for every member while the target value is strictly negative.  The new Suzuki
jet does not directly discharge mass curvature.  Its positive survivor is precise: any Suzuki
coupling must introduce an odd/reflection-asymmetric source leg before quotienting, while the mass
Turan determinant must retain its even two-replica form.  Matching only the positive coalescing
rate or the first defect scalar is rigorously insufficient.

### C43-AR — heat and shifted resolvents are two charts of one Laplace--Hankel kernel

The failed scalar transplant hides a common two-variable object.  Write
`H(t)=sum_q exp(-t w_q)` and, on packet classes for which Fubini is justified, define

\[
 \mathfrak B_H(f,g)=\int_0^\infty\!\int_0^\infty
      f(s)g(r)H(s+r)\,ds\,dr.
                                                               \tag{24.198}
\]

Absolute convergence of the Xi divisor gives the exact Laplace landing

\[
 \mathfrak B_H(f,g)=\sum_q (\mathcal Lf)(w_q)(\mathcal Lg)(w_q). \tag{24.199}
\]

For `nu>0`, let

\[
 \gamma_{\nu,y}(s)=\frac{s^{\nu-1}e^{-ys}}{\Gamma(\nu)},
 \qquad \mathcal L\gamma_{\nu,y}(w)=(y+w)^{-\nu}.        \tag{24.200}
\]

If `P(X)=sum_i c_i X^i` and
`f_(P,M,y)=sum_i c_i gamma_(M+i+1/2,y)`, then

\[
 \mathfrak B_H(f_{P,M,y},f_{P,M,y})
 =\sum_q (y+w_q)^{-2M-1}
      P((y+w_q)^{-1})^2.                                  \tag{24.201}
\]

Thus the complete shifted-reciprocal Hankel tail is the fractional-Gamma interior chart of
`mathfrak B_H`.  The half-integer is forced: it is exactly the square root of the leading
resolvent factor.

The mass chart is the confluent boundary chart.  In the distributional packet space put
`T_(Q,k,t)=partial_s^k Q(partial_s) delta_(t/2)`.  Its Laplace transform is
`w^k Q(w)e^{-tw/2}`, and therefore

\[
 \bigl(\mathfrak B_H(T_{Q,i,t},T_{Q,j,t})\bigr)_{i,j=0}^1
 =\begin{pmatrix}H_{Q,0}&H_{Q,1}\\H_{Q,1}&H_{Q,2}\end{pmatrix},
 \qquad \Delta_Q=\det\bigl(\mathfrak B_H|_{\langle T_{Q,0,t},T_{Q,1,t}\rangle}\bigr).
                                                               \tag{24.202}
\]

This is a genuine reduction of the bridge problem: Suzuki resolvent packets, mass heat jets, and
the Floquet two-plane are not three unrelated positivity analogies.  They are interior,
confluent-boundary, and prime-autocorrelation presentations of one completed two-time kernel.

A one-variable positive averaging argument cannot replace this kernel.  Direct Laplace expansion
gives

\[
 \sum_q\lambda_qP(\lambda_q)^2
 =\int_0^\infty e^{-yt}K_P(t)H(t)\,dt,
 \quad K_P(t)=\sum_{i,j}c_ic_j\frac{t^{i+j}}{(i+j)!},
 \quad \lambda_q=(y+w_q)^{-1}.                            \tag{24.203}
\]

For `P(X)=1-X`, `K_P(2)=1-4+2=-1`.  Equivalently `K_P` is the derivative of the
self-convolution of the exponential-generating polynomial `sum c_i t^i/i!`, not a square.
Therefore neither the positive theta endpoint moment measure nor heat positivity transfers by a
scalar positive kernel.  Any valid transfer must preserve the two-time Gram variables.

### C43-AS — radical-anchor coercivity reverses under heat ordering

The new Suzuki critical-radical theorem pays every sufficiently high off-line reciprocal atom
with a fixed critical-line atom.  Its mass analogue fails for an exact structural reason.  For an
off-line heat pair `z=a+ib`, `conj z=a-ib`, and a real critical anchor `c`, the unordered pair
contributions to heat curvature are

\[
 C_{z,\bar z}(t)=-4b^2e^{-2at},
\quad
 C_{z,c}(t)+C_{\bar z,c}(t)
 =2e^{-(a+c)t}\bigl(((a-c)^2-b^2)\cos(bt)
       +2b(a-c)\sin(bt)\bigr).                            \tag{24.204}
\]

If `c>a`, the second expression divided by `|C_(z,conj z)|` is
`O(e^{-(c-a)t})` and tends to zero.  If `c<a`, it can dominate along a phase-recurrence sequence,
but the filtered bottom-shell detector deliberately makes `Q(c)=0` for every lower real shell.
Real points with `c=a` are removed as well.  The next-shell gap then makes the sum of all surviving
higher anchors exponentially negligible.

So Suzuki's cofinite radical payment cannot reduce the mass proof burden.  Möbius resolvent
compactification makes a fixed radical atom dominate the remote tail; heat flow orders by least
real part, and the polynomial shell filter removes exactly the only anchors capable of paying the
least off-line shell.  This explains, rather than merely restates, why filtered Turan completeness
and the Suzuki finite-head reduction point in opposite directions.

### C43-AT — the Gaussian prime jet is an Euler-square/Fisher jet

The common-kernel picture does expose one coefficient-faithful source match.  For `Q=1`, let
`ell=log n`, `E=ell/2`, and
`phi_t(ell)=sqrt(pi/t) exp(-ell^2/(4t))`.  The normalized prime score and local curvature are

\[
 s_E(t)=-\partial_t\log\phi_t
      =\frac1{2t}-\frac{E^2}{t^2},
 \qquad
 c_E(t)=\partial_t^2\log\phi_t
      =\frac1{2t^2}-\frac{2E^2}{t^3}.                    \tag{24.205}
\]

Consequently, for the positive tilted prime law `mu`,

\[
 \frac{P_0P_2-P_1^2}{P_0^2}
 =\frac1{2t^2}-\frac{2}{t^3}\,\mathbb E_\mu E^2
   +\frac1{2t^4}\mathbb E_{\mu\otimes\mu}
      (E^2-E'^2)^2.                                      \tag{24.206}
\]

This is exactly source-visible in the new Gamma-sewn stack.  On a prime-power cell
`n=p^(e+1)`, corpus Euler calibration gives

\[
 E=\frac12\,H_\Gamma(p,e)+\frac14\log p,
 \qquad
 (\log p)^2=\frac32\bigl(K_2(p,e)+H_\Gamma(p,e)^2\bigr), \tag{24.207}
\]

where `K_2` is the boundary second-jet clock.  Thus both `E^2` and the exterior difference
`E^2-E'^2=(E+E')(E-E')` are reconstructed by the calibrated first and second Gamma boundary
jets; no fitted prime statistic is needed.  This is the correct use of the four-rate Fisher
corpus: it supplies the literal prime-square clock in (24.206), not generic Schur positivity.

The bridge is not yet a proof.  Formula (24.206) handles the `Q=1` prime--prime block only;
unfiltered curvature is not RH-complete, and the polar--Gamma/mixed blocks in (24.195) remain.
For general shell filter `Q`, the Gaussian transform is still a finite polynomial in `E^2` times
the same exponential, so the surviving avenue is now exact: build the completed two-time kernel
on polynomial functions of the calibrated Euler-square clock and prove its confluent boundary
Gram determinant nonnegative.  This replaces the vague search for arbitrary four-rate matching
by one coefficient-forced clock-extension theorem.

### C43-AU — the proved Suzuki coefficient cone cannot reach a positive-time heat jet

The common-kernel atlas suggests taking fractional-Gamma packets to the confluent mass boundary.
The unconditional Suzuki sector-circle cone cannot support that limit.  This has an exact Hardy
space proof, independent of asymptotic estimates.

Fix a valuation `M`, put `nu=M+1/2`, and work at the actual safe shift `y=1`.  After removing the
canonical power `X^M`, write `P(X)=b_0R(X)`, where `R(0)=1`.  Every fixed coefficient aperture in
the proved sector cone has the form

\[
 R(X)=1+\sum_{j\ge1}d_jX^j,
 \qquad \sum_{j\ge1}|d_j|^2\le C.                       \tag{24.208}
\]

The normalized Laplace transform of the corresponding fractional-Gamma packet is, with
`x=(1+w)^(-1)`,

\[
 L_R(w)=\frac{(1+w)^{-\nu}P((1+w)^{-1})}{P(1)}
       =x^\nu\frac{R(x)}{R(1)}.                          \tag{24.209}
\]

**Fixed-aperture nonconfluence theorem.**  For every fixed `M`, `C`, and `tau>0`, no sequence of
polynomials satisfying (24.208), with `R_N(1)ne0`, can obey

\[
 L_{R_N}(w)\longrightarrow e^{-\tau w}
 \quad\hbox{for every }w\ge0.                            \tag{24.210}
\]

Indeed (24.208) puts `R_N` in a bounded ball of Hardy `H^2(D)` and fixes `R_N(0)=1`; hence it is a
normal family on every compact subdisk.  If `|R_N(1)|` is unbounded along a subsequence, then for
every fixed `0<x<1` the numerator `R_N(x)` is uniformly bounded and (24.209) tends to zero,
contradicting (24.210).  If `R_N(1)->0`, boundedness of (24.209) forces `R_N(x)->0` for every
`0<x<1`; a locally uniform subsequential limit would vanish on an interval while retaining value
one at zero, another contradiction.  On the remaining subsequence
`R_N(1)->D` with `0<|D|<infinity`, and local normal convergence gives an analytic `R` with
`R(0)=1`.  Equations (24.209)--(24.210) would force

```text
R(x)=D x^(-nu) exp(-tau(1/x-1)),   0<x<1.
```

The right side tends to zero as `x->0+`, contradicting `R(0)=1`.

This closes the tempting passage from the thirteen unconditional shifted circle states to mass
curvature.  A positive-time delta has an essential-flat reciprocal-origin germ, whereas every
fixed-valuation, fixed-aperture Suzuki packet remains in a compact `H^2` resolvent chart.  Thus a
genuine confluent bridge must escape through growing coefficient aperture or valuation, or prove
new completed polar--Gamma positivity before taking the limit.  Existing sector positivity does
none of these, so it does not reduce the exact open core.

### C43-AV — mass heat is a bounded positive reweighting of Xi-shift valuation innovation

The newest `GammaSewnXiShiftTangentInnovation` corpus retains exactly the coordinate lost by the
endpoint tangent kernel.  At physical aperture one its depth law is

\[
 \pi_p(e)=(1-p^{-2})p^{-2e},
 \qquad
 \nu(p,e)=(\log p)\pi_p(e),                              \tag{24.211}
\]

and `nu(p,e)` is literally the forward difference of two adjacent prime-power coefficients of
the completed `+2` Xi-shift source.  Put `y_(p,e)=(e+1)log p` and, for `Q=1`, let the mass-prime
weight be

\[
 a_t(p,e)=\frac{\log p}{\pi},p^{-(e+1)/2}\phi_t(y_{p,e}),
 \qquad \phi_t(y)=\sqrt{\frac\pi t}e^{-y^2/(4t)}.
\]

Then direct cancellation, with no asymptotic input, gives the exact Radon--Nikodym identity

\[
 \boxed{\quad a_t(p,e)=\nu(p,e)R_t(p,e),\qquad
 R_t(p,e)=\frac{\phi_t(y_{p,e})e^{3y_{p,e}/2}}
                  {\pi(p^2-1)}
 =\frac{e^{9t/4-(y_{p,e}-3t)^2/(4t)}}
        {\sqrt{\pi t}(p^2-1)}.\quad}                    \tag{24.212}
\]

In particular

\[
 0<R_t(p,e)\le \frac{e^{9t/4}}{3\sqrt{\pi t}},           \tag{24.213}
\]

so every Gaussian half-density prime packet is an `L^infinity` positive reweighting of a literal
source-derived, depth-resolved innovation measure.  For a positive-root shell filter `Q_A`, replace
`phi_t(y)` in (24.212) by
`widehat{Q_A(x^2)^2e^{-tx^2}}(y)`.  Eventual Fourier positivity (24.190) makes the new density
positive, and polynomial-times-Gaussian decay makes it bounded.  Thus this is not restricted to
unfiltered curvature.

The gain is exact preservation of coherent covariance.  For any cell score `s`, the variance term
is

\[
 P^2\operatorname{Var}_\mu(s)=\frac12
 \sum_{p,e}\sum_{q,f}\nu(p,e)\nu(q,f)R(p,e)R(q,f)
       (s(p,e)-s(q,f))^2.                                \tag{24.214}
\]

This includes pairs with the same prime and different valuation depths.  Consequently the new
prime-only Gamma--Jordan response-gap Laplacian cannot equal mass covariance: its edge weight
vanishes on `p=q`, whereas (24.214) is strictly positive on `p=q,e ne f` whenever the heat score
separates depths.  Equivalently, conditional variance splits (24.214) into a strictly positive
within-prime depth term plus a between-prime endpoint term; endpoint tangent synthesis sees only
the latter.

The negative result exposes a better avenue.  The mass prime law already lives on the literal
Xi-shift innovation carrier, so no abstract source-span closure is needed.  Required construction
is a **depth-resolved Gamma--Jordan Schur lift before endpoint synthesis**, followed by adjoining
the polar states.  Its target coefficients are forced by (24.212), and its two-jet exterior energy
is exactly (24.214).  This is narrower than the previous arbitrary four-rate matching problem and
retains the same-prime valuation curvature that every prime-only kernel discards.

### C43-AW — positive aperture mixing has the wrong valuation curvature

Could (24.212) be generated from corpus's positive synchronized aperture family and then inherit
its Fisher/Schur inequalities automatically?  No.  Fix one prime `p`.  Every positive mixture of
the geometric aperture laws has depth sequence

\[
 m_e=\int_{x>0}(1-p^{-2x})p^{-2xe}\,d\eta(x)
     =\int_{[0,1)}(1-r)r^e\,d\widetilde\eta(r).           \tag{24.215}
\]

Cauchy--Schwarz applied to `sqrt(1-r) r^((e-1)/2)` and
`sqrt(1-r) r^((e+1)/2)` forces the Hausdorff log-convexity law

\[
 m_e^2\le m_{e-1}m_{e+1}\qquad(e\ge1).                  \tag{24.216}
\]

By contrast, after deleting constants independent of `e`, the mass heat depth weight is

```text
h_e=exp(-(e+1)log(p)/2-(e+1)^2 log(p)^2/(4t)).
```

Its adjacent quotient is strictly decreasing, and exactly

\[
 \frac{h_e^2}{h_{e-1}h_{e+1}}
   =\exp\!\left(\frac{(\log p)^2}{2t}\right)>1.          \tag{24.217}
\]

Therefore no finite or infinite positive mixture of synchronized Gamma apertures, even one chosen
separately for each prime, reproduces the mass heat depth law.  This is the valuation version of
the indefinite scalar kernel (24.203): resolvent/aperture packets are completely monotone in
depth, while parabolic heat is strictly log-concave there.

Positive survivor is forced.  Use (24.212) as a diagonal multiplication operator on the literal
innovation `L^2` space; do not average apertures.  Positivity of that reweighting is automatic, but
the completed theorem still requires a coefficient-exact Gamma/polar Schur row whose elimination
leaves this reweighted two-jet covariance.  Existing unweighted valuation Schur block proves the
right architecture, while (24.217) proves that its aperture-mixture closure cannot supply the
needed coefficients.

### C43-AX — coherent Gamma capacity survives the exact heat diagonal

`XiTransverseGammaValuationCoherence` removes one obstacle left in C43-AB.  Put `x_p=p^{-1}` and

\[
 h_e(p)=\sqrt{x_p}(1-x_p)x_p^e,
 \qquad \kappa=\frac{3\sqrt2}{4},\qquad \kappa^2=\frac98. \tag{24.218}
\]

Corpus proves that the corrected Gamma cross-coordinate is exactly `-kappa h_0(p)` and that its
Schur elimination deletes depth zero, leaving the shifted Szego kernel.  The literal innovation
weight (24.211) is a prime-diagonal congruence of the same feature:

\[
 \nu(p,e)=d_p^2h_e(p)^2,
 \qquad d_p^2=\frac{p(p+1)\log p}{p-1}.                  \tag{24.219}
\]

There is a stronger weighted consequence not stated in that module.  For arbitrary finitely
supported real coefficients `u_(p,e)` and arbitrary weights `r_(p,e)>=0`, set

```text
S_e=sum_p sqrt(r_(p,e)) d_p h_e(p) u_(p,e).
```

Then the coherent Gamma block has the exact square decomposition

\[
 \boxed{\quad
 \sum_{e\ge0}S_e^2-2\kappa vS_0+\frac98v^2
   =(S_0-\kappa v)^2+\sum_{e\ge1}S_e^2\ge0.
 \quad}                                                   \tag{24.220}
\]

Thus every nonnegative diagonal congruence preserves the fixed conductor capacity; no sum of
one-prime Schur costs occurs.  Taking `r_(p,e)=R_(Q,t)(p,e)` from (24.212), or its eventually
positive filtered version, makes

\[
 \sqrt{r_{p,e}},d_ph_e(p)=\sqrt{a_{Q,t}(p,e)}.           \tag{24.221}
\]

Absolute Gaussian decay extends (24.220) from finite packets to the complete source by ordinary
square-summable exhaustion.  Hence the earlier nonsummable scalar-conductor wall is resolved for
the exact heat diagonal, not merely for an abstract valuation model.

This still does not prove completed curvature.  Kernel (24.220) is diagonal in valuation depth
before its prime sum, whereas mass exterior energy (24.214) couples every pair `(e,f)` after the
two-jet determinant; moreover the local-curvature part of `P_2` is signed.  Corpus has not proved
that the reweighted Gamma cross in (24.220) equals the polar--prime mixed coefficients in
(24.148).  Exact remaining theorem is therefore smaller: add the missing cross-depth two-jet row
and prove its Gamma/polar coefficient equality.  Capacity and heat reweighting no longer need to
be invented.

### C43-AY — unit-shift cofinal finite part is the natural completed heat source

The heat diagonal points to a better source normalization than the completed `+2` innovation.
Let

\[
 d_1(n)=\Lambda(n)(1-n^{-1}).
\]

This is corpus's actual transverse shift-one arithmetic source, and on the Euler half-plane it is
the corrected `+1` defect of `xi'/xi`.  Pointwise for every `n>=2`, positivity and a geometric
series give

\[
 \boxed{\quad
 \frac{\Lambda(n)}{\sqrt n}
   =d_1(n)\sum_{j\ge0}n^{-j-1/2}.
 \quad}                                                   \tag{24.222}
\]

Consequently Gaussian absolute convergence permits Tonelli for every eventually positive
positive-root shell filter and gives

\[
 P_{Q,0}(t)=\frac1\pi\sum_{j\ge0}\sum_{n\ge2}
   d_1(n)n^{-j-1/2}
   \widehat{Q(x^2)^2e^{-tx^2}}(\log n).                  \tag{24.223}
\]

The equivalent one-step Radon--Nikodym density is

\[
 R^{(1)}_{Q,t}(n)=\frac{\sqrt n}{\pi(n-1)}
   \widehat{Q(x^2)^2e^{-tx^2}}(\log n).                  \tag{24.224}
\]

For `Q=1` this becomes

\[
 R^{(1)}_t(n)=
 \frac{e^{t/4-(\log n-t)^2/(4t)}}{\sqrt{\pi t}(n-1)},
 \qquad 0<R^{(1)}_t(n)\le\frac{e^{t/4}}{\sqrt{\pi t}}.  \tag{24.225}
\]

Unlike the depth-innovation density (24.212), this coefficient-level density is centered exactly
at the true prime saddle `log n=t` and lives at the exact polar scale `e^(t/4)`.  Thus the
half-density and polar residue are two faces of the unit-shift cofinal inverse.

The apparent disadvantage of shift one is actually its decisive feature.  If
`A_infty(s)=logDeriv(archFactor)(s)`, corpus proves

\[
 G_1(s):=A_\infty(s+1)-A_\infty(s)
 =\frac1{s+1}-\frac1{s-1}
   +\frac12\psi\!\left(\frac{s+1}{2}\right)
   -\frac12\psi\!\left(\frac s2\right),                \tag{24.226}
\]

and proves this correction is not rational.  Telescoping plus the standard digamma asymptotic,
already present in corpus, gives the exact cofinal finite-part law

\[
 \lim_{N\to\infty}\left[
   \sum_{j=0}^{N}G_1(s+j)-\frac12\log\frac{N+1}{2\pi}
 \right]=-A_\infty(s),                                  \tag{24.227}
\]

for fixed `s` away from the archimedean poles.  Indeed the sum is
`A_infty(s+N+1)-A_infty(s)`, while
`A_infty(s+N+1)-(1/2)log((N+1)/(2pi))->0`.

This reinterprets the missing completion.  Rationalizing one even `+2` cell hides the Gamma seam;
the cofinal unit-shift ladder reconstructs the full polar--Gamma logarithmic derivative as its
canonical finite part, while (24.222) reconstructs the literal half-density prime current with
positive coefficients.  Since determinant is nonlinear, the ladder must be completed **before**
taking its two-jet exterior square; telescoping first discards precisely the mixed terms sought in
(24.148).

The new exact frontier is a renormalized-cofinal Schur theorem: on the two Gaussian jet vectors,
form finite unit-shift source Grams, subtract the universal logarithmic endpoint in (24.227) at
matrix level, and prove that their exterior-square limit is nonnegative.  Equations
(24.222)--(24.227) force the prime and archimedean coefficient candidates, but do **not** by
themselves justify Gaussian-test/finite-part interchange, identify the endpoint as the claimed
rank-one jet row, or preserve positivity after subtraction.  Those are proof obligations, not
consequences of telescoping.  This is nevertheless the first avenue here that produces prime,
Gamma, polar, and mixed channels from one actual completed-Xi source rather than asking for an
exogenous conductor match.

### C43-AZ — finite unit ladder and exact endpoint leverage obstruction

The cofinal inverse in (24.222) has a dependency-closed finite form.  For every `N>=0`,

\[
 d_1(n)\sum_{j=0}^{N}n^{-j-1/2}
 =\Lambda(n)n^{-1/2}\bigl(1-n^{-N-1}\bigr).              \tag{24.228}
\]

Hence, writing `W(n)=widehat F_(Q,t)(log n)`,

\[
 \begin{aligned}
 P^{[N]}_{Q,0}(t)
 &:=\frac1\pi\sum_{n\ge2}d_1(n)W(n)
       \sum_{j=0}^{N}n^{-j-1/2},\\
 P_{Q,0}(t)-P^{[N]}_{Q,0}(t)
 &=\frac1\pi\sum_{n\ge2}\Lambda(n)n^{-N-3/2}W(n).       \tag{24.229}
 \end{aligned}
\]

Absolute Gaussian decay proves convergence without a prime number theorem.  Whenever the late
positive-root filter makes `W(n)>=0`, the approximation is monotone from below and the remainder
is positive.  Thus the prime face of the unit ladder has no limiting ambiguity.

The archimedean finite part has a different obstruction.  If a finite raw source Gram is positive
definite and its proposed endpoint counterterm is `L_N u u*`, then elementary congruence gives

\[
 \boxed{\quad
 G_N-L_Nuu^*\succeq0
 \quad\Longleftrightarrow\quad
 L_N\,u^*G_N^{-1}u\le1.
 \quad}                                                   \tag{24.230}
\]

Therefore positivity of the raw ladder does not survive finite-part subtraction for free.  The
missing theorem is an endpoint **leverage bound**, together with the coefficient theorem saying
that the logarithmic counterterm really is the required rank-one row on the chosen jet plane.
This corrects the stronger informal claim after (24.227).  The new cofinal Ward corpus proves an
analogous four-unit boundary-leverage law is equivalent to RH, so importing that target column
would merely rename the theorem.

### C43-BA — Gamma averaging identifies the shift-one Hankel cone with a rational mass cone

Newest reciprocal-Hankel corpus gives a more useful completion of the unit-shift idea.  Put
`w_q=alpha_q^2` and

\[
 \lambda_{y,q}:=\frac{\xiZeroCopyReciprocalSquare(q)}
 {1+y\,\xiZeroCopyReciprocalSquare(q)}
 =\frac1{w_q+y},
 \qquad
 \mu_m(y):=\sum_q\lambda_{y,q}^{m+1}.                    \tag{24.231}
\]

For `p(X)=sum_(i=0)^d c_iX^i`, cutoff `M>=0`, and

\[
 Q_{p,d,y}(W):=(W+y)^d p\bigl((W+y)^{-1}\bigr)
 =\sum_{i=0}^dc_i(W+y)^{d-i},                            \tag{24.232}
\]

absolute divisor convergence and the Gamma integral give the exact transmutation

\[
 \boxed{\begin{aligned}
 \sum_{i,j=0}^dc_ic_j\mu_{2M+i+j}(y)
 &=\sum_q\lambda_{y,q}^{2M+1}p(\lambda_{y,q})^2\\
 &=\sum_q\frac{Q_{p,d,y}(w_q)^2}
                 {(w_q+y)^{2(M+d)+1}}\\
 &=\frac1{(2M+2d)!}\int_0^\infty
    t^{2M+2d}e^{-yt}\,\mathcal H_{Q_{p,d,y}}(t)\,dt.
 \end{aligned}}                                         \tag{24.233}
\]

This is not an analogy: it is a positive Gamma average of the same polynomial-filtered mass heat
trace from (24.114).  Corpus theorem
`primeArchShiftedReciprocalHankelTailNonnegative_one_iff_riemannHypothesis`, at `M=0`, therefore
becomes the new exact mass criterion

\[
 \boxed{\quad
 \mathrm{RH}\ \Longleftrightarrow\
 \forall d\ \forall Q\in\mathbb R[W],\ \deg Q\le d:\quad
 \Re\frac1{(2d)!}\int_0^\infty t^{2d}e^{-t}
        \mathcal H_Q(t)\,dt\ge0.
 \quad}                                                   \tag{24.234}
\]

The polynomial maps in (24.232) are inverse on degree at most `d`:
`p(X)=X^dQ(X^(-1)-y)`.  Thus no test has been discarded.

On the explicit source line, Gamma averaging collapses the Gaussian family to one rational test:

\[
 \frac1{(2d)!}\int_0^\infty t^{2d}e^{-t}
 Q(x^2)^2e^{-tx^2}\,dt
 =\frac{Q(x^2)^2}{(1+x^2)^{2d+1}}
 =\frac{p((1+x^2)^{-1})^2}{1+x^2}.                      \tag{24.235}
\]

Its only poles are at `+-i`; residue calculus gives Fourier decay `e^(-|L|)` times a polynomial.
After the critical half-density, the prime series is therefore bounded by an absolutely
convergent `Lambda(n)n^(-3/2) poly(log n)` series.  Criterion (24.234) removes the moving heat-time
parameter and the PNT superresolution wall: every test now lives at the fixed absolute-Euler
shift `s=3/2`, where corpus already identifies the zeroth moment with `xi'/xi(3/2)` and every
higher entry with the explicit prime--Gamma negative-binomial tower.

### C43-BB — averaging and polynomial filtering do not commute positively

A hostile check explains why the filtered Gamma lift in (24.233) is load-bearing.  Expanding the
same shifted Hankel quadratic against the *unfiltered* heat trace gives

\[
 \sum_{i,j}c_ic_j\mu_{2M+i+j}(y)
 =\int_0^\infty e^{-yt}\mathcal H_1(t)K_{M,p}(t)\,dt,
 \qquad
 K_{M,p}(t)=\sum_{i,j}c_ic_j
 \frac{t^{2M+i+j}}{(2M+i+j)!}.                           \tag{24.236}
\]

The divided-factorial matrix here is not positive semidefinite.  At `M=0` its first `2x2` block
is

\[
 \begin{pmatrix}1&t\\t&t^2/2\end{pmatrix},
 \qquad \det=-t^2/2<0,
\]

and `p(X)=1-X` gives `K_(0,p)(1)=-1/2`.  Consequently scalar heat positivity, or any positive
mixture of unfiltered diagonal heat slices, cannot prove the shifted Hankel cone.  Formula
(24.233) succeeds because it absorbs the whole polynomial into `Q` **before** Gamma averaging.
This is the resolvent analogue of completing the unit-shift ladder before taking exterior square.

### C43-BC — exact use and exact limit of the new Suzuki/Ward corpus

Three new corpus results now meet at the same boundary.

1. `XiShiftedReciprocalHankelTailCriterion` proves that the source-only shift-one Hankel tail is
   equivalent to RH after every finite cutoff.  This validates (24.234) as a complete source
   criterion, but supplies no unconditional sign.
2. `SuzukiTwoJetShiftedHankelGate` identifies the first safe-shift minor exactly:

   \[
    \operatorname{SuzukiSlack}
    =16\frac{\mu_0(1)\mu_2(1)-\mu_1(1)^2}{\mu_0(1)^2}.  \tag{24.237}
   \]

   `SuzukiCoalescingXiSourceRate` and `SuzukiCoalescingParityLocking` now give the exact first-jet
   rate and endpoint selector.  But `SuzukiCoalescingBlaschkeFragmentation` proves arbitrary
   Blaschke degree can hide in the same first jet, and the two-jet gate controls only this first
   minor.  No finite-jet bootstrap to the cofinal Hankel cone is possible.
3. `GammaSewnMobiusXiWardHardyNonexpansive` proves unconditional non-diagonal target-Hardy
   contractivity.  The actual cofinal rank-one boundary lift, however, satisfies

   \[
    4G_P-r_Pr_P^*\succeq0\ \text{ for every finite packet }P
    \quad\Longleftrightarrow\quad\mathrm{RH},             \tag{24.238}
   \]

   by `GammaSewnMobiusXiWardCofinalBoundaryLift`; the corpus also proves the fixed transport is
   expansive in the physical source norm.  Target multiplier contractivity therefore cannot
   supply the leverage inequality (24.230).

The genuine new avenue is narrower than the finite-part exterior conjecture after (24.227): prove
the Gamma-averaged rational inequalities (24.234) directly as unit-shift **source-side** Schur
residuals, with finite prime ladder (24.228) and archimedean counterterm removed before Schur
elimination.  This avoids pointwise late-time PNT precision and asks for one coefficient-exact
source leverage theorem.  It remains open; identifying it with the existing Xi Ward boundary
column would be circular by (24.238).

**Novelty audit.**  `PrimeHeatBumpLocation` already contains the single-atom peak law, and the
digamma asymptotic and Gaussian Fourier identities are classical.  Corpus and arXiv searches found
no statement combining exact mass-parabolic source, the polar residue repair, superexponential
complete-prime-jet suppression, strict finite-degree heat-Hankel positivity, the universal
degree--time wedge, filtered-Turan completeness, prime information cone, eventual curvature, and
exponential-height repair, three-prime Lorentz compression, prime-square mean--variance defect,
Cartan--parabolic source transmutation, Gaussian Wronskian--Turan identity, the moment-jet
prime--Gamma double-boundary landing, and its one-dimensional Cauchy-transgression obstruction.
Novelty claim also includes the oscillator-action no-bootstrap law tying the universal wedge to
stable heat transport and eventual Fourier positivity/Fisher reduction for positive-root shell
filters, the Gaussian two-jet/Floquet Gram bridge, the even-Gaussian Suzuki second-jet obstruction,
the two-time Laplace--Hankel atlas, reversal of radical-anchor coercivity under heat order, the
Euler-square/Fisher clock identification, and the fixed-aperture nonconfluence theorem.  Synthesis
also includes the bounded positive reweighting of literal Xi-shift valuation innovations and its
endpoint-collapse obstruction, plus the log-convex/log-concave aperture-mixture separation.  It
also includes heat-diagonal stability of coherent `9/8` Gamma capacity, the finite unit-ladder
leverage obstruction, and Gamma-averaged equivalence between the shift-one reciprocal Hankel cone
and the rational mass cone.  The synthesis is (24.128)--(24.238), including unit-shift cofinal
finite-part reconstruction, not any ingredient in
isolation.  Closest located arXiv neighbours concern de Bruijn--Newman deformation
([arXiv:1904.12438](https://arxiv.org/abs/1904.12438)), Jensen-polynomial hyperbolicity
([arXiv:1910.01227](https://arxiv.org/abs/1910.01227)), and a coefficient-side uniform Toeplitz
wedge ([arXiv:2607.16795](https://arxiv.org/abs/2607.16795)); none states divisor-heat
filtered-Turan criterion or prime-information-cone theorem above.

**Higher universal principle.**  Mass-shifted propagation has two inequivalent scaling faces and
one two-time kernel behind them.
Vertical timelike scaling preserves exponential type and creates the Bessel caustic; co-moving
mass then erases off-line charge beyond the square-root horizon.  Real parabolic scaling removes
the universal rest mass and retains the squared divisor as Gaussian heat.  The former is a
transport/type problem; the latter is a reflection-positivity problem.  Earlier failures were
shadows of using the transport topology after its inverse had become exponentially ill-conditioned.
The parabolic face is the first route here that simultaneously preserves the full Xi geometry and
keeps the literal source absolutely convergent.  Gamma averaging reveals that its heat and
resolvent charts are related by a degree-dependent positive transform: degree `d` is sent to a
Gamma clock concentrated at time of order `2d`, and the resulting rational test sits at the fixed
absolute-Euler shift.  This transform kills the PNT superresolution problem but preserves the
entire RH cone.  Earlier failures were shadows of collapsing polynomial filtering, time averaging,
and endpoint subtraction in the wrong order.  Remaining obstacle can now be stated in either of
two exactly equivalent source charts: coherent completed heat curvature (24.148)--(24.150), or
unit-shift Gamma-averaged leverage (24.230), (24.234).  Resolvent compactification and heat order
reverse which spectral atoms are coercive; treating them as the same topology was the hidden
reason radical payment and positive scalar averaging both failed.

**Higher principle.**  Three failures are one phenomenon.  Local Lipschitz control, ordinary floor
averaging, and finite-aperture mean square each erase the primitive scalar mode in a topology whose
inverse has exponential or order-`X` condition.  Weighted-floor threshold (24.27)--(24.28) makes
this quantitative: smoothing strong enough to prove known endpoint lies below critical
invertibility threshold, while every type-zero-stable coordinate preserves whole RH obstruction.
Mass receiver lives in finer quotient where that mode has exponent `beta-1/2`.  A successful
theorem must retain one of three resources currently absent: coupled signed triangular transport
before collapsing harmonic projection (24.41), a scale-sensitive signed prime correlation for
timelike Bessel phase, or a
nonlinear/prime-adaptive Jordan-cofinal synthesis.  Another scalar synthesis with inverse condition
`exp(o(u))` is ruled out abstractly by critical floor Wiener lemma (24.36).

## Log

- 2026-08-08 — `[PROVED HERE]` finite true-prime cone, square cone-tail, exact prime polynomial,
  rapidity phase geometry, and prime-log quadrature-defect criterion; hostile audit completed.
- 2026-08-08 — `[PROVED HERE]` exact bounded-coboundary bridge to the outgoing current and
  uniform moving prime-annulus cancellation, closed minimal strip-limited cone, plus cofinally
  vanishing cutoff jumps; failed generic mean-square, Hilbert-energy, finite-frame/QEC,
  adjacent-prime stationary-phase, and metric-only Möbius/Euler clock-transport closures.
- 2026-08-08 — `[PROVED HERE]` sharp Bessel entropy--action slope
  `kappa_B=a/sqrt(a^2-1/4)`: endpoint exterior prime tail is `O(u^(-1/2))`, every larger tail
  decays exponentially, and every smaller raw cone has an exponentially divergent coherent prime
  annulus.  Replaced strip-limited hard core by exact caustic defect (18.1).
- 2026-08-08 — `[PROVED HERE]` `PNTPlus.MediumPNT` turns its
  `exp(-c(log x)^(1/10))` error into a `C_0` prime-discrepancy layer of width `L u^(1/10)` inside
  the Bessel caustic, with exact method wall
  `L_c=c kappa_B^(1/10)/(2a^2-1/2)`, yielding the sharper criterion (19.7).
- 2026-08-08 — `[PROVED HERE]` exact graded cone/type law (20.3): allowed source type `lambda`
  has sharp raw-cone slope `kappa_(a,lambda)`, interpolating from the RH Bessel caustic at
  `lambda=0` to the physical light cone at `lambda=1/2`.
- 2026-08-08 — `[PROVED HERE]` Bessel prefactor budget: raw source has a sharp logarithmic
  caustic at retreat `(2m_B)^(-1) log u`; after the `PNTPlus`-critical `L_c u^(1/10)` retreat,
  the same prefactor buys an additional `(2m_B)^(-1) log u+O(1)` discrepancy layer and yields
  the smaller exact criterion (21.10).
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` caustic-null polynomial mass jets preserve every
  spectral shell while raising the caustic prefactor from `u^(-1/2)` to `u^(-N-1/2)`, permitting
  every fixed additional logarithmic retreat.  Fixed holomorphic multipliers cannot remove the
  timelike core because its stationary dispersions fill `(a,infinity)`.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` graded rigidity collapses all `o(u)` caustic
  retreats in the type-zero quotient.  For every moving boundary `H(u)/u->kappa_B`, RH is
  equivalent to subexponential growth of its finite true-prime prefix or quadrature defect.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` hostile type-zero audit: actual integral Lipschitz
  transport leaves the scalar Chebyshev-error quotient and absolute `PNTPlus` control retains type
  `1/2`; ordinary Selberg floor averaging is square-root bounded precisely because its `zeta`
  symbol annihilates zero modes; generalized Dirichlet mean square requires exponential prime-log
  aperture.  Extracted the Jordan-floor symbol law
  `Mellin(T_k R)=(-1)^k zeta^(k) Mellin(R)` and the exact critical-scale hierarchy sufficient to
  expose zeros of every finite multiplicity without dividing by `zeta`.  Also extracted the
  critically stable harmonic-floor coordinate `Q=T_(1/n)R`, with exact inverse
  `R=T_(mu/n)Q`; critical normalization makes the inverse coefficients summable as
  `mu(n)/n^(3/2)`, reducing the mass current to one positive-weight floor average rather than an
  unstable `1/zeta` inversion.
- 2026-08-08 — `[PROVED HERE; LEAN-PROVED (threshold); LEAN DEFERRED (sawtooth gate)]` full weighted-floor audit: `theta=1/2` is sharp
  type-zero invertibility threshold for `T_(n^(-theta))`; hence every stable floor coordinate is a
  preconditioner, while square-root Selberg endpoint necessarily lies below threshold.  Exact
  floor-fibre Abel summation improves crude error from `O(M^2)` to explicit reciprocal-sawtooth
  prime correlation `sum_(m<=M)(Lambda(m)-1){N/m}` and isolates coupled two-clock statistic that
  must be controlled.  Endpoint anchoring then identifies it exactly with centered triangular
  hyperbola transport (24.33); existing norm-first transport theorems lose signs and critical scale.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` critical floor Wiener lemma: every Dirichlet-floor
  filter whose critical weighted truncation norm and inverse norm are `N^o(1)` preserves type zero
  exactly.  This closes all subpower-conditioned scalar preconditioners, not only power weights;
  any useful escape must pay positive type, prove RH-strength signed inverse cancellation, or use
  nonlinear prime-adaptive structure.
- 2026-08-08 — `[PROVED HERE; LEAN-PROVED]` harmonic triangular projection collapse: exact
  finite Fubini gives `sum_D w_D C_N(D)=B_N(N)-Q(N)-2γ H_N`.  Thus signed harmonic transport is
  precisely original stable core in new coordinates.  Exact positive path kernel (24.42)--(24.43)
  shows why diagonal energy loses order `N^2`, and its first path value already contains `R(N)`.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` superluminal causal-compression rigidity: for every
  `H>u>=0`, the critically gauged massive half-wave compressed to `(0,H)` retains exact operator
  norm `exp(lambda u)`.  Negative-corona modulation packets prove sharpness.  Fixed analytic
  damping and actual outgoing differential retain exact type `lambda` on every cone `H=kappa u`,
  `kappa>1`.  Since both outgoing cone slope and Bessel caustic exceed light speed, Hardy support
  cannot remove critical radiation.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` fixed-causal-filter rigidity: every nonzero bounded
  Hardy multiplier retains exact damped mass type `lambda` after superluminal compression.
  Lowering type requires moving exponential notch on every surviving negative-corona packet;
  inverse conditioning then pays same critical type.  This is microlocal twin of floor Wiener law.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` Selberg anchor/mass-horizon mismatch: acquiring
  critical relative error `delta=X^(-1/2+epsilon)` from harmonic small-value theorem requires
  log-window width `>40 X^(1/2-epsilon)`, exponential in mass log-time.  Any `O(h)` mass window
  yields only `delta=Omega(1/h)` and retains type `1/2`.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` exact harmonic-primitive/mass-adjoint reduction:
  finite Abel summation replaces `R(n)` by vanishing `E_n=J_n+2γ`, but adjoint cell quotient
  restores precisely displaced-zero exponent `beta-1/2`.  Separate norm or BV estimates remain
  type-sharp; only signed `E_n`--mass-increment correlation survives.
- 2026-08-08 — `[PROVED HERE; LEAN-PROVED (recursion); LEAN DEFERRED (scale audit)]` finite harmonic-primitive ladder rigidity: exact
  conjugate recursion `C(f,A)=boundary+C(Hf,DA)` shows each primitive lowers source power by one
  while mass adjoint raises receiver power by one.  Every finite depth preserves scale
  `n^(beta-1/2)`; repeated Abel integration cannot reduce RH proof burden.
- 2026-08-08 — `[PROVED HERE; LEAN-PROVED]` exact resolvent identification: in critical log
  normalization harmonic remainder tail has symbol `-(1/2-i*xi)^(-1)`, while mass outgoing current
  has symbol `1/2-i*xi`.  Their product is `-1` frequency-by-frequency; cell quotient is exact
  weighted average of same outgoing inverse.  Only noncommuting phase/prime-adaptive transforms can
  change proof burden.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` smooth Bessel-phase gauge no-go: exact covariant Abel
  identity moves receiver phase into harmonic source tail, but on each timelike ray gauge is only a
  bounded local Mellin twist.  Every displaced-zero mode keeps scale `n^(beta-1/2)`; useful
  connection must be genuinely arithmetic and scale-growing.
- 2026-08-08 — `[CORPUS TRANSPLANT; PAPER AUDITED]` critical moving-mass source on `4sigma v=1`
  obeys unconditional `O(u log u)` zero-density bound.  It is type zero, but subtracting it from
  fixed source preserves exponential type exactly; mass backtransport is exponentially
  ill-conditioned.
- 2026-08-08 — `[CORPUS TRANSPLANT; PAPER AUDITED]` arithmetic connection dichotomy: scaled
  anchored two-prime commutator is uniformly equivalent to raw seam difference and has positive
  off-line floor; exact prime-power phase nodes occupy at most one prime ray and vanish in global
  prime-clock quotient.  Only relation-valued approximate cross-prime cancellation survives.
- 2026-08-08 — `[PROVED HERE; LEAN-PROVED]` square-root mass information horizon: exact identity
  `|Im beta_a| Re beta_a=R|J|` shows every fixed off-line orbit is erased when `a(u)^2/u->infinity`
  and its line-conjugate pair diverges when `a(u)^2/u->0`.  Existing critical/subcritical `C_0`
  schedules are linear and quotient-null; sub-square-root moving mass is a new faithful carrier,
  pending cross-orbit positive separation.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` finite-packet sub-square-root receiver: for
  `a(u)=u^theta`, `1/3<theta<1/2`, exact chirp normal form and integral mean square prove finite
  conjugation-stable mass trace is `C_0` exactly when packet is critical.  Open bridge is uniform
  positive separation for growing full Xi packet plus prime-side control.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` parabolic mass blow-up: after removing rest mass,
  `exp(2a^2t) exp(-2at sqrt(a^2+w))` converges to `exp(-tw)` over complete Xi divisor, with a
  uniform exponential majorant.  Exact positive subordination kernel makes this the Gaussian heat
  approximate identity and eliminates growing-packet cancellation.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` exact mass-jet/heat-Hankel bridge: the operator
  `L_a=partial_tau^2-a^2` has exact eigenvalue `w=alpha^2`, so polynomial mass jets recover every
  polynomial-square Gaussian RH test.  An integral Lipschitz bound reduces target to integer
  polynomials and positive rational times.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` literal parabolic Euler transfer: differentiated
  mass source identity and dominated convergence put every Gaussian-Hermite Hankel test on one
  absolutely convergent Euler line.  New exact core is global prime--Gamma positivity (24.120).
  Large-mass pair positivity and termwise von-Mangoldt positivity both fail; `P(X)=X` already has
  sign-changing Hermite prime weights.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` parabolic orientation decomposition: every filtered
  analytic mass jet equals positive Hermitian mass minus an explicit sum-of-squares phase defect;
  in heat limit `D_1(t)=sum exp(-tA_q)(1-cos(tB_q))`, whose all-time vanishing is exactly RH.
  Existing KMS/Gram positivity controls ambient mass but not required sharp orientation budget.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` completed source normalization repaired: rational
  polar terms produce positive residue; fixed-degree complete prime jet is superexponentially
  invisible, giving strict ultraviolet heat-Hankel positivity.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` Hermite phase-space separation upgrades this to
  universal wedge `t(deg P+1)<=eta` and global prime information cone
  `log n=O(t+sqrt(t deg P))`, coefficient-uniform and using no PNT.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` RH is equivalent to nonnegative polynomial-filtered
  Turan curvature `H_Q H_Q''-(H_Q')^2`; finite shell interpolation, phase recurrence, and shell gap
  remove simple-bottom restriction in newest heat-Turan corpus.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` eventual filtered log-convexity already forces RH;
  exact bottom-shell Cesaro mean is strictly negative off line.  Rationalization yields countable
  fixed-degree integer endpoint with coefficient height `exp(O(t))`, matching prime information
  radius.  Finite-degree criterion lies between criticality of first `d+1` and first `d+2` shells.
- 2026-08-08 — `[FAILED WITH POSITIVE SURVIVOR]` one-prime/KMS covariance is sign-indefinite and
  independent scalar Gamma conductor has nonsummable Schur cost.  Exact survivor is coherent
  double-prime kernel plus mixed polar--Gamma covariance (24.148)--(24.150).
- 2026-08-08 — `[FAILED WITH POSITIVE SURVIVOR]` large-time PNT/saddle closure is exponentially
  underresolved: `e^(t/4)` prime saddle cancels polar residue while shell signal is `e^(-At)`;
  `PNTPlus` error remains `e^(t/4-c t^(1/10))`.  Exact pre-norm completed covariance is mandatory.
- 2026-08-08 — `[FAILED WITH POSITIVE SURVIVOR]` moving polar-null jets cannot beat the universal
  half-density strip envelope.  Maximum principle leaves signed cross-prime cancellation as the
  only route below boundary scale.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` every complete three-moment prime packet compresses
  exactly to at most three actual prime-power frequencies with positive aggregate weights before
  the Lorentz determinant.  Infinite independent-channel Schur cost is not intrinsic.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` for `Q=1`, coherent prime--prime curvature is the
  exact mean--variance/Stein defect of the tilted prime log-square law; the continuous Gaussian
  saddle saturates the identity exactly.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` Gaussian averaging transmutes the uniformly bounded
  reflected Meyer countertransport into every parabolic heat jet with an explicit integral
  capacity bound.  Turan curvature is one two-jet reflection determinant on this cyclic source
  cone; generic evaluation continuity remains RH-equivalent.
- 2026-08-08 — `[CORPUS TRANSPLANT + PROVED BRIDGE; LEAN DEFERRED]` the new Gaussian source
  Wronskian is horizontal displacement times positive density, and an isolated mass-Turan pair at
  time `1/(2*pi)` is exactly its negative ordinate-weighted squared energy.  Global cross-shell
  terms block direct norm closure; invariant arithmetic factorization is the surviving avenue.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` the reflected-Gaussian moment jet admits the same
  unconditional two-safe-line prime--Gamma Cauchy landing as the zero jet.  Their exterior product
  is an absolutely convergent double boundary formula for the horizontal Wronskian.  Landing
  itself retains orientation; only factorization through a line-reflection-invariant arithmetic
  observation remains open.
- 2026-08-08 — `[FAILED WITH POSITIVE SURVIVOR]` exact affine Cauchy transgression splits the
  double boundary Wronskian into two contour coboundaries plus one surviving horizontal-orbit
  coefficient.  Universal projective descent proves abstract invariant factorization is
  RH-equivalent.  Only a pre-landing arithmetic equality of reflected prime--Gamma logarithmic
  jets can remove the surviving class.
- 2026-08-08 — `[FAILED WITH POSITIVE SURVIVOR]` oscillator momentum moments prove a quantitative
  no-bootstrap theorem: stable transport of a degree-`d`, time-`T` Gaussian polynomial into the
  time-`t`, degree-`N` wedge requires `tN` comparable to `Td`.  Degree--time action is invariant;
  ultraviolet positivity cannot be squeezed to one all-degree positive time.
- 2026-08-08 — `[PROVED HERE; LEAN DEFERRED]` first-off-line-shell filters can be chosen with only
  positive real roots; their Gaussian-square Fourier transforms are strictly positive for all
  sufficiently late times.  The coherent prime packet is then an honest probability law, and
  completed Turan curvature reduces exactly to polar--Gamma/prime curvature compensation minus a
  score-mismatch square, with cross-prime coherence retained as score variance.
- 2026-08-08 — `[CORPUS TRANSPLANT + PROVED BRIDGE; LEAN DEFERRED]` critical Floquet unfolding
  identifies the three heat prime moments as the Gram matrix of the half-density damped von
  Mangoldt autocorrelation form on the two-dimensional Gaussian jet plane.  Universal two-bump
  indefiniteness forbids global diagonal positivity.  Surviving avenue is an exact Gamma-sewn
  Schur residual on this plane, needing at most three compressed aggregate prime rates.

## Addendum: safe-shift dispersion, arcsine recession, and terminal boundary flux

### C43-BD — the safe-shift first gate reduces to one coefficient-of-variation floor

Write one shifted reciprocal atom as `lambda=a+ib`, and use the exact response coordinates from
`SuzukiSafeShiftResponseChargeCancellation`

\[
 e=a,\qquad x={a^2-b^2\over a},\qquad
 \chi={b^2(a^2+b^2)\over a}.
\]

For `A=sum e`, `mu=(sum ex)/A`, the first shifted Hankel minor is exactly

\[
 \boxed{\quad
 m_0m_2-m_1^2
 =D-Q,\qquad
 D=A\sum e(x-\mu)^2,\qquad Q=A\sum\chi.
 \quad}                                                    \tag{24.239}
\]

Corpus sector bound `b^2/a^2<=1/84` gives the pointwise sharp consequence

\[
 {\chi\over ex^2}
 ={b^2(a^2+b^2)\over(a^2-b^2)^2}
 \le {85\over83^2}={85\over6889}.                         \tag{24.240}
\]

Hence, with expectation taken under probability weights `e/A`,

\[
 {\operatorname {Var}_e(x)\over \mathbb E_e(x^2)}
 \ge {85\over6889}
 \quad\Longrightarrow\quad D\ge Q
 \quad\Longrightarrow\quad m_0m_2-m_1^2\ge0.             \tag{24.241}
\]

This is a genuine proof-burden reduction: Suzuki's first nonlinear Schur gate needs only a
dimensionless longitudinal dispersion floor of about the same size as the corpus transverse
sector cap.  Existing corpus proves `D>0` but not this quantitative ratio.  Its explicit bound
`Q(1)<116/7968750000` would also close the gate from any source-derived lower bound of that size
for `D(1)`.

The natural attempt to manufacture that floor from the present zero-distribution corpus fails.
Infinite support, `sum 1/|rho|=infinity`, square summability, and the upper count `O(T log T)` do
not imply any prescribed lower tail for `sum 1/|rho|^2`.  Indeed, choose rapidly increasing
`R_j` and put `M_j` points in the `j`th shell with `M_j` comparable to `R_j/j`.  Then

\[
 \sum_j{M_j\over R_j}=\infty,\qquad
 \sum_j{M_j\over R_j^2}\asymp\sum_j{1\over jR_j}<\infty,  \tag{24.242}
\]

while sufficiently rapid shell spacing respects every upper `O(T log T)` count.  The square tail
can be made arbitrarily small after a chosen height.  A quantitative dispersion proof therefore
needs a lower local zero-density input or a different source identity; current upper-density and
harmonic-divergence theorems cannot supply it.

### C43-BE — no finite right shift makes all polynomial atoms positive

A tempting conjecture was that a sufficiently large real shift narrows every reciprocal atom so
much that all degree-`d` polynomial squares become atomwise positive.  It already fails for
degree one.  If `lambda` is nonreal, the real-linear map

\[
 (u,v)\longmapsto u+v\lambda
\]

is onto `C`.  Choose `z` with `Re(lambda z^2)<0` and solve `u+v lambda=z`; then the real linear
polynomial `p(X)=u+vX` obeys

\[
 \Re\bigl(\lambda p(\lambda)^2\bigr)<0.                  \tag{24.243}
\]

Thus angular narrowing helps a coefficient-conditioned test, never the whole degree cone.
There is no degree-only finite shift giving termwise positivity unless every atom is already
real.  Generic Krylov/replica projection laws cannot repair this: they have no connector to the
Xi source moments and would merely hide the same unbounded coefficient conditioning.

### C43-BF — all shifted moments have a universal arcsine far-right limit

Put

\[
 m_k(y):=\Re\,\xiShiftedReciprocalMoment(y,k),\qquad
 L(w):=\xiRealLogDeriv(w),\qquad y=w^2.
\]

The new `CompletedPrimeGammaMomentFarRightAsymptotic` corpus contains all ingredients needed beyond
its stated odd-moment corollary.  `xiLogDeriv_split`, the horizontal digamma asymptotic, and first-
prime Euler decay give

\[
 {L(w)\over\log w}\longrightarrow {1\over2},\qquad
 w^jL^{(j)}(w)\longrightarrow
 {(-1)^{j+1}(j-1)!\over2}\quad(j\ge1).                  \tag{24.244}
\]

For completeness, the horizontal digamma limit on the full real ray follows from the corpus
integer-shift limit by squeezing between adjacent integers, using strict monotonicity of real
digamma and monotonicity of `log`; no unproved continuous asymptotic is being imported.

Let `A=(2w)^(-1)d/dw=d/dy`.  Induction gives constants `c_(k,j)` such that

\[
 A^k\!\left({L(w)\over w}\right)
 =\sum_{j=0}^k c_{k,j}w^{-(2k+1-j)}L^{(j)}(w),\qquad
 c_{k,0}=(-1)^k(1/2)_k.                                  \tag{24.245}
\]

All terms with `j>=1` are `O(w^(-2k-1))`; only `j=0` carries `log w`.  Combining
`xiRealLogDeriv_eq_mul_re_xiShiftedReciprocalMoment` with
`iteratedDeriv_squaredXiRadialField` therefore proves, for every fixed `k`,

\[
 \boxed{\quad
 \lim_{y\to\infty}{4y^{k+1/2}\over\log y}\,m_k(y)
 =c_k:={(1/2)_k\over k!}={\binom{2k}{k}\over4^k}.
 \quad}                                                    \tag{24.246}
\]

These constants are not an arbitrary positive sequence.  They are the arcsine moments

\[
 c_k={1\over\pi}\int_0^1{x^k\over\sqrt{x(1-x)}}\,dx.     \tag{24.247}
\]

Let `H_n(y)=(m_(i+j)(y))_(0<=i,j<n)` and

\[
 R_n(y)=\operatorname {diag}_{0\le i<n}
 \left({2y^{i+1/4}\over\sqrt{\log y}}\right).
\]

Then entrywise

\[
 R_n(y)H_n(y)R_n(y)\longrightarrow C_n:=(c_{i+j})_{i,j<n}. \tag{24.248}
\]

For every nonzero real polynomial `p` of degree below `n`, (24.247) gives
`p^T C_n p=int p(x)^2 dnu_arc(x)>0`; hence `C_n` is strictly positive definite.  Openness of the
finite-dimensional positive-definite cone now proves unconditionally:

> For every fixed `n`, `H_n(y)` is strictly positive definite for all sufficiently large `y`.

Consequently, if RH is false, the least degree of a shifted-Hankel defect is finite at every fixed
shift but tends to infinity with the shift.  Off-line information does not disappear; it recedes
to polynomial degree infinity.  This is the resolvent analogue of Gaussian cooling recession,
now derived directly from the completed Gamma--Euler source.

### C43-BG — finite Hankel evolution is a Lyapunov flow with one terminal flux

Exact moment differentiation is

\[
 m_k'(y)=-(k+1)m_{k+1}(y).
\]

Let `T_n` be the weighted upper shift `(T_n)_(i,i+1)=i+1/2`, let `e=e_(n-1)`, and put
`v_n(y)_j=(n-1/2)m_(n+j)(y)`.  Entrywise algebra gives the exact finite-dimensional law

\[
 \boxed{\quad
 H_n'=-T_nH_n-H_nT_n^T-(ev_n^T+v_ne^T).
 \quad}                                                    \tag{24.249}
\]

For `E_y(s)=exp((s-y)T_n)`, this integrates to

\[
 H_n(y)=E_y(Y)H_n(Y)E_y(Y)^T
 +\int_y^Y E_y(s)(ev_n(s)^T+v_n(s)e^T)E_y(s)^T\,ds.       \tag{24.250}
\]

Thus interior shift transport is pure congruence and cannot change inertia.  Every possible sign
change enters through one rank-two terminal boundary flux.  This is the higher principle shadowed
by the earlier rank-one leverage and finite-part failures.

Let `D_n=det H_n`, and let `A_n` be the bordered Hankel determinant obtained by replacing the last
row `(m_(n-1+j))_j` by `(m_(n+j))_j`.  Jacobi's formula and (24.249) give, wherever `H_n` is
invertible and hence everywhere by polynomial continuation,

\[
 D_n'=-(2n-1)A_n,qquad
 D_n(y)=(2n-1)\int_y^\infty A_n(s)\,ds.                  \tag{24.251}
\]

The second identity uses `D_n(infinity)=0`, supplied by (24.246).  More precisely, the arcsine
limit gives

\[
 D_n(y)\sim {\det C_n\over4^n}
 { (\log y)^n\over y^{n^2-n/2}},\qquad
 A_n(y)\sim {n\over2y}D_n(y)>0.                           \tag{24.252}
\]

The derivative asymptotic is justified by the full jet limits (24.244)--(24.246), not by
formally differentiating an uncontrolled little-`o`.  Every fixed boundary flux is therefore
eventually oriented positively.  The exact core is now a finite-position flux reversal problem,
not construction of a positive far boundary.

### C43-BH — Möbius half-density transport explains degree-infinity inflow

For the shifted atom `lambda_y=(y+w)^(-1)` and `t>=0`,

\[
 \lambda_{y+t}={\lambda_y\over1+t\lambda_y}.             \tag{24.253}
\]

If

\[
 \Phi_y[p]:=\Re\sum_q\lambda_{y,q}p(\lambda_{y,q})^2,
\]

define the half-density Möbius semigroup

\[
 (\mathcal S_t p)(z):=(1+tz)^{-1/2}
 p\!\left({z\over1+tz}\right).
\]

Then absolute divisor convergence gives the exact transport identity

\[
 \boxed{\quad \Phi_{y+t}[p]=\Phi_y[\mathcal S_t p].\quad} \tag{24.254}
\]

Its generator is `-z^2 d/dz-z/2`, whose monomial matrix is `-T_infinity^T`.  Formula (24.249) is
exactly the leakage created by truncating this infinite congruence at degree `n`.  Backward
transport is

\[
 (\mathcal S_{-t}p)(z)=(1-tz)^{-1/2}
 p\!\left({z\over1-tz}\right),                            \tag{24.255}
\]

with a singularity at `z=1/t`.  Since `Re w_q>0`, far-shift atoms obey
`|t lambda_(y+t,q)|<t/(y+t)`.  A uniform Taylor connector therefore has geometric ratio
`r=t/(y+t)=1-y/(y+t)`; even for `p=1`, its omitted tail contains
`c_(N+1)r^(N+1)`.  Fixed accuracy as `t->infinity` needs degree at least of order `t/y`.
This is the exact degree horizon behind every failed attempt to transport fixed-degree far-right
positivity back to shift one.  `KrylovProjectedCompleteIncidenceLaw` supplies factorial bounds for
bounded generators, but this Möbius generator is degree-raising and unbounded; there is no Xi
connector that changes the horizon.

### C43-BI — first loss is a real-rooted terminal anti-Stieltjes event

Suppose a block first reaches the positive-semidefinite boundary while every smaller leading block
is positive definite.  Its Schur-null vector has last coefficient one; write it as the monic
polynomial `p(X)=sum_(j=0)^(n-1)c_jX^j`.  Then

\[
 \mathcal L_y(X^jp)=0\quad(0\le j<n),\qquad
 \mathcal L_y(f):=\Re\sum_q\lambda_{y,q}f(\lambda_{y,q}). \tag{24.256}
\]

Contracting (24.249) with this null vector kills both congruence terms and leaves

\[
 c^TH_n'(y)c=-(2n-1)\mathcal L_y(X^np).                  \tag{24.257}
\]

At the first crossing from an indefinite block to the far-right positive chamber, the left side
is nonnegative.  Hence every RH failure produces a boundary witness with

\[
 \mathcal L_y(X^np)\le0.                                 \tag{24.258}
\]

Moreover, positivity of all preceding leading minors makes the monic orthogonal polynomial `p`
the characteristic polynomial of a real symmetric Jacobi compression.  Its roots are real and
simple.  Therefore it is enough to prove one source theorem:

> every monic real-rooted null polynomial satisfying (24.256) has
> `mathcal L_y(X^n p)>0`.

This criterion is equivalent to preventing all finite-degree inflow from the arcsine chamber.  It
is materially narrower than arbitrary polynomial-square positivity: hard witnesses are forced to
the Schur boundary, are real-rooted, and require only one next mixed moment.  It is not yet proved.
`PrimeTailReflectionFoldedSecondOrderResolvent` reconstructs literal prime forcing against compact
supports, but only as a linear transport equality with arbitrary homogeneous datum; it supplies no
quadratic Gamma completion or sign for (24.258).  `EvenIndexHermitianDyadicOrbit` likewise needs an
exact dyadic coefficient recursion absent from the Xi shifted-moment tower.  Importing either as a
positivity argument would be theatre.

### Research status after C43-BI

- `[PROVED HERE; LEAN DEFERRED BY USER]` sector cap reduces first Suzuki gate to exact weighted
  coefficient-of-variation floor (24.241).
- `[FAILED]` present zero upper density plus harmonic divergence cannot provide quantitative
  dispersion floor; sparse-shell model (24.242) is class-complete obstruction.
- `[FAILED]` no finite right shift gives atomwise positivity for all degree-one tests (24.243).
- `[PROVED HERE; LEAN DEFERRED BY USER]` every fixed shifted Hankel block converges after diagonal
  normalization to strictly positive arcsine moment block (24.246)--(24.248).
- `[PROVED HERE; LEAN DEFERRED BY USER]` exact finite Lyapunov law, Duhamel formula, bordered
  determinant flux identity, and positive far-right flux asymptotic (24.249)--(24.252).
- `[PROVED HERE; LEAN DEFERRED BY USER]` exact Möbius half-density semigroup and linear inverse
  degree horizon (24.253)--(24.255).
- `[PROVED HERE; LEAN DEFERRED BY USER]` any first loss is a real-rooted null polynomial with a
  nonpositive terminal mixed moment (24.256)--(24.258).
- `[OPEN]` prove terminal anti-Stieltjes exclusion directly from completed prime--Gamma source.
  This is current noncircular frontier.  RH is not proved.

## Lean status (in progress)

Sections 1--4 were already formal in the corpus.  The four closed inputs of §2 are Lean theorems:

    RHTower/XiMassCriticalCenteredAtomCone.lean
      riemannHypothesis_iff_xiMassCriticalCenteredAtomConeLineBound   §2.1 centered finite cone
    RHTower/XiMassCriticalIntegerFace.lean
      norm_xiMassCriticalIntegerConeSum_le,
        xiMassCriticalCentered_add_integer_eq_primeAtomConeSum,
        riemannHypothesis_iff_xiMassCriticalPrimeAtomConeLineBound     §2.2 + §3 integer face
    RHTower/XiMassPrimeSquareBoundaryResidue.lean
      exists_norm_xiMassPrimeSquareLayer_vertical_bound               §2.3 full square layer
    RHTower/XiMassCriticalPrimeSquareTail.lean
      cone_exponent_le_neg_half                                       §4.1 cone half-decay
      norm_xiMassCenteredPrimeSquareAtom_beyond_cone_le,
        summable_norm_xiMassCriticalPrimeSquareConeTail,
        norm_xiMassCriticalPrimeSquareConeTail_le                     §4.2 uniform square tail
    RHTower/XiMassPrimePowerVerticalIdeal.lean
      xiMassCenteredPrimeAtom_support_primePower,
        summable_norm_xiMassHighPrimePowerAtom,
        norm_xiMassHighPrimePowerTail_vertical_le                     §5 higher prime powers

Newly formalized, axiom-clean (`[propext, Classical.choice, Quot.sound]`), wired, built:

    RHTower/XiMassCriticalTruePrimeCone.lean
      vonMangoldt_mul_dampedProfile_eq_centeredPrimeAtom   the cone summand is the depth-free
                                                          centered prime atom
      xiMassCriticalConeAtom, its support, summability     the cone as a truncated atom family
      tsum_xiMassCriticalConeAtom_eq_primePower            the cone reindexed by prime powers
      tsum_coneAtom_exponent_split,
        tsum_xiMassCriticalConeAtom_eq_three               **(6.2)** the exact three-layer split
                                                          `L_u = P_u + Q_u + R_u`
      norm_xiMassCriticalHighCone_le                       **§5** `R_u` is uniformly bounded
      xiMassPrimeSquareLayer_eq_cone_add_tail,
        exists_norm_xiMassCriticalSquareCone_bound         **§4** `Q_u = S_{2,u} - T_u` is
                                                          uniformly bounded
      xiMassCriticalPrimeAtomConeLineBound_iff_truePrimeCone,
        riemannHypothesis_iff_xiMassCriticalTruePrimeConeLineBound
                                                          **(6.1)** RH is equivalent to uniform
                                                          boundedness of the moving cone supported
                                                          on true primes only
      xiMassCriticalTruePrimeCone_eq_finsetSum             the true-prime cone as a finite sum
      xiMassCriticalTruePrimeDirichletConePolynomial,
        xiMassCriticalTruePrimeCone_eq_integral_dirichlet,
        riemannHypothesis_iff_xiMassCriticalTruePrimeDirichletConePairingLineBound
                                                          **(7.1)** the exact prime-supported
                                                          Dirichlet face and its RH criterion

    RHTower/XiMassRapidityPhaseGeometry.lean
      timelikeRapidity, cosh/sinh_timelikeRapidity,
        massPhase_timelike,
        massPhase_timelike_stationary_iff                 **(8.2)** inside the cone the phase is
                                                          `q cosh(t+η)` with the single stationary
                                                          point `t = -η`
      spacelikeRapidity, cosh/sinh_spacelikeRapidity,
        massPhase_spacelike,
        massPhase_spacelike_nonstationary                 **(8.3)** outside the cone the phase is
                                                          `r sinh(t+η)`, never stationary
      massPhase_onCone, massPhase_onCone_nonstationary     on the cone the phase is `u e^t`

    HTGeometry/BesselExteriorEnvelope.lean
      one_add_sq_div_two_le_cosh, cosh_le_exp,
        integrable_exp_quadratic, integral_exp_quadratic
      besselK1C, norm_besselK1C_integrand,
        norm_besselK1C_le                                 **(17.8)-(17.9)** the exterior Bessel
                                                          envelope for complex argument, with the
                                                          square-root gain
      sqrt_le_csqrtRe, normSq_ratio_le                    **(17.5)** Lemma 17.1, both halves

      xiMassCriticalConeEdge, xiMassCriticalConeEdge_ge,
        xiMassCriticalPrimeLogMeasure,
        integral_dampedProfile_primeLogMeasure           **(9.1)** the atomic Stieltjes pairing
                                                        `int K dTheta = P_u` with
                                                        `dTheta = sum (log p) delta_{log p}`
      xiMassCriticalPrimeQuadratureDefect,
        xiMassCriticalTruePrimeConeLineBound_iff_quadratureDefect,
        riemannHypothesis_iff_xiMassCriticalPrimeQuadratureDefectLineBound
                                                        **(9.2)** RH is equivalent to uniform
                                                        boundedness of the critical quadrature
                                                        defect between the true-prime logarithmic
                                                        measure and its continuum density

Sections 10--13 are the conjecture/audit record and assert no new theorem.  Still to formalize:
§8.1's rapidity integral representation, and sections 14--24.

### Lean progress: sections 8, 14, 17.1--17.3

Newly formalized, axiom-clean (`[propext, Classical.choice, Quot.sound]`), wired, built:

    RHTower/XiMassRapidityMassPhase.lean
      xiMassRapidityPhaseKernel,
        xiMassHyperbolicFourierKernel_eq_rapidity,
        stripFourier_xiMass_eq_integral_rapidityPhase      **(8.1)** the exact rapidity
                                                           representation with real amplitude and
                                                           the single mass phase
      xiMassCriticalDampedFourierProfile_eq_integral_rapidityPhase
      xiMassRapidityPhaseKernel_timelike/_spacelike/_onCone  **(8.2)-(8.3)** the collapsed kernel

    RHTower/XiMassTruePrimeCoboundaryBridge.lean
      xiMassCriticalTruePrimeCone_sub_outgoingFlux_eq      **(14.1)** exact coboundary identity
      exists_norm_truePrimeCone_sub_outgoingFlux_bound     **(14.2)** bounded coboundary
      exists_norm_truePrimeCone_depth_difference_bound     **(14.3)** annulus cancellation
      exists_norm_primeAtomCone_sub_truePrimeCone_bound,
        exists_norm_primeAtomCone_sub_centeredCone_bound   **(14.7)**
      xiMassConeDepthOfSlope, _slope, _half_lt, _lt_iff    the depth realizing a prescribed slope
      xiMassConeEdge_antitone, exists_depth_floor_stabilizes

    RHTower/XiMassEndpointClosedCone.lean
      xiMassCriticalOutgoingDeepShiftBound_eq/_mono        the deep-shift moment is affine in `d`
      exists_uniform_norm_xiMassCriticalSquareCone_bound,
        exists_uniform_norm_truePrimeCone_sub_outgoingFlux_bound
                                                           one coboundary constant on `[d0,a)`
      xiMassCriticalConeAtom_eq_of_floor_eq,
        xiMassCriticalTruePrimeCone_eq_of_floor_eq,
        exists_interior_depth_eq_endpoint                  prefix stabilization at the endpoint
      exists_norm_endpointTruePrimeCone_sub_outgoingFlux_bound  **(14.10)**
      riemannHypothesis_iff_xiMassCriticalEndpointConeLineBound  **(14.11)**
      norm_integral_growingFourierProfile_at_endpointCone_le,
        riemannHypothesis_iff_xiMassCriticalEndpointQuadratureDefectLineBound  **(14.13)-(14.14)**
      integral_dampedProfile_endpointPrimeLogMeasure

    HTGeometry/BesselOrderExteriorEnvelope.lean
      ofReal_realModifiedBesselKOrder_one,
        realModifiedBesselKOrder_one_le                    **(17.8)-(17.9)** the order-one
                                                           Schlaefli envelope with square-root gain

    RHTower/XiMassBesselConeEnvelope.lean
      sqrt_fullGap_le_csqrtRe_propagationArgument,
        sigma_le_csqrtRe_propagationArgument,
        sqrt_slopeGap_mul_le_csqrtRe_propagationArgument   **(17.5)** Lemma 17.1, all three bounds
      norm_stripFourier_xiMass_le_besselExterior           **(17.6)**
      norm_stripFourier_xiMass_le_besselExteriorSqrt       **(17.7)** valid for every `u>0`

    RHTower/PrimeLogRpowTail.lean
      sum_prime_log_rpow_dyadic_block_le,
        sum_prime_log_rpow_dyadic_tail_le,
        sum_prime_log_rpow_tail_le                         Chebyshev tail `sum_{p>X} (log p)
                                                           p^{-1-delta} <= C_delta X^{-delta}`

    RHTower/XiMassBesselConeTail.lean
      xiMassBesselConeExponent, _nonneg                    `eta_kappa >= 0` exactly from `kappa_B`
      sub_add_sqrt_le_sqrt_gap,
        xiMassBessel_exterior_exponent_le                  **(17.13)**
      norm_xiMassCenteredPrimeAtom_exterior_le,
        sum_norm_xiMassCenteredPrimeAtom_exterior_le       **(17.11)** exterior tail `C e^{-eta u}`
      norm_xiMassCriticalTruePrimeCone_slope_difference_le uniform prime-annulus cancellation
      riemannHypothesis_iff_xiMassCriticalBesselConeLineBound  **(17.12)** the closed sharp
                                                           Bessel cone criterion

Still to formalize: Corollary 17.4, Theorem 17.5, and sections 19--24.

### Lean progress: 17.4 and section 20

    RHTower/XiMassBesselConeQuadratureDefect.lean
      norm_xiMassCriticalGrowingFourierProfile_exterior_le,
        integral_exp_neg_shift_le,
        norm_integral_growingFourierProfile_exterior_le      **(17.16)** the exterior continuum
                                                             tail `C e^{-eta u}/(a-1/2)`
      xiMassCriticalConeEdge_pos, xiMassCriticalConeEdge_mono_slope
      exists_norm_integral_growingFourierProfile_at_besselCone_le
                                                             the closed-cone continuum prefix is
                                                             uniformly bounded
      riemannHypothesis_iff_xiMassCriticalBesselQuadratureDefectLineBound  **(17.15)** Corollary
                                                             17.4

    RHTower/XiMassGradedBesselConePhase.lean
      xiMassGradedConeSlope, one_le/one_lt_xiMassGradedConeSlope  **(20.1)**
      xiMassBesselConeExponent_gradedConeSlope              **(20.2)** `Gamma_a(kappa_{a,lam})
                                                             = lam`
      xiMassGradedConeSlope_zero, _half                     `kappa_{a,0}=kappa_B`,
                                                             `kappa_{a,1/2}=1`
      xiMassBesselConeExponent_mono                         `Gamma_a` is antitone in the slope
      XiMassCriticalOutgoingFluxLineGrowth,
        xiMassBottomPrimeLineGrowth_iff_outgoingFluxLineGrowth,
        xiMassCriticalOutgoingFluxLineGrowth_iff_nonnegative,
        xiMassCriticalOutgoingFluxLineGrowth_iff_mass_displacement_le
                                                             the graded source law transported to
                                                             the outgoing current
      exists_norm_besselCone_sub_outgoingFlux_type_le,
        xiMassCriticalBesselConeLineGrowth_iff_mass_displacement_le,
        xiMassCriticalBesselConeLineGrowth_gradedSlope_iff   **(20.3)** the graded Bessel cone
                                                             criterion; `lam = 0` is Theorem 17.3

Still to formalize: Theorem 17.5 and (20.4) (both need the uniform large-argument Bessel
asymptotic), section 19 (needs the differentiated exterior envelope and `MediumPNT`), and
sections 21--24.

### Lean progress: the uniform Bessel asymptotic

    HTGeometry/BesselOrderLaplaceAsymptotic.lean
      integral_even_eq_two_mul_complex, integral_Ioi_gaussian,
        sq_mul_exp_neg_mul_sq_le, integral_Ioi_sq_mul_exp_neg_mul_sq_le,
        integrable_sq_mul_exp_neg_mul_sq                elementary Gaussian facts
      besselLaplaceProfile, besselLaplaceProfile_sub_nonneg/_sub_le,
        abs_besselLaplaceProfile_sub_le                 `0 <= P(v) - 1/sqrt 2 <= v^2/sqrt 2`
      besselLaplaceKernel, besselK1C_eq_integral_laplaceKernel
                                                        the substitution `v = sqrt 2 sinh(t/2)`
                                                        turns the Schlaefli integral into an exact
                                                        Gaussian integral against `P`
      integral_Ioi_cexp_neg_mul_sq                      half-line complex Gaussian
      besselK1C_sub_leading,
        norm_besselK1C_sub_leading_le                   **the uniform large-argument asymptotic**
                                                        `K_1(w) = e^{-w}(sqrt(pi/(2w)) + R)`,
                                                        `|R| <= sqrt 2 e^{-Re w} sqrt(2 pi/Re w)
                                                                /(e Re w)`

This is the analytic input Theorem 17.5 and section 19 need.  What still separates them from a
Lean proof is the exact Fourier--Bessel identity (17.1)

    F_u(h) = 2 a tau_u / z_u(h) * K_1(a z_u(h)),

which needs the complex-rapidity contour shift `t -> t - zeta` with
`cosh zeta = tau_u/z_u(h)`, `sinh zeta = i h/z_u(h)`.  The corpus already owns the imaginary-shift
half of that (`RHTower.integral_horizontal_shift_of_decay`,
`integral_xiMassHyperbolicEntireKernel_shift_eq`); the real-translation half is Lebesgue
invariance; what is missing is the uniform strip decay bound for a general complex rapidity.

### Lean progress: the Fourier--Bessel identity at real vertical time

    HTGeometry/BesselOrderLaplaceAsymptotic.lean (continued)
      integrable_besselK1C_integrand,
        integral_cosh_mul_exp_neg_cosh,
        integral_odd_eq_zero                            whole-line Schlaefli integrals

    RHTower/XiMassFourierBesselRealTime.lean
      xiMassRealTimeRotation, its range, cos/sin        `theta = arctan(h/sigma)`
      xiMassRealTimePhase_rotated                       `sigma cosh(x-i theta) + i h sinh(x-i theta)
                                                         = sqrt(sigma^2+h^2) cosh x`
      stripFourier_xiMass_realTime_eq_bessel            **(17.1) at `u = 0`**
                                                        `F_0(h) = 2 a sigma/q * K_1(a q)`,
                                                        `q = sqrt(sigma^2+h^2)`

The remaining step to the general (17.1) is analytic continuation in `tau` from the positive real
axis to the open right half plane.  All three ingredients are now standard:
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` applies verbatim with a complex parameter
(`RCLike` covers `ℂ`), so `besselK1C` and `tau |-> stripFourier (xiMassAnalyticTest a tau) h` are
both complex-differentiable on `Re tau > 0`; the principal root `sqrt(tau^2+h^2)` avoids the cut
there (if its imaginary part vanishes its real part is positive); and the identity theorem applies
because the positive reals cluster in the half plane.

### Lean progress: (17.1) at complex vertical time

    HTGeometry/PrincipalSquareRootDeriv.lean
      csqrt_eq, continuousAt_csqrt, csqrt_ne_zero,
        hasStrictDerivAt_csqrt, differentiableAt_csqrt,
        differentiableOn_csqrt, csqrt_ofReal_of_pos      the principal square root is holomorphic
                                                         on the right half plane (inverse-function
                                                         theorem against `w -> w^2`)

    HTGeometry/BesselOrderLaplaceAsymptotic.lean (continued)
      integrable_exp_neg_mul_sq_shift,
        cosh_sq_mul_exp_neg_mul_cosh_le,
        integrable_cosh_sq_mul_exp_neg_mul_cosh          the differentiated Schlaefli majorant
      norm_cosh_ofReal, hasDerivAt_besselK1C,
        differentiableAt_besselK1C                       `K_1` is holomorphic on `Re w > 0`

    RHTower/XiMassFourierBesselIdentity.lean
      xiMassHyperbolicKernelC, its norm, integrability   the hyperbolic kernel at complex time
      xiMassProfileC, xiMassProfileC_eq_stripFourier
      hasDerivAt_xiMassProfileC                          the mass profile is holomorphic in `tau`
      xiMassBesselStrip, convex/open/positive-argument   `V_h = {0 < Re tau, |Im tau| < h}`
      xiMassBesselSide, differentiableAt_xiMassBesselSide
      xiMassProfileC_eq_besselSide_real                  agreement on the positive real axis
      xiMassProfileC_eq_besselSide,
        stripFourier_xiMass_eq_bessel                    **(17.1)**
                                                         `F_u(h) = 2 a tau / z * K_1(a z)`,
                                                         `z = csqrt(tau^2 + h^2)`, on the whole
                                                         spacelike strip `|u| < h`

The strip covers every cone `h >= kappa u` with `kappa > 1`, so (17.1) is now available exactly
where Theorem 17.5 and section 19 use it.

### Lean progress: shell expansion toward Theorem 17.5

    HTGeometry/PrincipalSquareRootDeriv.lean (continued)
      cpow_half_re_pos, cpow_half_sq, csqrt_eq_cpow_half
                                                        the principal root is the principal
                                                        one-half power on the right half plane

    HTGeometry/BesselOrderLaplaceAsymptotic.lean (continued)
      re_ofReal_div_pos,
        besselK1C_sub_leading_csqrt,
        norm_besselK1C_sub_leading_csqrt_le             **(17.9)** the asymptotic in
                                                        principal-square-root form

    RHTower/XiMassSpacelikeShellExpansion.lean
      xiMassShellArgument, its real part and positivity
      xiMassShellDefect, xiMassShellRadius
      xiMassShellArgument_sub_shellRadius_sq            **(17.19)** the exact, height-independent
                                                        defect `sigma^2 + s^2 -
                                                        (kappa s + i sigma)^2/(kappa^2-1)`
      shellRadius_re_ge, csqrt_shellArgument_re_ge      both radii have real part at least `q u`
      norm_csqrt_shellArgument_sub_shellRadius_le       **(17.19)** `|z - zeta| <= ‖defect‖/(2 q u)`,
                                                        explicit and uniform on every window of `s`

Remaining for Theorem 17.5: assemble (17.1), (17.9) and (17.19) into the shell asymptotic (17.20);
then (17.21) — the shell prime sum, which needs the corpus PNT `theta(x) ~ x` plus finite Stieltjes
partial summation — and finally the reverse-triangle assembly against the exterior tail (17.23),
which is already available as `sum_norm_xiMassCenteredPrimeAtom_exterior_le` (its proof never used
`eta_kappa >= 0`).

    HTGeometry/PrincipalSquareRootDeriv.lean (continued)
      csqrt_eq_of_sq_of_re_pos, re_ofReal_mul_pos, re_inv_pos,
        csqrt_ofReal_mul, csqrt_inv                     multiplicative rules for the principal root

    RHTower/XiMassShellLeadingTerm.lean
      sqrt_two_pi_mul_eq, besselLeading_collapse        **(17.20, leading term)** the Schlaefli
                                                        leading term of (17.1) collapses to
                                                        `sqrt(2 pi a) * tau * e^{-a z} / (z sqrt z)`

### Lean progress: the shell phase and radius

    HTGeometry/PrincipalSquareRootDeriv.lean (continued)
      norm_csqrt_sub_one_le, norm_mul_csqrt_sub_one_le  `csqrt` and `w -> w sqrt w` are Lipschitz
                                                        at `1` on the right half plane

    RHTower/XiMassShellPhase.lean
      shellQ, shellQ_pos, shellQ_sq, xiMassShellRadius_eq
      shellPhase, norm_shellPhase                       the fixed unit vector `i e^{-i a sigma/q}`
      exp_neg_mul_shellRadius                           **(17.20)** `e^{-a zeta}` splits exactly
                                                        into a positive real factor and that phase
      shellModulus, shellModulus_pos, shellLeadingDamped,
        shellLeadingDamped_eq, norm_shellLeadingDamped  the damped leading amplitude is a positive
                                                        real multiple of one `s`-independent phase

    RHTower/XiMassShellRelativeRadius.lean
      norm_xiMassShellDefect_le                         explicit window bound for the defect
      norm_csqrt_shellArgument_sub_rapidity_le          `‖z - q u‖ <= D_L` on every window,
                                                        uniformly in the height

    HTGeometry/PrincipalSquareRootDeriv.lean (continued)
      norm_csqrt, norm_mul_sub_one_le, norm_inv_sub_one_le
                                                        `‖csqrt w‖ = sqrt ‖w‖`; near-unit products
                                                        and inverses stay near-unit

    RHTower/XiMassShellAmplitudeRatio.lean
      shellRadiusBound, shellRadiusBound_nonneg
      norm_shellRadius_ratio_sub_one_le                 `‖z/(q u) - 1‖ <= D_L/(q u)`
      mul_csqrt_ofReal_mul                              positive real scalars factor out of the
                                                        `z sqrt z` amplitude

### Lean progress: the shell ratio (17.20)

    HTGeometry/PrincipalSquareRootDeriv.lean (continued)
      norm_mul3_sub_one_le                              a triple product of near-units

    RHTower/XiMassShellBesselRemainder.lean
      norm_besselLeadingFactor                          modulus of the Schlaefli leading factor
      norm_besselRemainder_le_relative                  **(17.9)** the remainder is smaller than
                                                        its own leading term by the factor
                                                        `2/(e a Re z) sqrt(2‖z‖/Re z)`

    RHTower/XiMassShellRatio.lean
      shellRoot, its real part and nonvanishing
      shellRatio, shellLeading_eq_model_mul_ratio       **exact** factorization of the shell
                                                        leading term as model times ratio
      norm_shellBoost_sub_one                           `‖tau/(iu) - 1‖ = sigma/u`
      norm_shellExpFactor_sub_one_le                    `‖e^{-a(z-zeta)} - 1‖ <= a D/(q u)`
      shellAmplitude_ratio_eq,
        norm_shellAmplitudeFactor_sub_one_le            `‖(qu)^{3/2}/(z sqrt z) - 1‖ <= 5 B/(q u)`
      exists_shellRatio_bound                           **(17.20)** `‖R - 1‖ <= C/u`, uniformly on
                                                        every window `0 <= s <= L`

    RHTower/XiMassShellAsymptotic.lean
      norm_shellArgument_le, norm_shellRoot_le          `‖z‖ <= sqrt(q^2+M) u` on every window
      shellRemainder_relative_le                        the Schlaefli remainder factor is `<= C/u`
      exists_shellProfile_relative_error                **(17.20)** the uniform shell asymptotic
                                                        `‖K_u(kappa u+s) - Lambda‖ <= (C/u)|Lambda|`

### Lean progress: (17.21) and the shifted exterior tail

    RHTower/XiMassShellPrimeMass.lean
      chebyshevTheta_eventually_relative                the plain relative PNT `|theta(x)-x|<=eps x`
                                                        from the corpus square-root-log error form
      chebyshevTheta_sub_eq_shellSum                    `theta(y)-theta(x)` is the shell prime sum
      exists_shell_theta_lower                          **(17.21)** `sum_{shell} log p >=
                                                        (1/2)(e^L-1) e^{kappa u}` for large `u`

    RHTower/XiMassShellExteriorTail.lean
      norm_xiMassCenteredPrimeAtom_exteriorSqrt_le,
        xiMassBesselExteriorSqrtTailConstant,
        sum_norm_xiMassCenteredPrimeAtom_exteriorSqrt_le
                                                        **(17.23)** the exterior tail past
                                                        `e^{kappa u + L}` with both the
                                                        stationary-phase factor `u^{-1/2}` and the
                                                        geometric gain `e^{-(a-1/2)L}`

### Lean progress: Theorem 17.5, its sharpness corollary, and §19.1--19.3

Newly formalized, axiom-clean (`[propext, Classical.choice, Quot.sound]`), wired, built:

    RHTower/XiMassSubthresholdDivergence.lean
      re_conj_phase_atom_ge                          the phase-projected atom is bounded below by
                                                     `(log p)(1-C/u)` times the shell modulus
      re_conj_phase_atom_window                      the same bound uniformly on a window
                                                     `κu < log p ≤ κu+t ≤ κu+L`
      sum_norm_exteriorBlock_le                      the exterior block of an annulus obeys the
                                                     shifted square-root tail
      exists_subthreshold_annulus_lower_bound        **(17.17)** Theorem 17.5: for `1 < κ < λ`
                                                     there are `c>0`, `u₀` with
                                                     `‖A_{κ,λ}(u)‖ ≥ c u^{-1/2} e^{-η_κ u}`

    RHTower/XiMassSubthresholdConeSharpness.lean
      xiMassBesselConeExponent_neg                   below the balance slope the cone exponent is
                                                     strictly negative
      tendsto_subthreshold_annulus_atTop             for `1 < κ < κ_B` the annulus diverges
      not_bounded_subthreshold_annulus               hence no uniform bound exists: the balance
                                                     slope of Theorem 17.3 is sharp

    RHTower/XiMassThetaLogDiscrepancy.lean
      xiMassThetaLogDiscrepancy,
        exists_norm_xiMassThetaLogDiscrepancy_le     **(19.1)** `|Θ(h) − e^h| ≤ C e^h e^{-c h^{1/10}}`
                                                     in logarithmic height, from the corpus
                                                     `MediumPNT`-based `θ` power-log theorem

    HTGeometry/BesselOrderDerivativeEnvelope.lean
      integral_exp_neg_mul_sq_shift, besselK1CDeriv,
        norm_besselK1CDeriv_integrand,
        cosh_sq_mul_exp_neg_mul_cosh_le_shift,
        norm_besselK1CDeriv_le                       `‖K₁'(z)‖ ≤ e^{-Re z} e^{2/Re z} √(2π/Re z)`:
                                                     the derivative has the same exterior envelope
                                                     with the same square-root gain

    RHTower/XiMassBesselHeightDerivative.lean
      xiMassBesselHeightSide, xiMassBesselHeightDeriv,
        hasDerivAt_xiMassBesselHeightSide            the closed height derivative
                                                     `2aτw(aK₁'(az)z − K₁(az))/z³`
      norm_besselHeightDerivCore_le                  its generic norm bound in terms of
                                                     `‖τ‖/‖z‖`, `|h|/‖z‖`, `1/Re z`

    RHTower/XiMassBesselDerivativeEnvelope.lean
      hasDerivAt_stripFourier_xiMass_bessel,
        xiMassFourierDerivative_eq_besselHeightDeriv the corpus Fourier derivative equals the
                                                     Bessel-side derivative outside the light cone
      norm_xiMassBesselHeightDeriv_le,
        norm_xiMassFourierDerivative_le,
        norm_xiMassCriticalOutgoingDerivative_le     **(19.2)** the differentiated exterior
                                                     envelope, with the same `u^{-1/2}` gain

    RHTower/XiMassPrimeWindowAbel.lean
      primeLogWindow, sum_primeLogWindow_indicator,
        intervalIntegrable_thetaWindowStep_mul
      sum_primeLogWindow_mul_eq                      finite-atom Abel summation against `Θ`
      integral_mul_exp_byParts                       the continuum pairing by parts
      primeLogWindow_quadrature_eq                   the window quadrature defect in discrepancy
                                                     form `E(T)G(T) − E(H)G(H) − ∫ E G'`

    RHTower/XiMassWindowDiscrepancyTail.lean
      xiMassExteriorAction_le                        `g_u` decreases with slope at least `a − 1/2`
      norm_xiMassCriticalDampedFourierProfile_exterior_le,
        norm_xiMassDampedProfileDeriv_exterior_le
      xiMassWindowDefectConstant
      norm_primeLogWindow_quadratureDefect_le        **(19.3)** the exterior discrepancy on a
                                                     window is at most
                                                     `(2+(T−H)) C_E C u^{-1/2} e^{g_u(H)-c H^{1/10}}`

Remaining in §19: the Taylor estimates (19.9)--(19.10) at the caustic and the resulting
penetration statement (19.6)--(19.7).

### Lean progress: §19.6, the caustic retreat law

Newly formalized, axiom-clean (`[propext, Classical.choice, Quot.sound]`), wired, built:

    RHTower/XiMassCausticPenetration.lean
      sharpSlope_pos, sharpSlope_mul_sqrt,
        sharpSlope_sq_sub_one,
        sharpSlope_eq_two_mul_sqrt              **(19.8)** the caustic ratio `κ_B = 2a√(κ_B²−1)`
      sharpAction_min                           the completed-square minimum principle
                                                `aH − ½√(H²−u²) ≥ u√(a²−¼)`, i.e. `g_u(κ_B u)=0`
                                                is the exact minimum of the action
      xiMassAction_le_slope                     the retreat cost `g_u(H) ≤ (κ_B u − H)·(−g_u'(H))`
      height_ratio_le, xiMassAction_penetration_le
                                                **(19.9)** `g_u(κ_B u − r) ≤ m_B r + 4a² r x`,
                                                `x = 2κ_B r/(u(κ_B²−1))`, `m_B = 2a²−1/2`
      rpow_sub_le                               **(19.10)** `A^p − A^{p−1}B ≤ (A−B)^p` for `p ≤ 1`

    RHTower/XiMassSubcausticVanishing.lean
      xiMassSubcausticHeight                    `H_*(u) = κ_B u − L u^{1/10}`
      tendsto_windowPrefactor_zero              `(2 + L u^{1/10})/√u → 0`
      exists_tendsto_subcausticWindowDefect_zero
                                                **(19.6)** there is a positive coefficient chamber
                                                bound `L_c` such that for every `0 < L ≤ L_c` the
                                                prime-discrepancy annulus between `H_*(u)` and the
                                                caustic tends to zero

The chamber bound produced by the Lean proof is exactly `L_c = c κ_B^{1/10}/m_B` of (19.4), for
the constant `c` supplied by the corpus power-log `θ` theorem.

Remaining in §19: the criterion transfer (19.7), which needs the edge corrections between the
raw heights `H_*(u)`, `κ_B u` and the integer cone edges `W_*(u)`, `W_B(u)`, plus a crude uniform
bound on a compact height range.

### Lean progress: §19.7, the subcaustic RH criterion — section 19 closed

Newly formalized, axiom-clean (`[propext, Classical.choice, Quot.sound]`), wired, built:

    RHTower/XiMassPrefixQuadratureDefect.lean
      xiMassVerticalBound, norm_stripFourier_le_verticalBound,
        norm_xiMassCenteredPrimeAtom_le_verticalBound,
        norm_xiMassCriticalGrowingFourierProfile_le_verticalBound,
        continuous_xiMassCriticalGrowingFourierProfile
      xiMassPrefixQuadratureDefect, xiMassPrefixDefectBound,
        xiMassPrefixDefectBound_nonneg, _mono,
        norm_xiMassPrefixQuadratureDefect_le    the defect at a fixed integer cutoff is bounded by
                                                a function of the cutoff alone, uniformly in the
                                                vertical time
      xiMassCriticalPrimeQuadratureDefect_eq_prefix
                                                the corpus cone defect is the prefix defect at
                                                `⌊e^{κu}⌋`
      xiMassPrefixQuadratureDefect_sub          two prefix defects differ by the prime annulus
                                                minus the continuum integral between the edges
      norm_integral_growing_edge_le             the integer edge correction is at most
                                                `√e·∫e^{-σ|x|}dx`: the continuum weight `e^{h/2}`
                                                grows half as fast as the edge gap `e^{-h}` shrinks

    RHTower/XiMassSubcausticCriterion.lean
      prefixDefect_sub_eq_window                the exact three-term decomposition
      exists_norm_prefixDefect_caustic_sub_le   the caustic and subcaustic defects differ by a
                                                globally bounded amount
      XiMassSubcausticQuadratureDefectLineBound,
        exists_riemannHypothesis_iff_xiMassSubcausticQuadratureDefectLineBound
                                                **(19.7)** RH is equivalent to uniform boundedness
                                                of the quadrature defect at the retreated cutoff
                                                `⌊e^{κ_B u − L u^{1/10}}⌋` for every `L` in the
                                                closed coefficient chamber

With this, sections 17 and 19 are fully formalized; §19.4 records the failure boundary and
asserts no new theorem.  Sections 20--24 remain.

### Lean progress: §20.4 — section 20 closed

    RHTower/XiMassGradedConeSharpness.lean
      xiMassBesselConeExponent_strictMono       `Γ_a(κ) = κ/2 − a√(κ²−1)` is strictly decreasing
      not_bigO_subgradedAnnulus                 **(20.4)** for `1 < κ < κ_{a,λ}` and every `μ > κ`
                                                the moving annulus is not `O(e^{λu})`

With (20.1)--(20.3) already formal in `RHTower/XiMassGradedBesselConePhase.lean`, the graded
cone/type phase diagram of section 20 is complete.

### Lean progress: §21 the logarithmic boundary layer (C42-P, positive half)

    RHTower/XiMassLogRetreatTail.lean
      xiMassBesselConeExponent_movingSlope      `η_{H/u}·u = a√(H²−u²) − H/2`
      xiMassBesselExteriorSqrtConstant_antitone,
        xiMassBesselExteriorSqrtTailConstant_antitone
                                                the exterior tail constant is antitone in the slope
      sum_norm_exteriorTail_movingSlope_le      hence the slope may move with the height:
                                                the tail past `e^H` is at most
                                                `C(κ₀) u^{-1/2} e^{g_u(H)}` whenever `H ≥ κ₀u`
      log_le_four_mul_rpow                      `log u ≤ 4 u^{1/4}`
      exists_norm_logRetreatTail_le             **(21.1)--(21.2)** the raw exterior tail past
                                                `κ_B u − q log u` is `O(u^{m_B q − 1/2})`
      exists_norm_logRetreatTail_bounded        **(21.3)** at `q_raw = 1/(2m_B)` the raw exterior
                                                tail is uniformly bounded

Remaining in §21: the matching lower bound (21.4) (a moving-slope version of Theorem 17.5),
and the sharper criterion (21.10) of C42-Q, which needs the §19 vanishing argument re-run with the
extra `q log u` retreat.

### Lean progress: §21.10 — the logarithmically corrected RH criterion (C42-Q)

The window estimate (19.3) was first sharpened: the exterior action decays with slope at least
`a − 1/2`, so the window bound no longer carries the window width and reads

`‖∫_{(H,T]} G dE‖ ≤ (2 + 1/(a−1/2))·C_E·C·u^{-1/2}·e^{g_u(H) − c H^{1/10}}`.

Newly formalized, axiom-clean, wired, built:

    RHTower/XiMassLogSubcausticWindow.lean
      xiMassLogSubcausticHeight,
        xiMassLogSubcausticHeight_le             `H(u) = κ_B u − L u^{1/10} − q log(max u 1)`,
                                                 the harmless initial-interval normalization
      exists_eventually_norm_logSubcausticWindowDefect_le
                                                 **(21.7)--(21.8)** for every `L` in the closed
                                                 chamber and every `q` with `m_B q ≤ 1/2`, the
                                                 annulus between `H(u)` and the caustic stays
                                                 uniformly bounded

    RHTower/XiMassMovingQuadratureCriterion.lean
      XiMassMovingQuadratureDefectLineBound
      exists_norm_prefixDefect_moving_sub_le      any moving height below the caustic with an
                                                 eventually bounded annulus has a globally
                                                 bounded defect difference
      riemannHypothesis_iff_movingQuadratureDefectLineBound
                                                 the general moving RH criterion
      exists_riemannHypothesis_iff_logSubcausticQuadratureDefectLineBound
                                                 **(21.10)** RH is equivalent to uniform
                                                 boundedness of the quadrature defect at
                                                 `⌊e^{κ_B u − L u^{1/10} − q log u}⌋`

Remaining in §21: the raw lower bound (21.4) (a moving-slope form of Theorem 17.5).  §21.1 and
§21.2 are the universal-principle statement and the hostile audit; §21.3 is the graded refinement.

### Lean progress: §21.3 — the logarithmic layer of every grade

    RHTower/XiMassCausticPenetration.lean  (addition)
      xiMassAction_le_slope_general            two-point convexity of the exterior action:
                                               `g_u(H) ≤ g_u(K) + (K−H)(−g_u'(H))`, which reduces
                                               to `Q_H Q_K ≤ KH − u²`, i.e. `0 ≤ u²(H−K)²`

    RHTower/XiMassGradedLogRetreat.lean
      xiMassGradedPenetrationRate,
        xiMassGradedPenetrationRate_pos        **(21.15)** `m_{a,λ} = aκ/√(κ²−1) − 1/2 > 0`
      xiMassAction_penetration_general_le      **(21.11)** the quantitative retreat cost at any
                                               slope: `g_u(κu − r) ≤ g_u(κu) + m r + 2a(κ/q) r x`
      exists_norm_gradedLogRetreatTail_le      **(21.16)--(21.17)** for every grade `0 ≤ λ < 1/2`
                                               and every `q` with `m_{a,λ} q ≤ 1/2`, the exterior
                                               true-prime tail past `κ_{a,λ}u − q log u` is
                                               `O(e^{λu})`: the coefficient-sharp logarithmic
                                               refinement of the whole cone/type duality, with
                                               (21.3) as its `λ = 0` member

### Lean progress: §23 — type-zero collapse of every sublinear caustic layer (C42-V)

Newly formalized, axiom-clean, wired, built:

    RHTower/XiMassPrefixQuadratureDefect.lean  (additions)
      norm_conePrimeIndexSum_le,
        conePrimeIndexSumBound_mono              the prime part of a cutoff cone is bounded by a
                                                 function of the cutoff alone, uniformly in `u`
      le_log_floor_exp_add_one,
        log_floor_exp_add_one_le                 `H ≤ log(⌊e^H⌋+1) ≤ H+1`

    RHTower/XiMassTypeZeroCore.lean
      XiMassTypeZero, XiMassTypeZero.add/.sub/.congr
                                                 **(23.1)** vertical type zero and its stability
      xiMassMovingPrimeCone,
        xiMassCriticalTruePrimeCone_eq_movingCone
      sum_norm_exteriorBlock_height_le,
        norm_conePrimeIndexSum_sub_le            two cutoff cones above a common exterior height
                                                 differ by at most the exterior tail
      xiMassAction_at_slope                      `g_u(κu) = −η_κ u`
      xiMassCriticalBesselConeLineGrowth_of_eventually
                                                 line growth is an eventual condition
      continuous_xiMassBesselConeExponent,
        xiMassBesselConeExponent_sharpSlope_eq_zero,
        xiMassGradedConeSlope_lt_sharpSlope
      riemannHypothesis_iff_typeZero_movingPrimeCone
                                                 **(23.5)** RH ⟺ the true-prime cone truncated at
                                                 any moving height with `H(u)/u → κ_B` has type
                                                 zero

    RHTower/XiMassTypeZeroDefect.lean
      xiMassBesselExteriorConstant_antitone,
        xiMassBesselContinuumTailConstant_antitone,
        norm_integral_growingFourierProfile_movingSlope_le
                                                 the continuum tail at a moving slope
      tendsto_coneEdge_ratio                     the integer cone edge has the same slope limit
      xiMassTypeZero_continuumPrefix             the continuum prefix has type zero
      riemannHypothesis_iff_typeZero_movingQuadratureDefect
                                                 **(23.6)** RH ⟺ the moving quadrature defect has
                                                 type zero
      xiMassAggressiveHeight,
        tendsto_xiMassAggressiveHeight_ratio,
        riemannHypothesis_iff_typeZero_aggressiveQuadratureDefect
                                                 **(23.9)--(23.10)** the revised exact open core at
                                                 the retreat `κ_B u − u/log(u+e)`

C42-W asserts no new theorem beyond (23.5)--(23.6): it observes that the bounded-quotient
optimizations of §§21--22 are unnecessary for the type quotient, which is exactly the content of
the two criteria above.

### Lean progress: §18 and §22 (C42-S positive survivor, C42-U identity wall)

§18 asserts no theorem beyond Corollary 17.4 at the balance slope: (18.1) is exactly
`riemannHypothesis_iff_xiMassCriticalBesselQuadratureDefectLineBound` with `κ = κ_B`, already
formal in `RHTower/XiMassBesselConeQuadratureDefect.lean`.

Newly formalized, axiom-clean, wired, built:

    RHTower/XiMassTimelikeIdentityWall.lean
      xiMassTimelikeSaddleDispersion,
        xiMassTimelikeSaddleDispersion_gt,
        xiMassTimelikeSaddleDispersion_surjOn    **(22.12)** as the ray parameter sweeps `(0,1)`
                                                 the timelike saddle dispersion sweeps `(a,∞)`
      eq_zero_of_vanishes_on_timelikeSaddles     **(C42-U) the timelike identity wall**: a fixed
                                                 entire multiplier annihilating the leading saddle
                                                 on every timelike ray vanishes identically, hence
                                                 also annihilates the spectral receiver
      xiMassSpacelikeSaddleDispersion,
        xiMassSpacelikeSaddleDispersion_pos,
        xiMassSpacelikeSaddleDispersion_sharpSlope
                                                 **(22.1)** the caustic saddle dispersion is the
                                                 finite nonzero number `2a²/κ_B` — the exact reason
                                                 (C42-S) inverse-dispersion damping cannot improve
                                                 the transport power

Remaining in §22: C42-T, the caustic-null jet hierarchy (22.7)--(22.11), which needs a uniform
stationary-phase expansion of the Schläfli carrier to arbitrary order.

### Lean progress: §24 — the harmonic floor transform and its critically stable inverse (C43-B)

Newly formalized, axiom-clean, wired, built:

    RHTower/FloorTransformHarmonicInverse.lean
      floorTransform, dirichletConv
      floorTransform_comp                        **(24.10)** floor associativity and hyperbola
                                                 regrouping give `T_a T_b = T_{a*b}`
      sum_divisors_moebius                       `∑_{d ∣ n} μ(d) = [n = 1]`
      harmonicWeight, moebiusHarmonicWeight, unitWeight,
        dirichletConv_harmonic_moebius           **(24.11)** `(1/d) * (μ(d)/d) = 1_{n=1}`
      floorTransform_unitWeight,
        floorTransform_moebiusHarmonic_harmonic  **(24.12)--(24.13)** the harmonic floor average
                                                 `Q(N)=∑_{d≤N}R(⌊N/d⌋)/d` has the exact inverse
                                                 `R(N)=∑_{d≤N}μ(d)Q(⌊N/d⌋)/d`
      abs_harmonicWeight_le, abs_moebiusHarmonicWeight_le,
        abs_floorTransform_le_of_weight,
        summable_criticalMajorant,
        abs_floorTransform_le_tsum_majorant,
        abs_floorTransform_harmonic_le,
        abs_floorTransform_moebiusHarmonic_le    **(24.14)** both directions of the inversion carry
                                                 the same square-root exponent, with the
                                                 absolutely convergent majorant `∑ d^{-3/2-ε}`

The remaining C43-B content — the Jordan symbol law (24.5) and the source theorem (24.6) — is a
statement about Mellin transforms of floor transforms, not about the mass receiver, and (24.6) is
explicitly not available in the corpus.

### Lean progress: §24 C43-F — the harmonic triangular projection

    RHTower/HarmonicTriangularProjection.lean
      harmonicSum, harmonicGap, harmonicGap_mul, harmonicGap_sq_mul, harmonicGap_nonneg
      sum_harmonicGap, sum_mul_harmonicGap, sum_sq_mul_harmonicGap
                                              the three telescoping moments of the increment weight
      sum_ramp_harmonicGap                    **(24.38)** `∑_{D<q}(q−D)w_D = q − H_q`
      sum_biramp_harmonicGap                  **(24.42)** `∑_{D<ℓ}(ℓ−D)(v−D)w_D
                                              = ℓv + 2ℓ − (ℓ+v+1)H_ℓ`
      hyperbolaSwap, shiftedSwap, shiftedSwap₂, tailSwap
                                              the four hyperbola regroupings used below
      sourcePartialSum, floorMoment, triangularTransport
      tail_sourcePartialSum_eq_triangularTransport
                                              **(24.32)** the transport is exactly the tail
                                              `∑_{d>D} R(⌊N/d⌋)`
      sum_harmonicSum_floor_eq                **(24.39)** `∑_{m≤N} a_m H_{⌊N/m⌋}
                                              = (T_{1/n} R)(N)`, the harmonic floor transform of
                                              the partial sums
      harmonic_projection_triangularTransport **(24.41)** `∑_{D<N} w_D T_N(D)
                                              = ∑_{m≤N} a_m⌊N/m⌋ − (T_{1/n}R)(N)`: the signed
                                              harmonic projection is a change of coordinates
      pathKernel, pathKernel_eq,
        harmonic_pathEnergy_triangularTransport,
        harmonic_pathEnergy_nonneg            **(24.42)--(24.43)** the exact quadratic path energy
                                              and the positive semidefiniteness of its kernel

All statements are for an arbitrary real source `a`, so they apply verbatim to `a_m = Λ(m) − 1`
and to the centered source `c` of `(24.43)`.

### Lean progress: §24 C43-D — the weighted-floor family and its critical threshold

    RHTower/FloorTransformPowerThreshold.lean
      powerWeight, moebiusPowerWeight
      dirichletConv_moebiusPower_power         **(24.25)** `d^{-θ}` and `μ(d)d^{-θ}` are Dirichlet
                                               inverse for every exponent
      floorTransform_moebiusPower_power        **(24.25)** hence `T_{n^{-θ}}` is exactly invertible
                                               for every `θ`
      abs_powerWeight_le, abs_moebiusPowerWeight_le,
        abs_floorTransform_le_of_powerBound,
        summable_powerMajorant,
        abs_floorTransform_le_tsum_powerMajorant,
        abs_floorTransform_power_le,
        abs_floorTransform_moebiusPower_le     **(24.26)--(24.27)** above the threshold both
                                               directions carry the square-root exponent, with the
                                               convergent majorant `∑ d^{-θ-1/2-ε}`
      sqrtProfile, model_lower_eq,
        model_lower_le_floorTransform_sqrtProfile,
        not_bounded_normalized_floorTransform_sqrtProfile
                                               **(24.28)** below the threshold the model profile
                                               `√N` is already unbounded after critical
                                               normalization: `T_{n^{-θ}}√ ≥ (√N/√2)(N/2)^{1/2-θ}`
      floorTransform_sqrtProfile_le,
        sqrt_le_floorTransform_sqrtProfile     **(24.28)** above the threshold the same profile is
                                               pinned between `√N` and a constant times `√N`

So `θ = 1/2` is exactly the invertibility threshold: every `θ > 1/2` is a stable coordinate at
critical type and therefore cannot by itself lower the RH proof burden, and every `θ < 1/2`
already fails on the model profile.

### Lean progress: §24 C43-K and C43-L — the primitive ladder and the exact resolvent

    RHTower/HarmonicPrimitiveLadder.lean
      abelPairing, discreteDeriv, sum_telescope_abel
      abelPairing_recursion                    **(24.69)** the exact Abel recursion, stated against
                                               an arbitrary primitive of `w f`, so no tail
                                               convergence hypothesis is needed
      abelPairing_ladder                       **(24.70)** the exact ladder identity: after `k`
                                               steps the pairing is `k` endpoint terms plus the
                                               pairing of the `k`-th primitive against the `k`-th
                                               difference quotient

    RHTower/HarmonicTailResolvent.lean
      harmonicTailKernel, harmonicTail,
        integrableOn_harmonicTailIntegrand,
        harmonicTailKernel_eq_sub,
        hasDerivAt_harmonicTailKernel
      hasDerivAt_harmonicTail,
        harmonicTail_resolvent                 **(24.76)** `(1/2 − ∂_h) 𝒯 = −I` for every bounded
                                               continuous critical remainder
      outgoingSymbol_ne_zero,
        harmonicTailSymbol_mul_outgoingSymbol  **(24.78)** the harmonic-tail symbol
                                               `−(1/2 − iξ)^{-1}` and the outgoing symbol
                                               `1/2 − iξ` multiply to `−1` at every frequency

The ladder identity is unconditional sequence algebra and the resolvent identity holds at every
frequency, so together they show that no finite number of Abel integrations and no scalar
translation-invariant transform with stable inverse can change the critical exponent — only a
genuinely noncommuting, prime-adaptive or mass-phase-adapted primitive could.

### Lean progress: §24 C43-P — the square-root mass information horizon

    RHTower/MassInformationHorizon.lean
      massOrbit_bounds                         **(24.93)** from `β² = α² + a²` alone: `|K| M = R|J|`
                                               and `a ≤ M ≤ a + R`, by the exact quartic relation
                                               `M²(M² − R² + J² − a²) = R²J²`
      massOrbitExponent,
        massOrbitExponent_le, le_massOrbitExponent
                                               **(24.94)--(24.97)** the exponent is sandwiched
                                               between the `a`- and `(a+R)`-profiles
      massOrbitExponent_neg                    **(24.99)** `σ a² > u R|J|` extinguishes the orbit
      massOrbitExponent_pos                    **(24.99)** `u R|J| > σ (a+R)²` keeps it visible
      massOrbit_transition                     **(24.98)** the leading coefficient vanishes exactly
                                               at `σ c² = R|J|`
      abs_norm_add_div_sub_one_le,
        norm_massConjugate_exp,
        norm_massConjugate_exp_reverse         **(24.95)** the dominant member has logarithmic
                                               magnitude `u|K| − σM`, the reverse member exactly
                                               `e^{-2u|K|}` smaller, so the pair cannot cancel

The two sign criteria are the whole phase diagram in unconditional form: no limit hypothesis is
used, only the explicit comparison of `σ a²` with `u R|J|`.
