# No finite completed-flux jet selects the symmetry axis

- **ID:** finite-jet-graded-reality-nonselection
- **Stage:** 2-fully-proven / needs independent audit
- **Type:** THEOREM (paper) / finite-passport no-go
- **Date:** 2026-07-10
- **Scientific status:** `[NOVELTY UNVERIFIED]` — the explicit construction appears absent from the
  local corpus and survived the parent-theory attack below.  Its proof is elementary entire-function
  theory, so scientific novelty is not claimed without a broader literature audit and independent
  expert review.
- **Statement:** For every finite jet depth `N` and every `0<b<1/2`, there is a real even entire
  function of exact order one, with no nonzero period and with zeros at `±ib`, whose residue-filled
  negative logarithmic derivative germs at the two partner zeros have identical Taylor coefficients
  through order `N` but are not equal as germs.  After functional-equation normalization, the two
  zeros lie at `1/2±b`, strictly inside the critical strip and off the critical axis.  Consequently
  FE symmetry, Schwarz reality, critical-strip location, order-one growth, and aperiodicity cannot
  turn any fixed finite completed-flux jet into a critical-axis selector.

## Why this is the correct attack

`CompletedFluxGradedReality.lean` proves that the complete coefficient sequence detects the critical
line.  That alone leaves open a dangerous simplification: perhaps a universal finite depth already
suffices once functional symmetry, Schwarz reality, order-one growth, and aperiodicity are imposed.
The theorem below rules this out constructively.  The obstruction is not merely that the required
depth is unknown; it is unbounded in the strongest natural symmetry envelope short of the Euler
source itself.

## Construction

Fix `N` and `0<b<1/2`.  Choose an odd integer `M>N`, put

\[
\lambda=\frac{\pi}{2b},\qquad \alpha=ib,\qquad
P_M(z)=1+(z^2+b^2)^M,\qquad
F_M(z)=\cosh(\lambda z)\,P_M(z).
\]

Then `F_M` is even and real entire:

\[
F_M(-z)=F_M(z),\qquad
F_M(\bar z)=\overline{F_M(z)}.
\]

Since `λα=iπ/2` and `P_M(±ib)=1`, the two points `±α` are simple nonreal zeros
of `F_M`.

For a simple zero `a`, define the residue-filled negative-logarithmic-derivative germ

\[
G_a(x)=
\begin{cases}
-1,&x=0,\\[2mm]
-x\dfrac{F_M'(a+x)}{F_M(a+x)},&x\ne0.
\end{cases}
\]

The singularity at `x=0` is removable.  Evenness of `F_M` gives the exact identity

\[
G_{-\alpha}(x)=G_\alpha(-x).                                      \tag{1}
\]

Thus equality of the two partner jets through a given order is equivalent to vanishing of the odd
Taylor coefficients of `G_α` through that order.

## Exact jet calculation

Split the germ into its `cosh` and polynomial parts:

\[
G_\alpha(x)
=-\lambda x\coth(\lambda x)
-x\frac{P_M'(\alpha+x)}{P_M(\alpha+x)}.                         \tag{2}
\]

The first term is even.  For the second term, write

\[
u(x)=(\alpha+x)^2+b^2=x(2\alpha+x).
\]

Then

\[
-x\frac{P_M'(\alpha+x)}{P_M(\alpha+x)}
=-\frac{2M\,x(\alpha+x)u(x)^{M-1}}{1+u(x)^M}.                  \tag{3}
\]

Because `u(x)=2αx+O(x^2)`, expression (3) has a zero of exact order `M`, with leading
coefficient

\[
-2M\alpha(2\alpha)^{M-1}=-M(2\alpha)^M\ne0.                   \tag{4}
\]

There are therefore no polynomial-factor contributions below order `M`.  At order `M` the
coefficient is nonzero; since `M` is odd, it is an odd Taylor coefficient.  Combining (1)--(4):

\[
[x^n]G_{-\alpha}=[x^n]G_\alpha\quad(0\le n<M),
\qquad
[x^M]G_{-\alpha}\ne[x^M]G_\alpha.                             \tag{5}
\]

As `M>N`, the partner germs agree through the prescribed depth `N` and disagree later.

## Functional-equation normalization

Put

\[
X_M(s)=F_M\!\left(-i\left(s-\tfrac12\right)\right).
\]

The even and real symmetries of `F_M` become

\[
X_M(1-s)=X_M(s),\qquad X_M(\bar s)=\overline{X_M(s)}.
\]

The zeros `±α` become

\[
\rho_- =\tfrac12-b,
\qquad
\rho_+ =\tfrac12+b=1-\rho_-.
\]

They are real, so Schwarz fixes each, while the functional equation exchanges them.  Because
`0<b<1/2`, both lie strictly inside `0<Re s<1`, and neither lies on `Re s=1/2`.  The affine coordinate
change sends a Taylor coefficient of order `n` to a nonzero scalar multiple of the corresponding
coefficient in (5); hence equality through `N` and failure at `M` are preserved.  Equivalently, the
one-base graded-reality equations hold through order `N` at `ρ_-` and fail at the odd order `M`.

## Exact order and aperiodicity

The polynomial factor does not change the order of `cosh(λz)`, so `F_M` and `X_M` have exact
entire order one.

To prove aperiodicity, suppose `F_M(z+h)=F_M(z)` for every `z`.  Along positive real `x`,

\[
\frac{\cosh(\lambda(x+h))}{\cosh(\lambda x)}\longrightarrow e^{\lambda h},
\qquad
\frac{P_M(x+h)}{P_M(x)}\longrightarrow1.
\]

Periodicity therefore gives `e^(λh)=1`, so `h=2πik/λ` for some integer `k`.  Such an `h` is a
period of `cosh(λz)`; cancelling this factor away from its discrete zero set and using the identity
theorem gives `P_M(z+h)=P_M(z)`.  A nonconstant polynomial has no nonzero period: the leading term of
`P_M(z+h)-P_M(z)` below its cancelled top degree is `deg(P_M)·lc(P_M)·h·z^{deg(P_M)-1}`.
Thus `h=0`.  The affine change of variables preserves aperiodicity, so `X_M` also has no nonzero
period.

## Consequence

There is no universal `N` for which the first `N` completed-flux coefficients select the critical
line in the class of aperiodic, order-one, FE-even, Schwarz-real entire functions even when the
tested zero is required to lie strictly inside the critical strip.  Any successful finite-depth
theorem for `xi` must therefore consume genuinely arithmetic Euler-source structure not present in
this envelope.  A source theorem using only FE, Schwarz, strip location, growth, and aperiodicity is
provably insufficient.

This does not rule out a finite theorem that uses a global Euler invariant.  It rules out a finite
local passport whose only global guards are the five conditions above.

## Parent-theory and literature attack

- The mechanism is high-order Hermite interpolation by multiplication with an even polynomial
  flat at the selected zero pair.  That mechanism is classical in spirit and prevents a confident
  novelty claim based only on the explicit formula.
- Classical Laguerre--Pólya theory already requires an infinite hierarchy of conditions in general,
  and finite initial inequalities are not known to characterize real-rootedness without additional
  restrictive hypotheses.
- Initial exact-phrase and mechanism searches across AMS, Project Euclid, and arXiv results located
  classical Laguerre inequalities and specialized coefficient criteria, but not this simultaneous
  FE/Schwarz/order-one/aperiodic finite-jet nonselection theorem.  That negative search is not a
  completed literature gate.

## Lean formalization status

`RHTower/FiniteJetGradedRealityNoGo.lean` formalizes the load-bearing local analytic core.  It
constructs the shifted even multiplier `1+(z^2-α^2)^(2N+1)`, proves the exact logarithmic-flux
correction identity, proves that the correction has analytic order exactly `2N+1`, realizes it as
the residue-filled negative logarithmic derivative of an explicit simple-zero factor, and proves
that the germ and its reflection have identical iterated derivatives through order `N` but differ
at order `2N+1`.

The exact module and exact Lake target build pass.  The load-bearing declarations use only
`propext`, `Classical.choice`, and `Quot.sound`.  The global scaled-`cosh` realization, its exact
entire order, critical-strip coordinate conversion, and aperiodicity argument remain paper-only;
therefore the card correctly remains at stage 2 rather than being promoted to stage 3.

## Gates

- [x] 0 → 1: the finite-passport claim was stated and attacked by an explicit family
- [x] 1 → 2: symmetry, zeros, exact jet contact, later failure, order, and aperiodicity were proved
- [ ] independent mathematical audit of the scaled coordinate conversion and aperiodicity argument
- [x] formalize the polynomial-flatness and completed-germ coefficient theorem in Lean
- [ ] 2 → 3: formalize the global scaled-`cosh` realization, exact order, strip location, and
  aperiodicity theorem
- [ ] literature and parent-theory audit sufficient for any scientific-novelty promotion
