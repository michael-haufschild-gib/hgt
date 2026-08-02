# Deninger--Meyer half-density L1 completion

## Status

Source seminorm, quotient seminorm, Banach completion, completed centered-flow isometry, and exact
Xi continuity spectrum are formalized unconditionally. Route remains open on faithfulness and
arithmetic admission. No RH claim is made here.

## Route

Route L (Deninger/Meyer arithmetic cohomology).

## Problem isolated

Let

\[
  H_M=\mathcal S_M/\mathcal B_P
\]

be the literal strong-log Meyer quotient already constructed in Lean, and let

\[
  (V_cg)(t)=e^{-c/2}g(t-c)
\]

be the centered logarithmic dilation flow. Existing work gives, for every actual Xi divisor point
\(\rho\), a nonzero algebraic functional on \(H_M\) with centered eigencharacter
\(e^{c(\rho-1/2)}\). What is absent is a source-defined Hausdorff completion on which the centered
flow is isometric and the actual Xi functionals survive continuously.

## Canonical candidate `[NEW CONJECTURE/CANDIDATE]`

Define on the literal strong-log source

\[
  p_{1/2}(g)=\int_{\mathbb R}e^{t/2}\lVert g(t)\rVert\,dt
\]

and on \(H_M\) take the quotient seminorm

\[
  \bar p_{1/2}([g])=\inf_{b\in\mathcal B_P}p_{1/2}(g+b).
\]

This is not a divisor-indexed Hilbert model, local Calderon regulator, Hellinger--Gamma coface,
incidence completion, or abstract postulated norm. It is defined directly on the source object and
then descended through the actual Meyer boundary.

## Forced-weight theorem `[PAPER PROOF]`

For a positive measurable weighted L1 functional

\[
  p_w(g)=\int w(t)\lVert g(t)\rVert\,dt,
\]

exact invariance under every centered flow forces

\[
  w(t+c)=e^{c/2}w(t)
\]

almost everywhere, hence \(w(t)=C e^{t/2}\) almost everywhere. Conversely \(e^{t/2}\) gives
exact invariance:

\[
\begin{aligned}
 p_{1/2}(V_cg)
 &=\int e^{t/2}e^{-c/2}\lVert g(t-c)\rVert\,dt\\
 &=\int e^{(u+c)/2}e^{-c/2}\lVert g(u)\rVert\,du\\
 &=p_{1/2}(g).
\end{aligned}
\]

The converse uses compactly supported continuous probes concentrated in arbitrary measurable
regions. That density argument is a later Lean target; no converse is needed to construct the
seminorm or prove its invariance.

## Exact Mellin continuity selector `[PAPER PROOF]`

For \(s=1/2+i\tau\),

\[
  |M_g(s)|
  \leq \int |e^{st}g(t)|\,dt
  =\int e^{t/2}|g(t)|\,dt
  =p_{1/2}(g).
\]

If \(\rho\) is an actual Xi zero, the existing Poisson/Meyer descent theorem says
\(M_b(\rho)=0\) for \(b\in\mathcal B_P\), so every critical-line Xi evaluation descends and is
bounded by \(\bar p_{1/2}\).

Conversely, suppose the nonzero descended Xi evaluation at \(\rho\) is bounded by
\(\bar p_{1/2}\). Quotient-flow isometry and the existing eigencharacter law give, for every real
\(c\),

\[
  e^{c(\Re\rho-1/2)}|E_\rho(u)|
  =|E_\rho(V_cu)|
  \le C\bar p_{1/2}(V_cu)
  =C\bar p_{1/2}(u).
\]

Using both signs of \(c\) forces \(\Re\rho=1/2\). Therefore

\[
  E_\rho\text{ is }\bar p_{1/2}\text{-bounded}
  \quad\Longleftrightarrow\quad
  \Re\rho=1/2.
\]

This theorem is unconditional; it characterizes the completion spectrum and does not assert that
all Xi evaluations are bounded.

## Exact remaining scientific frontier

Two source questions remain, and neither can be replaced by an abstract completion axiom.

1. **Hausdorff faithfulness:** prove that the Poisson boundary range \(\mathcal B_P\) is closed for
   \(p_{1/2}\), equivalently that \(\bar p_{1/2}([g])=0\) implies \([g]=0\) in literal Meyer
   cohomology.
2. **Arithmetic admission:** prove from the Gamma/co-Poisson source construction that every actual
   Xi zero evaluation is continuous for the faithful completed source geometry.

By the exact selector, item 2 is RH-strength and cannot be obtained from generic functional
analysis. The useful Deninger research target is therefore a source identity forcing admission
(or an equivalent positive middle Hodge polarization), while item 1 prevents a fake non-Hausdorff
completion from satisfying the claim.

## Non-overlap audit

Repository search found no existing seminorm on the literal strong-log Meyer target defined by
\(\int e^{t/2}\lVert g(t)\rVert\), no quotient-flow isometry for such a seminorm, and no theorem
identifying its continuous Xi spectrum. Existing half-density files concern prime/Theta carriers,
divisor Hilbert spaces, polarized transfer, or downstream boundary objects. Existing
`DeningerMeyerPositiveAdmissibleCompletionFrontier.lean` proves only the conditional implication
from a postulated norm-conservative completed dual action to RH; it does not construct this source
topology.

## Lean targets

- [x] raw half-density L1 seminorm on `DeningerMeyerStrongLogTarget`;
- [x] exact centered-flow invariance;
- [x] quotient seminorm on `DeningerMeyerStrongLogCohomology`;
- [x] exact quotient-flow isometry;
- [x] critical Mellin bound;
- [x] bounded descended Xi evaluation iff critical-line real part;
- [x] quotient-by-kernel Banach completion;
- [x] completed centered flow is a surjective linear isometry;
- [x] critical Xi evaluations extend continuously and remain nonzero;
- [ ] Poisson-boundary closedness / faithful embedding (open core);
- [ ] source arithmetic admission for every Xi divisor point (RH-bearing open core).

Formal module:
`formal/GaloisForLFunctions/RHTower/DeningerMeyerHalfDensityL1Completion.lean`.

Verification: direct `lake env lean`, targeted module build, global formal lint, and axiom audit all
pass. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
