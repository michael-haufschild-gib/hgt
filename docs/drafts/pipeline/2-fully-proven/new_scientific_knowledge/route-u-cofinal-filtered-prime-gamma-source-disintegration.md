# Route U: cofinal filtered prime--Gamma source disintegration

- **ID:** `route-u-cofinal-filtered-prime-gamma-source-disintegration`
- **Stage:** 2-fully-proven
- **Route:** U, fixed-carrier cofinal hard-edge packets
- **Type:** SOURCE BRIDGE / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [BRIDGE] [NOVELTY UNVERIFIED] [LEAN PENDING]`
- **Date:** 2026-08-14

## Exact frontier

`[CORPUS]` `XiShiftedFilteredGammaTransmutation.lean` proves that every shifted reciprocal
Hankel quadratic is a positive factorial normalization of a polynomial-filtered Xi heat integral.
`XiPolynomialGaussianExplicitFormula.lean` gives the literal Gamma, polar, and von-Mangoldt
formula for every polynomial-square heat trace.  `XiShiftedHardEdgeCofinalLinearFiniteHankelDimension.lean`
proves that false RH is equivalent to one fixed polynomial--Gaussian carrier producing negative
finite Hankel packets at every sufficiently large integral hard-edge mass.  These results are not
yet composed before divisor aggregation.

`[LOCAL-RESEARCH]` The paper-only hard-edge boundary state uses the finite density

\[
 g_{a,B}(x)^2={a^2\over a^2+x^2}
 B\!\left({a^2-x^2\over a^2+x^2}\right)^2,                 \tag{SD.1}
\]

whose limit is `HHWB.2`; no Lean theorem presently derives `(SD.1)` from the filtered literal
prime--Gamma source.

`[LITERATURE]` Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the
truncated Weil quadratic form*, arXiv:2607.02828v2, constructs a different finite Galerkin
coefficient-to-test-function dictionary, an exact finite source quotient, and a positive
Cauchy--Stieltjes archimedean tail.  Suzuki, arXiv:2606.09096, gives a localized Weil operator and
leaves arithmetic prime control open.  Neither source states the Laplace--reciprocal cancellation
below or the cofinal fixed-carrier source-inversion phase.

## Conjecture loop

### C1 -- universal pointwise completed-balance positivity

Conjecture that every shifted-reversal polynomial has nonnegative literal completed balance at
every positive heat time.

**Verdict:** `[CIRCULAR]`.  Shifted reversals range over arbitrary finite real polynomials (already
at shift zero by coefficient reversal).  The polynomial-Gaussian criterion says nonnegativity for
all such polynomials and all positive times is equivalent to RH.  Repackaging this statement as a
source balance supplies no producer.

### C2 -- one negative filtered integral is impossible for a fixed carrier

Conjecture that fixed-carrier origin alone forbids a negative filtered integral.

**Verdict:** `[FALSIFIED AS AN INFERENCE]`.  Existing cofinal compactification proves exactly that
false RH would give one fixed carrier with negative filtered packets.  Fixedness becomes useful
only after retaining the literal source and its hard-edge cancellation; it is not itself a sign.

### C3 -- positive source disintegration with degree cancellation

`[CONJECTURE]` The filtered Hankel scalar is the integral of the literal completed prime--Gamma
balance against a positive Laplace weight.  For a hard-edge lift, reciprocal reversal cancels the
entire degree-dependent density.  Consequently every negative packet contains an actual
prime--Gamma source inversion, necessarily beyond the completed aperture.  False RH is equivalent
to a cofinal family of these source inversions from one fixed carrier.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK`.  It is not a sign theorem and does not
claim RH.  It changes the remaining object from a divisor-side negative quadratic to a literal
source-side inversion at a certified super-aperture time.  Scalar-budget countermodels do not kill
it because the complete Gamma, polar, and von-Mangoldt incidence is retained pointwise before the
positive Laplace average.

## Exact statement

For `y in R`, `d in N`, `c : Fin(d+1) -> R`, put

\[
 Q_{y,d,c}(W)=\sum_{i=0}^d c_i(W+y)^{d-i}.
\]

For `s>0`, define the literal completed balance

\[
\begin{aligned}
 \mathcal B_{y,d,c}(s)
 := {}&\int_{\mathbb R}|Q_{y,d,c}(x^2)|^2e^{-sx^2}
       \vartheta_\infty(x)\,dx\\
 &+2\pi Q_{y,d,c}(-1/4)^2e^{s/4}
 -\Re\sum_{m\ge1}{\Lambda(m)\over\sqrt m}
   \widehat{\bigl(Q_{y,d,c}(x^2)^2e^{-sx^2}\bigr)}(\log m).
                                                               \tag{SD.2}
\end{aligned}
\]

Let

\[
 \mathcal K_{y,d,c}(s)
 =\mathbf 1_{s>0}s^{2d}e^{-ys}\mathcal B_{y,d,c}(s),\qquad
 \mathcal C_{y,d,c}=\int_0^\infty\mathcal K_{y,d,c}(s)\,ds.    \tag{SD.3}
\]

Then, for `y>0`,

\[
 \boxed{\quad
 \mathcal C_{y,d,c}
 =\pi(2d)!\,\mathcal H_{y,d}(c).
 \quad}                                                       \tag{SD.4}
\]

Moreover, take `a>0`, `B in R[X]`,

\[
 R(Z)=B(2a^2Z-1),\quad d=\deg R,\quad c_i=[Z^i]R,
 \quad Q=Q_{a^2,d,c}.
\]

For every real `x`, reciprocal reversal gives the exact degree cancellation

\[
 \boxed{\quad
 {a^2Q(x^2)^2\over(a^2+x^2)^{2d+1}}
 ={a^2\over a^2+x^2}
 B\!\left({a^2-x^2\over a^2+x^2}\right)^2.
 \quad}                                                       \tag{SD.5}
\]

If `\mathcal C_{y,d,c}<0`, then there exists `s>0` with

\[
 \mathcal B_{y,d,c}(s)<0,                                    \tag{SD.6}
\]

and, provided `c ne 0`,

\[
 A_{\rm PG}<s(\deg Q+1).                                     \tag{SD.7}
\]

Define `XiShiftedHardEdgeCofinalPrimeGammaInversionPhase` to mean that one fixed
polynomial--Gaussian carrier and cutoff index have, at every sufficiently large integral mass,

1. negative completed capital `(SD.3)` for the explicit finite hard-edge packet;
2. an actual balance inversion `(SD.6)` satisfying `(SD.7)`;
3. the existing parabolic lower and linear upper dimension bounds.

The closed capstone is

\[
 \boxed{\qquad
 \neg\mathrm{RH}
 \quad\Longleftrightarrow\quad
 \texttt{XiShiftedHardEdgeCofinalPrimeGammaInversionPhase}.
 \qquad}                                                     \tag{SD.8}
\]

## Dependency-closed paper proof

The polynomial-square explicit formula gives, pointwise for `s>0`,

\[
 \mathcal B_{y,d,c}(s)=\pi\,T(Q_{y,d,c},s).                  \tag{SD.9}
\]

Multiplication by `s^(2d)e^(-ys)` identifies the right side with `pi` times the real filtered
Gamma kernel at `M=0`.  Integrating on `(0,infinity)` and applying the already proved filtered
Gamma transmutation yields

\[
 \mathcal C_{y,d,c}
 =\pi\int_0^\infty s^{2d}e^{-ys}T(Q,s)\,ds
 =\pi(2d)!\mathcal H_{y,d}(c),
\]

which is `(SD.4)`.  No component is split and no new infinite interchange is introduced: the
literal prime series is already absolutely convergent at each positive heat time, while
integrability of the complete kernel is the existing transmutation theorem.

For `(SD.5)`, the shifted-reversal evaluation law gives

\[
 Q(x^2)=(a^2+x^2)^dR((a^2+x^2)^{-1}).
\]

Since

\[
 2a^2(a^2+x^2)^{-1}-1={a^2-x^2\over a^2+x^2},
\]

substitution into `R=B(2a^2X-1)`, squaring, and cancelling the positive power
`(a^2+x^2)^(2d)` proves `(SD.5)`.

If the capital is negative and every positive-time balance were nonnegative, then the Laplace
weight in `(SD.3)` would be nonnegative everywhere on `(0,infinity)`, so its integral would be
nonnegative.  This contradiction proves `(SD.6)`.  By `(SD.9)` the selected polynomial-Gaussian
trace is negative.  When `c ne 0`, shifted reversal is nonzero; the completed-wedge theorem then
forces `(SD.7)`.

For `(SD.8)`, start from the existing closed equivalence

\[
 \neg\mathrm{RH}\iff
 \texttt{XiShiftedHardEdgeCofinalLinearNegativePhase}.
\]

At each cofinal mass, `(SD.4)` multiplies the explicit negative quadratic by the strictly positive
factor `pi*(2d)!`, hence gives negative capital.  The preceding argument supplies the source
inversion and aperture escape; the old phase supplies both dimension bounds.  Conversely, one
negative capital at the threshold mass and `(SD.4)` recover one negative explicit Hankel
quadratic, and the existing finite-Hankel criterion gives `not RH`.  This proves the closed
equivalence.

## Hostile proof audit

- `(SD.4)` is an equality of complete integrands; it does not illegally integrate Gamma, polar,
  and prime terms separately.
- The indicator at nonpositive heat time is irrelevant because every set integral is over `Ioi 0`.
- The Laplace weight is strictly positive on `Ioi 0`; nonnegativity suffices for the contradiction.
- Negative capital forces `c ne 0`, since the zero vector gives zero Hankel quadratic by `(SD.4)`.
- Aperture escape applies to the actual shifted-reversal polynomial, not to an unrelated degree
  bound.
- `(SD.8)` is a source-faithful equivalence, not an RH proof.  Remaining open core is an
  unconditional mechanism excluding the cofinal inversion phase.

## Higher universal principle

Divisor-side Hankel negativity, heat-side polynomial growth, and hard-edge Cauchy compactness are
three shadows of one positive source disintegration.  The Laplace variable is not an auxiliary
estimate: it resolves every finite divisor packet into literal completed arithmetic-source
balances.  Reciprocal reversal is the exact gauge in which all admission-degree powers cancel,
leaving `(SD.1)`.  Earlier scalar budgets failed because they integrated or quotiented away this
source incidence before applying the hard-edge gauge.

## Exact open core after this theorem

`[OPEN CORE]` Prove that a single fixed polynomial--Gaussian physical carrier cannot sustain the
cofinal super-aperture source inversions in `(SD.8)`.  Any acceptable theorem must use the
degree-free Cauchy density `(SD.5)` and the literal Gamma--polar--von-Mangoldt incidence; generic
Hankel positivity, root hyperbolicity, or scalar absolute-tail bounds are already known to be
insufficient or RH-equivalent.
