# Parity-free simple-ground Fourier real-zero law

- **ID:** `parity-free-simple-ground-fourier-real-zero-law`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, full restricted-Weil ground selection
- **Type:** THEOREM + FAILED CLOSURE AUDIT (paper)
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [FINITE ODD CORE LEAN-PROVED] [CONTINUOUS STEP OPEN]`
- **External parent:** Connes--van Suijlekom,
  [Quadratic Forms, Real Zeros and Echoes of the Spectral Action](https://arxiv.org/abs/2511.23257)
- **Statement:** For the reflection-invariant truncated-convolution operators of
  Connes--van Suijlekom, a simple isolated lowest eigenfunction has a Fourier transform with only
  real zeros without assuming that the eigenfunction is even.  The missing odd case follows from
  a nonnegative rank-one correction of the squared frequency operator.

## Goal and Route-U verdict

The Route-U finite-impedance branch suggested the following attack.

> **[CONJECTURE, FALSIFIED AS A CLOSURE]** A simple negative hard root
> $r=-\kappa^2$ with positive terminal mass makes $i\kappa$ a common nonreal zero of the
> ground, so a degenerate or odd extension of the Connes--van Suijlekom theorem should contradict
> it.

The exact killing mechanism is parity.  Positive terminal mass proves

\[
 \langle \cosh(\kappa t),k\rangle=0
 \qquad(k\in\ker A_\sigma^+),
\]

so $i\kappa$ is common only to the **even** ground space.  It says nothing about an odd vector at
the bottom of the full operator.  The common-zero formulation for a degenerate ground therefore
does not apply at $i\kappa$ unless one first supplies the missing cross-parity admission theorem.

The strongest positive survivor is the theorem proved below: the evenness hypothesis in the
simple-ground real-zero theorem is unnecessary.  This is useful but does not close Route U.  It
proves that an earlier simple odd ground also has a real-rooted Fourier transform, so odd descent
is compatible with the external theorem rather than contradictory to it.  The missing datum is
full-ground parity selection (or an equivalent literal odd-sector lower bound), not another
real-zero theorem.

## 1. Finite odd theorem

Use the finite matrix setting of the external parent.  On

\[
 H=\mathbb R^{\{-N,\ldots,N\}},
 \qquad De_j=j e_j,
 \qquad \Gamma e_j=e_{-j},
\]

let $Q\ge0$ be real symmetric, commute with $\Gamma$, and have entries

\[
 q_{ij}=\frac{b_i-b_j}{i-j}\quad(i\ne j),
 \qquad b_{-j}=-b_j,
\]

with arbitrary reflection-even diagonal.  Put

\[
 \eta=\sum_{j=-N}^N e_j,
 \qquad
 \beta=\sum_{j=-N}^N b_j e_j.
\]

Then $\eta$ is even, $\beta$ is odd, and the exact commutator is

\[
 [D,Q]=DQ-QD=|\beta\rangle\langle\eta|-|\eta\rangle\langle\beta|.
 \tag{PF.1}
\]

Assume

\[
 \ker Q=\mathbb R\xi,
 \qquad \Gamma\xi=-\xi.
 \tag{PF.2}
\]

Let $\widehat\xi$ be the Fourier transform of the trigonometric polynomial with coefficient
vector $\xi$, restricted to one period and extended by zero.  Then every zero of
$\widehat\xi$ is real.

## 2. Squared-frequency correction `[PAPER-PROVED]`

Set

\[
 \delta=D\eta=\sum_{j=-N}^N j e_j.
\]

Both $\delta$ and $\xi$ are odd.  Write temporarily

\[
 a=\langle\delta,\xi\rangle,
 \qquad b=\langle\beta,\xi\rangle.
\]

Applying `(PF.1)` to $\xi$ gives

\[
 QD\xi=b\eta.                                             \tag{PF.3}
\]

The vector $D\xi$ is nonzero and even, hence it cannot lie in the one-dimensional odd kernel of
(Q).  Therefore

\[
 0<\langle QD\xi,D\xi\rangle=ab.                         \tag{PF.4}
\]

In particular $a\ne0$.  Rescale $\xi$ so that

\[
 \langle\delta,\xi\rangle=1.
 \tag{PF.5}
\]

After this rescaling, `(PF.4)` says (b>0).

Restrict to the odd subspace (H^-), and put (T=D^2|_{H^-}).  Its spectrum is the simple set
$\{1^2,\ldots,N^2\}$.  Squaring the commutator and using parity gives

\[
 [T,Q]|_{H^-}=|\beta\rangle\langle\delta|
              -|\delta\rangle\langle\beta|.              \tag{PF.6}
\]

Equations `(PF.2)`, `(PF.5)`, and `(PF.6)` imply

\[
 QT\xi=b\delta-\beta.                                    \tag{PF.7}
\]

Define the rank-one correction

\[
 T'=T-|T\xi\rangle\langle\delta|.                        \tag{PF.8}
\]

First, $T'\xi=0$.  Second, `(PF.6)` and `(PF.7)` give

\[
 QT'=T'^*Q.                                               \tag{PF.9}
\]

Indeed,

\[
 QT-TQ=-|\beta\rangle\langle\delta|
        +|\delta\rangle\langle\beta|,
\]

while the two correction terms are

\[
 -|b\delta-\beta\rangle\langle\delta|,
 \qquad
 -|\delta\rangle\langle b\delta-\beta|,
\]

and their skew difference cancels the commutator exactly.  Thus (T') induces a self-adjoint
operator on the separated Euclidean quotient $H^-/\ker Q$.

The new point is that this induced operator is not merely self-adjoint; it is nonnegative.  For
every odd (f), `(PF.1)` gives

\[
 \langle QD^2f,f\rangle
 =\langle QDf,Df\rangle
  -\langle\beta,f\rangle\langle\delta,f\rangle.
 \tag{PF.10}
\]

Using `(PF.7)` in `(PF.8)`, the mixed terms cancel and yield

\[
 \langle QT'f,f\rangle
 =\langle QDf,Df\rangle-b\langle\delta,f\rangle^2.
 \tag{PF.11}
\]

But `(PF.3)` and `(PF.5)` say

\[
 \langle D\xi,Df\rangle_Q=b\langle\delta,f\rangle,
 \qquad
 \|D\xi\|_Q^2=b.
\]

Cauchy--Schwarz for the semidefinite (Q)-inner product therefore gives

\[
 b^2\langle\delta,f\rangle^2
 \le b\langle QDf,Df\rangle.
\]

Since (b>0), `(PF.11)` is nonnegative.  Hence every eigenvalue of the operator induced by (T')
on $H^-/\ker Q$ lies in $[0,\infty)$.

## 3. Determinant and Fourier zeros `[PAPER-PROVED]`

For $s\notin\{1^2,\ldots,N^2\}$, the rank-one determinant identity and `(PF.5)` give

\[
\begin{aligned}
 \det(T'-s)
 &=\det(T-s)
   \left(1-\langle\delta,(T-s)^{-1}T\xi\rangle\right)\\
 &=-s\det(T-s)\langle\delta,(T-s)^{-1}\xi\rangle.
                                                               \tag{PF.12}
\end{aligned}
\]

The left side has one zero from $\xi$, and every remaining zero is a nonnegative eigenvalue of
the quotient operator.  Consequently every zero of

\[
 \det(T-s)\langle\delta,(T-s)^{-1}\xi\rangle              \tag{PF.13}
\]

is nonnegative.

Oddness of $\xi$ supplies the exact bridge back to the first-order Fourier resolvent:

\[
 \sum_{j=-N}^N\frac{\xi_j}{z-j}
 =\left\langle\delta,(z^2-T)^{-1}\xi\right\rangle.       \tag{PF.14}
\]

Indeed, the (j,-j) pair on both sides is

\[
 \frac{2j\xi_j}{z^2-j^2}.
\]

By `(PF.13)`, every non-pole zero of `(PF.14)` has $z^2\ge0$, hence $z\in\mathbb R$.
The Shannon formula used in the external parent writes the actual Fourier transform as a real-zero
sine factor times this rational function.  Pole cancellations occur only at the real sampling
lattice, and oddness contributes the zero at (z=0).  Therefore every zero of
$\widehat\xi$ is real.

This proves the finite odd theorem.

## 4. Infinite-dimensional theorem `[PAPER-PROVED]`

Let (A) be the lower-bounded self-adjoint operator associated with a real truncated-convolution
form on (L^2([-L/2,L/2])), under the precise core and isolation hypotheses of the external
parent.  Assume its minimum $\lambda$ is simple and isolated, with odd eigenfunction $\xi$.

The external approximation proof applies after projecting every approximant to the odd subspace.
More explicitly, choose odd trigonometric polynomials $\eta_\varepsilon$ converging to $\xi$ in
norm with Rayleigh value below $\lambda+\varepsilon$, and let $E_N$ be a symmetric Fourier
space containing $\eta_\varepsilon$.  The minimum $\lambda_N$ of the compressed form satisfies

\[
 \lambda\le\lambda_N\le\lambda+\varepsilon.
\]

If the rest of the spectrum of $A$ lies above $\lambda+\Delta$, min--max on
$E_N\cap\xi^\perp$ puts the second compressed eigenvalue above $\lambda+\Delta$.  Hence, for
small $\varepsilon$, the compressed minimum is simple.  The compression commutes with reflection,
so its minimum vector has definite parity; its nonzero overlap with the odd vector $\xi$ forces
that parity to be odd.  Subtracting $\lambda_N I$ gives a positive matrix of the finite form above
with one-dimensional odd kernel.  Its minimum vector therefore has real-rooted Fourier transform.

The compressed vectors converge to $\xi$ in $L^2$.  Since all functions have support in the
fixed interval,

\[
 |\widehat f(z)|
 \le \sqrt L\,e^{L|\operatorname{Im}z|/2}\|f\|_2,
\]

so their Fourier transforms converge locally uniformly on $\mathbb C$.  Hurwitz's theorem then
excludes a nonreal zero of $\widehat\xi$.

Finally, a simple eigenfunction of a reflection-commuting operator is automatically either even or
odd.  The even case is the external theorem; the odd case is proved above.  Therefore:

\[
 \boxed{
 \text{Every simple isolated lowest eigenfunction has only real Fourier zeros.}
 }
 \tag{PF.15}
\]

No parity hypothesis is needed.

## 5. Hostile audit and significance

- **Internal audit.** Route U already used the even theorem and the finite-source common-zero
  remark.  Corpus searches found no general odd proof or the (D^2) correction `(PF.8)`--`(PF.11)`.
  This is not a Lean claim.
- **External audit.** The cited primary source proves the even theorem, comments that degenerate
  eigenspaces require common zeros, and checks the odd phenomenon only in its explicit
  five-dimensional appendix.  Targeted arXiv searches found no exact general odd statement.
  Search absence is not a priority proof; status remains `[NOVELTY UNVERIFIED]`.
- **Circularity audit.** `(PF.15)` uses only the divided-difference commutator, positivity,
  simplicity, parity, min--max, and Hurwitz.  It does not assume zero reality or RH.
- **Route-U delta.** The theorem removes parity from the external real-zero mechanism but kills the
  proposed closure: an odd spectral descent produces another real-rooted ground rather than a
  contradiction.  Any successful successor must prove from the literal completed-Xi source that
  the selected even critical state is the full bottom, or must couple its nonreal zero to every odd
  lower-ground vector.  Even-ground common zeros alone cannot do this.
- **Lean status.** Finite odd core is proved in
  `formal/GaloisForLFunctions/RHTower/CCMParityFreeOddGroundFourier.lean`: positive semimetric
  completion, nonnegative full characteristic roots, and real non-pole Fourier-resolvent zeros.
  `CCMCompactFourierMeanSquareZeroTransfer.lean` proves the exact fixed-support `L²` Fourier bound,
  locally uniform convergence, and nonzero-limit real-zero transfer. Literal published-source
  parity blocks and compressed-ground mean-square convergence remain open. This formalization
  closes the finite and analytic-transfer parts of the literature parity debt but does not receive
  Route-O ground-selection credit.

## No-go closure

- **Exact killing theorem/mechanism:** $i\kappa$ is common only to the even kernel; odd ground
  evaluation is unconstrained.
- **Strongest positive survivor:** parity-free simple-ground Fourier real-zero law `(PF.15)`.
- **New insight:** parity is not the obstruction.  Full-ground selection is.
- **Status:** dependency-closed paper proof; external novelty unverified; finite odd core
  and fixed-support analytic transfer Lean-closed; no Route-O ground-selection credit.

## Log

- 2026-08-11 — odd (D^2) correction derived; common-zero closure falsified; paper proof closed.
- 2026-08-14 — finite odd squared-frequency correction and non-pole Fourier-resolvent reality
  formalized in `CCMParityFreeOddGroundFourier.lean`.
- 2026-08-14 — exact fixed-support mean-square-to-locally-uniform Fourier estimate and Hurwitz
  zero-locus transfer formalized in `CCMCompactFourierMeanSquareZeroTransfer.lean`; literal
  compressed-ground approximation remains.
