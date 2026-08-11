# Rank-two commutator parity-multiplicity balance

- **ID:** `rank-two-commutator-parity-multiplicity-balance`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Route:** U, full restricted-Weil parity descent
- **Type:** THEOREM + FRONTIER REDUCTION (paper)
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`
- **External parent:** Connes--van Suijlekom,
  [Quadratic Forms, Real Zeros and Echoes of the Spectral Action](https://arxiv.org/abs/2511.23257)
- **Statement:** For every eigenvalue of a reflection-invariant divided-difference operator with
  the Connes--van Suijlekom rank-two commutator, its even and odd multiplicities differ by at most
  one.  In particular, any eigenvalue lying strictly below the opposite-parity floor is simple.

## 1. Exact finite theorem

Use the real finite-dimensional setting

\[
 De_j=j e_j,
 \qquad \Gamma e_j=e_{-j},
 \qquad D\Gamma=-\Gamma D,
 \qquad Q\Gamma=\Gamma Q,                                 \tag{PMB.1}
\]

and assume the exact commutator

\[
 [D,Q]
 =|\beta\rangle\langle\eta|-|\eta\rangle\langle\beta|,
 \qquad \Gamma\eta=\eta,
 \qquad \Gamma\beta=-\beta.                              \tag{PMB.2}
\]

For a real eigenvalue $\lambda$, let

\[
 E_\lambda^\pm
 =\ker(Q-\lambda I)\cap\ker(\Gamma\mp I).                \tag{PMB.3}
\]

Then

\[
 \boxed{
 \left|\dim E_\lambda^+-\dim E_\lambda^-\right|\le1.
 }                                                        \tag{PMB.4}
\]

### Proof

If $f\in E_\lambda^+$ and $\langle\eta,f\rangle=0$, parity also gives
$\langle\beta,f\rangle=0$.  Hence `(PMB.2)` gives $[D,Q]f=0$, and therefore

\[
 QDf=DQf=\lambda Df.                                     \tag{PMB.5}
\]

The vector $Df$ is odd.  Moreover $D$ is injective on
$E_\lambda^+\cap\eta^\perp$: if $Df=0$, then $f$ is a multiple of $e_0$, but
$\langle\eta,e_0\rangle\ne0$.  Thus

\[
 D:E_\lambda^+\cap\eta^\perp\hookrightarrow E_\lambda^-. \tag{PMB.6}
\]

Since the kernel of one linear functional has codimension at most one,

\[
 \dim E_\lambda^+-1\le\dim E_\lambda^-.                 \tag{PMB.7}
\]

Similarly, if $g\in E_\lambda^-$ and $\langle\beta,g\rangle=0$, then parity gives
$\langle\eta,g\rangle=0$, so $[D,Q]g=0$ and

\[
 D:E_\lambda^-\cap\beta^\perp\hookrightarrow E_\lambda^+. \tag{PMB.8}
\]

Here $D$ is injective on the entire odd subspace.  Hence

\[
 \dim E_\lambda^--1\le\dim E_\lambda^+.                 \tag{PMB.9}
\]

Equations `(PMB.7)` and `(PMB.9)` prove `(PMB.4)`.

## 2. Strict parity-floor corollary

Let

\[
 \alpha_+=\inf\operatorname{spec}(Q|_{H^+}),
 \qquad
 \alpha_-=\inf\operatorname{spec}(Q|_{H^-}).             \tag{PMB.10}
\]

If $\lambda<\alpha_+$ is an odd eigenvalue, then $E_\lambda^+=0$; `(PMB.4)` forces

\[
 \dim E_\lambda^-=1.                                    \tag{PMB.11}
\]

The even analogue is identical.  Thus every eigenvalue strictly below the opposite-parity floor
is simple.  This conclusion uses no positivity of $Q$ and no generic-simplicity assumption.

The same proof applies to an infinite-dimensional reflection-invariant self-adjoint operator on a
common commutator core whenever eigenvectors lie in the domain of $D$ and `(PMB.2)` holds there.
Compact resolvent then makes every relevant eigenspace finite-dimensional and every isolated
parity-separated floor simple.

## 3. Route-U consequence `[PAPER-PROVED]`

At the selected hard-edge aperture, the even form has floor zero.  A simple negative hard root
$r=-\kappa^2$ with positive terminal mass supplies the explicit odd trial vector from the
parity-jet law with energy

\[
 r\gamma_r=-\kappa^2\gamma_r<0.                          \tag{PMB.12}
\]

If the literal full odd form is admitted, its floor $\lambda_-$ is therefore negative, while the
even floor is zero.  The strict parity-floor corollary makes $\lambda_-$ automatically simple.
The parity-free real-zero theorem from
`parity-free-simple-ground-fourier-real-zero-law` then implies that this unique odd lower-ground
vector has a Fourier transform with only real zeros.

So the positive-terminal-mass branch has the exact spectral shape

\[
 \boxed{
 \text{even critical vector with }\pm i\kappa\text{ zeros}
 \quad\Longrightarrow\quad
 \text{unique simple odd lower ground with only real zeros}.
 }                                                        \tag{PMB.13}
\]

This is a strict reduction: odd degeneracy is not an escape hatch.  It is also a no-go for the
proposed contradiction.  The unique odd lower ground need not vanish at $i\kappa$, so its real-zero
law remains compatible with the nonreal zero of the selected even excited state.

## 4. Exact cross-source coupling

Let $Af=0$ with $f$ even, let $Ag=\lambda g$ with $g$ odd and $\lambda\ne0$, and normalize

\[
 \langle\eta,f\rangle=1,
 \qquad
 \langle\beta,g\rangle=1.                               \tag{PMB.14}
\]

The commutator gives

\[
 ADf=-\beta,
 \qquad
 (A-\lambda I)Dg=\eta.                                  \tag{PMB.15}
\]

Pairing the second identity with $f$ yields the exact gap-current law

\[
 \boxed{
 \langle Df,g\rangle=\langle f,Dg\rangle=-\frac1\lambda.
 }                                                        \tag{PMB.16}
\]

Thus parity-separated levels are not uncoupled; their gap is the reciprocal of one canonical
source current.  However `(PMB.16)` contains no sign or vanishing statement at $i\kappa$ and does
not close Route U.

## 5. Hostile audit

- **Internal audit.** The corpus contains many parity decompositions and hard-edge inertia laws,
  but searches found no eigenvalue-by-eigenvalue multiplicity balance `(PMB.4)` or cross-current
  law `(PMB.16)` for this commutator.
- **External audit.** The cited paper proves the commutator identity and assumes a simple even
  minimum for its main theorem.  Its source does not state `(PMB.4)` or use it to make a separated
  odd floor automatically simple.  Priority remains unverified.
- **Route significance.** The theorem removes simplicity as an independent odd-branch premise.
  It also proves that odd descent cannot be killed by appealing to possible ground degeneracy.
- **Lean status.** Not started.  A finite abstract commutator formalization would not construct the
  literal hard-edge odd operator or its domain, so it would not satisfy the Route-U formal-credit
  rule.

## No-go closure

- **Exact killing mechanism:** an odd lower ground is automatically simple and real-rooted, but
  neither fact transfers the even zero $i\kappa$ to it.
- **Strongest positive survivor:** parity multiplicities differ by at most one, plus exact
  reciprocal gap-current `(PMB.16)`.
- **New insight:** positive terminal mass forces a unique odd spectral descent; remaining wall is
  cross-parity zero transfer or full odd admission, not simplicity.
- **Status:** dependency-closed paper proof; novelty unverified; no Lean or RH claim.

## Log

- 2026-08-11 — multiplicity balance and gap-current law proved; odd-degeneracy escape closed.
