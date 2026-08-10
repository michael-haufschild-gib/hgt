# Prime-valuation cyclic coframe and diagonal dagger-defect law

- **ID:** `prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-CANCELLATION LAW (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [NO RH CLAIM]`
  `[NOVELTY AUDIT OPEN] [LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`
- **Role:** replaces scalar Kummer reader by complete countable prime coframe and proves
  coordinatewise off-line injectivity before scalarization.

## Goal

Decide whether many-prime source classes can cancel each other inside current signed
cyclic/Hochschild-boundary quotient and thereby supply missing physical nullity.

## Setup

Let

\[
 A=\mathcal B\rtimes_{\mathrm{alg}}\mathbb Q^\times
 \tag{1}
\]

be actual rational-adelic Bruhat crossed-product core and let `epsilon_0` be zero-adele trace.
Let

\[
 \mathscr H=
 C_1(A)\big/
 \bigl(\operatorname{im}(\tau+1)+\operatorname{im}b_2\bigr)
 \tag{2}
\]

be signed degree-one cyclic/Hochschild-boundary quotient used by source route. Here `tau` is
degree-one cyclic reversal and `b_2` is alternating Hochschild boundary.

For every ordinary prime `ell`, write `v_ell:Q^times->Z` for normalized valuation and define on
homogeneous crossed-product monomials

\[
 \partial_\ell(aU_q)=v_\ell(q)aU_q,
 \qquad
 \phi_\ell(a_0,a_1)
 =\varepsilon_0(a_0\partial_\ell a_1).
 \tag{3}
\]

## Theorem 1: valuation cyclic coframe

For every prime `ell`:

1. `partial_ell` is algebra derivation;
2. `epsilon_0 partial_ell=0`;
3. `phi_ell` is cyclic: `phi_ell(a,b)+phi_ell(b,a)=0`;
4. `phi_ell b_2=0`.

Hence `phi_ell` descends to linear functional on `mathscr H`.

### Proof

For homogeneous crossed-product monomials, scaling grade of product is product `qr`. Since

\[
 v_\ell(qr)=v_\ell(q)+v_\ell(r),
\]

one obtains Leibniz rule

\[
 \partial_\ell(xy)=(\partial_\ell x)y+x(\partial_\ell y),
\]

then extends by finite-support linearity. Trace reads only grade one and `v_ell(1)=0`, proving
`epsilon_0 partial_ell=0`.

Apply trace to derivation of product:

\[
 0=\varepsilon_0\partial_\ell(ab)
 =\varepsilon_0((\partial_\ell a)b)
  +\varepsilon_0(a\partial_\ell b).
\]

Traciality changes first term to `phi_ell(b,a)`, proving cyclicity. Finally,

\[
 \begin{aligned}
 &\phi_\ell(ab,c)-\phi_\ell(a,bc)+\phi_\ell(ca,b)\\
 &=\varepsilon_0(ab\partial_\ell c)
   -\varepsilon_0(a(\partial_\ell b)c)
   -\varepsilon_0(ab\partial_\ell c)
   +\varepsilon_0(ca\partial_\ell b)\\
 &=0
 \end{aligned}
\]

by traciality. Thus functional kills both relations in `(2)`. QED.

## Theorem 2: prime classes are coordinate basis

For retained prime tensor

\[
 u_p=(gU_p)\otimes(gU_{p^{-1}}),
 \qquad
 \varepsilon_0^{(1)}(u_p)=1,
 \tag{4}
\]

one has

\[
 \boxed{\phi_\ell([u_p])=-\delta_{\ell p}.}
 \tag{5}
\]

Consequently classes `[u_p]` are linearly independent in `mathscr H`. Map

\[
 \Phi:\operatorname{span}\{[u_p]:p\in\mathbb P\}
 \longrightarrow\mathbb C^{(\mathbb P)},
 \qquad
 \Phi(x)=(\phi_\ell(x))_\ell
 \tag{6}
\]

sends `[u_p]` to `-e_p` and is isomorphism onto finitely supported sequences.

### Proof

Second tensor factor has grade `p^-1`, so

\[
 \partial_\ell(gU_{p^{-1}})
 =v_\ell(p^{-1})gU_{p^{-1}}
 =-\delta_{\ell p}gU_{p^{-1}}.
\]

Use product trace one in `(4)` to obtain `(5)`. If finite sum
`sum_p alpha_p[u_p]=0`, applying `phi_ell` gives `-alpha_ell=0` for every `ell`. Thus all
coefficients vanish, and `(6)` follows. QED.

## Corollary 3: scalar Kummer reader is logarithmic contraction

Unique factorization gives, for every positive rational `q`,

\[
 \log q=\sum_\ell v_\ell(q)\log\ell.
 \tag{7}
\]

Therefore established Kummer derivation and cocycle factor as

\[
 \partial_{\log}=\sum_\ell(\log\ell)\partial_\ell,
 \qquad
 \phi_{\log}=\lambda_{\log}\circ\Phi,
 \tag{8}
\]

where

\[
 \lambda_{\log}((x_\ell))
 =\sum_\ell(\log\ell)x_\ell.
\]

All sums are finite on algebraic crossed-product elements. Scalar Kummer theory is therefore one
covector shadow of full prime-valuation coframe, not complete arithmetic source object.

## Theorem 4: diagonal off-line dagger-defect injectivity

Let `rho` be nontrivial Xi zero, put

\[
 a_\rho=\Re\rho-\tfrac12,
 \qquad c_\rho=\Xi_C^{(r_\rho)}(w_\rho)\ne0,
 \tag{9}
\]

and define vector-valued physical defect on prime span by

\[
 \mathbf D_\rho(x)
 =c_\rho\bigl((1-\ell^{2a_\rho})\phi_\ell(x)\bigr)_\ell.
 \tag{10}
\]

Then

\[
 \mathbf D_\rho([u_p])
 =-c_\rho(1-p^{2a_\rho})e_p,
 \tag{11}
\]

and

\[
 \boxed{
 \ker\!\left(
 \mathbf D_\rho|_{\operatorname{span}\{[u_p]\}}
 \right)
 =
 \begin{cases}
 \operatorname{span}\{[u_p]\},&a_\rho=0,\\
 0,&a_\rho\ne0.
 \end{cases}}
 \tag{12}
\]

### Proof

Equation `(11)` is `(5)` substituted into `(10)`. If `a_rho=0`, every multiplier vanishes. If
`a_rho!=0`, then `p^(2a_rho)!=1` for every prime `p>1`; all diagonal coefficients in `(11)` are
nonzero. Linear independence from Theorem 2 makes operator injective. QED.

Contracting `(10)` by `lambda_log` recovers corpus signed-Kummer physical defect. Thus its scalar
formula is exact contraction of diagonal vector law.

## No-cancellation theorem

No finite cross-prime linear combination of current prime classes can cancel physical defect off
critical line. More generally, any completion on which every `phi_ell` extends continuously and
separates completed prime span retains coordinatewise injectivity. Merely adding primes, averaging,
or faithfully completing existing quotient cannot produce missing nullity.

Successful construction must instead change boundary law so valuation cocycles acquire a
transgression. This is stronger than “find larger receiver”: receiver is already complete enough
to see each prime independently.

## Nomotopy interpretation

Scalar observer confused arithmetic direction because it contracted infinite coframe. Restoring
coframe shows obstruction is not uncertainty among primes. Every prime carries same radial law
independently. Genuine law event must change differential/extension class simultaneously across
coframe, rather than arrange cancellation among coordinates.

This links to radial-gauge card: each `phi_ell` detects relative one-leg valuation but remains
equivariant under diagonal `Gamma_c`. Countably many such detectors still do not reduce radial
gauge stabilizer.

## Hostile audit

1. This theorem does not force `D_rho=0` and does not prove RH.
2. Trace--derivation cyclic cocycle is classical. Candidate novelty is exact rational-adelic
   valuation coframe, factorization of dagger defect, and resulting no-cancellation theorem.
3. Raw `[u_p]` lives in quotient `(2)`, not asserted to be genuine `HH_1` cycle. Existing corrected
   multiplier class supplies genuine homology separately.
4. A completion where valuation cocycles fail to extend may escape no-go; that failure is exactly
   singular transgression to be constructed and cannot be assumed.

## Lean-return note

Formalized; see `prime-valuation-cyclic-coframe-and-diagonal-dagger-defect-law-formalized.md`.
The Route-R files listed here were inspected and not rebuilt; the formalization instead reuses the
generalized-prime group algebra already built for
`generalized-prime-compound-countermodel-to-universal-selector`.

## Log

- 2026-08-08 — prime-by-prime Stokes deformation audit; proof promoted.
