# Kähler--Riemann flow purity

- **ID:** `deninger-kahler-riemann-flow-purity`
- **Stage:** 2-fully-proven
- **Type:** LITERATURE THEOREM + PAPER COROLLARY
- **Label:** `DAC_KAHLER_RIEMANN_FLOW_PURITY`
- **Parent:** `deninger-source-three-term-hodge-purity`
- **Statement:** conformal flow on a dense-leaf Kähler--Riemann foliation
  acts on reduced leafwise degree \(n\) as \(e^{nt/2}\) times a unitary
  group; its generator has real part \(n/2\).

## Source theorem

Let \((S,\mathcal F,\omega)\) be a Kähler--Riemann foliation of complex
leaf dimension \(g\) on a closed oriented manifold, with oriented
transversal and a dense leaf.  Deninger--Singhof prove:

1. the orthogonal reduced leafwise Hodge decomposition
   \[
   A^\bullet_{\mathcal F}(S)
   =
   \mathcal H^\bullet_{\mathcal F}
   \widehat\oplus
   \overline{\operatorname{im}d_{\mathcal F}}
   \widehat\oplus
   \overline{\operatorname{im}d_{\mathcal F}^*};
   \]
2. identification of reduced leafwise cohomology with harmonic forms;
3. nondegenerate leafwise Poincaré duality when a leaf is dense;
4. a polarized real Hodge structure on primitive reduced cohomology;
5. Proposition 4.6: if a leafwise holomorphic map \(f\) satisfies
   \[
   f^*[\omega]=q[\omega],\qquad q>0,
   \]
   then on reduced degree \(n\)
   \[
   f^*=q^{n/2}U_n
   \]
   for a unitary \(U_n\).

Primary source:
[Deninger--Singhof, *Real polarizable Hodge structures arising from
foliations*](https://arxiv.org/abs/math/0204111), especially Section 4,
Propositions 4.1, 4.3, 4.4, and 4.6.

## Continuous-flow corollary

`[PROVED HERE] [DAC_KAHLER_RIEMANN_FLOW_PURITY]`

Assume a smooth flow \(\phi^t\) preserves \(\mathcal F\), is holomorphic
along leaves, and satisfies
\[
 (\phi^t)^*[\omega]=e^t[\omega].                                    \tag{1}
\]
Then for every \(n\)
\[
 (\phi^t)^*|_{\bar H^n_{\mathcal F}}
   =e^{nt/2}U_n(t),                                                  \tag{2}
\]
where every \(U_n(t)\) is unitary.  The group law for \(\phi^t\) and
uniqueness in `(2)` give
\[
 U_n(t+s)=U_n(t)U_n(s).
\]
If the action is strongly continuous on the Hilbert completion of
harmonic forms, \(U_n(t)\) is a strongly continuous unitary group.  By
Stone's theorem its generator is skew-adjoint.  Hence the generator of
\((\phi^t)^*\) has the form
\[
 \Theta_n=\frac n2+S_n,\qquad S_n^*=-S_n.                            \tag{3}
\]
Every point-spectral value \(\lambda\) therefore satisfies
\[
 \operatorname{Re}\lambda=\frac n2.                                \tag{4}
\]
For \(n=1\), `(4)` is Deninger's critical-line purity.

## Proof

Apply Deninger--Singhof Proposition 4.6 to \(f=\phi^t\) and
\(q=e^t\), obtaining `(2)`.  The flow law implies the unitary group law.
Strong continuity and Stone's theorem give `(3)`.  A skew-adjoint
operator has purely imaginary point spectrum, proving `(4)`.

Equivalently, without invoking the infinitesimal generator, if
\(\Theta_nx=\lambda x\), then
\[
 \|(\phi^t)^*x\|
 =e^{t\operatorname{Re}\lambda}\|x\|
 =e^{nt/2}\|x\|,
\]
for every \(t\), so \(\operatorname{Re}\lambda=n/2\).

## Arithmetic consequence and exact limit

If reduced arithmetic cohomology is realized by this leafwise theory in
degree one and every nontrivial zero of completed zeta occurs in the
point spectrum of \(\Theta_1\), then RH follows from `(4)`.

This theorem does not construct the arithmetic lamination, prove the
prime-orbit trace formula, or identify zeta zeros with the spectrum.  It
turns Hodge positivity from an independent analytic axiom into a
consequence of one geometric construction gate:
`DAC_KAHLER_RIEMANN_ARITHMETIC_LEAF_REALIZATION`.

**Verdict:** `FULLY PROVEN; SOURCE HODGE/PURITY IMPLICATION CLOSED`.

## Log

- 2026-07-26 — Extracted the exact continuous-flow corollary from
  Deninger--Singhof Section 4.  No Xi space, zero-defined norm, RH
  premise, CCM object, or numerical computation occurs.
