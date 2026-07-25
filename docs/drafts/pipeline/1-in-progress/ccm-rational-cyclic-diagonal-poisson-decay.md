# Rational CCM cyclic diagonal decay is signed Poisson decay

- **ID:** ccm-q-cyclic-diagonal-poisson
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / FORMALIZATION TARGET
- **Source:** CCM, arXiv:math/0703392, Proposition 4.8 and Definition 4.9
- **Statement:** The rational CCM restriction lands in the exact cyclic target because its
  cyclic diagonal trace is a signed adelic Poisson sum with both boundary terms killed by
  \(\ker\varepsilon_0^\natural\cap\ker\varepsilon_1^\natural\).

## Goal

Reconstruct, dependency by dependency and without an RH premise, the analytic landing theorem
used by the arithmetic-cohomology cokernel. This is the analytic input needed before the
Real-Brauer lift can be completed in Lean.

The target condition is source-faithful:
\[
 {\bf S}^{\natural}(C_{\mathbb Q},\mathcal L^1(\mathcal H_b))
 \subset C(C_{\mathbb Q},\mathcal L^1(\mathcal H_b))^\natural
\]
requires only that the scalar cyclic main-diagonal trace
\[
 b\longmapsto\operatorname{Tr}(T_0(b)\cdots T_n(b))
\]
belong to
\[
 {\bf S}(C_{\mathbb Q})
 =\bigcap_{\beta\in\mathbb R}\mu^\beta\mathcal S(C_{\mathbb Q}).
\]
It does not require rapid decay of the operator trace norm.

## Exact conjecture

Let
\[
 Z=f_{k_0}U_{k_0}\otimes\cdots\otimes f_{k_n}U_{k_n}
 \in\mathcal S(\mathcal G_{\mathbb Q})^\natural_0,
 \qquad
 \gamma_0=1,\quad\gamma_{j+1}=k_j\gamma_j .
\]

`[CCM_Q_CYCLIC_POISSON]`

1. If \(\prod_jk_j\ne1\), the cyclic diagonal trace is identically zero.
2. If \(\prod_jk_j=1\), set
   \[
     h_b(q)=\prod_{j=0}^n f_{k_j}(\gamma_j^{-1}qb).
   \]
   Then
   \[
     \Theta_Z(b)=\sum_{q\in\mathbb Q^\times}h_b(q)
   \]
   is absolutely convergent at every \(b\), continuous in trace norm before taking trace, and
   its scalar value satisfies adelic Poisson duality.
3. The source conditions
   \(\varepsilon_0^\natural(Z)=\varepsilon_1^\natural(Z)=0\) remove respectively the physical
   zero term and Fourier zero term. Consequently
   \(\Theta_Z\in{\bf S}(C_{\mathbb Q})\), including every multiplicative derivative.
4. Complex conjugate sign-reflection carries \(\Theta_Z\) to
   \(\overline{\Theta_Z}\). Hence the exact target cyclic submodule is stable under the
   quaternionic operator involution.

The first formal sector is
\[
 f=f_\infty\otimes 1_{\widehat{\mathbb Z}},\qquad
 \Theta_f(\mu)=\sum_{m\in\mathbb Z}f_\infty(\mu m).
\]
For \(\mu>0\), Poisson summation gives
\[
 \Theta_f(\mu)
 =\mu^{-1}\sum_{m\in\mathbb Z}
   \widehat f_\infty(m/\mu).
\]
If \(f_\infty(0)=0\) and
\(\widehat f_\infty(0)=\int_\mathbb Rf_\infty=0\), both sides are punctured lattice sums and
Schwartz seminorm estimates give arbitrary polynomial decay at \(\infty\) and \(0^+\).

## Attack

1. Formalize scaled one-dimensional Schwartz Poisson summation.
2. Prove arbitrary-power bounds for punctured Schwartz lattice sums.
3. Combine Poisson with the two vanishing functionals to prove two-ended value decay.
4. Commute \(\mu\partial_\mu\) through the Schwartz family; repeat for every derivative.
5. Express every finite Bruhat factor as a finite linear combination of compact-open coset
   indicators. Reduce its rational diagonal to finitely many shifted/dilated integer lattices.
6. Prove finite Fourier duality for those periodic weights and assemble adelic Poisson.
7. Extend from algebraic tensors and monomials through the Bruhat--Schwartz LF bornology and
   cyclic completion.

## Hostile checks

- Absolute orbit bounds alone cannot prove decay as \(\mu\to0^+\); they grow at density
  order \(\mu^{-1}\). Cancellation must occur before taking absolute values.
- \(\varepsilon_0=0\) alone removes only the physical origin. Without
  \(\varepsilon_1=0\), Poisson leaves the \(\mu^{-1}\widehat f(0)\) term.
- Degree-zero evidence cannot be extrapolated to cyclic degree \(n\). The product condition
  \(\prod k_j=1\) and the product trace \(\operatorname{Tr}(T_0\cdots T_n)\) must be encoded.
- Two-ended value decay is weaker than membership in \({\bf S}(C_{\mathbb Q})\); all
  multiplicative derivatives and LF-continuity remain mandatory.
- No positivity, zero location, spectral determinant, or RH statement is used.

## Gates

- [x] 0 → 1 in-progress: exact source target, attack, and obstruction identified
- [x] Basic \(1_{\widehat{\mathbb Z}}\) value-level Poisson sector formalized
- [ ] 1 → 2 fully-proven: full adelic/LF/cyclic proof dependency-closed
- [ ] 2 → 3 formalized: exact theorem, targeted Lean builds, axiom audit
- [ ] 3 → 4 publication-ready

## Log

- 2026-07-25 — Created after hostile re-reading of CCM Proposition 4.8 and Definition 4.9.
  Corrected prior conflation of pointwise trace class with strong-Schwartz diagonal trace.
- 2026-07-25 — Formalized exact scaled Poisson duality and explicit arbitrary-power bounds at
  both multiplicative ends for the \(1_{\widehat{\mathbb Z}}\) sector. Capstone axiom audits
  contain only foundational Lean axioms.
