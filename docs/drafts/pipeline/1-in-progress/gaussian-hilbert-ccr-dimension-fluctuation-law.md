# Gaussian Hilbert CCR dimension--fluctuation law

- **ID:** gaussian-hilbert-ccr-dimension-fluctuation-law
- **Stage:** 1-in-progress
- **Type:** FAILURE-DRIVEN CANDIDATE UNIVERSAL LAW
- **Source:** `gaussian-hilbert-fano-curvature.md`
- **Scientific status:** `[CONJECTURED] [NOVELTY UNVERIFIED]`
- **Statement:** A finite commuting annihilation compression with an exact CCR completion obeys
  a dimension-sharp number-variance identity whose two remainders are mixed nonnormality and
  traceless leakage energy.

## Goal

Replace the signed row--column anomaly in the failed multi-mode commutator-square route by an
exact positive decomposition.  The target must specialize to the Hilbert-line self-commutator
law, apply to every finite annihilation-invariant Fock subspace, and expose a quantitative open
condition for low-dimensional Gaussian determinant concavity.

## Exact conjecture

Let `I`, `N`, and `M` be finite index sets.  Put `d = card I`.  For every `i in I`, let

\[
 A_i:\mathbb R^N\to\mathbb R^N,
 \qquad B_i:\mathbb R^M\to\mathbb R^N,
\]

and assume the finite upper-left canonical commutation relations

\[
 B_iB_j^*=\delta_{ij}I+A_j^*A_i-A_iA_j^*                 \tag{CCR}
\]

together with `A_i A_j = A_j A_i`.  Define

\[
\begin{aligned}
 E&=\sum_i\lVert A_i\rVert_{HS}^2,\\
 V&=\left\lVert\sum_iB_i^*A_i\right\rVert_{HS}^2,\\
 C&=\sum_{i,j}\lVert A_iA_j^*-A_j^*A_i\rVert_{HS}^2,\\
 S&=\sum_iB_i^*A_i,\\
 K&=\sum_{i,j}\left\lVert dB_i^*A_j-\delta_{ij}S\right\rVert_{HS}^2.
\end{aligned}
\]

Then the proposed **CCR dimension--fluctuation identity** is

\[
 \boxed{\quad
 d(d+1)(dE-V)=d^2C+K.
 \quad}                                                   \tag{DF}
\]

Consequently, if `d>0`,

\[
 \boxed{\quad V\le dE.\quad}                             \tag{FB}
\]

Equality in (FB) holds exactly when every mixed commutator vanishes and the leakage tensor is
pure trace:

\[
 A_iA_j^*=A_j^*A_i,
 \qquad dB_i^*A_j=\delta_{ij}S
 \quad(i,j\in I).                                        \tag{EQ}
\]

For a finite annihilation-invariant subspace of symmetric Fock space, `E` is the mean total
number and `V` is its Slater determinant-line variance.  Thus (FB) says that its Fano factor is
at most the active one-particle dimension.  At `d=1`, `K=0` and (DF) becomes

\[
 E-V=\frac12\lVert[A_1,A_1^*]\rVert_{HS}^2,
\]

the exact Hilbert-line law.

## Paper-proof attack

Put

\[
 Q=\sum_iA_i^*A_i,
 \qquad R=\sum_iA_iA_i^*,
 \qquad T=\sum_{i,j}\lVert B_i^*A_j\rVert_{HS}^2.
\]

The proof is expected to close through four exact identities:

1. Expanding `V` with (CCR) and commutativity gives

   \[
   V=E+\operatorname{tr}(QR)-\operatorname{tr}(Q^2).     \tag{1}
   \]

2. The mixed-commutator parent identity is

   \[
   C=\lVert Q-R\rVert_{HS}^2
    =\operatorname{tr}(Q^2)+\operatorname{tr}(R^2)
      -2\operatorname{tr}(QR).                            \tag{2}
   \]

3. Summing the diagonal part of (CCR) gives
   `sum_i B_i B_i^* = dI+Q-R`, and therefore

   \[
   T=dE+\operatorname{tr}(QR)-\operatorname{tr}(R^2)
    =(d+1)E-V-C.                                         \tag{3}
   \]

4. Orthogonally separating the trace and traceless parts of the matrix-valued tensor
   `Z_(ij)=B_i^*A_j` gives

   \[
   K=d^2T-dV.                                            \tag{4}
   \]

Substitution of (3) into (4) is exactly (DF).  Every term on the right of (DF) is a literal sum
of squares, which yields (FB) and (EQ).

## Hostile audit

- The scalar identity `d sum ||z_i||^2 - ||sum z_i||^2 >= 0`, Hilbert--Schmidt polarization,
  finite CCR block algebra, and the mixed-commutator formula are parent mathematics.
- The arbitrary commuting-tuple counterexample does not apply: it has no matrices `B_i`
  satisfying (CCR).  The radial weighted symmetric-module counterexample fails for the same
  reason.
- The compiled degree-five Gaussian counterexample is compatible with (DF): it only requires
  `V>E`, whereas (FB) permits `V` up to `dE` when `d>1`.
- The candidate contribution is the exact invariant organization (DF), especially the
  traceless leakage tensor `K`, its equality classification, and the Gaussian determinant-line
  interpretation.  Exact searches across Fano-factor bounds, compressed annihilators,
  Hilbert--Schmidt commutators, and multivariable Fock modules have not located (DF).  Search
  noncollision is not priority evidence.
- (DF) alone does not prove the three-dimensional Gaussian concavity conjecture.  In dimension
  `d`, that conjecture becomes the sharper coercivity target

  \[
   dC+K/d\ge(d-1)(d+1)E,
  \]

  in the unscaled notation.  This is the next hostile gate, not an assumed corollary.

## Gates

- [x] 0 -> 1 in-progress: exact statement, falsification boundary, and proof attack recorded
- [ ] 1 -> 2 fully-proven: close identities (1)--(4), equality, and Fock interpretation
- [ ] 2 -> 3 formalized: exact finite-matrix theorem, bound, and equality criterion compile
- [ ] 3 -> 4 publication-ready: expert novelty audit and a sharp Gaussian/kernel consequence

## Log

- 2026-07-20 -- conjectured from the failure of the naive multi-mode commutator square; isolated
  the traceless CCR leakage tensor as the missing positive remainder.
