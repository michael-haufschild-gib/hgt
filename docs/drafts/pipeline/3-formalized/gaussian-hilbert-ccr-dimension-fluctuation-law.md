# Gaussian Hilbert CCR dimension--fluctuation law

- **ID:** gaussian-hilbert-ccr-dimension-fluctuation-law
- **Stage:** 3-formalized
- **Type:** FAILURE-DRIVEN CANDIDATE UNIVERSAL LAW
- **Source:** `gaussian-hilbert-fano-curvature.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-FORMALIZED FINITE-MATRIX LAW]
  [FOCK APPLICATION PAPER-LEVEL] [NOVELTY UNVERIFIED]
- **Statement:** A finite commuting annihilation compression with an exact CCR completion obeys
  a dimension-sharp number-variance identity whose two remainders are mixed nonnormality and
  traceless leakage energy.

## Goal

Replace the signed row--column anomaly in the failed multi-mode commutator-square route by an
exact positive decomposition.  The target must specialize to the Hilbert-line self-commutator
law, apply to every finite annihilation-invariant Fock subspace, and expose a quantitative open
condition for low-dimensional Gaussian determinant concavity.

## Exact theorem

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

Then the **CCR dimension--fluctuation identity** is

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

## Dependency-closed paper proof

Put

\[
 Q=\sum_iA_i^*A_i,
 \qquad R=\sum_iA_iA_i^*,
 \qquad T=\sum_{i,j}\lVert B_i^*A_j\rVert_{HS}^2.
\]

The proof closes through four exact identities:

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
of squares, which yields (FB).  Since `d>0`, equality in (FB) forces both square energies to
vanish.  A finite sum of nonnegative coordinate squares vanishes exactly when every coordinate
vanishes, giving (EQ).  For `d=1`, the only leakage-tensor component is its trace, so `K=0` and
(DF) reduces to the stated self-commutator law.  No spectral estimate or completeness limit is
used.

The matrix theorem is dependency-closed.  The Fock interpretation uses the standard block
decomposition of each annihilation operator relative to a finite annihilation-invariant subspace:
the invariant upper-left blocks commute, while the off-diagonal creation/leakage blocks satisfy
(CCR).  The current Lean file formalizes the exact finite-matrix law; a typed connector from an
abstract finite Fock subspace to these blocks remains separate formalization work and is not
silently included in the Stage-3 label.

## Exact Lean theorem surface

The module `GaloisForLFunctions.HilbertMetric.CCRDimensionFluctuation` contains:

- `ccrNumberVariance_eq_mean_add_product_sub_columnSq` for identity (1);
- `ccrPairwiseMixedCommutatorEnergy_eq` and
  `ccrMixedCommutatorEnergy_eq_trace_polynomial` for identity (2);
- `ccrFullLeakageEnergy_eq_mean_variance_commutator` for identity (3);
- `ccrScaledTracelessLeakageEnergy_eq` for identity (4);
- `ccr_dimension_fluctuation_pairwise_identity` for (DF);
- `ccr_numberVariance_le_card_mul_mean` for (FB);
- `ccr_numberVariance_eq_card_mul_mean_literal_iff` for the literal rigidity classification
  (EQ);
- `oneMode_ccr_two_mul_mean_sub_variance_eq_pairwiseCommutator` for the exact one-mode law.

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
  noncollision is not priority evidence, so the result remains `[NOVELTY UNVERIFIED]`.
- (DF) alone does not prove the three-dimensional Gaussian concavity conjecture.  In dimension
  `d`, that conjecture becomes the sharper coercivity target

  \[
   d^2C+K\ge d(d+1)(d-1)E,
  \]

  or equivalently

  \[
   \frac{d}{d+1}C+\frac{K}{d(d+1)}\ge(d-1)E.
  \]

  This is the next hostile gate, not an assumed corollary.
- The law is an exact algebraic bridge and is plausibly publishable as part of a larger package,
  but no general-journal significance claim is made without either a sharp Gaussian/kernel
  consequence or an independent expert novelty audit.

## Gates

- [x] 0 -> 1 in-progress: exact statement, falsification boundary, and proof attack recorded
- [x] 1 -> 2 fully-proven: identities (1)--(4), equality, and Fock interpretation proved on paper
- [x] 2 -> 3 formalized: exact finite-matrix identity, bound, literal equality criterion, and
  one-mode specialization compile unconditionally
- [ ] 3 -> 4 publication-ready: expert novelty audit and a sharp Gaussian/kernel consequence

## Log

- 2026-07-20 -- conjectured from the failure of the naive multi-mode commutator square; isolated
  the traceless CCR leakage tensor as the missing positive remainder.
- 2026-07-20 -- closed the four-identity paper proof and formalized the pairwise sum-of-squares
  law, dimension bound, literal rigidity criterion, and one-mode specialization in Lean 4.
- 2026-07-20 -- verification audit: the leaf and Hilbert-metric umbrella pass direct Lean checks;
  `lake build GaloisForLFunctions.HilbertMetric` succeeds; headline axiom audits report only
  `propext`, `Classical.choice`, and `Quot.sound`.  No owned Lean process or scratch file was left
  running after the audit.
