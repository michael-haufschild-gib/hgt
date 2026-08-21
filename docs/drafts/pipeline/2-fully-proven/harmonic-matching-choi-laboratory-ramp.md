# Harmonic-matching Choi laboratory ramp

- **ID:** harmonic-matching-choi-laboratory-ramp
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Brown--Susskind same-draw growth--plateau--recurrence programme
- **Statement:** One fixed, ordinary, time-independent matching Hamiltonian has fixed-error Choi circuit complexity at least half the number of active harmonic edges throughout every laboratory-time shell.

## Goal

Replace the existing operator-norm laboratory ramp by a Choi trace-distance ramp.  The late plateau
and complete-circuit first-reentry laws already use this metric, so this theorem removes the metric
mismatch that prevented a literal same-draw growth--plateau--first-recurrence composition.

## Gates

- [x] 0 → 1 in-progress: exact matching model, active-shell mechanism, and circuit-cut passport
- [x] 1 → 2 fully-proven: dependency-closed proof below, `[PROVED HERE]`
- [ ] 2 → 3 formalized: Lean theorem and targeted module audit
- [ ] 3 → 4 publication-ready: external novelty audit and composition into master paper

## Statement

Let the qubits be the endpoints of `L` disjoint pairs, indexed by `j=0,...,L-1`, and put

\[
  H_L=\sum_{j=0}^{L-1}\frac{1}{j+1}\,|11\rangle\!\langle11|_j,
  \qquad U_L(t)=e^{-itH_L}.
\]

Let `C` be any circuit of one- and two-qubit gates, and let `g_2(C)` count its two-qubit gates.
Write `d_\mathrm{Choi}` for trace distance between normalized pure Choi states.  Define

\[
  \varepsilon_*=\sqrt{\frac{1-2^{-1/2}}2}.
\]

For every `K>=1`, `2K<=L`, and `pi K <= t < pi(K+1)`, the following implication holds:

\[
  d_\mathrm{Choi}(C,U_L(t))<\varepsilon_*
  \quad\Longrightarrow\quad K\le 2g_2(C).
\]

Consequently fixed-error Choi circuit complexity is at least `ceil(K/2)`, uniformly on the whole
time shell.  In particular it grows linearly in laboratory time while `2 floor(t/pi)<=L`.

## Proof `[PROVED HERE]`

### 1. A full active harmonic block

Put `K=floor(t/pi)`.  On the `K` pairs whose one-based indices satisfy
`K+1 <= j+1 <= 2K`, the controlled-phase angle is

\[
  \phi_j=\frac{t}{j+1}\in[\pi/2,\pi).
\]

Indeed `t>=pi K` and `j+1<=2K` give the lower bound; `t<pi(K+1)` and
`j+1>=K+1` give the upper bound.

### 2. One active pair is untouched below half-block cost

Each two-qubit gate touches endpoints in at most two matching pairs.  One-qubit gates touch no pair
for cut-crossing purposes.  Hence the set of pair labels touched by a circuit has cardinality at
most `2g_2(C)`.  If `2g_2(C)<K`, one active pair `j` is untouched.

Across the cut consisting of the first endpoint of that pair versus all remaining qubits, every
gate, and therefore the complete circuit matrix `W`, factorizes.  Thus

\[
  W=W_A\otimes W_B

\]

up to the canonical configuration reindexing.  No assumption about the individual factors is used;
unitarity of their product supplies the required normalization.

### 3. Sharp product-overlap bound for one controlled phase

Let `D=2N` be the Hilbert-space dimension, with the selected endpoint contributing the factor `2`.
The target diagonal phases can be written

\[
  u_0(y)=r(y),\qquad u_1(y)=r(y)e^{-i\phi b(y)},
\]

where `b(y)` is the mate bit and `|r(y)|=1`.  Exactly `N/2` off-configurations have each mate-bit
value.  Write `alpha_a=(W_A)_{aa}`, `beta_y=(W_B)_{yy}` and
`S_a=sum_y conjugate(beta_y)u_a(y)`.  Then

\[
  \operatorname{tr}(W^*U)=\overline{\alpha_0}S_0+\overline{\alpha_1}S_1.
\]

Cauchy--Schwarz in the endpoint coordinate gives

\[
 |\operatorname{tr}(W^*U)|^2
 \le (|\alpha_0|^2+|\alpha_1|^2)(|S_0|^2+|S_1|^2).
\]

The Gram matrix of `u_0,u_1` is

\[
 N\begin{pmatrix}
 1 & e^{-i\phi/2}\cos(\phi/2)\\
 e^{i\phi/2}\cos(\phi/2)&1
 \end{pmatrix},
\]

whose largest eigenvalue is `N(1+|cos(phi/2)|)`.  Therefore

\[
 |S_0|^2+|S_1|^2
 \le N(1+|\cos(\phi/2)|)\sum_y|\beta_y|^2.
\]

The product of the two diagonal squared norms is at most the full Hilbert--Schmidt squared norm of
`W_A tensor W_B=W`.  Since `W` is unitary this norm is `D`.  Combining the bounds and using `D=2N`
gives the sharp estimate

\[
 \frac{|\operatorname{tr}(W^*U)|^2}{D^2}
 \le \frac{1+|\cos(\phi/2)|}{2}.
\]

For `phi in [pi/2,pi]`, `|cos(phi/2)|<=1/sqrt(2)`.  The pure-Choi trace-distance identity now yields

\[
 d_\mathrm{Choi}(W,U)^2
 =1-\frac{|\operatorname{tr}(W^*U)|^2}{D^2}
 \ge \frac{1-2^{-1/2}}2=\varepsilon_*^2.
\]

Thus every circuit with `2g_2(C)<K` is at Choi distance at least `epsilon_*`, proving the
contrapositive of the theorem.

### 4. Robust same-draw neighbourhood

For any finite laboratory horizon `T`, Duhamel's inequality gives
`||exp(-itH)-exp(-itH_L)||_op <= |t| ||H-H_L||_op`.  Normalized Choi-vector distance is at most
operator norm, and pure-state trace distance is at most vector distance.  Hence the ramp persists,
with any fixed strict error slack, throughout an operator-norm ball of radius proportional to
`1/T` about `H_L`.  Every nondegenerate product-Gaussian ordinary two-local ensemble assigns this
ball positive probability.  One Hamiltonian is drawn once; the conclusion then holds
simultaneously for all times in the prescribed laboratory shells.

## Scope and frontier

This theorem supplies a genuine linear Choi-metric growth segment and makes later Choi plateau and
complete-set first-reentry results metrically composable.  It does not by itself prove a
high-probability ramp for a typical centered fixed-q ensemble, nor an effective Brown-scale plateau
onset.  Those remain the quantitative frontier.

## Log

- 2026-08-22 — conjecture survived cut-count, Schmidt-spectrum, robustness, and metric audits;
  dependency-closed paper proof completed.
