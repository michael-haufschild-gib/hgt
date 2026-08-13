# Markovian return recovery and complexity reflection law

- **ID:** `markovian-return-recovery-complexity-reflection-law`
- **Stage:** 2 -- fully proved on paper
- **Type:** theorem / open-system recurrence rigidity / robust circuit incidence
- **Parent:** `autonomous-return-complexity-reflection-law.md`
- **Status:** `[PAPER-PROVED] [FRONTIER ADVANCE] [CLASSICAL CORE] [EXTERNAL PRIORITY OPEN] [LEAN DEFERRED]`
- **Date:** 2026-08-13

## Public sentence

A full autonomous Markovian quantum channel cannot return without refunding every earlier loss.
An approximate full-channel return supplies an explicit recovery channel at every intermediate time
and reflects every unitary-circuit complexity shell across the return.  An exact return forces the
entire semigroup to be unitary: genuine dissipation and exact full-channel recurrence are mutually
exclusive.

## Setup

Let `K=C^D`, and let `(Lambda_t)_(t>=0)` be a quantum dynamical semigroup on `End(K)`:

\[
 \Lambda_0=\operatorname{id},
 \qquad
 \Lambda_{s+t}=\Lambda_s\circ\Lambda_t,
 \tag{1}
\]

where every `Lambda_t` is completely positive and trace preserving.  Continuity is not needed for
the quantitative statements below.

Use unhalved diamond distance

\[
 d_\diamond(\Phi,\Psi)=\|\Phi-\Psi\|_\diamond.             \tag{2}
\]

Fix a proposed full-channel return time `R>0` and define

\[
 \delta_R=d_\diamond(\Lambda_R,\operatorname{id}).         \tag{3}
\]

Let `G` be a finite inverse-closed dictionary of unitary channels.  For a word `w`, write
`mathcal W_w` for its unitary channel and define

\[
 C_\epsilon^\diamond(\Phi)
 =\min\{|w|:d_\diamond(\mathcal W_w,\Phi)\le\epsilon\}.     \tag{4}
\]

For each exact length `ell`, define normalized circuit incidence

\[
 I_{\ell,\epsilon}^\diamond(\Phi)
 ={1\over |G|^\ell}
 \left|\{w\in G^\ell:
 d_\diamond(\mathcal W_w,\Phi)\le\epsilon\}\right|.       \tag{5}
\]

## Theorem A -- every intermediate channel has the return segment as a recovery

For every `0<=t<=R`,

\[
 \boxed{
 \Lambda_{R-t}\circ\Lambda_t
 =\Lambda_t\circ\Lambda_{R-t}=\Lambda_R,}                 \tag{6}
\]

and hence

\[
 \boxed{
 \|\Lambda_{R-t}\circ\Lambda_t-\operatorname{id}\|_\diamond
 =\delta_R.}                                               \tag{7}
\]

Thus `Lambda_(R-t)` is one explicit `delta_R`-recovery channel for `Lambda_t`, simultaneously at
every intermediate time.

Moreover, for every operator `X` on `K` tensored with an arbitrary ancilla,

\[
 \boxed{
 \|(\Lambda_t\otimes\operatorname{id})(X)\|_1
 \ge (1-\delta_R)\|X\|_1.}                               \tag{8}
\]

In particular, an approximate full-channel return permits at most `delta_R` relative loss of any
ancilla-assisted trace-distance distinguishability anywhere in the return cycle.

### Proof

Equation (6) is the semigroup law.  Equation (7) is (3).  Complete positivity and trace
preservation make `Lambda_(R-t)` completely contractive in trace norm, so

\[
 \|(\Lambda_t\otimes\operatorname{id})(X)\|_1
 \ge\|(\Lambda_R\otimes\operatorname{id})(X)\|_1.
\]

The reverse triangle inequality and (3) give

\[
 \|(\Lambda_R\otimes\operatorname{id})(X)\|_1
 \ge\|X\|_1-
 \|((\Lambda_R-\operatorname{id})\otimes\operatorname{id})(X)\|_1
 \ge(1-\delta_R)\|X\|_1.
\]

This proves (8).  QED.

## Theorem B -- robust circuit-complexity reflection for open dynamics

For every `0<=t<=R` and every `epsilon>=0`,

\[
 \boxed{
 C_{\epsilon+\delta_R}^\diamond(\Lambda_{R-t})
 \le C_\epsilon^\diamond(\Lambda_t),
 \qquad
 C_{\epsilon+\delta_R}^\diamond(\Lambda_t)
 \le C_\epsilon^\diamond(\Lambda_{R-t}).}                \tag{9}
\]

At every exact word length,

\[
 \boxed{
 I_{\ell,\epsilon}^\diamond(\Lambda_t)
 \le I_{\ell,\epsilon+\delta_R}^\diamond(\Lambda_{R-t}),
 \qquad
 I_{\ell,\epsilon}^\diamond(\Lambda_{R-t})
 \le I_{\ell,\epsilon+\delta_R}^\diamond(\Lambda_t).}  \tag{10}
\]

Therefore every nonnegative length partition function

\[
 Z_{b,\epsilon}^\diamond(\Phi)
 =\sum_{\ell\ge0}b_\ell I_{\ell,\epsilon}^\diamond(\Phi) \tag{11}
\]

obeys the same two radius-interlacing inequalities.  This includes the geometric Abel profile
`b_ell=a^ell`.

### Proof

Suppose a unitary word channel `mathcal W` satisfies

\[
 \|\mathcal W-\Lambda_t\|_\diamond\le\epsilon.
\]

Composition by a channel is diamond-contracting, so (6) gives

\[
 \begin{aligned}
 \|\Lambda_{R-t}\circ\mathcal W-\operatorname{id}\|_\diamond
 &\le
 \|\Lambda_{R-t}\circ\mathcal W-
   \Lambda_{R-t}\circ\Lambda_t\|_\diamond
 +\|\Lambda_R-\operatorname{id}\|_\diamond\\
 &\le\epsilon+\delta_R.                                  \tag{12}
 \end{aligned}
\]

Postcomposition by the inverse unitary channel is a diamond isometry.  Applying it to both maps in
(12) yields

\[
 \|\Lambda_{R-t}-\mathcal W^{-1}\|_\diamond
 \le\epsilon+\delta_R.                                  \tag{13}
\]

Word inversion is a length-preserving bijection because the dictionary is inverse closed.  Thus
every word counted near `Lambda_t` injects, by inversion, into the enlarged shell near
`Lambda_(R-t)`.  This proves the first inequalities in (9)--(10).  Interchange `t` and `R-t` for
the second inequalities.  Nonnegative summation proves the partition-function statement.  QED.

## Corollary C -- exact Markovian recurrence is unitary and palindromic

If `delta_R=0`, then for every `0<=t<=R`, `Lambda_(R-t)` is a CPTP two-sided inverse of `Lambda_t`.
A finite-dimensional CPTP automorphism with a CPTP inverse is a unitary conjugation.  Consequently,
for every `t` there is a unitary `U_t`, unique up to phase, such that

\[
 \Lambda_t(X)=U_tXU_t^*,
 \qquad
 \Lambda_{t+R}=\Lambda_t.                                 \tag{14}
\]

Thus the channels themselves form a periodic one-parameter group of unitary conjugations.  Under
the standard continuity premise for a quantum dynamical semigroup, their projective unitary
representatives have the usual continuous Hamiltonian lift.

Equations (9)--(11) become exact equalities under `t mapsto R-t`.  Hence no genuinely dissipative
finite-dimensional quantum dynamical semigroup has a nonzero exact recurrence of the full channel.

The classification of CPTP maps with positive/CPTP inverse as unitary channels is classical.  The
new candidate composition is the simultaneous recovery law (7)--(8) with shellwise robust circuit
reflection (9)--(11); priority remains open.

## Conjecture--failure--proof loop

### C0 -- an open Markovian channel can dissipate and later exactly recur

Label: `[FALSIFIED]` by Corollary C.

Exact return makes every earlier segment CPTP-invertible by the remaining segment.  The semigroup
is unitary on the full channel space.

### C1 -- approximate recurrence constrains only the endpoint

Label: `[FALSIFIED]` by Theorem A.

The remaining physical evolution is a uniform recovery map at every intermediate time, and (8)
forbids larger distinguishability loss anywhere in the cycle.

### C2 -- open dynamics destroys recurrence reflection of complexity

Label: `[FALSIFIED FOR UNITARY-CIRCUIT COST]` by Theorem B.

The intermediate channels need not themselves be assumed unitary.  Semigroup composition,
contractivity, and inverse words suffice for robust reflection.

### C3 -- Markovian recurrence reflection proves Brown growth

Label: `[FALSIFIED]`.

The law transfers whatever complexity is present between the two sides of a return.  It neither
forces first-cut growth nor supplies a recurrence time.

## Hostile audit

1. **Unconditional scope:** every finite-dimensional CPTP semigroup, every full-channel diamond
   return defect, every inverse-closed unitary gate dictionary.
2. **No hidden reversibility premise:** approximate Theorems A--B do not assume any `Lambda_t` is
   unitary or invertible.
3. **Full-channel qualification is load-bearing:** recurrence of one stationary state does not make
   an open channel reversible.  The norm in (3) quantifies recurrence of the entire channel.
4. **Markovian qualification is load-bearing:** non-Markovian dynamics can lose information to an
   environment and later receive it back; the system maps need not form a CPTP semigroup.
5. **No Brown ramp:** first-cut undistortion for ordinary static local Hamiltonians is unchanged.
6. **Novelty:** CPTP-inverse rigidity and reversible/decoherence-free semigroup structure are
   classical.  Targeted searches did not locate the quantitative all-intermediate recovery plus
   shellwise circuit-reflection package.  This is separation evidence only, not priority proof.
7. **Physics meaning:** an observed full-channel recurrence distinguishes reversible memory from
   Markovian dissipation.  No black-hole, gravity, or thermodynamic-limit claim is made.

## External boundary

- Nayak and Sen, *Invertible Quantum Operations and Perfect Encryption of Quantum States*
  (`quant-ph/0605041`), characterize quantum operations with quantum-operation inverses.  This is
  the classical input behind Corollary C.
- Quantum-dynamical-semigroup/decoherence theory classically splits reversible and stable sectors.
  The present theorem does not claim that decomposition as new.
- Research on non-Markovian information backflow concerns families outside the semigroup premise;
  it is not contradicted by Corollary C.

## Formalization status

Lean is deliberately deferred during the shared corpus refactor.  No Lean process was started.
Later formalization should separate abstract contractive semigroup recovery, diamond-norm channel
composition, inverse-word shell injection, and the imported finite-dimensional CPTP-inverse
classification.
