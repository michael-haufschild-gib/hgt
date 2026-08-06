# Direct-net adaptive static-Choi shortcut action law

- **ID:** `direct-net-adaptive-static-choi-shortcut-action-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / finite-window adaptive shortcut law
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../3-formalized/adaptive-static-choi-circuit-shortcut-action-law.md`
- **Date:** 2026-08-06

## Exact result

Let `d >= 1`, let `E : Fin d -> R`, and put

\[
 \Phi_E(t)=d^{-1/2}\sum_{i=1}^{d}e^{-itE_i}|i,i\rangle .
\]

Let `Delta` be trace distance between normalized pure states.  Fix a replica
order `r >= 1`, a time scale `T>0`, and define the intrinsic replica action
resolution

\[
 \delta_r(E)=\min\!\left(\{1\}\cup
 \left\{\left|\sum_i(p_i-q_i)E_i\right|:
  |p|=|q|=r,\ \sum_i(p_i-q_i)E_i\ne0\right\}\right)>0.       \tag{1}
\]

Assume only maximal projective spectral rank:

\[
 \sum_i k_i=0,\qquad \sum_i k_iE_i=0,\qquad k_i\in\mathbb Z
 \quad\Longrightarrow\quad k=0.                             \tag{2}
\]

Let `W` be any finite family of arbitrary normalized target states in the
full `d^2`-dimensional Choi Hilbert space.  For `0 <= epsilon < 1`, if `X` is
a standard real Gaussian, then

\[
 \boxed{
 (1-\epsilon^2)^r
 \Pr_X\{\exists w\in W:\Delta(\Phi_E(TX),\phi_w)\le\epsilon\}
 \le |W|\left[r!\,d^{-r}
 +\exp\!\left(-\frac{(T\delta_r(E))^2}{2}\right)\right].
 }                                                           \tag{3}
\]

For uniform time on `[-T,T]`,

\[
 \boxed{
 (1-\epsilon^2)^r {1\over2T}\operatorname{Leb}
 \{t\in[-T,T]:\exists w\in W:\Delta(\Phi_E(t),\phi_w)\le\epsilon\}
 \le |W|\left[r!\,d^{-r}
 +\min\{1,(T\delta_r(E))^{-1}\}\right].
 }                                                           \tag{4}
\]

The finite dictionary can resolve an arbitrary, even uncountable, adaptive
target class.  Let `C` be any type of normalized targets, let `sigma` choose
one target after observing time, and let `A` be a measurable success event.
Suppose maps `a : C -> W` and normalized net targets `phi_w` obey

\[
 \Delta(\psi_c,\phi_{a(c)})\le\eta\qquad(c\in C).             \tag{5}
\]

If on `A` the selected target is captured at radius `epsilon`, then, for
`epsilon+eta<1`, equations (3) and (4) hold with the left event replaced by
`A` and `epsilon` replaced by `epsilon+eta`.  No measurability, independence,
computability, or finite-range condition is imposed on `sigma`.  Thus the
law charges an infinite adaptive circuit family by its finite metric entropy,
not by an invalid union over its elements.

## Proof

### 1. Direct target overlap

Fix one normalized target `phi`.  Write

\[
 c_i=\langle i,i|\phi\rangle,\qquad a_i={|c_i|\over\sqrt d}.
\]

The physical overlap is the exponential polynomial

\[
 b_\phi(t)=\langle\Phi_E(t),\phi\rangle
 =\sum_i {c_i\over\sqrt d}e^{itE_i}.                         \tag{6}
\]

The diagonal projection of a unit vector has squared norm at most one, so

\[
 \sum_i a_i^2={1\over d}\sum_i|c_i|^2\le {1\over d}.         \tag{7}
\]

Cauchy--Schwarz also gives

\[
 \sum_i a_i\le {1\over\sqrt d}\sqrt{d\sum_i|c_i|^2}\le1.   \tag{8}
\]

For normalized pure states,

\[
 \Delta(\Phi_E(t),\phi)^2=1-|b_\phi(t)|^2.
\]

Consequently capture at any `epsilon<1` implies

\[
 |b_\phi(t)|\ge\sqrt{1-\epsilon^2}.                          \tag{9}
\]

This direct implication replaces the earlier orbit-anchor triangle step.
There is no factor `4` and no restriction `epsilon<1/2`.

### 2. Exact replica action

For multiplicity vectors `p,q : Fin d -> N` with `|p|=|q|=r`, expanding the
`2r`-th overlap moment gives coefficients of absolute value

\[
 M_r(p)M_r(q)\prod_i a_i^{p_i+q_i},                          \tag{10}
\]

where `M_r(p)=r!/prod_i p_i!`.  Their total sum is

\[
 \left(\sum_i a_i\right)^{2r}\le1.                          \tag{11}
\]

Gaussian averaging multiplies the `(p,q)` term by

\[
 \exp\!\left[-{T^2\over2}
   \left(\sum_i(p_i-q_i)E_i\right)^2\right].                \tag{12}
\]

Uniform averaging multiplies it by the corresponding sinc reporter.  Split
the expansion into zero and nonzero actions.  Equation (1), (11), and the
triangle inequality give

\[
 \mathbb E_X|b_\phi(TX)|^{2r}\le Z_{r,\phi}
 +e^{-(T\delta_r(E))^2/2},                                  \tag{13}
\]

and

\[
 {1\over2T}\int_{-T}^{T}|b_\phi(t)|^{2r}\,dt\le Z_{r,\phi}
 +\min\{1,(T\delta_r(E))^{-1}\}.                            \tag{14}
\]

Here `Z_(r,phi)` is the absolute mass of the zero-action terms.

### 3. Uniform full-target collision floor

By (2), zero action with `|p|=|q|` forces `p=q`.  Hence

\[
 Z_{r,\phi}=\sum_{|p|=r}M_r(p)^2\prod_i a_i^{2p_i}.          \tag{15}
\]

Since `M_r(p)<=r!`, the multinomial theorem and (7) give

\[
 \begin{aligned}
 Z_{r,\phi}
 &\le r!\sum_{|p|=r}M_r(p)\prod_i(a_i^2)^{p_i}\\
 &=r!\left(\sum_i a_i^2\right)^r\\
 &\le r!d^{-r}.                                             \tag{16}
 \end{aligned}
\]

This bound is uniform over every normalized target in the full Choi space;
off-diagonal target mass can only reduce the collision floor.

### 4. Threshold amplification and finite adaptive union

On a capture event, (9) yields

\[
 (1-\epsilon^2)^r\le |b_\phi(t)|^{2r}.
\]

Markov's integral inequality, followed by (13) or (14) and (16), proves the
one-target estimate.  Finite subadditivity over `W` proves (3) and (4).  A
selector that inspects time has success event contained in this same finite
union, so it pays no further adaptive factor.

### 5. Infinite adaptive class through a net

For `t in A`, the pure-state trace-distance triangle inequality and (5) give

\[
 \Delta(\Phi_E(t),\phi_{a(\sigma(t))})\le\epsilon+\eta.      \tag{17}
\]

Thus `A` is contained in the finite union of radius-`epsilon+eta` balls around
the net targets.  Apply (3) or (4).  The argument uses no regularity of the
selector because only the measurable subset `A` is measured.

## Strict improvement over the anchor law

The formalized anchor law uses `sqrt(1-4 epsilon^2)`, requires
`epsilon<1/2`, and exposes the survival-distribution collision mass.  The
direct law instead uses `sqrt(1-epsilon^2)`, works for every
`epsilon<1`, and for static Choi trajectories bounds every arbitrary full
target by `r! d^(-r)`.  Its net form also covers infinite and continuous gate
families.

## Hostile audit

1. Equations (3)--(4) are time-window laws.  They do not prove monotone
   Brown--Susskind growth from time zero or a lower bound at one prescribed
   deterministic time.
2. The intrinsic action resolution can be extremely small at growing replica
   order.  The theorem exposes that cost; it does not bound it uniformly in
   system size.
3. Infinite target classes are charged by an explicitly supplied finite net.
   A useful circuit corollary still needs a proved covering-number bound for
   the chosen continuous gate model.
4. Maximal projective rank is used only to eliminate nonpermutation replica
   collisions.  Without it, (13)--(14) remain true with the exact targetwise
   zero-action mass in place of `r! d^(-r)`.
5. This theorem is a stronger shortcut/plateau bridge, not the unresolved
   fixed-time quenched coefficient-space anti-concentration theorem.
6. No novelty claim is authorized before an external priority audit.  The
   proof ingredients are classical; potential value is their direct-target,
   finite-action, full-Choi, adaptive-net synthesis.

## Lean certificate

- **Subprobability module:**
  `GaloisForLFunctions.HTGeometry.SubprobabilityPhaseTwistedReplicaShortcutActionLaw`
- **Operational module:**
  `GaloisForLFunctions.RHTower.DirectAdaptiveStaticChoiShortcutActionLaw`
- **Finite Gaussian capstone:**
  `gaussian_directAdaptiveStaticChoiTargetShortcut_probability_le`
- **Finite uniform capstone:**
  `uniform_directAdaptiveStaticChoiTargetShortcut_probability_le`
- **Infinite-selector Gaussian capstone:**
  `gaussian_directAdaptiveNetStaticChoiShortcut_probability_le`
- **Infinite-selector uniform capstone:**
  `uniform_directAdaptiveNetStaticChoiShortcut_probability_le`
- **Padded-circuit capstones:**
  `gaussian_directAdaptivePaddedCircuitShortcut_probability_le`,
  `uniform_directAdaptivePaddedCircuitShortcut_probability_le`
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Wiring:** imported by both `GaloisForLFunctions.HTGeometry` and
  `GaloisForLFunctions.RHTower`

## Log

- 2026-08-06 — Direct-target conjecture survived anchor, zero-coordinate,
  resonance, full-space, and adaptive-selector attacks; dependency-closed
  paper proof completed.
- 2026-08-06 — Subprobability replica action, direct full-Choi collision
  floor, finite adaptive dictionary, and arbitrary-selector finite-net laws
  formalized; capstone axioms audited.
