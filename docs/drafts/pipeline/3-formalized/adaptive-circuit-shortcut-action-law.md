# Adaptive circuit-shortcut action law

- **ID:** `adaptive-circuit-shortcut-action-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / universal finite-window shortcut law
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/observer-spectral-shortcut-action-law.md`
- **Date:** 2026-08-05

## Result

Let `I` be a nonempty finite set, let `p_i>=0` with `sum_i p_i=1`,
and let `E_i` be arbitrary real energies.  In an orthonormal family `(e_i)`,
put

\[
 \Psi(t)=\sum_{i\in I}\sqrt{p_i}\,e^{-itE_i}e_i .       \tag{1}
\]

The weights may vanish, the spectrum may be degenerate or resonant, and no
genericity, chaos, locality, random-matrix or eigenvector assumption is made.

Fix `0<epsilon<1/2`, a finite dictionary `A` of arbitrary unit target states,
and a replica order `r>=1`.  Write

\[
 u_\epsilon^2=1-4\epsilon^2.                           \tag{2}
\]

For multiplicity vectors `a,b:I->N` with total mass `r`, define

\[
 \Delta_{a,b}=\sum_i(a_i-b_i)E_i                       \tag{3}
\]

and let `w_(a,b)>=0` be the exact bivariate multinomial weight in the
`r`th power of the survival fidelity with spectral weights `p`.  Thus

\[
 \sum_{a,b}w_{a,b}=1.                                  \tag{4}
\]

Define the absolute completed replica collision mass

\[
 Z_r(p,E)=\sum_{\Delta_{a,b}=0}w_{a,b}                 \tag{5}
\]

and the intrinsic positive action resolution

\[
 \delta_r(E)=\min\bigl(\{1\}\cup
   \{|\Delta_{a,b}|:\Delta_{a,b}\ne0\}\bigr)>0.      \tag{6}
\]

If `tau` is uniform on `[-T,T]`, `T>0`, then

\[
 \boxed{
 \Pr_\tau\{\exists\phi\in A:\
       d_{\rm tr}([\Psi(\tau)],[\phi])\le\epsilon\}
 \le
 |A|\,u_\epsilon^{-2r}
 \left[Z_r(p,E)+\min\{1,(T\delta_r(E))^{-1}\}\right].
 }                                                       \tag{7}
\]

If instead `tau=T X` for a standard real Gaussian `X`, then the sharper
Gaussian-window law is

\[
 \boxed{
 \Pr_X\{\exists\phi\in A:\
       d_{\rm tr}([\Psi(TX)],[\phi])\le\epsilon\}
 \le
 |A|\,u_\epsilon^{-2r}
 \left[Z_r(p,E)+e^{-T^2\delta_r(E)^2/2}\right].
 }                                                       \tag{8}
\]

The target in `(7)` or `(8)` may be selected after observing the time.  The
selector is not fixed, computable or independent of the Hamiltonian: its
complete finite range is already inside the single event.

For a finite gate alphabet with at most `M>=2` labelled choices per padded
circuit step, the outputs of all words of length at most `s` form a dictionary
of size at most `M^(s+1)`.  Therefore

\[
 \Pr\{C_\epsilon(\Psi(\tau))\le s\}
 \le
 M^{s+1}u_\epsilon^{-2r}
 \left[Z_r(p,E)+\mathcal R_r(T,E)\right],              \tag{9}
\]

where `R_r=min{1,(T delta_r)^(-1)}` for a uniform window and
`R_r=exp(-T^2 delta_r^2/2)` for a Gaussian window.

If the energy family has maximal projective rational rank, zero action forces
`a=b`, and `(5)` becomes the exact permutation floor

\[
 Z_r(p,E)=B_r(p)=\sum_a w_{a,a}.                       \tag{10}
\]

Thus `(9)` has exactly three prices: circuit description entropy, completed
spectral collision, and unresolved finite-window spectral action.  There is
no fourth adaptive-selector term.

## Proof

### 1. One arbitrary target reduces to one phase-coherence packet

Fix `phi in A`.  If its `epsilon`-capture set is empty, its contribution is
zero.  Otherwise choose one captured time `t_0` and put
`y_i=exp(-i t_0 E_i)`.  For every other captured time `t`, the triangle
inequality for pure-state trace distance gives

\[
 d_{\rm tr}([\Psi(t)],[\Psi(t_0)])\le2\epsilon.
\]

The pure-state identity

\[
 d_{\rm tr}([v],[w])^2=1-|\langle v,w\rangle|^2
\]

and orthonormality in `(1)` therefore give

\[
 \left|\sum_i p_i e^{-itE_i}\overline{y_i}\right|^2
 \ge1-4\epsilon^2=u_\epsilon^2.                      \tag{11}
\]

This witness phase may depend on the target and on the Hamiltonian.  Every
bound below is uniform in all unit phases `y_i`.

### 2. Replica amplification retains all target labels

Raise `(11)` to the `r`th power.  Markov's elementary integral inequality
gives

\[
 u_\epsilon^{2r}\Pr\{\phi\text{ captures }\Psi(\tau)\}
 \le
 \mathbb E_\tau
 \left|\sum_i p_i e^{-i\tau E_i}\overline{y_i}\right|^{2r}.
                                                               \tag{12}
\]

The bivariate multinomial expansion of the right side is

\[
 \sum_{a,b}w_{a,b}
   \left(\prod_i\overline{y_i}^{a_i}y_i^{b_i}\right)
   e^{-i\tau\Delta_{a,b}}.                            \tag{13}
\]

Every phase twist in parentheses has modulus one.  Importantly, labels have
not been scalarized before the positive replica moment was formed.

### 3. Exact finite-window action

For a symmetric uniform window,

\[
 \mathbb E_\tau e^{-i\tau\Delta}=\operatorname{sinc}(T\Delta).
\]

The zero-action terms in `(13)` have total absolute weight `Z_r(p,E)`.  Every
nonzero term has modulus at most

\[
 \min\{1,(T|\Delta|)^{-1}\}
 \le\min\{1,(T\delta_r(E))^{-1}\}.
\]

Their weights total at most one by `(4)`.  Taking absolute values in `(12)`
therefore proves the one-target form of `(7)`.

For `tau=T X`, Gaussian characteristic-function evaluation gives

\[
 \mathbb E_Xe^{-iTX\Delta}=e^{-T^2\Delta^2/2}.
\]

The identical zero/nonzero split proves the one-target form of `(8)`.

### 4. Adaptive circuit union

The event selected by an arbitrary map from observation time to `A` is a
subset of the union of the capture sets of all targets in `A`.  Finite
subadditivity and the target-uniform one-target estimate multiply the bound by
`|A|`.  Padding circuit words gives `|A|<=M^(s+1)` and proves `(9)`.  No
targetwise recurrence exceptional set is introduced.

### 5. Maximal-projective simplification

Both `a` and `b` have total mass `r`, so `a-b` is a balanced integer
character.  Maximal projective rational rank makes `Delta_(a,b)=0` imply
`a=b`.  The phase twist in `(13)` is then one and the zero-action mass is
exactly `(10)`.

## Quenched ensemble corollary

Let `H` be random, allow its spectral weights, energies and finite circuit
dictionary to depend measurably on `H`, and then sample observation time.
Conditioning on `H` and applying `(9)` gives the exact ensemble bound

\[
 \Pr_{H,\tau}\{C_\epsilon(\Psi_H(\tau))\le s\}
 \le M^{s+1}u_\epsilon^{-2r}
 \mathbb E_H[Z_r(p_H,E_H)+\mathcal R_r(T,E_H)].        \tag{14}
\]

For any `zeta,delta>0`, the explicitly resolved version is

\[
 \begin{aligned}
 \Pr_{H,\tau}\{C_\epsilon(\Psi_H(\tau))\le s\}
 &\le
 \Pr_H\{Z_r(p_H,E_H)>\zeta\text{ or }
              \delta_r(E_H)<\delta\}\\
 &\quad+M^{s+1}u_\epsilon^{-2r}
   [\zeta+\mathcal R_r(T,\delta)].                    \tag{15}
 \end{aligned}
\]

This is the required quenched correction.  A gapped easy eigenstate has
concentrated spectral weight and hence large collision mass; a nearly
resonant spectrum has small action resolution.  Neither can disappear inside
an annealed completed-orbit average.

## Hostile audit

1. `(7)--(15)` are window laws, not a lower bound at one prescribed time.
   They prove a finite-window plateau/no-shortcut statement, not monotone
   Brown--Susskind growth from time zero.
2. `delta_r(E)` can be extremely small.  Maximal projective rank proves it is
   positive at each finite size and order; it does not supply a useful
   many-body lower bound.
3. Circuit entropy is paid explicitly.  The law becomes informative only
   when the collision and action terms beat `M^(s+1)`.
4. The dictionary is finite.  Adjustable continuous gates require a separately
   proved circuit net and its approximation-radius loss.
5. The triangle step uses `epsilon<1/2`.  No claim is made at larger error.
6. The theorem is fully adaptive over the finite dictionary and over random
   Hamiltonians, but it does not prove the unresolved fixed-time static seed
   expansion theorem.
7. Moment amplification and union bounds are classical ingredients.  Any
   novelty claim must be based on the exact collision--action--description
   synthesis and a concrete many-body instantiation, not on Markov's
   inequality or the Gaussian characteristic function separately.

## Formal certificate

Formalization is split along the mathematical boundary between spectral
action and operational circuit geometry:

- `formal/GaloisForLFunctions/HTGeometry/PhaseTwistedReplicaShortcutActionLaw.lean`
  proves the phase-twisted replica expansion, uniform and Gaussian action
  kernels, finite adaptive dictionary unions, intrinsic-resolution laws, and
  maximal-projective permutation-floor specializations.
- `formal/GaloisForLFunctions/RHTower/AdaptiveCircuitShortcutActionLaw.lean`
  proves normalization of the spectral orbit, pure-state trace-distance
  triangle reduction, capture-to-anchor coherence, arbitrary adaptive target
  laws, exact padded-circuit entropy, probability-normalized forms `(7)--(9)`,
  and maximal-projective circuit corollaries.

Headline declarations:

- `RHTower.uniform_adaptiveTargetShortcut_probability_le`
- `RHTower.gaussian_adaptiveTargetShortcut_probability_le`
- `RHTower.uniform_adaptivePaddedCircuitShortcut_probability_le`
- `RHTower.gaussian_adaptivePaddedCircuitShortcut_probability_le`
- `RHTower.uniform_adaptivePaddedCircuitShortcut_actionLaw_floor`
- `RHTower.gaussian_adaptivePaddedCircuitShortcut_actionLaw_floor`

No `sorry`, `admit`, new axiom, `opaque`, `unsafe`, numerical computation, or
unproved spectral genericity premise occurs in these modules.
