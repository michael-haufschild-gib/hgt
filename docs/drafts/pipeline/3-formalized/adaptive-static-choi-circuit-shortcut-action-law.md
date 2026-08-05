# Adaptive static-Choi circuit-shortcut action law

- **ID:** `adaptive-static-choi-circuit-shortcut-action-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM / OPERATIONAL CHANNEL-COMPLEXITY BRIDGE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/static-local-complexity-law.md`
- **Spectral input:** `../3-formalized/adaptive-circuit-shortcut-action-law.md`
- **Date:** 2026-08-05

## Exact theorem

Let (I) be a nonempty finite set of size (D), let (E_i\in\mathbb R),
and define the normalized static-Hamiltonian Choi orbit in
(\mathbb C^{I\times I}) by

\[
 \Omega_E(t)=D^{-1/2}\sum_{i\in I}e^{itE_i}|i,i\rangle .        \tag{1}
\]

Let (\mathcal A) be any finite family of normalized target states in the
full (D^2)-dimensional Choi Hilbert space. Targets need not lie in the
diagonal spectral subspace and may depend on the Hamiltonian. Fix
(0\leq\epsilon<1/2), replica order (r\geq1), and put

\[
 u_\epsilon^2=1-4\epsilon^2.                              \tag{2}
\]

For the uniform spectral weights (p_i=D^{-1}), let
(Z_r(E)) be the exact order-(r) replica collision mass and let

\[
 \delta_r(E)=\min\bigl(\{1\}\cup
   \{|\Delta_{a,b}|:\Delta_{a,b}\ne0\}\bigr)>0             \tag{3}
\]

be the intrinsic replica-action resolution.

For (X\sim N(0,1)) and (T>0),

\[
 \boxed{
 \Pr\{\exists\phi\in\mathcal A:
   d_{\rm tr}([\Omega_E(TX)],[\phi])\le\epsilon\}
 \le
 |\mathcal A|u_\epsilon^{-2r}
 \left[Z_r(E)+e^{-T^2\delta_r(E)^2/2}\right].
 }                                                        \tag{4}
\]

For time uniform on the centered interval, equivalently normalized
Lebesgue measure on ((-T,T]),

\[
 \boxed{
 \Pr\{\exists\phi\in\mathcal A:
   d_{\rm tr}([\Omega_E(t)],[\phi])\le\epsilon\}
 \le
 |\mathcal A|u_\epsilon^{-2r}
 \left[Z_r(E)+\min\{1,(T\delta_r(E))^{-1}\}\right].
 }                                                        \tag{5}
\]

The target may be chosen after observing time. There is no selector penalty
beyond the complete dictionary cardinality.

For padded words of length (s+1) over a finite gate alphabet (G),
(|\mathcal A|=|G|^{s+1}) exactly. If the spectrum has maximal projective
rational rank, then

\[
 Z_r(E)=B_r(D):=
 \sum_{|a|=r}{r\choose a}^{\!2}D^{-2r},                  \tag{6}
\]

the unavoidable uniform permutation floor.

## Dependency-closed proof

### 1. Choi normalization and pair overlap

Orthogonality of the diagonal basis gives

\[
 \|\Omega_E(t)\|^2=D^{-1}\sum_i1=1.                    \tag{7}
\]

For all (t,t_0\),

\[
 \langle\Omega_E(t_0),\Omega_E(t)\rangle
 =D^{-1}\sum_i e^{-it_0E_i}e^{itE_i}.                  \tag{8}
\]

Thus, with (y_i=e^{-it_0E_i}), the pair overlap is exactly the
phase-twisted microcanonical spectral amplitude. Every (y_i) has modulus
one.

### 2. An arbitrary full-space target reduces to one anchor phase

Fix (\phi\in\mathcal A). If its capture set is empty there is nothing to
bound. Otherwise choose one captured time (t_0). For every other captured
time (t), the triangle inequality for normalized pure-state trace distance
gives

\[
 d_{\rm tr}([\Omega_E(t)],[\Omega_E(t_0)])\le2\epsilon. \tag{9}
\]

The pure-state identity

\[
 d_{\rm tr}([v],[w])^2=1-|\langle v,w\rangle|^2          \tag{10}
\]

then yields

\[
 u_\epsilon\le
 \left|D^{-1}\sum_i y_i e^{itE_i}\right|.              \tag{11}
\]

This step never projects (\phi). Hence targets are arbitrary states in the
full Choi Hilbert space, not only diagonal phase states.

### 3. Replica action and adaptive union

Raise `(11)` to power (2r). The phase-twisted replica expansion has
nonnegative bivariate multinomial coefficients totaling one. Its zero-action
terms have mass (Z_r(E)). Every nonzero action is at least
(\delta_r(E)) in absolute value.

The Gaussian characteristic function bounds nonzero terms by
(e^{-T^2\delta_r(E)^2/2}); the symmetric uniform kernel bounds them by
(\min\{1,(T\delta_r(E))^{-1}\}). Markov's integral inequality proves the
one-target forms. Finite subadditivity over all target labels proves `(4)`
and `(5)`, including every selector whose range lies in (\mathcal A).

### 4. Circuit and maximal-projective specializations

Padded circuit words are functions from (s+1) positions to (G), hence
their cardinality is (|G|^{s+1}). Maximal projective rational rank makes
every balanced zero-action character trivial. Therefore the zero-action
sector consists exactly of equal multiplicity packets and equals `(6)`.

This proves every statement above. □

## Hostile audit

1. This is an operational full-Choi theorem; no target-subspace restriction
   is hidden.
2. Adaptivity is complete only for a finite target dictionary. Adjustable
   continuous gates require a separately controlled net.
3. The theorem is a finite-window probability law, not pointwise monotone
   complexity growth.
4. Intrinsic resolution can be arbitrarily small. Maximal projective rank
   proves positivity, not a uniform many-body lower bound.
5. The microcanonical weight is physically forced by the normalized Choi
   state. This does not prove the corresponding law for a fixed easy product
   state in the original system.
6. The theorem can prove long-time circuit-hard Choi plateaux once the
   permutation floor beats circuit entropy. It does not prove the
   Brown--Susskind linear-growth onset or its exponential finite-size scale.
7. The result is a missing rigorous bridge between existing spectral action
   and channel complexity. No standalone novelty claim is made.

## Formal artifact

Module:
`formal/GaloisForLFunctions/RHTower/AdaptiveStaticChoiCircuitShortcutActionLaw.lean`.

It formalizes `(7)`--`(11)`, arbitrary-target uniform and Gaussian action and
probability laws, exact padded-circuit entropy, and maximal-projective
permutation-floor forms. It reuses the static spectral Choi vector,
pure-state trace distance, intrinsic replica action, and phase-twisted
adaptive-union modules.
