# Lag-resolved static-Choi shortcut dichotomy law

- **ID:** `lag-resolved-static-choi-shortcut-dichotomy-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** deterministic recurrence/shortcut decomposition
- **Status:** `[LEAN-PROVED] [BRIDGE]`
- **Parent:** `oriented-no-shortcut-without-return-law.md`
- **Date:** 2026-08-07

## Exact claim

Let \(d>0\), let \(\Phi(t)\) be the normalized spectral Choi orbit of an
arbitrary time-independent \(d\)-level Hamiltonian, and put

\[
 C(x,\lambda)=\{t:\lambda\leq |\langle\Phi(t),x\rangle|\}.
\]

For an anchor \(u\), define

\[
 \alpha_u(x)=\langle\Phi(u),x\rangle,
 \qquad
 r_u(x)=x-\alpha_u(x)\Phi(u).                         \tag{1}
\]

For every index type \(W\), normalized target family \(x_w\), anchor map
\(a:W\to\mathbb R\), set \(A\subseteq\mathbb R\) containing every \(a(w)\),
and real thresholds \(\theta,\eta\),

\[
 \boxed{
 \bigcup_{w\in W} C(x_w,\theta)
 \subseteq
 R_A(\eta)\ \cup\
 \bigcup_{w\in W} C(r_{a(w)}(x_w),\theta-\eta), }
                                                               \tag{2}
\]

where

\[
 R_A(\eta)=\{t:\exists u\in A,\
    \eta\leq|\langle\Phi(t),\Phi(u)\rangle|\}.         \tag{3}
\]

The decomposition is genuinely lag resolved:

\[
 |\langle\Phi(t),\Phi(u)\rangle|
   =\left|\frac1d\sum_j e^{i(t-u)E_j}\right|,          \tag{4}
\]

and the transverse residual obeys

\[
 r_u(x)\perp\Phi(u),\qquad
 S_{-u}r_u(x)=r_0(S_{-u}x),                             \tag{5}
\]

where \(S\) is spectral phase translation.  In particular
\(r_u(\Phi(u))=0\): an exact earlier orbit target contributes no transverse
mass.

## Internal frontier

- `[CORPUS]` `iUnion_staticChoiOverlapCaptureSet_subset_scalar_union_traceless_budget`
  in `formal/GaloisForLFunctions/RHTower/ScalarRecurrenceTracelessCircuitSplit.lean`
  proves `(2)` only at the fixed anchor `u=0`.
- `[CORPUS]` `staticChoiPhaseShift_staticSpectralChoiVector` and
  `inner_staticChoiPhaseShift` in
  `formal/GaloisForLFunctions/RHTower/StaticChoiForwardSpectralDimensionLaw.lean`
  provide exact spectral translation.
- `[CORPUS]` `staticChoiTargetCapture_implies_anchorCoherence` in
  `formal/GaloisForLFunctions/RHTower/AdaptiveStaticChoiCircuitShortcutActionLaw.lean`
  selects an anchor from the target's complete capture set.  It does not
  separate a prescribed cheaply reachable past from the transverse shortcut
  channel.
- `[LOCAL-RESEARCH]` Static Krylov carrier load was falsified for this role:
  its norm forgets target time and remains large on an easy past target at
  every later horizon.

## External frontier and hostile verdict

- `[LITERATURE]` Brown--Susskind predicts linear growth, a maximal plateau,
  and doubly exponential recurrence for autonomous chaotic dynamics.
- `[LITERATURE]` rigorous saturation/recurrence results cover random circuits
  and stochastic local-Hamiltonian evolution, not one ordinary fixed random
  local Hamiltonian.
- `[LITERATURE]` no-fast-forwarding lower bounds are worst-case simulation
  statements; they do not classify every late short circuit as a return to a
  cheaply reachable past.

Verdict on novelty of `(1)--(5)`: **`BRIDGE`**.  The algebra is orthogonal
projection plus unitary translation and is not new scientific knowledge.
Its role is nevertheless load-bearing: it repairs the exact invariant defect
which killed static carrier load and changes the remaining probabilistic
problem from “all shortcuts” to “anchor-orthogonal shortcuts only.”

## Complete paper proof

Because \(\|\Phi(u)\|=\|x\|=1\), Cauchy--Schwarz gives
\(|\alpha_u(x)|\leq1\).  Equation `(1)` gives the exact decomposition

\[
 \langle\Phi(t),x\rangle
 =\alpha_u(x)\langle\Phi(t),\Phi(u)\rangle
  +\langle\Phi(t),r_u(x)\rangle.                       \tag{6}
\]

If the first inner product on the right has modulus at least \(\eta\), then
\(t\in R_A(\eta)\) because \(u=a(w)\in A\).  Otherwise, the triangle
inequality, `(6)`, and \(|\alpha_u(x)|\leq1\) imply

\[
 \theta
 \leq |\langle\Phi(t),x\rangle|
 <\eta+|\langle\Phi(t),r_u(x)\rangle|,
\]

hence \(\theta-\eta\leq|\langle\Phi(t),r_u(x)\rangle|\).
This proves `(2)` pointwise before any union or measure bound.

Taking the inner product of `(1)` with \(\Phi(u)\) and using
\(\langle\Phi(u),\Phi(u)\rangle=1\) proves orthogonality.  Spectral phase
translation is unitary and sends \(\Phi(u)\) to \(\Phi(0)\), so it preserves
the coefficient \(\alpha\) and sends `(1)` exactly to the zero-anchor
residual, proving `(5)`.  If \(x=\Phi(u)\), its coefficient is one and the
residual is zero.  Finally, translating both vectors by \(-u\) turns their
inner product into \(\langle\Phi(0),\Phi(t-u)\rangle\), whose diagonal Choi
expansion is `(4)`.

No compactness, spectral genericity, randomness, locality, finite target
family, or positivity condition on \(\theta,\eta\) is used.

## Hostile proof audit

1. **Target-cardinality leak:** none in the longitudinal branch; `R_A` is one
   event formed before the circuit union.
2. **Static-carrier false positive:** impossible for exact past-orbit targets,
   because their transverse residual is exactly zero.
3. **Hidden target-independent anchor:** none; the theorem permits an arbitrary
   anchor map and only requires its image to lie in `A`.
4. **Adaptive-selector loophole:** not solved.  A quenched theorem must still
   control every anchor-orthogonal residual selected by the circuit family.
5. **Claim inflation:** `(2)` alone does not prove complexity growth, plateau,
   or the Brown--Susskind law.

The paper proof is dependency closed.  The exact remaining `[OPEN CORE]` is a
quenched growing-replica upper bound for the second term of `(2)`, uniform over
the finite circuit dictionary and its permitted anchor choices, strong enough
to survive the circuit union.

## Lean verification

- File:
  `formal/GaloisForLFunctions/RHTower/LagResolvedStaticChoiShortcutDichotomyLaw.lean`
- Main theorem:
  `iUnion_staticChoiOverlapCaptureSet_subset_anchorReturnTube_union_residual`
- Exact supporting laws:
  `staticChoiTarget_capture_anchor_or_residual_budget`,
  `staticChoiAnchorResidual_self_eq_zero`,
  `staticChoiPhaseShift_anchorResidual_eq_tracelessResidual`, and
  `norm_inner_staticSpectralChoiVector_eq_survival_lag`.
- Verification: `lake env lean` passed on the module.
- Axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`.
