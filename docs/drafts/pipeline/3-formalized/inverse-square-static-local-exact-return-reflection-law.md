# Inverse-square static-local exact return and operator-complexity reflection

- **ID:** inverse-square-static-local-exact-return-reflection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `inverse-square-static-local-laboratory-complexity-growth-law.md`
- **Statement:** One explicit connected static nearest-neighbour chain has an exact factorial-cube return period; its operator-norm two-qubit-gate complexity is exactly reflection-symmetric about that return, and the existing laboratory-time linear bounds therefore occur at both reflected times.

## Goal

Close the same-Hamiltonian growth--return bridge for the inverse-square chain without importing the
finite-dictionary Choi metric.  The claim is a derived `[BRIDGE]`, `[NOVELTY UNVERIFIED]`: exact
rational-spectrum recurrence and inversion symmetry are standard mechanisms; value lies in their
exact composition with the already formalized static connected-chain ramp.

## Exact statement

For `L : ℕ`, put

\[
 Q_L=(L!)^3,\qquad R_L=2\pi Q_L,
\]

and let

\[
 \widehat H_L=\sum_{j=1}^{L}j^{-2}P_{2j-1,2j}
 +L^{-3}\sum_{j=1}^{L-1}P_{2j,2j+1},
 \qquad U_L(t)=e^{-it\widehat H_L}.
\]

Let `C_L^op(t, ε)` be the infimum in `ℕ∞` of the counted two-qubit-gate costs of all
support-certified one/two-qubit circuits within global operator norm `ε` of `U_L(t)`; one-qubit
gates have cost zero. Then, for every `L, ε, t`,

\[
 U_L(R_L)=I,
 \qquad
 C_L^{\rm op}(R_L-t,\varepsilon)=C_L^{\rm op}(t,\varepsilon).
\]

If additionally

\[
 0<\varepsilon\le 1/100,
 \qquad 1024\pi\varepsilon\le t\le \varepsilon L/2,
\]

then, writing

\[
 a=\left\lfloor\frac{t}{128\pi\varepsilon}\right\rfloor,
 \qquad b=\left\lceil\frac{2t}{\varepsilon}\right\rceil,
\]

both `s=t` and `s=R_L-t` obey

\[
 a\le C_L^{\rm op}(s,\varepsilon)\le b.
\]

## Complete paper proof

For `L=0`, both energy sums vanish, so the return statement is immediate.  Assume `L>0`.
Every denominator occurring in a matching term is `k^2` with `1≤k≤L`.  Since `k∣L!`, write
`L!=ka`.  Then

\[
 \frac{Q_L}{k^2}=\frac{(ka)^3}{k^2}=ka^3\in\mathbb N.
\]

Likewise `L∣L!`; writing `L!=Lb` gives `Q_L/L^3=b^3∈ℕ`.  Every computational-basis energy is a
sum of a subset of matching coefficients and a nonnegative integer multiple of the bridge
coefficient.  Hence for every basis configuration `x` there is `N_x∈ℕ` such that

\[
 Q_LE_L(x)=N_x.
\]

The evolution is diagonal, and therefore

\[
 U_L(R_L)_{xx}
 =\exp(-i,2\pi Q_LE_L(x))
 =\exp(-i,2\pi N_x)=1,
\]

while all off-diagonal entries vanish.  Thus `U_L(R_L)=I`.

Diagonal exponentiation also gives the autonomous group law
`U_L(s+t)=U_L(s)U_L(t)`.  Consequently

\[
 U_L(R_L-t)U_L(t)=U_L(R_L)=I.
\]

Since `U_L(t)` is unitary, its inverse is `U_L(t)^*`; hence
`U_L(R_L-t)=U_L(t)^*`.

For a support-certified local gate `g`, define `g*` by keeping its support and taking the conjugate
transpose of its matrix.  Unitarity is preserved.  If the matrix of `g` factorizes across a cut,
its conjugate transpose factorizes across the same cut by conjugate-transposing both factors.
Thus `g*` is again a support-certified gate of the same arity.  For a circuit `c`, reverse gate
order and replace every gate by its adjoint, obtaining `c*`.  Then

\[
 M(c^*)=M(c)^*,\qquad \operatorname{cost}(c^*)=\operatorname{cost}(c).
\]

The global operator norm is invariant under conjugate transpose.  Therefore

\[
 \|M(c^*)-U_L(R_L-t)\|
 =\|(M(c)-U_L(t))^*\|
 =\|M(c)-U_L(t)\|.
\]

Adjoint reversal is consequently a cost-preserving bijection between circuits admitted at `t` and
circuits admitted at `R_L-t`.  Their cost sets, and hence their `ℕ∞` infima, are equal.  This proves
exact operator-complexity reflection.

Under the laboratory-window hypotheses, the existing floor/ceiling theorem says every admitted
circuit at `t` has cost at least `a` and constructs one admitted circuit of cost exactly `b` (with
strict error below `ε`).  Thus `a≤C_L^op(t,ε)≤b`.  Exact reflection transfers both inequalities to
`R_L-t`, completing the combined law. ∎

## Hostile audit

- No monotonicity between two arbitrary times is claimed; only a two-sided envelope and exact
  return reflection.
- `R_L` is a valid period, not asserted minimal.
- Complexity uses the existing global `L2` operator norm and system-only support-certified circuits;
  no ancilla/channel or fixed finite-alphabet statement is inferred.
- Weak bridges certify connected interaction geometry but remain below laboratory error during the
  ramp window; no transport mechanism is claimed.
- No plateau, exponential complexity, first-return law, Haar behavior, or Brown--Susskind theorem is
  inferred.

## Gates

- [x] 0 → 1 in-progress: exact statement frozen; internal reflection and ramp corpus audited;
  factorial-cube period closes denominator obstruction.
- [x] 1 → 2 fully-proven: dependency-closed proof above; `[PAPER-PROVED] [BRIDGE]`.
- [x] 2 → 3 formalized: exact Lean capstone; direct and target builds pass; axiom audit reports
  only `propext`, `Classical.choice`, and `Quot.sound`. Project lint reaches this module and retains
  only three unrelated pre-existing umbrella-reachability failures.
- [ ] 3 → 4 publication-ready: integrate into standalone recurrence manuscript after literature
  positioning audit.

## Approach

Use factorial divisibility to integerize every diagonal energy, derive exact return entrywise, build
the adjoint involution on support-certified local circuits, use `L2` operator-norm star invariance,
then apply the existing floor/ceiling theorem at one side of the exact return.

## Log

- 2026-08-17 — `[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]`; certificate
  `inverseSquareChain_growth_exactReturn_reflection` composes exact factorial-cube return, exact
  operator-complexity reflection, and existing laboratory-window floor/ceiling bounds.
