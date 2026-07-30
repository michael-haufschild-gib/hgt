# Star-multiplicative defect chain law

- **ID:** `star-multiplicative-defect-chain-law`
- **Stage:** 3-formalized
- **Type:** exact algebraic composition law / operator-theory bridge
- **Scientific status:** `[PAPER-PROVED] [PARENT ALGEBRA]`
- **Parent:** `../../1-in-progress/source-generated-ternary-reciprocity-law.md`
- **Lean target:** `GaloisForLFunctions.HTGeometry.StarMultiplicativeDefectChain`

## Exact theorem

For a map \(\Phi:A\to B\) between star rings, define
\[
\Gamma_\Phi(x,y)
=\Phi(x^\dagger y)-\Phi(x)^\dagger\Phi(y).               \tag{1}
\]
If \(\Psi:B\to C\) is additive, then
\[
\Gamma_{\Psi\Phi}(x,y)
=\Psi\!\left(\Gamma_\Phi(x,y)\right)
+\Gamma_\Psi(\Phi(x),\Phi(y)).                            \tag{2}
\]

There is also an order-unit-weighted identity.  For chosen intermediate and output inverse
weights \(h^{-1}\in B\) and \(k^{-1}\in C\), put
\[
\Gamma_{\Phi}^{h}(x,y)
=\Phi(x^\dagger y)-\Phi(x)^\dagger h^{-1}\Phi(y),        \tag{3}
\]
and
\[
\Gamma_{\Psi}^{k|h}(b,c)
=\Psi(b^\dagger h^{-1}c)-\Psi(b)^\dagger k^{-1}\Psi(c). \tag{4}
\]
Then
\[
\Gamma_{\Psi\Phi}^{k}(x,y)
=\Psi\!\left(\Gamma_\Phi^{h}(x,y)\right)
+\Gamma_\Psi^{k|h}(\Phi(x),\Phi(y)).                     \tag{5}
\]
Both identities are direct algebraic cancellation laws.

## Meaning and boundary

For unital completely positive maps, `(1)` is the standard Kadison--Stinespring covariance and
has a positive-kernel factorization.  For nonunital completely positive maps with strictly
positive output order unit, `(3)` is the generalized Schwarz defect.  Those positivity facts are
parent operator theory and are not re-proved by this module.

The exact survivor is compositional: previously created multiplicative defect is transported and
new defect is added.  This makes `(2)` and `(5)` possible local laws of total irreversible
distinction.  It does not identify the defect with objective actualization, time, causality,
spacetime, gravity, or any gauge force.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.StarMultiplicativeDefectChain`
- **Definitions:** `starMultiplicativeDefect`, `weightedStarMultiplicativeDefect`,
  `relativeWeightedStarMultiplicativeDefect`
- **Theorems:** `starMultiplicativeDefect_comp`,
  `weightedStarMultiplicativeDefect_comp`
- **Direct check:** passed with
  `lake env lean GaloisForLFunctions/HTGeometry/StarMultiplicativeDefectChain.lean`
- **Target build:** passed with
  `lake build GaloisForLFunctions.HTGeometry.StarMultiplicativeDefectChain`
- **Axiom audit:** only `propext`, `Classical.choice`, and `Quot.sound`
- **Repository lint:** new module is reachable from `HTGeometry`; full lint remains red on
  pre-existing/concurrent unreachable modules outside this card
- **Excluded:** complete positivity, invertibility of order units, support-pseudoinverse
  extensions, source canonicity, and all physical interpretation

## Log

- 2026-07-30 — unweighted and source-changing weighted composition identities proved in Lean.
