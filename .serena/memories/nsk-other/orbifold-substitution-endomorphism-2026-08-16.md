# The orbifold tail lane — state after 2026-08-16

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/rational-coarse-graining-orbifold-tail-classification.md`
(the last six sections of the card hold the details; ledger entry also written).

## Modules (unconditional, axiom-clean, `HTGeometry` umbrella)

`HTGeometry/EigenLogDerivNormalization.lean`
- `deriv_eigen_of_chain_rule`, `eigen_logDeriv_of_chain_rule` — field-generic `(T1) → (T3)`;
  the chain-rule hypothesis is needed **only at the eigenvector itself**.
- `coeff_comp_C_mul_X`, `coeff_eigen_of_comp_scale`, `coeff_eigen_pow_of_comp_scale` —
  `Q^Phi(rho·T) = rho^d Q(T)  ⇒  Phi(q_j) = rho^(d-j) q_j`.

`HTGeometry/JetRationalSubstitution.lean` (~550 lines)
- `substitutionValue/Jet/Deriv`, triangularity, `algebraicIndependent_substitutionJet`,
  `jetSubstitution` (via `IsFractionRing.liftAlgHom`), `jetSubstitution_deriv` (differential),
  `orbifoldTail = stableRangeCore`, `derivationClosed_orbifoldTail`, `orbifoldTailAlgEquiv`.
- Chain rule: `substitutionChainField`, `pd_jetSubstitution_top`.
- `pd_commutator`, `pd_comm`, `pd_order_le`.
- `(T1)` `pd_eigen_of_jetSubstitution_eigen`; `(T3)` `eigen_logDeriv_pd_of_jetSubstitution_eigen`
  (needs `M ≥ 1`).
- `substitutionJet_one`, `jetSubstitution_jet_one` — `Phi_R(y_1) = y_1·R'(y_0)` exactly.
- `jetSubstitution_eulerQuotient` — the Euler quotient `y_1·pd_1 v / v` of a `(T3)`-eigenvector is
  `Phi_R`-fixed; `mem_orbifoldTail_of_fixed`.
- `IsInvariantDifferential`, `invariantCurrent k q = q·y_1^k`,
  `jetSubstitution_invariantCurrent`, `adjoin_le_orbifoldTail_of_isInvariantDifferential`,
  `differentialAdjoin_le_orbifoldTail_of_isInvariantDifferential` — the card's easy half of item
  (1), now for the concrete `Phi_R`.
- `isInvariantDifferential_pd_of_order_zero_eigen` — the **order-zero exit**: differentiating an
  order-zero eigen-relation gives an invariant 1-differential with the same eigenvalue.

## Two simplifications found

1. The chain rule does **not** need "order ≤ m ⇒ membership in `adjoin C {y_0..y_m}`".  Use the
   total-derivative formula on the finite jet slice every element inhabits.
2. The degenerate branch `Phi_R(s) = s`, `ord s = 0` does **not** need the composition-degree
   theory `deg(s∘R) = deg s · deg R`: if `s` is nonconstant then `pd_0 s ≠ 0` and `pd_0 s` *is* the
   invariant 1-differential.

## What is left (hard direction)

The descent from `(T3)` at order `nu`.  Both remaining branches need one thing: a coprime
representation of an element of `C(y_0)(y_1)` as `P(y_1)/Q(y_1)` over `F = C(y_0)`.  The route:
`y_1` is transcendental over `F`, so `RatFunc.algEquivOfTranscendental` identifies `F⟮y_1⟯` with
`RatFunc F`, whose `num`/`denom` are coprime by construction; `Phi_R` restricts to `F` (it sends
`y_0 ↦ R(y_0)`) and acts on `y_1` by the scaling `y_1 ↦ R'(y_0)·y_1`, so in `RatFunc F` coordinates
it is "apply `Phi_R|_F` to coefficients, then substitute `T ↦ rho·T`".  Coprimality then forces
`Q^Phi(rho T) = rho^(deg Q) Q(T)` and likewise for `P`, and
`coeff_eigen_pow_of_comp_scale` turns every coefficient into an order-zero eigen-relation, which
`isInvariantDifferential_pd_of_order_zero_eigen` converts into an invariant differential.
Estimated 300–500 lines.  For `nu ≥ 2` the same slicing is needed with `Phi_R(y_nu) = rho·y_nu + L`,
`L ≠ 0`, which additionally requires solving the affine equation `Phi(z) = rho z - dL` in `F`.
