# The orbifold tail, its substitution endomorphism, and (T1)/(T3) are Lean objects

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/rational-coarse-graining-orbifold-tail-classification.md`
(the last four sections of the card hold the details).

## New modules (unconditional, axiom-clean, `HTGeometry` umbrella)

`HTGeometry/EigenLogDerivNormalization.lean`
- `deriv_eigen_of_chain_rule`, `eigen_logDeriv_of_chain_rule` — field-generic `(T1) → (T3)`.
  The chain-rule hypothesis is needed **only at the eigenvector itself**, which is what makes it
  usable when the chain rule holds only in bounded order.
- `coeff_comp_C_mul_X`, `coeff_eigen_of_comp_scale`, `coeff_eigen_pow_of_comp_scale` — if
  `Q^Phi(rho·T) = rho^d Q(T)` then `Phi(q_j) = rho^(d-j) q_j`.  The `nu = 1` descent core.

`HTGeometry/JetRationalSubstitution.lean` (~400 lines)
- `substitutionValue R = R(y_0)`, `substitutionJet R l = delta^l R(y_0)`,
  `substitutionDeriv R = pd_0 R(y_0)`; triangularity of the Jacobian.
- `algebraicIndependent_substitutionJet` (Jacobian criterion, det `R'(y_0)^n`),
  `jetSubstitution R hR : JetField C Unit →ₐ[C] JetField C Unit` via `IsFractionRing.liftAlgHom`.
- `jetSubstitution_deriv` — commutes with the jet derivation.
- `orbifoldTail R hR = stableRangeCore (jetSubstitution R hR)`,
  `derivationClosed_orbifoldTail`, `orbifoldTailAlgEquiv`,
  `adjoin_le_orbifoldTail_of_eigenvector`.
- **The chain rule**: `substitutionChainField` (equalizer of the two twisted derivations on a
  finite jet slice) and `pd_jetSubstitution_top`:
  `(∀ j > M, pd_j v = 0) ⇒ pd_M(Phi_R v) = Phi_R(pd_M v)·R'(y_0)`.
- `pd_commutator`, `pd_comm`, `pd_order_le`,
  `pd_eigen_of_jetSubstitution_eigen` **(T1)**,
  `eigen_logDeriv_pd_of_jetSubstitution_eigen` **(T3)** (needs `M ≥ 1`, exactly the card's
  `ord u ≥ 1`, because that is what makes `pd_M(R'(y_0)) = 0`).

## The relative constant-kernel lemma is NOT needed

Earlier note said the chain rule required "order ≤ m ⇒ lies in `adjoin C {y_0..y_m}`".  It does
not.  Every element lies in `jetObservableField C y_0 N` for **some** `N`
(`exists_jetObservableField_of_mem_differentialAdjoin` + `differentialAdjoin_jet_zero_eq_top`);
on that slice the *total* derivative formula `pd_M(Phi v) = Σ_(l≤N) Phi(pd_l v)·pd_M(z_l)` holds by
an equalizer argument, and the order hypothesis kills the terms `l > M` while triangularity kills
`l < M`.

## What is left

Only the descent: from `(T3)` at order `nu`, the coefficient identity
`(P·Q)^(Phi_R)(R'·T + L) = R'^(deg)·(P·Q)(T)` in `F[T]`, the `sigma`-stable pole multiset, and the
explicit `nu = 1` branch (`L = 0`, so `coeff_eigen_pow_of_comp_scale` applies directly).  No
missing infrastructure remains between the card's setup and that descent.
