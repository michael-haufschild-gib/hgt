# Orbifold-tail card: the substitution endomorphism and its order descent

Card: `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/other/rational-coarse-graining-orbifold-tail-classification.md`

## What is built (all unconditional, axiom-clean, umbrella-wired)

`HTGeometry/JetRationalSubstitution.lean`
- `substitutionValue R = R(y0)`, `substitutionJet R l = delta^l R(y0)`, `substitutionDeriv R = R'(y0)`
- `jetSubstitution R hR : JetField C Unit →ₐ[C] JetField C Unit` (Jacobian criterion, triangular
  with constant diagonal `R'(y0)`), injective, differential (`jetSubstitution_deriv`)
- `orbifoldTail R hR = stableRangeCore`, derivation-closed, `Phi_R` restricts to an automorphism
- chain rule `pd_jetSubstitution_top`, `(T1) pd_eigen_of_jetSubstitution_eigen`,
  `(T3) eigen_logDeriv_pd_of_jetSubstitution_eigen`
- `jetSubstitution_jet_one : Phi_R(y1) = y1 * R'(y0)` — the order-one substitution is an EXACT scaling
- `IsInvariantDifferential R hR k q lam`, `invariantCurrent k q = q * y1^k`,
  `jetSubstitution_invariantCurrent`, `differentialAdjoin_le_orbifoldTail_of_isInvariantDifferential`
- `isInvariantDifferential_pd_of_order_zero_eigen` — the order-zero exit

`HTGeometry/TwistedScalingDescent.lean` (generic polynomial layer)
- `twistComp Phi T P = (P.map Phi).comp T`; degree/leadingCoeff laws for `natDegree T = 1`
- `exists_scalars_of_twisted_cross` — coprimality splits the cross identity
- `coeff_eigen_of_twistComp_scale` — for `T = C rho * X`, every coefficient is an eigenvector

`HTGeometry/JetSubstitutionDescent.lean`
- `jetPrefixField C M` = subfield of `y_0..y_(M-1)`; `mem_jetPrefixField_iff` (order below M),
  `transcendental_jet_over_jetPrefixField`, `jetPrefixField_succ`, `jetPrefixField_zero`,
  `exists_algebraMap_of_forall_pd_eq_zero`
- `jetSubstitutionPrefix` (restriction of Phi_R), `substitutionShift R M = delta^M R(y0) - R'*y_M`
  with `ord < M`, `substitutionAffine`, `jetSubstitution_aeval` (transport)
- `SubstitutionEigen R hR M kappa w lam` := `w != 0 ∧ ord w ≤ M ∧ Phi_R(w)*R'^kappa = lam*w`;
  `IsInvariantDifferential = SubstitutionEigen … 0 …` (Iff.rfl)
- `exists_coprime_slicing`, `substitutionEigen_leadingRatio`, `exists_substitutionEigen_pred`
- `exists_isInvariantDifferential_of_substitutionEigen`, `exists_isInvariantDifferential_of_eigen`
- `exists_nonzero_isInvariantDifferential_or_eq_one`
- ORDER ONE CLOSED: `substitutionShift_one` (L = 0), `substitutionEigen_coeffRatio`,
  `exists_nonzero_isInvariantDifferential_of_order_one`,
  `exists_nonzero_isInvariantDifferential_of_pd_one_ne_zero`,
  `exists_differentialAdjoin_invariantCurrent_le_orbifoldTail`

## The one remaining obligation

Weight-zero exit above order one.  At `M >= 2` the affine remainder `L != 0`, so only the LEADING
coefficients satisfy per-coefficient relations and the descent can land on `k = 0` with a constant.

Route (derived, not yet formalized): the next-to-leading coefficient of `P^Phi . T = c*P` is
exactly a solution of the affine cocycle equation `Phi_R(t) - R'*t = -L`, namely
`t = P_(a-1)/(a*P_a)`, legitimate whenever `deg P >= 1`.  In the translated coordinate
`z = y_M + t` the substitution becomes the pure scaling `z |-> R'*z`, so the full coefficient
analysis applies at every order.  Trichotomy at level M then:
  (i) `deg P = deg Q = 0`: `w` already has order <= M-1, descend with kappa unchanged;
  (ii) normalize, non-monomial: escape with `kappa' != 0`, eigenvalue 1;
  (iii) normalize, both monomials: `w = s*z^n`, `n = deg P - deg Q != 0`, `kappa' = kappa + n`.
Residual configuration: `w = e * prod_j z_j^(n_j)` with `e` a coefficient constant and
`sum n_j = -kappa`.  At `kappa = 0` this is a constant, excluded by nonconstancy — that is exactly
why order one closes.  For `kappa != 0` a further input is needed; the natural candidate is the
residue obstruction "`e/X` has no primitive in `F(X)`", which kills `kappa = 1` (the (T1) output)
but not general `kappa`.

Sanity check of the mechanism: `R = z^d` gives `P = C(1/y0)*X`, `Q = 1`, `s = 1/y0`, `k = 1`, i.e.
the invariant differential `dz/z` — correct.

## Dependent cards

`floquet-orbifold-tail-emergence` needs `Tail(z^2+1) = C` and `Tail((z-1)^2) = C`.  Both would
follow from the general weight-zero closure plus the orbit argument recorded on the orbifold card
(critical-point order bookkeeping along the infinite forward and backward orbits of 0).
`orbifold-tail-holographic-reconstruction` needs the same tail interface.
Note: in ALL exceptional cases (power, Chebyshev, Lattes) the tail generator has jet order exactly
one — `q(y0)*y1^k`.  So "the minimal order in a nonconstant tail is one" is an equivalent
formulation of the remaining gap, and might be the easier statement to attack.
