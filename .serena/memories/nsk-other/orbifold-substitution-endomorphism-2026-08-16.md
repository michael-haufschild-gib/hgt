# Orbifold-tail family: the Casale-free route, now reduced to a rational-map statement

Cards: `rational-coarse-graining-orbifold-tail-classification` (stage 2), and the two that depend on
the same tail interface: `floquet-orbifold-tail-emergence`, `orbifold-tail-holographic-reconstruction`.

## The chain, all unconditional and axiom-clean

`HTGeometry/JetRationalSubstitution.lean` — `jetSubstitution R hR` = `Phi_R`, `orbifoldTail`,
chain rule, `(T1)`, `(T3)`, `jetSubstitution_jet_one` (order one is an EXACT scaling),
`IsInvariantDifferential`, `invariantCurrent`,
`differentialAdjoin_le_orbifoldTail_of_isInvariantDifferential`,
`isInvariantDifferential_pd_of_order_zero_eigen`.

`HTGeometry/TwistedScalingDescent.lean` — generic: `twistComp`, degree/leadingCoeff laws,
`exists_scalars_of_twisted_cross` (coprimality splits the cross identity),
`coeff_eigen_of_twistComp_scale`, `coeff_affine_pow`, `twistComp_affine_cocycle`.

`HTGeometry/JetSubstitutionDescent.lean` — `jetPrefixField`, `jetSubstitutionPrefix`,
`substitutionShift`/`substitutionAffine`, `jetSubstitution_aeval_of_act`,
`SubstitutionEigen`, `exists_coprime_slicing(_of_coordinate)`, `substitutionEigen_leadingRatio`,
`exists_substitutionEigen_pred`, `exists_isInvariantDifferential_of_eigen`,
`exists_nonzero_isInvariantDifferential_or_eq_one`;
ORDER ONE CLOSED (`substitutionShift_one`, `substitutionEigen_coeffRatio`,
`exists_nonzero_isInvariantDifferential_of_order_one`);
NORMALIZATION (`exists_normalizing_shift`, `jetSubstitution_jet_add`, `HasNormalizingShift`,
`lowerOrder_or_hasNormalizingShift`, `substitutionEigen_normalized_trichotomy`) and the capstone
`exists_nonzero_isInvariantDifferential_or_hasNormalizingShift`.

`HTGeometry/RationalInvariantDifferential.lean` (NEW) — transports everything to `RatFunc C`:
`exists_ratFunc_of_order_zero`, `ratFuncDeriv` (+ `ratFuncDeriv_X : (X)' = 1`, `_add`, `_mul`,
`_C`, and the bundled `ratFuncDerivation : Derivation C (RatFunc C) (RatFunc C)` — mathlib has
none), `ratFuncEval_ratFuncSubstitution`,
`exists_ratFunc_relation_of_isInvariantDifferential` and its converse, and the classical capstones
`exists_ratFunc_relation_of_order_one`, `exists_ratFunc_relation_or_hasNormalizingShift`.

## The single remaining obligation, stated classically

A degree-≥2 rational map `R` which admits no nonzero-weight invariant rational differential
(`Q∘R·(R')^k = mu·Q`, `k != 0`) also admits no rational **affine connection**
(`alpha(R)·(R')^2 + R'' = alpha·R'`).  Both halves die by the same orbit/pole argument, worked out
by hand for `R = z^2+1`:
- tensor: at the critical point 0, `2·ord_1(Q) + k = ord_0(Q)`; along the infinite forward orbit
  `1 → 2 → 5 → 26 → …` the order is constant, so `ord_1(Q) = 0`, so `ord_0(Q) = k != 0`; then the
  order is constant along the infinite backward orbit of 0, giving infinitely many zeros/poles.
- connection: the same forcing puts a pole of `alpha` at 0 and hence at every point of the infinite
  backward orbit.

Substrate for formalizing it: `HTGeometry/RationalPoleOrder.lean` has `poleOrder` and `RegularAt`.
What is missing is the signed order `ord_a = zeroOrder − poleOrder`, its additivity under products
and zpow, and the composition law `ord_a(Q∘R) = ord_a(R − R(a))·ord_{R(a)}(Q)` — which follows from
the local factorization `Q = (X−b)^m·U` with `U` regular and nonvanishing at `b`.

Checked identities (hand, for orientation): for `z^d` the connection is `alpha = −1/z` and
`Gamma' − Gamma^2/2 = 1/(2z^2)` is the invariant quadratic differential with eigenvalue `d^2`;
in general `P := Gamma' − Gamma^2/2` obeys `P(R)R'^2 = P − S_R` with `S_R` the Schwarzian, so
"invariant connection ⇒ invariant tensor" is NOT automatic — the orbit argument is the route.

## Lean process notes
- `set x := e with h` clears and re-introduces every hypothesis whose type mentions `e`; put all
  `set`s BEFORE any `obtain`, or avoid `set`.
- `not_imp` is ambiguous → `Classical.not_imp`.
- `refine ⟨_, _, …, hres⟩` only infers holes if the determining term comes last.
- Structure-literal fields (e.g. building a `Derivation`) need `show` to unfold before `rw`.
