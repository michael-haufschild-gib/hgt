# The toric certificate for Theorem A (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **29**.
Completes the toric arc begun in
[[research/tame_monomial_eigenvolume_toric_model_2026_08_06]]; depends on
[[research/monomial_map_injective_total_invariance_2026_08_06]].

## `ToricEigenvolumeCertificate.lean`

One theorem, `toric_eigenvolume_certificate`, hypotheses **only** `∀ i, 1 ≤ e i` and
`∀ i, IsUnit ((e i : k))` (tameness).  Nothing about orders is assumed.  Conjuncts:

1. **(3)** coordinate divisors totally invariant — `comap_monomialMap_span_X`
2. **(2),(5)** `formOrder 1 (∏ X j) (coordDivisor i) = −1` — `formOrder_coordDivisor_log`
3. ramification index `= e i` — `orderAt_coordDivisor_monomialMap_X`
4. Jacobian order `= e i − 1` — `orderAt_coordDivisor_det_jacobian`
5. **(8),(9)** shifted order law
6. **(6)** `e − 1 = e·boundary(F i) − boundary(i)`

## Honest framing (important)

In the toric model the order `c = −1` is **computed directly**, so routing the conclusion through
`eigenvolumeOrder_eq_neg_one_of_someRamified` would add nothing mathematically — it would be a
derivation of something already in hand.  The certificate is therefore stated as what it is: an
**independent verification** that every hypothesis and every conclusion of the general theorem hold
simultaneously in a model where each can be checked by hand.  Do not re-dress it as a derivation.

Also worth recording: applying the *packaged* theorems (`formOrder_pullback_shiftLaw`,
`eigenvolume_shiftLaw`) to the toric model is blocked by their **global** hypotheses
(`hwd : ∀ P : PrimeDivisor B, (comap φ P.1).height = 1`, `hJ` at every prime divisor).  Only the
unpackaged `orderAt_map_eq_mul_ramification` — which takes `P`, `Q` and
`hQ : Q.1 = comap φ P.1` as explicit arguments — applies pointwise at a single divisor.

## Card status

Theorem A is now: proved in general at scheme level with geometric inputs as hypotheses
([[research/scheme_eigenvolume_horizon_assembled_2026_08_06]]), and fully verified unconditionally
in the toric model.

## Remaining in general

1. Different exponent `e − 1` for a general tame extension.
2. Sheaf of differentials on a scheme.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
