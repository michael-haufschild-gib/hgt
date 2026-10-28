# Fable §7: the sign, the collision count, the census

- **ID:** fable-three-questions
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) programme
- **Source:** docs/reports/review-2810/fable.md §7 (Q-I, Q-II, Q-III)
- **Statement:** Definite answers to the three questions of the review, each formalized.

## Q-I — selective dyadic Toeplitz sign (one generator, prime two)

Answer (paper):
1. The dyadic sign is RH at every overlap, even with generators of arbitrarily small support and
   pole moments killed (pole complement = whole tower). Assembly of the one-prime tower law
   (`zeta_one_prime_tower_law`, small-support annihilators) plus a pole kill point.
2. Rigidity: if two weights `λ, λ'` differ by a one-signed `u` with
   `Σ_{|log n − D| ≤ r} |u(n)|/√n ≥ c e^{δD}` (`δ > 0`), they are never both dyadic positive along a
   nonnegative generator; the 2×2 Gram on lags `{0, d}` fails at an explicit `d`. Proof: PSD 2×2
   minors bound `|w(d)| ≤ w(0)`; the difference of the two lag sequences is the prime difference,
   one-signed and exponentially growing.
3. Corollaries: `Λ` and `Λ + ε n^{−η}` (`0 < η < 1/2`) are never both dyadic positive, though they share
   every Brun–Titchmarsh / short-interval PNT statement up to `1 + o(1)`; so those inputs cannot decide
   the sign. `Λ` and its Liouville twin are never both dyadic positive (full form).

Lean (compiled, axioms standard):
`SelectiveMultiscaleArithmeticPositivity/TheDyadicSignIsRigid.lean` —
`primeMass_add_le_of_towerPositive`, `not_towerPositive_and_of_unbounded`,
`not_towerPositive_and_perturbed`, `sum_perturbation_Ioc_le`,
`not_towerPositive_liouvilleTwin_and_vonMangoldt` (any scale `ℓ > 0`; dyadic specializations).
`SelectiveMultiscaleArithmeticPositivity/TheDyadicSignOfAPoleFreeGeneratorIsRH.lean` —
`zeta_poleFree_small_tower_law`, `riemannHypothesis_iff_towerPositive_poleFree_small`,
`not_towerPositive_liouvilleTwin_of_riemannHypothesis`, `not_towerPositive_perturbed_of_riemannHypothesis`.

## Q-II — t-uniform collision bound for the heat flow

Answer (paper): split the nonreal zeros of `H_t` at height `h`.
1. Energy–count law: below the Gaussian horizon, `#{Im w ≥ h} ≤ 2K/h²`, `K` the energy
   `Σ_{Im ρ>0} ((Im ρ)² − 2t − h²/2)_+` of `Ξ` (weak majorization at threshold `h²/2`).
2. `t`-uniform high count at every height ⟺ zeros approach the line ⟺ LH ∧ every cosine shift has
   finitely many nonreal zeros. (⇒ survival of deep zeros by Hurwitz discs; ⇐ energy law below the
   horizon, antitone count above.) Zero high count at every height ⟺ RH.
3. `t`-uniform total count ⟺ finite off-line support (corpus). The flow has no depth-count law for
   the near-axis zeros (corpus `not_heat_depthCountLaw`, `twoPairQuartic_depthBudget_fails`): the
   only dynamical content beyond the depth counting of `Ξ` is the near-axis count.
So the subexponential/polynomial targets are statements about the near-axis count; any
`t`-uniform bound on the high part is Lindelöf-strength.

Lean (compiled): `RHTower/DeBruijnHighCollisionsReadTheDepth.lean` — `highCount_le_of_energy`,
`exists_highCount_le_of_zerosApproachLine`, `eventually_exists_highZeros`,
`zerosApproachLine_of_highCount`, `zerosApproachLine_iff_highCount`, `lindelof_of_highCount`,
`highCount_iff_lindelof_and_cosShiftXi_finite_nonreal`, `riemannHypothesis_iff_highCount_zero`.

## Q-III — higher inertia census

Answer (paper):
- Certificate class: `q ≤ 1`, `q ≤ 0` on `(−∞, 0]`, `q(x) ≤ β(2 − x)`. Then `tr q(Â) ≤ s₁` for every
  `Â = Σ_simple vv* + Σ_mult m vv* + Σ_pairs (aa* − B)` with `‖v‖ = 1`, `‖a‖² − tr B = 2`, `B ⪰ 0`
  (Weyl monotonicity for the positive count, Ky Fan + Schur for the top `s₂ + p` eigenvalues).
- `q*(x) = 1 − (64/49)((x − 1)² − 1/8)²` is in the class (`β = 32/7`).
- Sine-kernel Gram moments at bandwidth one: `κ₂ = 4/3`, `κ₃ = 2`, `κ₄ = 13/4`
  (fully distinct 3- and 4-cycle terms vanish). Value of `q*`: `16/21 > 3/4`.
- Optimality: block model with simple pairs of overlap `√2/4` (`16/21` of zeros) and coalesced pairs
  (`5/21`) matches all four moments; so `16/21` is exactly the best degree-≤4 certificate.
- Remaining input for `ζ`: the 3- and 4-level correlation sums at bandwidth `λ → 1⁻`.

Lean: TODO.

## Log
- 2026-10-28 — created; Q-I and Q-III paper answers drafted.
