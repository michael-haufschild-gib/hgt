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
`highCount_iff_lindelof_and_cosShiftXi_finite_nonreal`, `riemannHypothesis_iff_highCount_zero`,
two-sided depth law `highCount_le_card_deepCopies` (uniform bound `D(h/2)/(2h²)`) and
`card_deepCopies_le_of_highCount` (`D(2h) ≤ B`).

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
- With `κ₂ = 4/3, κ₃ = 2`: `q⋆` reaches `3/4` iff `κ₄ ≤ 2503/768`; sine kernel `κ₄ = 2496/768`.

Lean (compiled): `ArithmeticCastelnuovoSeveri/HigherInertiaCertifiesSixteenTwentyFirsts.lean` —
`sum_le_of_isInertiaCertificate`, `sum_eigenvalues₀_le_of_isInertiaCertificate`,
`sum_eigenvalues₀_le_card_of_columns`, `isInertiaCertificate_rankTrace`,
`isInertiaCertificate_qStar`, `sum_qStar_eq_moments`, `qStar_moments_le_card_of_columns`,
`qStar_value_sineMoments`, `extremalDiag_moments`, `three_quarters_le_qStarValue_iff`,
`abs_qStarValue_sub_le`, `witness_moments`, `le_sixteen_twentyFirsts_of_valid`, `sum_qStar_witness`.

Final answer (range obstruction): the `k`-th Gram moment at bandwidth `λ` is a `k`-level correlation
whose cycle test function has `Σ|ξ_i| ≤ 2λ` for `k = 3` but up to `4λ` for `k = 4` (alternating edge
frequencies). Inside the correlation range `Σ|ξ| < 2` the cubic moment exists for `λ < 1` and equals
the blind-spot value `2` at `λ → 1`; the quartic moment exists only for `λ < 1/2`, where the rank cap
gives at most `λ`. Hence order-≤4 inertia from in-range correlations certifies exactly `2/3`; `16/21`
needs the beyond-threshold fourth moment `κ₄ = 13/4` at `λ → 1`, and `3/4` needs `κ₄ ≤ 2503/768`.
- Prime side (paper): with `Ĝ = A + E`, `A ≈ λ⁻¹ I`, `κ₃ = λ⁻² + 1 + tr E³/N` (triples are exact
  prime-power coincidences, negligible), `κ₄ = λ⁻³ + 2/λ + tr E⁴/N`; the pair-pair diagonal of
  `tr E⁴/N` is `(4/15)λ` (patterns: `4(L − max)₊ + 8(L − y − y')₊` against `yy'`), exact for `λ < 1/2`.
  At `λ = 1` the sine kernel has `c₄ = 1/4 = 4/15 − 1/60`: the `−1/60` is the off-diagonal
  (products `n₁n₃ ≈ n₂n₄ > T`) — beyond threshold, as in the CUE high range `x + y > N`.
- Sine-kernel moments (Lean): `κ₂ = 4/3`, `κ₃ = 2`, `κ₄ = 13/4`, defined as the coincidence
  expansions of `tr Ĝᵏ` against the determinantal correlations `ρ_m = det[S(x_a − x_b)]`.
  Fourier side: `S = 𝓕1`, `S² = 𝓕Δ`, `S³ = 𝓕(Δ⋆1)`; `∫S⁶ = 11/20`, `∫_{|η|≤1/2}(Δ⋆1)² = 9/20`;
  fully distinct triangles and four-cycles vanish; the `K₄`-with-doubled-matching integral is
  `∫(Δ³ − Δ⁴/3) = 11/30` via `|1⋆(1e_x)|(η) = |L S(Lx)|`, `L = (1−|η|)₊`.
  `ArithmeticCastelnuovoSeveri/TheSineKernelMomentsMatchTheBlindSpot.lean` — `sineKappa₂_eq`,
  `sineKappa₃_eq`, `sineTriple_eq_zero`, `sineMoments_eq_blindSpot`, `cubic_sineValue_le_two_thirds`,
  `qStarValue_sineKappa`.
  `ArithmeticCastelnuovoSeveri/TheSineKernelFourthMomentIsThirteenQuarters.lean` — `rho₃_eq`,
  `rho₄_eq`, `sineQuartPair_eq`, `sineSquarePair_eq`, `sineCycle₄_eq_zero`, `sineKappa₄_eq`,
  `integral_sk_sq_mul_K15`, `qStarValue_sineKappa_eq` (`16/21`), `sineMoments_eq_witness`,
  `quartic_sineValue_le_sixteen_twentyFirsts`, `sineKappa₄_lt_blindSpot`,
  `neg_coeff_of_beats_two_thirds_sine`, `sixteen_twentyFirsts_le_card_of_sineMoments`.
- Lean: `ArithmeticCastelnuovoSeveri/TheBlindSpotIsExactThroughThirdOrder.lean` —
  `triangle_variation_le`, `square_variation_le`, `square_variation_attained`,
  `sum_le_card_of_isInertiaCertificate`, `blindSpot_moments`, `blindSpot_value`,
  `cubic_value_le_two_thirds`, `quartic_value_le`, `neg_coeff_of_beats_two_thirds`,
  `qStar_value_diagonal`.
- ζ zeros, unconditionally (complex ordinates), Montgomery's mean-square method (card
  `3-formalized/zeta-three-and-four-level-form-factors.md`): the 3-level form factor vanishes,
  `∫_0^T S(T^α)S(T^β) conj S(T^{α+β}) = o(T log T)` for `α + β < 1` (`tendsto_tripleFormFactor`), and
  the 4-level form factor is Gaussian, `∫_0^T |S(T^α)|²|S(T^β)|² ~ (αβ/16) T log²T` for `α < β`,
  `α + β < 1` (`tendsto_fourLevelFormFactor`). In range, ζ's higher statistics are the sine
  kernel's — no extra census information beyond the blind spot.
- Zeta23's `Z.Gz P T = P.Gp T` makes every power trace prime-side; the cubic `ζ` moment is an
  in-range Zeta23-§5-scale computation, but it carries no census information (blind spot).

## Log
- 2026-10-28 — created; Q-I and Q-III paper answers drafted.
- 2026-10-28 — Q-I, Q-II, Q-III certificate formalized and wired.
- 2026-10-29 — Q-II two-sided depth law; Q-III range obstruction and third-order blind spot formalized.
- 2026-10-29 — sine-kernel moments `κ₂, κ₃, κ₄` and the `16/21` census corollaries formalized.
- 2026-10-29 — ζ 3- and 4-level form factors below threshold formalized.
