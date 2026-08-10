# Atomic--differential--operator three-realization process law — Lean certification

- **ID:** ULF-ADOR-1
- **Paper card:**
  `atomic-differential-operator-three-realization-process-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveThreeRealizationPacket`
- **Universal-law umbrella:**
  `GaloisForLFunctions.HTGeometry.UniversalLawField`

## The certified object

`packetMoment lam w n = ∑ⱼ wⱼ λⱼⁿ` is equation (1) with **complex** weights, so the card's
hypothesis `wⱼ ∈ ℂ^×` is carried exactly; `packetMoment_ofReal` is the definitional bridge to
`processMoment` of `ConstitutiveCyclicProcessFourShadow`, whose `spectrumPoly lam = ∏ⱼ (X − λⱼ)`
(equation (2)) and its degree/evaluation/leading-coefficient lemmas are reused rather than
rebuilt.

## Certified declarations

### §2.1 — atomic moment chart

`packetMeasure lam w = ∑ⱼ ENNReal.ofReal wⱼ • Measure.dirac λⱼ` is the atomic measure of the
positive chamber, and `integral_packetMeasure` is equation (3):
`∫ xⁿ dμ = packetMoment lam w n`.  Integrability against a Dirac measure had to be built by hand
(`hasFiniteIntegral_iff_enorm` plus `lintegral_dirac'`): mathlib has no `Integrable f (dirac a)`
lemma for an unbounded `f`.

### §2.2 — analytic differential chart

`packetFun lam w t = ∑ⱼ wⱼ e^{λⱼ t}`.

- `hasDerivAt_exp_mul` — the derivative of `s ↦ e^{λ s}`;
- `iteratedDeriv_packetFun` — the closed form of every jet, by induction through
  `iteratedDeriv_succ` and `deriv_fun_sum`;
- `iteratedDeriv_packetFun_zero` — equation (4), `f⁽ⁿ⁾(0) = mₙ`;
- `packet_ODE` — equation (5), `p(D) f = 0`, at **every** point `t`, by exchanging the two finite
  sums and evaluating `p` at each frequency.

### §2.3 — linear operator chart

- `packetMoment_eq_operator` — equation (6), `mₙ = cᵀ Aⁿ b` with `A = diagonal lam`, `b = 1`,
  `c = w`;
- `packetMoment_eq_orbit` — equation (7), `mₙ = ⟨v, Uⁿ v⟩` with `v = (√wⱼ)ⱼ` in the positive
  chamber.

### §3 — recurrence and transfer law

- `packetMoment_recurrence` — equation (8), the order-`r` recurrence of the spectrum polynomial;
- `packetMoment_recurrence_fin` — its `Fin`-indexed form, used by the Hankel system;
- `tsum_packetMoment_mul_pow` — equation (9), `∑ₙ mₙ zⁿ = ∑ⱼ wⱼ/(1 − λⱼ z)` whenever
  `‖λⱼ z‖ < 1` for every `j`.

### §4 — Hankel window, rank, and Prony reconstruction

- `rectVandermonde`, `packetHankel`, and `packetHankel_eq` — equation (10),
  `H_N = V_Nᵀ diag(w) V_N`;
- `rank_packetHankel_le` — `rank H_N ≤ min(N+1, r)`;
- `packetHankelSq`, `packetHankelSq_eq`, `det_packetHankelSq`, `det_packetHankelSq_ne_zero` — the
  leading `r × r` block has determinant `(det V)² ∏ⱼ wⱼ ≠ 0` for complex nonzero weights;
- `rank_packetHankel_of_le` — `rank H_N = r` once `r ≤ N+1`;
- `mulVec_injective_of_det_ne_zero`, `packetHankelSq_mulVec_coeff`,
  `packet_coeff_eq_of_responses_eq`, `packet_spectrumPoly_eq_of_responses_eq`,
  `packet_weights_eq_of_responses_eq`, `packetMoment_eq_of_eq_below` — the Prony reconstruction as
  determinacy statements: two packets agreeing on the first `2r` responses have the same
  recurrence coefficients, the same spectrum polynomial (hence the same unordered frequency
  packet), the same weights, and the same responses forever;
- `packet_withheld_prediction` — equation (12), the withheld response `m_{2r}`.

### §4 — the correction to equation (11)

Equation (11) of the paper card, `rank H_N = min(N+1, r)`, is **false** for `N+1 < r`, and the
formalization refutes it rather than restating it.

- `det_ne_zero_of_rank_eq_card` — new infrastructure: a square complex matrix of full rank has
  nonzero determinant (mathlib has `Matrix.rank_of_isUnit` but not this converse), proved through
  `Submodule.eq_top_of_finrank_eq`, surjectivity of `mulVecLin`, and
  `LinearMap.injective_iff_surjective`;
- `cubeRoot`, `cubeRoot_sq`, `cubeRoot_sum`, `cubeRoot_pow_three`, `cubeRoot_im_pos`,
  `cubeLam`, `cubeW`, `cubeLam_injective` — the three cube roots of unity with uniform positive
  weight, built elementarily from `√3` rather than through `Complex.exp`;
- `packetMoment_cube_zero/one/two` — `m₀ = 1`, `m₁ = m₂ = 0`;
- `rank_packetHankel_cube` — `rank H₁ = 1 < 2 = min(N+1, r)`: the printed identity fails inside the
  positive unitary chamber, for distinct unit-modulus frequencies and strictly positive weights.

The counterexample is recorded in §8 of the paper card together with the signed-weight variant
`r = 2`, `w = (1, −1)`, `λ = (1, 2)`, for which even `m₀ = 0`.

### §5 — positive unitary chamber

`momentGram_apply_packet` transports the Toeplitz Gram entries of
`ConstitutiveCyclicProcessFourShadow` into packet notation; `momentGram_posSemidef`,
`rank_momentGram` (the Toeplitz rank identity `min(N+1, r)`, true as printed) and
`exists_moment_near_one` (recurrence of the unitary orbit by compactness) are reused from that
module.

### Capstone

`three_realizations` bundles, for one positive unitary packet with `r ≤ N+1`: the atomic chart,
the jet chart, the annihilating ODE, the state-space chart, the rational transfer function, the
Hankel rank `r`, the Toeplitz Gram rank `min(N+1, r)`, and the withheld prediction.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveThreeRealizationPacket.lean
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Both green with no warnings (11,478-job umbrella build).  `#print axioms` on
`three_realizations`, `rank_packetHankel_cube`, `integral_packetMeasure`, `packet_ODE`,
`iteratedDeriv_packetFun_zero`, `packetMoment_eq_operator`, `packetMoment_eq_orbit`,
`tsum_packetMoment_mul_pow`, `packetHankel_eq`, `rank_packetHankel_le`,
`rank_packetHankel_of_le`, `packet_spectrumPoly_eq_of_responses_eq`,
`packet_weights_eq_of_responses_eq`, `packetMoment_eq_of_eq_below`,
`packet_withheld_prediction`, `momentGram_apply_packet`, and `det_ne_zero_of_rank_eq_card`
reports only `propext`, `Classical.choice`, and `Quot.sound`.  No hypothesis, interface `Prop`,
placeholder, or project axiom is used anywhere in the module.
