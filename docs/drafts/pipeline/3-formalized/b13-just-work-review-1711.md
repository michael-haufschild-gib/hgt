# B13 just-work items of review 1711 (B13-J1 – B13-J6)

- **ID:** b13-just-work-review-1711
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../reports/review-1711/b13.md §6
- **Statement:** Six assemblies around B13 (finitely many off-line zeros of ζ force none): its metric
  form, the implication from Connes' step 1 up to odd top relations, the single-ordinate case, the
  heat-monodromy count of off-line zeros mod 8, the spectral Selberg model, and the exact residue of
  step 1 on the finite stratum.

## Goal
Make each B13 statement of §6 of the report one Lean theorem. None proves B13.

## Results

**B13-J1 (metric form).** In the finite stratum the set of bases with infinitely many subexponential
readings of the Weil lag is all of `(0, ∞)` (RH) or null (a finite layer is seen at almost every
base). B13 ⇔ (FOL ⇒ this set has positive measure) ⇔ (FOL ⇒ for every rate `a > 0` the bases with
infinitely many readings `≤ C e^{anℓ}` have positive measure).
Proof: FOL gives ZAL; RH ⇔ ZAL ∧ AAL; the metric detection theorem makes the set null off AAL; under
RH the lag is bounded at every base.
Lean (`InfiniteRankWeilTheory/TheFiniteStratumIsAMetricZeroOneLaw`):
`subexponentialLagBases_eq_Ioi_of_riemannHypothesis`, `volume_subexponentialLagBases_eq_zero_of_finiteOffLine`,
`subexponentialLagBases_zero_one_of_finiteOffLine`, `b13_iff_pos_volume_subexponentialLagBases`,
`b13_iff_pos_volume_lagRecurrenceBases`.

**B13-J2 (step 1 ⇒ B13 up to odd relations).** Let step 1 mean: at every large aperture the CCM
restricted Weil form has a ground state that is not reflection-odd. Under step 1 and FOL, RH holds,
or the top ordinates of the off-line set satisfy an integer relation with odd coefficient sum.
Proof: off RH the finite off-line set is a finite top layer at the zero width
(`exists_finiteTopLayer_of_finite_offLine`); its ordinates lie in the top-ordinate set; with even
relations the CCM no-go (`not_finiteTopLayer_of_eventually_ground_not_odd`) contradicts step 1.
Lean (`ExceptionalLayerTheory/GroundStateParityExcludesFiniteLayersWithEvenTopRelations`):
`EventuallyGroundNotOdd`, `zetaTopOrdinates`, `TopOrdinatesHaveEvenRelations`,
`riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd`,
`finiteOffLine_imp_riemannHypothesis_or_not_evenTopRelations`, `topOrdinatesHaveEvenRelations_of_independent`.

**B13-J3 (one top ordinate).** A top-ordinate set with at most one element has only the trivial
relation; step 1 and FOL then give RH. This covers a single off-line quartet of any multiplicity.
Lean (same module): `topOrdinatesHaveEvenRelations_of_subsingleton`,
`riemannHypothesis_of_finiteOffLine_of_eventuallyGroundNotOdd_of_subsingleton`.

**B13-J4 (monodromy and the count mod 8).** If the forward monodromy group of the heat flow is
proper, then under FOL the number of off-line zeros (with multiplicity) is divisible by 8, i.e. the
zeros with Re ρ > ½, Im ρ > 0 have even total multiplicity. Exactly four off-line zero copies (one
simple quartet) force the full signed group.
Proof: `N(t)` equals the number of off-line copies for small `t > 0` (right limit of the heat count)
and `8 ∣ N(t)` for every `t > 0` when the group is proper.
Lean (`GaloisTheoryOfZeros/AProperMonodromyGroupDividesTheOffLineZerosIntoGroupsOfEight`):
`eight_dvd_card_offLine_of_not_mem_forwardMonodromy`, `mem_forwardMonodromy_of_not_eight_dvd_card_offLine`,
`mem_forwardMonodromy_of_card_offLine_eq_four`.

**B13-J5 (spectral model).** Some compact surface has an entire Selberg zeta function that is an
Euler product on Re s > 1, satisfies the exact functional equation, and has a finite nonempty set of
zeros off the line in the strip, all real; its logarithmic derivative is a nonnegative real number
on the real axis right of 1 (the Euler logarithm has nonpositive coefficients). For ζ, Re(−ζ'/ζ(σ))
≥ 0 for σ > 1 and ξ is positive on ℝ.
Lean (`CompactHyperbolicSurfaces/TheSelbergZetaIsASpectralModelOfAFiniteLayer`):
`CompactQuotient.logDeriv_eulerZeta_ofReal`, `exists_selbergZeta_spectral_finiteLayer`,
`riemannZeta_euler_sign_and_xi_real_pos`.

**B13-J6 (the residue of step 1).** Under step 1 a finite off-line set is empty, or the
leading-order parity balance `F` of its top layer is `≤ 0` at every aperture phase `θ(a) = −2a·t`;
such a layer has an odd top relation.
Proof: one aperture with `F > 0` gives odd ground states at arbitrarily large apertures
(`exists_aperture_ground_odd`); even relations give one (`ccm_exists_large_aperture_odd_wins_of_even_relations`).
Lean (`ExceptionalLayerTheory/GroundStateParityExcludesFiniteLayersWithEvenTopRelations`):
`finiteOffLine_imp_riemannHypothesis_or_balance_nonpos`, `evenTopRelations_false_of_balance_nonpos`.

## Open: the residue
A top layer escapes step 1 only if `F ≤ 0` along its whole aperture line. Proved in Lean, each for all
integer relations: positivity for every fixed ordinate shape at small depth (`CCMParityDeepLimit`,
`exists_deep_balance_pos`), for every fixed cluster shape at large height
(`CCMParityLargeHeightCluster`, `exists_height_ground_odd`), and wherever `|F| > Lη` somewhere on a
line passing within `η` of the half-turn (`CCMParityNearHalfTurn`). The thresholds depend on the shape,
so the residue is the set of odd-relation layers at intermediate depth and height on which `F` stays
nonpositive. Whether it is empty is open, already for two top ordinates; it is a question about
`4 × 4` Cauchy pencils along a closed curve of a 2-torus.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully proven (assemblies of corpus theorems)
- [x] 2 → 3  formalized: each module checked with `lake --old env lean`, no warnings; wired into the
  umbrellas `InfiniteRankWeilTheory`, `ExceptionalLayerTheory`, `GaloisTheoryOfZeros`,
  `CompactHyperbolicSurfaces`

## Log
- 2026-11-17 — created and formalized.
