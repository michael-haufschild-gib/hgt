# Suzuki residual-overcrowding and entire-pair closure

- **ID:** `suzuki-residual-overcrowding-entire-pair-closure`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-residual-overcrowding-entire-pair-closure.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/SuzukiResidualOvercrowding.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiCompactifiedLabelOvercrowding.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiEndpointNevanlinnaMass.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiCommonGaugeQuotient.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiDonoghueHerglotzTransform.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiDonoghueSeriesTransform.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiDonoghueKernelUniformBound.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiCayleyPhaseLift.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiClarkFiniteReconstruction.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiClarkSeriesReconstruction.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFixedLatticeRigidity.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiFixedLatticeRigidityLimit.lean`
  - `formal/GaloisForLFunctions/HTGeometry/UniformZeroCountBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ComplexWeakConvergenceBridge.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ContinuousPhaseLiftUniqueness.lean`

## Formal content

| Card | Lean |
|---|---|
| `(5)` fixed-cutoff escaped tail converges | `tendsto_escapedTail` |
| `(4)` Theorem A: the residual *is* the escaped-label tail | `tendsto_escapedTail_atTop`, `labelHead`, `labelHead_mono` |
| Theorem B order engine `(6)`--`(8)` | `label_zero_neg`, `abs_label_le_of_between`, `le_card_labelWindow`, `abs_le_card_labelWindow`, `escapedTail_eq_zero`, `escapedTail_eq_zero_uniform` |
| Theorem A + B combined: interior vanishing | `residual_eq_zero_of_uniform_count` |
| Theorem C count stability without Rouché | `sum_divisor_le_of_bounds`, `eventually_half_norm_le`, `eventually_norm_le_of_tendstoUniformlyOn`, `eventually_sum_divisor_le`, `sum_divisor_le_of_uniform_bounds`, `exists_uniform_bound_of_eventually` |
| `(13)` the common gauge cancels in the ratio | `tendsto_suzukiMeromorphicCarrier` |
| `(15)` both projective endpoint limits of the Donoghue kernel | `tendsto_suzukiDonoghueKernel_atTop`, `tendsto_suzukiDonoghueKernel_atBot` |
| `(17)` weak convergence transfers to the Herglotz transforms | `integral_extendedProjectiveKernel_split`, `tendsto_integral_extendedProjectiveKernel_nevanlinna` |
| `(18)` closure: `sigma_res = 0` and the labelled mass is one | `suzuki_closure_labelledMass_eq_one`, `measureReal_interior_add_endpoint`, `endpointMass_eq_zero_iff_smul_eq_zero`, `measureReal_endpoint_eq_half` |
| `(19)` fixed-lattice rigidity, with a Clark reconstruction | `suzuki_fixedLattice_rigidity_of_clark`, `suzuki_fixedLattice_rigidity_finiteAperture_offAtoms`, `suzuki_fixedLattice_rigidity_countable_offAtoms` |
| `(19)` is false without it | `not_fixedLatticeJets_determine_carrier`, `not_fixedLatticeJets_determine_reflectionNormalized_carrier` |

Supporting layer: `donoghueTransform`, `im_donoghueTransform_pos`, `im_suzukiDonoghueKernel`,
`cayleyOfHerglotz`, `normSq_cayleyOfHerglotz_donoghueTransform_lt_one`, `cayleyOfHerglotz_ofReal`,
`cayleyPhaseLift_injective`, `eq_of_cayleyOfHerglotz_ofReal_eq`, `eq_of_exp_eq_of_eq_at`,
`eq_of_exp_eq_of_reflection`, `phase_zero_of_reflection`, `phase_eq_iff_boundaryHerglotz_eq`,
`clarkFiniteHerglotz`, `im_clarkFiniteHerglotz_pos`, `clarkFiniteReconstruction`,
`clarkFiniteReconstruction_odd`, `clarkFiniteReconstruction_symmetricPair_odd`,
`summable_donoghueSeries`, `im_donoghueSeriesTransform_pos`, `summable_clarkSeries`,
`clarkSeriesReconstruction`, `clarkSeriesReconstruction_odd`,
`not_atom_at_zero_of_reflectionNormalized`, `norm_cayleyOfHerglotz_sub_one_le`,
`tendsto_cayleyOfHerglotz_of_abs_atTop`, `cayleyOfHerglotz_neg_mul_self`, `exp_reflection_of_odd`,
`exists_nonconstant_reflectionNormalized_carrier`, `dense_compl_of_finite`,
`dense_compl_of_countable`, `phase_eq_of_boundaryHerglotz_eq_off`.

## Four things the formalization settled that the paper did not

**Theorem B is order combinatorics, not analysis.**  The "enlarged interval" step is
`abs_label_le_of_between`: strict monotonicity plus the reflection pairing forces labels to leave a
symmetric window in index order, so a window's label *count* bounds the *index* of every label in
it.  That is the sharp form of `(7) ⟹ (8)`, and it needs no measure theory at all.

**Theorem C needs no argument principle.**  The card's own proof plan called for Rouché; mathlib
carries none.  The Jensen route replaces it: `AnalyticOnNhd.sum_divisor_le` bounds zero counts
directly, and `eventually_sum_divisor_le` makes the bound uniform from pointwise convergence at the
centre plus uniform convergence on the sphere.  The contour plan is retained on the card only as a
record of the alternative.

**`(18)` was a real gap, not a corollary.**  The card introduces `(18)` as "combining Theorems B–D".
Both halves had declarations but nothing joined them, so the conclusion was never stated.  The join
is measure additivity on the compact projective interval (`measureReal_interior_add_endpoint`); the
formalization also proves the card's evenness claim, that each endpoint carries `alpha/2`.

**`(19)` is false as literally stated, and the corrected statement is proved.**
`not_fixedLatticeJets_determine_reflectionNormalized_carrier` refutes it on the corpus's carrier
model with the odd wobble `x + sin x (1 + cos x)/4`, which is reflection-normalized and fixes the
whole even phase lattice with derivative one.  Rigidity holds exactly for carrier classes admitting
a Clark reconstruction, and that reconstruction is then *built* — for a finite aperture and for the
full `ℤ`-indexed lattice — so the theorem is not conditional on an unexamined hypothesis.  Two
structural facts fall out: a reflection-normalized carrier can carry no atom at the origin
(`not_atom_at_zero_of_reflectionNormalized`), and reflection-symmetric configurations always admit
the normalization (`clarkFiniteReconstruction_odd`).

## Hypotheses

Weak convergence of the tested totals and coordinatewise convergence of the labels and masses — the
card's own extraction hypotheses `(3)` — plus, for `(8)`, the uniform window count `(7)`, which
Theorem C then produces.  For `(19)`, a Clark reconstruction, which is constructed rather than
assumed in the finite and countable cases.  No hypothesis is a theorem proved elsewhere in the
corpus.

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs.  Every cited
declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's four unchecked gates — source common-gauge pair normality, the source zero-linear-mass
theorem, the Xi/de Branges ratio identification, and RH — are frontier items beyond this card's
claims.  Within `(19)`, what remains is a winding lift for a configuration with interior atoms:
`exists_nonconstant_reflectionNormalized_carrier` supplies a non-degenerate witness with the
endpoint-concentrated configuration, but a witness whose phase winds across interior atoms is not
built.  That is an inhabitedness refinement of the hypothesis class, not a link in the chain.
