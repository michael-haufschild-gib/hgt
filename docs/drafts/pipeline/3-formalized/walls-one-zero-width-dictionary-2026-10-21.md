# The walls measure one zero width: identities between the obstructions

- **ID:** walls-one-zero-width-dictionary-2026-10-21
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-2110/walls-ledger.md, Wall 1 with faces 1.1–1.5 (cited in the companion documents by the labels 1, 2, 4, 11, 12) · hard-obstacles-summary.md §2.2 ("O1 and O2 are one problem")
- **Statement:** The graded forms of the square-root barrier (face 1.1), the axis outside the zero set (1.2) and the ground-energy path (1.3) are readings of one number, the zero width `zetaZeroWidth = sup |Re ρ − ½| = Θ − ½`; the Jensen gap (1.5) reads it at the endpoint; node criticality is the support condition of the forced dual measure (1.4). Lean module `formal/GaloisForLFunctions/SquareRootThreshold/TheWallsMeasureOneZeroWidth.lean`.

## Goal
The walls ledger lists seventeen obstructions in seventeen languages. The suspicion was that
several are the same obstacle. This card records which of them are literally the same number and
in which direction each reading is proved, so that progress on one wall is automatically progress
on the others and so that the one missing arrow is named.

## The dictionary (all unconditional, no premises)

One number in four languages (`σ ≥ 0`):

| Language | Statement | Lean |
|---|---|---|
| Zeta23 configuration | `∀ ρ ∈ zetaZeroConfig.carrier, Re ρ ≤ ½ + σ` | `zetaZeroWidth_le_iff_re_le` (existing) |
| RHTower abscissa | `zetaZeroAbscissa ≤ ½ + σ`; `zetaZeroWidth = zetaZeroAbscissa − ½` | `zetaZeroWidth_le_iff_zetaZeroAbscissa_le`, `zetaZeroWidth_eq_zetaZeroAbscissa_sub_half` |
| CCM Xi half-plane bound | `XiZeroHalfPlaneBound σ` | `zetaZeroWidth_le_iff_xiZeroHalfPlaneBound`, `xiZeroHalfPlaneBound_zetaZeroWidth` |

Wall 1 (square-root barrier) reads the width, for `0 ≤ σ < ½`:

| Prime-side quantity | Equivalent to `zetaZeroWidth ≤ σ` | Lean |
|---|---|---|
| Deficit primitive `D(T) = ∫₀ᵀ(eᵗ − ψ(eᵗ))dt`, one-sided | `∀ β > σ, ∃ B, D(T) ≤ B(1+T)e^{(½+β)T}` (and the mirror `≥ −…`) | `zetaZeroWidth_le_iff_forall_deficitPrimitive_le`, `…_ge` (new iff; the ⟹ direction `exists_abs_deficitPrimitive_le_of_zetaZeroWidth_le` is the generalized von Koch bound integrated) |
| Mean-square band `∫₀ᴸ Ẽ²` | `∀ β > σ, MeanSquareBandRate β` | `zetaZeroWidth_le_iff_forall_meanSquareBandRate` |
| Laplace energy / spectral band | rate β for every β > σ | `zetaZeroWidth_le_iff_forall_laplaceEnergyRate`, `…_spectralBandRate` |
| Suzuki completed formation energy | subpower at exponent `1 + 2σ` | `zetaZeroWidth_le_iff_suzukiCompletedFormationEnergy_subpower` |
| Möbius–divisor Abel energy exponents | `inf = 1 + 2·zetaZeroWidth` | `one_add_two_mul_zetaZeroWidth_eq_sInf_mobiusDivisorAbelMeanSquareEnergy_exponents` |
| Lag family `P_v` | `≥ −Ce^{σv}` eventually (generic width) | `zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp` (existing) |
| Window ceiling excess exponent `θ*` | `zetaZeroWidth ≤ θ* ≤ zetaZeroWidth/2 + ¼` | `windowCeilingExcessExponent`, `zetaZeroWidth_le_windowCeilingExcessExponent`, `windowCeilingExcessExponent_le_half_zetaZeroWidth_add_quarter` |

Wall 12 (forced dual measure, ground-energy path) and wall 1, directly:

- `μ(A) ≥ −Ce^{2σA}` eventually ⟹ `zetaZeroWidth ≤ σ` (`zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`).
- `μ(A) ≥ −Ce^{2σA}` eventually ⟹ `P_v ≥ −C'e^{σv}` eventually, for **every** width `2w < log 2` (no exceptional set), by the Rayleigh bridge alone, without passing through the zeros (`lag_primeWindow_ge_neg_exp_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`).
- Hence the three graded statements are ordered: ground-energy floor (rate 2σ) ⟹ lag floor (rate σ) ⟺ width ≤ σ ⟺ every wall-1 reading at rate σ.
- **Open arrow:** `zetaZeroWidth ≤ σ ⟹ μ(A) ≥ −Ce^{2σA}`. At `σ = 0` it is `RH ⟹ μ ≥ 0` (proved). For `σ > 0` it is the graded form of the no-crossing problem; the obstruction is that the explicit-formula control of the off-line zero sum needs an `H¹` norm while `μ(A)` is `L²`-normalized.

Wall 4 (axis outside the zero set, heat flow): `newmanConstant ≤ zetaZeroWidth²/2` (`newmanConstant_le_half_sq_zetaZeroWidth`); endpoint `zetaZeroWidth = 0 ↔ newmanConstant = 0`.

Wall 2 (Jensen gap): each zero right of the line contributes `2π m_ρ log|ρ/(1−ρ)|` to the Balazard–Saias–Yor integral (`two_pi_mul_log_norm_div_le_integral_log_norm_zeta_criticalLine`); the integral vanishes iff the width does (`integral_log_norm_zeta_criticalLine_eq_zero_iff_zetaZeroWidth_eq_zero`). No graded (exponent) reading exists: the Blaschke weight of a zero decays with its height.

Wall 11 = wall 12 (positivity side): `PrimeBlindPositiveOn S ↔ ∃ lam, WeilPositiveFull lam ∧ lam = 0 off S` (`primeBlindPositiveOn_iff_exists_weilPositiveFull_eq_zero_off`), and since the cone is `{Λ}`, `↔ WeilPositiveFull Λ ∧ supp Λ ⊆ S` (`primeBlindPositiveOn_iff_weilPositiveFull_vonMangoldt_and_support`). Node criticality is the support condition of cone uniqueness.

Endpoint identities (width zero in every language): `zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero`, `…_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero`, `…_iff_primeBlindPositiveOn_primePowers`, `…_iff_deficitPrimitive_bound`.

## Walls with no width reading
Walls 3, 5–10, 13–17 are not graded by the width: 3/7 are quantifier statements on the same lag family (horizon law), 5/14/15 are structural impossibilities (no Frobenius, size law, orientation blindness), 6/16 are threshold classifications at damping ½ (absolute convergence; parity pairs), 8/9/11/13 are rigidity and selectivity laws, 17 is an exponent law on the pronic Gram. The admission at damping `ε` of wall 16 yields the translation closure `ζ(ρ)=0, Re ρ > ½+ε ⟹ ζ(ρ−ε)=0` and bounds no width.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven: every arrow is a composition of corpus theorems plus the von Koch integration and the pinching argument
- [x] 2 → 3  formalized: `TheWallsMeasureOneZeroWidth.lean`, `lake env lean` clean, axioms standard (see log)
- [ ] 3 → 4  not applicable (no stage 4 for non-RH items)

## Approach
Glue the three zero-set languages (`zetaZeroConfig`, `zetaZeroAbscissa`, `XiZeroHalfPlaneBound`) through the strip, then compose the existing width laws. New mathematics: the one-sided deficit-primitive rate law (von Koch bound integrated against `e^{(½+β)t}` on `[0,T]`), the ceiling excess exponent pinching, the direct ground-energy ⟹ lag-floor arrow, and the per-zero Jensen floor.

## Log
- 2026-10-21 — created directly in 3-formalized; module compiled with `lake env lean`; wired into the SquareRootThreshold umbrella (import uncommitted, [S] until committed).

## Round two: more walls folded, and the principle behind them

Three further modules (all unconditional, standard axioms; `lake env lean` clean; wired):

- `formal/GaloisForLFunctions/RHTower/AdmixturesAndTheShiftedPairLeaveTheWeilCone.lean` —
  admixture (old wall 8) and temperedness gate (old wall 9) are the Weil-cone point (face 1.4):
  `weilPositiveFull_admixture_iff` (`tΛ + (1−t)λ₀` positive iff RH ∧ λ₀ = Λ, t ≠ 1);
  `not_weilPositiveFull_shiftedPairVonMangoldt` (every shift); `weilPositiveDegree_two_shiftedPairVonMangoldt_iff`
  (degree-two cone: positive iff RH ∧ a = 0; the cone reads the coefficient size at the node 2).
- `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/UnsignedMajorantsAndSignBlindDataStopAtHalfDamping.lean` —
  old walls 6, 16, 17 are one threshold: `uniformReceiverBound_iff_half_lt` (unsigned majorant on the
  damped class iff ε > ½), `uniformReceiverBound_iff_amplitudeInvariant`,
  `receiverBounded_magnitudeInvariant_iff` (magnitudes |c(d)|, the ℓ²-class data, decide iff ε > ½; below
  it `Kχ₄(d)d^{−ε}` and `K1_odd(d)d^{−ε}` have equal magnitudes and opposite receivers).
- `formal/GaloisForLFunctions/SquareRootThreshold/LagGridsAndTransportLawsReadTheZeroWidth.lean` —
  old wall 7 (grids) is the width up to attainment: `zetaZeroWidth_le_iff_attainedTop_and_grid_primeWindow_ge_neg_exp`;
  old wall 10 (transport) is a width reading: `zetaZeroWidth_le_iff_mobiusDivisorDilationCovariancePrefix_subpower`.

**The principle** — `formal/GaloisForLFunctions/SquareRootThreshold/TheZeroWidthIsAnUnboundedApertureProperty.lean`:
`configWidth Z = sup |Re ρ − ½|` for any zero configuration (`zetaZeroWidth = configWidth zetaZeroConfig`, rfl).
Faithful at unbounded aperture: `configWidth_eq_zero_iff_weil_nonneg` (tempered Z), `configWidth_le_iff_lag_twoBump_ge_neg_exp`.
Blind at every bounded aperture: `exists_configWidth_eq_and_weil_nonneg_on_aperture` (∀ a > 0, ∀ δ ∈ (0, ½],
the lattice {½ ± δ + πik/a} is tempered, has width δ and nonnegative form on all tests of aperture a);
`exists_configWidth_eq_and_onLineShadow_on_aperture` (its form below a is the form of a weighted on-line
configuration: invisibility is mimicry); `not_forall_configWidth_eq_zero_of_weil_nonneg_on_aperture`;
`configWidth_unbounded_aperture_property` (the conjunction). Together with the sign theorem and the grid
theorem: the width is decided only by the complete, signed, unbounded-aperture, pointwise data of the
explicit formula; walls 3, 7, 13, 15 and the window-boundedness of all certificates are its coarsenings.

Ledger structure after this round: seven walls — Wall 1 (faces 1.1–1.6, old 1, 2, 4, 7, 8, 9, 10, 11, 12),
Wall 16 (faces 16.1–16.4, old 6, 16, 17, 10), standalone 3, 5, 13, 14, 15; a "principle" section precedes Wall 1.

## Round three: the width is a Landau exponent

`formal/GaloisForLFunctions/SquareRootThreshold/TheZeroWidthIsALandauExponent.lean` (clean, standard axioms):
`lagRates Z w = Ici (configWidth Z)` and `configWidth Z = sInf (lagRates Z w)` for tempered Z and good w;
for ζ, `zetaZeroWidth = sInf (zetaLagRates w)` (good w), `= sInf deficitAbsRates` (two-sided deficit rates
`|D(T)| ≤ B(1+T)e^{(½+β)T}`), `= sInf bandRates` (mean-square band rates); the polar ground-energy exponent
`polarGroundEnergyRate = sInf {σ ≥ 0 | μ₀(A) ≥ −Ce^{2σA} eventually}` satisfies
`zetaZeroWidth ≤ polarGroundEnergyRate ≤ ½` and `RH ↔ polarGroundEnergyRate = 0`; `zetaZeroWidth_exponent_law`
collects these. The open arrow of the dictionary is now the inequality `polarGroundEnergyRate ≤ zetaZeroWidth`.
Chain: walls → zero width → tail exponent (Landau abscissa) → unbounded-aperture property (exponents are
invisible to bounded parameter ranges; mimics realize every width below every aperture).
