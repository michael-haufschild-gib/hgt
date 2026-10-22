# Rank-one polarized exchange-geometrizability — Lean certificate

- **ID:** `rank-one-polarized-exchange-geometrizability-formalized`
- **Stage:** 3-formalized
- **Type:** CERTIFICATE (Lean 4)
- **Paper proof:** `rank-one-polarized-exchange-geometrizability.md`
- **Status:** `[LEAN-FORMALIZED] [UNCONDITIONAL]`

## Modules

| File | Contents |
|---|---|
| `RHTower/RankOnePolarizedExchangeCurvature.lean` | items 1, 2, 8; universal character curvature `(12)`–`(13)` |
| `RHTower/RankOnePolarizedExchangeModularGain.lean` | items 3, 5, 6; `(4)`, `(5)`, `(14)`, `(15)`; Hermitian corollary `(23)`–`(26)` |
| `RHTower/RankOnePolarizedExchangeCoherentKernel.lean` | items 4, 7, 10 |
| `RHTower/RankOnePolarizedExchangeHorizon.lean` | items 11, 12; `(18)`–`(22)`; generating-set landing |
| `RHTower/RankOnePolarizedExchangeHorizonTopology.lean` | items 9, `(11)`; the character topology; the provenance-flag horizon |
| `RHTower/RankOnePolarizedExchangeRealization.lean` | item 3 as a four-way equivalence; item 4 at real and spectral weight |

All are in namespace `RHTower`.  The index monoid is `ℕ+` and the modular character is a genuine
monoid homomorphism `χ : ℕ+ →* kˣ`, so no positivity or nonvanishing side condition is carried.

## Card statement to Lean name

| Card | Lean |
|---|---|
| item 1: `A m A n = A (mn)` | `conormalTransport_mul` |
| `(1)`, `(3)`: the polarized transport | `exchangeTransport`, `exchangeTransport_eq_diagonal_mul` |
| item 2, `(2)`, `(12)`: exact curvature | `exchangeCurvature_eq` |
| Bianchi identity | `exchangeCurvature_bianchi` |
| item 3 / `(13)`: representation ↔ trivial character | `exchangeTransport_mul_iff` |
| item 3: representation ↔ `T 2 ^ 2 = T 4` ↔ `χ_θ 2 = 1` ↔ `θ = 0` | `exchangeTransport_modularGain_tfae` (and its three constituents `exchangeTransport_modularGain_mul_iff`, `exchangeTransport_modularGain_two_sq_iff`, `modularGain_two_eq_one_iff`) |
| item 4: factorization through a categorical realization forces `θ = 0` | `eq_one_of_factors` (character), `eq_zero_of_factors` (weight), `re_eq_of_factors` (purity line) |
| item 5: `T₀ = A` | `exchangeTransport_modularGain_zero`, `exchangeTransport_one` |
| item 6: blindness to imaginary height | `spectralGain_eq_of_re_eq` |
| `(4)`–`(5)`: critical-line specialization | `exchangeTransport_spectralGain_one_mul_iff` |
| `(14)`–`(15)`: purity template `Re s = w/2` | `exchangeTransport_spectralGain_mul_iff` |
| item 7, `(6)`–`(7)`: `H χ` is `⊤` or the permanent line | `coherentKernel_one`, `coherentKernel_of_ne_one` |
| item 7: invariance and restricted representation | `permanentLine_invariant`, `coherentKernel_isRep` |
| item 8, `(8)`: `J χ n ^ 2 = χ n • 1` | `exchangeSwap_sq` |
| item 8, `(9)`: calibrated paracyclic bridge | `exchangeCurvature_eq_paracyclic`, `exchangeCurvature_two_eq_zero_iff_swap` |
| item 9, `(10)`–`(11)`: initial Scott topology `{∅,{0},ℝ}` | `isOpen_exchangeHorizon_iff` |
| item 9: all nonzero weights topologically indistinguishable | `inseparable_exchangeHorizon_iff` |
| item 9: the `T₀` quotient has two points | `card_separationQuotient_exchangeHorizon` |
| character version `{∅,{1},X}` | `isOpen_characterHorizon_iff` |
| item 10, `(17)`: word kernel equals pairwise kernel | `wordKernel_eq_coherentKernel` |
| item 11, `(18)`: `D` is square zero | `exchangeDifferential_eq`, `exchangeDifferential_sq` |
| item 11, `(19)`: exchange homology | `exchangeFlag_of_eq_one`, `exchangeFlag_of_ne_one`, `exchangeHomologyEquiv`, `subsingleton_exchangeHomology` |
| item 11, `(20)`: transverse contraction is an isomorphism | `transverseEquiv` |
| item 12, `(21)`: chain maps into the acyclic complex vanish on homology | `landingH1_eq_zero`, `landingH0_eq_zero` |
| item 12: homology-conservative landing forces the horizon | `eq_one_of_landing_ne_zero` |
| `(22)`: landings over a multiplicative generating set force `χ = 1` | `eq_one_of_forall_mem_closure` |
| `(22)`: prime-indexed landings suffice | `eq_one_of_forall_prime` |
| `(16)`: the transverse framed quotient | domain of `transverseEquiv` |
| `(23)`–`(24)`: Hermitian torsion and crossed cocycle | `hermitianTorsion`, `hermitianAnomaly_mul` |
| `(25)`: curvature is the affine transgression of the anomaly | `exchangeCurvature_hermitianTorsion` |
| `(26)`: reciprocal flatness ↔ unit torsion ↔ zero anomaly | `inv_eq_conj_iff_torsion_eq_one`, `hermitianAnomaly_eq_zero_iff` |

## Relation to the existing corpus calculation

The card's hostile audit records that the raw matrix curvature already exists in
`RHTower/Deninger/DeningerOneSidedFramedMateCurvatureTransgression.lean`.  That file is imported, not
duplicated, and the identification is proved:

- `spectralGain_one_apply` — the half-density spectral gain is `deningerHalfDensityMateGain`;
- `exchangeTransport_spectralGain_one_eq` — the polarized transport of that gain is
  `deningerOneSidedFramedTransport`.

Everything new is the typed synthesis: the representation/factorization criterion, the coherent
kernel classification, the word-defect stabilization, the paracyclic calibration, the two horizon
topologies, the off-horizon acyclic complex, and the landing criterion.

## Generality actually proved

The card states the universal corollary over a field of characteristic zero.  The Lean proofs hold
over **every** field: the calibration used is `(2 : k) - 1 = 1`, a unit in any characteristic, so no
characteristic hypothesis is needed.  Items 3, 5, 6, 9 and the spectral specializations are stated
over `ℝ` with the power character, as in the card.

## Axiom audit

`[propext, Classical.choice, Quot.sound]` for every declaration listed above.
