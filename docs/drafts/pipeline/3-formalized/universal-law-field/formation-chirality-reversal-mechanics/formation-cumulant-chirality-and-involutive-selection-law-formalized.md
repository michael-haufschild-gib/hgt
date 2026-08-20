# Formation cumulant chirality and involutive selection — Lean certification

- **ID:** ULF-FCRM-1
- **Paper card:** `formation-cumulant-chirality-and-involutive-selection-law.md`
- **Lean modules (all new, all umbrella-wired):**
  `HTGeometry.PositiveJumpFormationChirality`, `HTGeometry.ExponentialFormationResponse`,
  `HTGeometry.EsscherFormationChirality`, `HTGeometry.GeometricModeChirality`,
  `HTGeometry.AbelianZetaGasChemicalPotentialShift`, `HTGeometry.AbelianZetaGasModeChirality`,
  `HTGeometry.AbelianZetaGasDirectedEntropy`
- **Status:** `[LEAN-CERTIFIED] [UMBRELLA-WIRED] [NO SORRY] [NO AXIOMS] [TARGETED BUILD]`

## §4 — the response calculus

`ExponentialFormationResponse` types the two directed costs, the Jeffreys work and the commutator,
and proves, from the card's own response chain (`F' = −m`, `m' = −V`, `V' = −κ₃`) and nothing else:

* `jeffreysWork_eq_integral_secondResponse` — **(FCRM.10)** `J(u) = u ∫₀ᵘ V`;
* `formationChiralityAt_eq_integral_secondResponse` — the first form of **(FCRM.11)**,
  `χ(u) = ∫₀ᵘ (u − 2t) V(t) dt`, by parts against `w(t) = u − 2t`;
* `formationChiralityAt_eq_integral_thirdResponse` — the boxed form of **(FCRM.11)**,
  `χ(u) = ∫₀ᵘ t(u − t) κ₃(t) dt`, by parts against `g(t) = t(u−t)` with `g(0) = g(u) = 0`;
* `directed_reconstruction` — **(FCRM.12)**.

## §5 — the universal positive-jump law

`PositiveJumpFormationChirality` builds the kernel and the chronology from scratch — mathlib has
neither.

* `formationKernel a = a − 2 + (a+2)e^{−a}`, `hasDerivAt_formationKernel`,
  `deriv_formationKernel_pos` (from `e^a > a+1`), `formationKernel_pos`, `formationKernel_neg`,
  `formationKernel_pos_iff` — **(FCRM.16)** and the sign law;
* `formationKernel_pointwise` — the exact identity
  `2(e^{−tx} − e^{−sx}) + (t−s)(x e^{−sx} + x e^{−tx}) = e^{−sx} K((t−s)x)`;
* `PositiveJumpDatum` — a nonzero jump measure carried by `(0,∞)` with its admitted parameter set;
* `chirality_eq_integral` — **(FCRM.16b)**; `chirality_pos`, `chirality_antisymm`,
  `lt_iff_chirality_pos` — **(FCRM.15)** and **(FCRM.16c)**;
* `thirdCumulant_pos` — **(FCRM.14)**;
* the reusable `integral_pos_of_ae_pos`.

`EsscherFormationChirality` closes the bridge to actual relative entropies:
`llr_esscherLaw`, `klDiv_esscherLaw` (**FCRM.9**), `esscherDirected_nonneg` (Gibbs),
`klChirality_esscherLaw`, and the order core of Theorem 7.2,
`eq_id_of_strictMonoOn_of_iterate_id`.

## §6 — the abelian-zeta-gas realization

`GeometricModeChirality` proves that **one geometric occupation mode is exactly a compound-Poisson
formation**:

* `hasSum_modeLogPartition` — `−log(1 − a e^{−λt}) = ∑_{k≥1} (a^k/k) e^{−k t λ}`, i.e. the Laplace
  exponent of `∑_{k≥1} (a^k/k) δ_{kλ}`; `hasSum_modeLogPartition_sub` is the literal
  **(FCRM.17)** exponent relative to the untilted mode;
* `hasSum_modeFirstMoment`, `hasSum_modeChirality`, `modeChirality_pos`;
* `hasDerivAt_modeLogPartition`, `hasDerivAt_modeFirstMoment`, `hasDerivAt_modeSecondResponse` —
  the exact chain **(FCRM.21)** — with `modeSecondResponse_pos` and `modeThirdCumulant_pos`.

`AbelianZetaGasChemicalPotentialShift` identifies the corpus's fugacity shift with the mode Esscher
tilt: `ratio_fugacityShiftParameters` (`ratio_{τ+u}(m) = modeRatio (ratio_τ m) (log p) u`),
`coe_nnNormalizer_eq_exp`, `neg_log_nnNormalizer_eq_tsum_modeLogPartition`.

`AbelianZetaGasModeChirality` supplies the missing analytic input and assembles the source law:

* `ratio_le_half`, `summable_log_mul_ratio` (the log absorbed into a slightly smaller Euler
  exponent — the general-`θ` version of the card's majorant **(FCRM.22)**),
  `summable_log_mul_modeMean`;
* `socleExpectation_eq_ofReal`, `socleExpectation_ne_top`, `toReal_socleExpectation` — the socle
  expectation as a real mode sum;
* `gasLogPartition`, `gasFirstMoment`, `gasChirality`, `gasChirality_eq_tsum`,
  `gasChirality_eq_tsum_kernel` — **(FCRM.22b)** as the literal prime/depth/multiplicity series;
* `gasChirality_pos` — **(FCRM.20)**; `gasChirality_lt_iff` — the source chronology;
* `gasThirdCumulant`, `gasThirdCumulant_eq`, `modeThirdCumulant_gas_pos` — **(FCRM.18)**.

`AbelianZetaGasDirectedEntropy` converts this into relative entropies of the *actual* class laws:

* `classLaw_fugacityShift_eq_esscherLaw` — the shifted class law is the Esscher tilt of the base
  class law by `log|soc A|`;
* `klDiv_classLaw_fugacityShift` — **(FCRM.9)** for the gas;
* `klChirality_classLaw_fugacityShift` — the gas commutator *is* the directed KL asymmetry;
* `classLaw_fugacityShift_injective`.

## §7 — selection

* `fugacityShift_eq_of_involution` — **Theorem 7.1 / (FCRM.24)**;
* `centered_reversal_selection` — **(FCRM.25)**;
* `measurableEmbedding_of_finite_order`, `klChirality_map_of_finite_order`,
  `fugacityShift_finite_order_symmetry_id` — **Theorem 7.2 / (FCRM.27)**.

## Verification (2026-08-20)

All seven modules elaborate from the tree with `lean` on the project `LEAN_PATH` (no lake lock, no
full or umbrella build), 0 errors.  Every public `theorem`/`lemma` in them — 77 declarations in the
last full audit — reports only `propext`, `Classical.choice`, `Quot.sound` under `#print axioms`.
All seven are imported by `GaloisForLFunctions.HTGeometry.UniversalLawField`.

## Scope note on the admitted chamber

The card's Corollary 6.2 works on `J_{σ,τ} = (1−σ−τ, ∞)` and its literal source interval
`I_{σ,τ} = J ∩ [−τ, ∞)`.  The corpus's `AbelianZetaParameters` already encodes exactly that literal
source type (`0 < σ`, `0 ≤ τ`, `1 < σ + τ`), and the shift `fugacityShiftConv θ u (0 ≤ u)` ranges
over precisely the admitted chemical potentials at or above the base point.  The Lean statements are
therefore given on the literal source interval, as the card requires.

## Hostile boundaries kept

The Gaussian counterexample of Loop B is respected structurally: `formationKernel_pos` needs a
*positive* jump, and `modeThirdCumulant_pos` needs `λ > 0`; nothing in the development asserts
chirality for a general exponential family.  Loop H is respected literally: `hmono` alone only gives
a strictly increasing parameter map, and the identity conclusion uses finite order
(`eq_id_of_strictMonoOn_of_iterate_id`).
