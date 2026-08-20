# Universal-law-field FULL sweep ledger (all cards, incl. subfolders)

Started 2026-08-20.  Scope: every `.md` card under
`docs/drafts/pipeline/2-fully-proven/universal-law-field/`, **including subfolders** (127 cards),
per explicit user directive superseding the 2026-08-12 top-level-only scope correction.

A card is `DONE` only when every displayed theorem is closed unconditionally in Lean (no `sorry`,
no added axioms, no hypothesis interfaces standing in for the content), the modules are wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`, and the card plus a `-formalized.md`
companion have been moved to `docs/drafts/pipeline/3-formalized/universal-law-field/`.

## Status table

(rows appended as each card is audited/closed)

| # | Card | Status |
|---|---|---|
| 1 | `amplified-generative-response-mechanics/amplified-admission-depth-escape-and-reduction-pencil-law.md` | **DONE 2026-08-20** — promoted. New modules `HTGeometry/ReductionPencilKPositivity.lean` (Thm 2.1: `id⊗Φ_{n,c}` positive ⟺ `c ≥ min(k,n)`, both halves + maximally-entangled necessity, no Schmidt/SVD) and `HTGeometry/AmplifiedAdmissionGauge.lean` (AGR.1–AGR.4, AGR.7, AGR.12–AGR.14). Axiom-clean, umbrella-wired |
| 2 | `anti-equivariant-descent-mechanics/reflection-blind-descent-freezing-...-law.md` | **DONE 2026-08-20** — existing `HTGeometry/AntiEquivariantDescentFormation.lean` re-verified (elaborates, axiom-clean, umbrella-wired), all four laws covered; promoted |
| 3 | `asymptotic-law-core-mechanics/asymptotic-law-core-formation-...-law.md` | **DONE 2026-08-20** — `HTGeometry/ConstitutiveAsymptoticLawCore.lean` verified; promoted |
| 4 | `asymptotic-law-core-mechanics/strict-convex-nonlinear-exchange-...-law.md` | **DONE 2026-08-20** — `HTGeometry/ConstitutiveAsymptoticLawCoreRigidity.lean` verified; promoted |
| 5 | `triple-reporter-fusion/triple-reporter-fusion-additive-dissipation-...-law.md` | **DONE 2026-08-20** — `HTGeometry/ConstitutiveTripleReporterFusion.lean` verified; promoted |

## Verification recipe used for every "existing module" card

```
scratchpad/scr/verify.sh <Dotted.Module> <Namespace> <decl...>
```
elaborates the tree source with a bare `lean` on the project `LEAN_PATH` (no lake lock, no full
build), greps the umbrella imports, and prints `#print axioms` for every displayed capstone.
A card is promoted only when the source elaborates clean, every displayed theorem has a matching
declaration, the axiom print is `propext / Classical.choice / Quot.sound`, and the module is
reachable from `GaloisForLFunctions.HTGeometry.UniversalLawField`.
| 6 | `divisible-formation-potential-mechanics/quantized-proximity-approximate-formation-and-winding-selection-law.md` | **DONE 2026-08-20** — `HTGeometry/ConstitutiveApproximateFormationSelection.lean` verified; promoted |
| 7 | `formation-chirality-reversal-mechanics/observer-fibre-chirality-conservation-...-law.md` | **DONE 2026-08-20** — existing `ConstitutiveObserverFibreChirality` verified; §5's sufficient-statistic reduction was the real gap and is now closed by the new `HTGeometry/KLFactorizationSufficiency.lean` (factored densities are KL pair-sufficient; Esscher instance). Promoted |
| 8 | `formation-chirality-reversal-mechanics/formation-cumulant-chirality-and-involutive-selection-law.md` (ULF-FCRM-1) | **IN PROGRESS** — see the work plan below |

## ULF-FCRM-1 work plan (card 8)

Card was `[NO LEAN YET]`.  New modules landed so far:

* `HTGeometry/PositiveJumpFormationChirality.lean` — the universal kernel
  `K(a) = a − 2 + (a+2)e^{−a}`, `formationKernel_pos` / `_neg` / `_pos_iff` via
  `K'(a) = 1 − (a+1)e^{−a} > 0` (from `e^a > a+1`), the exact pointwise identity
  `2(e^{−tx} − e^{−sx}) + (t−s)(x e^{−sx} + x e^{−tx}) = e^{−sx} K((t−s)x)`, the
  `PositiveJumpDatum` bundle, `chirality_eq_integral` (**FCRM.16b**), `chirality_pos`,
  `lt_iff_chirality_pos` (**FCRM.16c**), `thirdCumulant_pos` (**FCRM.14**), plus the reusable
  `integral_pos_of_ae_pos`.
* `HTGeometry/EsscherFormationChirality.lean` — `llr_esscherLaw`, `klDiv_esscherLaw`
  (**FCRM.9**), `klChirality_esscherLaw` (the difference `2(F(t)−F(s)) + (t−s)(m(s)+m(t))`),
  and `eq_id_of_strictMonoOn_of_iterate_id` (the order core of **Theorem 7.2**).

Still to build for this card:

1. §4 (**FCRM.8**, **FCRM.10**, **FCRM.11**, **FCRM.12**) — the second/third-response calculus,
   under the card's own stated regularity (differentiation under the integral through order three).
2. §6 Theorem 6.1 / Corollary 6.2 — the abelian-zeta-gas realization.  Route: one geometric mode
   `φ(t) = −log(1 − a e^{−λ t})` is exactly the compound-Poisson log-Laplace of
   `ν = Σ_{k≥1} (a^k/k) δ_{kλ}` (the `−log(1−x) = Σ x^k/k` series), so per-mode chirality is the
   kernel integral; sum over `(p, j)` with the Dirichlet majorant already in
   `AbelianZetaGas/RelativeEntropy.lean` (`summable_primes_log_mul_ladderBound`).
3. §7 Theorem 7.1 — instantiate `klChirality_eq_zero_of_reversal`
   (`HTGeometry.ConstitutiveObserverFibreChirality`) against the chronology.

### ULF-FCRM-1 continuation record (2026-08-20)

Landed and umbrella-wired: `PositiveJumpFormationChirality`, `EsscherFormationChirality`,
`ExponentialFormationResponse` (§4: `jeffreysWork_eq_integral_secondResponse` = FCRM.10,
`formationChiralityAt_eq_integral_secondResponse` and `..._thirdResponse` = FCRM.11,
`directed_reconstruction` = FCRM.12), `GeometricModeChirality`
(`hasSum_modeLogPartition` = the mode Lévy series, `hasSum_modeFirstMoment`,
`hasSum_modeChirality`, `modeChirality_pos`), and
`AbelianZetaGasChemicalPotentialShift` (`shiftTau`, `ratio_shiftTau`
— `ratio_{τ+t}(m) = modeRatio (ratio_τ m) (log p) t` —, `coe_nnNormalizer_eq_exp`,
`log_nnNormalizer`).

**Remaining for §6 (Theorem 6.1 / Corollary 6.2), in order:**

1. `gasLogPartition θ t := −log ((shiftTau θ t).nnNormalizer)` and
   `= ∑' m, modeLogPartition (θ.ratio m) (log p_m) t`  — immediate from `log_nnNormalizer`,
   `ratio_shiftTau` and `tsum_neg`.
2. `(socleExpectation (shiftTau θ t)).toReal = ∑' m, modeFirstMoment (θ.ratio m) (log p_m) t`.
   The corpus has `socleExpectation_eq` (grouped by prime, in `ℝ≥0∞`) and
   `summable_primes_log_mul_tsum_modeMean` **only for `temperatureParameters`**; the general-`θ`
   summability majorant has to be added first (same Dirichlet majorant, `σ + τ > 1`).
3. The gas KL: `classMass θ A = ennNormalizer θ * ofReal (|A|^{-σ} |soc A|^{-τ})`, so
   `log (mass_s A / mass_t A) = log N_s − log N_t + (t−s) log|soc A|`; integrate against the
   discrete `classLaw` to get **FCRM.9** for the gas.
4. `gasChirality = ∑' m, modeChirality …` and `> 0` for `s < t` (**FCRM.20**, **FCRM.22b**), from
   `modeChirality_pos` plus summability.
5. **FCRM.18**: `κ₃(t) = ∑ (log p)³ r(1+r)/(1−r)³ > 0`.
6. **Theorem 7.1**: `klChirality_eq_zero_of_reversal` + the chronology.
   **Theorem 7.2**: `eq_id_of_strictMonoOn_of_iterate_id` + the chronology.
