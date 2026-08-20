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
| 8 | `formation-chirality-reversal-mechanics/formation-cumulant-chirality-and-involutive-selection-law.md` (ULF-FCRM-1) | **DONE 2026-08-20** — card was `[NO LEAN YET]`; seven new modules close §4, §5, §6 and §7 in full (see the companion in 3-formalized). Promoted |

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

### ULF-FCRM-1 — completed 2026-08-20

Seven new modules: `PositiveJumpFormationChirality`, `ExponentialFormationResponse`,
`EsscherFormationChirality`, `GeometricModeChirality`, `AbelianZetaGasChemicalPotentialShift`,
`AbelianZetaGasModeChirality`, `AbelianZetaGasDirectedEntropy`.  The route that made §6 tractable:
one geometric occupation mode is *literally* a compound-Poisson formation (the `−log(1−x) = ∑xᵏ/k`
series is its Laplace exponent), and the corpus's fugacity shift is exactly the mode Esscher tilt,
so the whole gas is a summable family of geometric modes.  The one analytic input the corpus lacked
was the general-`θ` log-weighted mode majorant, obtained by absorbing `log p ≤ pᵉ/ε` into a slightly
smaller Euler exponent.
| 15–16 | `tensor-polarization-amplification-mechanics/*` (2 cards) | **DONE 2026-08-20** — both modules re-verified, folder companion written; promoted |
| 17 | `bi-formation-interference-mechanics/reciprocal-hadamard-mixed-cumulant-...-law.md` | **DONE 2026-08-20** — the card's one recorded gap (Theorem 2.2 clause 4, quadratic mgf ⟹ Gaussian) closed by the new `HTGeometry/GaussianQuadraticCumulantCharacterization.lean` (analytic continuation on the strip `|Re z| < δ`, no Marcinkiewicz); promoted |
| 18 | `constitutive-parallax-mechanics/split-formation-parallax-...-law.md` | **DONE 2026-08-20** — the card's one recorded gap `(CPM.18)` closed by the new `HTGeometry/SplitFormationParallaxDistanceBound.lean`; promoted |
| 19 | `formation-admission-amplification-mechanics/fixed-envelope-family-...-law.md` | **DONE 2026-08-20** — `HTGeometry/FixedEnvelopeFormationAmplification.lean` verified, all 12 displayed results present; promoted |
| 20 | `source-selected-fock-interaction-mechanics/ramification-fock-filtration-...-law.md` | **DONE 2026-08-20** — `HTGeometry/ConstitutiveRamificationFockExcessSelection.lean` verified (Thm 2.1, §3, Thm 4.1, Thm 5.1 all present); promoted |

## Cards audited and found to need more Lean (precise TODO)

| Card | What is missing |
|---|---|
| `law-history-spectral-mechanics/pagewise-hodge-formation-properness-and-stable-organ-selection-law.md` | The existing `ConstitutivePagewiseFormationSelection` carries only the finite **diagonal** normal form (§3–§5). Theorem 2.1 `(PHF.9)`–`(PHF.11)` (the orthogonal death-page flag `K₁ = ⊕ L_r⁺ ⊕ K_∞`, its countable closure form, and the Pythagoras conservation) and Corollary 2.2 `(PHF.12)` are **not** formalized. Needs: nested closed subspaces, `Submodule.orthogonal` complements inside a subspace, an orthogonal-family Hilbert sum, and the induced page isomorphism `K_r/K_{r+1} ≅ L_r⁺ ≅ L_r⁻ ≅ C_r/C_{r+1}` |
| `species-relative-formation-mechanics/three-slot-exchangeability-descent-...-law.md` | `ConstitutiveExchangeableFormationSelection` is entirely at the **reporter/scalar** level. Theorem 2.1 `(EFD.4)` `D(α‖β) = D(p‖q) + D(q‖p)` for the three-slot product laws, Corollary 2.2 `(EFD.5)`, Theorem 4.1 `(EFD.11)` recovery neutrality and the KL form of Theorem 5.1 are **not** formalized. Needs: finite-alphabet product measures and their `klDiv`, plus the chain rule already present in `ConstitutiveFunctionalEquationPacketLift` |
| `ternary-formation-interference-mechanics/symmetric-formation-homology-...-law.md` | `ConstitutiveSymmetricFormationHomology` carries the charge/overlap core only. Card's own gate is `[~]`: **explicit chain-complex permutation isomorphisms, reporter duality (Thm 5.1), the positive Hodge carrier (Thm 6.1) and the Fisher-nullity realization remain open** |
| `generative-response-mechanics/fourier-kernel-admission-...-law.md` | `FourierKernelAdmission` carries the five finite laws. **The analytic finite-measure statements `(FKA.6)`–`(FKA.23)` are not Lean theorems** |
| `route-q-ratio-gate-decision.md` | Mechanism fully certified in `DivisorHeightRatioGate`. The two residual inputs are a **verified-zero numerical computation** (`γ₁ > 9`) and a signed-moment lower bound from zero locations — excluded by this session's Lean rule 4 (no computations). Decide explicitly when the card is reached |
| `nonvacuous-independence-and-polarization-import-law.md` | Quantitative core certified (`SelbergSpectralParameter`). Remaining clauses need a **hyperbolic-surface spectral layer** (Laplace spectrum on `Γ\ℍ`, Eisenstein series, Maass–Selberg, Selberg trace formula and zeta) absent from mathlib and the corpus |

### Standing note on the audit

A dump of every remaining card's Lean/Gates sections is regenerated with
`python3 - <<'PY' ... PY` over `2-fully-proven/universal-law-field` (see the sweep session log);
most cards state their own residual obligation explicitly in a `## … Lean …` section, and a large
minority record "no Lean file was written in this research pass", i.e. the whole card must be
built from scratch.
| `local-exponential-test-closure-mechanics/local-exponential-complete-order-fusion-...-law.md` | **PARTIAL, advanced 2026-08-20.**  Theorem 2.1 = `dense_polySubmodule`; Theorem 3.1 forward = `re_matQuad_blockHankel_nonneg`; **Theorem 3.1 converse and Corollary 3.2 now closed** in the new `HTGeometry/LocalExponentialSignConeConverse.lean` (`ae_posSemidef_of_forall_blockHankel_nonneg`, `ae_posSemidef_iff_forall_blockHankel_nonneg`, `exists_blockHankel_neg_of_not_ae_posSemidef`).  Still to build: Lemma 4.1 (rational phases dense in `L²(μ;ℂ^d)` — needs Fourier uniqueness for a finite complex measure), Theorem 4.2 (three-way equivalence), Theorem 5.1 `(LEF.18)`–`(LEF.19)` (immediate from 4.2), Theorem 6.1 (Euler-shell realization), Theorem 7.1 (no uniform finite depth) |
| `c1-o-open-core-reduction-theorem.md` (ULF-MECH-3) | Components (A)–(C) are in-tree (`XiWeilResolventSource`, `XiQuotientRealDecay.tendsto_primeArchSource_packetSum_of_tendsto`, `CCMPublishedRestrictedWeilMatrix`). **(D) is the card's own new lemma and is not in the tree**: a tent test's evaluation vector lies in `RHTower.XiWeilSquareSummable`. Needs the tent transform's `γ^{-2}` strip decay against Riemann–von Mangoldt counting. Clauses 1 and 3 of the reduction are then immediate (clause 3 is witness transport along an equality); clause 2 is a typing statement about what the comparison reduces to |
