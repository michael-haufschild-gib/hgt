# Programme: formalize every stage-2 card in `2-fully-proven/leftovers` and `2-fully-proven/route TT`

- **ID:** stage2-leftovers-route-tt-formalization-programme-2026-10-16
- **Stage:** 1-in-progress (tracker; it is not itself a theorem card)
- **Goal:** every proven theorem on the eleven cards below gets an unconditional Lean proof (standard
  axioms only, no premises standing for analytic inputs), wired into its umbrella and audited with
  `lake env lean`; then each card moves to `3-formalized`.

## Rules in force
- One single-threaded Lean process at a time, foreground: `lake env lean -j 1 <file>` for audit;
  an olean only via `lake --old env lean -j 1 -o <olean> -i <ilean> <file>`, module by module.
  Never `lake build` (it runs parallel jobs; OOM). No umbrella or full builds; wire by `cat >>`.
- No computations; no heartbeat raising; scratch files in the session scratchpad.
- Search the corpus before writing any new declaration.

## Card ledger

| # | card | paper content | Lean state at start (2026-10-16) | next step |
|-|-|-|-|-|
| 1 | leftovers/finite-weil-adjacent-nodal-transport | adjacent coupling for every strictly increasing node family | canonical log nodes only | **DONE 2026-10-17** → 3-formalized (`FiniteWeilNodalAdjacentCoupling`, `FiniteWeilNodalMixtureTransport`) |
| 2 | leftovers/lee-yang-prime-pivot-dual-spectrum | spin partition, spectrum, converse chain, wall bound, signed coefficient | two-wall core | **DONE 2026-10-17** → 3-formalized (`LeeYangPrimePivotSpinPartitionSpectrum`) |
| 3 | route TT/tt-boundary-quadratic-norm-orientation | C78 norm/trace orientation at the boundary | `/tmp` drafts lost | **DONE 2026-10-17** → 3-formalized (`ThetaCuspRatioBoundaryNormOrientation`, `...SourceSlopeReal`, `...BoundaryNormInterior`) |
| 4 | route TT/route-tt-structural-theorems-2026-10-14 | T1–T7, L1–L14 | T4 corpus lemma, T1 at convexity rung, T7, L10, L12 §2, L13 | audit each item; T3, T2, L1, L3 … |
| 5 | leftovers/weil-cone-pole-duality-anatomy | (A) modular/Dirichlet fat cones, (B) factorization, (C) function fields | Krein–Milman reduction; Dirichlet symbol positivity (CANNOT-539) | Weil functionals for L(s,f), L(s,χ), curves |
| 6 | leftovers/twisted-minimum-principle | primal TMP construction (C1)–(C4), Steps 1–6 | TMP proved by dual route; Steps 1, 5 pieces | Dirichlet problem on modular strip, corner Martin kernel, Green identity |
| 7 | leftovers/smooth-stein-order-two-autonomous-ade-frequency-rank | Stein surface minimal hull dim ≤ 2 | none | CR/contact geometry, Levi-flat obstruction, Weinstein (Taubes) |
| 8 | leftovers/nonvacuous-independence-and-polarization-import-law | B′ clauses 1–3 | clauses 1–2 proved (`exists_finiteIndex_small_eigenvalue`) | clause 3: Selberg zeta zero at s_j |
| 9 | leftovers/verified-height-one-zero-turing-extension | RH through T₁ = T₀ + 111/256 | consumer theorems only | conflicts with "no computations" (needs Platt–Trudgian + Turing certificate) |
| 10 | leftovers/route-e-cofactor-amplified-e3-token-supply | E₃ token supply | elementary layers, MT mean-square bricks | Matomäki–Teräväinen Thm 1.2 |
| 11 | leftovers/route-e-forbidden-support-e3-stability | MT all-interval E₃ with forbidden support | elementary perturbation layer | Matomäki–Teräväinen Thm 1.2 |

## Log
- 2026-10-16 — ledger created after reading all eleven cards. Started card 1.
- 2026-10-17 — cards 1, 2, 3 formalized, audited (standard axioms), wired, moved to 3-formalized.
  Build rule after user correction: never `lake build` (parallel jobs → OOM); oleans only via
  `lake --old env lean -j 1 -o … -i …`, one module at a time; audits with `lake env lean -j 1`.
  The 25 C75–C77 upstream oleans card 3 needed were built that way.

## Card 4 (route-tt-structural-theorems) item ledger — 2026-10-17

Proven items (formalization targets):
- T1 cone-existence ladder: corpus has the convexity rung in Herglotz form
  (`exists_herglotz_trivialWeights_boosted`, boost `c(s+½)^θ`); TODO: parametric-μ₊ version and the
  Weil-cone form with density `Ω + C(1+|t|)^θ` (pointwise `Re(1+it)^θ ≤ (1+|t|)^θ` + modified bridge).
- T2 gap-weighted carrier (parametric θ₂): TODO (partial summation / continuation).
- T3 invariant forms: simple-zero core exists (`nonempty_positiveInvariantForm_iff`,
  `eq_conj_of_invariant_ne_zero`); TODO: jet components for multiple zeros (correction) and the
  statement over the actual zero set of Ξ.
- T4 depth blindness: TODO corollary of `integral_horizontal_shift_of_upper_inv_one_add_sq_decay`
  (both signs of `β - ½`).
- T5 Ruelle zeta quasi-RH (Ruelle–Pollicott), T6 analytic Ruelle zeta zero-free (nuclear
  Fredholm determinants): TODO, large infrastructure.
- T7: DONE in corpus (MUST-1442).
- L1 Maass–Selberg resonance identity; L2 E* Fourier expansion + Hecke factorization
  `2ζ(2s)E(i,s) = 4ζ(s)L(s,χ₋₄)`: TODO.
- L3 archimedean decomposition, completely monotone kernel, PD positivity, anomaly window, Selberg
  Plancherel density: TODO (check `weilArchRe_eq_levy_pole`).
- L5 (i) `ξ(0) = ξ(1) = ½`; (ii) positive measure `2cosh(x/2)+ε cos(γ₁x)` argument: TODO.
- L6 pencil obstruction; L7 Davenport–Heilbronn (cited theorem, large): TODO.
- L10 twin rigidity (paper) + unconditional corollary: TODO; [L] parts DONE (`weilPositiveDegree_iff`,
  `forall_re_weilDegreePoleFunctional_nonneg_iff`).
- L12 §1 second clause (no compactly supported test is Ξ²-divisible), §3 exact archimedean form,
  §4 keystone reduction: TODO; §2 DONE in corpus.
- L13: DONE in corpus (MUST-1458/1463).
- L14 1 (pole-negative violators), 2 (dilation continuity, PBAP(1) ⟹ PBAP(1/k), PBAP(½) theta
  datum), 3 (Markov + pole, sinh-capacity criterion), 4 (cores = wandering vectors, Farkas dual),
  5 (`e^{|Ω(0)|} = 8π e^{γ+π/2}`), 6 (`Ω ≥ Ω(0)`): TODO.
Not proven theorems on the card (no formalization obligation, recorded as such): the
"structural laws for the PBAP lane" addendum (marked heuristic); L4, L8, L9 (named heuristic
obstructions); L11 index law and L12 §1 first clause (paper with an explicitly stated unproved
C^k-approximation gap); the conjectured quasi-RH ladder in L14.2; core existence (open) in L14.4.
- 2026-10-17 card 4 progress: T4 DONE (`TranslationAveragedDensityDepthBlindness`:
  `integral_translationAveraged_depth_blind`, both shift directions). `ArchimedeanAnomalyConstantLaws`:
  L5(i) `XiC_pole_points`; L14.5 `gammaBracket_zero_eq`, `exp_abs_gammaBracket_zero`; L14.6
  `gammaBracket_zero_le`/`gammaBracket_mono`; L3 `weilArchRe_eq_autocorrelation_form`,
  `exp_half_div_sinh_eq`, `hasSum_archLevyDensity`, `completelyMonotone_archLevyDensity`,
  `plancherelDensity_nonneg`; L14.1 `weilArch_sub_pole_ge`, `pole_lt_of_violation`,
  `weilArchRe_nonneg_of_pole_heavy` (exact constant `|A(0)| = γ+π/2+log 8π`). Remaining in L3: the
  anomaly window `A < 0 ⟺ |t| < t₀`, `t₀ > 2π` (needs `Re ψ(¼+iπ) < log π`, margin ≈ 1.6e-3).
- 2026-10-17 card 4: T3 with the multiplicity correction DONE (`ZeroAlgebraJetInvariantForms`):
  jet model of `O/(Ξ)` with `M_q` = character × unipotent; support law
  `invariantForm_eq_zero_of_ne_conj` (via `exists_rat_exp_ne_one`, `2^a ≠ 3^b`); PSD radical
  `invariantForm_higherJet_radical`; `posDef_invariantForm_real_simple`; `valueForm`
  (best-possible PSD form); `exists_posDef_invariantForm_XiC_iff` (PD invariant form ⟺ RH ∧ simple
  zeros). Standard axioms; wired.
- 2026-10-17 card 4: L6 DONE (`HermitianPencilEulerFactorObstruction`: real roots of `det(B+tH)`,
  `riemannHypothesis_of_XiC_eq_det_pencil`, resolvent trace continuous off ℝ,
  `not_pencilResolventTrace_eq_eulerFactor`). Standard axioms; wired.
- 2026-10-17 card 4: T2 DONE (`PrimeGapDirichletContinuation`, namespace `RHTower.PrimeGapDirichlet`):
  `GapMomentBound θ` (Σ_{p_k≤X} g_k² ≤ C X^{1+θ}); `GapMomentBound.nonneg`;
  `gapMomentBound_of_eventually_gap_le`, `gapMomentBound_one` (Bertrand), `gapMomentBound_hoheisel`
  (θ = 71/100, corpus Hoheisel supply); Abel summation `summable_gap_sq_mul_rpow`;
  `exists_gapDirichlet_continuation` (D = 1/(s−1) + G, G holomorphic on Re s > θ),
  `differentiableOn_gapDirichletCont`, `tendsto_sub_one_mul_gapDirichletCont` (residue 1, θ < 1),
  `norm_gapDirichletCont_critical_le` (θ < ½ ⟹ |D(½+it)| ≤ C(1+|t|)),
  `gapDirichlet_continuation_hoheisel` (unconditional instance). Standard axioms; wired.
  Recorded: Heath-Brown's admissibility of 5/18+ε is a cited literature input, not proved on the card;
  the card's "≍ |t|" lower half has no paper proof (only ≪ is a theorem).
