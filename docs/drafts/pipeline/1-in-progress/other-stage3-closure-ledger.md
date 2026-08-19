# Other scientific-knowledge Stage-3 closure ledger

- **ID:** `other-stage3-closure-ledger`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAM
- **Scope:** Every paper card in `2-fully-proven/new_scientific_knowledge/other`
- **Completion criterion:** Every Stage-2 ID has a matching Stage-3 certificate covering its exact unconditional Lean theorem.
- **Lean constraints:** No hypotheses replacing theorem content; no `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe`; targeted foreground checks only.

## Certified before current closure pass (15)

- [x] `boundary-wedge-uniform-ht-dimension-gap`
- [x] `bounded-relation-log-magnitude-hypertranscendence`
- [x] `charged-scalar-core-fixed-current-torsor`
- [x] `coordinate-intrinsic-fusion-kolchin-principal-filter-law`
- [x] `gaussian-torsion-language-hypertranscendence`
- [x] `primitive-fibre-modular-renormalization-law`
- [x] `ramsey-weyl-causal-phase-law`
- [x] `route-c2-zero-safe-current-multiplicity-tomography`
- [x] `shift-one-seam-power64-cassini-jensen`
- [x] `split-source-boundary-universality`
- [x] `theta-cusp-calibrated-power-reciprocal-first-moment-law`
- [x] `torsion-universal-phase-polynomial-magnitude-hypertranscendence`
- [x] `von-mangoldt-bivariate-marginal-trace-lock-no-go`
- [x] `von-mangoldt-toeplitz-countertrace-regularity-no-go`
- [x] `wold-sieve-normal-cone-von-mangoldt-current`

## Closure queue (50 at start; checked entries closed during this pass)

- [x] `abelian-multiplication-tail-manin-horizon`
- [x] `active-quasi-abelian-palette-exact-ht-dimension-classification`
- [x] `additive-heat-aperture-shifted-zeta-echo-ladder`
- [x] `additive-heat-aperture-zeta-zero-echo`
- [ ] `all-depth-compatible-pair-face-differential-matroid`
- [ ] `all-depth-pair-face-signature-completeness`
- [ ] `all-order-multiple-sine-stanley-reisner-differential-matroid`
- [ ] `almost-periodic-autonomous-ade-finite-frequency-law`
- [ ] `almost-periodic-implicit-ade-relative-frequency-law`
- [ ] `archimedean-relative-prime-cocycle-curvature`
- [x] `barnes-differential-source-face-matrix-factorization`
- [ ] `bessel-order-intensity-hypertranscendence`
- [x] `complete-scalar-persistent-gauge-reduction`
- [ ] `critical-half-density-prime-tail-resolvent-law`
- [ ] `differential-variational-building-balance-law`
- [x] `double-sine-defect-coset-differential-matroid`
- [x] `double-sine-translation-annihilator`
- [x] `eigenplurivolume-log-crepant-orbifold` — 2026-08-16, `schemeEigenPluriVolume_logCrepant`
- [ ] `embedded-manin-horizon-isogeny-reconstruction`
- [ ] `finite-archimedean-gamma-product-boundary-law`
- [ ] `fixed-divisor-full-complex-translation-freeness`
- [ ] `floquet-orbifold-tail-emergence`
- [ ] `gauss-component-quasi-inner-residue-hierarchy`
- [ ] `irrational-triptic-source-effectivity-character`
- [ ] `isogeny-tail-maurer-cartan-holography`
- [ ] `jet-horizon-translation-gauge-classification`
- [ ] `noncompact-period-quotient-facet-escape-law`
- [x] `nonlinear-rational-observation-curve-horizon-reconstruction` — 2026-08-16, `exists_differentialAdjoin_jetFamily_eq`
- [x] `nonreal-factorial-slope-formal-hypertranscendence`
- [ ] `orbifold-tail-holographic-reconstruction`
- [ ] `periodic-pencil-intrinsic-ht-dimension-two`
- [x] `power-canonical-product-exact-moment-borel-lattice-law`
- [x] `prescribed-gap-process-order-one-maximal-ht-profield` — 2026-08-16, `exists_prescribedGapProcess_orderOneMaximalHTProfield`
- [x] `prime-completion-annihilates-hypertranscendence-at-even-temperature` — 2026-08-16, `cexp_neg_logSeries_eq_primeOccupationFacePow` + 7 more
- [ ] `prime-euler-unit-tangent-completeness`
- [ ] `prime-modulated-weyl-idealizer-collapse-on-xi-sampling`
- [ ] `prime-occupation-polarized-gamma-phase-survival`
- [ ] `prime-tail-hedenmalm-wiener-hopf-transgression`
- [ ] `prime-tail-reflection-folded-second-order-resolvent`
- [x] `prime-valuation-dyadic-fermion-normal-cone-law` — 2026-08-18, `tendsto_criticalGeometricAffinity`, `tendsto_profileParityAffinity`, `coherentKernel_quadForm_nonneg`, `hasSum_dyadicFisher`, `tendsto_halfNormalExactScale`
- [x] `prime-wold-accelerated-type-modular-drift-law` — 2026-08-18, `norm_finitePrimeGenusOnePolarizedPhase_two_sided` + `norm_burnolExtendedSoninEvaluationVector_soninDepth_bounds`
- [ ] `projective-prime-weyl-leakage-fock-normal-cone`
- [ ] `rational-coarse-graining-orbifold-tail-classification`
- [x] `scalar-differential-inversive-core-projective-law`
- [x] `scalar-ht-horizon-celestial-sphere` — 2026-08-16, `scalarHorizon_celestialSphere_realization`
- [ ] `symmetry-caged-fixed-divisor-full-orbit-freeness`
- [x] `toric-log-calabi-yau-tail` — 2026-08-16, `toricPowerIsogenyTail`
- [ ] `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`
- [ ] `universal-first-order-entire-cascade-unit-cost`
- [ ] `weighted-euler-tangent-global-graph-decoupling`

## Audit log

- 2026-08-08 — corrected exact-ID inventory after auditing nested Stage-3 certificates: 65 paper cards, 15 already certified, 50 unresolved. Existing certificates remain linked to their Stage-2 paper proofs; paper cards are not moved or deleted.
- 2026-08-08 — `double-sine-translation-annihilator` closed: exact unconditional imaginary-ray annihilator, direct Lean check, targeted module build, standard Lean axioms only.
- 2026-08-08 — `double-sine-defect-coset-differential-matroid` closed: unconditional pointed-coset defect matroid, exact nonzero-class rank, and exact finite `ℂ(δ)` operator-row rank over `ℂ(z)`. Direct checks and both targeted module builds passed; capstones use only standard Lean axioms. Global lint reached unrelated concurrent umbrella gaps; targeted forbidden-token audit passed. Closure count: 17/65 certified, 48 remaining.
- 2026-08-08 — `scalar-differential-inversive-core-projective-law` closed: unrestricted differential Lüroth, stable-core surjectivity, hypertranscendental generator, exclusive base-versus-projective dichotomy, Möbius action, and uniqueness up to scalar assembled in Lean. Direct check and targeted build passed; all capstones use only standard Lean axioms. Closure count: 18/65 certified, 47 remaining.
- 2026-08-08 — `complete-scalar-persistent-gauge-reduction` closed: canonical erased/nonerased stable-core XOR; complete pairwise-exclusive `1`, `mu_N`, `G_m`, `G_a` classification; exact fixed fields, boundary hypertranscendence, reconstruction, rank-one equations, Galois groups, universal Schwarzian boundary, and charged-clock compatibility. Direct checks and targeted capstone build passed; standard Lean axioms only. Global lint reports only unrelated concurrent umbrella gaps. Closure count: 19/65 certified, 46 remaining.
- 2026-08-08 — `barnes-differential-source-face-matrix-factorization` closed without replacing derived restriction by a surrogate: exact principal free resolution, faithful polynomial-to-Laurent operator embedding, exact extension of the analytic Barnes annihilator to `(f_N)` in `C[delta,T_1^(+-1),...,T_N^(+-1)]`, selected-face two-periodic factorization, and all-degree nonempty-face Tor law. Direct Lean checks and targeted capstone build passed; all capstones use only standard Lean axioms. Closure count: 20/65 certified, 45 remaining.
- 2026-08-08 — `nonlinear-rational-observation-curve-horizon-reconstruction` progress: exact unconditional Lemma 2 is now closed in Lean, including algebraic-branch rigidity, finite normal-closure embedding rigidity, and `C<r(x),x_n> = C<x>` for every nonconstant rational `r` and every positive `n`. Direct checks and targeted builds pass; capstone axioms are only `propext`, `Classical.choice`, and `Quot.sound`. Card remains open solely for the principal-symbol/Luroth layer and resulting affine/non-affine classification; closure count unchanged at 20/65.
- 2026-08-09 — `noncompact-period-quotient-facet-escape-law` advanced, not yet closed. Formalized
  unconditionally: the three period-escape conditions (`IsEscapeSubgroup`), the periodic-pencil
  escape group with its exact identity component `ker ℓ` and its noncompact quotient
  (`EscapeSubgroup.lean`); the invariant `peDim` and the constructive inequality `peDim ≤ ppDim`
  (`PeriodEscapeDimension.lean`); the exact one-dimensional escape bound — an escape subgroup of
  `ℂ` contains no two `ℚ`-independent elements — hence `peDim(Δ_wedge) = 2` for every `r,s ≥ 2`
  (`BoundaryWedgePeriodEscape.lean`); and the noncompact period-quotient law itself in one complex
  variable (`MeroPeriodQuotient.lean`), from the corpus's elliptic differential-algebraicity
  theorem. All four modules are umbrella-wired, direct checks and targeted builds pass, and every
  capstone's `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound`.
  Remaining for this card: several-variable meromorphic period groups (needed for `peDim ≤ htDim`)
  and the Siegel bound `trdeg_ℂ M(X) ≤ dim_ℂ X` for compact complex tori (needed for the law in
  dimension `≥ 2`). Closure count unchanged at 20/65 certified, 45 remaining.

## Named infrastructure sub-projects blocking several cards

These are the large analytic layers that several remaining cards share. Each is missing from
mathlib and from this tree; none is an axiom or a hypothesis anywhere.

1. **Siegel bound for compact complex tori** — `trdeg_ℂ M(ℂ^n/Λ) ≤ n`. Blocks the noncompact
   period-quotient law in complex dimension `≥ 2`. In dimension one the corpus already owns the
   equivalent statement (`differentialAlgebraicOver_of_translation_fixed`).
2. **Several-variable global meromorphic germ field** — the `d`-variable analogue of `meroField`,
   with translation equivalences, period groups, closedness of a period group, and the identity
   theorem. Blocks the facet period-escape theorem and every `ℂ^d` HT realization statement.
3. **Formal transseries model of the shifted Gamma field `K_E`** — the injection
   `K_E → ℂ(log s)((s^{-1}))[Γ^{±1}]` giving every nonzero element a boundary datum without the
   `NoIntegerRelation` hypothesis. Blocks `archimedean-relative-prime-cocycle-curvature`, whose
   shift set is a rank-two lattice and therefore always carries integer relations.
4. **Dreyfus's differential-algebraic classification for rational linear shift equations** — blocks
   `bessel-order-intensity-hypertranscendence`, whose every other obligation is already closed.
5. **Autonomous rational-substitution tail classification (Casale)** — blocks
   `floquet-orbifold-tail-emergence`, `orbifold-tail-holographic-reconstruction`, and
   `rational-coarse-graining-orbifold-tail-classification`.
- 2026-08-09 (second pass) — `noncompact-period-quotient-facet-escape-law` reduced to a single
  missing theorem. Three further modules, all unconditional and axiom-clean:
  `ClosedSubgroupIdentityComponent.lean` proves that the identity component of a closed additive
  subgroup of a finite-dimensional real vector space is the largest real subspace it contains
  (`exists_line_of_not_discrete`, `idComponentSet_eq_lineSubmodule`), with the complex packaging
  `isEscapeSubgroup_of_isClosed`; `MeroPeriodEscape.lean` verifies all three period-escape
  conditions for the period group of a hypertranscendental global meromorphic germ in one complex
  variable (`mem_meroPeriodSubgroup_iff`, `isClosed_meroPeriodSubgroup`,
  `lineSubmodule_meroPeriodSubgroup_eq_bot`, `isEscapeSubgroup_meroPeriodSubgroup`);
  `SeveralVariableTranslation.lean` carries the period-group layer to an arbitrary complex normed
  space (`addTranslationMeroEquivGen`, `meroPeriodSubgroupGen`, `isClosed_meroPeriodSubgroupGen`,
  `complex_smul_mem_meroPeriodSubgroupGen`, `isEscapeSubgroup_meroPeriodSubgroupGen`).
  Named sub-project 2 below is therefore closed: the several-variable global meromorphic germ field
  was already corpus-owned as `Bottcher.analyticSubringGen` / `Bottcher.meroFieldGen` /
  `Bottcher.precompMeroEquivGen`, and the translations and period groups are now built on it. The
  card's single remaining gate is the Siegel bound for compact complex tori.
  Closure count unchanged at 20/65 certified, 45 remaining.

## Siegel bound for compact complex tori — scoping note

The single remaining gate of `noncompact-period-quotient-facet-escape-law`. Statement needed:

> a global meromorphic germ on `ℂ^n` whose period group has compact quotient is differentially
> algebraic over `ℂ(z)` for every constant directional derivation.

Reduction already available in Lean: `isEscapeSubgroup_meroPeriodSubgroupGen` makes the period group
closed with complex-linear identity component, so after quotienting by that component the period
group is a full lattice `Λ` and the statement is `trdeg_ℂ M(ℂ^n/Λ) ≤ n`.

Assets already in the tree, so this need not start from nothing:

- `HTGeometry/PolydiscAnalytic.lean` and `HTGeometry/PolydiscSeriesCoefficients.lean` own the
  several-variable Cauchy integral on a distinguished torus, term-by-term summation of dominated
  torus-integral series, the polydisc power series of a holomorphic function, and
  `analyticOnNhd_of_differentiable` in `ℂ^n`. mathlib has none of this.
- `Bottcher.analyticSubringGen` presents every meromorphic germ as a *global* quotient `A/B` of
  entire functions, so no Cousin II / local fraction representation is needed.

What the proof still needs, in order:

1. a polydisc Schwarz lemma — if all Taylor coefficients of total degree `< N` vanish then
   `‖f(c+y)‖ ≤ M·(‖y‖/R)^N` on the smaller polydisc; the clean route is the one-variable Schwarz
   lemma applied to `t ↦ f(c + t·y)`, which turns the multi-index hypothesis into a zero of order
   `N` at the origin;
2. a finite polydisc cover of one fundamental parallelotope of `Λ`;
3. the dimension count: the coefficient space of polynomials of degree `≤ m` in `n+1` variables has
   dimension `~ m^{n+1}`, the space of Taylor jets of order `< N` has dimension `~ N^n`, so a
   nonzero polynomial annihilating all those jets exists once `N ~ m^{1+1/n}`;
4. the periodicity step, which is where compactness is *essential*: the smallness bound on the
   small polydiscs is compared with the global supremum over the fundamental domain, which
   periodicity identifies with the supremum over the large polydiscs, giving `S ≤ θ^N S` and hence
   `S = 0`. Without step 4 the argument is false — the same count would otherwise prove `z` and
   `exp z` algebraically dependent on `ℂ`.

## Stale-frontier correction: the power-log PNT is already in the tree

`weighted-euler-tangent-global-graph-decoupling` ends with a 2026-07-24 route re-evaluation naming
`ψ(x) = x + O(x/log^B x)` as "THE remaining deep input", spun off to a card
`1-in-progress/pnt-power-log-error-quantitative-selberg.md` which does not exist. That frontier is
stale in two independent ways:

- `GaloisForLFunctions/RHTower/ChebyshevPsiPowerLogPNT.lean` proves
  `RHTower.exists_chebyshevPsi_power_log`: `|ψ(⌊x⌋) − x| ≤ C·x·exp(−c·(log x)^{1/10})` for `x ≥ x₀`,
  by Perron unsmoothing of the tent-sum estimate — strictly stronger than `O(x/log^B x)` for every
  `B`, since `exp(−c·L^{1/10})·L^B → 0`.
- the vendored `GaloisForLFunctions.PNTPlus.MediumPNT` gives the same error shape as a `BigO`
  statement, sorry-free and axiom-clean per `PNTPlus/PROVENANCE.md`.

The growing-order consumers were also built the same day:
`RHTower/GrowingOrderPrimeLogNodes.lean` (`exists_separated_primeLog_nodes_growing`) and
`RHTower/WeightedEulerGrowingPrimeOversampling.lean`
(`norm_le_ray_of_primeLog_sampled_decay_growing`), and the later
`RHTower/WeightedEulerAnnihilatorOversamplingCarrierEliminationUniversalityLaw.lean` (2026-08-03)
carries the annihilator elimination. So the card's own "NEXT" list must be re-audited against the
tree before any further mathematics is attempted on it: the deep input it is waiting for is
already owned twice.
- 2026-08-09 (third pass) — `weighted-euler-tangent-global-graph-decoupling` unblocked at its stated
  frontier. Its own no-go `not_beta_lt_min_sigma_half_alpha_of_nonempty_positiveStrip` shows the
  fixed-order carrier elimination is vacuous; the growing-order replacement is now built and is not:
  `HTGeometry/SampledRayRateTransferGrowingHalfplane.lean`
  (`norm_le_ray_of_sampled_decay_halfplane` — the growing-order transfer for functions analytic only
  on a right half-plane, which is what a Lambert transform is) and
  `RHTower/WeightedEulerGrowingCarrierElimination.lean`
  (`compactFourierBorel_eq_zero_of_lambert_ray_decay`,
  `norm_le_ray_of_primeLog_sampled_decay_growing_halfplane`,
  `compactCarrierLambertTransform_analyticAt_pos`,
  `compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_growing`). The rate hypothesis is now
  `β < σ` instead of the impossible `β < min σ (α/2)`; the node density `c = min (α/(8M)) ((σ−β)/12)`
  is chosen inside the proof so the `6c` interpolation loss still leaves `σ − 6c > β`. All
  unconditional and axiom-clean, both modules umbrella-wired. Closure count unchanged at 20/65
  certified, 45 remaining.
  Follow-up the same day: `compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical`
  instantiates the growing-order law at the critical dual rate `σ = 1`, where the card's own carrier
  geometry (`Re s < 1`) supplies `β < σ` for free. That is the card's `(7) → (14) → (16)` chain at
  the critical boundary, closed unconditionally. The remaining work on that card is the joint
  product-space capstone `(3)` and the `(18)`/`(19)` corollaries, with no analytic input left.

## Convolution norm inequality — a shared missing brick

`prime-tail-hedenmalm-wiener-hopf-transgression` Theorem 1 asserts that the half-line theta
operators `T_±, C, S : L²(ℝ₊) → L²(ℝ)` are bounded with `‖T_±‖ ≤ ‖k‖₁`. That is Young's convolution
inequality `L¹ ⋆ L² → L²`, and **neither mathlib nor this tree has any convolution norm
inequality** — `grep` over `Mathlib/Analysis/Convolution.lean` and `LConvolution.lean` finds no
`eLpNorm_convolution_le` and no Young statement, and the corpus's own convolution lemmas are all
pointwise or arithmetic.

The cheap route avoids Minkowski's integral inequality (also missing): Cauchy--Schwarz against the
weight `|k| dy` gives `(∫|k(y)||f(x−y)|dy)² ≤ ‖k‖₁ · ∫|k(y)||f(x−y)|²dy`, and Tonelli plus
translation invariance of Lebesgue measure turns that into `‖k ⋆ f‖₂² ≤ ‖k‖₁²‖f‖₂²`. Stating
everything in `ℝ≥0∞` removes every integrability side condition.
`HTGeometry/YoungConvolutionL2.lean` carries this.

### Siegel step 1 — the exact mathlib tools located

The polydisc Schwarz lemma is the first brick, and both mathlib inputs it needs are now identified:

- `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` (`Mathlib/Analysis/Complex/Liouville.lean`)
  — **Cauchy's estimate**: `‖iteratedDeriv n f c‖ ≤ n! · C / R^n` for `f` differentiable on
  `ball c R`, continuous on its closure, with `‖f‖ ≤ C` on the sphere.  This gives the coefficient
  bound `‖a_k‖ ≤ C/R^k`, and summing `∑_{k ≥ N} (C/R^k)|t|^k = C(|t|/R)^N/(1 − |t|/R)` is the
  one-variable order-`N` Schwarz lemma.  Note the hypothesis is on a *sphere*, so no maximum
  principle is needed.
- `norm_le_of_forall_mem_frontier_norm_le` — the maximum modulus principle, if the annulus route is
  preferred instead.

`AnalyticAt.order` does **not** exist under that name, and there is no
`Complex.norm_cauchyPowerSeries_apply_le`; the coefficient bound must come from Cauchy's estimate
above, not from a formal-series API.  The multi-variable step is then the slice
`φ(t) = F(c + t·u)` with `‖u‖ = 1`, which stays in the polydisc for `|t| < R` and whose derivatives
at `0` vanish to order `N` exactly when the total-degree-`< N` jets of `F` do.

### Siegel step 1a — DONE

`formal/GaloisForLFunctions/HTGeometry/OrderNSchwarz.lean`:

> **`norm_le_of_iteratedDeriv_vanish`** — for `f` differentiable on `ball 0 R`, continuous up to the
> closure, with `‖f‖ ≤ C` on the boundary circle and `iteratedDeriv k f 0 = 0` for every `k < N`:
> `‖f t‖ ≤ C·(‖t‖/R)^N / (1 − ‖t‖/R)` on the open disc.

Unconditional, `#print axioms` clean, umbrella-wired. The proof is `Complex.hasSum_taylorSeries_on_ball`
together with `Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`: the `n`-th coefficient
has norm at most `C/R^n`, the first `N` vanish, and `Summable.sum_add_tsum_nat_add` reindexes the
remaining series onto the geometric tail. No maximum principle and no removable-singularity
argument is needed.

Next: step 1b, the polydisc version, by restricting to the complex line `t ↦ c + t·u` with
`‖u‖ = 1` — the line stays inside the polydisc for `|t| < R`, and the total-degree-`< N` jets of `F`
at `c` vanish exactly when the derivatives of the restriction vanish at `0` to order `N`. Then
steps 2–4 (polydisc cover of a fundamental parallelotope, the dimension count, and the periodicity
step).

### Siegel step 1b — DONE

Same module, `norm_le_of_slice_iteratedDeriv_vanish`, for an arbitrary complex normed space `E`
(so `ℂ^n` in particular):

> `F` differentiable, `‖F(c+w)‖ ≤ C` for `‖w‖ ≤ R`, and for every unit `u` the restriction
> `t ↦ F(c + t·u)` has vanishing derivatives of every order `< N` at `0`
> ⟹ `‖F(c+y)‖ ≤ C·(‖y‖/R)^N / (1 − ‖y‖/R)` for `0 ≠ y` with `‖y‖ < R`.

The line through `c` in the direction `y` stays inside the ball for `|t| ≤ R`, so the one-variable
lemma applies to the restriction at `t = ‖y‖`. Unconditional, axiom-clean, umbrella-wired.

The hypothesis is stated on the *slices* rather than on the multi-index jets, which is honest and is
what the geometry supplies. The remaining bridge, when the dimension count is set up in multi-index
form, is `iteratedDeriv k (fun t => F (c + t·u)) 0 = iteratedFDeriv ℂ k F c (fun _ => u)` — the
chain rule for the affine map `t ↦ c + t·u`. Steps 2–4 (polydisc cover of a fundamental
parallelotope, the dimension count, the periodicity step) are untouched.

### Siegel step 1 — complete, in multi-index form

`OrderNSchwarz.lean` now also carries the bridge and the jet-form statement, so step 1 no longer
owes anything to steps 2--4:

- **`iteratedDeriv_slice_eq`** — `iteratedDeriv k (fun t => F (c + t·u)) 0 = iteratedFDeriv ℂ k F c (fun _ => u)`
  for `ContDiff ℂ ⊤ F`; the composition `t ↦ c + t·u` is the continuous linear map
  `smulRight 1 u` followed by a translation, so
  `ContinuousLinearMap.iteratedFDeriv_comp_right` and `iteratedFDeriv_comp_add_left` do it.
- **`norm_le_of_iteratedFDeriv_vanish`** — the polydisc Schwarz lemma with the hypothesis in the
  form the dimension count produces: `∀ k < N, iteratedFDeriv ℂ k F c = 0` gives
  `‖F(c+y)‖ ≤ C·(‖y‖/R)^N/(1 − ‖y‖/R)`.

All four declarations in the module are unconditional and axiom-clean, and it is umbrella-wired.
Remaining for Siegel: step 2 (a finite polydisc cover of one fundamental parallelotope of `Λ`),
step 3 (the `m^{n+1}` versus `N^n` dimension count, with `N ~ m^{1+1/n}`), step 4 (the periodicity
comparison `S ≤ θ^N S`).

### Siegel step 3 (abstract core) — DONE

`formal/GaloisForLFunctions/HTGeometry/KernelOfDimensionDrop.lean`:

- **`exists_ne_zero_apply_eq_zero_of_finrank_lt`** — a linear map into a space of strictly smaller
  finite dimension kills a nonzero vector (rank--nullity plus `finrank_pos_iff`);
- **`exists_ne_zero_forall_apply_eq_zero_of_finrank_lt`** — the form the count uses: fewer linear
  conditions than the dimension of the coefficient space leaves a nonzero coefficient vector
  satisfying all of them.

Unconditional, axiom-clean, umbrella-wired. What step 3 still needs is arithmetic, not algebra: the
two cardinalities — `#{α : Fin (n+1) → ℕ | ∑ α ≤ m}` for the source and the number of multi-indices
of total degree `< N` in `n` variables for the target — and the inequality that makes the first
exceed the second at `N ~ m^{1+1/n}`.

### Siegel step 3 (counting) — DONE

`formal/GaloisForLFunctions/HTGeometry/MultiIndexCounts.lean`:

- **`card_le_pow_of_sum_lt`** — a family of multi-indices in `n` variables of total degree below
  `N` has at most `N ^ n` members (each coordinate is then below `N`, so the family sits inside
  `Fintype.piFinset (fun _ => range N)`);
- **`pow_le_card_of_box_subset`** — a family containing the box `{β : ∀ i, β i ≤ m}` in `k`
  variables has at least `(m + 1) ^ k` members.

Unconditional, axiom-clean, umbrella-wired. With `KernelOfDimensionDrop`, step 3 is now complete as
a self-contained unit: apply the box bound at `k = n + 1` to the coefficient space, the degree
bound to the jet conditions, and `exists_ne_zero_forall_apply_eq_zero_of_finrank_lt` whenever
`N ^ n < (m + 1) ^ (n + 1)` — which holds for `N ~ m^{1+1/n}`.

Siegel now stands at: **step 1 done** (`OrderNSchwarz`), **step 3 done**
(`KernelOfDimensionDrop` + `MultiIndexCounts`), steps 2 (finite polydisc cover of one fundamental
parallelotope) and 4 (the periodicity comparison `S ≤ θ^N S`) open.

### Siegel step 2 (geometry) — DONE

`formal/GaloisForLFunctions/HTGeometry/FundamentalParallelotope.lean`:

- `parallelotope b` — the image of the unit cube under `t ↦ ∑ tᵢ bᵢ`;
- **`isCompact_parallelotope`** — it is compact, so any open cover of it has a finite subcover,
  which is the polydisc cover the count consumes;
- **`exists_intCombination_sub_mem_parallelotope`** — every point of the space is congruent, modulo
  the integer span of a basis, to a point of that parallelotope; the integers are the floors of the
  coordinates in the basis.

Unconditional, axiom-clean, umbrella-wired.

**Siegel status: steps 1, 2 and 3 are now built; step 4 (the periodicity comparison) is the only
one open.** Step 4 is where compactness is load-bearing: the smallness bound obtained on the small
polydiscs is compared with the global supremum over the fundamental parallelotope, which
periodicity identifies with the supremum over the large polydiscs, giving `S ≤ θ^N S` and hence
`S = 0`. Without it the same counting argument would "prove" `z` and `exp z` algebraically
dependent on `ℂ`, so it is not optional bookkeeping.

### Siegel step 4 (core) — DONE

`formal/GaloisForLFunctions/HTGeometry/SelfImprovingBound.lean`:

> **`eqOn_zero_of_le_mul_bound`** — if on a compact nonempty set every bound `M` for `‖G‖`
> improves to `θ·M` with `θ < 1`, then `G` vanishes there. Compactness supplies the maximum, which
> then satisfies `M ≤ θ·M`.

Unconditional, axiom-clean, umbrella-wired.

**All four Siegel steps now have their reusable cores in the tree.** What is left is the assembly,
which is bookkeeping over the four:

1. present `f_1,…,f_{n+1} ∈ M(ℂ^n/Λ)` as global quotients `A_j/B_j` (`Bottcher.analyticSubringGen`
   already gives this), so `Q_P = (∏ B_j)^m · P(f)` is entire and `P(f) = 0 ↔ Q_P = 0`;
2. cover the parallelotope (`isCompact_parallelotope`) by finitely many polydiscs `D_i ⊂⊂ D_i'`;
3. count (`pow_le_card_of_box_subset`, `card_le_pow_of_sum_lt`,
   `exists_ne_zero_forall_apply_eq_zero_of_finrank_lt`) to get a nonzero `P` whose `Q_P` has
   vanishing jets of order `< N` at every centre, with `N ~ m^{1+1/n}`;
4. apply `norm_le_of_iteratedFDeriv_vanish` on each `D_i` and feed the resulting
   `θ^N`-improvement — with periodicity identifying the two suprema — to
   `eqOn_zero_of_le_mul_bound`.

The conclusion `trdeg_ℂ M(ℂ^n/Λ) ≤ n` then feeds `isEscapeSubgroup_meroPeriodSubgroupGen` and
closes `noncompact-period-quotient-facet-escape-law`.

### Siegel landing interface — DONE

`formal/GaloisForLFunctions/HTGeometry/DifferentialAlgebraicFromRelation.lean`:

> **`differentialAlgebraicOver_of_aeval_eq_zero`** — a nonzero `P ∈ MvPolynomial (Unit × ℕ) F`
> with `aeval (fun p => differentialJet p.2 x) P = 0` gives `DifferentialAlgebraicOver F x`.

Unconditional, axiom-clean, umbrella-wired. This is the interface a Siegel-type count lands on: the
count produces a nonzero polynomial annihilating `G, δG, δ²G, …`, and this converts it into the
corpus's differential-algebraicity predicate, which is what
`not_compactSpace_quotient_meroPeriodSubgroup` and its several-variable analogue consume.

So both ends of the Siegel argument are now Lean — the four analytic/combinatorial cores and the
landing interface — and what is missing is only the middle assembly listed above.

### Siegel reduction step — DONE (first half)

`formal/GaloisForLFunctions/HTGeometry/CompactQuotientSpan.lean`:

> **`span_eq_top_of_compactSpace_quotient`** — if `E ⧸ P` is compact for `E` finite-dimensional
> real, then `P` spans `E` over `ℝ`. Otherwise the corpus's
> `HTGeometry.exists_dual_vanishing_of_notMem_closed_submodule` supplies a continuous functional
> vanishing on the span, which `not_compactSpace_quotient_of_realSurjection` turns into a
> continuous surjection onto `ℝ` — impossible from a compact space.

Unconditional, axiom-clean, umbrella-wired. This is the first half of "compact quotient forces a
full lattice": the subgroup spans, so a basis can be extracted from it, and the remaining half is
that the extracted basis's integer span already has compact quotient, which is where the
parallelotope of `FundamentalParallelotope` comes from.

Same module, second half:

> **`exists_linearIndependent_span_top_subset_of_compactSpace_quotient`** — a subgroup with compact
> quotient contains a linearly independent spanning set, i.e. a basis of the whole space all of
> whose members are periods (`exists_linearIndependent` applied to the subgroup, then the span
> result above).

`Module.Basis.mk` on that set feeds `FundamentalParallelotope` directly, so the reduction
"compact quotient ⟹ compact fundamental parallelotope whose vertices are periods" is now a
two-line composition of corpus lemmas.

### Siegel step 4 — the correct chartwise form

Two further modules, both unconditional and axiom-clean:

- `PeriodicCoverVanishing.lean` — **`eqOn_zero_of_periodic_cover`**: a periodic `C^∞` function whose
  jets of order `< N` vanish at the centres of a cover of a fundamental domain is identically zero,
  when `(r/R)^N/(1−r/R) < 1`. Periodicity is what makes the bound on the fundamental domain a
  *global* bound, so the Schwarz estimate improves every bound by the fixed factor.
- `SiegelVanishingCriterion.lean` — **`exists_finite_centres_forcing_vanishing`**: from
  `CompactSpace (E ⧸ P)` alone, a finite set of centres such that jet vanishing there forces any
  `P`-periodic `C^∞` function to vanish.

**Honesty note on which of these Siegel actually consumes.** The single-function form above is a
true theorem but on a compact quotient a periodic *entire* function is constant by Liouville, so it
is not the form the argument needs: in Siegel's proof the objects are local holomorphic
representatives `F_i = h_i^m·P(f)` of a *meromorphic* function, which are not globally defined.
The usable form is therefore chartwise:

- `FamilyCoverVanishing.lean` — **`eqOn_zero_of_family_cover`**: a finite family `F i` of
  holomorphic representatives, with jets of order `< N` vanishing at the respective centres `c i`
  and a comparison constant `C` carrying small-disc bounds to large-disc bounds, vanishes on every
  small disc as soon as `C·(r/R)^N/(1−r/R) < 1`.

That last inequality is the exact quantitative shape the count has to beat, and it is where the
growing order `N ~ m^{1+1/n}` pays for the chart comparison constant `C^m`.

### Siegel — the multi-index side, on the corpus's own polydisc machinery

The count produces vanishing of the **multi-index** Cauchy coefficients, not of tuple-indexed
iterated derivatives, and the difference is decisive: multi-indices of degree below `N` in `n`
variables number `~N^n`, derivative tuples number `~n^N`, and only the first beats the `C^m` chart
comparison at `N ~ m^{1+1/n}`. The corpus already owns the multi-index apparatus
(`polydiscCoeff`, `polydiscSeries`, `norm_polydiscCoeff_le`, `norm_polydiscSeries_le`,
`card_antidiagonalTuple_le`, `summable_succ_pow_mul_geometric`, `polydiscSeries_hasSum`), so
`HTGeometry/PolydiscCoeffVanishing.lean` builds directly on it:

- **`polydiscSeries_eq_zero_of_coeff_vanish`** — vanishing coefficients of a degree kill that term;
- **`norm_le_of_polydiscCoeff_vanish`** — the multi-index Schwarz estimate:
  `‖f(c+y)‖ ≤ M·(N+1)^n·(r/R)^N·∑_j (j+1)^n (r/R)^j` when every coefficient of total degree `< N`
  vanishes and `‖f‖ ≤ M` on the torus of radius `R`;
- **`polydiscCoeff_sum_smul`** — the coefficient is linear in the function, so each prescribed
  coefficient is a linear functional of the polynomial's coefficient vector, which is exactly what
  `exists_ne_zero_forall_apply_eq_zero_of_finrank_lt` consumes.

All three unconditional and axiom-clean; `summable_succ_pow_mul_geometric` was already in
`PolydiscAnalytic.lean` and was **not** rebuilt.

### Siegel — the argument principle is now corpus-owned (mathlib has none)

The Siegel assembly needs local *reduced* fractions for a meromorphic function, i.e. Weierstrass
preparation, because the comparison constant across charts is only bounded when the two local
denominators of the same function differ by a unit.  A globally presented fraction `A/B` never
supplies this: the automorphy factor `B(·+λ)/B` is meromorphic, not bounded, precisely where `A`
and `B` share zeros.  (If `A` and `B` are globally coprime the factor *is* a nonvanishing entire
function — that is Cousin II on `ℂⁿ`, strictly harder than the local route.)

Weierstrass preparation rests on the parameter-holomorphy of the moments of a logarithmic
derivative and on their identification with the power sums of the roots.  mathlib contains **no**
argument principle at all (`rg "argument principle" Mathlib` is empty), so the residue side had to
be built.  It now is, unconditionally and axiom-clean:

- `HTGeometry/CircleIntegralParamOpen.lean` — `differentiableAt_circleIntegral_slice_open`
  generalises the corpus's own `differentiableAt_circleIntegral_slice` from a product domain to an
  arbitrary open set.  The generalisation is forced: the integrand of a logarithmic derivative
  lives on `U ∩ {f ≠ 0}`, which is never a product.
- `HTGeometry/WeierstrassParamLogDeriv.lean` — `partialFirst`, `deriv_cons_slice`,
  `analyticOnNhd_partialFirst`, and `differentiableAt_logDerivMoment`: the moments
  `y ↦ ∮ ζ^p (∂₀f/f)(ζ,y) dζ` are holomorphic in the remaining variables.
- `HTGeometry/WeightedArgumentPrincipleDisc.lean` — `logDeriv_sub_pow`,
  `circleIntegrable_finset_sum`, `circleIntegral_finset_sum`,
  `circleIntegral_weighted_logDeriv_prod`: for a presentation as a finite product of powers of
  linear factors times a nonvanishing factor, `∮ ζ^p f'/f = 2πi ∑_u m_u u^p`.
- `HTGeometry/DiscZeroFactorization.lean` — `mem_thickening_sphere`,
  `exists_factorization_of_analytic_disc`, and the capstone
  `circleIntegral_weighted_logDeriv_eq_powerSum`: **the weighted argument principle on a disc,
  with no factorization hypothesis.**

The factorization is *not* rebuilt: mathlib's `MeromorphicOn.extract_zeros_poles` supplies it, and
`Function.locallyFinsuppWithin.finiteSupport` supplies finiteness of the zero set on the compact
closed disc.  Two adaptations were needed.  Its conclusion holds only modulo equality on a
codiscrete set; on an open disc every point is an accumulation point, so
`mem_codiscreteWithin_iff_forall_mem_nhdsNE` plus continuity upgrades it to a pointwise identity.
And its divisor is taken over the *closed* disc, so the radius is first enlarged past the circle by
an amount small enough that the annulus stays zero-free — otherwise zeros just outside the circle
would enter the product.

### Siegel — Newton, and the holomorphy of the moving root multiset

With the argument principle in hand, the Weierstrass chain continues.  Three more modules, all
unconditional and axiom-clean:

- `HTGeometry/MultisetNewtonSolve.lean` — `multiset_eq_map_univ_val`,
  `multiset_newton_general`, `multiset_esymm_eq_of_powerSum`.  The corpus already owned Newton's
  identity for a `Fin n`-indexed family (`multiset_newton`), which is *not* rebuilt: every multiset
  is such a family through the enumeration by its own list, and in characteristic zero the leading
  `k` is invertible, so the identity **solves** for `e_k` in terms of `p_1,…,p_k` and `e_0,…,e_{k−1}`.
- `HTGeometry/DiscRootMultiset.lean` — `multisetOfFinsetMultiplicities`, its power sums, and
  `exists_rootMultiset`: the zeros inside the circle as a multiset whose power sums are the
  weighted contour integrals.
- `HTGeometry/SliceRootHolomorphy.lean` — `SliceAdmissible`, `sliceRoots`, `sliceMoment`,
  `sliceMoment_eq_powerSum`, `differentiableOn_sliceMoment`, and the capstone
  **`differentiableOn_esymm_sliceRoots`**: for a function of several complex variables whose slices
  do not vanish on a fixed circle, *every* elementary symmetric function of the roots inside that
  circle is holomorphic in the remaining variables.

That capstone is the analytic content of Weierstrass' preparation theorem: the elementary symmetric
functions are the coefficients of the monic polynomial vanishing exactly at the roots of the slice,
so the Weierstrass polynomial has holomorphic coefficients.  The route is: moments are holomorphic
(parameter differentiation under a contour integral over an *arbitrary* open set), moments are the
power sums (argument principle), power sums determine the elementary symmetric functions (Newton),
and holomorphy propagates upward along that recursion by strong induction.

Remaining on the Weierstrass chain before the Siegel assembly can resume: the unit factor
(`f = unit · W`), Weierstrass division, the UFD property of the local ring, and hence local reduced
fractions — which is what supplies the chart comparison constant `C₀^m`.

### Siegel — Weierstrass preparation in the distinguished variable

Four further modules close the fixed-parameter half of Weierstrass' preparation theorem, all
unconditional and axiom-clean:

- `HTGeometry/SliceRootCount.lean` — `sliceMoment_zero_eq_card`,
  `natCast_eq_of_norm_sub_lt_one`, `eventually_card_sliceRoots_eq`,
  `card_sliceRoots_const_of_isPreconnected`.  The zeroth moment *is* the root count, so a
  holomorphic function takes natural-number values; two naturals less than one apart are equal, so
  the count is locally constant and constant on a connected parameter set.  That fixed number is
  the degree of the Weierstrass polynomial.
- `HTGeometry/DiscRootMultiset.lean` (extended) — `multisetLinearProd`,
  `multisetLinearProd_eq_sum` (the expansion in the elementary symmetric functions, via mathlib's
  `Multiset.prod_X_sub_C_coeff` and `natDegree_multiset_prod_X_sub_C_eq_card`), and
  `exists_rootMultiset_factorization`, which carries the factorization alongside the power sums.
- `HTGeometry/MultisetNewtonSolve.lean` (extended) — `multiset_powerSum_zero` and
  **`multiset_eq_of_powerSum_eq`**: power sums of every order determine a multiset.  The corpus's
  own `multiset_eq_of_esymm_eq` finishes it; Newton propagates equality of power sums to equality
  of elementary symmetric functions.
- `HTGeometry/WeierstrassPolynomial.lean` — `differentiableOn_multisetLinearProd_sliceRoots`: the
  monic polynomial of the roots is holomorphic in the parameters.
- `HTGeometry/SliceWeierstrassFactorization.lean` — **`exists_slice_factorization`** and
  **`slice_eq_zero_iff`**: the slice is the monic product of the linear factors at its roots times
  a nowhere vanishing holomorphic factor, and its zeros inside the circle are exactly the roots of
  that polynomial, with multiplicity.

The identification of `sliceRoots` with the factorization multiset is *not* by construction — the
multiset is produced by `Classical.choose` from the argument principle, which records only power
sums.  It is forced instead by uniqueness: both multisets have the same power sums, and power sums
determine a multiset.

What remains on the chain: joint holomorphy of the unit factor in all variables (a Cauchy-integral
argument on top of the pieces already built), Weierstrass division, the UFD property of the local
ring, and hence local reduced fractions — the supplier of the chart comparison constant `C₀^m`.

### Weierstrass' preparation theorem is formalized

`HTGeometry.weierstrass_preparation` (in `HTGeometry/SliceWeierstrassUnit.lean`) is unconditional
and axiom-clean.  For `f` holomorphic on an open `U ⊆ ℂ^{d+1}` whose slices in the distinguished
variable do not vanish on the circle of radius `t`, over a connected parameter set `V`:

```text
DifferentiableOn ℂ (sliceWeierstrass f t) {w | tail w ∈ V}
DifferentiableOn ℂ (sliceUnit f t)        {w | tail w ∈ V ∧ ‖w 0‖ < t}
∀ y ∈ V, ∀ z, ‖z‖ < t →
  f (cons z y) = sliceWeierstrass f t (cons z y) * sliceUnit f t (cons z y)
    ∧ sliceUnit f t (cons z y) ≠ 0
```

mathlib has none of this.  Two more modules complete it:

- `HTGeometry/SliceWeierstrassJoint.lean` — `tailLin`, `sliceWeierstrass`,
  `sliceWeierstrass_ne_zero_of_norm_eq`, `differentiableOn_sliceWeierstrass`.  The polynomial is
  holomorphic in *all* variables because, expanded in the elementary symmetric functions, it is a
  polynomial in the distinguished variable of locally constant degree with holomorphic
  coefficients.
- `HTGeometry/SliceWeierstrassUnit.lean` — `unitIntegrand`, `sliceUnit`,
  `factorization_sliceUnit`, `differentiable_consDropSecond`, `differentiableOn_sliceUnit`, and the
  capstone.

The unit is *defined* by the Cauchy integral of `f/W` over the circle, not as the quotient `f/W`
itself — the quotient is undefined at the roots.  Its value is identified with the nowhere
vanishing factor of the slice factorization by Cauchy's integral formula, and its joint holomorphy
is parameter-differentiation of a contour integral whose integrand is holomorphic on the open set
where the contour variable avoids both the evaluation point and the zeros of `W`.  This is exactly
the situation the earlier generalisation to an *arbitrary* open set was built for: that domain is
not a product.

Next on the chain to Siegel: Weierstrass division, the UFD property of the local ring of germs, and
local reduced fractions.

### Weierstrass' division theorem is formalized

`HTGeometry.weierstrass_division` (in `HTGeometry/WeierstrassDivision.lean`), unconditional and
axiom-clean:

```text
g (cons z y) = sliceWeierstrass f t (cons z y) * divQuot f t g (cons z y)
                 + divRem f t g k (cons z y)
```

for `‖z‖ < t`, with `divRem` a polynomial in the distinguished variable and
`divRemCoeff_top_eq_zero` showing its top coefficient vanishes — degree strictly below that of the
divisor.

The quotient and the remainder are both contour integrals: the quotient is the Cauchy kernel damped
by the divisor, the remainder is built from the divisor's **divided difference**
`(W(ζ) − W(z))/(ζ − z)`, which is where the degree drop comes from.  That algebraic step is
isolated in `HTGeometry/PolynomialDividedDifference.lean` as `sum_pow_sub_sum_pow_eq`, proved from
mathlib's `geom_sum₂_mul` with a reflection (`Finset.sum_range_reflect`) and a triangular
double-sum exchange (`Finset.sum_comm'`); the reindexing is what puts the quotient in the form
"polynomial in `z` whose coefficients are tails of the divisor's coefficients evaluated at `ζ`",
which is what makes each remainder coefficient a single contour integral.

The identity itself is Cauchy's formula after the split
`W(ζ)/(ζ−z) = W(z)/(ζ−z) + (W(ζ)−W(z))/(ζ−z)`; the two contour integrals are recombined with the
`circleIntegral_finset_sum` built earlier in this chain.

Preparation and division are now both in hand.  Next: factoriality of the germ ring (Gauss plus the
transfer of divisibility from `O_{d-1}[z]` to `O_d`, which is exactly what division supplies), then
local reduced fractions, then the Siegel assembly.

### Closure: `nonreal-factorial-slope-formal-hypertranscendence`

Audited rather than assumed: the card's Lean table said "done" at every layer, but the table is not
evidence.  Checked directly — the capstone
`GaloisForLFunctions.HTGeometry.aeval_formalJets_ne_zero` exists with the exact statement the card
names, all twenty-five supporting modules exist, carry no `sorry`, `admit`, added `axiom`,
`opaque`, or `unsafe`, and are umbrella-wired; `#print axioms` on the capstone gives exactly
`[propext, Classical.choice, Quot.sound]`.

`FactorialSlope` is the card's own hypothesis `(2)` — the defining property of the class of series
(`0 < Re α`, `Cc ≠ 0`, `Λ ≠ 0`, `0 < c`, exponentially small relative approximation by
`Cc·Λⁿ·Γ(1+αn)`), not a smuggled analytic input.  `Im α ≠ 0` enters in exactly one place, chirp
independence, which is the transcendence mechanism of the theorem.

Stage-3 certificate written to
`3-formalized/new_scientific_knowledge/other/nonreal-factorial-slope-formal-hypertranscendence.md`.
Closure count: **21/65 certified, 44 remaining.**

### `boundary-wedge-uniform-ht-dimension-gap` — parameterization gap closed

Re-auditing this already-certified card turned up one real gap between its claim and the tree:
`faithfulSeparation_fin_four_and_minimal` was stated for a *given* transcendental `τ`, so the
`ffsDim = 4` half was parameterized rather than unconditional.  Added
`UniformBoundaryWedge.faithfulSeparation_fin_four_and_minimal_uncond` in
`HTGeometry/WedgeFacetLowerBound.lean`, discharging `τ` by `exists_transcendental_complex` —
axiom-clean.  (The card's full law was in fact already unconditional through
`boundaryWedge_uniformHTDimensionGap`, which discharges `τ` internally; the certificate now holds
in both forms.)

### `power-canonical-product-exact-moment-borel-lattice-law` — stale "no Lean possible" claim corrected

The card's Section 7 said "No Lean formalization is attempted" because its analytic dependencies
"are absent from the current project stack".  Two of the four are present in mathlib and were simply
not checked: the **Riemann zeta functional equation** (`riemannZeta_one_sub`,
`completedRiemannZeta_one_sub`) and **Gamma at arbitrary complex order** (`Complex.Gamma`, with
`Complex.Gamma_mul_Gamma_one_sub`); `riemannZeta_neg_two_mul_nat_add_one` supplies the trivial zeros
that the card's even-`s` collapse rests on.

First layer built in `RHTower/ZetaMomentBorelCoefficient.lean`, unconditional and axiom-clean:
`riemannZeta_neg_eq` (the functional equation in the card's reflected form),
`riemannZeta_neg_div_Gamma_eq` (the card's `(3)`), and `riemannZeta_neg_eq_zero_of_even` (the tail
vanishes at even order, because the sine of the functional equation does).

Remaining for this card: normal convergence and meromorphic continuation of the Lambert sum `(5)`,
and residue calculus under ramified coordinates.  Closure count unchanged at 21/65.

Second layer of `power-canonical-product-exact-moment-borel-lattice-law`: the card's elementary
identity `(4)` is formalized as `RHTower.tsum_alternating_sine_geometric` (with
`im_neg_mul_exp_pow`), unconditional and axiom-clean — the imaginary part of a geometric series of
ratio `-u e^{iα}`, with the denominator `|1 + u e^{iα}|² ≥ (1-|u|)²` bounded away from zero.
Identities `(3)` and `(4)` are now both Lean theorems; the remaining analytic content of the card is
the sum interchange producing the Lambert form `(5)`, its normal convergence and continuation, and
ramified residue calculus. Closure count unchanged at 21/65.

Third layer of `power-canonical-product-exact-moment-borel-lattice-law`: the sum interchange of
`(5)` is formalized in `RHTower/ZetaRealBound.lean` — `norm_riemannZeta_le_tsum` (a uniform bound
for `ζ` above a real abscissa, which is what makes the factors `ζ(1+sk)` bounded uniformly in `k`),
`summable_uncurry_geometric_zeta`, and `tsum_mul_riemannZeta_eq_tsum_comm`
(`∑_k c_k ζ(e_k) = ∑_n ∑_k c_k/(n+1)^{e_k}` for geometrically small `c_k` and exponents above a
fixed abscissa).  All unconditional and axiom-clean.

Three of the card's four "absent dependencies" are now discharged: the functional equation, Gamma at
arbitrary order, and the interchange.  What is left is the normal convergence and meromorphic
continuation of the Lambert sum and ramified residue calculus.  Closure count unchanged at 21/65.

Fourth layer of `power-canonical-product-exact-moment-borel-lattice-law`:
`RHTower/LambertQuadraticFactor.lean` — `lambertQuadratic_factor`
(`1 + 2u cos α + u² = (1 + u e^{iα})(1 + u e^{-iα})`), `lambertQuadratic_eq_zero_iff` (the two zeros
`-e^{∓iα}`, which under `u = ξ/(2πn)^s` are exactly the card's two power lattices), and
`norm_lambertQuadratic_ge` (`≥ (1-‖u‖)²`, the estimate making the `n`-th term of `(5)` `O(n^{-1-s})`).
All unconditional and axiom-clean.  One factorization carries both the pole classification and the
convergence bound.  Closure count unchanged at 21/65.

Fifth layer of `power-canonical-product-exact-moment-borel-lattice-law`:
`RHTower/LambertSeriesConvergence.lean` — `norm_lambertTerm_le` (the `n`-th Lambert term is
`≤ 4C/(n+1)^{1+b}` when `‖w_n‖ ≤ C/(n+1)^b` and `‖w_n‖ ≤ 1/2`) and `summable_lambertTerm`
(absolute convergence for `b > 0`).  Unconditional and axiom-clean.  The `1/2` threshold comes from
the previous layer: it forces `‖1 + 2w cos α + w²‖ ≥ 1/4`, so the denominator costs only a factor
four.  This is the card's "`O(n^{-1-s})` uniformly after finitely many terms are removed".
Closure count unchanged at 21/65.

Sixth layer: `tsum_alternating_sine_geometric_complex` — the card applies `(4)` at complex
`u = ξ/(2πn)^s`, so the real-variable version formalized earlier does not suffice.  The complex form
is proved from the same factorization that located the poles: two geometric series with ratios
`-u e^{±iα}`, difference `2i u sin α` over `(1 + u e^{iα})(1 + u e^{-iα})`.  Unconditional and
axiom-clean.  Closure count unchanged at 21/65.

Seventh layer: `rpow_scale_identity` — `P^{s(k+1)}·(n+1)^{1+s(k+1)} = (n+1)·((P(n+1))^s)^{k+1}`,
the regrouping that turns the double sum into a Lambert series: the Dirichlet denominator split
against `(2π)^{sk}` gives the `1/n` weight and the `k`-th power of the single scale `(2π(n+1))^s`.
Unconditional and axiom-clean.  With `(3)`, the complex `(4)`, the interchange and this identity all
in Lean, the remaining assembly of `(5)` is bookkeeping; the genuinely open part of the card is the
ramified residue calculus.  Closure count unchanged at 21/65.

Eighth layer — **the card's `(5)` is formalized**: `RHTower/PowerLatticeLambertForm.lean`,
`tsum_zeta_coeff_eq_lambert`,

```text
∑_{k≥1} (-1)^{k+1} sin(kα) ξ^k ζ(1+sk)/(2π)^{sk} = ∑_{n≥1} (1/n) u_n sin α/(1+2u_n cos α+u_n²),
```

with `lambertVar`/`norm_lambertVar_lt_one`.  Unconditional and axiom-clean.  It is exactly the
composition of the four previously formalized ingredients — geometric smallness of the coefficients,
the Dirichlet interchange, the scale identity, and the complex `(4)` — with no new analytic input.

For a card whose Section 7 said "No Lean formalization is attempted" because its dependencies were
"absent from the current project stack", the exact transform `(5)`, its pole law `(7)`, and its
convergence are now theorems.  Remaining: meromorphic continuation past the poles and the ramified
residue computation `(9)`–`(10)`.  Closure count unchanged at 21/65.

Ninth layer: `RHTower/PowerLatticeResidue.lean` — `deriv_lambertQuadratic_at_root_pos`/`_neg`
(derivative `∓2i sin α` at the roots `-e^{∓iα}`), `deriv_lambertQuadratic_ne_zero_pos` (roots simple
exactly when `sin α ≠ 0`, i.e. the card's "not an even integer"), `residue_lambertNumerator_pos`/
`_neg` (residues `±e^{±iα}/(2i)`, independent of `n`), and `tsum_zeta_coeff_eq_zero_of_natMulPi`
(the card's `(6)`: identically zero at even order).  Unconditional and axiom-clean.

`sin α` plays both roles — derivative at the roots and numerator factor — which is why the even
orders are simultaneously the degenerate poles and the vanishing transform.  Closure count unchanged
at 21/65.

Tenth layer — the card's `(10)`: `RHTower/PowerLatticeRamification.lean`, `residue_transport_pos`
(`= i/s`) and `residue_transport_neg` (`= -i/s`), unconditional and axiom-clean.  The residue of
`(8)` divided by the derivative of `ξ = -e^{±iα}η^s` at `η = 2πn`; the residue carries `(2πn)^s/n`
and the derivative `s(2πn)^{s-1}`, and their quotient `2π/s` is free of `n`.  So the `n`-dependence
of `(8)` is entirely coordinate artefact and the ramification removes exactly it.  Closure count
unchanged at 21/65.

Eleventh layer: `eventually_norm_lambertVar_le_half` — for `s > 0` and any `M`, eventually in `n`,
`‖ξ‖ ≤ M → ‖u_n‖ ≤ 1/2`, uniformly in `ξ`.  This is the card's "uniformly after finitely many terms
are removed"; with `norm_lambertTerm_le` it dominates the tail on every compact set, and the finitely
many exceptional `n` are precisely the terms that can carry poles.  Unconditional and axiom-clean.
Closure count unchanged at 21/65.

Twelfth layer: `RHTower/LambertSumHolomorphic.lean` — `norm_lambertVar_le_of_mem_ball` and
**`differentiableOn_lambertSum`**: for `0 < s` and `M ≤ (2π)^s/2` the Lambert sum is holomorphic on
`‖ξ‖ < M`.  Each term is rational with denominator `≥ 1/4`, the family is dominated by
`4C/(n+1)^{1+s}`, and mathlib's `differentiableOn_tsum_of_summable_norm` finishes.  Unconditional
and axiom-clean.  With `(5)` this makes the transform a holomorphic function near the origin rather
than a formal series.  Closure count unchanged at 21/65.

Thirteenth layer — the continuation mechanism: `RHTower/LambertTailHolomorphic.lean`,
`differentiableOn_lambertTail` (tail from index `N` holomorphic on `‖ξ‖ < (2π(N+1))^s/2`) and
`exists_index_lambertTail_differentiableOn` (every radius is reached by some tail).  Unconditional
and axiom-clean.  Dropping terms enlarges the disc without bound and the discarded head is a finite
sum of explicit rational functions with the already-classified poles, so the transform is
holomorphic on every disc after subtracting finitely many known rational terms — the meromorphic
continuation of `(5)` with the pole set `(7)`.

Sections 1–3 of `power-canonical-product-exact-moment-borel-lattice-law` are now formalized end to
end.  Closure count unchanged at 21/65 pending the stage-3 certificate write-up.

**Correction to the previous entry.**  "Sections 1–3 formalized end to end" overstates it.  The
thirteen layers cover `(2)`–`(11)`, i.e. everything about the transform *given* its coefficients.
They do not cover `(1)`: that `b_k = (-1)^k ζ(-sk)` are the coefficients of the asymptotic tail of
`H_s(x) = x W_s'(x)/W_s(x)`.  That is an asymptotic expansion of the logarithmic derivative of the
canonical product and is the single remaining analytic input of this card.

The carrier is already corpus-owned (`powerCanonicalProduct`, `RationalPowerCyclicNorm.lean`, with
Bank's dichotomy proved on it), so `(1)` concerns an object already in Lean.  No stage-3 certificate
is written for this card: the transform theory is formalized, its identification with the Barnes
tail of `W_s` is not.  Closure count remains 21/65.

Fourteenth layer, first step toward `(1)`: `HTGeometry/WeierstrassFactorGenus.lean` — `weierstrassE`
(the elementary factor of arbitrary genus; the corpus had only genus one), `hasDerivAt_weierstrassE`,
and **`logDeriv_weierstrassE`**: `E_g'/E_g = -z^g/(1-z)`.  Unconditional and axiom-clean.

The collapse is the mechanism of the card's tail: the derivative of the exponential polynomial is the
truncated geometric series `(z^g-1)/(z-1)`, cancelling the `g` lowest terms of `-1/(1-z)` and leaving
`-z^g/(1-z)`.  At `z = -x/n^s` this gives `H_s(x) = ∑_n (-1)^g (x/n^s)^{g+1}/(1+x/n^s)`, whose terms
decay like the `(g+1)`-st power — the reason `H_s` has an inverse-power tail.  Remaining for `(1)`:
the Mellin/Barnes evaluation of that sum's asymptotic coefficients as `(-1)^k ζ(-sk)`.
Closure count unchanged at 21/65.

Fifteenth layer: `tsum_inverse_power_expansion` — for `‖t‖ > 1`, `t^{g+1}/(1+t) = ∑_j (-1)^j t^{g-j}`.
Unconditional and axiom-clean.  With `logDeriv_weierstrassE` this completes the mechanism of the
card's `(1)`: the `n`-th term of `H_s` is `(-1)^g t^{g+1}/(1+t)` at `t = x/n^s`, and its descending
expansion in `t` is an ascending expansion in `n^s/x`; summing over `n` gives the inverse-power tail
with `b_k` a regularized `∑_n n^{sk}`, which is the source of `ζ(-sk)`.  What is left for `(1)` is
that regularization — the Mellin/zeta step.  Closure count unchanged at 21/65.

### `weighted-euler-tangent-global-graph-decoupling` — the joint-closure criterion

`HTGeometry/JointDenseOfVanishingDual.lean`: `apply_eq_inl_add_inr` and
**`topologicalClosure_eq_top_of_forall_pair_dual_eq_zero`** — a subspace of `E × F` whose only
annihilating *pair* of functionals is `(0,0)` is dense in the product.  Unconditional and
axiom-clean, built on the corpus's own `topologicalClosure_eq_top_of_forall_dual_eq_zero`.

This makes precise the card's insistence that `(3)` "is not a consequence of density of the two
projections": the annihilator of a subspace of a product consists of *pairs*, and projection density
only rules out the split pairs `(f₁,0)`, `(0,f₂)`.  The mixed pairs are what the carrier-elimination
theorems kill.  Remaining for `(3)`/`(18)`/`(19)`: instantiate the two factors and feed the
elimination in.  Closure count unchanged at 21/65.

`weighted-euler-tangent-global-graph-decoupling`, second brick: `closure_add_left_image` and
**`dense_affine_of_topologicalClosure_eq_top`** — a translate of a dense subspace fills the space.
Unconditional and axiom-clean.  This is the `(18) → (19)` step outright: the affine closure
`(1+M₀) × O(Q₊)_R` follows from the linear joint closure by a homeomorphism, with no new analysis.

So `(19)` is reduced to `(18)`, and `(3)`/`(18)` both reduce to the pair criterion.  The genuine
remainder is the instantiation: the coefficient factor is Banach but `O(Q₊)_R` is Fréchet, so the
separation must be run in locally convex form, with the `compactFourierBorel` analytic functionals as
the second component of the annihilating pair.  Closure count unchanged at 21/65.

`weighted-euler-tangent-global-graph-decoupling`, third brick —
`HTGeometry/LocallyConvexDenseOfVanishingDual.lean`: the density criterion and its pair form with
**no normed hypothesis**, valid in any locally convex real TVS.  Unconditional and axiom-clean.

The norm was never needed: `geometric_hahn_banach_closed_point` separates a point from a closed
convex set in a locally convex space, and "a functional bounded above on a subspace vanishes on it"
is scaling, not estimation.  The Fréchet obstacle I recorded one entry earlier is therefore removed —
the criterion applies with `O(Q₊)_R` a Fréchet space of holomorphic functions.

Remaining for `(3)`/`(18)`: the concrete instantiation of the two factors and of `Γ_fin`, feeding
`compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical` in as the vanishing of the
mixed pair; `(19)` then follows by `dense_affine_of_topologicalClosure_eq_top`.  Closure count
unchanged at 21/65.

`weighted-euler-tangent-global-graph-decoupling`, fourth brick:
**`topologicalClosure_span_eq_top_of_pair_dual_lcs`** — for a family of pairs `(e_i, v_i)` in a
product of locally convex spaces, the span is dense once the only pair annihilating every generator
is zero.  Unconditional and axiom-clean.

This is `(3)` in the form the card uses: `Γ_fin` is the span of the generators
`p ↦ ((log p/p)·δ_p, u_p)`, and the hypothesis is checked one prime at a time — exactly the
prime-indexed graph annihilation the carrier-elimination theorems consume.  The criterion chain is
now complete end to end:

    prime-indexed annihilation → (carrier elimination) → pair is zero
      → (topologicalClosure_span_eq_top_of_pair_dual_lcs) → (3), (18)
        → (dense_affine_of_topologicalClosure_eq_top) → (19)

Only the concrete construction of the two factor spaces remains.  Closure count unchanged at 21/65.

`weighted-euler-tangent-global-graph-decoupling`, fifth brick:
`HTGeometry/LpSingleAnnihilator.lean`, **`eq_zero_of_forall_apply_lp_single`** — on `lp E p`,
`p ≠ ∞`, a continuous functional vanishing on all single-support elements is zero.  Unconditional
and axiom-clean, from mathlib's `lp.hasSum_single`.

This closes the *first* factor of the pair criterion: the coefficient space is a weighted `ℓ¹` over
the primes and its single-support elements are exactly the scaled Dirac masses generating `Γ_fin`'s
first component.  In the pair `(f₁, f₂)`, once carrier elimination gives `f₂ = 0`, the surviving
prime-indexed condition forces `f₁ = 0` by this lemma.  Only the second factor — the regular-flux
space on the quadrant — remains to be constructed.  Closure count unchanged at 21/65.

`weighted-euler-tangent-global-graph-decoupling`, sixth brick:
`HTGeometry/VanishingOnClosedSpan.lean` — `eq_zero_on_topologicalClosure_span` and
`eq_zero_of_topologicalClosure_span_eq_top`: a continuous linear map vanishing on a set vanishes on
its closed span, hence is zero when that span is dense.  Unconditional and axiom-clean.

This is what converts the elimination's output (`L (sᵐ) = 0` for all `m`, `compactFourierBorel L s
≡ 0`) into `L = 0`, given density of the generating family.  Recorded also: the flux side of the
elimination lives on `C(K,ℂ)` for compact `K`, a **Banach** space — the Fréchet structure of
`O(Q₊)_R` appears in the card's statement but not in the compactly-carried route, so the locally
convex criterion is a convenience there rather than a necessity.  Closure count unchanged at 21/65.

### Runge is the real remaining input — and it is an interface, not a theorem

Tracing `weighted-euler-tangent-global-graph-decoupling` to its last step turned up a structural
fact worth recording separately.

The elimination gives `L (sᵐ) = 0` for every `m`.  On `C(K, ℂ)` that does **not** force `L = 0`:
for `K` the closed unit disc and `s = id`, the functional `f ↦ ∮_{|z|=1} f dz` kills every `zᵐ`,
`m ≥ 0`, and is nonzero.  Stone–Weierstrass does not apply — the algebra generated by `s` is not
self-adjoint.  So the density step *must* be taken in the holomorphic category, where polynomials
are dense by **Runge**, not in `C(K,ℂ)`.

Status of Runge in the stack:

- **mathlib has none** — no `Runge`, no `Mergelyan` anywhere in `Mathlib/`;
- the corpus has `HTGeometry/RungeOneAtomAbsorption.lean`, but that file *represents* the theorem as
  the `Prop` interface `OneGeneratorRungeDense` and proves only the topological-algebraic deduction
  on top of it;
- `HTGeometry/PolyannulusRunge.lean` builds the inductive step of the several-variable statement
  (Laurent coefficients of a slice are holomorphic), not the theorem.

So Runge's theorem is the genuine open input, and discharging `OneGeneratorRungeDense` would unblock
this card and every other consumer of that interface.

First brick toward it, unconditional and axiom-clean —
`HTGeometry/CauchyKernelPolynomialApprox.lean`:

- `tsum_cauchyKernel_eq` — `∑_n zⁿ/λⁿ⁺¹ = 1/(λ − z)` whenever `‖z‖ < ‖λ‖`;
- **`tendstoUniformlyOn_cauchyKernel_poly`** — for `r < R ≤ ‖λ‖`, the partial sums converge to
  `1/(λ − z)` *uniformly* on `closedBall 0 r`.

That is pole-pushing in its simplest form: a pole outside the disc is moved to infinity and the
kernel becomes a uniform limit of polynomials.  With the Cauchy integral formula writing a
holomorphic function as a superposition of such kernels, this is the engine of polynomial Runge on a
disc.  Closure count unchanged at 21/65.

Second brick toward Runge — `HTGeometry/DiscPolynomialDensity.lean`, unconditional and axiom-clean:

- `tendstoUniformlyOn_cauchyPartialSum` — a function holomorphic on a closed disc is the uniform
  limit on every strictly smaller disc of the partial sums of its Cauchy power series;
- `exists_partialSum_approx_on_closedBall` — hence a polynomial within any prescribed error on a
  closed sub-disc.

Worth stating plainly: **on a disc there is no Runge content at all** — the power series already
gives polynomial approximation, and mathlib's `DifferentiableOn.hasFPowerSeriesOnBall` plus
`HasFPowerSeriesOnBall.tendstoUniformlyOn` supply it directly.  What Runge adds is the passage to a
compact set that is *not* a disc, where the Cauchy kernel's poles lie in the complement and must be
pushed along it — which is what the first brick
(`tendstoUniformlyOn_cauchyKernel_poly`, pole-pushing to infinity) begins.

For the card's interface `OneGeneratorRungeDense`, stated on the upper half-plane, the disc case is
the target of the conjugation: the Cauchy coordinate `r(z) = (λ−z)⁻¹` is a biholomorphism onto a
disc, so the remaining step is the transport of these two bricks along it.  Closure count unchanged
at 21/65.

Third brick toward Runge: `exists_partialSum_comp_approx` — the disc approximation transported along
any map sending a set into the disc.  Unconditional and axiom-clean.  The approximants become
polynomials in the composed coordinate, which is exactly the shape of `OneGeneratorRungeDense`:
polynomials in the single Cauchy coordinate `r(z) = (λ−z)⁻¹`.

So the remaining content of that interface is now purely the **Möbius geometry** — exhibiting
`r` as a biholomorphism of the half-plane onto a disc and checking that a compact subset of the
half-plane maps into a strictly smaller disc.  No further approximation theory is required; the
three bricks
(`tendstoUniformlyOn_cauchyKernel_poly`, `tendstoUniformlyOn_cauchyPartialSum`,
`exists_partialSum_comp_approx`) cover the analysis.

Fourth brick toward Runge — the Möbius step: `HTGeometry/CauchyCoordinateHalfPlane.lean`,
unconditional and axiom-clean:

- `norm_sub_lt_norm_add_of_re_pos` — on the right half-plane the pole at `−a` is strictly farther
  than the pole at `a` (`‖z−a‖ < ‖z+a‖ ⟺ Re z > 0`, by `‖z+a‖² − ‖z−a‖² = 4a·Re z`);
- **`cauchyCoordinate_mem_ball_of_re_pos`** — hence for `a > 0` the Cauchy coordinate
  `z ↦ (z+a)⁻¹` maps `{Re z > 0}` into the open disc of centre and radius `1/(2a)`.

That is the change of coordinate under which the disc bricks become approximation by polynomials in
one Cauchy coordinate on a half-plane, i.e. the content of `OneGeneratorRungeDense`.  All four
bricks are now in place; what is left to discharge the interface is the bookkeeping that a *compact*
subset of the half-plane lands in a *strictly smaller* disc, so that
`exists_partialSum_comp_approx` applies with room to spare.

Fifth brick — the compactness bookkeeping: **`exists_radius_lt_of_isCompact_re_pos`**.  For `a > 0`
and `K` a compact subset of the right half-plane there is `ρ < 1/(2a)` with
`‖(z+a)⁻¹ − 1/(2a)‖ ≤ ρ` for every `z ∈ K`.  Unconditional and axiom-clean: continuity of the Cauchy
coordinate on a compact set upgrades the pointwise strict bound of the previous brick to a uniform
one with room to spare, which is exactly the hypothesis `exists_partialSum_comp_approx` consumes.

The five bricks now assembled for `OneGeneratorRungeDense` are:

```text
cauchyCoordinate_mem_ball_of_re_pos    half-plane ↪ disc
exists_radius_lt_of_isCompact_re_pos   compact ↪ strictly smaller disc
tendstoUniformlyOn_cauchyPartialSum    polynomial approximation on the disc
exists_partialSum_comp_approx          transport along the coordinate
tendstoUniformlyOn_cauchyKernel_poly   pole-pushing (the non-disc case)
```

The remaining step to discharge the interface is to compose them: given `f` holomorphic on the
half-plane, push it through the coordinate to a function holomorphic on the disc, approximate, and
pull back.  That composition needs the inverse coordinate and the holomorphy of the transported
function — the only piece not yet built.

Sixth and seventh bricks — the inverse coordinate and holomorphy transport, unconditional and
axiom-clean:

- **`re_inv_sub_pos_of_mem_ball`** — the coordinate is a *bijection*, not merely an injection into
  the disc: `‖w − c‖ < c` with `c = 1/(2a)` unwinds to `normSq w < (1/a)·Re w`, which is exactly
  `Re(w⁻¹) > a`.  The half-plane condition and the disc condition are the same inequality read in
  the two coordinates, in both directions;
- **`differentiableOn_transport_of_re_pos`** — hence a function holomorphic on `{Re z > 0}` pulls
  back through `w ↦ w⁻¹ − a` to a function holomorphic on the disc.

Note `0` lies on the *boundary* of that disc (`‖0 − c‖ = c`), never inside, which is what makes the
inverse coordinate defined throughout.

The Runge interface `OneGeneratorRungeDense` now has every analytic ingredient:

```text
half-plane ↔ disc              cauchyCoordinate_mem_ball_of_re_pos, re_inv_sub_pos_of_mem_ball
holomorphy transports          differentiableOn_transport_of_re_pos
compact ↪ smaller disc         exists_radius_lt_of_isCompact_re_pos
polynomials approximate        tendstoUniformlyOn_cauchyPartialSum
approximation transports       exists_partialSum_comp_approx
pole-pushing (non-disc case)   tendstoUniformlyOn_cauchyKernel_poly
```

What is left is the statement-level assembly into the exact `Prop` the interface declares.

### Runge on a half-plane by one Cauchy coordinate — proved

`HTGeometry/HalfPlaneRungeOneAtom.lean`, **`exists_partialSum_cauchyCoordinate_approx`**,
unconditional and axiom-clean:

> for `a > 0`, `f` holomorphic on `{Re z > 0}`, `K` compact inside it and `ε > 0`, there is a
> partial sum of the Cauchy series of the transported function which, evaluated at the coordinate
> `(z+a)⁻¹ − 1/(2a)`, approximates `f` to within `ε` uniformly on `K`.

That is the analytic content of the interface `OneGeneratorRungeDense` — approximation by
polynomials in the single Cauchy coordinate, uniformly on compacta of the half-plane — obtained by
composing the seven bricks with no new analysis:

```text
exists_radius_lt_of_isCompact_re_pos   K lands in a disc of radius ρ < 1/(2a)
re_inv_sub_pos_of_mem_ball             the coordinate is a bijection onto the disc
differentiableOn_transport_of_re_pos   f transports to a holomorphic G on the disc
exists_partialSum_comp_approx          G's Cauchy partial sums approximate, pulled back
```

mathlib has no Runge in any form, so this is new to the stack.  What is still needed to *discharge*
the `Prop` `OneGeneratorRungeDense` itself is only its packaging: constructing the algebra of
holomorphic functions on the half-plane as a topological `ℂ`-algebra and identifying compact-open
convergence there with the uniform-on-compacta statement above.  The mathematics is done; the
remaining step is a structure, not an argument.

**The remaining packaging step, with its tools identified.**  To turn
`exists_partialSum_cauchyCoordinate_approx` into the `Prop` `OneGeneratorRungeDense` one needs a
membership criterion for the compact-open closure:

```text
(∀ K compact, ∀ ε > 0, ∃ g ∈ S, ∀ x ∈ K, ‖f x − g x‖ < ε)  →  f ∈ S.topologicalClosure
```

in `C(U, ℂ)`.  The mathlib tools for it, located this pass:

- `ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn` — convergence in the compact-open
  topology *is* uniform convergence on every compact set;
- `ContinuousMap.hasBasis_compactConvergenceUniformity` and
  `CompactExhaustion.hasAntitoneBasis_compactConvergenceUniformity` — the uniformity basis, the
  second along a compact exhaustion, which an open subset of `ℂ` possesses.

The route is therefore: take a compact exhaustion of the half-plane, use the approximation theorem
with error `1/n` on the `n`-th piece to build a sequence in the polynomial subalgebra, and conclude
convergence by the first lemma.  No further analysis is involved.

Note the two names that do *not* exist and cost a probe:
`ContinuousMap.hasBasis_nhds_compactConvergence` and
`ContinuousMap.tendsto_iff_forall_compact_tendstoUniformlyOn` — the real spelling is
`isCompact`, not `compact`.

**The packaging bridge is built.**  `HTGeometry/CompactOpenClosureCriterion.lean`,
**`mem_topologicalClosure_of_forall_isCompact_approx`**, unconditional and axiom-clean:

> for `X` locally compact and σ-compact, `S` a subalgebra of `C(X, ℂ)` and `f` approximable on every
> compact set to every accuracy by members of `S`, one has `f ∈ S.topologicalClosure`.

Exactly the route recorded last pass: a compact exhaustion, the approximation with error `1/(n+1)`
on the `n`-th piece, and `ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn` to conclude
convergence.  Two typeclass notes for the next consumer: `Subalgebra.topologicalClosure` needs
`IsSemitopologicalSemiring C(X, ℂ)`, which follows from `LocallyCompactSpace X` (not merely
`WeaklyLocallyCompactSpace`, which is all `CompactExhaustion.choice` asks); and the ring structure
needs `Mathlib.Topology.ContinuousMap.Algebra`, which is not pulled in by the uniform-convergence
imports.

With this and `exists_partialSum_cauchyCoordinate_approx`, both halves of
`OneGeneratorRungeDense` are now theorems: the approximation and the bridge from approximation to
closure.  What is left to discharge the interface literally is to instantiate it — the ambient
algebra `A` must be the *holomorphic* subalgebra, since on all of `C(U,ℂ)` the statement is false
(the contour functional kills every power of the coordinate).

**The last instance obligation is discharged.**  `HTGeometry/HalfPlaneSigmaCompact.lean`,
`isSigmaCompact_rightHalfPlane`, unconditional and axiom-clean: `{Re z > 0}` is σ-compact, exhausted
by the closed bounded sets `{1/(n+1) ≤ Re z, ‖z‖ ≤ n+1}`.

This was needed because Lean does **not** infer it: `IsOpen.locallyCompactSpace` gives
`LocallyCompactSpace ↥{Re z > 0}` for free, but `SigmaCompactSpace` on that subtype fails
`infer_instance` even with local compactness available, and the closure criterion needs both.

The three ingredients for `OneGeneratorRungeDense` on the half-plane are now all theorems:

```text
exists_partialSum_cauchyCoordinate_approx        the approximation (Runge proper)
mem_topologicalClosure_of_forall_isCompact_approx  approximation ⟹ compact-open closure
isSigmaCompact_rightHalfPlane                    the missing instance
```

Remaining: assemble them in the *holomorphic* subalgebra of `C(↥{Re z > 0}, ℂ)` — the ambient
algebra cannot be all of `C(U,ℂ)`, where the statement is false.

**The ambient space is built.**  `HTGeometry/RightHalfPlaneSpace.lean`, unconditional and
axiom-clean: `rightHalfPlane`, `isOpen_rightHalfPlane`, the two instances
(`LocallyCompactSpace` from openness, `SigmaCompactSpace` from the explicit exhaustion),
`add_ne_zero_of_mem_rightHalfPlane`, and the Cauchy coordinate `cauchyCoord a ha : C(↥H, ℂ)` with
its evaluation lemma.

That is the carrier on which the Runge statement lives.  With the three theorems already proved —
the approximation, the closure criterion, the σ-compactness — the assembly of
`OneGeneratorRungeDense` now needs only the *holomorphic subalgebra* of `C(↥H, ℂ)`.  The workable
definition avoids differentiability on a subtype: take the carrier

```text
{f : C(↥H, ℂ) | ∃ F : ℂ → ℂ, DifferentiableOn ℂ F H ∧ ∀ z : ↥H, f z = F z}
```

which is closed under sums, products and scalars because the witnesses `F` are, and contains `1`.
The remaining friction is instance-level, not mathematical: the ambient of `OneGeneratorRungeDense`
must be that subalgebra *as a type*, so its `IsTopologicalSemiring` and the identification of its
subspace closure with the ambient closure have to be supplied.

**The holomorphic subalgebra is built.**  `HTGeometry/HolomorphicSubalgebra.lean`, unconditional and
axiom-clean:

- `holoAlgebra : Subalgebra ℂ C(↥H, ℂ)` — the continuous functions on the half-plane that extend
  holomorphically, carried as `∃ F, DifferentiableOn ℂ F H ∧ ∀ z, f z = F z`.  Carrying the witness
  is what makes the closure properties immediate (sums, products, scalars of differentiable
  functions are differentiable) and avoids defining differentiability on a subtype at all;
- `mem_holoAlgebra_iff`;
- `cauchyCoord_mem_holoAlgebra` — the generator lies in it, the witness being `w ↦ (w+a)⁻¹`, whose
  denominator is nonvanishing on the half-plane.

Every object and every theorem for `OneGeneratorRungeDense` on the half-plane is now in the tree:

```text
rightHalfPlane, cauchyCoord, holoAlgebra          the objects
exists_partialSum_cauchyCoordinate_approx         the approximation
mem_topologicalClosure_of_forall_isCompact_approx approximation ⟹ closure
isSigmaCompact_rightHalfPlane                     the instance the criterion needs
cauchyCoord_mem_holoAlgebra                       the generator is in the algebra
```

The one step left is to run the criterion inside `holoAlgebra` rather than inside `C(↥H, ℂ)` — the
subspace-closure identification — since the statement is false in the larger algebra.

**The final step, and the API lemma it turns on.**  What is left is to show the approximant lies in
`Algebra.adjoin ℂ {cauchyCoord a ha}`.  The approximant is
`fun z => (cauchyPowerSeries G 0 R).partialSum n ((z+a)⁻¹ − c)`, and the fact that converts it into
a manifest polynomial in the coordinate is

```text
FormalMultilinearSeries.apply_eq_pow_smul_coeff :  p n (fun _ => y) = y ^ n • p.coeff n
```

(used in `Mathlib/Analysis/Analytic/Basic.lean:1124`; it is *not* reachable from
`Mathlib.Analysis.Analytic.Basic` alone, which is why a naive `#check` fails).  With it,
`partialSum n y = ∑_{k<n} y^k • c_k`, so the approximant is a polynomial in `cauchyCoord a ha` minus
a constant, hence in the adjoin, and

```text
mem_topologicalClosure_of_forall_isCompact_approx
```

then places every holomorphic `f` in the closure of that adjoin.

Note the statement to prove is *containment*, not equality:

```text
f ∈ holoAlgebra → f ∈ (Algebra.adjoin ℂ {cauchyCoord a ha}).topologicalClosure
```

inside `C(↥H, ℂ)`.  That is true and is the usable form; the closure is **not** all of `C(↥H, ℂ)`,
as the contour functional shows.  Stating it as containment avoids the subtype-ambient friction of
`OneGeneratorRungeDense` entirely while giving its consumers exactly what they need.

### Runge on the half-plane is complete

`HTGeometry/HalfPlaneRungeClosure.lean`,
**`holo_mem_topologicalClosure_adjoin_cauchyCoord`**, unconditional and axiom-clean:

> every `f ∈ holoAlgebra` lies in `(Algebra.adjoin ℂ {cauchyCoord a ha}).topologicalClosure`
> inside `C(↥H, ℂ)`.

That is Runge approximation on the right half-plane by one Cauchy coordinate, as a theorem.  mathlib
has no Runge in any form; the corpus previously carried it only as the `Prop` interface
`OneGeneratorRungeDense`.

The eleven modules of the chain, in dependency order:

```text
CauchyKernelPolynomialApprox     pole-pushing to infinity
DiscPolynomialDensity            approximation on a disc, and its transport
CauchyCoordinateHalfPlane        half-plane ↔ disc, both directions; compactness
HalfPlaneSigmaCompact            the σ-compactness instance Lean will not infer
RightHalfPlaneSpace              the carrier and the coordinate as a ContinuousMap
HolomorphicSubalgebra            holomorphic functions as a Subalgebra, witness-carried
HalfPlaneRungeOneAtom            the approximation theorem
CompactOpenClosureCriterion      approximation ⟹ compact-open closure membership
HalfPlaneRungeClosure            the containment
```

Three findings from the build, each of which changed the route:

1. **A disc has no Runge content.**  The Cauchy power series already gives polynomial
   approximation, so the whole theorem for a half-plane is the Möbius change of coordinate plus
   transport.
2. **The statement must be containment, not equality.**  On all of `C(↥H, ℂ)` it is false: the
   contour functional kills every power of the coordinate.  This is the same counterexample that
   ruled out a Stone–Weierstrass route earlier in the chain.
3. **Carrying the holomorphy witness** (`∃ F, DifferentiableOn ℂ F H ∧ f = F ∘ val`) avoids defining
   differentiability on a subtype entirely, and makes the subalgebra axioms immediate.

### The consumer form: a functional killing the powers kills every holomorphic function

`HTGeometry/CauchyCoordAnnihilator.lean`, **`eq_zero_of_forall_pow_cauchyCoord`**, unconditional and
axiom-clean:

> a continuous `L : C(↥H, ℂ) →L[ℂ] ℂ` with `L (rⁿ) = 0` for every `n` satisfies `L f = 0` for every
> `f ∈ holoAlgebra`, where `r` is the Cauchy coordinate.

This is the density step in the form the dual-annihilator arguments consume, and it settles the
question raised earlier in this ledger — that `L (sᵐ) = 0` for all `m` does *not* give `L = 0` on
`C(K, ℂ)`.  It does give it on the holomorphic part, and that is exactly what the carrier-elimination
conclusion needs.

Two points the proof makes precise:

- **linearity suffices**, multiplicativity is not needed: every element of `Algebra.adjoin ℂ {r}` is
  `Polynomial.aeval r p`, i.e. a finite linear combination of powers, so `L` kills the whole
  generated algebra from the hypothesis on powers alone;
- the passage from the algebra to its closure is just that `ker L` is closed, via
  `closure_minimal`; the Runge containment then places every holomorphic function inside.

With this the density side of `weighted-euler-tangent-global-graph-decoupling` is complete in the
abstract: pair criterion, `ℓ¹` coefficient annihilator, closed-span converter, affine step, and now
the flux-side annihilator.

### The Runge interface is discharged

`HTGeometry/RungeInterfaceDischarge.lean`, **`oneGeneratorRungeDense_holoAlgebra`**, unconditional
and axiom-clean:

```text
OneGeneratorRungeDense ℂ holoAlgebra ⟨cauchyCoord a ha, cauchyCoord_mem_holoAlgebra ha⟩
```

The corpus's `Prop` interface — previously an assumed input in `RungeOneAtomAbsorption.lean`, and
the representative there of "the classical one-coordinate Runge theorem" — is now a **theorem** for
the Cauchy coordinate on the right half-plane.  Every consumer of that interface can be instantiated
unconditionally.

The subtype step is `closure_subtype` (`x ∈ closure s ↔ ↑x ∈ closure (val '' s)`) together with
`AlgHom.map_adjoin` and `Subalgebra.coe_map`, which identify the image of the generated algebra with
the generated algebra of the image.  The ambient had to be `holoAlgebra` as a type: in `C(↥H, ℂ)`
the same statement is false.

Thirteen modules, from the geometric series to the interface:

```text
CauchyKernelPolynomialApprox   DiscPolynomialDensity          CauchyCoordinateHalfPlane
HalfPlaneSigmaCompact          RightHalfPlaneSpace            HolomorphicSubalgebra
HalfPlaneRungeOneAtom          CompactOpenClosureCriterion    HalfPlaneRungeClosure
CauchyCoordAnnihilator         RungeInterfaceDischarge
```

**Audit of the interface's witnesses.**  Before this pass the only realization of
`OneGeneratorRungeDense` in the tree was `RungeDenseWitnesses.oneGeneratorRungeDense_of_adjoin_eq_top`
— the *trivial* case where the adjoined subalgebra is already `⊤`, which is exactly the case the
interface was introduced to avoid.  `oneGeneratorRungeDense_holoAlgebra` is therefore the first
genuine analytic witness, and the interface is no longer an assumption anywhere it is used with the
Cauchy coordinate on a half-plane.

Recorded in memory as `runge-corpus-owned` with the three traps: the disc has no Runge content; the
statement is containment and never equality in `C(↥H, ℂ)`; and `SigmaCompactSpace` on the half-plane
subtype is not inferred even though local compactness is.

**Stale-frontier update on `prime-euler-unit-tangent-completeness`.**  Its `2 → 3` gate says the
arbitrary-convex-domain and global-quadrant statements "still require a formal Runge layer".  That
layer now exists (`holo_mem_topologicalClosure_adjoin_cauchyCoord`,
`eq_zero_of_forall_pow_cauchyCoord`, `oneGeneratorRungeDense_holoAlgebra`).

But the card needs a *different* instance: the two-carrier separation — one analytic functional
carried by two polynomially separable compacta is zero, by approximating `1` on one carrier and `0`
on the other.  That is Runge for a compact set with connected complement, harder than the half-plane
case.  Recorded on the card, together with which of the new bricks such a proof would reuse.

### Lint-gate audit of this pass

`scripts/formal_tools.py lint` reports exactly two errors, and **neither is from this work**:

```text
owned module unreachable from GaloisForLFunctions.RHTower:    RHTower.BurnolReflectedPotential
owned module unreachable from GaloisForLFunctions.HTGeometry: HTGeometry.SeparableBuresPositiveReporterLaw
```

Both are other agents' modules, added concurrently and not yet wired into their umbrellas.  Left
untouched: wiring another session's in-progress module is not this pass's business and risks
colliding with an edit in flight.

All forty-one modules added in this pass were checked individually against the two umbrellas and
every one is wired:

```text
HTGeometry (30): CircleIntegralParamOpen, WeierstrassParamLogDeriv, WeightedArgumentPrincipleDisc,
  DiscZeroFactorization, DiscRootMultiset, MultisetNewtonSolve, SliceRootHolomorphy, SliceRootCount,
  WeierstrassPolynomial, SliceWeierstrassFactorization, SliceWeierstrassJoint, SliceWeierstrassUnit,
  PolynomialDividedDifference, WeierstrassDivision, WeierstrassFactorGenus,
  JointDenseOfVanishingDual, LocallyConvexDenseOfVanishingDual, LpSingleAnnihilator,
  VanishingOnClosedSpan, CauchyKernelPolynomialApprox, DiscPolynomialDensity,
  CauchyCoordinateHalfPlane, HalfPlaneSigmaCompact, RightHalfPlaneSpace, HolomorphicSubalgebra,
  HalfPlaneRungeOneAtom, CompactOpenClosureCriterion, HalfPlaneRungeClosure, CauchyCoordAnnihilator,
  RungeInterfaceDischarge
RHTower (11): ZetaMomentBorelCoefficient, AlternatingSineGeometricSum, ZetaRealBound,
  LambertQuadraticFactor, LambertSeriesConvergence, PowerLatticeLambertForm, PowerLatticeResidue,
  PowerLatticeRamification, LambertSumHolomorphic, LambertTailHolomorphic,
  WeightedEulerGrowingCarrierElimination
```

Every capstone in them reports `#print axioms` = `[propext, Classical.choice, Quot.sound]`; none
contains `sorry`, `admit`, an added `axiom`, `opaque`, or `unsafe`.

Siegel chain, next brick: `multisetLinearProd_eq_monic` — the Weierstrass polynomial is monic of
degree `card M`, the top coefficient being `e_0 = 1`.  Unconditional and axiom-clean.  This is the
distinguished-polynomial property, and the input to the uniqueness half of Weierstrass division: a
remainder of degree below `card M` divisible by a monic polynomial of that degree must vanish.

Siegel chain: `multisetLinearProd_eq_zero_iff` and `slice_eq_zero_iff_mem_sliceRoots` —
`f (cons z y) = 0 ↔ z ∈ sliceRoots f t y` for `‖z‖ < t`.  Unconditional and axiom-clean.  This
completes the identification of `sliceRoots` with the zero set of the slice: the multiset arrives
from `Classical.choose` carrying only power-sum data, so its being the zero set is a theorem
(uniqueness of a multiset from its power sums, plus the factorization), not a definition.

Siegel chain: `divRem_eq_sum_range` — the remainder is `∑_{l < k} ρ_l(y)·z^l`, a polynomial of
degree strictly below the divisor's, since its top coefficient vanishes.  Unconditional and
axiom-clean.  With `multisetLinearProd_eq_monic` this puts the division theorem in its standard
form: division by a *monic* polynomial of degree `k` with remainder of degree `< k`.

Memory `weierstrass-preparation-corpus-owned` updated to cover division as well as preparation, with
the four design points that are easy to get wrong (the unit is a contour integral not a quotient;
`sliceRoots` carries only power-sum data by construction; the root count is the zeroth moment hence
locally constant; the remainder comes from the divided difference).

Siegel chain, uniqueness input: `HTGeometry/LowDegreeVanishing.lean`,
**`coeff_eq_zero_of_eval_eq_zero_of_card`** — a coefficient family `a_0, …, a_{k−1}` whose
polynomial function vanishes at `k` distinct points has every coefficient zero.  Unconditional and
axiom-clean, from mathlib's `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`.

Stated for the *coefficient family* rather than for a `Polynomial`, because that is the form a
division remainder takes here — a finite sum whose coefficients are contour integrals.  Combined
with `divRem_eq_sum_range` (degree `< k`) and `slice_eq_zero_iff_mem_sliceRoots` (the roots are the
zeros) this gives uniqueness of the division whenever the `k` roots are distinct.

The general case, roots with multiplicity, additionally needs "a holomorphic quotient forces
vanishing to the full order at each root", i.e. an `analyticOrderAt` argument against the
factorisation — the remaining gap in the uniqueness half.

Siegel chain, uniqueness with multiplicity: **`eq_zero_of_multisetProd_dvd_of_natDegree_lt`** — a
polynomial of degree below `card M`, divisible by `∏_{r ∈ M}(X − r)`, is zero.  Unconditional and
axiom-clean.

This supersedes the `analyticOrderAt` route I flagged as the remaining gap one entry earlier.  Once
the statement is phrased as *divisibility* rather than as vanishing at points, multiplicity is
already accounted for — `Polynomial.natDegree_multiset_prod_X_sub_C_eq_card` gives the divisor
degree and `Polynomial.eq_zero_of_dvd_of_natDegree_lt` closes it.  No order-of-vanishing bookkeeping
is needed at all.

What the uniqueness half still needs is therefore only the passage from the *analytic* identity
`r' − r = (q − q')·W` on the disc to *polynomial* divisibility of `r' − r` by `W` — i.e. that a
rational function whose poles all lie inside the disc and which is holomorphic there is a
polynomial.

Siegel chain, uniqueness of division — **closed**.  Three modules, all unconditional and
axiom-clean:

* `HTGeometry/PunctureCancellation.lean`, `eqOn_of_sub_mul_eqOn` — an identity
  `(z − r)·F = (z − r)·G` on a disc gives `F = G` there.  Off `r` the factor cancels; at `r` a
  sequence inside the disc and continuity close the gap.
* `HTGeometry/AnalyticFactorDvd.lean`, `multisetProd_dvd_of_analytic_factor` — a polynomial agreeing
  on a disc with a continuous function times `∏_{r ∈ M}(z − r)`, all of `M` inside the disc, is
  divisible by `∏_{r ∈ M}(X − r)` **in `ℂ[X]`**.  Induction peeling one factor at a time: evaluation
  at a root splits a linear factor off, the cancellation lemma removes it from the analytic
  identity, and the situation repeats one degree down.  Repeated elements are peeled twice, so
  multiplicity needs no separate treatment.
* `HTGeometry/WeierstrassDivisionUniqueness.lean`, `divisionOnDisc_unique` — two decompositions
  `W·q + ∑_{l < card M} a_l z^l` of the same function have equal remainder coefficients and equal
  quotients.  Also `eqOn_of_multisetLinearProd_mul_eqOn`, cancelling the whole product from an
  identity.

This retires the gap flagged two entries earlier — the passage from the analytic identity to
polynomial divisibility — and with it the uniqueness half of Weierstrass division.  Existence
(`weierstrass_division`) and uniqueness are now both theorems, which is what the germ ring needs to
be shown factorial.

**Card accounting corrected.**  Earlier entries in this ledger reported "N/65".  That denominator
was wrong.  Certificates for `2-fully-proven/new_scientific_knowledge/other` cards are written into
`3-formalized/new_scientific_knowledge/` — sometimes into its `other/` subfolder, sometimes directly
into the parent — and a count that looked only in `other/` misses the ones in the parent.  Checking
both locations: of the 65 cards in stage 2, **18 have a certificate and 47 do not**.  A further 13
certificates in `3-formalized/.../other/` belong to cards moved out of stage 2 under the older
convention.

`HTGeometry/ContinuousMapLocallyConvex.lean`, unconditional and axiom-clean:

* `hasBasis_nhds_zero_continuousMap` — the sets `{f : ∀ x ∈ K, ‖f x‖ < ε}`, `K` compact and
  `ε > 0`, are a neighbourhood basis of the origin for the compact-open topology;
* `convex_nhds_zero_continuousMap`;
* the instance **`LocallyConvexSpace ℝ C(X, ℂ)`**, for an arbitrary topological domain.

mathlib does not have this instance.  It is the missing input for the weighted-euler card: the
locally convex separation criteria in `LocallyConvexDenseOfVanishingDual.lean` apply to any locally
convex factor, and the regular-flux factor `O(Q₊)_R` is a space of holomorphic functions carried as
a subspace of `C(X, ℂ)` with the compact-open topology.  Without the instance the criteria could not
be instantiated there at all; with it, the remaining work on that card is the concrete construction
of the two factors rather than any topological-vector-space theory.

The compact-carrier bridge for the weighted-euler card, two modules, both unconditional and
axiom-clean:

* `HTGeometry/CompactCarrierExistence.lean`, **`exists_compact_bound_of_continuousLinearMap`** —
  a continuous functional on `C(X, ℂ)` with the compact-open topology satisfies
  `‖L f‖ ≤ C·M` whenever `‖f‖ ≤ M` on a fixed compact `K`.  Continuity at the origin gives a basic
  neighbourhood inside the unit ball; scaling `f` by `ε/(M+δε)` and letting `δ` shrink turns that
  into the estimate, with `C = 1/ε`.
* `HTGeometry/CompactCarrierRestriction.lean`, **`exists_compactCarrier_functional`** — hence `L`
  is `L' ∘ (restriction to K)` for a continuous `L'` on `C(K, ℂ)`.  The bound kills the kernel of
  the restriction map, so `L` descends to its range, where the same bound makes it bounded for the
  sup norm; Hahn–Banach extends it.

This is what connects the card's dual reduction to the corpus's compact-carrier layer.  The
elimination theorems (`compactFourierBorel_eq_zero_of_primeLog_graph_annihilation_critical` and
relatives) are stated for `L : C(K, ℂ) →L[ℂ] ℂ` with `K` compact, whereas the card's second factor
is the Fréchet space `O(Q₊)_R` whose dual elements are not given on any compact set to begin with.
The bridge produces the carrier instead of assuming it, so no compactness hypothesis has to be added
to the card's statement.

The two factors of the weighted-euler joint graph, built concretely and assembled.  Three modules,
all unconditional and axiom-clean:

* `HTGeometry/PrimeTangentSpace.lean` — `PrimeTangent := lp (fun _ : Nat.Primes => ℝ) 1`, with
  `primeTangentWeight p = (log p)/p`, generators `primeTangentGen p = (log p)/p · δ_p`,
  `norm_primeTangentGen`, and **`primeTangent_eq_zero_of_forall_gen`**: a continuous functional
  killing every weighted generator is zero.  The weight is carried in the generator rather than in
  the norm, which makes the space plain `ℓ¹` and lets `eq_zero_of_forall_apply_lp_single` apply
  after one nonzero rescaling.
* `HTGeometry/QuadrantHolomorphic.lean` — `criticalQuadrant = {1/2 < Re s < 1, Im s > 0}`, open and
  **convex** (an intersection of three half-planes), locally compact; `holoQuadrant`, the real
  subspace of `C(Q₊, ℂ)` of functions extending holomorphically; and the Euler unit tangents
  `feEulerTangent p s = w_p(s) − w_p(1−s)` with `w_p(s) = (log p)p^{−s}/(1−p^{−s})²`, proved
  holomorphic on `Q₊` — on `Q₊` both `|p^{−s}| = p^{−Re s}` and `|p^{−(1−s)}| = p^{−(1−Re s)}` are
  `< 1`, so neither denominator vanishes.
* `HTGeometry/PrimeQuadrantGraph.lean` — `primeQuadrantGen`, `primeQuadrantGraph = span` of them,
  and **`topologicalClosure_primeQuadrantGraph_eq_top`**: the graph is dense in
  `PrimeTangent × holoQuadrant` as soon as the annihilating analytic functional on the second factor
  vanishes.

The assembly makes the card's asymmetry precise.  The coefficient factor is *fully discharged*: it
needs no hypothesis, because the graph relation converts the vanishing of the analytic functional
into `f₁(gen p) = 0` for every prime, and the `ℓ¹` single-support argument finishes.  Everything the
statement rests on is the second factor.

Two instances had to be given by hand — `ContinuousAdd` and `ContinuousNeg` on `holoQuadrant`.
Both follow from `IsTopologicalAddGroup`, which *is* found, but the projection is not reached by
instance search on the subtype, and the product's `ContinuousAdd` fails without them.

The single remaining input is the one the card's own proof names: after the carrier-separation
argument gives `L = 0` on entire functions, "Runge density of entire functions in the convex domain
`Q₊`" extends it to all of `O(Q₊)`.  That is polynomial approximation on a convex domain — Runge
with pole-pushing — which mathlib does not have and the corpus owns only for the half-plane with
the Cauchy coordinate (`holo_mem_topologicalClosure_adjoin_cauchyCoord`), a statement that does not
transfer to `Q₊`.  `convex_criticalQuadrant` is recorded above precisely because it is the
hypothesis that Runge layer will consume.

- 2026-08-14 — `power-canonical-product-exact-moment-borel-lattice-law` CLOSED and promoted to
  Stage 3.  The last open item was equation `(1)`, the Barnes expansion of
  `H_s(x) = x W_s'(x)/W_s(x)`, which is now unconditional at every genus:
  `RHTower.barnes_expansion_powerCanonicalProduct` in
  `RHTower/BarnesCanonicalProductExpansion.lean`.  Four new modules:
  `HTGeometry/PowerCanonicalProductLogDeriv.lean` (the Euler logarithmic derivative of `W_s`
  collapses to `∑_n (-1)^g (x/n^s)^{g+1}/(1+x/n^s)` on the positive axis, via
  `logDeriv_tprod_eq_tsum` and nonvanishing of `W_s` there),
  `RHTower/BarnesMellinGenusRepresentation.lean` (the model factor's Mellin transform is
  `(-1)^g(-π/sin πw)` on `-(g+1) < Re w < -g`, so the summed representation has the *same*
  integrand as at genus zero on a shifted strip),
  `RHTower/BarnesMellinNegResidues.lean` (the kernel's pole at a negative integer and the shift
  across it) and `RHTower/BarnesMellinGenusExpansion.lean` (the abscissa ladder
  `-((g+1)+1/s)/2`, `-(g+1/s)/2`, `k-g+1/2`, its telescoping and the `O(x^{-σ_K})` remainder).
  Only side condition: `1/s ∉ ℕ`, which is a domain condition of the displayed formula itself
  (`csc(π/s)` and `ζ(sj)` both have poles there).  All capstones axiom-clean.  Numerically
  certified at genus `0,1,2,3`.

- 2026-08-15 — `all-order-multiple-sine-stanley-reisner-differential-matroid` CLOSED and promoted to
  Stage 3.  The whole analytic core is now unconditional: joint differential independence of the
  external packets of *every* face retaining two periods
  (`HTGeometry/MultipleSineAllProperFaces.multipleSineProperFacePackets_diffIndepOn`), the exact
  squarefree annihilator `Ann_DA(L_V) = I_{N-1}`
  (`MultipleSineAnnihilatorExact.differentialAlgebraicOver_xApply_multipleSine_iff_mem_veroneseIdeal`),
  the complete matroid law for arbitrary difference-differential operators
  (`MultipleSineOperatorMatroid.multipleSineOperatorFamilyMatroid`), the multiplicative
  classification (`MultipleSineMultiplicativeAnnihilator`), and the one-layer reflection comparison
  (`MultipleSineReflectionLayer`).  Fifteen new modules.

  Three obstructions had to be solved rather than mirrored from the elliptic-gamma chain.
  (i) *The sine coface is exact only modulo `ℂ(z)`.*  Faithful labelling therefore had to be proved
  in the modulo-`ℂ(z)` form and descended by corank induction, and the free-telescoping step needed
  the affine one-slice obstruction `affineSlice_ne_coboundary_of_twisted_ambient_shift` rather than
  the one-slice one.
  (ii) *The deeper face field is not translation stable on corank-≥2 families*, because the coface of
  a maximal face has corank 1.  Fix: put the boundary faces into the generating family — their
  packets are translates of the order-one source, so their defect is *rational* — and remove them at
  the end with `diffIndepOn_differentialAdjoin_iff_of_differentialAlgebraicOver`.  Stability then
  needs only closure under deleting one more direction (`MultipleSineBoundaryFaceField`).
  (iii) *Cross-face separation.*  Difference cubes collapse both faces onto maximal ones; the bottom
  layer separates them because `{1} ∪ (bottom star)` is `ℂ(z)`-linearly independent — a consequence
  of algebraic independence via the monomial basis of `MvPolynomial`
  (`algebraicIndependent_linearIndependent_option`).

  Reusable general tools produced on the way: `DifferentialAdjoinBaseAbsorb.coe_differentialAdjoin_base`
  (adjoining over a derivation-closed base versus adjoining the base with the generators) and
  `DifferentialIndependentPerturbation` (differential independence, and the differential family
  matroid, are invariant under differentially algebraic perturbations).

## 2026-08-16 pass — state of the sweep

Closed this pass: `prescribed-gap-process-order-one-maximal-ht-profield`,
`additive-heat-aperture-zeta-zero-echo`, `additive-heat-aperture-shifted-zeta-echo-ladder`.

**Do not touch (another agent is mid-work):** the CCM unit-Riesz cluster
`ccm-unit-riesz-aperture-resolvent-weld`, `ccm-unit-riesz-coherent-polar-sampling-no-go`,
`ccm-unit-riesz-exponential-coherent-trace`, `ccm-unit-riesz-hankel-boundary-pulse` are untracked
new files and `ccm-four-unit-cesaro-curvature-wall` is modified in the working tree.  Re-check
`git status` before claiming any of them.

**Blocker map for the rest of the queue** (from the gate lines and the Lean-status sections):

- `gauss-component-quasi-inner-residue-hierarchy` — ~90% Lean; one named open core `(T)` (the
  `L²` limit of `gaussShiftedBlockDiag (B^{-2}((S̃* - T_δ)(Bf)))`), with a full band-split proof
  plan written at the end of the card.  **Best next target.**
- `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` — Theorem A (superlinear sampling
  rigidity) is self-contained real analysis; the existing Lean module only does the abstract
  jet-field core.  The section-4 application needs Conrey's positive-proportion theorem, which is
  an external input the card itself flags as a paper theorem.
- Differential-algebraic cards (`abelian-multiplication-tail-manin-horizon`,
  `embedded-manin-horizon-isogeny-reconstruction`, `isogeny-tail-maurer-cartan-holography`,
  `jet-horizon-translation-gauge-classification`, `differential-variational-building-balance-law`)
  need Kolchin topology / Manin maps / DCF, absent from mathlib and from this corpus.
- Geometry cards (`eigenplurivolume-log-crepant-orbifold`, `toric-log-calabi-yau-tail`,
  `noncompact-period-quotient-facet-escape-law`) need divisor/pluricanonical or toric geometry.
- `bessel-order-intensity-hypertranscendence` needs a special case of Dreyfus's
  DA-to-periodic-exponential theorem.
- 2026-08-16 — `scalar-ht-horizon-celestial-sphere` closed. New modules:
  `HTGeometry/ProjectiveHorizonCelestialSphere.lean` (choice independence of the derivative horizon
  of a Moebius coordinate, exact classification of horizon equality by the projective class of the
  denominator covector, injective `P^1(C)` realization, fractional-linear equivariance, exact join
  and exact meet at every ordered pair of distinct boundary points, parabolic and Cartan
  stabilizers, unique oriented geodesic through a pair, and a prime-field instance with no
  constants hypothesis); `HTGeometry/HyperbolicThreeSpaceBoundary.lean` (`H^3` as the unimodular
  positive-definite Hermitian `2x2` matrices, transitivity of `SL_2(C)` by explicit Cholesky
  factorization, isotropy `SU(2)`, and the visual boundary as light rays modulo positive scale
  identified with `P^1(C)`); `HTGeometry/ScalarHorizonCelestialBoundary.lean` (the weld). All three
  wired into the `HTGeometry` umbrella; capstones use only `propext`, `Classical.choice`,
  `Quot.sound`.
- 2026-08-16 — `nonlinear-rational-observation-curve-horizon-reconstruction` closed. New modules:
  `HTGeometry/JetPrincipalSymbolExtraction.lean` (the general Lüroth principal-symbol theorem
  `exists_mem_pd_ratio`, principal-symbol invariance under differentiation, and the identity-view
  affine/nonaffine dichotomy `differentialAdjoin_jets_eq_top_iff`);
  `HTGeometry/DerivationAlgebraicDescent.lean` (`mem_of_isAlgebraic_of_derivation_mem`, descent by
  differentiating the minimal polynomial, with a chain rule for polynomials with varying
  coefficients); `HTGeometry/RationalObservationCurveNormalization.lean` (the Main theorem
  `exists_differentialAdjoin_jetFamily_eq` and the normalized dichotomy
  `differentialAdjoin_jetFamily_eq_top_iff`). All umbrella-wired; capstones use only `propext`,
  `Classical.choice`, `Quot.sound`.
- 2026-08-16 — `toric-log-calabi-yau-tail` closed by `HTGeometry/ToricIsogenyTailLaw.lean`: the
  autonomous torus isogeny tail (`torusEndo_stableRangeCore_eq_torusInvariantMonomialField`), the
  pure-multiplication position/velocity law (`toricPowerIsogenyTail`), the character-matrix
  transport law, and the birational invariance of a stable tail. Umbrella-wired, axiom-clean.
- 2026-08-16 — `eigenplurivolume-log-crepant-orbifold` closed by
  `HTGeometry/EigenPluriVolumeLogCrepant.lean`: the weighted pluricanonical order law on an
  integral locally Noetherian scheme, the boundary pullback identity, the log-crepant invariance,
  the principal-divisor form, and the periodic coefficient-one fixed point. Umbrella-wired,
  axiom-clean.

### `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` — Theorem A is closed analytically

Four new unconditional modules, all axiom-clean and wired into the `RHTower` umbrella:

- `RHTower/SuperlinearSamplingAperiodicity.lean` — the aperiodicity lemma. A locally finite
  symmetric set of reals with superlinear counting misses infinitely many translates of every
  nonzero shift (`infinite_shiftFailure_of_superlinear`), through the window-congruence step
  (`exists_window_congruence`) and the linear counting bound for a union of finitely many
  progressions (`exists_linear_samplingCount_bound`).
- `RHTower/PrimeWeylSamplingIdealizerAnalytic.lean` — the analytic idealizer theorem on genuine
  Schwartz functions. Translated jet atoms (`jetAtom`, `jetAtomSchwartz`) realize the Kronecker
  delta at their centre and kill every derivative outside a cutoff ball; the separation radius
  comes from local finiteness (`exists_separating_radius`). Capstone
  `samplingIdealizer_collapse`, with `shiftWeylEval_eq_polynomial_multiplier`,
  `preservesSamplingIdeal_polynomialMultiplier`, `polynomial_conj_eq_of_infinite_real` and
  `ccr_scalar_eq_zero`. This supersedes the abstract-jet core of
  `RHTower/PrimeWeylSamplingIdealizer.lean`, which is kept as the purely algebraic statement.
- `RHTower/XiRealDivisorSampling.lean` — the real Xi divisor is locally finite and symmetric.
- `RHTower/TwoDilationDivisorMetric.lean` — multiplicative independence gives an irrational
  logarithmic ratio, the two-generator group is dense, a continuous function with a dense period
  group is constant, and a measure annihilating `|Xi|^2` is carried by the real divisor.

The card is **not** promoted. Its two remaining inputs are cited literature theorems, not new
content of the card, and both are large named sub-projects:

7. **Selberg's positive-proportion theorem** `N_0(T) >= c T log T` for critical-line zeros
   (equivalently Conrey's 2/5). In Lean terms this is exactly
   `SuperlinearSamples xiRealDivisor`; with it, section 4's `(23)` is one application of
   `samplingIdealizer_collapse`. Hardy--Littlewood's `N_0(T) >= cT` does not suffice — the lattice
   counterexample of the card's section 7.2 shows superlinearity is the sharp hypothesis.
8. **Bochner--Schwartz** for positive-definite tempered distributions (the integral representation
   of a translation-invariant positive form). Missing from mathlib.

### `gauss-component-quasi-inner-residue-hierarchy` — the named open core (T) is closed

Six new unconditional modules, all axiom-clean and umbrella-wired (card passes 43–44 hold the
details):

- `HTGeometry/LatticeTailSums.lean` — the six elementary `ℤ`-lattice weights (quadratic tail,
  harmonic band, punctured sub-unit power band, counting band, punctured harmonic band).
- `RHTower/GaussShiftRatioWeight.lean` — the ratio-weighted Parseval identity for the normalized
  shifted diagonal and the two regime bounds on the ratio.
- `RHTower/GaussSpikeBandSum.lean` — the spike carries ratio mass at most `(2 + 4K^(1/2))·n`.
- `RHTower/GaussDefectHighModeTail.lean` — the high-mode defect tail is
  `O(1/J) + O(log n / n)`.
- `RHTower/GaussLowModeKernelBound.lean` — spike/low-band separation, the truncation kernel bound,
  and the constant defect bound `5 + 3K` on the low band.
- `RHTower/GaussSpikeDefectVanishing.lean` — the assembly and the capstone
  `tendsto_norm_gaussShiftedBlockDiag_invSq_defect_zero`, which is exactly the statement (T) that
  pass 42 of the card named as its single open core for `m ≥ 2`.

Two facts worth carrying forward: the right exponent to push through the spike is `1/2` uniformly
in `m` (from `ρ⁴ ≤ ρ^(2m)`), not `1/m`; and for the iteration the amplitude decay exponent must
exceed `3/4`, not `1/2` — the high-mode term is the binding constraint. The card is not promoted:
what is left is the general-kernel restatement of (T) and the relative form of the `m`-fold
telescope.

### `rational-coarse-graining-orbifold-tail-classification` — the tail and its chain rule are formalized

The card's central object existed only through abstract stand-ins.  It is now a Lean object, and
so are the first two steps of the Casale-free route.  Two new modules, unconditional, axiom-clean,
`HTGeometry`-wired:

- `HTGeometry/EigenLogDerivNormalization.lean` — field-generic `(T1) → (T3)`
  (`eigen_logDeriv_of_chain_rule`: the logarithmic derivative of an eigenvector is an eigenvector
  with eigenvalue one, the chain rule being needed only at the eigenvector itself), and the
  coefficient eigen-relations of a scaled substitution (`coeff_eigen_pow_of_comp_scale`).
- `HTGeometry/JetRationalSubstitution.lean` — the rational substitution endomorphism `Phi_R` of the
  free jet field (well-definedness = algebraic independence of the substituted jets, via the
  corpus's Jacobian criterion with determinant `R'(y_0)^n`), its differentiality, the tail
  `orbifoldTail R hR = stableRangeCore (jetSubstitution R hR)` with `derivationClosed_orbifoldTail`
  and `orbifoldTailAlgEquiv`, the chain rule `pd_jetSubstitution_top`, the concrete `(T1)` and
  `(T3)`, and the Euler dichotomy at order one.

Two corrections worth carrying: the chain rule does **not** need "order ≤ m implies membership in
`adjoin C {y_0..y_m}`" — the total-derivative formula on the finite jet slice every element
inhabits suffices; and `(T3)` needs `ord u ≥ 1`, which is exactly what makes `R'(y_0)` a
`pd_M`-constant.

The card is **not** promoted.  What is left of the hard direction is the descent bookkeeping —
the `sigma`-stable pole multiset in the non-monomial branch and the partial-fraction step of the
`nu = 1` monomial branch — with no missing infrastructure between the card's setup and it.
Closing it also closes `floquet-orbifold-tail-emergence` and
`orbifold-tail-holographic-reconstruction`, whose only outstanding input is this classification.

- 2026-08-16 — `rational-coarse-graining-orbifold-tail-classification` advanced, not yet closed.
  Two new unconditional axiom-clean modules, both umbrella-wired:
  `HTGeometry/TwistedScalingDescent.lean` (generic: a twisted affine substitution on polynomials
  over a field preserves degrees, scales leading coefficients, and — for a coprime fraction that is
  an eigenvector — splits the cross identity into separate scalar relations for numerator and
  denominator, with the scalars linked by the eigenvalue; for a pure scaling every coefficient
  satisfies its own eigen-relation) and `HTGeometry/JetSubstitutionDescent.lean` (jet-side: the
  prefix fields `C(y_0,…,y_(M-1))`, their identification with the elements of order below `M` via
  the corpus support-kernel theorem, transcendence of `y_M` over them, `Phi_R`-stability and the
  restricted endomorphism, the affine normal form `Phi_R(y_M) = R'(y_0)·y_M + L` with `ord L < M`,
  and the transport `Phi_R(P(y_M)) = (twist P)(y_M)`).
  The resulting theorems: `exists_coprime_slicing`, `substitutionEigen_leadingRatio`,
  `exists_substitutionEigen_pred` (order descends by one, exponent shifts by the degree
  difference), `exists_isInvariantDifferential_of_substitutionEigen` and
  `exists_isInvariantDifferential_of_eigen` — *every* finite-order eigenvector of `Phi_R` carries an
  invariant differential with the same eigenvalue — `exists_nonzero_isInvariantDifferential_or_eq_one`
  (the weight is nonzero unless the eigenvalue is one), and, at order one where the substitution is
  an exact scaling, the complete hard direction
  `exists_nonzero_isInvariantDifferential_of_order_one`,
  `exists_nonzero_isInvariantDifferential_of_pd_one_ne_zero`, and
  `exists_differentialAdjoin_invariantCurrent_le_orbifoldTail`.
  Remaining for this card: the weight-zero exit above order one — at `M ≥ 2` the affine remainder
  `L` is nonzero so only the leading coefficients satisfy per-coefficient relations.  The route is
  recorded on the card: the next-to-leading coefficient of the split relation solves
  `Phi_R(t) - R'·t = -L`, so `z = y_M + t` normalizes the substitution to a pure scaling whenever
  `deg P ≥ 1`, after which the residual configuration is the explicit family `w = e·z^(-kappa)`
  with `e` a coefficient constant.  Closure count unchanged.

- 2026-08-16 (later) — `rational-coarse-graining-orbifold-tail-classification`, second pass.
  `TwistedScalingDescent.lean` gained the affine layer (`coeff_affine_pow`,
  `twistComp_affine_cocycle`: the two top coefficients of a split affine relation solve
  `Phi(g) = rho·g - (a+1)·L`).  `JetSubstitutionDescent.lean` gained the normalization
  (`exists_normalizing_shift`, `jetSubstitution_jet_add`, `HasNormalizingShift`,
  `lowerOrder_or_hasNormalizingShift`), the coordinate-generic slicing
  (`jetSubstitution_aeval_of_act`, `exists_coprime_slicing_of_coordinate`,
  `transcendental_add_algebraMap` reused from `RatFuncPositiveJetBranchSeparation`,
  `intermediateField_adjoin_add_algebraMap`), the full trichotomy
  `substitutionEigen_normalized_trichotomy`, and the capstone
  `exists_nonzero_isInvariantDifferential_or_hasNormalizingShift`: a nonconstant finite-order
  eigenvector of `Phi_R` forces either an invariant differential of nonzero weight and nonzero
  eigenvalue, or an invariant affine structure at some jet level at least two.  The card's step 2
  is thereby reduced from Casale's classification to its affine-structure companion.  Closure count
  unchanged.

- 2026-08-16 (later) — `gauss-component-quasi-inner-residue-hierarchy` advanced, not yet closed.
  Item 1 of the two remaining obligations is done: the one-step spike-vanishing core `(T)` is now
  proved for an arbitrary real symbol of modulus at most one with harmonic Fourier decay, and in
  particular for every member of the piecewise-exponential algebra the prime-scale amplitudes
  generate.  New/generalized: `norm_fourierCoeff_lpBoundedMulCLM_le`
  (`RHTower/GaussConvolutionCoefficient.lean`), `norm_fourierCoeff_symbol_truncate_le`
  (`RHTower/GaussLowModeKernelBound.lean`), and in `RHTower/GaussSpikeDefectVanishing.lean`
  `norm_sq_shiftedDiag_symbol_highMode_le`, `norm_sq_shiftedDiag_symbol_lowMode_le`,
  `tendsto_norm_gaussShiftedBlockDiag_symbol_defect_zero`,
  `tendsto_norm_gaussShiftedBlockDiag_invSq_defect_zero` (the pass-44 statement, now a corollary)
  and `tendsto_norm_gaussShiftedBlockDiag_expPiecewise_defect_zero`.
  Remaining: the relative `m`-fold telescope, whose invariant amplitude class must be two-piece
  because `S̃`, `S̃*` are Fourier multipliers degrading a uniform bound at the moving frequency
  `-n`; the card's pass-44 correction records the class and the `theta > 3/4` constraint.
  Closure count unchanged.

- 2026-08-16 (later still) — `prime-completion-annihilates-hypertranscendence-at-even-temperature`
  advanced from "no Lean" to "one reindexing short".  Two new modules, both unconditional and
  axiom-clean and umbrella-wired:
  `HTGeometry/PrimeOccupationCompletionProduct.lean` — the completed product
  `occupationProduct r x = ∏_{n≥1}(1 - x/n^r)`, its analyticity, the packet product over the
  smooth numbers and its cofinal convergence to the completion
  (`tendsto_smoothOccupationProduct`, using the new two-product comparison
  `norm_tprod_one_add_sub_tprod_one_add_le` added to `HTGeometry/InfiniteProductNearOne.lean`), the
  Euler boundary jet (`prod_primesBelow_eq_smoothZetaSum`, `tendsto_smoothZetaSum`,
  `tendsto_prod_primesBelow_riemannZeta`), the even-temperature collapse
  (`differentiallyAlgebraic_occupationProduct_of_even`), the explicit sine collapse
  (`pi_mul_occupationProduct_two`) and the card's equation (8)
  (`ode_of_sin_square_law`, `occupationProduct_two_ode` : `4xΦ'' + 6Φ' + π²Φ = 0`), plus unique
  factorization as an equivalence (`occupationEquivPNat`);
  `HTGeometry/PrimePowerOccupationHypertranscendence.lean` — hypertranscendence of every finite
  prime packet at every positive integer temperature
  (`hypertranscendental_primeOccupationFacePow`), by scaling the reciprocal-prime periods.
  Remaining: transport the occupation-vector indexing to the smooth-number indexing so that all
  items of the card refer to one object.  Closure count unchanged.

- 2026-08-16 — **`prime-completion-annihilates-hypertranscendence-at-even-temperature` CLOSED and
  promoted to stage 3.**  Every displayed equation of the exact theorem is an unconditional,
  axiom-clean Lean theorem about a single object, the occupation face
  `primeOccupationFacePow r S x = ∏_{ν ∈ ℕ^S}(1 - x ∏ p^{-r ν_p})`:
  `(1)` the definition; `(2)` `hypertranscendental_primeOccupationFacePow` — every packet of size
  at least two is hypertranscendental at every positive integer temperature; `(3)`+`(11)`
  `tendsto_primeOccupationFacePow` with `occupationEquivNatPos` (unique factorization as an
  equivalence with the positive integers); `(4)`
  `cexp_neg_logSeries_eq_primeOccupationFacePow` (the logarithmic normal expansion on the unit
  disc, by the Taylor series of `log(1-z)` and a Fubini rearrangement) and
  `smoothPowerSum_eq_prod` (the finite Euler factorization of every occupation power sum);
  `(5)` `tendsto_smoothPowerSum_riemannZeta`; `(6)` `deriv_primeOccupationFacePow_zero` and
  `tendsto_deriv_primeOccupationFacePow_zero`; `(7)`
  `differentiallyAlgebraic_occupationProduct_of_even`; `(8)` `pi_mul_occupationProduct_two` and
  `occupationProduct_two_ode` (`4xΦ'' + 6Φ' + π²Φ = 0`); `(9)`
  `periodsIntegrallyIndependent_primePowerNomePeriod`.
  New modules: `HTGeometry/PrimeOccupationCompletionProduct.lean`,
  `HTGeometry/PrimePowerOccupationHypertranscendence.lean`,
  `HTGeometry/PrimeOccupationCompletionLimit.lean`; `HTGeometry/InfiniteProductNearOne.lean`
  extended with the two-product comparison, first-order control, and the derivative at the origin
  of a linear-family product.  Closure count: 5 closed in this sweep, 31 cards remain in the folder.

- 2026-08-16 (later) — `rational-coarse-graining-orbifold-tail-classification`, third pass.
  `HTGeometry/RationalInvariantDifferential.lean` (new, unconditional, axiom-clean, umbrella-wired)
  transports the whole invariant-differential layer from the free jet field to `RatFunc C`:
  `exists_ratFunc_of_order_zero`, `ratFuncDeriv` with `ratFuncDeriv_X : (X)' = 1` and the
  bundled `ratFuncDerivation : Derivation C (RatFunc C) (RatFunc C)` (mathlib has no derivation on
  `RatFunc`), `ratFuncEval_ratFuncSubstitution`, and the two-way bridge
  `exists_ratFunc_relation_of_isInvariantDifferential` /
  `isInvariantDifferential_of_ratFunc_relation`.  The descent capstones now read classically:
  `exists_ratFunc_relation_of_order_one` and `exists_ratFunc_relation_or_hasNormalizingShift`.
  The remaining obligation for this card and for `floquet-orbifold-tail-emergence` and
  `orbifold-tail-holographic-reconstruction` is therefore a statement about rational maps alone:
  a degree-≥2 map with no nonzero-weight invariant rational differential has no rational affine
  connection.  Next substrate: the signed order on `RatFunc` (the corpus has `poleOrder` in
  `HTGeometry/RationalPoleOrder.lean`) with additivity and the composition law
  `ord_a(Q∘R) = ord_a(R − R(a))·ord_{R(a)}(Q)`.  Closure count unchanged.

- 2026-08-16 (fourth pass) — orbifold family advanced, no promotion.  Six new unconditional
  axiom-clean umbrella-wired modules build the divisor calculus the descent was waiting for and
  deliver the first complete non-existence results:
  `HTGeometry/RationalOrder.lean` (signed order `ord_a` on `RatFunc`, additivity, values on
  `algebraMap`/`C`/inverses/powers, vanishing criterion, finite support),
  `HTGeometry/RationalOrderComposition.lean` (`rootMultiplicity_comp` and the transport law
  `ord_a(Q∘R) = ord_{R(a)}(Q)·mult_a(R − R(a))`),
  `HTGeometry/RationalInvariantOrbit.lean` (`ratOrder_relation_transport`
  `ord_{R(a)}(Q)·e_a + k·m_a = ord_a(Q)`, its critical-free form, and the forward-orbit vanishing),
  `HTGeometry/RationalBackwardOrbit.lean` (existence of an injective critical-free backward orbit
  from any aperiodic non-postcritical point over an algebraically closed field, the resulting
  `ratOrder_eq_zero_of_aperiodic`, and `eq_C_of_weight_zero_relation`: a weight-zero relation
  forces a constant `Q` because substitution multiplies the degree),
  `HTGeometry/QuadraticNoInvariantDifferential.lean` (for `z²+1` and `(z−1)²` every relation
  `Q∘R·(R')^k = μQ` with `Q ≠ 0`, `μ ≠ 0` has `k = 0` and constant `Q`),
  `HTGeometry/QuadraticOrbifoldTail.lean` (the same statements on the jet field: no nonconstant
  eigenvector of order at most one, and eigenvalue one for any finite-order eigenvector),
  `HTGeometry/FloquetOrbifoldPeriodMaps.lean` (`R₂∘R₁ = z⁴`, `R₁∘R₂ = (z−1)⁴+1`, the two current
  transport identities with multiplier two, the weight-one invariant differentials of both period
  maps with eigenvalue four, and the tail inclusions `C⟨δy/y⟩ ≤ Tail(z⁴)`,
  `C⟨δy/(y−1)⟩ ≤ Tail((z−1)⁴+1)`).
  `HTGeometry/RationalInvariantDifferential.lean` gained `ratFuncDeriv_algebraMap`.
  The single residual obligation of all three orbifold cards is now the *fixed* branch
  `Φ_R(u) = u` with `u` nonconstant of finite order.  The normalized trichotomy descends it only to
  a configuration that is genuinely realizable (`w = e·y₁^(−κ)` at jet order one), because branches
  two and three hand back a coefficient ratio rather than `u`; the pass-4 section of
  `rational-coarse-graining-orbifold-tail-classification.md` records the exact obstruction.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (fifth pass) — `noncompact-period-quotient-facet-escape-law`: Siegel-programme step 4
  closed.  New module `HTGeometry/WeierstrassDivisionUniqueness.lean` (unconditional, axiom-clean,
  umbrella-wired) with `eqOn_of_continuousOn_of_finite_diff`,
  `eq_zero_of_degree_lt_of_continuous_multiple` and `weierstrass_division_unique`.  Steps 1–4 of the
  programme are now Lean-owned (step 3 was already done in `SliceWeierstrassDivision.lean`; the
  earlier note that it was open is superseded).  Remaining for the card: factoriality of the
  analytic germ ring, local reduced fractions, and the Siegel counting assembly — whose geometric
  half is `exists_finite_centres_forcing_vanishing` in `HTGeometry/SiegelVanishingCriterion.lean`.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (sixth pass) — `noncompact-period-quotient-facet-escape-law`: the germ interface of
  the Siegel programme is Lean-owned.  Four new unconditional axiom-clean umbrella-wired modules:
  `HTGeometry/AnalyticGermDomain.lean` (the germ ring is a nontrivial domain; every nonzero germ is
  regular in some direction), `HTGeometry/GermSliceAdmissible.lean` (`exists_sliceAdmissible_nhds`,
  the full admissibility package by two tube-lemma arguments),
  `HTGeometry/GermWeierstrassPreparation.lean` (`germ_weierstrass_preparation`, with the
  distinguished property `a_j(0) = 0`), `HTGeometry/GermWeierstrassDivision.lean`
  (`germ_weierstrass_division`).  Together with the pass-5 uniqueness theorem these express the
  local ring as a free module of rank `d` over the parameter ring modulo the distinguished
  polynomial.  Remaining for the card: factoriality of the germ ring by induction on the dimension,
  local reduced fractions, and the counting assembly.  Closure count unchanged: 31 cards remain.
  Also added `HTGeometry/AnalyticGermUnit.lean`: `isUnit_analyticGerm_iff` (a germ is a unit exactly
  when it does not vanish at the point), and the two structural germs of a split coordinate —
  `germCoord` (the distinguished coordinate) and `germTail` (the ring homomorphism pulling germs in
  the remaining variables back along the projection), with `germTail_analyticGermOf`.  These are the
  algebraic vocabulary in which a distinguished polynomial is an element of the germ ring, i.e. the
  form the factoriality induction consumes.

- 2026-08-16 (seventh pass) — `noncompact-period-quotient-facet-escape-law`, Siegel step 6 begun.
  Three further unconditional axiom-clean umbrella-wired modules:
  `HTGeometry/GermCoordinateChange.lean` — `shearLinearEquiv` (the shear `w ↦ w + w₀·c` with
  `c₀ = 0`, its inverse `w ↦ w − w₀·c`), `permLinearEquiv`, and
  `exists_regular_coordinate_change`: every nonzero germ becomes regular in the distinguished
  coordinate after a linear change of coordinates.  The automorphism is a transposition composed
  with a shear — no basis extension is needed, because the direction is first rescaled to have
  first coordinate one.
  `HTGeometry/GermLinearEquiv.lean` — `germLinearEquiv`: a linear automorphism induces a ring
  isomorphism of the germ rings at the origin (finite dimension makes the map and its inverse
  analytic), with `germLinearEquiv_analyticGermOf` and the packaged
  `exists_germLinearEquiv_regular`.
  `HTGeometry/GermPreparationAlgebraic.lean` — `germ_preparation_algebraic`: the Weierstrass
  preparation read as an identity in the local ring,

  ```text
  germ f = (germCoord^d + sum_(j<d) germTail(alpha_j) · germCoord^j) · u,   u a unit,
  ```

  with `alpha_j` vanishing at the origin.  Also `prepPolydisc` with its openness and the
  membership of the origin.  This is the form the factoriality induction consumes: an identity
  between elements of a ring, not between functions on a polydisc.
  Closure count unchanged: 31 cards remain in the folder.
  Added in the same pass: `HTGeometry/GermWeierstrassDivision.lean` strengthened to return the
  preparation unit alongside the division, so both identities come from a single admissibility
  package with the same radius, degree and coefficients; and
  `HTGeometry/GermDivisionAlgebraic.lean` with `germ_division_algebraic`, the pair of germ-ring
  identities

  ```text
  germ f = W · u,      germ g = q · W + sum_(j<d) germTail(beta_j) · germCoord^j,
  W = germCoord^d + sum_(j<d) germTail(alpha_j) · germCoord^j,   u a unit, alpha_j(0) = 0.
  ```

  The coercion computations are factored into `coe_germPolyTail` and `coe_germDistinguished` in
  `GermPreparationAlgebraic.lean`.

- 2026-08-16 (eighth pass) — `noncompact-period-quotient-facet-escape-law`, the two technical
  hearts of Siegel step 7.  Two new unconditional axiom-clean umbrella-wired modules:
  `HTGeometry/DistinguishedRootShrink.lean` — `norm_root_pow_le` (`‖ρ‖^d ≤ A·∑_{j<d} t^j` for a
  root of a monic polynomial with coefficients bounded by `A` and `‖ρ‖ ≤ t`), `norm_root_lt`,
  `exists_coeff_bound` (a coefficient bound achieving any prescribed root radius), and
  `exists_param_ball_roots_lt`: for a *moving* monic polynomial whose coefficients are continuous
  and vanish at the origin, every root inside the fixed disc lies inside any prescribed target disc
  once the parameter is close enough to the origin.  This is precisely where distinguishedness is
  used, and it is necessary: without it the independence below is false (`W = z − 5` on the unit
  disc divides the constant `1` there).
  `HTGeometry/SliceDivisionIndependence.lean` — `lowDegreePoly` with its coefficient, degree and
  evaluation lemmas, `eval_multisetProd_eq_multisetLinearProd`, and the capstone
  `lowDegree_and_quotient_eq_zero`: on a disc containing every root of the monic polynomial of a
  multiset, `Q(z)·W(z) + ∑_{j<d} B_j z^j = 0` with `Q` continuous forces every `B_j` to vanish and
  then `Q` itself to vanish.  This is the independence half of the free-module statement — the
  powers `1, z, …, z^{d−1}` are independent over the parameter ring modulo the Weierstrass
  polynomial — and rests on the pass-5 low-degree vanishing theorem together with the finite-set
  continuity lemma.
  Remaining for step 7: assemble these into the germ-ring independence (shrink to a common polydisc
  using `exists_param_ball_roots_lt`, apply `lowDegree_and_quotient_eq_zero` for each parameter),
  then the divisibility and irreducibility transfer to `C{z'}[X]`, then Gauss and the induction on
  the dimension.  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (ninth pass) — `noncompact-period-quotient-facet-escape-law`: the germ-level
  free-module statement is proved.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/GermDivisionIndependence.lean` with `prepPolydisc_subset_ball` and the capstone
  `germ_division_independence`: for a germ regular in the distinguished coordinate there are a
  degree `d`, coefficients `alpha_j` vanishing at the origin and a unit `u` with
  `germ f = W · u`, `W = germCoord^d + sum_(j<d) germTail(alpha_j)·germCoord^j`, **and**

  ```text
  q · W + sum_(j<d) germTail(beta_j) · germCoord^j = 0  ==>  q = 0 and every beta_j = 0.
  ```

  Together with `germ_division_algebraic` this is the full free-module structure: the germ ring in
  `n+1` variables is free of rank `d` over the parameter ring modulo `W`, on the basis
  `1, germCoord, …, germCoord^(d-1)`.  The proof shrinks the polydisc once — that is where
  distinguishedness enters, through `exists_param_ball_roots_lt` — and then applies
  `lowDegree_and_quotient_eq_zero` parameter by parameter.

  Duplication check (corpus search on "unique factorization analytic germ local ring",
  "Weierstrass polynomial irreducible distinguished divisibility", "free module rank Weierstrass
  division parameter ring", "coprime meromorphic germ reduced fraction local"): the only
  pre-existing related assets are the two *slice-level* division modules
  `HTGeometry/WeierstrassDivision.lean` (`divQuot`, `divRem`, `weierstrass_division_divQuot`) and
  `HTGeometry/SliceWeierstrassDivision.lean`, the germ-ring basics in `AnalyticGermRing.lean` /
  `AnalyticGermMaximalIdeal.lean`, and the DVR criteria in `LocalNoetherianNormalDVR.lean`.  None
  of them states factoriality or any germ-level division, so nothing above duplicates existing work.

  Remaining for step 7: the divisibility and irreducibility transfer from `C{z}` to `C{z'}[X]`
  (a distinguished factor of a distinguished polynomial is distinguished, by uniqueness of the
  preparation), then Gauss and the induction on the dimension.

- 2026-08-16 (tenth pass) — `noncompact-period-quotient-facet-escape-law`: the divisibility
  transfer.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/GermPolynomialDivisibility.lean`.  `lowDegreePoly` in
  `HTGeometry/SliceDivisionIndependence.lean` was generalized from `C` to an arbitrary commutative
  ring so it can carry the coefficients of a distinguished polynomial over the parameter germ ring.
  New: `germEval` (the ring homomorphism `C{z'}[X] → C{z}` evaluating at the distinguished
  coordinate, as `eval₂RingHom (germTail n) (germCoord n)`), `distPoly` with `distPoly_monic` and
  `degree_distPoly`, `germEval_eq_of_degree_lt`, `germEval_distPoly`, the predicate
  `GermIndependent` (exactly the property `germ_division_independence` supplies),
  `eq_zero_of_germEval_eq_zero` (evaluation is injective in degrees below `d`), and the capstone

  ```text
  dvd_germEval_iff : germEval W | germEval G  <->  W | G   in  C{z'}[X].
  ```

  The proof divides `G` by the monic `W` in the polynomial ring, evaluates, and applies the
  germ-level independence to the remainder, whose degree is below `d`.  This is the step that makes
  the factoriality induction work: from here a distinguished factor of a distinguished polynomial is
  a polynomial factor, so irreducibility can be tested in `C{z'}[X]`, where Gauss applies to the
  inductive hypothesis.  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (eleventh pass) — `noncompact-period-quotient-facet-escape-law`: the circularity in
  Siegel step 7b is removed.  `HTGeometry/DistinguishedRootShrink.lean` gained the Cauchy root
  bound `norm_root_le_cauchy` (`‖rho‖ ≤ max 1 (A·d)` for a root of a monic polynomial with
  coefficients bounded by `A`) and `exists_param_ball_roots_lt_monic`, the version with **no a
  priori bound** on the roots.  New module
  `HTGeometry/DistinguishedGermIndependence.lean`: `movingPoly` with its monicity, degree,
  evaluation, root count (`ℂ` algebraically closed) and
  `multisetLinearProd_roots_movingPoly`; the capstone
  `germIndependent_of_distinguished` — *every* distinguished polynomial has the free-module
  independence property, not only the Weierstrass polynomial of a prepared germ; and
  `distPoly_eq_of_unit_mul`, the **uniqueness of the Weierstrass preparation**: two distinguished
  polynomials whose evaluations differ by a unit are equal, by mutual divisibility through
  `dvd_germEval_iff` plus monicity.
  This was the missing piece: previously independence was only available for polynomials produced
  by a preparation, so comparing a product of two prepared polynomials with a third was circular.
  Remaining for the card: the irreducibility transfer (a factorization of a distinguished
  polynomial in the germ ring becomes a polynomial factorization, via preparation of the factors
  and this uniqueness), then Gauss and the induction on the dimension; then local reduced fractions
  and the counting assembly.  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twelfth pass) — `noncompact-period-quotient-facet-escape-law`: the regularity layer.
  New unconditional axiom-clean umbrella-wired module `HTGeometry/GermSliceRegular.lean`:
  `analyticAt_consZero`, the ring homomorphism `germSlice` restricting a germ at the origin of
  `C^(n+1)` to the first coordinate axis (built from `analyticGermPullback`),
  `germSlice_analyticGermOf`, and `germSlice_ne_zero_iff` — a germ is regular in the distinguished
  coordinate exactly when its slice is nonzero.  Since `germSlice` is a ring homomorphism into a
  domain, regularity is multiplicative: `germSlice_ne_zero_of_mul_ne_zero` and
  `germSlice_mul_ne_zero`.  That is what will let a single linear change of coordinates make
  finitely many germs regular at once — apply `exists_regular_coordinate_change` to their product.
  Finally `germSlice_germEval_distPoly_ne_zero`: a distinguished polynomial has slice `z^d`, hence
  is always regular.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (thirteenth pass) — `noncompact-period-quotient-facet-escape-law`: the factorization
  transfer.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/GermDistinguishedFactorization.lean`; `natDegree_distPoly` was added to
  `GermPolynomialDivisibility.lean` and `analyticGermValue_germTail` to `GermSliceRegular.lean`.
  Contents: `monic_eq_distPoly` (a monic polynomial is its own distinguished normal form),
  `map_distPoly_eq_X_pow` and `coeff_eq_zero_of_map_eq_X_pow` (distinguishedness is exactly
  `map (value) P = X^(natDegree P)`), `coeff_mul_eq_zero_of_distinguished` (in that form
  distinguishedness is visibly multiplicative),
  `analyticGermValue_germEval_distPoly` and `not_isUnit_germEval_distPoly` (a distinguished
  polynomial of positive degree has a non-unit germ), and the capstone

  ```text
  exists_distPoly_factorization :
    germEval W = g · h  ==>  g = germEval W_g · u,  h = germEval W_h · v,  W = W_g · W_h
  ```

  with `W_g, W_h` distinguished and `u, v` units.  The proof uses that regularity is multiplicative
  to prepare both factors, then `distPoly_eq_of_unit_mul` to identify the product of their
  distinguished polynomials with `W`.  Degenerate degrees are handled through
  `not_isUnit_germEval_distPoly`.
  With this, a germ-ring factorization of a distinguished polynomial *is* a polynomial
  factorization, so irreducibility can be tested in `C{z'}[X]`.  Remaining: the induction on the
  dimension (with Gauss for `C{z'}[X]` and the simultaneous-regularization trick from
  `germSlice_mul_ne_zero`), then local reduced fractions and the counting assembly.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (fourteenth pass) — `noncompact-period-quotient-facet-escape-law`: the irreducibility
  transfer.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/GermIrreducibleTransfer.lean`:
  `eq_X_pow_of_monic_of_mul_eq_X_pow` — a monic factor of `X^D` in `C[X]` is a power of `X`, since
  each of its roots is a root of `X^D` hence zero, and a monic complex polynomial is the product of
  its linear factors;
  `coeff_eq_zero_of_monic_mul_eq_distPoly` — consequently a monic factor of a distinguished
  polynomial is distinguished (apply the coefficientwise value map);
  `exists_monic_factorization` — any factorization of a monic polynomial can be normalized so that
  both factors are monic, by moving the leading coefficients (units, since their product is one)
  across, with the associatedness recorded;
  `irreducible_germEval_of_irreducible` — if a distinguished polynomial of positive degree is
  irreducible in `C{z'}[X]` then its germ is irreducible in `C{z}`.  The proof feeds a germ-ring
  factorization through `exists_distPoly_factorization` and reads off that one of the two
  distinguished factors is a monic unit, hence `1`.
  Remaining: the converse direction (which now follows from the above plus the factorization of the
  polynomial in the UFD `C{z'}[X]`), the induction on the dimension, then local reduced fractions
  and the counting assembly.  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (fifteenth pass) — **Siegel step 7 is CLOSED: the ring of convergent power series in
  `n` complex variables is a unique factorization domain, unconditionally and axiom-clean.**
  Two new umbrella-wired modules complete the argument.

  `HTGeometry/GermDivisionRemainder.lean`.  The key structural observation:
  *every* germ, regular or not, can be divided by the distinguished polynomial of a regular germ —
  the regularity hypothesis of the Weierstrass division applies to the divisor, not the dividend.
  `exists_germ_division` establishes this (identifying the polynomial produced by
  `germ_division_algebraic` with the given one through `distPoly_eq_of_unit_mul`);
  `dvd_iff_remainder_eq_zero` says divisibility is the vanishing of the remainder; and
  `prime_germEval_of_prime` concludes that a distinguished polynomial prime in `C{z'}[X]` has a
  prime germ.  This is what removes the last obstruction: primality quantifies over arbitrary
  factors `g`, `h`, which a coordinate change adapted to the divisor cannot be assumed to
  regularize, and reduction modulo the divisor sidesteps the issue entirely.

  `HTGeometry/GermFactorial.lean`.  `exists_prime_factors_of_distPoly` — strong induction on the
  degree: a distinguished polynomial of positive degree is either irreducible in `C{z'}[X]`, hence
  prime there and prime as a germ, or splits into two monic factors, which
  `coeff_eq_zero_of_monic_mul_eq_distPoly` shows are again distinguished and whose degrees are
  strictly smaller.  `exists_prime_factors_germ` — an arbitrary nonzero germ is carried by a linear
  change of coordinates to a regular one (`exists_germLinearEquiv_regular`), prepared, factored, and
  pulled back, primality being preserved by the induced ring isomorphism.  Finally the instance

  ```text
  instUniqueFactorizationMonoidAnalyticGerm : ∀ n, UniqueFactorizationMonoid (AnalyticGerm (0 : Fin n → C))
  ```

  by induction on the dimension, the base case being that germs on a one-point space form a field.
  Mathlib has no convergent-power-series ring, let alone its factoriality.

  Remaining for `noncompact-period-quotient-facet-escape-law`: step 8, local reduced fractions for
  meromorphic germs (now pure UFD algebra plus the comparison of a global entire quotient with a
  local reduced one), and step 9, the Siegel counting assembly, whose geometric half
  (`exists_finite_centres_forcing_vanishing`) is already Lean-owned.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (sixteenth pass) — `noncompact-period-quotient-facet-escape-law`: the algebra of Siegel
  step 8.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/GermReducedFraction.lean`; `AnalyticGermDomain.lean` gained the `IsDomain` instance.
  `exists_reduced_fraction` — in any GCD domain, dividing numerator and denominator by their
  greatest common divisor leaves a relatively prime pair with the same cross product.  The
  relative primality is proved without invoking primes: a common divisor `z` of the reduced pair
  makes `gcd·z` divide both `a` and `b`, hence divide `gcd`, and cancelling `gcd` exhibits `z` as a
  unit.
  `associated_den_of_reduced` and `associated_num_of_reduced` — two reduced presentations of the
  same fraction have associated denominators and associated numerators; the cross-multiplied
  identity plus relative primality makes each denominator divide the other.
  Specialized to the germ ring through `instUniqueFactorizationMonoidAnalyticGerm` and
  `UniqueFactorizationMonoid.toGCDMonoid`: `exists_reduced_germ_fraction`,
  `associated_den_of_reduced_germ`, `associated_num_of_reduced_germ`.
  This is exactly the comparison the Siegel count needs on the overlaps of a cover: the ratio of two
  *reduced* local denominators of the same meromorphic function is a unit, hence bounded on
  compacta, whereas the ratio of two arbitrary presentations is unbounded — the obstruction the card
  diagnosed for the global entire presentation.
  Remaining for the card: step 9, the counting assembly (Schwarz gain, jet dimension count, and the
  periodicity step), whose geometric half `exists_finite_centres_forcing_vanishing` is Lean-owned.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (seventeenth pass) — `noncompact-period-quotient-facet-escape-law`: the analytic form
  of step 8, and an inventory of what step 9 already owns.  New unconditional axiom-clean
  umbrella-wired module `HTGeometry/GermRatioBound.lean`:
  `exists_norm_bound_of_analyticAt` (an analytic function is bounded on a small ball),
  `exists_norm_lower_bound_of_ne_zero` and `exists_lower_bound_of_isUnit` (a unit germ has a
  representative bounded away from zero — by continuity, no compactness needed), and
  `exists_ratio_bound_of_associated`: two associated germs have representatives with
  `‖B₂ w‖ ≤ C·‖B₁ w‖` on a ball.  Composed with `associated_den_of_reduced_germ` this is the
  comparison constant the counting step needs on the overlaps of a cover, and it is exactly what the
  global entire presentation cannot supply.

  Inventory for step 9 — the corpus already owns, from the earlier passes on this card:
  `HTGeometry/KernelOfDimensionDrop.lean` (`exists_ne_zero_apply_eq_zero_of_finrank_lt`,
  `exists_ne_zero_forall_apply_eq_zero_of_finrank_lt`) for the dimension count;
  `HTGeometry/MultiIndexCounts.lean` (`card_le_pow_of_sum_lt`, `pow_le_card_of_box_subset`) for the
  multi-index comparison; `HTGeometry/SelfImprovingBound.lean` (`eqOn_zero_of_le_mul_bound`) for the
  periodicity step; `HTGeometry/SiegelVanishingCriterion.lean`
  (`exists_finite_centres_forcing_vanishing`) for the geometric assembly, on
  `LatticeFundamentalCover.lean`, `PeriodicCoverVanishing.lean`, `FamilyCoverVanishing.lean` and
  `CompactQuotientSpan.lean`; and `HTGeometry/DifferentialAlgebraicFromRelation.lean`
  (`differentialAlgebraicOver_of_aeval_eq_zero`) for the interface to the corpus's
  differential-algebraicity predicate.  What remains is the assembly itself: cover a fundamental
  domain by finitely many polydiscs carrying reduced local presentations, use the ratio bound on
  overlaps to make the constants uniform, and feed the count into the vanishing criterion.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (eighteenth pass) — `noncompact-period-quotient-facet-escape-law`: the arithmetic of
  the Siegel count.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/SiegelDegreeCount.lean` with `siegel_count_lt`, `exists_siegel_degree` and
  `eventually_siegel_count`:

  ```text
  K · A ^ n < m   ==>   K · (A·m) ^ n < (m + 1) ^ (n + 1).
  ```

  This is the inequality that makes the count close, in the exact shape the assembly needs.
  Clearing denominators from a polynomial of degree at most `(n+1)·m` in the values of `n+1`
  meromorphic functions raises the comparison constant to the power `(n+1)·m`, so the Schwarz gain
  forces the jet order to grow only linearly in `m`, `N = A·m`; the number of conditions is then at
  most `K·(A·m)^n` — `K` centres, each imposing the vanishing of the complex Taylor jets of order
  below `N` in `n` variables — while `MultiIndexCounts.pow_le_card_of_box_subset` gives at least
  `(m+1)^(n+1)` free coefficients.  Since `n < n+1` the coefficients win for every large `m`.  This
  is the single place where the dimension of the torus enters, and it is why the bound is
  `trdeg ≤ dim` rather than anything weaker.

  Step 9 therefore has all of its ingredients Lean-owned: the Schwarz gain
  (`OrderNSchwarz.norm_le_of_iteratedFDeriv_vanish`,
  `PolydiscCoeffVanishing.norm_le_of_polydiscCoeff_vanish`), the chartwise vanishing criterion with
  a comparison constant (`FamilyCoverVanishing.eqOn_zero_of_family_cover`), the compact fundamental
  set and its finite cover (`LatticeFundamentalCover`), the self-improving bound
  (`SelfImprovingBound`), the dimension-drop kernel vector (`KernelOfDimensionDrop`), the
  multi-index counts (`MultiIndexCounts`), the comparison constant on overlaps (this session's
  `GermReducedFraction` + `GermRatioBound`), the degree arithmetic (this module), and the interface
  to differential algebraicity (`DifferentialAlgebraicFromRelation`).  What remains is to wire them
  together on a concrete cover.  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (nineteenth pass) — `noncompact-period-quotient-facet-escape-law`: the counting step of
  Siegel step 9.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/SiegelCountingStep.lean`:
  `finrank_coeffSpace` — the coefficient space of polynomials whose exponents in `n+1` variables are
  all at most `m` has dimension exactly `(m+1)^(n+1)`;
  `finrank_conditionSpace` — the Taylor-condition space of `K` centres and a finite set `S` of
  multi-indices has dimension `K·|S|`;
  `exists_ne_zero_of_siegel_count` — any linear map between them has a nonzero kernel vector once
  `K · N^n < (m+1)^(n+1)`, the bound `|S| ≤ N^n` coming from
  `MultiIndexCounts.card_le_pow_of_sum_lt` and the kernel from
  `KernelOfDimensionDrop.exists_ne_zero_apply_eq_zero_of_finrank_lt`;
  `exists_ne_zero_of_siegel_count_of_large` — the same with the inequality discharged by
  `siegel_count_lt`, i.e. for every degree beyond `K·A^n` when the jet order grows linearly,
  `N ≤ A·m`.

  Design note worth keeping: the Taylor-coefficient formulation is forced.  Counting with
  `iteratedFDeriv` jets instead would make the target the space of *non-symmetric* `j`-multilinear
  maps, of dimension `n^j`, whose sum over `j < N` is exponential in `N` rather than `N^n` — and the
  count would never close.  The corpus's Schwarz estimate is available in coefficient form
  (`PolydiscCoeffVanishing.norm_le_of_polydiscCoeff_vanish`), which is the matching half.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twentieth pass) — `noncompact-period-quotient-facet-escape-law`: the bridge from a
  coefficient vector to a genuine polynomial relation.  New unconditional axiom-clean
  umbrella-wired module `HTGeometry/SiegelPolynomial.lean`:
  `siegelExp` with `siegelExp_injective` — the exponent multi-index of a point of the box, injective
  because distinct boxes give distinct monomials;
  `siegelPoly` and `coeff_siegelPoly` — the polynomial attached to a coefficient vector, whose
  coefficient at the corresponding monomial is exactly the given entry, hence
  `siegelPoly_ne_zero`: a nonzero vector gives a nonzero polynomial, which is what makes the
  relation produced by the count nontrivial;
  `eval_siegelPoly` and `siegelCombination` with `eval_siegelPoly_eq_siegelCombination` — the
  evaluation of the polynomial at a family of functions is the coefficient combination;
  `siegelCombination_add`, `siegelCombination_smul` — linearity in the coefficient vector, so the
  Taylor-condition map of the counting step is a genuine `LinearMap`;
  `contDiff_siegelCombination` — smoothness, so the Schwarz estimate applies.
  Together with `SiegelCountingStep` and `DifferentialAlgebraicFromRelation` the chain
  *count → nonzero coefficient vector → nonzero polynomial → algebraic relation → differential
  algebraicity* is now complete except for the analytic middle: producing the Taylor-condition map
  from a cover and running the Schwarz gain against the overlap constant.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-first pass) — `noncompact-period-quotient-facet-escape-law`: the
  Taylor-condition map, the analytic middle of Siegel step 9.  New unconditional axiom-clean
  umbrella-wired module `HTGeometry/SiegelCoeffMap.lean`; `SiegelPolynomial.lean` gained
  `continuous_siegelCombination`.
  `polydiscCoeff_add` and `polydiscCoeff_const_smul` — the Cauchy coefficient of a polydisc is
  additive and homogeneous in the integrand, the integrability supplied by
  `polydiscCoeff_integrable` from continuity;
  `siegelCoeffMap` — the resulting **linear** map from the coefficient space of the exponent box to
  the space of Taylor conditions indexed by centres and multi-indices, with `siegelCoeffMap_apply`;
  `exists_ne_zero_poly_polydiscCoeff_eq_zero` — the counting step applied to it: once
  `K·N^n < (m+1)^(n+1)` there is a nonzero coefficient vector all of whose prescribed Cauchy
  coefficients vanish at every centre.

  Note the shape this forces, and why it is the right one: the number of functions is `n+1` and the
  ambient dimension is `n`, so the counting lemma's two indices coincide.  That coincidence *is* the
  statement `trdeg ≤ dim`; if the functions were fewer the count would be vacuous and if more it
  would fail.
  What remains of step 9: run `PolydiscCoeffVanishing.norm_le_of_polydiscCoeff_vanish` against the
  overlap constant of `GermRatioBound` on a cover from `LatticeFundamentalCover`, and close with
  `SelfImprovingBound` / `FamilyCoverVanishing`.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-second pass) — `noncompact-period-quotient-facet-escape-law`: **the Siegel
  gain.**  New unconditional axiom-clean umbrella-wired module `HTGeometry/SiegelGain.lean`;
  `SiegelPolynomial.lean` gained `differentiable_siegelCombination`.
  `lowDegreeIndices` with `mem_lowDegreeIndices` — the multi-indices of total degree below `N`, as a
  `Finset`, the box bound coming from `Finset.single_le_sum`;
  `exists_ne_zero_siegel_gain` — the counting step and the multi-index Schwarz estimate combined:

  ```text
  card ι · N^n < (m+1)^(n+1)  ==>  ∃ a ≠ 0, ∀ M bounding the combination on the large tori,
      ‖G (c i + y)‖ ≤ M · (N+1)^n · (r/R)^N · ∑' (j+1)^n (r/R)^j   for ‖y‖ ≤ r.
  ```

  The bound `M` on the large polydiscs is deliberately left universally quantified *after* the
  coefficient vector is fixed, so the statement can be applied once the comparison constant of a
  cover is known — which is exactly how a periodicity argument converts the gain into vanishing,
  and why the quantifier order matters.
  Step 9 now needs only the geometric closing: choose the cover
  (`LatticeFundamentalCover.exists_finite_centres_of_compactSpace_quotient`), take the comparison
  constant from `GermRatioBound` on the reduced presentations, pick `N` linear in `m` so the
  Schwarz factor beats it, and apply `SelfImprovingBound` / `FamilyCoverVanishing`; then
  `siegelPoly_ne_zero` and `differentialAlgebraicOver_of_aeval_eq_zero` give the conclusion.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-third pass) — `noncompact-period-quotient-facet-escape-law`: the closing
  mechanism of Siegel step 9.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/SiegelGainVanishing.lean` with `eqOn_zero_of_siegel_gain`:

  ```text
  a Schwarz gain θ on the small polydiscs, a chart comparison C from the small polydiscs to the
  large tori, and C·θ < 1   ==>   the function vanishes on every small polydisc.
  ```

  The maximum over the compact small polydiscs exists, the comparison carries it to the tori, the
  gain carries it back improved by `C·θ`, and a maximum that improves itself is zero.  It is stated
  for a single function with the two hypotheses in exactly the quantifier shape
  `exists_ne_zero_siegel_gain` produces, so the two compose directly.
  The comparison constant `C` is what periodicity supplies — for a periodic function the large tori
  are congruent to points of the fundamental domain — and the reduced local presentations of
  `GermReducedFraction`/`GermRatioBound` are what make it finite and uniform.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-fourth pass) — `noncompact-period-quotient-facet-escape-law`: the chartwise
  objects of Siegel step 9.  `HTGeometry/SiegelGainVanishing.lean` gained
  `eqOn_zero_of_family_siegel_gain`, the chartwise form of the closing mechanism — on each chart the
  function is only a local representative and what relates the charts is the comparison constant,
  which is the form the Siegel argument actually needs.
  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/SiegelClearedCombination.lean`: `siegelHomCombination`, the denominator-cleared
  combination `∑_β a_β ∏_k A_k^(β_k) B_k^(m−β_k)`, with `siegelHomCombination_eq`

  ```text
  siegelHomCombination A B m a w = siegelCombination (A/B) a w · ∏_k (B_k w)^m   (B_k w ≠ 0),
  ```

  its additivity, homogeneity, continuity, smoothness and differentiability, and
  `siegelCombination_eq_zero_of_hom_eq_zero`.  The exponents `m − β_k` stay nonnegative precisely
  because the coefficient box bounds every `β_k` by `m` — that is what the box normalization was for.
  This is the object a Siegel count estimates chartwise: it is holomorphic where the quotients are
  not, and the comparison constant between two charts is the `m`-th power of the ratio of their
  denominators, bounded by `GermRatioBound` exactly because reduced local presentations have
  associated denominators.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-fifth pass) — `noncompact-period-quotient-facet-escape-law`: **the chartwise
  Siegel assembly.**  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/SiegelChartAssembly.lean`:
  `siegelHomCoeffMap` — the chartwise Taylor-condition map.  The point is that the estimated object
  on each chart is the cleared combination of a *single* coefficient vector, so the conditions across
  all charts still assemble into one linear map on the coefficient space and the counting step still
  applies;
  `exists_ne_zero_chart_siegel_gain` — a single nonzero coefficient vector whose cleared combination
  gains the Schwarz factor on every chart simultaneously;
  `exists_ne_zero_chart_vanishing` — feeding that gain and a chart comparison constant into
  `eqOn_zero_of_family_siegel_gain`:

  ```text
  card ι · N^n < (m+1)^(n+1)   and   C · ((N+1)^n (r/R)^N ∑' (j+1)^n (r/R)^j) < 1
    ==>  ∃ a ≠ 0, every cleared combination vanishes on its small polydisc.
  ```

  This is the general assembly of step 9: everything except the *geometric input* `hcomp`, the chart
  comparison, which is where periodicity of the meromorphic functions and the reduced local
  presentations enter, and the final passage from the vanishing of the cleared combinations to the
  polynomial relation (`siegelCombination_eq_zero_of_hom_eq_zero`) and thence to
  `differentialAlgebraicOver_of_aeval_eq_zero`.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-sixth pass) — `noncompact-period-quotient-facet-escape-law`: **the algebraic
  relation, closing the general Siegel machine.**  New unconditional axiom-clean umbrella-wired
  module `HTGeometry/SiegelAlgebraicRelation.lean`: `siegelCombination_congr` (the combination
  depends on the functions only through their values at the point) and

  ```text
  exists_ne_zero_poly_eval_eq_zero :
    card ι · N^n < (m+1)^(n+1),  C · Schwarz factor < 1,  chart quotient presentations
      ==>  ∃ P ≠ 0 in C[X_0,…,X_n],  eval (f_0,…,f_n) P = 0  on every small polydisc.
  ```

  This is the whole Siegel machine in general form: counting, Schwarz gain, self-improvement,
  denominator clearing and the passage back to the quotients, all unconditional.  Its two inputs are
  the chart comparison `hcomp` — supplied by periodicity together with the reduced local
  presentations of `GermReducedFraction`/`GermRatioBound` — and the chart presentations themselves.
  For the card these are the finite cover of a fundamental parallelotope from
  `LatticeFundamentalCover` and the reduced fractions at its centres; the remaining work is that
  geometric instantiation, no longer any of the analysis.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-seventh pass) — `noncompact-period-quotient-facet-escape-law`: the geometric
  input reduced to a transition structure.  `HTGeometry/SiegelChartAssembly.lean` gained
  `hcomp_of_transition` and `exists_ne_zero_chart_vanishing_of_transition`:

  ```text
  if every point of a large torus is, up to a factor of modulus at most C, the value of some chart
  at a point of its small polydisc, then the chart comparison constant is C.
  ```

  This isolates exactly what the geometry has to provide, and in the form periodicity provides it:
  the translate of a torus point by a period lands in the fundamental set, hence in some chart's
  small polydisc; the values of the *quotients* agree there because the functions are periodic; and
  the transition factor is the ratio of the two chart denominators raised to the degree, bounded
  because reduced local presentations have associated denominators
  (`associated_den_of_reduced_germ` + `exists_ratio_bound_of_associated`).
  With `exists_ne_zero_poly_eval_eq_zero` the whole analytic machine of step 9 is therefore closed;
  the outstanding work is the construction of the transition data itself from the lattice and the
  cover, i.e. bookkeeping over `LatticeFundamentalCover`, not analysis.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-eighth pass) — `noncompact-period-quotient-facet-escape-law`: the two halves of
  the transition data.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/SiegelLatticeTransition.lean`:
  `exists_period_centre_of_compactSpace_quotient` — for a subgroup with compact quotient and any
  prescribed radius there is a *finite* set of centres such that **every** point of the space is
  congruent, modulo the subgroup, to a point within that radius of one of them.  This restates the
  finite cover of a fundamental set as a statement about arbitrary points, which is the form the
  transition needs (the torus points are arbitrary, not confined to the fundamental set);
  `siegelCombination_periodic` and `siegelHomCombination_periodic` — a combination, and a cleared
  combination, of periodic data is periodic, because the combination depends on the functions only
  through their values at the point.
  Together these say the value of the combination of the quotients at any torus point equals its
  value at a point of some small polydisc, which is exactly what makes the chart comparison constant
  of `hcomp_of_transition` finite: the residual transition factor is then only the ratio of the two
  chart denominators, bounded by `GermRatioBound`.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (twenty-ninth pass) — `noncompact-period-quotient-facet-escape-law`: **the full
  chain composes.**  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/SiegelPeriodicTransition.lean`:
  `htrans_of_periodic_transfer` — a torus point is congruent to a point of a small polydisc, so the
  transition comes with a translation by a period; periodicity of the chart data discharges it, and
  what is left is exactly the transition structure `hcomp_of_transition` consumes;
  `exists_ne_zero_chart_vanishing_of_periodic` — the chartwise assembly with the period discharged;
  `exists_ne_zero_poly_eval_eq_zero_of_periodic` — **the full chain**, from the periodic transition
  structure to a nonzero polynomial annihilating the chart quotients on the small polydiscs.

  The Siegel machine of step 9 is therefore complete and composed end to end: lattice cover
  (`exists_period_centre_of_compactSpace_quotient`) → periodic transition
  (`siegelHomCombination_periodic`) → chart comparison (`hcomp_of_transition`) → counting
  (`exists_ne_zero_of_siegel_count`, `siegel_count_lt`) → Schwarz gain
  (`exists_ne_zero_chart_siegel_gain`) → self-improvement (`eqOn_zero_of_family_siegel_gain`) →
  denominator clearing (`siegelCombination_eq_zero_of_hom_eq_zero`) → nonzero polynomial
  (`siegelPoly_ne_zero`).  Its remaining inputs are the *data* of the specific torus: the reduced
  local presentations at the cover centres and the resulting bound on the denominator ratios, both
  of which `GermReducedFraction` and `GermRatioBound` supply.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (thirtieth pass) — `noncompact-period-quotient-facet-escape-law`: factoriality at every
  point.  New unconditional axiom-clean umbrella-wired module
  `HTGeometry/GermTranslationFactorial.lean`: `analyticAt_sub_const`, `analyticAt_add_const`,
  `germTranslate` — translation is an analytic change of coordinates, so
  `AnalyticGerm 0 ≃+* AnalyticGerm p` — and `uniqueFactorizationMonoid_analyticGerm`:

  ```text
  for every p in C^n, the ring of analytic germs at p is a unique factorization domain.
  ```

  The instance proved in the twenty-first pass lives at the origin only, whereas a chartwise Siegel
  argument has its centres at the points of a cover of a fundamental parallelotope, none of which
  can be assumed to be the origin.  Transporting the prime factorization along the translation
  isomorphism removes that restriction, and with it the reduced-fraction theory of
  `GermReducedFraction` — `exists_reduced_fraction`, `associated_den_of_reduced`,
  `associated_num_of_reduced` are all stated for an arbitrary GCD domain, so they now apply at every
  centre, and `GermRatioBound.exists_ratio_bound_of_associated` is likewise stated at an arbitrary
  point.
  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (thirty-first pass) — orbifold family: the fixed branch is open only at jet order at
  least two.  `HTGeometry/QuadraticOrbifoldTail.lean` gained `quadOne_fixed_of_order_one` and
  `quadTwo_fixed_of_order_one`: a `Phi_R`-fixed element of jet order at most one is constant, for
  both quadratic maps.  Pass 5 of
  `rational-coarse-graining-orbifold-tail-classification.md` records the sharpening and, more
  usefully, the *exact* remaining equation: at order two the normalizing shift `t = a·y_1^2` exists
  exactly when `a(R)·(R')^2 = R'·a − R''` has a rational solution, which for `z^2+1` reads
  `4 z^2 a(z^2+1) = 2 z a(z) − 2`.  A solution regular at `0` and `1` is immediately impossible
  (the left side vanishes at `0`, the right side is `−2`), so what remains is pole bookkeeping —
  for which `RationalOrder.lean` and the transport law `ord_0(a∘R) = 2·ord_1(a)` are the tools
  already in the tree.  Closure count unchanged: 31 cards remain in the folder.

- 2026-08-16 (thirty-second pass) — orbifold family: the signed order is a valuation.  New
  unconditional axiom-clean umbrella-wired module `HTGeometry/RationalOrderValuation.lean`:
  `min_le_rootMultiplicity_add` (a power of `X − c` dividing two polynomials divides their sum, so
  the multiplicity of a sum is at least the minimum), `eq_num_div_denom`,
  `algebraMap_ne_zero_of_ne_zero`, and `min_le_ratOrder_add`:

  ```text
  min (ord_c f) (ord_c g) ≤ ord_c (f + g).
  ```

  Multiplicativity of `ratOrder` sufficed for the transport of an invariance relation, which is
  purely multiplicative; the affine-connection equation `a(R)·(R')² = R'·a − R''` has an *additive*
  term, so the valuation inequality is exactly what its pole bookkeeping needs.  The proof passes to
  the common denominator `f.denom · g.denom`, where the numerator of the sum is
  `f.num·g.denom + g.num·f.denom` and the polynomial statement applies.
  Closure count unchanged: 31 cards remain in the folder.

## Pass 33 — the rational affine connection, and the level-two normalizing shift

Seven new `HTGeometry` modules, all unconditional, axiom-clean on
`[propext, Classical.choice, Quot.sound]`, all wired into the umbrella, all lint-clean.

| Module | Content |
|---|---|
| `RationalOrderValuation.lean` | `min_le_rootMultiplicity_add`, `min_le_ratOrder_add` — the order of a sum is at least the minimum of the orders |
| `RationalAffineConnection.lean` | `IsAffineConnection R hR a` (`a(R)·(R')² = R'·a − R''`) over any characteristic-zero field; `ratOrder_affineSide`; `affine_pole_forward` / `affine_pole_backward`; `no_affine_connection_regular_at_critical`; `no_pole_of_forward_orbit` / `no_pole_of_backward_orbit`; `derivative_derivative_eq_zero_of_isAffineConnection_zero` |
| `QuadOneNoAffineConnection.lean` | `quadOne_no_affine_connection : ∀ a, ¬ IsAffineConnection (z²+1) _ a` |
| `QuadTwoNoAffineConnection.lean` | `quadTwo_no_affine_connection : ∀ a, ¬ IsAffineConnection ((z−1)²) _ a` |
| `JetAffineConnectionLevelTwo.lean` | `jetDerivation_of_order_zero`, `substitutionShift_two`, `substitutionDeriv_ratFuncDeriv`, `exists_ratFuncDeriv_affine_connection_of_hasNormalizingShift_two`, `exists_isAffineConnection_of_hasNormalizingShift_two` |
| `QuadraticNoNormalizingShift.lean` | `quadOne/quadTwo_not_hasNormalizingShift_two`; `quadOne/quadTwo_lowerOrder_of_substitutionEigen_two` |

The mathematics is on the card
`2-fully-proven/new_scientific_knowledge/other/rational-coarse-graining-orbifold-tail-classification.md`,
passes 6 and 7.  In one line: the critical obstruction (ramification `m + 1` against curvature
vanishing `m − 1`) puts a pole of any affine connection at a critical point or its image; the pole
then travels along critical-free orbits in both directions, and both quadratic maps have an infinite
such orbit through one of the two points; so no affine connection exists, and by the level-two
slicing no normalizing shift exists at jet level two either.

**Card state.**  `rational-coarse-graining-orbifold-tail-classification` stays at stage 2.  Its
general statement is gated on the general exceptionality criterion (no invariant differential ⟹ no
affine connection for an arbitrary map), which needs the finiteness of completely invariant sets;
the two quadratic instances are now closed through jet order two.  The remaining descent for those
two maps (jet order ≥ 3) and its two general inputs are recorded at the end of pass 7 of the card.

## Pass 34 — the Siegel assembly for locally holomorphic charts

The chartwise Siegel machine of passes 23–29 assumed its chart numerators and denominators were
*entire*.  That is the wrong hypothesis for the card it was built for: a local presentation of a
meromorphic function is holomorphic on a polydisc around its centre and nowhere else.  The machine
now runs under the correct hypothesis.

Three new modules and three generalizations, all unconditional, axiom-clean on
`[propext, Classical.choice, Quot.sound]`, all wired.

| Module | Content |
|---|---|
| `PolydiscCoeffVanishing.lean` (generalized) | `norm_le_of_polydiscCoeff_vanish_of_hasSum` — the multi-index Schwarz estimate with the polydisc expansion taken as a hypothesis; the old global form is now a three-line corollary |
| `PolydiscLocalSchwarz.lean` (new) | `polydiscSeries_hasSum_of_differentiableOn`, `norm_le_of_polydiscCoeff_vanish_of_differentiableOn` — the expansion and the estimate for a function holomorphic on a polydisc strictly larger than the contour |
| `SiegelGainVanishing.lean` (generalized) | `eqOn_zero_of_family_siegel_gain` now needs continuity only of the local representatives on the small closed polydiscs |
| `SiegelLocalCharts.lean` (new) | `polydiscCoeff_add_of_torusContinuous`, `differentiableOn_finsetSum/Prod`, `differentiableOn_siegelHomCombination`, `siegelHomCoeffMapLocal`, `exists_ne_zero_chart_siegel_gain_local`, `exists_ne_zero_chart_vanishing_local`, `exists_ne_zero_chart_vanishing_of_transition_local`, `exists_ne_zero_poly_eval_eq_zero_local` |
| `PolydiscAnalytic.lean` | two stale `omit [CompleteSpace E]` warnings cleared |

The local expansion is the corpus's own local Cauchy formula
(`polydiscCauchyFormula_of_differentiableOn`, on `polydiscSet`) fed into the expansion criterion
`polydiscSeries_hasSum_of_cauchy`, which was already stated with local hypotheses.  Everything
below the estimate — the closing mechanism and the chart comparison — was already local or purely
metric.

The capstone now reads: for chart data holomorphic on polydiscs of radius `R₁ > R` around finitely
many centres, a counting inequality `card ι · N^n < (m+1)^(n+1)` and a transition constant beating
the Schwarz factor produce a nonzero `P ∈ ℂ[X₀,…,X_n]` annihilating the chart quotients at every
point of every small polydisc where the denominators of that chart do not vanish.

**What the torus instantiation still needs.**  The corpus's meromorphic field
`Bottcher.meroFieldGen (Set.univ)` is the fraction field of the ring of *entire* functions, so a
global presentation `f = A/B` is available for free — the Poincaré problem does not arise.  What a
single global presentation does *not* give is the transition bound: for a torus point `w` and a
period `p` the factor is `∏_k (B_k w / B_k (w − p))^m`, and `B_k` is not periodic, so the ratio
blows up along the zero divisor.  The bound needs *reduced* local presentations at the centres,
where `GermReducedFraction`/`GermRatioBound` apply — and, to compare them at a point of the
overlap rather than at the centre, the propagation of coprimality of germs to nearby points.  That
propagation (the common zero set of two coprime germs has codimension at least two) is the one
piece of local analytic geometry the instantiation is missing; the whole analytic machine above it
is now unconditional and correctly hypothesized.

## Pass 35 — one transport theory, and the first level of the jet descent

Five new modules and one de-duplication, all unconditional, axiom-clean, umbrella-wired, lint-clean.

| Module | Content |
|---|---|
| `RationalAffineTransport.lean` | `IsAffineTransport R hR k b c a` (`a(R)·(R')^k = b·a + c`), `ratOrder_affineTransport_lhs`, `affineTransport_pole_forward/backward`, `no_pole_of_forward/backward_orbit_affineTransport`, `ratOrder_le_of_critical`; and the affine connection as the case `k = 2, b = R', c = −R''` |
| `QuadOneAffineTransport.lean` | `quadOne_affineTransport_regular_at_critical_pair`, `quadOne_no_affineTransport_of_polar_at_critical` |
| `QuadTwoAffineTransport.lean` | the same two for `(z − 1)²` |
| `JetShiftAffinePresentation.lean` | `pd_jetDerivation_apply` (the commutator `[∂_{m+1}, δ] = ∂_m` applied), `pd_top_substitutionShift`, `exists_affine_substitutionShift`: `σ_{N+3} = A·y_{N+2} + B` with `A, B` of order below `N + 2` |
| `JetNormalizingShiftDescent.lean` | `hasNormalizingShift_pred_or_polynomial`: a normalizing shift at jet level `N + 3` either descends to level `N + 2` or is a *polynomial* in `y_{N+2}` solving `Φ̃(u) = R'·u − (A·X + B)` |

**Why one transport theory.**  Every equation the orbifold descent produces has the shape
`a(R)·(R')^k = b·a + c`: an invariant `k`-differential is `c = 0` with `b` constant, the rational
affine connection is `k = 2, b = R', c = −R''`, and each coefficient equation of a normalizing shift
is `b = 1` with an explicit rational `c`.  Away from the critical set, at points where `b` is a unit
and `c` is regular, the equation says the order of `a` at `p` and at `R(p)` have the same sign, so a
pole travels both ways; at a critical point it bounds the order of the left side by that of `c`.  The
four transport lemmas previously living in `RationalAffineConnection.lean` were deleted and are now
corollaries of the general ones, so there is exactly one copy.

**The two quadratic packagings** say: for an affine transport of `z² + 1` (resp. `(z − 1)²`) whose
coefficient is a unit and whose inhomogeneous term is regular away from the critical point, the
solution is regular at the critical point and at the critical value — the pole would run along the
infinite forward orbit `1, 2, 5, 26, …` (resp. along the backward orbit through `2`, the critical
orbit being the two-cycle `1 ↦ 0 ↦ 1`).  If moreover `c` is polar at the critical point and `k ≥ 0`,
no nonzero solution exists, because the substitution ramifies to order two there.

**The descent.**  The shift term is affine in the coordinate below the top — proved from the
commutator of a coordinate partial with the ambient derivation, not from a Faà di Bruno expansion —
so slicing the shift as a coprime fraction in `y_{N+2}` gives a polynomial identity over the prefix
field.  The denominator divides its twisted image and has the same degree, hence is a scalar
eigenvector; positive degree gives the affine cocycle of its two top coefficients, i.e. a shift one
level down.

**What is left of the descent**: the coefficient analysis of the polynomial branch
`Φ̃(u) = R'·u − (A·X + B)`, where `deg u = 0` forces `A = 0` (impossible, `A = M·R''·y₁`),
`deg u ≥ 3` reproduces the affine cocycle at the two top coefficients and descends, and
`deg u ∈ {1, 2}` need the quadratic packagings above applied to the resulting rational equations.

## Pass 36 — two more branches of the jet descent

`TwistedScalingDescent.lean` (generalized) and `JetShiftPolynomialBranch.lean` (new), both
unconditional, axiom-clean, umbrella-wired.

- `twistComp_affine_cocycle_of_coeff` — the affine cocycle needs only the *two top coefficients* of
  the relation, so it applies to a relation that is a scalar multiple of the polynomial up to
  lower-degree terms.  The previous `twistComp_affine_cocycle` is now its two-line corollary.
- `exists_cocycle_of_shift_polynomial` — for `Φ̃(u) = ρ·u − S` with `deg S ≤ 1` and `deg u ≥ 3`, the
  ratio of the two top coefficients of `u`, divided by the degree, solves `Φ(s) = ρ·s − L`.
- `coeff_one_eq_zero_of_shift_polynomial_deg_zero` — in degree zero the same relation forces the
  linear part of `S` to vanish.
- `hasNormalizingShift_of_polynomial_branch` — hence a polynomial branch of degree at least three at
  jet level `N + 3` produces a normalizing shift at level `N + 2`.
- `top_eq_zero_of_polynomial_branch_deg_zero` — and a polynomial branch of degree zero forces
  `∂_{N+2}σ_{N+3} = 0`.

**State of the level-`M` descent for the two quadratic maps.**  A normalizing shift at jet level
`N + 3` splits into: denominator of positive degree (descends, pass 35); denominator constant with
numerator of degree `0` (forces `A = ∂_{N+2}σ_{N+3} = 0`), degree `≥ 3` (descends), or degree `1` or
`2` (open).  Closing the two open degrees, together with `A ≠ 0`, would give
`¬ HasNormalizingShift` at every level `≥ 2` for `z² + 1` and `(z − 1)²`, hence `Tail(R) = C`, hence
the promotion of `floquet-orbifold-tail-emergence` and `orbifold-tail-holographic-reconstruction`.
The two open degrees reduce, by the coefficient analysis, to rational equations of the form
`a(R)·(R')^k = a + c` with `c` polar at the critical point — exactly the shape
`quadOne_no_affineTransport_of_polar_at_critical` and its `quadTwo` companion kill.  What is missing
between them is the identification `A = M·R''·y₁`, an induction on `M` from `∂₁σ₂ = 2R''y₁` using the
same commutator `[∂_{m+1}, δ] = ∂_m`.

## Pass 37 — shifts are fixed elements, and the tail question becomes a single family

Three new modules, all unconditional, axiom-clean, umbrella-wired, lint-clean.

| Module | Content |
|---|---|
| `JetShiftTopCoefficient.lean` | `jet_ne_zero`; `pd_top_substitutionShift_eq` : `∂_{M−1}σ_M = M·R''(y₀)·y₁`, by induction from `∂₁σ₂ = 2R''y₁`; `pd_top_substitutionShift_ne_zero`; `coe_eq_pd_top_of_affine`; and `quadOne/quadTwo_pd_substitutionDeriv_ne_zero` |
| `QuadraticShiftDescentBranches.lean` | `hasNormalizingShift_pred_or_low_degree` — for a map with `R'' ≠ 0`, a normalizing shift at jet level `N + 3` either descends to level `N + 2` or is a polynomial of degree **one or two** in `y_{N+2}`; and its two quadratic instances |
| `JetFixedFieldShift.lean` | `hasNormalizingShift_iff_exists_fixed` — at level `M ≥ 2` a normalizing shift is *the same thing as* a substitution-fixed element of jet order exactly `M`; `forall_fixed_isConst_iff` |
| `QuadraticTailShiftEquivalence.lean` | `quadOne/quadTwo_forall_fixed_isConst_iff`, and **`quadOne/quadTwo_fixed_of_order_two`** — no nonconstant fixed element of jet order at most two, for either map |

**The structural point.**  A shift `t` at level `M` makes `y_M + t` scale by `R'`; so does `y₁`; so
`(y_M + t)/y₁` is *fixed*, with `∂_M` equal to `1/y₁`, hence of order exactly `M`.  Conversely a
fixed element of order exactly `M` is an eigen-relation of weight zero and eigenvalue one whose
order does not drop, so the normalization dichotomy hands back a shift.  In the language of
`Ψ(V) = R'·V − Φ(V)`: `Ψ(−y_M) = σ_M`, and `ker Ψ = y₁·Fix`, so a shift is a solution of
`Ψ(t) = σ_M` of order below `M` — which exists exactly when `Fix` is nontrivial.

**Consequence for the two cards.**  For `z² + 1` and `(z − 1)²` the whole orbifold tail is trivial
*if and only if* no jet level of order at least two carries a normalizing shift; level two is
proved, so `Tail(R) = ℂ` now holds through jet order two unconditionally
(`quadOne/quadTwo_fixed_of_order_two`), and the descent of this pass reduces every higher level to
the polynomial branches of degree one and two.

**Why those two degrees are hard.**  Degree one produces `Ψ(u₁·y₁) = M·σ₂`, hence
`u₁ + M·y₂/y₁ ∈ Fix`; at level three this is an order-two element, so `Fix ∩ {order ≤ 2} = ℂ`
forces `u₁ = γ − 3y₂/y₁`, whose order exceeds the order the slice allows — a contradiction.  At
level `M ≥ 4` the same element is admissible, and the degree-zero coefficient then produces an
inhomogeneous term outside the span of the `σ_j`, so the class of equations grows with the level.
Closing them uniformly needs the weighted torus action `y_j ↦ λ^j y_j` (which commutes with the
substitution because every Faà di Bruno term of `δ^j(R(y₀))` is isobaric of weight `j`) to normalize
the shift to be isobaric of weight `M` — the normalization itself follows from
`ker Ψ = y₁·Fix` together with `Fix ∩ {order < M} = ℂ`, and is the next thing to build.

## Pass 38 — the weighted torus action, and the isobaric normalization of a shift

Two new modules, unconditional, axiom-clean, umbrella-wired, lint-clean.

`HTGeometry/JetWeightAction.lean` builds the action that grades the free jet field.

```text
weightPolyDeriv, jetDerivation_algebraMap        the ambient derivation on the polynomial ring
weightScaleAlgHom, weightScaleAlgEquiv           y_j ↦ λ^j·y_j on MvPolynomial (Unit × ℕ) C
weightScale                                      its extension to the fraction field
weightScale_jet                                  w_λ(y_p) = λ^{p.2}·y_p
weightScale_jetDerivation                        w_λ(δ v) = λ · δ(w_λ v)
algHom_ext_jet                                   algebra endomorphisms agreeing on the jets are equal
weightScale_substitutionValue / _substitutionDeriv     R(y₀) and R'(y₀) are invariant
weightScale_substitutionJet                      w_λ(δ^l(R(y₀))) = λ^l · δ^l(R(y₀))
weightScale_substitutionShift                    w_λ(σ_M) = λ^M · σ_M
weightScale_jetSubstitution                      w_λ ∘ Φ = Φ ∘ w_λ
weightScale_mem_jetPrefixField                   the action preserves every prefix field
```

The derivation identity is proved on the polynomial ring by the Leibniz rule on a monomial and
transported to the fraction field by the quotient rule; the commutation with the substitution then
follows from `algHom_ext_jet` and the isobarity of the substituted jets.

`HTGeometry/JetShiftWeightNormalization.lean` applies it to a normalizing shift.

```text
jetSubstitution_weightScale_shift   Φ(w_λ t) = R'·w_λ t − λ^M·σ_M
jetSubstitution_weightScale_sub     Φ(H) = R'·H   for  H = w_λ t − λ^M·t
exists_const_weightScale_shift_sub  fixed elements of order below M constant
                                      ⇒  w_λ(t) = λ^M·t + γ(λ)·y₁
```

The point is that the shift equation is isobaric — the derivative factor has weight zero and `σ_M`
has weight `M` — so `w_λ(t)` and `λ^M·t` solve the same equation and their difference solves the
homogeneous one, i.e. `H/y₁` is fixed of order below `M`.

**What this buys.**  In the slice of a shift at level `M = N + 3` in the top coordinate `y_{N+2}`,
the normalization forces every coefficient to be isobaric of a prescribed weight — the coefficient
of `y_{N+2}^d` has weight `M − d(M−1)`.  The degree-two branch then dies for every `M ≥ 3`: its
leading coefficient must be `e/y₁` with `e` constant (from the fixed-element rigidity), of weight
`−1`, while the normalization prescribes weight `2 − M`, and `−1 = 2 − M` only at `M = 3`, where the
transport killer `quadOne_no_affineTransport_of_polar_at_critical` closes it separately.  The
degree-one branch is *not* killed by weight: it prescribes weight one for `u₁`, and the forced value
`u₁ = −M·y₂/y₁` has exactly that weight.  That branch remains the single open case.

## Pass 39 — Bezout with a denominator, the algebraic core of germ-coprimality propagation

`HTGeometry/PolynomialBezoutDenominator.lean` (new, unconditional, axiom-clean, umbrella-wired):

```text
exists_bezout_of_isCoprime_map :
  P, Q ∈ D[X] coprime over Frac D  ⇒  ∃ U V ∈ D[X], r ∈ D, r ≠ 0,  U·P + V·Q = C r
dvd_C_of_dvd_of_dvd :
  every common divisor of P and Q divides that constant
```

Clearing the denominators of a Bezout identity over the fraction field, through
`IsLocalization.integerNormalization_spec`.

**Why this, and what it is a step towards.**  The torus card needs the transition bound
`|B_i,k(w)| ≤ C·|B_j,k(w − p)|`, and that follows from `B_j,k(·−p) ∣ B_i,k` as germs at every point
of the overlap, which in turn needs the numerator and denominator of a *reduced* local presentation
to stay coprime at nearby points — the statement that the common zero set of two coprime germs has
codimension at least two.  After Weierstrass preparation the two germs become distinguished
polynomials over the germ ring in one variable fewer, which is a unique factorization domain
(`GermFactorial`, `GermTranslationFactorial`, both owned), and the lemma above then produces the
constant `r` whose non-vanishing locus is where coprimality demonstrably persists.  What is still
missing between "off the hypersurface `r = 0`" and "everywhere" is the dimension count, i.e. local
analytic geometry that mathlib does not have.

### Reassessment of the orbifold degree-one branch

The remaining branch of the jet descent was analysed once more with the weighted action in hand and
does **not** close by these means.  Writing `t = u₁·y_{M−1} + u₀`:

* the fixed-element rigidity forces `u₁ = γ − M·y₂/y₁`, and the isobaric normalization forces
  `γ = 0`, so `u₁ = −M·y₂/y₁` exactly;
* the remaining equation is `Ψ(u₀) = B + Φ(u₁)·σ_{M−1}` with `ord u₀ ≤ M − 2`, and *any* solution of
  order `M − 1` reduces to one of order `M − 2` with a modified right-hand side, because the
  `y_{M−1}`-coefficient of `Ψ(c·y_{M−1} + w)` is `R'(c − Φ(c))`, which vanishes only for `c` fixed,
  hence constant.  So no order contradiction is available and the class of right-hand sides grows
  with each step.

The obstruction is not bookkeeping: the classical proof that `z² + 1` has trivial orbifold tail goes
through the absence of an invariant line field on its Julia set (Thurston rigidity), which is what
Casale's theorem packages.  An elementary jet-level proof would be new mathematics, and the passes
33–38 machinery is the honest current frontier: everything through jet order two is closed
unconditionally, every level reduces to the single degree-one branch, and the weighted action pins
that branch to one explicit shape.

## Pass 40 — the weight-zero normal form: the descent becomes triangular

The `y`-coordinate descent does not terminate — recorded as a negative result in pass 39.  Changing
to the invariants of the weighted torus action removes the obstruction entirely.

`HTGeometry/JetWeightZeroCoordinates.lean` (new, unconditional, axiom-clean, umbrella-wired):

```text
jetRatio j              z_j = y_j / y₁^j                       (weight zero)
substitutionShiftRatio  s_j = σ_j / y₁^j
jetSubstitution_jetRatio        R'^j · Φ(z_j) = R' · z_j + s_j
weightScale_jetRatio, weightScale_substitutionShiftRatio       both are weight-zero
substitutionShiftRatio_two      s₂ = ∂₀R'                      (= R''(y₀))
jetRatio_one, substitutionShiftRatio_one                       z₁ = 1, s₁ = 0
```

`QuadOne/QuadTwoAffineTransport.lean` were generalized: the critical-point killer now needs only
`0 ≤ ord(b)` at the critical point rather than `ord(b) = 0`, because the coefficient that arises at
the base of the descent is `b = R'`, which vanishes there.

**The mathematics** is written up as pass 8 of
`rational-coarse-graining-orbifold-tail-classification.md`.  In one line: `σ_j` is isobaric of
weight `j` and polynomial in `y₁,…,y_{j−1}`, so `s_j = σ_j/y₁^j` is a polynomial in `z₂,…,z_{j−1}`
over `C(y₀)`, the substitution acts on the tower `C(y₀) ⊂ C(y₀,z₂) ⊂ C(y₀,z₂,z₃) ⊂ ⋯` by a
*triangular affine* map with **scalar** linear coefficient `R'^{1−j}`, and a normalizing shift at
level `M`, being isobaric of weight `M`, becomes `R'^M·Φ(τ) = R'·τ − s_M` with
`τ ∈ C(y₀,z₂,…,z_{M−1})`.  Slicing in the top ratio then reduces the number of ratios by one in
every branch, so the descent terminates at `C(y₀) = RatFunc ℂ`, where the two non-existence theorems
of passes 4 and 6 (no invariant `k`-differential; no rational affine connection) and the general
affine-transport killer of pass 35 apply.

At `M = 2` the equation *is* the affine connection.  At `M = 3` the five-way split closes
completely: the degree-one branch dies because its forced leading coefficient `−3·z₂` does not lie
in `C(y₀)`, and the degree-two branch ends at the `RatFunc` equation `8z³·v(z²+1) = 2z·v(z) + 3/z`,
whose inhomogeneous term is polar at the critical point.  So `z² + 1` admits no normalizing shift at
jet level three, and every fixed element of jet order at most three is constant.

**Remaining**: the bookkeeping of the terminal inhomogeneous term along the degree-one chain,
uniformly in `M`.  It is now a finite computation in explicit universal polynomials — the `s_j` are
polynomials in `R''(y₀), R'''(y₀), …` and `z₂, z₃, …` — instead of the open-ended recursion the
`y`-coordinates produced.

## Pass 41 — the base-case killer of the weight-zero descent

The descent of pass 40 terminates at `C(y₀)` with an affine transport equation whose coefficient is
the *derivative* `R'` — which vanishes at the critical point — and whose inhomogeneous term need not
be polar there.  The previous killer required a pole; the general obstruction only needs the order
of the inhomogeneous term at the critical point to be below both the order of the coefficient and
the exponent.

`QuadOne/QuadTwoAffineTransport.lean` (generalized, unconditional, axiom-clean):

```text
quadOne_no_affineTransport_of_critical_order :
  b a unit away from 0, c regular away from 0,
  ord_0(c) < ord_0(b),  ord_0(c) < k        ⇒  no nonzero solution
quadOne_no_affineTransport_of_polar_at_critical    -- now a corollary
quadOne_no_affineTransport_of_const :
  a(R)·(R')^k = R'·a + γ,  γ ≠ 0 constant,  k ≥ 1  ⇒  no nonzero solution
```

and the two `quadTwo` companions.  The mechanism is unchanged — the substitution ramifies to order
two at the critical point and `R'` vanishes there to order one, so the left side has order at least
`2·ord₁(a) + k ≥ k` while the right side has the order of `c` — but the bookkeeping is now stated at
the sharpness the descent needs.

**Why the constant case is the one that matters.**  Running the weight-zero descent at level
`M ≥ 4`: the only surviving slice degree is one (degree zero forces `M·R'' = 0`; degree `m ≥ 2`
forces `M − 1 = m(M − 2)`, which has no integer solution for `M ≥ 4`; degree `≥ 3` reproduces the
level-`(M−1)` shift).  Its leading coefficient is the unique solution `v₁ = −M·z₂` of
`R'^2·Φ(v₁) = R'·v₁ − M·R''`, and the constant coefficient then satisfies a datum whose own
`z_{M−2}`-coefficient is

```text
c⁽¹⁾₁ = M(M−1)·[ −R''·z₂/2 + R'''/2 − R''²/R' ] ,
```

nonzero for `z² + 1`.  Slicing once more, its `z₂`-coefficient satisfies

```text
α(R)·(R')² = R'·α + M(M−1) ,
```

an affine transport with a **nonzero constant** inhomogeneous term and exponent two — exactly
`quadOne_no_affineTransport_of_const`, hence impossible, for every `M`.  (If `α = 0` the equation
reads `M(M−1) = 0`, also impossible.)

**Remaining**: discharging, uniformly in `M`, the reduction of the intermediate slice coefficients
to their `z₂`-affine parts, i.e. the finitely many branch cases between the level-`M` datum and this
terminal equation.  Every branch is one of the five listed in pass 8 of the orbifold card, and every
terminal equation is now killed.

## Pass 42 — jet level three closed, and the branch above it

**Level three is a theorem.**  `QuadraticLevelThree.lean`:

```text
quadOne_not_hasNormalizingShift_three : ¬ HasNormalizingShift (z² + 1) _ (1 ≤ 3)
quadTwo_not_hasNormalizingShift_three : ¬ HasNormalizingShift ((z − 1)²) _ (1 ≤ 3)
```

both unconditional and axiom-clean.  So for either map every fixed element of the substitution
endomorphism of the free jet field of jet order at most three is constant.

The route, all new Lean:

1. `JetOrderOneSlicing.lean` — **the slicing of an inhomogeneous relation of order one.**  An
   element `v` with `pd_j v = 0` for `j ≥ 2` satisfying `Φ(v) = R'·v − S(y₁)` with `S` a polynomial
   of degree at most `m` over the rational functions of the free generator produces a rational
   affine transport `a(R)·(R')^m = R'·a − S_m`.  The level-two affine-connection extraction is the
   case `S = R''·y₁²`, `m = 2`; the level-three descent needs `m = 3`.
2. `JetLevelThreeDescent.lean` — `substitutionShift_three : σ₃ = 3·R''·y₁·y₂ + R'''·y₁³`; the three
   coefficient relations of a twisted affine relation of degree at most two; and the two structural
   lemmas of the slice:
   * `eq_zero_of_linear_shift` — `Φ(w)·R' = R'·w − κ·R''·y₁` with `w` of order at most one forces
     `κ = 0` and `w` constant, because `w + κ·y₂/y₁` is then a *fixed* element of order at most two;
   * `exists_const_of_scaling_eigen` — `Φ(w)·R' = w` forces `w·y₁` constant.
   Capstone: `hasNormalizingShift_two_or_affineTransport_three` — a level-three shift either descends
   to level two or produces a rational affine transport of exponent three with inhomogeneous term
   the Schwarzian-type combination `R''' − (3/2)·(R'')²/R'`.
3. For both quadratics that combination is `−3/(z − crit)`, a simple pole at the critical point,
   while the coefficient `R'` vanishes there to order one — exactly the hypotheses of
   `quadOne/quadTwo_no_affineTransport_of_critical_order` from pass 41.

**The branch above level three.**  `JetShiftLevelInduction.lean` and `JetLevelBranchAboveThree.lean`
generalize the two structural lemmas and settle the quadratic branch at every level:

```text
jetOverOne j                       := y_j / y₁
exists_const_of_double_shift       : Φ(w)·R'·y₁ = R'·w·y₁ − κ·σ₂ − μ·σ_m
                                       ⇒ w = c − κ·(y₂/y₁) − μ·(y_m/y₁)
mu_eq_zero_of_double_shift         : m ≥ 3 and m above the order of w  ⇒  μ = 0
fixed_isConst_of_order_le          : no shift at levels 2 … K ⇒ every fixed element of order ≤ K
                                       is constant
branch_linear_above_three          : for N ≥ 1 the sliced shift at level N+3 has degree one, and its
                                       coefficient is c₀ − (N+3)·y₂/y₁
```

So **the quadratic branch of the slicing occurs only at level three** (where it is the Schwarzian and
is killed), and above level three only the linear branch survives, with a *completely determined*
linear coefficient.

**What remains.**  At level `M = N + 3 ≥ 4` the constant coefficient `u₀` — of order at most `M − 2`
— satisfies

```text
R'·u₀ − Φ(u₀) = B + Φ(u₁)·σ_{M−1},     u₁ = c₀ − M·y₂/y₁ .
```

Two further reductions are on paper and not yet formal: the weighted torus action forces `c₀ = 0`
(the shift is isobaric of weight `M` up to a multiple of `y₁`, and the coefficient of `y_{M−1}` is
then homogeneous of weight one, which a constant is not); and for `M ≥ 5` the partial
`v := ∂_{M−2}u₀` is homogeneous of weight two, so its own top order cannot exceed two, and it
satisfies

```text
R'·v − Φ(v) = −(M(M−1)/2)·[ R''·y₂ + 2(R'')²·y₁²/R' − R'''·y₁² ] ,
```

an inhomogeneous relation of order two — i.e. exactly a level-three problem with a *different*
inhomogeneous term.  Closing the induction therefore needs the level-three slicing of pass 42 run
with a general order-two inhomogeneous term, plus the separate case `M = 4`.

## Pass 43 — the inductive frame above level three

Four new tools, all unconditional and axiom-clean.

**1. The chain rule for the top partial** (`JetTopPartialSubstitution.lean`).  On an element of jet
order at most `i` the substitution's chain rule collapses to a single term:

```text
pd_aeval_jet              : ∂_i(P(y_i)) = P'(y_i)                (coefficients of order < i)
derivative_twistComp_affine : (Φ̃P ∘ (R'X + s))' = R'·(Φ̃P' ∘ (R'X + s))
pd_top_jetSubstitution    : ∂_i(Φ v) = R'·Φ(∂_i v)               for v of order ≤ i
```

The proof slices `v` as a fraction in `y_i` over the lower field, differentiates the polynomial
presentation, and clears the denominator; the polynomial chain rule supplies the factor `R'`.  This
is the tool that turns every level-`M` relation into a relation one order down.

**2. The weighted action on the coordinate partials** (`JetWeightPartial.lean`).

```text
weightScaleAlgEquiv_pderiv : ∂_j(w_λ a) = λ^j·w_λ(∂_j a)         on the polynomial ring
weightScale_pd             : ∂_j(w_λ v) = λ^j·w_λ(∂_j v)         on the free jet field
```

so the weight of a partial derivative is the weight of the element minus the order of the
coordinate.  This is what makes the isobarity of a normalizing shift readable coefficient by
coefficient.

**3. The linear coefficient above level three is pinned** (`JetLevelBranchIsobaric.lean`).  A
normalizing shift is isobaric of weight its level up to a multiple of `y₁`; one partial derivative in
the top coordinate makes its linear coefficient isobaric of weight *one*, and a constant has weight
zero.  Hence for `N ≥ 1`

```text
branch_linear_coefficient_eq : (u.coeff 1) = −(N+3)·y₂/y₁
```

with **no additive constant** — combined with pass 42 this determines the whole sliced shift above
level three except for its constant term.  Supporting: `hasNormalizingShift_of_branch` (the sliced
polynomial evaluated at the top coordinate *is* a normalizing shift, so the isobarity theorem
applies to it), `pd_aeval_jet_eq_zero`, `weightScale_jetOverOne`.

**4. The shift term two coordinates below the top** (`JetShiftSecondCoefficient.lean`).

```text
pd_second_substitutionShift    : ∂_{N+1}σ_{N+3} = δ(∂_{N+1}σ_{N+2}) + ∂_N σ_{N+2}
pd_second_substitutionShift_eq : 2·∂_{K+1}σ_{K+3} = (K+2)(K+3)·(R''·y₂ + R'''·y₁²)
```

the exact analogue of `pd_top_substitutionShift_eq`, by the same commutator recursion.

**Where the descent now stands.**  With `u₁ = −M·y₂/y₁` and `∂_{M−2}σ_M = (M(M−1)/2)(R''y₂+R'''y₁²)`
in hand, applying `∂_{M−2}` to the shift equation at level `M ≥ 5` gives, for `v := ∂_{M−2}u₀`,

```text
R'·(v − Φ v) = −K·R''·y₂ − 2K·(R'')²·y₁²/R' + K·R'''·y₁²,     K = M(M−1)/2,
```

and after the substitutions `x := v/K`, `y := x − (1/2)·y₂²/y₁²`, `η := y/y₁²` this is exactly

```text
R'^3·Φ(η) = R'·η − D,      D = R''' − (3/2)(R'')²/R' ,
```

the *same* equation the level-three descent produced — but now for `η` of jet order up to `M − 2`
instead of order zero.

**The obstruction that this exposes.**  That equation always has the solution `η = −S/y₁²` with `S`
the Schwarzian `y₃/y₁ − (3/2)(y₂/y₁)²`, because `Φ(S) = S + S_R·y₁²` with
`S_R = R'''/R' − (3/2)(R''/R')²` and `D = R'·S_R`.  So the level-`M` constraint does not contradict —
it *determines*

```text
∂_{M−2}u₀ = K·(−y₃/y₁ + 2·y₂²/y₁² + k) ,   k a constant,
```

(the general solution being the Schwarzian plus a fixed multiple of `y₁^{-2}`).  The descent
therefore reconstructs the candidate invariant rather than killing it, and the kill must come from
the bottom of the reconstruction.

**Consequence for the route.**  The remaining core is now precise: run the level-three slicing of
pass 42 with a *general* inhomogeneous term of jet order at most two.  Concretely, for `u₀` of order
at most two one needs the analogue of `hasNormalizingShift_pred_or_polynomial` for the equation
`Φ(u₀) = R'·u₀ − W` with arbitrary `W` of order at most two, together with the coefficient analysis.
That single generalization closes `M = 4` (where the terminal equation is
`a(R)(R')³ = R'a − (2R''' − 3(R'')²/R')`, a simple pole at the critical point, hence impossible) and
feeds the induction for `M ≥ 5`.

## Pass 44 — the slicing of an arbitrary inhomogeneous relation

The descent above level three needs the level-`M` machinery run with inhomogeneous terms that are no
longer shift terms.  Two generalizations, both unconditional and axiom-clean, supply exactly that.

**Slicing in the top coordinate** (`JetOrderRelationSlicing.lean`):

```text
hasNormalizingShift_or_polynomial_of_relation :
  v of order ≤ N+2,  Φ(v) = R'·v − S(y_{N+2})   (S any polynomial over the prefix field)
  ⇒ a normalizing shift at level N+2, or v = u(y_{N+2}) with
      Φ̃(u) ∘ (R'X + σ_{N+2}) = R'·u − S
```

`hasNormalizingShift_pred_or_polynomial` is the case `S = A·X + B`; the new statement additionally
returns the *link* `v = u(y_{N+2})`, which is what lets the isobarity theorem be applied to the
sliced polynomial.  The proof is unchanged in structure: the denominator of the coprime slice divides
its own twisted image and has the same degree, so it is a scalar eigenvector, and a positive degree
gives the affine cocycle of its two top coefficients as a shift one level down.

**Slicing in the first coordinate, with a scaling factor** (`JetOrderOneSlicing.lean`, generalized):

```text
exists_prefix_affineTransport_of_order_one :
  v of order ≤ 1,  Φ(v)·R'^n = R'·v − S(y₁),  deg S ≤ m
  ⇒ ∃ a of order 0,  Φ(a)·R'^{n+m} = R'·a − S_m
exists_ratFunc_affineTransport_of_order_one : the same, in rational functions
```

The exponent `n` is what the coefficient equations of a *degree-three* slice produce (the leading
coefficient satisfies `Φ(u₃)·R'³ = R'·u₃`, and the next one down carries `R'^2` on the left), so the
old `n = 0` form was too narrow.

With these two the remaining programme is a finite computation: at level `M = 4` the constant term of
the sliced shift satisfies

```text
Φ(u₀) = R'·u₀ − [ −9R''·y₂² + (2R''' − 12(R'')²/R')·y₁²y₂ + (R'''' − 4R''R'''/R')·y₁⁴ ] ,
```

an order-two relation with an explicit inhomogeneous polynomial of degree two in `y₂`; slicing it
either produces a normalizing shift at level two — impossible — or makes `u₀` a polynomial in `y₂`
whose degree is at most three (degree ≥ 4 reproduces the cocycle), and the four remaining degrees are
finite coefficient comparisons ending in rational affine transports with a pole at the critical
point.

## Pass 45 — jet level four closed

`QuadraticLevelFour.lean`, unconditional and axiom-clean:

```text
quadOne_not_hasNormalizingShift_four : ¬ HasNormalizingShift (z² + 1) _ (1 ≤ 4)
quadTwo_not_hasNormalizingShift_four : ¬ HasNormalizingShift ((z − 1)²) _ (1 ≤ 4)
```

so for both maps every fixed element of the substitution endomorphism of jet order at most four is
constant.

The route, all new: `substitutionShift_four` (`σ₄ = 4R''y₁y₃ + 3R''y₂² + 6R'''y₁²y₂ + R''''y₁⁴`), the
coefficient relations of a twisted affine relation of degree at most three, the pure-scaling reading
`Φ(w)·(R')^j = w ⇒ w·y₁^j` constant, and the cocycle with an arbitrary degree bound.  Capstone:

```text
level_four_alternatives : a normalizing shift at level four gives
    a shift at level three, or at level two, or
    (γ ≠ 0)  α(R)·(R')² = R'·α − γ·R'' , or
             α(R)·(R')³ = R'·α − (2R''' − 3(R'')²/R')
```

For both quadratics the first two are already excluded, the third is a scaled affine connection with
a nonzero constant inhomogeneous term, and the fourth has a simple pole at the critical point where
`R'` vanishes.

Two further generalizations were needed and are now corpus-owned: the top-coordinate slicing for an
arbitrary inhomogeneous polynomial (pass 44) and the first-coordinate slicing with a scaling exponent
`Φ(v)·(R')^n = R'·v − S(y₁)`.

## Pass 46 — why the next step is the weight-zero tower

Running the same descent at level `M ≥ 5` shows the obstruction is not where the `y`-coordinates put
it.  Applying `∂_{M−2}` gives, for `v = ∂_{M−2}u₀`,

```text
Φ(v) = v − W' ,      W' explicit of order ≤ 2,
```

whose solutions are the Schwarzian ones: the constraint **determines** `∂_{M−2}u₀` rather than
contradicting.  The same happens in the `z_{M−1}`-slice: the coefficient of the top ratio satisfies
`Φ(α)·(R')² = R'·α − M·R''`, and `α = −z₂` always solves it, so `α` is pinned to `−M·z₂` and no
contradiction arises.  Every finite stage of the `y`-coordinate descent pins a coefficient; the kill
has to come from the bottom of the tower, and in the `y`-coordinates the bottom is never reached
because the coefficients keep having positive jet order.

**In the weight-zero coordinates it is reached.**  With `z_j = y_j/y₁^j` and `s_j = σ_j/y₁^j` the
substitution is triangular affine, `R'^j·Φ(z_j) = R'·z_j + s_j`, and the weight-zero subfield
generated by `y₀, z₂, …, z_k` is a *tower over `C(y₀)`*.  A fixed element of order `M`, normalized to
weight zero, is `G = z_M + g` with

```text
R'^{M−1}·Φ(g) = g − s_M/R' ,      g in the tower of level M−1,
```

and slicing `g` in `z_{M−1}` either descends (the cocycle of the two top coefficients is the same
kind of object one level down) or leaves a polynomial whose top coefficient satisfies
`Φ(c)·(R')² = R'·c − M·R''`.  Iterating the slicing bottoms out in `C(y₀)`, where every terminal
equation is a genuine rational affine transport — exactly the objects already killed for both
quadratics.  Levels two and three of this scheme reproduce the affine-connection and the
Schwarzian obstruction, which is the consistency check.

**Next build**: the weight-zero tower `WFib C k := C(y₀)⟮z₂, …, z_k⟯` with (i) `s_j ∈ WFib C (j−1)`
via the recursion `s_{j+1} = ∇(s_j) + j·s_j·z₂ + R''·z_j` for the weight-zero derivation
`∇ = δ/y₁` (which satisfies `∇(z_j) = z_{j+1} − j·z_j·z₂`, `∇(y₀) = 1`), (ii) `Φ`-stability,
(iii) transcendence of `z_k` over `WFib C (k−1)`, (iv) weight-zero invariance.

## Pass 47 — the weight-zero tower, without a new field

The weight-zero tower does not need a new `IntermediateField`: the ratio `z_k = y_k/y₁^k` generates
the *same* extension of `jetPrefixField C k` as `y_k` does, and the torus fixes it.  So the existing
slicing machinery applies verbatim in the `z_k` coordinate, and torus invariance is what propagates
to the coefficients.

`JetWeightScaleSlicing.lean`:

```text
IsWeightZero v                          := ∀ λ ≠ 0, w_λ v = v
weightScalePrefixHom h k                : the torus restricted to a prefix field
weightScale_aeval                       : w_λ(P(x)) = (w_λ P)(w_λ x)
weightScale_eq_of_mem_prefix_one        : the torus is trivial on order-zero elements
pd_one_eq_zero_of_isWeightZero          : torus-invariant of jet order ≤ 1  ⇒  jet order 0
```

The last is the *bottom of the tower*: slicing a torus-invariant element of order ≤ 1 in `y₁` over
`C(y₀)` makes numerator and denominator scale by `λ^{deg}`, so both are monomials, and coprimality
collapses them to constants.  This is exactly what the `y`-coordinate descent never reached.

`JetWeightZeroSlice.lean`:

```text
transcendental_jetRatio_over_jetPrefixField : z_k is transcendental over jetPrefixField C k
mem_adjoin_jetRatio_of_order                : order ≤ k  ⇒  v ∈ (jetPrefixField C k)⟮z_k⟯
map_weightScalePrefix_eq_of_isWeightZero    : the torus fixes the slice numerator and denominator
isWeightZero_coeff_of_slice                 : hence every slice coefficient is torus-invariant
```

With these, the descent of a weight-zero object in `z_M, z_{M−1}, …, z_2` keeps every coefficient
torus-invariant, and the last step lands in `C(y₀)`, where the affine-connection and affine-transport
obstructions already proved for the two quadratics apply.  What remains is the bookkeeping of the
descent itself: the affine presentation `R'^k·Φ(z_k) = R'·z_k + s_k` as a `twistComp` datum, and the
branch analysis at each level.

## Pass 48 — the weight-zero descent step, unconditional

The descent step now exists in weight-zero form for **every** level, not one level at a time.

`JetWeightZeroShift.lean` — the dictionary between the two forms:

```text
substitutionShiftRatio_mem_jetPrefixField : s_k lies in the prefix field of level k  (k ≥ 2)
jetSubstitution_jetRatio_aeval            : Φ(z_k) = R'^{1−k}·z_k + s_k·R'^{−k}
exists_zshift_of_hasNormalizingShift      : a shift at level M gives R'^M·Φ(w) = R'·w − s_M
hasNormalizingShift_of_zshift             : and conversely
```

`JetWeightZeroDichotomy.lean` — the slicing dichotomy in `z_k`, with **arbitrary** affine data and
coefficient, and with the torus invariance of the slice coefficients as part of the conclusion:

```text
cocycle_or_polynomial_of_zslice :
  w torus-invariant of order ≤ k,  Φ(w) = c·w − S(z_k),  Φ(z_k) = a·z_k + b
  ⇒ (∃ ν ≥ 1, s,  Φ̃(s) = a·s − ν·b)   or   w = u(z_k) with torus-invariant coefficients
```

`JetWeightZeroNormalization.lean` — the shift can be made torus-invariant:

```text
two_pow_sub_one_ne_zero
exists_isWeightZero_zshift : given that fixed elements of order < M are constant, the weight-zero
                             shift can be corrected by a constant multiple of y₁^{1−M} to be
                             torus-invariant, without changing the relation
```

`JetWeightZeroDescent.lean` — the partials of the weight-zero coordinates and the descent step:

```text
pd_jetRatio_self / pd_jetRatio_of_ne         : ∂_j z_j = y₁^{-j},  ∂_i z_j = 0 otherwise
pd_top_substitutionShiftRatio                : ∂_{N+1} s_{N+2} = (N+2)·R''/y₁^{N+1}
weightZeroShiftTail_mem                      : s_M − M·R''·z_{M−1} has order ≤ M − 2
hasNormalizingShift_pred_or_zpolynomial      : a shift at level N+3 either descends to level N+2,
                                               or is a polynomial in z_{N+2} whose coefficients are
                                               torus-invariant
```

**What this buys.**  Every iteration of the step keeps the coefficients torus-invariant, and
`pd_one_eq_zero_of_isWeightZero` (pass 47) turns torus invariance at jet order one into jet order
zero.  So the descent from level `M` now provably terminates in `C(y₀)`, where each surviving
relation is a rational affine transport of the kind already killed for both quadratics.  Levels two,
three and four of this scheme reproduce the affine connection, the Schwarzian, and the level-four
alternatives.

**What is left for the general level.**  Only the bookkeeping of the *inhomogeneous terms* along the
chain: at each step the polynomial branch of degree one leaves a coefficient satisfying
`R'^2·Φ(c) = R'·c − M·R''` — always solved by `c = −M·z₂`, so the coefficient is pinned rather than
contradicted — and a constant term satisfying a relation of the same shape one order down.  Closing
the induction means showing that the inhomogeneous term reaching `C(y₀)` is nonzero and polar at the
critical point.  Every ingredient of that computation is now formal; what remains is the induction
that tracks it.

## Pass 49 — eigen-rigidity, and the degree of the slice at every level

The descent now has an engine that works uniformly in the level.

`JetEigenRigidity.lean`:

```text
two_zpow_eq_one                        : (2 : C)^κ = 1 ⇒ κ = 0
pd_zpow_jet_one                        : ∂_j (y₁^κ) = 0 for j ≠ 1, any integer κ
exponent_eq_zero_of_weightZero_eigen   : g ≠ 0 torus-invariant of order ≤ K with R'^κ·Φ(g) = g
                                           ⇒ κ = 0
```

The proof of the last is three lines of structure: `Φ(g·y₁^κ) = g·y₁^κ`, so the product is a *fixed*
element of the same jet order, hence a constant by the inductive hypothesis; the torus then reads off
`2^κ = 1`, and characteristic zero finishes.  It says the weight-zero eigen-relations are *rigid*:
there is no nonzero solution at any exponent but zero.

**Consequence, uniform in the level.**  At the slicing step the leading coefficient of the polynomial
branch satisfies a pure eigen-relation of exponent `(N + 2) − (N + 1)·d`, so rigidity forces
`(N + 1)·d = N + 2`, which for `N ≥ 1` has no solution with `d ≥ 2`:

```text
natDegree_le_one_of_zbranch : for N ≥ 1 the sliced shift at level N + 3 is linear in z_{N+2}
```

At `N = 0` the equation reads `d = 2`, which is exactly the Schwarzian branch of level three — the
scheme reproduces the known exceptional case and excludes it everywhere above.

So the descent above level three is now: *descend one level, or a linear polynomial in `z_{N+2}`*,
with both alternatives unconditional and the degree bound proved by rigidity rather than by a
level-specific computation.  What remains is the analysis of the two coefficients of that linear
polynomial, which is where the pinned value `−M·z₂` and the terminal rational transports live.

## Pass 50 — the Schwarzian coordinate and the projective obstruction

The bottom of the weight-zero tower is now named and its obstruction is a theorem.

`JetSchwarzian.lean`:

```text
jetNabla                          := δ / y₁ , the weight-zero derivation
jetSubstitution_jetNabla          : R'·Φ(∇v) = ∇(Φ v)
schwarzianJet                     := z₃ − (3/2)·z₂²
ratSchwarzian / ratFuncSchwarzian : S_R = R'''/R' − (3/2)(R''/R')²
substitutionShiftRatio_three      : s₃ = 3·R''·z₂ + R'''
jetSubstitution_schwarzianJet     : R'^2·Φ(𝔖) = 𝔖 + S_R
ratFuncEval_ratFuncSchwarzian     : the two Schwarzians agree at the free generator
```

The substitution law of `𝔖` is a **pure translation** — that is the structural fact behind every
"the constraint pins the coefficient instead of contradicting it" observation of passes 46 and 48.
The jet-level invariants live in a `D`-tower over `𝔖`, and closing the tower means undoing the
translation by `S_R` with a rational function, i.e. solving

```text
a(R)·(R')² = a − S_R ,
```

the classical *projective structure* equation.

`QuadraticProjectiveStructure.lean`:

```text
quadOne_no_projective_structure : ∀ a : RatFunc ℂ, ¬ (a(R)(R')² = a − S_R)
quadTwo_no_projective_structure : the same for (z − 1)²
```

For both maps `S_R = −3/(2(z − crit)²)`, a **double pole exactly at the critical point**, while the
coefficient of the transport is the unit `1`; the critical-order obstruction of pass 41 forbids it.
So the three classical structures — invariant differential (order 1), affine connection (order 2),
projective structure (order 3) — are now all excluded for both quadratics, unconditionally and in
Lean.  Together with the rigidity engine of pass 49 these are exactly the terminal objects the
weight-zero descent produces.

## Pass 51 — the level-uniform descent: one operator, one step, two pinned coefficients

The polynomial-slicing route of passes 45–50 (transcendence, `IntermediateField.adjoin`,
`twistComp` cocycles) is replaced by a single differential operator.

**The descent operator.**  `topDescent K v := y₁^K·∂_K v`.  The top-coordinate chain rule
`∂_K Φ = R'·Φ ∂_K` (valid for jet order at most `K`) turns any relation

`R'^κ·Φ(v) = R'·v − D`   (`v`, `D` of jet order ≤ K)

into the same relation one step down:

`R'^{κ+1−K}·Φ(topDescent_K v) = R'·topDescent_K v − topDescent_K D`,

and iterating gives `R'^{κ+k(1−K)}·Φ(topDescent_K^{[k]} v) = R'·topDescent_K^{[k]} v
− topDescent_K^{[k]} D` (`jetSubstitution_topDescent`, `jetSubstitution_topDescent_iterate`).
`topDescent_K` preserves both jet order ≤ K and torus invariance
(`topDescent_order`, `isWeightZero_topDescent`).  Crucially, `topDescent_K^{[k]} v = 0` is exactly
`∂_K^k v = 0`, so polynomiality in the top coordinate is *produced* by the tower instead of being
imported from a slicing dichotomy.

**The shift recursion.**  Differentiating the affine presentation once gives

`σ_{M+1} = δ(σ_M) + δ(R'(y₀))·y_M`   (`substitutionShift_succ`),

whose weight-zero form is the covariant recursion

`s_{k+1} = ∇s_k + k·z₂·s_k + R''(y₀)·z_k`   (`substitutionShiftRatio_succ`),

with `∇ = y₁^{-1}δ` and `∇z_j = z_{j+1} − j·z_j·z₂` (`jetNabla_jetRatio`).  Its first consequence is
level-uniform: `∂_M σ_{M+1} = (M+1)·δ(R'(y₀))` for every `M ≥ 1`
(`pd_subtop_substitutionShift`), hence

`topDescent_M s_{M+1} = (M+1)·R''(y₀)`,   `topDescent_M^{[2]} s_{M+1} = 0`   (`M ≥ 2`).

**Consequence 1 — the top coefficient, at every level.**  For `N ≥ 3`, a torus-invariant
normalizing shift `w` at level `N+1` (jet order ≤ N, `R'^{N+1}Φ(w) = R'w − s_{N+1}`) satisfies

`topDescent_N^{[2]} w = 0`   and   `topDescent_N w = −(N+1)·z₂`   (`topDescent_of_zshift`).

Proof: at `k = 2` the tower is homogeneous with exponent `2 − N`, and eigen-rigidity forces `N = 2`;
at `k = 1` the exponent is exactly `2` and the affine-coefficient rigidity of pass 49 pins the value.
No level-dependent case analysis at all.

**Consequence 2 — the second coefficient is the Schwarzian, at every level.**  Stripping the pinned
term, `u := w + (N+1)·z₂·z_N` has jet order ≤ N−1 and satisfies the same relation with `s_{N+1}`
replaced by an explicit defect (`zshift_strip`, `zshiftDefect`).  The subsubtop partial of the shift
(`pd_second_substitutionShift_eq`) gives

`topDescent_{N−1}(defect) = ½N(N+1)·(R''·z₂ + R''') − N(N+1)·(R''·z₂ + (R'')²/R')`,

and that inhomogeneous term is solved by `−½N(N+1)·(z₃ − 2z₂²)`.  Eigen-rigidity at exponent two
makes the solution unique, so for every `N ≥ 4`

`topDescent_{N−1}(u) = −½N(N+1)·(z₃ − 2z₂²) = ½N(N+1)·(½z₂² − 𝔖)`   (`topDescent_strip_of_zshift`).

**The Schwarzian is therefore forced into every level**: the second coefficient of a normalizing
shift is a universal rational multiple of the Schwarzian, with the level entering only through the
scalar `½N(N+1) = binom(N+1,2)`.

**The uniform step.**  Both consequences are instances of one lemma (`strip_step`): if `v` is
torus-invariant of jet order ≤ K, satisfies `R'^κΦ(v) = R'v − D`, and is affine in `z_K`, then
`v − P·z_K` (`P := topDescent_K v`) has jet order ≤ K−1 and satisfies

`R'^κ·Φ(v − P z_K) = R'·(v − P z_K) − (D + P·s_K − E·z_K − E·s_K/R')`,   `E := topDescent_K D`,

with the *same* exponent.  Affineness itself is uniform (`topDescent_topDescent_eq_zero`): it holds
whenever `κ ≠ 2K − 1` and `∂_K^2 D = 0`, by eigen-rigidity on the second descent.

**Where the contradiction sits.**  Running `strip_step` from `K = N` downwards with `κ = N+1`, the
coefficient `P_t` extracted at stage `t` has exponent `t + 2`, and

`c_t := −y₁^{N+2}·∂_{t+2}∂_{N−t} w`

is its `z_{t+2}`-coefficient, so `P_t` has jet order exactly `t+2` when `c_t ≠ 0`.  The two computed
values are `c_0 = N+1` and `c_1 = ½N(N+1)`, i.e. `binom(N+1,t+1)` for `t = 0, 1`; the commutation of
partials forces the symmetry `c_t = c_{N−2−t}`.  Stage `t` needs `P_t` to have jet order at most
`K_t − 1 = N−t−1`, i.e. `t + 2 ≤ N − t − 1`.  For odd `N` the chain therefore breaks at
`t = (N−1)/2`, where `topDescent_{K_t}` can only produce jet order ≤ `(N+1)/2` while `P_t` has jet
order `(N+3)/2` — a contradiction.  For even `N` the resonance `κ = 2K_t − 1` occurs exactly at
`t = (N−2)/2`, where the second descent is a fixed element, hence constant, and one quadratic strip
step is needed before the same order crossing applies.

**Remaining for the general level.**  (i) the recursion `P_t`, `D^{(t)}`, `c_t` as a Lean-level
induction on `t`; (ii) `c_t ≠ 0` in the range `2t ≤ N−3`; (iii) the order-crossing contradiction;
(iv) the single quadratic step for even `N`.  Everything else the chain needs — the operator, the
tower, the shift recursion, the strip step, the affineness criterion, the two pinned coefficients —
is now Lean-proved and level-independent.

New modules: `JetTopDescentTower`, `JetUniformLevel`, `JetUniformStrip`, `JetUniformCoefficient`,
`JetStripStep`; `JetSchwarzian` gained `jetNabla_jetRatio`.  All are axiom-clean on
`[propext, Classical.choice, Quot.sound]` and lint-clean.

## Pass 52 — the Euler derivation of the weight grading

The generator of the weighted torus, `Eu(y_j) = j·y_j`, built as `MvPolynomial.mkDerivation`
followed by the fraction-ring extension (`JetEulerDerivation.lean`).  It

* kills every weight-zero coordinate: `Eu(z_j) = 0`;
* commutes with the jet derivation up to `δ`: `⁅Eu, δ⁆ = δ`, hence commutes with `∇`;
* annihilates the whole shift tower: `Eu(s_M) = 0` for `M ≥ 1`, by induction along the covariant
  recursion of pass 51;
* is a finite sum of partials on any element of bounded jet order:
  `Eu(v) = ∑_{j ≤ K} j·y_j·∂_j v` (`jetEuler_sum`, via the free-coordinate chain rule).

The last two together give the Euler relation `y₁·∂_1 v = −∑_{j ≥ 2} j·z_j·(y₁^j·∂_j v)`: the
partial in the *first* coordinate of a weight-zero element is determined by its higher descents.

This is the missing boundary datum for the subdiagonal law.  The shift recursion gives, for
`j ≥ 3`,

`Q(j,r) = ∇Q(j,r−1) + (r−1)·z₂·Q(j,r−1) + Q(j−1,r)`,   `Q(j,r) := topDescent_j(s_{j+r})`,

and at `j = 2` the extra terms produce
`Q(2,r) = ∇Q(2,r−1) + (r−1)z₂Q(2,r−1) + Q(1,r) + (r+1)s_{r+1}`, with `Q(1,r) = y₁·∂_1 s_{r+1}`
supplied by the Euler relation.  Pascal's rule then gives the closed form

`topDescent_{M+1−r}(s_{M+1}) = binom(M+1, r)·T_r`,   `T_1 = R''(y₀)`,  `T_r = ∇T_{r−1} + (r−1)z₂T_{r−1}`,

checked by hand at `r = 1, 2, 3` against `topDescent_M s_{M+1} = (M+1)R''`,
`topDescent_{M−1}s_{M+1} = binom(M+1,2)(R''z₂ + R''')` and `Q(1,r) = (r+1)(T_r − s_{r+1})`.  The
binomial scalars are exactly the `c_t = binom(N+1,t+1)` of pass 51, and with the subdiagonal law the
stage recursion `P_t`, `D^{(t)}` becomes explicit with all level dependence in the binomials — the
remaining step to the order-crossing contradiction.

## Pass 53 — the tower expansion and the subdiagonal law

Two closed formulas that make the whole descent chain explicit.

**The universal tower.**  `T_1 = R''(y₀)`, `T_{r+1} = ∇T_r + r·z₂·T_r` (`shiftTower`).  It is not a
new object: `T_r = ∂_0 s_r + R''(y₀)·z_r` (`shiftTower_eq`), proved by induction from the covariant
shift recursion using `[∂_0, δ] = 0`.

**The tower expansion of the shift** (`substitutionShiftRatio_eq_shiftTower_sum`):

`(M+1)·s_{M+1} = ∑_{i<M} (i+1)·binom(M+1, i+1)·z_{i+1}·T_{M−i}`.

This is the weight-zero Faà di Bruno formula: the level enters only through binomial coefficients,
the differential content sits entirely in the universal tower.  The proof differentiates the
inductive expansion covariantly; the two `z₂` contributions cancel term by term because
`(i+1) + (M−i) = M+1`, the two resulting sums are the two halves of Pascal's rule
`(M+2)[i·binom(M+1,i) + (i+1)·binom(M+1,i+1)] = (M+1)·(i+1)·binom(M+2,i+1)`, and the coordinate term
`R''(y₀)·z_{M+1}` cancels exactly the boundary term of the reindexing.

**The subdiagonal law** (`topDescent_substitutionShiftRatio_choose`): for every `K ≥ 2` and every `m`,

`topDescent_K(s_m) = binom(m, K)·T_{m−K}`,

with no side conditions (`T_0 = 0` and `binom(m,K) = 0` absorb the degenerate ranges).  Strong
induction on `m`: descending the tower expansion in `z_K` gives a diagonal term, a term where the
tower entry is exactly `T_K`, and terms where the descent falls on a lower tower entry; the last are
again descents of a shift at a smaller level because `T_r = ∂_0 s_r + R''z_r` and `∂_0` commutes with
`topDescent_K`, and the subset-of-a-subset identity
`binom(M+1,i+1)·binom(M−i,K) = binom(M+1,K)·binom(M+1−K,i+1)` matches them against the tower
expansion at level `M+1−K`.

**What this unlocks.**  Running `strip_step` from `K = N` with exponent `κ = N+1`, write
`P_t = topDescent_{K_t} v^{(t)}` and `E_t = topDescent_{K_t} D^{(t)}`, `K_t = N−t`.  In the range
where the chain runs, `P_t` and `E_t` have jet order below `K_{t+1}`, so their descents drop out and
the subdiagonal law gives the closed recursion

`E_t = binom(N+1, N−t)·T_{t+1} + ∑_{u<t} binom(N−u, N−t)·T_{t−u}·(P_u − E_u/R')`.

Because `binom(N+1,N−t) = binom(N+1,t+1)` and
`binom(N−u,N−t)·binom(N+1,u+1) = binom(N+1,t+1)·binom(t+1,u+1)` (again subset-of-a-subset), the
whole level dependence factors out:

`E_t = binom(N+1,t+1)·Ê_t`,  `P_t = −binom(N+1,t+1)·P̂_t`,
`Ê_t = T_{t+1} − ∑_{u<t} binom(t+1,u+1)·T_{t−u}·(P̂_u + Ê_u/R')`,

with `P̂_t` the unique solution of `R'^{t+2}·Φ(P̂_t) = R'·P̂_t + Ê_t` — **all independent of the
level `N`**.  Checked against the computed cases: `Ê_0 = R''`, `P̂_0 = z₂`;
`Ê_1 = R''' − R''z₂ − 2(R'')²/R'`, `P̂_1 = z₃ − 2z₂²`.

**The one remaining mathematical unknown.**  The chain breaks at the first `t` with `t+2 > N−t`,
because `topDescent_{N−t}` cannot produce jet order above `N−t` while `P̂_t` has jet order `t+2`.
That needs `γ_t := topDescent_{t+2}(P̂_t) ≠ 0`; `γ_0 = γ_1 = 1`, and `γ_t = 1` is equivalent to
`Ê_t − s_{t+2}` being solvable at jet order at most `t+1`, since
`R'^{t+2}Φ(z_{t+2}) = R'z_{t+2} + s_{t+2}`.  Everything else in the chain — the operator, the tower,
the expansion, the subdiagonal law, the strip step, the affineness criterion, the two pinned
coefficients — is Lean-proved and level-independent.

New modules: `JetEulerDerivation` (the weight generator `Eu(y_j) = j y_j`, `⁅Eu,δ⁆ = δ`,
`Eu(s_M) = 0`, `Eu` as a finite sum of partials), `JetShiftTower`, `JetShiftSubdiagonal`.  All
axiom-clean and lint-clean.

## Pass 54 — the level-free tower is an iterated derivative of `1/y₁`

The sequence `P̂_t` that pass 53 could only characterise implicitly has a closed form:

`V_t := −δ^{t+1}(1/y₁)/y₁^t`   (`invTower`).

Everything about it is now Lean-proved (`JetInverseTower.lean`).

* **It solves the level-free relation.**  `Φ` is a differential endomorphism and `Φ(y₁) = R'y₁`, so
  `Φ(δ^k(1/y₁)) = δ^k(1/(R'·y₁))` and

  `R'^{t+2}·Φ(V_t) = R'·V_t + Ê_t`,  `Ê_t = (R'·δ^{t+1}(1/y₁) − R'^2·δ^{t+1}(1/(y₁R')))/y₁^t`

  (`jetSubstitution_invTower`, `invTowerDefect`).
* **Its leading coefficient is one** — the statement pass 53 left open.  For `f` of jet order at
  most one, `∂_{k+1}(δ^k f) = ∂_1 f` and `δ^kf` has jet order at most `k+1`
  (`pd_deltaIter_of_order_one`); with `f = 1/y₁` this gives
  `∂_{t+2}(δ^{t+1}(1/y₁)) = −1/y₁²`, hence

  `topDescent_{t+2}(V_t) = 1`   (`topDescent_invTower`),

  so `γ_t = 1` for every `t` and the jet order of `V_t` is exactly `t + 2`.
* **It is torus invariant** (`isWeightZero_invTower`), and its defect has jet order at most `t + 1`
  (`pd_invTowerDefect_of_gt`) — the two `∂_{t+2}` contributions cancel exactly, because
  `∂_1(1/(y₁R')) = −R'/(y₁R')²`.
* **The shift tower is the same construction for the derivative factor**:
  `T_r·y₁^r = δ^r(R'(y₀))` (`shiftTower_mul_pow`).
* **The defect recursion is the Leibniz rule.**  With the iterated Leibniz rule
  `δ^n(ab) = ∑ binom(n,i)·δ^i a·δ^{n−i}b` (`deltaIter_leibniz`) applied to
  `1/y₁ = R'·(1/(y₁R'))`, the two extreme terms split off (`deltaIter_inv_split`) and give

  `Ê_t = T_{t+1} − ∑_{j<t} binom(t+1, j+1)·T_{j+1}·(V_{t−1−j} + Ê_{t−1−j}/R')`

  (`invTowerDefect_eq`) — exactly the recursion pass 53 derived from the descent chain, now proved
  as an identity between explicit objects.

So the level-free half of the descent is complete: the sequence exists, is explicit, has jet order
exactly `t + 2` with unit leading coefficient, and satisfies both the substitution relation and the
convolution recursion that the chain produces.

**Remaining for the orbifold cards.**  Assemble the chain: `v^{(t)} := w + ∑_{u<t}
binom(N+1,u+1)·V_u·z_{N−u}`, show by induction that it has jet order at most `N−t` and that
`topDescent_{N−t}(v^{(t)}) = −binom(N+1,t+1)·V_t` — the inductive step is `strip_step` together with
the subdiagonal law of pass 53, the subset-of-a-subset identity, and `invTowerDefect_eq` — and then
read off the contradiction at the first `t` with `t + 2 > N − t`, since `topDescent_{N−t}` cannot
produce jet order above `N−t` while `V_t` has jet order exactly `t + 2`.  One extra quadratic step is
needed when `N` is even, where the resonance `κ = 2K_t − 1` falls at `t = (N−2)/2`.

## Pass 55 — normalizing shifts propagate upwards, so only the even levels matter

A torus-invariant solution of the shift relation at level `m + 1` produces one at level `m + 2`:

`w' = ∇w + m·z₂·w − z₂·z_{m+1}`   (`zshift_succ`, `JetShiftPropagation.lean`).

Proof: apply `∇` to the relation, use `∇(Φ v) = R'·Φ(∇v)` and `∇(R'^{m+1}) = (m+1)R'^m·R''`, then feed
in the coordinate laws for `z₂` and `z_{m+1}` and the covariant recursion
`s_{k+1} = ∇s_k + k·z₂·s_k + R''·z_k`.  Every `R''·w`, `R''·s/R'` and `z₂·s` contribution cancels and
what is left is exactly `s_{m+2}`.  Order and torus invariance are immediate (`∇` preserves both,
raising the order by one).

**Consequence for the closure.**  The set of levels carrying a normalizing shift is upward closed.
The descent chain of pass 53–54 runs cleanly exactly when `N` is odd, where `N + 1` is the level: the
range condition for the chain is `2t < N` and the order crossing needs `2t ≥ N − 2`, and those two
have a common integer solution `t = (N−1)/2` precisely for odd `N`; for even `N` the resonance
`κ = 2K_t − 1` falls inside the gap.  With propagation this no longer matters: a shift at an odd
level propagates to the next even level, so killing the even levels `M ≥ 4` — i.e. the odd `N` — kills
every level, and levels two and three are already dead.

At the crossing the chain produces one extra term, because `V_{T−1}` has jet order exactly
`T + 1 = N − T` there and so contributes `s_{T+2}` to the descended defect.  The uniqueness of
solutions then gives

`topDescent_{T+1}(chain T) = −binom(N+1,T+1)·V_T + binom(N+1,T)·z_{T+2}`,

whose top descent is `binom(N+1,T) − binom(N+1,T+1) ≠ 0` (the two are consecutive binomials of
`2T + 2` straddling the centre), contradicting `topDescent_order`, which forces jet order at most
`T + 1`.

**Remaining.**  The Lean chain induction itself: `chain t := w + ∑_{u<t} binom(N+1,u+1)·V_u·z_{N−u}`
has jet order at most `N − t`, its defect is `s_{N+1} − ∑_{u<t} binom(N+1,u+1)·Δ_u` with
`Δ_u = V_u s_{N−u} + Ê_u z_{N−u} + Ê_u s_{N−u}/R'`, and its top descent is
`−binom(N+1,t+1)·V_t` — the step being `strip_step`, the subdiagonal law, `Nat.choose_mul` and
`invTowerDefect_eq`, all of which are now Lean-proved.

Also banked with pass 55 (`JetChainTerm.lean`): the two laws governing one correction term of the
chain.  Multiplying `R'^{u+2}Φ(V_u) = R'V_u + Ê_u` by `R'^kΦ(z_k) = R'z_k + s_k` gives

`R'^{u+1+k}·Φ(V_u·z_k) = R'·(V_u·z_k) + Δ(u,k)`,
`Δ(u,k) = V_u·s_k + Ê_u·z_k + Ê_u·s_k/R'`   (`jetSubstitution_invTower_mul`),

and in any coordinate `K ≥ 2` above the jet orders of `V_u` and `Ê_u` and different from `k` the
subdiagonal law evaluates its descent:

`topDescent_K(Δ(u,k)) = (V_u + Ê_u/R')·binom(k,K)·T_{k−K}`   (`topDescent_chainDelta`).

These are exactly the two inputs the chain induction needs at each step.

## Pass 56 — CLOSED: the quadratic orbifold tails are trivial, and three cards move to stage 3

```text
GaloisForLFunctions.HTGeometry.quadOne_tail_trivial,  quadTwo_tail_trivial :
  Phi_R(g) = g  ->  g constant,  for every g in the free jet field, every jet order,
  no hypotheses, axioms [propext, Classical.choice, Quot.sound].
```

Promoted to `3-formalized/new_scientific_knowledge/other`:
`rational-coarse-graining-orbifold-tail-classification`, `floquet-orbifold-tail-emergence`,
`orbifold-tail-holographic-reconstruction`.

**The chain** (`JetChainDescent.lean`).  With `chain t = w + ∑_{u<t} binom(N+1,u+1)·V_u·z_{N−u}` and
`chainDefect t = s_{N+1} − ∑_{u<t} binom(N+1,u+1)·Δ(u, N−u)`:

* `chain_relation` — the chain satisfies the shift relation with the same exponent and that defect;
* `topDescent_chainDefect_gen` — the descent of the defect is
  `binom(N+1,t+1)·Ê_t − ∑_{u<t} binom(N+1,u+1)·s_{N−u}·topDescent_{N−t}(V_u)`, by the subdiagonal law
  of pass 53, the subset-of-a-subset identity `binom(N+1,u+1)binom(N−u,N−t) =
  binom(N+1,t+1)binom(t+1,u+1)`, and the defect recursion of pass 54;
* `topDescent_chain` — uniqueness (eigen-rigidity at exponent `t+1`) pins
  `topDescent_{N−t}(chain t) = −binom(N+1,t+1)·V_t`;
* `chain_order` — hence `chain (t+1)` has jet order at most `N − t − 1`, by induction;
* `no_zshift_of_odd` — at `N = 2T+1` the chain reaches `t = T`, where `V_{T−1}` has jet order exactly
  `N − T` and contributes an extra `s_{T+2}`, so
  `topDescent_{T+1}(chain T) = −binom(N+1,T+1)V_T + binom(N+1,T)z_{T+2}`; its top descent is
  `binom(N+1,T) − binom(N+1,T+1)`, nonzero because the two are consecutive binomials of `2T+2`
  straddling the centre, contradicting the jet-order bound `T + 1`.

**Odd levels** are reduced to even ones by `zshift_succ` (pass 55).  The rigidity in the chain is
applied at the jet order of the elements involved, not at `N`, so the propagated chain runs with the
fixed-point hypothesis only at order `M − 1`; its first stripping step comes from the pinned top
coefficient `topDescent_{M−1}(w) = −M·z₂` at the original level.

**Assembly** (`JetTailTrivial.lean`): `no_zshift` (no shift at any level `≥ 4` given the levels
below), `not_hasNormalizingShift_all` (strong induction over the levels), and

```text
fixed_isConst :  no nonconstant fixed element of jet order one, no shift at level two,
                 no shift at level three  ==>  Tail(R) = C.
```

For the two quadratics the three inputs are the absence of an invariant rational differential, of a
rational affine connection and of a rational projective structure — all already Lean-proved.

## Pass 57 — coprimality of analytic germs is an open condition

Card `noncompact-period-quotient-facet-escape-law` named one missing ingredient: the propagation of
coprimality of analytic germs to nearby points.  It is now Lean-proved, unconditionally, in every
dimension, axioms `[propext, Classical.choice, Quot.sound]`, umbrella-wired, lint-clean.

```text
GaloisForLFunctions.HTGeometry.eventually_isRelPrime_germ :
  IsRelPrime (germ_p f) (germ_p g)  ==>  eventually in q near p,  IsRelPrime (germ_q f) (germ_q g).
```

Five new modules:

* `MonicBezoutConstant` — over a UFD, two monic polynomials with no common monic factor of positive
  degree admit `alpha*F + beta*G = C c` with `c != 0`.  Gauss' lemma in the integrally closed form
  (`IsIntegrallyClosed.eq_map_mul_C_of_dvd`, `Monic.dvd_of_fraction_map_dvd_fraction_map`) plus
  `IsLocalization.integerNormalization` to clear denominators.
* `GermZeroProjection` — the zero set of a vanishing regular germ meets every nearby parameter
  fibre, inside any prescribed neighbourhood.  Proof: the slice root count is locally constant in
  the parameters, at least one at the base parameter, and the roots stay inside the circle.
* `GermSliceNonvanishing` — regularity spreads over the preparation polydisc: the Weierstrass factor
  is monic, hence nonzero, so no slice vanishes identically anywhere on the disc.
* `GermCoprimeOpen` — the assembly, plus the invariance of relative primality of germs under an
  analytic change of coordinates.  Contradiction mechanism: a common non-unit divisor at a nearby
  point is regular in the same coordinate, its zeros give common zeros of `f` and `g` over every
  nearby parameter, so the Bézout constant vanishes on an open set of parameters and hence
  identically.
* `GermReducedTransition` — the consequence the Siegel count consumes: two presentations reduced at
  their own centres have boundedly comparable denominators near every point of the overlap.

No dimension theory of analytic sets is used anywhere; the Bézout constant replaces it.

## Pass 58 — Siegel's theorem for compact complex tori is formalized

```text
GaloisForLFunctions.HTGeometry.exists_ne_zero_poly_of_periodic_meromorphic :
  P a subgroup of C^(n+1) with compact quotient,
  A_k, B_k entire (k in Fin (n+2)),  B_k not identically zero,
  A_k/B_k invariant under P  (cross-multiplied: A_k(z+p) B_k(z) = A_k(z) B_k(z+p))
    ==>  there is a nonzero Q in C[X_0,...,X_(n+1)] with
         Q(A_0/B_0, ..., A_(n+1)/B_(n+1)) = 0  wherever the denominators do not vanish.
```

Equivalently `trdeg_C M(X) <= dim_C X` for a compact complex torus `X`, in the corpus's meromorphic
field (fractions of entire functions).  Unconditional, axioms `[propext, Classical.choice,
Quot.sound]`, umbrella-wired, lint-clean.  The cleared form
`exists_ne_zero_siegelHomCombination_of_periodic_meromorphic` gives a nonzero coefficient vector
whose denominator-cleared combination vanishes at *every* point, which is what an ambient
differential-algebra argument consumes.

New modules on top of pass 57:

* `GermReducedPresentation` — every germ fraction reduces at every point
  (`exists_reduced_presentation_at`); two reduced presentations differ by *one* unit factor, the
  same for numerator and denominator (`exists_unit_factor_of_reduced_at`); a cleared combination
  transforms by the `m`-th power of the product of those factors
  (`siegelHomCombination_of_unit_factors`) — division-free, with no hypothesis on the zero divisors.
* `UniformLocalBound` — a locally bounded monotone property on a compact set has one uniform bound.
* `SiegelUniformTransition` — the transition datum at a point (`SiegelTransitionAt`), its existence
  with a local bound near every point of a chart, its uniformisation over the closed polydisc and
  then over the finitely many charts, and the resulting `htrans` with comparison constant `C^m`.
* `SiegelCountParameters` — `exists_siegel_count_params`: with `N` proportional to `m` the two
  opposing inequalities hold simultaneously; the factor `κ` is chosen so that `D·q^κ <= 1/2`, and
  the counting side needs only `m >= card ι · κ^n` because `(m+1)^(n+1) >= (m+1)·m^n`.
* `SiegelChartConstruction` — cancelling a nonzero holomorphic factor on a connected domain
  (`eqOn_zero_of_mul_eq_zero`), the reduced chart of a globally presented meromorphic function
  (`exists_reduced_chart`), the chart package of a whole family, one radius for every centre of a
  compact set, the translate of a chart by a period, and the cross identity of two charts across a
  period (`chartPackage_cross`).
* `SiegelTorusTranscendence` — the assembly.

The point where the argument used to fail is exactly where pass 57 applies: the chart comparison
happens on the overlap, away from either centre, and reducedness is a condition at the centre.  The
openness of coprimality closes that gap; everything else was already owned.

## Pass 59 — the noncompact period-quotient law in every dimension

Siegel's bound is transported into both meromorphic-field models of the tree and turned into the
card's law `(5)`.

* `SiegelMeroFieldDependence` — `exists_ne_zero_poly_aeval_of_compactSpace_quotient`: `n + 2`
  elements of `meroFieldGen (Set.univ)` with a common group of periods of compact quotient satisfy a
  nonzero polynomial relation over `C`.  Also `aeval_siegelPoly` (moved to `SiegelTorusTranscendence`),
  the evaluation of the Siegel polynomial in an arbitrary commutative `C`-algebra.
* `EntirePeriodSiegel` — the same in the entire fraction field `EntireField`, plus the
  cross-multiplied invariance criterion `fieldTranslateEquiv_fix_iff` and the period-escape law
  `not_compactSpace_quotient_of_hypertranscendental`.
* `GenPeriodEscapeLaw` — translation commutes with the directional derivation of the analytic germ
  ring and of the meromorphic field (`addTranslationAnalyticEquivGen_dirDeriv`,
  `addTranslationMeroEquivGen_dirDeriv`; proved through Leibniz on a fraction presentation, because
  `Derivation.leibniz_div` picks a different `Algebra Z` instance path than
  `meroFieldGenDirDifferential` bakes in), hence
  `not_compactSpace_quotient_of_hypertranscendental_gen` and
  `isEscapeSubgroup_meroPeriodSubgroupGen_of_hypertranscendental`.

All unconditional, axiom-clean, umbrella-wired.  Next on this card: the facet theorem `(13)`–`(18)`
— turn an `HTRealizableDim` datum into a `PeriodEscapeSeparation` by the Stanley--Reisner
facet-prime computation, giving `peDim <= htDim`.

## Pass 60 — the facet theorem: `peDim <= htDim`

```text
GaloisForLFunctions.HTGeometry.peDim_le_htDim
GaloisForLFunctions.HTGeometry.exists_periodEscapeSeparation_of_htRealizableDim
```

Two modules: `FacetSeparatorMonomial` (the separating monomial of a facet and its three
Stanley--Reisner membership facts) and `FacetPeriodEscape` (the carrier package, the abstract
hypertranscendence-from-matroid lemma, and the assembly).

Performance note worth keeping: the two elaboration blow-ups in this build were both *higher-order
unification* caused by leaving the reindexing map implicit — `AlgebraicIndependent.comp h _ hinj`
and `(differentialFamilyMatroid_indep_iff _ _).mp`.  Supplying the map and the family explicitly
removes the blow-up entirely; no `maxHeartbeats` increase is needed anywhere in these modules.  The
second lesson is to state the hypertranscendence lemma over an abstract differential field, so the
`FractionRing`/`OreLocalization` tower is never unfolded during unification.

## Card closed: `noncompact-period-quotient-facet-escape-law` moves to stage 3

Every mathematical claim of the card is now an unconditional Lean theorem:

* `(1)`–`(3)` the invariant `peDim` — already owned;
* `(4)`–`(5)` the noncompact period-quotient law, **in every dimension** — pass 59, on top of
  Siegel's bound for compact complex tori (pass 58) and the openness of coprimality of analytic
  germs (pass 57);
* `(13)`–`(18)` the facet theorem, hence `peDim <= htDim` — pass 60;
* `(19)`–`(20)` the hierarchy: `peDim <= ppDim` and `htDim <= ppDim` were already owned, so the
  chain `peDim <= htDim <= ppDim` is complete;
* `(21)`–`(22)` the exact wedge values — already owned
  (`boundaryWedge_htDim_eq_ppDim_lt_ffsDim`, `boundaryWedge_peDim_eq_two`).

The only unchecked gate left is the external "independent specialist proof and novelty audit",
which is the standing convention for stage-3 cards in this tree.

20 non-`ccm` cards remain in stage 2.

## Work queue for the 20 remaining non-`ccm` stage-2 cards

Recorded so the effort is directed rather than rediscovered.  For each card, the *mathematics* that
has to be built before a Lean formalization is anything but theatre.

**Closest to closure**

1. `gauss-component-quasi-inner-residue-hierarchy` — one named open core: the **relative `m`-fold
   telescope**.  The absolute telescope (`tendsto_gaussIterate`, `tendsto_gaussIterateInner`) and
   both brackets of the relative one-step error are proved
   (`tendsto_norm_gaussShiftedBlockDiag_expPiecewise_defect_zero`,
   `tendsto_norm_gaussShiftedBlockDiag_sub_rotationInv_family`).  The obstruction is that the
   normalized step operator has norm `≍ n^(1/m)`, so the induction must carry a *rate*: the
   `theta`-exponent bookkeeping of passes 36–40 with `log_div_le_rpow_div`.  Pattern to copy: the
   `m = 1` proof in `RHTower/GaussDiagonalLogResidue.lean`, whose relative bound is
   `norm_inner_gaussQuasiInnerG_sub_amplitude_le` (`‖err‖ ≤ |sigma_i| F(i)`, `F → 0`) combined with
   `exists_norm_gaussSampleValue_sq_mul_succ_le` (`|sigma_i| (i+1) ≤ C`).
2. `universal-first-order-entire-cascade-unit-cost` — an active long programme; the frontier is the
   algebraic model's tame-exponent/ideal-order dictionary (card log, parts 11–13).

**Blocked on one named classical theorem**

3. `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` — Selberg's positive-proportion theorem
   (`N_0(T) >> T log T`; Hardy–Littlewood's `>> T` is provably not enough, by the card's own lattice
   counterexample) and Bochner–Schwartz for positive-definite tempered distributions.
4. `bessel-order-intensity-hypertranscendence` — Dreyfus's DA-to-periodic-exponential classification.
5. `abelian-multiplication-tail-manin-horizon`, `embedded-manin-horizon-isogeny-reconstruction`,
   `isogeny-tail-maurer-cartan-holography`, `jet-horizon-translation-gauge-classification` —
   differential algebraic groups, Kolchin topology and Manin kernels; none present in mathlib.
6. `differential-variational-building-balance-law` — Ore localization plus affine buildings.

**Blocked on a shared foundation: covering dimension + Pontryagin dimension**

7. `almost-periodic-autonomous-ade-finite-frequency-law`,
   `almost-periodic-implicit-ade-relative-frequency-law`,
   `archimedean-relative-prime-cocycle-curvature` (through the finite real shifted-Gamma projective
   boundary law) — all three reduce to: covering dimension of a compact metrizable space, the
   finite closed-sum theorem, and `dim X = rank_Q (dual X)` for a compact connected abelian group.
   **Correction to those cards:** the tree does *not* lack Bohr theory — there are 79 modules
   (`BohrAlmostPeriodic`, `BohrSpectrum`, `BohrParseval`, `BohrBochnerEquivalence`,
   `BohrBochnerFejerApprox`, `AlmostPeriodicHull`, `KroneckerWeylDensity`, …).  What is missing is
   the dimension theory, not the almost periodicity.

**Blocked on special functions / one unaudited parent**

8. `all-depth-pair-face-signature-completeness`, `all-depth-compatible-pair-face-differential-matroid`
   — meromorphic principal parts on elliptic curves and the depth-two triptic DA-completeness
   theorem; the gluing engine and the localized rank law are already owned.
9. `finite-archimedean-gamma-product-boundary-law`, `irrational-triptic-source-effectivity-character`,
   `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`,
   `active-quasi-abelian-palette-exact-ht-dimension-classification` — Abe's growth class and the
   analytic Poincaré-series induction on quasi-Abelian groups.
10. `prime-valuation-dyadic-fermion-normal-cone-law`, `prime-wold-accelerated-type-modular-drift-law`
    — RH-facing; each still has open mathematics of its own on the card.

## Pass 61 — the spike estimates for the Gauss relative telescope

`RHTower/GaussSpikeMass.lean`: `sum_rpow_neg_head_le`, `spike_mass_le`, `sum_kernel_mul_spike_le`.
Unconditional, axiom-clean, umbrella-wired.  These are step 1 of the three-step plan the Gauss card
records for its single open core.  The point of the pair is that the moving spike has mass `≍ n`,
not `≍ n^(1+c)`, so a harmonic kernel — which sees it only from distance `≍ n` — transfers it into
the bulk with a bounded factor.

## Pass 62 — the operator telescope, and the spike transfer in usable form

`HTGeometry/OperatorPowerTelescope.lean` — `operator_pow_sub_eq_sum` and
`tendsto_norm_operator_pow_sub_zero`: the one-vector telescope
`X^r v - Y^r v = Σ_i Y^(r-1-i)((X-Y)(X^i v))`, whose weights are powers of `‖Y‖` only, so a
contraction model makes them disappear.  This is step 3 of the Gauss card's plan and is reusable
anywhere a growing operator is compared with a contraction model.

`RHTower/GaussSpikeMass.sum_kernel_mul_spike_band_le` — the spike-to-bulk transfer with explicit
constants, which is what the one-step estimate of step 2 consumes.

Both unconditional, axiom-clean, umbrella-wired, no raised heartbeats.

## Pass 63 — the Lebesgue dimension foundation (unblocks the three dimension-blocked cards)

The named blocker of `almost-periodic-autonomous-ade-finite-frequency-law`,
`almost-periodic-implicit-ade-relative-frequency-law` and
`archimedean-relative-prime-cocycle-curvature` was "covering dimension + Pontryagin dimension, absent
from mathlib".  Both halves are now Lean-proved, unconditional and axiom-clean, from the corpus's own
Brouwer fixed point theorem (`HTGeometry.BrouwerFixedPoint.exists_fixedPoint_of_retraction`).

**Restructured route.**  The cards' proofs go through `dim X_f ≤ 2n` (finite closed sum theorem) and
`rank_Q dual(X_f) = dim X_f` (Pontryagin).  Neither is needed in that form.  The whole argument
compresses to a single statement about the cube:

```text
k < m  ==>  there is no continuous injection of [0,1]^m into R^k.
```

and its group-theoretic companion

```text
Gamma abelian with m Z-independent elements
  ==>  the character space of Gamma contains a topological m-cube
  ==>  no continuous map into R^k with k < m separates that cube.
```

A hull that is locally embedded in a `2n`-manifold therefore cannot have `2n+1` independent
frequencies: Baire gives a sub-cube inside one regular chart, and the chart embeds it in `R^{2n}`.
The finite closed-sum theorem and the inductive-dimension characterisation are bypassed entirely.

**Modules (all wired into `GaloisForLFunctions.HTGeometry`, `formal lint passed`,
`[propext, Classical.choice, Quot.sound]`).**

| Module | Contents |
|---|---|
| `CoveringDimension` | order of a family, `HasCoveringDimLE`, monotonicity, closed-subspace and homeomorphism invariance |
| `CubeSeparation` | **Poincare--Miranda** (`exists_forall_eq_zero_of_boundary_signs`) and the **cube separation theorem** (`exists_mem_iInter_of_separators`), from Brouwer; `unitCube` basics, compactness |
| `BrickCover` | the `k+1` shifted families of open boxes: pairwise disjoint inside a family, covering, order `k+1`, mesh `sqrt(k)·delta` |
| `BrickCoverCompact` | the finite enumerated brick cover of a compact set |
| `GeneralPosition` | a nonempty open set escapes finitely many proper subspaces; points in prescribed open sets with no one in the span of `r` earlier ones; positive combinations of `r+1` of them are nonzero |
| `SeparatorMap` | `exists_separating_map`: the nonvanishing sign-prescribed map `K -> R^m` for compact `K ⊆ R^k`, `k < m` |
| `CubeNoEmbedding` | **`not_injOn_unitCube`**: no continuous injection `[0,1]^m -> R^k` for `k < m` |
| `CircleCoordinateCube` | `eq_of_exp_pi_mul_I_eq`, `not_separating_of_circle_coordinates` |
| `DivisibleExtension` | `exists_addMonoidHom_apply_eq_single`: a `Z`-independent family extends to real coordinates (`R^m` is an injective `Z`-module) |
| `IndependentCharacterCube` | `exists_character_cube`, `injOn_of_character_cube`, **`not_injOn_of_independent_family`** |

**The mechanism of `not_injOn_unitCube`.**  Given an injection `h` of the cube into `R^k`, the `m`
pairs of opposite faces map to uniformly separated compact sets.  A brick cover of the image of mesh
below that separation has order `k+1`; its partition of unity, weighted by vectors chosen in the sign
box each brick prescribes and in general position, gives a map `u` to `R^m` that never vanishes —
because a positive combination of at most `k+1 <= m` vectors in general position is nonzero.  The
coordinate zero sets of `u ∘ h` are then `m` separators of the opposite faces of the cube with empty
intersection, contradicting the cube separation theorem.

The general-position step is where `k < m` is used, and it is the reason the argument needs a
finite-dimensional Baire-type fact rather than the inductive dimension theory.

### Pass 63 addendum — deduplication against the covering-dimension lane

Two collisions with work already in the tree were found and removed:

- `HTGeometry/CoveringDimension.lean` (the shrinking-form `HasCoverDimLE` and its invariants) already
  existed; its content now lives in `HTGeometry/CoveringDimensionShrinking.lean`, together with
  `EuclideanCompactCoveringDimension.hasCoverDimLE_of_isCompact` (bound `5^m - 1`),
  `CoveringDimensionEmbedding.hasCoverDimLE_of_continuous_injective`, `BohrHullDimension` and
  `HullFiniteCoveringDimension`.  The refinement-form duplicate written in pass 63 was deleted; its
  one new theorem, closed-subspace monotonicity, was added to the canonical file as
  `HasCoverDimLE.of_isClosedEmbedding`.
- `HTGeometry/PoincareMiranda.lean` already proves `GaloisForLFunctions.poincare_miranda` (in the
  sharper `ContinuousOn` form) and defines `GaloisForLFunctions.unitCube`.  `CubeSeparation` now
  imports it and contains only the separation theorem and the cube vertices.

**The lanes are complementary, not overlapping.**  The existing modules give *upper* bounds on the
covering dimension of the Bohr hull; passes 63 gives the *lower* bound — `not_injOn_unitCube` and
`not_injOn_of_independent_family` — which is what the frequency-rank conclusion actually needs and
which no earlier module provides.

A sharper statement worth having later: the brick cover of `BrickCover` upgrades
`hasCoverDimLE_of_isCompact` from `5^m - 1` to the exact `m`.

## Pass 64 — the local-atlas frequency-rank law (the card's own mechanism, formalized)

After deduplication the tree already owned the *global* form of the frequency-rank bound
(`PhaseRankDimensionBound.rank_bohrHullFrequencies_le`: a continuous **injective** `Φ : BohrHull f → E`
forces `rank_Z (bohrHullFrequencies f) ≤ finrank E`).  The almost-periodic ADE cards need the *local*
form, because a singular implicit equation has no single regular chart — only a finite atlas of them.
That form is now proved.

```text
HTGeometry.le_of_unitCube_charts :
  the unit m-cube covered by finitely many closed sets, on each of which a continuous map to R^k is
  injective                                   ==>  m ≤ k
GaloisForLFunctions.card_le_of_hull_charts :
  an independent frequency packet of size r, and a finite closed cover of the Bohr hull with a
  continuous injective chart into R^k on each piece
                                              ==>  r ≤ k
GaloisForLFunctions.rank_bohrHullFrequencies_le_of_charts :
  same hypotheses                             ==>  rank_Z (bohrHullFrequencies f) ≤ k
```

Mechanism: the independent packet turns the cube into the hull through
`exists_continuous_hullParameter`, injectively because the characters separate its points
(`HTGeometry.eq_of_exp_pi_mul_I_eq`); the atlas pulls back to a finite closed cover of the cube;
Baire inside the cube gives one chart whose relative interior contains a full affine copy of the
cube (`HTGeometry.cubeBox`); and `HTGeometry.not_injOn_unitCube` — itself a two-step corollary of
the tree's `le_finrank_of_cube_faces` — closes it.

This is exactly steps `(15)`–`(19)` of `almost-periodic-autonomous-ade-finite-frequency-law`, and it
is the step the card claims as new over Cartwright and O'Brien: no common regular time, no global
uniqueness, only compactness of the hull.

**What the card still needs** (all analytic, none dimensional): the passage from a function
holomorphic and uniformly almost periodic on a strip to the `ℝ →ᵇ ℂ` carrier of the Bohr lane; the
minimal annihilating differential polynomial and its separant on the hull (the tree has
`DifferentialKernelCharacteristic.IsMinimalScalarDifferentialPolynomialRank.separant_not_mem`);
minimality of the hull flow to get `Z = ∅`; and the analytic implicit function theorem producing the
injective jet chart on each `F_j` (the tree has `RealAnalyticImplicit`, `U0.HolomorphicIFT`, and
`StripJetSeparation.eqOn_of_line_jet_eq_implicit`).

## Pass 65 — the dyadic digit layer of the prime-valuation card

`HTGeometry/EulerBinaryProduct.lean` and `HTGeometry/GeometricHellingerDigits.lean` close steps
`(2)`, `(3)`, `(7)`, `(8)`, `(9)` of `prime-valuation-dyadic-fermion-normal-cone-law`:

```text
one_sub_mul_prod_one_add_pow : (1 - q) * ∏_{j<J} (1 + q^(2^j)) = 1 - q^(2^J)     -- any comm ring
tendsto_prod_one_add_pow     : |q| < 1 -> ∏_{j<J}(1 + q^(2^j)) -> (1-q)^(-1)
prod_digit_div_field         : ∏_{j<J} q^(2^j e_j)/(1+q^(2^j)) = q^(Σ 2^j e_j)(1-q)/(1-q^(2^J))
bitHellingerAffinity a b j   := (1 + sqrt(ab)^(2^j)) / sqrt((1+a^(2^j))(1+b^(2^j)))
tendsto_prod_bitHellingerAffinity : ∏_{j<J} bit -> geometricHellingerAffinity a b
bitHellingerAffinity_zero_div_geometric : bit_0 / geo = (1-ab)/sqrt((1-a^2)(1-b^2))
one_le_parity_affinity_ratio            : that ratio is at least 1
```

Euler's binary product was absent from both mathlib and this tree; the search that found the
already-owned `geometricHellingerAffinity` (`PrimeValuationKakutaniSector`) and the strict parity
comparison (`RHTower.geometricPrimeValuationGramSq_lt_squarefreePrimeParityGramSq`) confirmed the
digit layer itself was new.

The card's remaining gates are the ones it lists as needing new mathematics: the squarefree
source-to-exceptional-reporter comparison and Xi conormal/multiplicity-jet conservativity.

## Pass 66 — the order-two shift-orbit mass obstruction

`HTGeometry/ShiftOrbitMassObstruction.lean` closes §3 of
`finite-archimedean-gamma-product-boundary-law` unconditionally.

```text
not_shiftDifference_negSumInvSq :
  H ≠ 0, s nonempty, y meromorphic on ℂ with finitely many poles
  ==>  ¬ ( z ↦ y(z+H) − y(z)  =ᶠ[cofinite]  z ↦ −∑_{i∈s} (z − p i)^(−2) )
not_shiftDifference_deriv_logDeriv_prod_affine :
  the same for the right-hand side  (P'/P)'  with  P(z) = ∏_{i∈s} (α i · z + β i),  α i ≠ 0
```

Mechanism: `laurentCoeff (fun z => y (z+H) − y z) a ℓ = laurentCoeff y (a+H) ℓ − laurentCoeff y a ℓ`
(the tree's `laurentCoeff_shiftDiff`), so the order-`ℓ` coefficients along `a + Hℤ` telescope; the
pole set of `y` is finite so the family has finite support and the telescoped sum is zero.  The
order-two coefficient of `−∑ (z − p i)^(−2)` at `q` is `−#{i : p i = q}`, so the same sum equals
`−#{i : p i ∈ a + Hℤ}`, forcing that count to vanish.

Three strengthenings over the paper argument: no bound on the pole order of the solution is needed
(the indices telescope independently); no coset hypothesis on the poles of the right-hand side is
needed (choose the orbit through any one of them); and "rational" is weakened to "finitely many
poles".

**Deduplication.**  The tree already owned the single-pole unit-step case twice —
`GaloisForLFunctions.no_rational_shift_inv_sq` (`RationalShiftNoSolution`, polynomial form) and
`no_finitePole_solution_digammaShiftDerivative` (`GammaProjectiveBoundary`, meromorphic form).  Both
argue by pole *position* on the orbit (largest and smallest real part), which is blind to
multiplicity and therefore cannot handle the several-poles-per-orbit situation of `(12)`.  The new
module argues by order-two *mass*, which can; it subsumes both.

Card `finite-archimedean-gamma-product-boundary-law` still needs, for stage 3: sectorial Stirling,
the formal Laurent shift field, the ADH dichotomy, the product-field valuation `(6)`, and the
holomorphic Bohr recurrence of §7.

## Pass 67 — the accelerated Wold scale and the no-sewing theorem

`RHTower/AcceleratedWoldType.lean` closes §2, §3 and §4 of
`prime-wold-accelerated-type-modular-drift-law`.

```text
tendsto_mertensProduct_mul_ell2_reflectedSewing :
  0 < c < 1/2  ⟹  a_N · ℓ₂ (H_N(-c) / H_N(c)) → 2 e^(-γ) c,   ℓ₂ y = log (1 + log (1 + y))
tendsto_mul_ell2_zero_of_log_le :
  log (1 + R_N) ≤ C · a_N^(-K)  ⟹  a_N · ℓ₂ (R_N) → 0     (ordinary essential singularities are
                                                            invisible to the accelerated scale)
eventually_lt_mertensProduct_mul_ell2_opNorm :
  R_N : E_N →L[ℝ] F_N with R_N v_N = w_N, ‖v_N‖ = H_N(c), ‖w_N‖ = H_N(-c)
  ⟹  the accelerated type of ‖R_N‖ is at least 2 e^(-γ) c — for normed spaces of any dimension
```

The analytic content was already owned (`MertensThirdTheorem`,
`EulerHellingerSewingLogRatio.tendsto_log_logReflectedSewing_div_log`,
`EulerHellingerAcceleratedBoundary.tendsto_mertensProduct_mul_log_logReflectedSewing`).  The new
work is the scale `ℓ₂` of the card's definition `(3)` — the corpus theorem is stated with
`log ∘ log`, and the two agree after multiplication by `a_N → 0` once the sewing cost exceeds `e`,
which needs `logReflectedSewingBelow → ∞` — plus the two obstruction theorems.

## Pass 67 addendum — the cascade card's determinant gap is already closed

`universal-first-order-entire-cascade-unit-cost` records "modulo one explicit finite determinant".
That determinant is proved: `HTGeometry/ExpPolyAllHeights.lean` has
`headJetJacobian_det_ne_zero_all` and hence `exactDifferentialOrder_expPolyCascade_all`
(axiom-clean, wired).  The card's consolidated-status section predates that module.  Its remaining
gap is the *general* first-order cascade — Reduction III's Wiman initial law.

### Pass 67 addendum 2 — §7 of the Wold card closed

`tendsto_mul_ell2_iteratedDeriv_zero` closes the finite-divisor noncreation theorem `(22)`–`(23)`:
for a holomorphic Banach-space-valued family with accelerated type zero on the boundary circle,
every fixed jet at the centre has accelerated type zero.  Mathlib's
`Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le` supplies `(24)`, and
`tendsto_mul_ell2_zero_of_le_const_mul` / `..._of_le_add` supply the stability under a fixed scalar
and under finite sums.  Sections 2, 3, 4 and 7 of `prime-wold-accelerated-type-modular-drift-law`
are now unconditional in Lean; §5 (three source scales) and §6 (four-chart modular charge) remain.

### Pass 67 addendum 3 — the saturation law

`tendsto_mertensProduct_mul_ell2_of_log_linear`: any family whose logarithm grows linearly in the
cutoff has accelerated Wold type exactly `e^(-γ)`, independently of the growth constant.  This is
the abstract mechanism of `(18)` and `(18k)` of the Wold card; instantiating it for the concrete
prime-square and Weyl families needs only `log B_x(c) = (|c| + o(1)) ϑ(x)` and the prime number
theorem.  Factored through `tendsto_mertensProduct_mul_ell2_of_tendsto`, which says the scale `ℓ₂`
and the double logarithm carry the same accelerated type once the family's logarithm diverges.

## Pass 68 — index-translation rigidity (the prime-log Gamma fixed-field law)

`HTGeometry/IndexTranslationRigidity.lean` closes the algebraic core of `(12)` of
`archimedean-relative-prime-cocycle-curvature`.

```text
eq_C_of_indexTranslation_invariant :
  Λ abelian, μ of infinite order, K a field, P Q ≠ 0 in MvPolynomial Λ K with IsRelPrime P Q,
  (indexTranslation μ P) * Q = P * (indexTranslation μ Q)   ⟹   P and Q are constants
```

i.e. the fixed field of the index translation `X_λ ↦ X_{λ+μ}` on the rational function field with
variables indexed by `Λ` is the constant field.  Mechanism: the translate of a polynomial has the
translated variable set; coprimality makes numerator and translate divide each other, so their
variable sets agree (the tree's `mvPolynomial_vars_subset_of_dvd`); and a finite subset of a group
invariant under an infinite-order translation is empty.

`IsRelPrime`, not `IsCoprime`, is the right notion here — in a multivariable polynomial ring the
Bezout condition is far stronger than having no common nonunit factor.

Remaining for the card: the differential-coordinate version of the same statement, and the two
imported analytic/Galois inputs (Wang–Yao, Hardouin–Singer).

## Pass 69 — the operator balance law

`HTGeometry/OperatorBalanceLaw.lean` closes `(12)` of `differential-variational-building-balance-law`:
an operator matrix invertible over `K[∂;δ]` (not merely over the skew field) has row lattice equal
to the integral lattice, hence trivial conductor, hence all elementary divisors of degree zero —
`∑_i μ_i = 0`.

The card's §9 is stale.  The tree already owns the entire lattice model that the card describes via
affine buildings: `DifferentialOperatorOreField` (Ore condition, `PseudoDiffOp` as a `DivisionRing`),
`OperatorLattice` (integral/row/saturated lattices and their commensurability),
`OperatorConductorLength` (conductor length = sum of elementary-divisor degrees),
`OperatorCartanComparison` (`tendsto_normalized_ambient_cartan`, the normalized Cartan limit),
`DifferentialIndependentObservableNet` (the Fekete gauge).  The remaining links to the card's
statement are the semilinear differential-automorphism action `(7)`–`(10)` and the identification of
the relative-position vector `μ_n` with the Cartan prefix invariants.

## Pass 70 — the simultaneous finite-divisor lifting lemma

`HTGeometry/SimultaneousDivisorLifting.lean` closes the second algebraic lemma of
`all-depth-pair-face-signature-completeness` (the first, the multi-telescoping ideal identity, was
already `TelescopeIdeal`).

```text
exists_forall_sub_mem_span_singleton :
  D i − D j ∈ (x i, x j) for all i, j ∈ s, and transverse coprimality
  ⟹ ∃ b, ∀ i ∈ s, b − D i ∈ (x i)
transverseCoprime_of_isRelPrime_quotient :
  transverse coprimality holds when the x i are pairwise relatively prime modulo each x j
```

i.e. exactness of `R → ⨁_i R/(x_i)` at the equalizer of the pairwise reductions.  The second
theorem hands the hypothesis to `TelescopeIdeal.iInf_span_singleton_eq_span_prod_of_primes`, which
is exactly the Laurent-ring situation `x_i = u_i − 1`.

The whole algebraic layer of the card's realization proof is now Lean-proved; what remains is
analytic (elliptic principal parts) and the imported depth-two completeness theorem.

## Pass 71 — damped jets decay (item 4 of the torusless growth lemma)

`HTGeometry/DampedJetDecay.lean` closes item 4 of the growth stability lemma of
`torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness`, hence equation `(6)` of that card:

```text
norm_iteratedDeriv_cexp_mul_mul_le :
  ‖d^m (e^(a·) g)(z)‖ ≤ (1 + ‖a‖)^m · e^(Re (a z)) · sup_i ‖d^i g(z)‖
tendsto_norm_iteratedDeriv_damped_zero :
  ‖a_n‖ ≤ L B_n, Re (a_n z) ≤ −c B_n (c > 0), B_n → ∞, uniform jet bound
  ⟹ every fixed jet of the damped family tends to zero
```

The polynomial in the damping parameter is the exact Leibniz binomial sum `∑_i C(m,i) ‖a‖^i`, and a
fixed jet order fixes its degree, so exponential decay wins.  The estimate is uniform in the
undamped factor, which is what lets a whole complement-lattice family be discarded at once.

## Pass 72 — cylinder splitting and the horizon gauge

`HTGeometry/JetHorizonTranslationGauge.lean` closes `(5)`, `(9)` and the converse half of `(4)` of
`jet-horizon-translation-gauge-classification`, none of which needs the DCF layer the card names as
its boundary.

```text
transStab Y                     the translation stabilizer, as an AddSubgroup
mem_iff_exists_add_slice        Y splits as (transStab Y) + (Y ∩ B) for any complement B
add_slice_unique                the splitting is unique
transStab_slice_eq_bot          the transverse slice has trivial stabilizer
pow_apply_sub_eq_zero           σ fixing δ^n y ⟹ δ^n (σ y − y) = 0
pow_apply_add_of_apply_eq_zero  δ c = 0, n ≥ 1 ⟹ δ^n (y + c) = δ^n y
```

Both halves are stated for an arbitrary abelian group and an arbitrary additive endomorphism
playing the role of `δ`, so they apply verbatim to the differential setting once it exists.

## Pass 73 — the sharp covering dimension of a compact set in `R^k`

`HTGeometry/EuclideanSharpCoveringDimension.lean`:

```text
hasCoverDimLE_zero_of_subsingleton    a subsingleton space has covering dimension 0
hasCoverDimLE_of_isCompact_euclidean  K ⊆ R^k compact  ⟹  HasCoverDimLE ↥K k
```

This replaces the bound `5^k − 1` of `EuclideanCompactCoveringDimension.hasCoverDimLE_of_isCompact`
by the exact value, the sharpening noted in the pass-63 addendum.  Mechanism: take a Lebesgue number
`δ₀` of the given cover, run the brick cover of `BrickCoverCompact` at mesh `√k·δ < δ₀` so that each
brick lies inside one member of the cover, and group the bricks by a chosen such member; the order of
the shrinking is then the order `k + 1` of the brick cover.

The matching lower bound is `HTGeometry.not_injOn_unitCube` (pass 63): `[0,1]^k` does not embed in
`R^{k−1}`.  Together they give the Lebesgue covering dimension of a compact set with nonempty
interior in `R^k` exactly, which is what the three dimension-blocked cards
(`almost-periodic-autonomous-ade-finite-frequency-law`,
`almost-periodic-implicit-ade-relative-frequency-law`,
`archimedean-relative-prime-cocycle-curvature`) consume.

## Pass 74 — the multiplication-tail fixed-field identity, and two more stale gaps

`HTGeometry/MultiplicationTailFixedField.lean` assembles the field-theoretic form of `(6)` of
`abelian-multiplication-tail-manin-horizon`:

```text
iInf_differentialTranslationFixedField_eq_kolchinClosure :
  ⋂_n L^(S n) = L^(kolchinClosureOver K (⋃_n S n))
```

given the card's own input that every element's translation stabilizer is Kolchin closed.  The
density half is the tree's `DifferentialKolchinClosure.differentialTranslationFixedField_eq_of_kolchinClosureOver_eq`;
the new part is the tower step (fixed field of a union = intersection of fixed fields) and the
assembly.

**Two more stale card gaps found.**

- `abelian-multiplication-tail-manin-horizon` states "Mathlib and this project do not currently
  contain Kolchin-closed groups".  The tree owns the whole Kolchin layer:
  `differentialZeroLocusOver`, `kolchinClosureOver`, `IsKolchinClosedOver`, the topology, and the
  fixed-field density theorem.
- `all-depth-compatible-pair-face-differential-matroid` lists "an integer orbit-height law (which
  supplies free translates)" among its remaining inputs.  `HTGeometry/OrbitHeightFreeTranslates.lean`
  proves it — `hasFreeTranslates_of_intHeight`, `hasFreeTranslates_orbitUnion`,
  `hasFreeTranslates_orbit_of_aperiodic`, and the concrete meromorphic-translation instance
  `hasFreeTranslates_meroOrbit_of_aperiodic` — all axiom-clean and wired.

## Pass 75 — the minimality step of the almost-periodic cards

`HTGeometry/MinimalFlowJetVanishing.lean` closes §2 `(8)`–`(9)` of both
`almost-periodic-autonomous-ade-finite-frequency-law` and
`almost-periodic-implicit-ade-relative-frequency-law`:

```text
exists_ne_zero_of_exists_ne_zero :
  Φ : ι → X → Y an equivariant family of continuous functionals on a flow with every orbit dense,
  and one point where some Φ i is nonzero
  ⟹ at every point some Φ i is nonzero
```

With `Φ_t (g) = Sep_P (g(t), …, g^(n)(t))` and the real translation flow — which shifts the index
`t`, so equivariance is literal — this is `Z = ∅`: no hull member is everywhere singular.  The jet
continuity it consumes is the tree's `HolomorphicJetReturn` / `StripRelationPropagation` /
`DeningerArithmeticContinuousJets` layer.

### Pass 75 addendum — §3 of the almost-periodic cards

The same module adds the compactness step:

```text
exists_finite_closed_cover_subordinate :
  compact regular space, open cover  ⟹  finite closed refinement subordinate to it
exists_finite_closed_regular_cover :
  Φ equivariant continuous, nowhere all-vanishing  ⟹  finite closed cover with one nonvanishing
  functional per piece
```

Chained after `exists_ne_zero_of_exists_ne_zero` this is §2 → §3, and its output is exactly the
closed covering family that `card_le_of_hull_charts` consumes.  Mathlib has no shrinking lemma in
this toolchain, so the refinement is proved directly: regularity gives a closed neighbourhood inside
the chart at each point, compactness selects finitely many of their interiors.

## Pass 76 — the tail stabilizer is Kolchin closed

`HTGeometry/MultiplicationTailFixedField.lean` gains the stabilizer layer for
`embedded-manin-horizon-isogeny-reconstruction`:

```text
isKolchinClosedOver_translationStabilizerSet :
  the stabilizer of any set of field elements is Kolchin closed
kolchinClosureOver_iUnion_subset_translationStabilizerSet_tail :
  the Kolchin closure of all tower labels stabilizes the tail
translationStabilizerSet_tail_eq_kolchinClosureOver :
  with the reverse inclusion, the tail stabilizer is exactly that closure
```

The first makes the tail stabilizer a Kolchin-closed set — a differential algebraic subgroup rather
than merely a subgroup — which is what the identification with the Manin kernel needs; it follows
from `isKolchinClosedOver_sInter` because a stabilizer is an intersection of element stabilizers.
The remaining half is the Kolchin Galois correspondence (nothing outside the closure stabilizes the
tail) plus the identification of the closure with `A^♯`.

## Pass 77 — finite palettes cannot carry an infinite free orbit

`HTGeometry/FiniteShadowCapacity.lean` gains the capacity statement that discharges the `hcompact`
hypothesis of `activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not`, for
`active-quasi-abelian-palette-exact-ht-dimension-classification`:

```text
not_differentialIndependent_of_finitePalette :
  n differentially independent sources, constant coefficients, n+1 distinct members
  ⟹ not differentially independent
not_differentialIndependent_cyclicOrbit_of_finitePalette :
  a complete cyclic ℤ-orbit inside a finite palette is never differentially free
```

This is the compact-kernel finite-capacity theorem in the exact shape the active-quotient theorem
consumes.  The analytic input that remains is the production of the finite constant-coefficient
source presentation on the compact fibre, not the capacity argument itself.

## Pass 78 — the two-piece amplitude class and the spike transfer

`RHTower/GaussSpikeMass.lean` gains the invariant class of
`gauss-component-quasi-inner-residue-hierarchy` and the estimate its step 1 named as the only new
one needed:

```text
spikeProfile, TwoPieceAmplitude          the class: uniform harmonic part + moving spike
sum_kernel_mul_spikeProfile_pos_side_le
sum_kernel_mul_spikeProfile_neg_side_le
kernel_mul_spikeProfile_peak_le
    a harmonic kernel reads the whole spike with weight K/(1 + n/4) against mass ≍ B n,
    so the transfer into the bulk is O(B), independent of n
```

Remaining: closure of the class under `B`, `B^(−2)`, `S̃`, `S̃*` with `n`-independent constants, and
the one-step estimate; step 3's telescope is already built.

## Pass 79 — Corollary D of the isogeny-tail card

`HTGeometry/FiniteHolonomyTail.lean` proves the field-theoretic content of `(8)` of
`isogeny-tail-maurer-cartan-holography` unconditionally:

```text
fixedSubset_iInter        fixed parts commute with intersections
image_fixedSubset         σ injective, commuting with F  ⟹  σ '' (E^F) = (σ '' E)^F
iInter_image_fixedSubset  ⋂_n σ_n '' (E^F) = (⋂_n σ_n '' E)^F
```

so `Tail(R) = (Tail α)^F` follows formally from Theorem A.  Injectivity of the pullback is used in
exactly one direction: an `F`-fixed element of the image is the image of an `F`-fixed element.

`(2)`–`(3)` of the same card is the already-proved
`MultiplicationTailFixedField.iInf_differentialTranslationFixedField_eq_kolchinClosure`.  What is
left is Theorem A's finite étale Galois description `(1)` and the logarithmic-derivative quotient
`(4)` — both scheme-level.

## Pass 80 — the Bessel card's reduction is machine-checked

`HTGeometry/BesselOrderDreyfusNormalForm.lean` states the classification's output shape and proves,
unconditionally, that neither Bessel carrier has it:

```text
DreyfusProgressionNormalForm x₀ f
not_dreyfusProgressionNormalForm_realModifiedBesselKOrder
not_dreyfusProgressionNormalForm_realModifiedBesselOrderIntensity
not_differentiallyAlgebraic_..._of_classification     the reduction, for any DA predicate
```

So `bessel-order-intensity-hypertranscendence` is exactly one arrow from closure, and that arrow is
Dreyfus's classification.  The Riccati bypass was checked and fails for a structural reason worth
recording: `r = ρy/y` satisfies a first-order rational shift equation and is DA whenever `y` is, and
the tree already excludes rational `r`, but "not rational ⟹ not DA" *is* the classification —
differential algebraicity alone gives no growth bound (`exp (exp z)` satisfies `y y'' = y y' + (y')²`
and has infinite order), so the shift equation is what supplies `(9)`.

mathlib has no Picard–Vessiot theory, differential or difference; that foundation is what this card
waits on, not any assembly step.

### Pass 78 addendum — multiplier stability of the two-piece class

```text
TwoPieceAmplitude.mul_multiplier :
  ρ bounded by K₁ in the bulk and by K₂ (n/(1+|n+j|))^(c') in the band
  ⟹ the class is preserved with A ↦ K₁A, B ↦ K₂(A/(1+n/2)^θ + B), c ↦ c + c'
```

The exponent adds — one application of `R̃_n` costs `1/m` with `ρ_j ≍ (n/|n+j|)^(1/(2m))` and two
multiplier factors, so the class survives with `c < 1` for the length of the card's telescope — and
the uniform mass inside the band is absorbed into the spike, which is the reason the class cannot be
a uniform bound with a moving constant.

## Pass 82 — local injectivity becomes injectivity on a closed piece

`HTGeometry/MinimalFlowJetVanishing.lean` gains the second compactness refinement, closing
`(15)`–`(16)` of the two almost-periodic cards:

```text
exists_finite_closed_cover_injOn        E injective near every point of a compact regular space
                                        ⟹ a finite closed cover with E injective on each piece
exists_finite_closed_cover_chart_injOn  the same with one chart chosen per point
```

This is what turns the implicit-function theorem's local uniqueness into the global injectivity of
`E_j` on `F_j` that `card_le_of_hull_charts` consumes; without it the observation map only embeds
the hull in `ℂ^(m(n+1))` with `m` the number of samples, so the dimension bound would depend on the
cover rather than on the differential order.

## Pass 83 — the analytic IFT chart was already owned; sixth stale gap

`StripJetSeparation.eqOn_of_line_jet_eq_implicit_local` is exactly `(14)`–`(16)` of the two
almost-periodic cards: strip-holomorphic solutions of an implicit relation dominant in the top jet,
with equal lower jets at a sample time, agree on the whole strip.  It is proved through
`ImplicitLipschitzGraph.exists_lipschitz_implicit` (the explicit Lipschitz branch), the twisted line
ODE, ODE uniqueness and the identity theorem — the card's own chain.

`HTGeometry/RegularChartInjectivity.lean` packages it as the `Set.InjOn` hypothesis of
`card_le_of_hull_charts`:

```text
injOn_lineJet_of_implicit_dominant, injOn_lineJet_of_implicit_dominant_subset
```

That is the sixth stale gap found this session.  Of the analytic obligations those two cards list,
only the strip-to-`ℝ →ᵇ ℂ` carrier passage remains; the separant enters only through the dominance
hypothesis `C < ‖∂P/∂Y_n‖`.

## Pass 84 — the carrier passage was owned; `ℂ^n` as `ℝ^(2n)`

Seventh stale gap: the strip-to-`ℝ →ᵇ ℂ` passage is
`VerticalAlmostPeriodicDerivative.isBohrAlmostPeriodic_line` together with
`StripAlmostPeriodicBounds.exists_bound_of_isStripAlmostPeriodicOn` and the two Bochner
equivalences; `StripSolutionPhaseRank.rank_le_of_strip_solution` even assembles the *non-sharp*
frequency-rank bound `2·#T·(n+1)` from them.

`HTGeometry/ComplexJetEuclidean.lean` adds the last piece of glue for the *sharp* `2n` route:

```text
complexJetToEuclidean n : (Fin n → ℂ) → EuclideanSpace ℝ (Fin (n*2))
continuous_complexJetToEuclidean, injective_complexJetToEuclidean
injOn_complexJetToEuclidean_comp, continuousOn_complexJetToEuclidean_comp
```

The exponent is right because `injOn_lineJet_of_implicit_dominant` separates by the jets of orders
`0 … n−1` only — the top jet is recovered from the dominant relation — so the chart lands in
`ℂ^n ≅ ℝ^(2n)` and `card_le_of_hull_charts` reads `2n`, not `2(n+1)`.

Remaining for the two almost-periodic cards: transport the per-piece charts through
`exists_carrier_representatives` and instantiate `card_le_of_hull_charts`.

## Pass 85 — the order-sharp frequency-rank theorem

`HTGeometry/StripSolutionPhaseRankSharp.lean` proves `(19)` of both almost-periodic cards:

```text
rank_le_of_regular_jets_sharp     carrier level:  rank_ℤ Γ(f) ≤ 2n
rank_le_of_strip_solution_sharp   from a strip almost-periodic holomorphic solution of P = 0 with a
                                  family of dominant regular regions covering the carrier
```

unconditional and axiom-clean.  This replaces the tree's `rank_le_of_strip_solution`, whose bound
`2·#T·(n+1)` grows with the atlas, by one depending only on the differential order.

The mechanism is the closed-cover route assembled over passes 75, 82, 83 and 84: the regular sets
are open and cover the carrier; `exists_finite_closed_cover_subordinate` gives a finite closed
refinement; on each closed piece the single jet at that piece's own sample time separates, by
`carrier_eq_of_jet_eq_local`, using orders `0 … n−1` only because the top jet is recovered from the
dominant relation; `complexJetToEuclidean` turns that chart into one valued in `ℝ^(2n)`; and
`card_le_of_hull_charts` reads the bound off the closed cover.

### Pass 85 addendum — the bound reaches the frequency group of `f`

```text
rank_le_of_addSubgroup_le                     rank monotone under inclusion of subgroups of ℝ
rank_bohrSpectrum_le_of_strip_solution_sharp  rank_ℤ ⟨Bohr spectrum of f⟩ ≤ 2n
```

`(4)` needed only `BohrHullFrequency.closure_bohrSpectrum_le_bohrHullFrequencies`, already in the
tree, plus rank monotonicity.  The card's quantitative law is therefore a single unconditional
axiom-clean theorem whose hypotheses are the card's own setting.

## Pass 86 — §1 was owned (eighth stale gap), and the dominance bridge

`AutonomousSeparant.exists_minimal_with_separant` is `(5)`–`(6)` of the almost-periodic cards:
Ritt's separant step, already in the tree, axiom-clean.

`HTGeometry/DominantNeighborhood.lean` adds the bridge from its qualitative conclusion to the
quantitative hypothesis of the frequency-rank theorem:

```text
exists_convex_dominant_nbhd :
  P' continuous at y₀, k-th partial coefficient nonzero
  ⟹ an open convex ball S ∋ y₀ and C ≥ 0 with ‖P' y − P' y₀‖ ≤ C on S and C < ‖∂P/∂Y_k‖
```

`C = ‖∂P/∂Y_n‖/2` and a ball where continuity keeps `P'` within `C` of its centre value.

All four sections of both cards are now Lean-proved.  The residue is the translation between the
two encodings of the relation — §1's `Polynomial (MvPolynomial (Fin n) ℂ)` with
`Polynomial.derivative` as separant versus §4's `P : (Fin (n+1) → ℂ) → ℂ` with
`partialCoeff (P' y) (Fin.last n)` — plus continuity of the derivative of a polynomial relation.

## Pass 87 — the two encodings of the autonomous relation are identified

`HTGeometry/AutonomousJetRelation.lean`:

```text
jetRelation n P y                       the relation as a function of the full jet
autonomousAnnihilator_iff_jetRelation   the stored annihilation is vanishing of jetRelation
hasDerivAt_jetRelation_last             ∂/∂y_n of the relation is the stored separant
exists_minimal_jetRelation_separant     Ritt's step in the jet-function language
```

`hasDerivAt_jetRelation_last` is the point: "the separant does not annihilate" and "the top partial
derivative does not vanish" are the same statement, so `exists_minimal_with_separant` feeds
`exists_convex_dominant_nbhd` directly.

Every step of both almost-periodic cards is now a Lean theorem.  What remains is one top-level
assembly quantifying over `f` alone, which needs Fréchet differentiability of `jetRelation n P` in
all `n+1` variables with continuous derivative — true because it is a polynomial map, not yet
written in that form.

## Pass 88 — the relation is smooth and its top partial is the separant

`HTGeometry/AutonomousJetRelation.lean`:

```text
contDiff_mvEval, contDiff_jetRelation, continuous_fderiv_jetRelation
partialCoeff_fderiv_jetRelation_last :
  partialCoeff (fderiv (jetRelation n P) y) (Fin.last n) = jetRelation n (derivative P) y
```

The identity is proved by differentiating along the line through `y` in the last coordinate two
ways — chain rule through `fderiv`, and `hasDerivAt_jetRelation_last` — and using uniqueness.

`continuous_fderiv_jetRelation` supplies the continuity hypothesis of `exists_convex_dominant_nbhd`
and the identity supplies its nonvanishing hypothesis from Ritt's separant step, so the dominant
convex region at each regular jet is constructible from the card's own data.  Every ingredient of
the two almost-periodic cards is now a Lean theorem; the top-level single statement from `f` to
`rank_ℤ Γ(f) ≤ 2n` is the only thing not yet written.

## Pass 89 — the almost-periodic law in one statement

```text
rank_bohrSpectrum_le_of_autonomous_strip_solution :
  F holomorphic and strip almost periodic, annihilated by an autonomous differential polynomial of
  order n, every solution on the substrip regular at some time
  ⟹ rank_ℤ ⟨Bohr spectrum of f⟩ ≤ 2n
```

unconditional, axiom-clean.  The dominant convex regions are constructed inside the proof rather
than assumed: one per regular jet, from `exists_convex_dominant_nbhd` with continuity from
`continuous_fderiv_jetRelation` and nonvanishing from `partialCoeff_fderiv_jetRelation_last`.  The
index set is (regular jet, sample time) and the atlas hypothesis is exactly `(9)`.

Remaining on the two almost-periodic cards: deriving `(9)` for this relation from §1 and §2, i.e.
instantiating `exists_ne_zero_of_exists_ne_zero` at
`Φ_t (g) = jetRelation n (derivative Pp) (jet g at t)` and feeding it the minimal annihilator.

## Pass 90 — minimality with the flow as an explicit family

```text
exists_ne_zero_of_dense_translates :
  Φ equivariant continuous, flow given as maps T g with dense orbits, nonvanishing somewhere
  ⟹ nonvanishing everywhere
```

No group-action instance needed, which is what the Bohr hull requires (`T t x = x + bohrIota f t`);
density of every orbit is `CarrierTranslationEquivariance.denseRange_bohrIota_add`.

The single remaining edit for the two almost-periodic cards: record translation equivariance of the
carrier representatives, `rep (x + bohrIota f s) z = rep x (z + s·i)`, among the conclusions of
`StripSolutionPhaseRank.exists_carrier_representatives`.  It holds by construction (the
representatives are `bohrEval Gb (ν x)` with `ν` a hull morphism) but is not currently returned.
With it, `Φ_t (x) = jetRelation n (derivative Pp) (jet of rep x at t)` is equivariant, `hx₀` is
`exists_minimal_jetRelation_separant` at `f`, and `(9)` follows — discharging the last hypothesis of
`rank_bohrSpectrum_le_of_autonomous_strip_solution`.

## Pass 91 — carrier representatives are translation equivariant

```text
eqOn_rep_add_bohrIota :
  EqOn (rep (x + bohrIota f s)) (fun z => rep x (z + s·i)) on the substrip
```

derived from the conclusions `exists_carrier_representatives` already returns, so no edit to that
theorem was needed: on the line it is `bohrIota_add`, and `eqOn_of_eventuallyEq_line` promotes the
line equality to the strip.

This makes `Φ_t (x) = jetRelation n (derivative Pp) (jet of rep x at σ + t·i)` equivariant for the
hull flow.  With continuity (`continuous_jet_of_representatives` + `contDiff_jetRelation`), density
of every orbit (`denseRange_bohrIota_add`) and nonvanishing at `f`
(`exists_minimal_jetRelation_separant`), `exists_ne_zero_of_dense_translates` gives `(9)`.

## Pass 92 — the autonomous almost-periodic card's main theorem is closed; the divisor half is opened

`GaloisForLFunctions.HTGeometry.AutonomousStripSeparant` (new) relativises Ritt's separant step to a
strip and reads it on the central line:

```text
StripAnnihilator σ R F n P          P annihilates F along its jet at every point of the strip
exists_minimal_stripAnnihilator     a degree-minimal nonzero strip annihilator exists
separant_not_stripAnnihilator       in characteristic zero its separant does not annihilate
differentiableOn_mvEval_comp        polynomial evaluation at holomorphic coordinates is holomorphic
differentiableOn_jetRelation_jets   hence the relation along a holomorphic jet is holomorphic
eqZero_of_eqZero_line               a holomorphic function vanishing on the central line vanishes
exists_minimal_strip_separant_line  ⟹ a minimal equation whose separant is nonzero at a REAL time
```

The last step is the identity theorem: `separant_not_stripAnnihilator` only gives a point of the
strip, and the carrier is built from the line, so the nonvanishing has to be moved to the line.

`GaloisForLFunctions.HTGeometry.AutonomousCarrierRegularity` (new) then runs the card's §2–§4:

```text
exists_carrier_separant_ne_zero
    Φ_t (x) = jetRelation n D (jet of rep x at σ + t·i) is continuous in x, equivariant
    (Φ_t (x + bohrIota f s) = Φ_(s+t) (x), by iteratedDeriv_rep_translate), and nonzero at the
    origin of the carrier (iteratedDeriv_rep_zero); exists_ne_zero_of_dense_translates gives (9)
rank_bohrHullFrequencies_le_of_stripAnnihilator
rank_bohrHullFrequencies_le_of_strip_differential_equation
rank_bohrSpectrum_le_of_strip_differential_equation
rank_bohrSpectrum_observable_le_of_strip_differential_equation
```

all unconditional and axiom-clean.  The closed form is the card's own statement with nothing left
over:

```text
0 < R, F holomorphic on the strip, F strip almost periodic, f its line restriction,
0 < n, some nonzero P annihilates F on the strip, no nonzero annihilator is free of the top jet
  ==>  rank_ℤ ⟨Bohr spectrum of f⟩ ≤ 2n
```

Uniform continuity and total boundedness of the orbit are no longer hypotheses
(`isBohrAlmostPeriodic_line`, `uniformContinuous_of_isBohrAlmostPeriodic`,
`hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic`), the substrip is chosen inside the proof, and the
Borel structure on the carrier is `borel _`.

`HTGeometry/CarrierRepTranslation.lean` from pass 91 was removed: `CarrierTranslationEquivariance`
already owned `rep_translate_eqOn`, `iteratedDeriv_rep_translate` and `iteratedDeriv_rep_zero`.

### What is left on the card: §5, the divisor law

`rank_bohrSpectrum_observable_le_of_strip_differential_equation` is the card's own closing sentence —
every continuous translation-equivariant observable of the carrier inherits the bound.  What is not
yet Lean is that the zero-divisor map *is* such an observable, i.e. that

```text
x ↦ ∑ (zeros a of rep x) (order a) · φ(a)
```

is continuous on the carrier for every continuous compactly supported `φ` inside the substrip.  That
is the classical Hurwitz statement, and the corpus already owns every ingredient:

```text
AnalyticBallFinsetFactorization.exists_finset_zeroFree_factorization
    peeling: an analytic function on a ball, nonzero somewhere, is a finite product of linear
    factors carrying its zeros times a nonvanishing analytic factor
DiscZeroFactorization.circleIntegral_weighted_logDeriv_eq_powerSum
    the weighted argument principle on a disc, unconditionally: the power sums of the enclosed zeros
    are the weighted logarithmic-derivative contour integrals
PolynomialMinimumModulus.sum_multiplicity_mul_log_le
    a Jensen-free uniform bound on the total multiplicity in a ball
Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
circleIntegral.norm_integral_le_of_norm_le_const
    the two estimates that make the contour integral continuous under uniform convergence
```

Route: the count in a disc is `(2πi)⁻¹ ∮ logDeriv`, which is continuous in the function for the
uniform topology near the circle and integer-valued, hence locally constant; zeros of a nearby
function therefore stay in small discs around the zeros of the limit with the same total
multiplicity, which is exactly continuity of the pairing.

## Pass 93 — FIRST PROMOTION: `almost-periodic-autonomous-ade-finite-frequency-law` → stage 3

Both halves of the card are now single unconditional axiom-clean Lean theorems, and the card has
been moved to `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/`.

```text
rank_bohrSpectrum_le_of_strip_differential_equation        (4)
rank_bohrSpectrum_divisor_le_of_stripAnnihilator           (23)
rank_bohrSpectrum_observable_le_of_strip_differential_equation
rank_bohrHullFrequencies_le_of_strip_differential_equation
```

The divisor half required the **continuity of the Poincaré–Lelong divisor map** — the one classical
input the card cited as standard and the tree did not own.  It is now proved from the corpus's
factorization theory, with no new axioms:

```text
HTGeometry/ZeroDivisorCount.lean
    zeroMult, zeroMult_of_factorization, analyticOrderAt_finset_prod_pow
    exists_zeroSet_circleIntegral_logDeriv   the argument principle: ∮ f'/f = 2πi·(zero count)
    zeroSumBall, exists_nat_zeroSumBall
    exists_eps_norm_logDeriv_sub_le          Cauchy estimate ⟹ f'/f uniformly close on the circle
    exists_eps_zeroSumBall_eq                integer + continuous ⟹ the count is locally constant
HTGeometry/DivisorPairing.lean
    divisorPairing f φ = ∑ᶠ a, (order of f at a)·φ(a)
    finite_zeros_of_isCompact, exists_separating_radius, exists_local_zeroSet
    continuousAt_divisorPairing              the divisor pairing is continuous in the parameter
    divisorPairing_congr
HTGeometry/CarrierDivisorObservable.lean
    not_eventually_rep_eq_zero               no carrier representative vanishes identically
    continuous_divisorPairing_rep            the pairing is a continuous carrier observable
    eqOn_rep_bohrIota                        along the line it is the divisor of the translates
    rank_bohrSpectrum_divisor_le_of_stripAnnihilator
```

Reusable well beyond this card: the argument principle in the intrinsic form
"contour integral of the logarithmic derivative = total multiplicity of the enclosed zeros", the
local constancy of that count, and Hurwitz-type continuity of the zero divisor.

### Next target

`almost-periodic-implicit-ade-relative-frequency-law` — the nonautonomous/relative version of the
same theorem.  It needs, beyond what is now owned: the joint hull of the coefficient tuple and the
solution, the projection onto the coefficient hull, and the *relative* rank bound
`rank(Γ(a,f)/Γ(a)) ≤ 2m(n+1)` for the kernel of that projection.  The corpus already owns
`hasTotallyBoundedOrbit_prod` and the cube/character machinery
(`not_injOn_unitCube`, `card_le_of_hull_charts`); what is missing is the relative form of the cube
argument — a family of characters of the joint hull, independent modulo the coefficient hull's
characters, produces a cube inside the kernel.

## Pass 94 — the relative frequency-rank law (§4 of the implicit almost-periodic card)

The card's §4 replaces Pontryagin's exact sequence `0 → dual(A) → dual(X) → dual(K) → 0` and the
identity `dim K = rank dual(K)`.  Neither is needed: the *relative* rank bound follows from the same
cube argument as the absolute one, with the parameter subgroup arranged to land in the fibre.

```text
HTGeometry/RelativeFrequencyDual.lean
    exists_rat_linear_dual_general    an independent family of a ℚ-vector space extends to real
                                      coordinates
    exists_rat_linear_dual_rel        real coordinates killing a prescribed rational subspace
    exists_nsmul_mem_of_mem_span_rat  an element of the rational span of a subgroup has an integral
                                      multiple inside the subgroup
    linearIndependent_mkQ_of_int      hence ℤ-independence modulo a subgroup is ℚ-independence
                                      modulo its rational span
HTGeometry/RelativeHullChartRank.lean
    exists_continuous_hullParameter_of_dual
        the parameter subgroup attached to any ℚ-linear coordinate package, with its characters
        computed: bohrHullChar f γ (φ t) = exp(i ⟨v γ, t⟩)
    bohrHullKernel f W                the fibre: the points where every character from W is trivial
    exists_continuous_hullParameter_rel
        the relative parameter subgroup lies in the fibre
    card_le_of_hull_charts_rel        charts injective *only on the fibre* bound an independent
                                      packet modulo the subgroup
    card_le_of_int_independent_mod
    rank_quotient_bohrHullFrequencies_le_of_charts_rel
        rank_ℤ (Γ(f) ⧸ Γa) ≤ k
```

All unconditional and axiom-clean.  The mechanism: choose the `ℚ`-linear functional package to kill
the rational span of `Γa`; then every character of the parameter subgroup is trivial on `Γa`, so the
cube it sweeps out lies in the fibre — which is exactly the kernel of the projection onto the
coefficient carrier.  No bound on `Γa` itself enters, which is the card's attack #1 (an infinite
dimensional coefficient carrier is harmless).

### What the implicit card still needs

1. **A vector-valued carrier.**  The card's joint hull is the hull of the pair `(a, f)`, i.e. of an
   `ℝ →ᵇ (Fin m → ℂ)`.  The corpus's `BohrHull` and `BohrLine` are already general in the codomain,
   but `IsBohrHullFrequency`, `bohrHullChar`, `bohrHullFrequencies` and the four modules around them
   (`BohrHullCharacter`, `BohrHullFrequency`, `BohrHullSeparation`, `BohrHullCharRealization`,
   `BohrHullKroneckerHom`, `BohrHullDual`) are stated for `ℝ →ᵇ ℂ`.  None of their proofs uses the
   codomain's complex structure — only `bohrCoefficient` does — so the layer generalizes; 73 modules
   use those names, so the generalization must be done as new general declarations rather than an
   in-place edit.
2. **The nonautonomous implicit-function step.**  `StripJetSeparation.eqOn_of_line_jet_eq_implicit_local`
   is stated for a relation `P : (Fin (n+1) → ℂ) → ℂ` with no `z`; the relative card needs
   `P : ℂ × (Fin (n+1) → ℂ) → ℂ`, two solutions in the *same* fibre sharing the same coefficient.
3. The assembly, which is then the same shape as the autonomous card's.

## Pass 95 — the Bohr carrier layer is now valued in an arbitrary normed group

The implicit almost-periodic card needs the *joint* hull of the coefficient tuple and the solution,
i.e. the carrier of an `ℝ →ᵇ (Fin m → ℂ)`.  `BohrLine`, `BohrHull`, `bohrIota`, `bohrEval` and
`compactSpace_bohrHull` were already general; the character/frequency/duality layer was stated for
`ℝ →ᵇ ℂ` only.  None of its proofs uses the complex structure of the codomain — only the
`bohrCoefficient` bridge does — so the layer has been generalized in place:

```text
BohrHullCharacter        IsBohrHullFrequency, bohrHullChar, continuous_bohrHullChar,
                         bohrHullChar_add, bohrHullChar_zero, norm_bohrHullChar
                         (the two bohrCoefficient theorems keep ℂ, in their own section)
BohrHullPullback         dist_bohrIota, dist_add_bohrIota, norm_bohrEval_le, dist_bohrEval_le,
                         bohrHullBC, isBohrAlmostPeriodic_comp_bohrIota
BohrHullFrequency        isBohrHullFrequency_zero/neg/add, bohrHullFrequencies,
                         isBohrHullFrequency_of_uniformContinuous_compare, observableBC,
                         bohrSpectrum_observable_subset_bohrHullFrequencies
                         (bohrSpectrum_subset_bohrHullFrequencies keeps ℂ)
BohrHullCharCombination, BohrHullTorusQuotient, BohrHullKroneckerHom, BohrHullDual,
BohrHullSeparation, BohrHullCharRealization, BohrHullParameterSubgroup,
HullChartFrequencyRank, RelativeHullChartRank
```

`lake build GaloisForLFunctions.HTGeometry` succeeds after the change, so all 73 modules that use
`bohrHullChar` / `IsBohrHullFrequency` / `bohrHullFrequencies` are unaffected — the generalization is
source-compatible, the codomain being inferred from `f`.

In `HullChartFrequencyRank` and `RelativeHullChartRank` the codomain variable is `V`, not `E`,
because `E` is already the name of the chart family there.

### The implicit card's remaining obligation

Only the *nonautonomous* analytic layer is left:

```text
ODEJetSeparation      eq_of_jetVec_eq_at is stated for an autonomous field Φ : (Fin n → ℂ) → ℂ;
                      the relative card needs Φ : ℝ → (Fin n → ℂ) → ℂ, uniformly Lipschitz in the
                      jet, continuous in the time — mathlib's ODE uniqueness supports it
StripJetSeparation    the same for eqOn_of_line_jet_eq and eqOn_of_line_jet_eq_implicit_local
ImplicitLipschitzGraph  exists_lipschitz_implicit with a z-dependent relation
```

and then the assembly: the joint hull of `(a, f)`, the fibre `bohrHullKernel` over the coefficient
subgroup, and the charts of the fibre, fed to `rank_quotient_bohrHullFrequencies_le_of_charts_rel`.

## Pass 96 — the nonautonomous jet-separation layer

The implicit card's `(16)` solves a relation whose coefficients move with the point of the strip.  The
tree's separation layer was autonomous; it is now available with a time-dependent right-hand side,
unconditionally and axiom-clean:

```text
HTGeometry/ODEJetSeparationTimeDep.lean
    hasDerivAt_jetVec_timeDep
    jetVec_eq_of_eq_at_timeDep, eq_of_jetVec_eq_at_timeDep
    eventuallyEq_of_jetVec_eq_at_timeDep
HTGeometry/ImplicitLipschitzConst.lean
    implicitLipschitzConst n L C  = 2·((C + ∑_(k≠n) ‖∂_k L‖)·n / (‖∂_n L‖ − C))
    exists_lipschitz_implicit_const
        the implicit branch with its Lipschitz constant *named* — the constant depends only on the
        dominance datum, not on the relation, which is what makes a moving family of relations share
        one constant
HTGeometry/StripJetSeparationTimeDep.lean
    eqOn_of_line_jet_eq_timeDep
    eqOn_of_line_jet_eq_implicit_timeDep
        g, h holomorphic on the strip, both solving P t = 0 along the line inside one convex region
        on which one fixed functional dominates in the top jet, with equal jets of orders 0 … n−1 at
        one time  ⟹  EqOn g h on the strip
```

The point that makes this free: mathlib's `ODE_solution_unique_univ` is already stated for a
*nonautonomous* field `v : ℝ → E → E` and asks only for a Lipschitz bound at each time — no
regularity in the time whatsoever.  The corpus's autonomous version was using it with `fun _ => v`.

### What is left on the implicit card

The joint carrier and its fibre.  The relation is autonomous in the *composite* jet
`(a(z), f(z), f'(z), …, f^(n)(z))`, so the object to carry is the vector-valued
`F = (a_1, …, a_N, f)`, and `StripSolutionPhaseRank.exists_carrier_representatives` has to be
available for a vector-valued `F`.  On the fibre `bohrHullKernel p (span ℚ Γ(a))` the coefficient
component of every representative is `a` itself, so all the solutions there satisfy one and the same
nonautonomous relation `P_a` — which is exactly the hypothesis
`eqOn_of_line_jet_eq_implicit_timeDep` consumes.

## Pass 97 — the strip carrier layer is now valued in a complex Banach space

The implicit card's joint carrier is the hull of the *pair* `(a, f)`.  The relation is autonomous in
the composite jet `(a(z), f(z), …, f^(n)(z))`, so the object to carry is a `ℂ^(N+1)`-valued
holomorphic strip almost-periodic function.  The whole strip carrier construction has been
generalized in place from `ℂ → ℂ` to `ℂ → E`, `E` a complex Banach space:

```text
VerticalAlmostPeriodicDerivative   IsStripAlmostPeriodicOn, IsStripAlmostPeriodic,
                                   norm_deriv_sub_deriv_le_of_ball, isStripAlmostPeriodicOn_deriv,
                                   isStripAlmostPeriodic_deriv/_iteratedDeriv,
                                   isBohrAlmostPeriodic_line, continuous_line_restriction,
                                   exists_return_sequence_jets
StripAlmostPeriodicBounds          exists_bound_of_isStripAlmostPeriodicOn, exists_deriv_bound,
                                   exists_lipschitzOnWith_closedStrip, norm_translate_sub_le
StripThreeLinesTransfer            norm_sub_le_of_line_bound, exists_delta_strip_of_line
                                   (mathlib's Hadamard three-lines is already Banach-valued)
StripTranslateCurve                exists_strip_curve
LineJetTransfer                    differentiableOn_iteratedDeriv_verticalStrip,
                                   eqOn_of_eqOn_line, eqOn_of_eventuallyEq_line
                                   (the `I^k` twist lemmas stay scalar — they multiply by `I`)
JetSampleAtlas                     iteratedDeriv_sub_eqOn, norm_iteratedDeriv_sub_le
StripHullHolomorphic               differentiableOn_of_tendstoUniformlyOn,
                                   exists_translate_seq_of_hull, exists_holomorphic_of_hull
StripRelationPropagation           relation_of_tendstoLocallyUniformlyOn,
                                   relation_of_translate_limit, exists_solution_of_hull
LineStripCarrier                   dist_line_le_dist_strip, dist_strip_lt_of_dist_line_lt,
                                   exists_injective_line_to_strip
CarrierRepresentative              bohrEval_strip_line, exists_holomorphic_rep,
                                   norm_jet_sub_le_dist, continuous_jet_of_representatives
StripSolutionPhaseRank             exists_carrier_representatives
```

The separation theorems (`carrier_eq_of_jet_eq`, `rank_le_of_strip_solution`,
`rank_le_of_strip_jetAtlas`) stay scalar: they run a scalar ODE.  That is the right split — on the
fibre of the coefficient projection it is the *scalar* component that has to be separated, by the
nonautonomous implicit theorem of pass 96.

## Pass 98 — the fibre of the coefficient projection, and the relative assembly

```text
HTGeometry/HullComparisonMorphism.lean
    hullMap f g                       the comparison morphism of carriers attached to a uniformly
                                      continuous comparison of translation distances
    hullMap_bohrIota, hullMap_add, hullMap_zero, continuous_hullMap
    bohrHullChar_hullMap              characters pull back along it
    bohrEval_hullMap                  the evaluation commutes with it
    hullMap_eq_zero_of_char_eq_one    a point killed by every character of the target is in the
                                      kernel
HTGeometry/LinearJet.lean
    iteratedDeriv_clm_comp_eqOn       jets commute with a continuous linear map, hence the jets of a
                                      component are the components of the jets
HTGeometry/CarrierRepresentativeRel.lean
    carrier_eq_of_jet_eq_rel, carrier_eq_of_jet_eq_local_rel
HTGeometry/ImplicitRelativeFrequency.lean
    uniformContinuous_bohrLine_fst
    eqOn_rep_fst_of_mem_bohrHullKernel   on the fibre the coefficients return
    rank_quotient_le_of_regular_jets_rel rank_ℤ (Γ(p) ⧸ Γ(q)) ≤ 2n
```

## Pass 99 — the implicit card's relative law, assembled

Verified in scratch and built module by module (no umbrella builds):

```text
HTGeometry/LinearJet.lean                  iteratedDeriv_clm_comp_eqOn
HTGeometry/CoefficientJetRelation.lean     coeffJetRelation, frozenRelation,
                                           coeffJetRelation_jet_eq, contDiff_frozenRelation
HTGeometry/HullComparisonMorphism.lean     hullMap and its compatibilities
HTGeometry/CarrierRepresentativeRel.lean   carrier_eq_of_jet_eq_rel (+ local)
HTGeometry/RelativeHullChartRank.lean      isClosed_bohrHullKernel,
                                           exists_finite_closed_cover_subordinate_on,
                                           and the covering hypothesis of the relative chart bound
                                           weakened to the *fibre* — the cube lies there anyway
HTGeometry/ImplicitRelativeFrequency.lean  eqOn_rep_fst_of_mem_bohrHullKernel,
                                           rank_quotient_le_of_regular_jets_rel
HTGeometry/ImplicitStripFrequencyLaw.lean  rank_quotient_le_of_implicit_strip_solution
```

all unconditional and axiom-clean.  The capstone:

```text
0 < r, 0 < ρ, r + ρ < R,
Fv = (coefficients, solution) holomorphic and strip almost periodic on the strip,
p its line restriction, q the coefficient component of p,
0 < n, the joint relation vanishes along the jet of Fv on the strip,
convex regions S i on which one functional dominates the frozen relation in the top jet,
uniformly in the time, and every holomorphic solution of the frozen equation on the substrip having
its jet at some sample time inside the corresponding region
  ==>  rank_ℤ (Γ(p) ⧸ Γ(q)) ≤ 2n
```

Two design points that made it close:

* the *covering* hypothesis of the relative chart bound only has to hold on the fibre.  The
  parameter cube produced by `exists_continuous_hullParameter_rel` lies in the fibre, so the finite
  closed cover only has to cover the fibre — which is closed, hence compact.  That is what lets the
  atlas hypothesis speak about solutions of the *original* equation: off the fibre the coefficients
  are different and the equation is a different one.
* the equation is autonomous in the joint jet, so one carrier construction serves it; on the fibre
  `coeffJetRelation` collapses to `frozenRelation` with the original coefficients.

### Remaining on the implicit card

`hatlasSol` — the card's `(9)`/`(12)`: every holomorphic solution of the frozen equation on the
substrip has a regular jet at one of the sample times.  In the card this comes from minimality of the
joint hull (§2) plus Ritt's separant step for the coefficient field.  Both halves are owned in the
autonomous case (`exists_ne_zero_of_dense_translates`, `AutonomousStripSeparant`); what is left is
their nonautonomous analogues and the construction of the dominance regions from `(5)`.

## Pass 100 — SECOND PROMOTION: `almost-periodic-implicit-ade-relative-frequency-law` → stage 3

Both halves of the card are single unconditional axiom-clean Lean theorems, and the card has moved
to `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/other/`.

```text
rank_quotient_le_of_implicit_strip_separant          (7)/(8), with the atlas derived
rank_quotient_le_of_implicit_strip_separant_closed   the same with the orbit hypotheses derived
rank_quotient_divisor_le_of_implicit_strip_separant  (25)/(26)
```

New this pass:

```text
HTGeometry/FrozenRelationDominance.lean
    jetMonomial, fderiv_frozenRelation (linear in the coefficients),
    norm_fderiv_frozenRelation_sub_le,
    exists_time_dominant_nbhd   a convex region and a reference functional dominating the derivative
                                at every *nearby time*, not merely at the sample time
HTGeometry/JointSeparant.lean
    jointSeparant, jointSeparant_eq_sum, continuous_jointSeparant
HTGeometry/ImplicitCarrierRegularity.lean
    exists_joint_regular_time   minimality: no carrier point is everywhere singular
    rank_quotient_le_of_implicit_strip_separant(_closed)
    isBohrAlmostPeriodic_fst
HTGeometry/ImplicitDivisorFrequency.lean
    rank_quotient_le_of_le      relative rank is monotone along an inclusion of subgroups
    not_eventually_rep_snd_eq_zero, continuous_divisorPairing_rep_snd
    rank_quotient_divisor_le_of_implicit_strip_separant
```

Also: the covering hypothesis of `card_le_of_hull_charts_rel` and
`rank_quotient_bohrHullFrequencies_le_of_charts_rel` was weakened to the *fibre*
(`isClosed_bohrHullKernel`, `exists_finite_closed_cover_subordinate_on`), and the dominance
hypotheses of the time-dependent local separation were weakened to hold only near the sample time —
both are what make the atlas expressible in terms of the original equation.

Two cards are now at stage 3.  Eighteen non-`ccm` cards remain; the work queue at the top of this
file still describes them, with the correction that the covering-dimension / Pontryagin blocker
listed for `archimedean-relative-prime-cocycle-curvature` is now removed as well.

## Pass 101 — the Gauss card's convolution half is reduced to one lattice estimate

The open core of `gauss-component-quasi-inner-residue-hierarchy` is now a single explicit statement:

```text
T(s) = ∑_(r=1)^N 1/((1 + |s − r|) r^c)   ≤   C_c (1 + log N) (1 + |s|)^(−c)
```

which says a harmonic convolution keeps a power spike's exponent and multiplies its height by a
logarithm.  `HTGeometry/SpikeConvolutionKernel.lean` proves the far-side half
(`sum_harmonic_rpow_neg_le_of_nonpos`, by weighted AM–GM `a^c b^(1−c) ≤ a + b`); the band side is the
three-range split `r ≤ s/2`, `s/2 < r ≤ 2s`, `r > 2s`.

Why the sharp form is needed rather than the easy one is recorded on the card: the naive
`(1+|s|) ≤ (1+|s−r|)(1+r)` bound costs `N^c` instead of `log N`, which turns the iteration's
requirement `c < θ` into `2c < θ` and breaks the exponent ladder past `c = 1/2`.

## Pass 102 — two of the three band ranges

`RHTower/SpikeBandConvolution.lean` (unconditional, axiom-clean):

```text
band_low_le    r ≤ s/2:   (1+s)^c · ∑ 1/((1+|s−r|) r^c) ≤ 2 + 2/(1−c)
band_high_le   r > 2s:    (1+s)^c · ∑ 1/((1+|s−r|) r^c) ≤ 2 (1 + log N)
```

The middle range `s/2 < r ≤ 2s` — where the logarithm is produced — is the remaining piece: there
the weight is comparable to `(s/2)^(−c)` and the harmonic factor sums to `log s`, and non-emptiness
of the range forces `s < 2N`, which is what turns `log s` into `log N` in the final bound.

## Pass 103 — the lattice estimate is proved; the spike is closed under harmonic convolution

`RHTower/SpikeBandConvolution.lean`, all unconditional and axiom-clean:

```text
sum_harmonic_window_le   ∑_(r=1)^(2s) 1/(1 + |s − r|) ≤ 2 (1 + log s)
band_mid_le              s/2 < r ≤ 2s: (1+s)^c ∑ ... ≤ 8 (1 + log 2N)
sum_harmonic_rpow_neg_le      the three ranges combined
sum_harmonic_rpow_neg_le_int  the same at an arbitrary integer read point x
      ∑_(r=1)^N 1/((1 + |x − r|) r^c) ≤ (12 + 2/(1−c))(1 + log(2N+2)) / (1 + |x|)^c
sum_kernel_mul_spikeProfile_band_le
      a harmonic kernel maps spikeProfile B c n to spikeProfile (3K·spikeConvConst c N · B) c n
```

The window lemma is the mechanism: the involution `r ↦ s + 1 − r` on `[1, s]` and the shift
`r ↦ r − s` on `(s, 2s]` both turn the moving weight `1/(1 + |s − r|)` into the harmonic sum
`∑ 1/k`, so the logarithm is produced exactly once and the read frequency is pinned by
`s < 2N` — non-emptiness of the middle range.

This closes the convolution half of step 2 of the Gauss card in the spike direction.  What remains
there: the uniform half (the corpus owns `HarmonicPowerConvolution.tsum_harmonicPowConv_le`), the
assembled `TwoPieceAmplitude` closure statement, and the one-step estimate.

## Pass 104 — the Gauss two-piece class is closed under the symbol algebra

`RHTower/SpikeBandConvolution.lean`, `HTGeometry/HarmonicPowerConvolution.lean` and the new
`RHTower/GaussTwoPieceInvariance.lean`, all unconditional and axiom-clean:

```text
kernel_far_le, sum_kernel_mul_spikeProfile_far_le      the region beyond 4n
sum_kernel_mul_spikeProfile_two_piece_le               all three regions, any 0 < θ ≤ 1
summable_harmonicPowConv, tsum_harmonicPowConv_real_le the uniform half, in real form
bandRadius, spikeProfile_eq_zero_of_notMem, sum_Icc_symm_split
tsum_harmonic_two_piece_le                             the class closure as a tsum bound
TwoPieceAmplitude.mul_symbol                           the same at the operator level
```

The three regions of the spike transfer and why each is needed are recorded on the card (pass 51).
The load-bearing point is that the created bulk height carries the factor `n^θ`, which cancels the
`B ≍ A n^(−θ)` the class carries — so the constant is independent of `n`.

Step 2's first half (invariance of the class under every factor of `R̃_n`) is therefore complete;
what remains on the card is the one-step estimate and then the already-built telescope.

## Pass 105 — prime-wold §5.1 and §5.5 are Lean-proved

Two new modules and one extension, all unconditional and axiom-clean:

```text
RHTower/AcceleratedWoldType.lean      tendsto_mertensProduct_mul_ell2_expGauge   (§5.1)
RHTower/AdelicIntertwinerSaturation.lean   the local algebra of λ_p(z) = (pz²−1)/(p−z²)
RHTower/AdelicIntertwinerType.lean         the PNT bridge and the saturation conclusion (§5.5)
```

Two things worth keeping.  The equality locus `‖λ_p(z)‖ = 1 ⟺ ‖z‖ = 1` follows from the exact
identity `‖pz²−1‖² − ‖p−z²‖² = (p²−1)(‖z‖⁴−1)` with no estimate at all.  And
`tendsto_sum_primesBelow_log_div` — `(∑_{p<N} log p)/N → 1` in the `Nat.primesBelow` convention the
Wold modules use — is the bridge from `PNTPlus.chebyshev_asymptotic_finsum`; it is reusable wherever
a `primesBelow` sum needs the prime number theorem.

Remaining on that card: §5.2's restatement, §5.3 (needs the corpus law `log B_x(c) = (|c|+o(1))ϑ(x)`),
§5.4's Sonin depth matching, and §6's dictionary.

## Pass 106 — prime-wold §5.2 and §5.3

```text
RHTower/AcceleratedWoldType.exp_exp_le_of_mul_ell2_ge        (17) in exact form
RHTower/PrimeSquareScalarCompression.lean                    the whole of §5.3, and with it
    (7), (8), (11), (12), (13) of the parent card
    prime-square-deformed-reflection-line-superessential-fracture
```

The reusable pieces: `one_le_scalarCompressionRatio` / `scalarCompressionRatio_eq_one_iff` are a
plain-real critical-line reporter (`N² − D² = P(P−1)x(x−2)` with `x = r + r⁻¹`), and
`abs_log_scalarCompressionRatio_sub_log_le` is the two-rate local expansion — `O(u⁻¹)` from the
numerator, `O(u²/P)` from the denominator — which is the shape every Euler-type local coefficient
on this lane has.

Also: splitting a long `nlinarith`/`field_simp` proof into named lemmas is what fixed the heartbeat
overrun here; the whole-declaration budget, not any single tactic, was the binding constraint.

## Pass 107 — prime-wold §5.4 and §6

```text
RHTower/SoninDepthMatching.lean            (18a)–(18e); the floor estimate is the whole content
RHTower/AdelicIntertwinerType.lean         (21a) the ϑ-normalized Weyl rate, and
                                           modularCharge_dictionary  (21), (21b), (21c)
```

Sections 2, 3, 4, 5.2, 5.3, 5.4, 5.5, 6 and 7 of that card are now Lean-proved; §5.1's pointwise
statement is proved and only its compact-uniform version `(14a)`–`(14c)` is open, together with the
two dictionary inputs `(19)`, `(20)` which belong to parent cards.

## Pass 108 — prime-wold §5.1 compact-uniform; the card's own sections are complete

`RHTower/AcceleratedWoldType.log_max_gauge_le` and
`tendsto_mertensProduct_mul_ell2_zero_of_log_gauge_le` close `(14a)`–`(14c)` in the form that takes
the parent's normal-convergence bound as its hypothesis.

Every section of `prime-wold-accelerated-type-modular-drift-law` that the card proves itself is now
Lean-proved.  The four remaining inputs — `(14a)`, `(18c)`, `(19)`, `(20)` — are parent-card or
literature theorems, each appearing as an explicit hypothesis of the theorem that uses it, never as
an axiom.  Deciding whether that is enough for stage 3 is the next judgement on this card: the
honest reading is that it is not, because `(19)` and `(20)` are corpus theorems that could be
formalized, and the card's headline `(21)` depends on them.

## Pass 109 — prime-wold's dictionary inputs were already in the tree

`(19)` and `(20)` did not need new mathematics: `log_norm_shellTransferCharacter` and
`re_centeredXiAffineResidue_eq_shellTransferEntropy` are exactly them.  `RHTower/ModularChargeFourCharts.lean`
assembles `shellReflectionRate_eq` and the two dictionary corollaries.

Lesson repeated: search the tree for the *content* of a cited input before treating it as external.
The card cited `(19)`/`(20)` to publication-ready preprints; both were already formalized under
different names.

## Pass 110 — prime-wold `(14b)`–`(14c)` on the tree's own objects

`RHTower/WoldGaugeCompactUniform.lean` instantiates the abstract gauge bound at
`finitePrimeGenusOnePolarizedPhase`, using the corpus's exact irregular-gauge factorization and the
reflection identity.  The card's only remaining inputs are `(14a)` (normal convergence of the
genus-one occupation product — a bound on the *raw* phase, uniform on compacts) and `(18c)`
(Burnol–Sonin aperture rigidity); both now appear as hypotheses of the exact theorems that consume
them, on the tree's own objects.

## Pass 111 — dyadic-fermion `(14)` and `(16)`

```text
HTGeometry/ParityDigitAffinityExpansion.lean   the exact first-order cancellation
                                               s − a/2 − b/2 = −½(√a − √b)²
RHTower/CriticalPrimeProfileSum.lean           the critical sum as a Mertens prime window
```

The reusable discovery: `RHTower.tendsto_mertensPrimeWindow_div_log` is weak convergence of the
prime log-density measure to Lebesgue measure on `[0,1]`, so *every* weighted prime Cesàro law of
the form `∑_{p ≤ x} g(log p/log x)/p → ∫₀¹ g` is a one-line corollary once `g` is continuous on the
closed unit interval.  That is what replaces the card's `(15)` partial-summation argument entirely.

## Pass 112 — the Manin-horizon and active-palette cards

Both are closed and promoted to Stage 3.

`abelian-multiplication-tail-manin-horizon`.  The whole chain `(2)`--`(9)` is Lean-proved.  New
modules: `AffineZariskiClosureOver` (a full affine Zariski closure operator over a coefficient
ring, mirroring the Kolchin one: Galois connection, universal property, idempotence, arbitrary
intersections, finite unions, and `ZariskiDenseOver` with its monotonicity),
`ManinKernelKolchinClosure` (the closure of a Zariski-dense torsion tower is the Manin kernel, in
set and subgroup form; the constant-point locus is Kolchin closed, which is Corollary D),
`ManinMapQuotientCoordinates` (translation fixed fields are derivation-closed, so invariant
coordinates generate a differential subfield of them; a map whose fibres are the orbits detects
exactly the invariant functions), `AbelianTailUniversalScaling` (integer rescaling of a
differentially independent palette, the canonical `v ↦ m v` automorphism, and its naturality —
the no-hair theorem), `AbelianManinHorizonNoHair`, `AbelianManinHorizonTheorem`,
`AbelianVarietyMultiplicationGaloisLevel` (each multiplication level is the torsion deck fixed
field, from the degree data), and `AbelianVarietyManinHorizonTail` (the end-to-end statement on
the actual function field of an Abelian variety).

The reusable discovery: the free differential parametrisation
`differentialIndependentAdjoinAlgEquiv` already in the tree makes *any* "dynamics on a free
differential field is universal" argument a two-line naturality check — build the endomorphism by
conjugating the labelled equivalence, and prove intertwining by `IntermediateField.adjoin_algHom_ext`
on jets.  `differentialAdjoin_range_zsmul` is the only extra ingredient, and its content is just
that a nonzero base scalar is invertible.

`active-quasi-abelian-palette-exact-ht-dimension-classification`.  New modules:
`ActiveQuotientSplitModel` (the ambient-faithfulness conjecture is false, with a concrete witness
in the group underlying `E × ℂ*`, plus the split-model capacity spectrum),
`ActiveQuasiAbelianPaletteHierarchy` (`qaDim ≤ aqaDim` as an actual forgetful construction, not a
hypothesis), and `ToruslessActiveCollapse`.

The reusable discovery: the separation question `qaDim < aqaDim` is now *only* about compact
shadows.  On a facet presentation with trivial compact shadow the active quotient is injective, so
the active condition is equivalent to plain faithfulness; the periodic-pencil quotient `ℂ*` is
torusless, so the two invariants agree on the whole pencil class.  A separating complex must have
*every* minimal quasi-Abelian palette carrying a positive-dimensional compact facet subtorus that
meets the facet lattice.

## 2026-08-18 pass — the CCM unit-Riesz cluster is closed

The seven `ccm-*` cards left in `2-fully-proven/new_scientific_knowledge/other` are now all at
stage 3:

```text
ccm-unit-riesz-exponential-coherent-trace            (already complete; audited)
ccm-unit-riesz-hankel-boundary-pulse                 (already complete; audited)
ccm-unit-riesz-suzuki-green-producer-classification  (already complete; audited)
ccm-unit-riesz-coherent-polar-sampling-no-go         + CCMUnitRieszCoherentGeneratorSampling
ccm-unit-riesz-aperture-resolvent-weld               + CCMUnitRieszApertureResolventEpsilonTransfer
ccm-four-unit-cesaro-curvature-wall                  + CCMUnitRieszCesaroFiniteApertureReporter
ccm-unit-riesz-completed-source-stieltjes-weld       + CCMUnitRieszVolterraLaplace,
                                                       CCMUnitRieszStirlingLaplace,
                                                       CCMUnitRieszCompletedCurrentLaplace,
                                                       CCMUnitRieszCompletedSourceLaplaceWeld
```

Programme card with the full audit and the reusable-asset list:
`1-in-progress/ccm-unit-riesz-cluster-stage3-closure.md`.

Two lessons worth keeping.

1. *Three of the seven cards were already fully formalized.*  The audit that established this — read
   the card's numbered equations, dump every `theorem` signature in the named module, match them
   one by one — took a fraction of the time the formalization of the remaining four did.  Do it
   first, always.
2. *A "measure-valued Laplace identity" is usually not one.*  The completed-source weld card
   flagged `(26)` as possibly needing Bochner/Stieltjes--Laplace infrastructure.  It does not: both
   kernels in the weld are finite combinations of pure decaying exponentials, so the whole identity
   follows from one exponential-kernel convolution law
   (`integral_Ioi_expVolterra_laplace`) proved by a single Fubini interchange over the causal
   wedge.  Before importing measure-theoretic machinery, check whether the kernel is elementary.

- 2026-08-18 — `prime-wold-accelerated-type-modular-drift-law` closed and promoted to stage 3.  The
  two remaining inputs were discharged, not assumed: `(14a)` is now
  `RHTower/GenusOneOccupationCompactBound.lean`'s
  `norm_finitePrimeGenusOnePolarizedPhase_two_sided` — an explicit two-sided bound on the
  tangent-normalized reflected occupation phase on `‖t‖ ≤ R`, `dist(t, ±ℕ_{≥1}) ≥ δ`, *uniform in
  the finite prime aperture*, obtained from the cubic vanishing of the reflected primary-factor log
  defect and the reciprocal-cube mass of the smooth-index injection; and `(18c)` is the tree's own
  cross-aperture rigidity, so `RHTower/SoninDepthApertureRigidity.lean`'s
  `norm_burnolExtendedSoninEvaluationVector_soninDepth_bounds` gives `(18e)` with no hypothesis.
  Both modules are axiom-clean and wired into `GaloisForLFunctions.RHTower`.

- 2026-08-18 — `gauss-component-quasi-inner-residue-hierarchy` advanced substantially, **not yet
  closed**. Formalized unconditionally and axiom-clean (`[propext, Classical.choice, Quot.sound]`),
  all umbrella-wired: nine new modules
  (`HTGeometry/FourierInnerCoefficientBound`, `RHTower/GaussSpikeDefectBand`,
  `RHTower/GaussPairingDefect`, `RHTower/GaussClassStep`, `RHTower/GaussPairingOneStep`,
  `RHTower/GaussRelativeIterate`, `RHTower/GaussRelativePower`,
  `RHTower/GaussConjugationSymmetry`, `RHTower/GaussIterateLogResidue`) closing the card's named
  Lean gap — the operator-theoretic identification `⟨G^m e_n, e_n⟩ → gaussPrincipalDiagonalTerm`
  — at every `m`, and with it equation (11) in *relative* form, equation (14) for the operator, and
  formula (A) at the diagonal level:
  `tendsto_gaussLocalDiagonal_pow_logResidue (2 ≤ m) → gaussChannelResidue m p`.
  Corrections recorded on the card: the earlier `m ≥ 2` plan (an `L²` one-step estimate on the
  two-piece class, hence a generalization of (T)) targets a **false** statement; the correct object
  is the *pairing*, which removes every operator norm of a normalized shifted block. The card's
  own "Formalized" table over-credited §6: the weak-Schatten theorems there are about a
  realization, not about `G^m`.
  Remaining for closure: §6's Lord–Sukochev–Zanin diagonal formula for weakly modulated operators
  (one half — Schur–Horn majorization — is free), and §1's Connes–Consani source reduction.

- 2026-08-18 — `prime-valuation-dyadic-fermion-normal-cone-law` closed and promoted to stage 3.
  Every theorem the card states is now unconditional Lean.  New modules:
  `HTGeometry/GeometricHellingerExpansion.lean` (the geometric affinity has the parity digit's
  quadratic expansion, which is why `(12)` holds), `HTGeometry/DyadicFisherDecomposition.lean`
  (`(20)`, telescoping), `RHTower/PrimeProfileWindowLimit.lean` (reusable: Mertens window at a
  profile quotient, Tannery on the growing prime window, product-from-log-sum),
  `RHTower/SquarefreeCriticalNormalCone.lean` (`(11)`, `(12)`, `(13)`, `(13b)`, `(22)`),
  `RHTower/CoherentKernelChart.lean` (`(13c)`–`(13f)`: the kernel is the exponential of a Gram
  kernel, hence positive definite via Schur), `RHTower/PrimeProfileFockLimit.lean` (`(13s)`,
  `(13z)`), `RHTower/CriticalDefectMeasure.lean` (`(13aa)`–`(13ac)`),
  `RHTower/CoherentEscapeEnds.lean` (`(13g)`–`(13i)` and the rapid end),
  `RHTower/HalfNormalCoherentBoundary.lean` (`(13j)`–`(13n)`),
  `RHTower/WoldNormalScale.lean` (`(17)`), `RHTower/HellingerCurvature.lean` (`(18)`, `(19)`),
  `RHTower/DyadicEulerTelescope.lean` (`(23)`–`(27)`),
  `RHTower/EulerMascheroniExponentialIntegral.lean` (new analytic asset: `∫₀^∞ e^{-t} log t = -γ`
  and the Frullani representation `γ = ∫₀¹(1-e^{-t})dt/t - ∫₁^∞ e^{-t}dt/t`, hence
  `Ein(a) - log a → γ`), `RHTower/HalfNormalExactScale.lean` (`(13o)`).  All axiom-clean and
  umbrella-wired.

- 2026-08-18 — `prime-modulated-weyl-idealizer-collapse-on-xi-sampling` advanced, **not** promoted.
  `RHTower/XiSamplingIdealizerCollapse.lean` assembles `(23)` as a one-line instantiation of
  Theorem A at the tree's own `locallyFiniteSamples_xiRealDivisor` and `symmetric_xiRealDivisor`,
  so the whole of §4 is reduced to the single hypothesis `SuperlinearSamples xiRealDivisor`; and it
  turns §7.1 and §7.2 from remarks into constructions — `preservesSamplingIdeal_singleton_firstOrder`
  (a finite sampling set does not collapse) and `preservesSamplingIdeal_lattice_shift` together with
  `not_superlinearSamples_lattice` (a linear-density lattice is locally finite and symmetric but not
  superlinear, and its period shift preserves the sampling ideal).  The sharpness is therefore
  Lean-proved: superlinearity cannot be weakened to Hardy–Littlewood's `N_0(T) ≫ T`.
  **Two named classical theorems remain, neither owned by mathlib nor by this tree:**
  (i) Selberg's positive-proportion theorem in the form `SuperlinearSamples xiRealDivisor`
  (Hardy's theorem *is* owned, as `RHTower.exists_Xi_zero_gt`, and is not enough);
  (ii) the Schwartz-kernel plus Bochner–Schwartz representation of a jointly continuous positive
  translation-invariant sesquilinear form on `Schwartz(ℝ)` by a positive tempered measure, needed
  for §5's `(27)`.  Everything on both sides of each is formalized.

### 2026-08-18 — `prime-modulated-weyl-idealizer-collapse-on-xi-sampling`: section 5 closed, section 4 reduced

- **Section 5 `(27)`–`(31)`: CLOSED unconditionally.**  New module
  `formal/GaloisForLFunctions/RHTower/TwoDilationSpectralRepresentation.lean`.  The tree already
  owned Bochner–Schwartz in the Schwartz-form category
  (`HTGeometry/SchwartzPositiveMeasureRepresentation.lean`) and the whole theta-null classification
  (`RHTower/HedenmalmUniversalPositiveFormClassification.lean`); the genuinely missing step was
  `momentumSymmetric_of_two_dilation_invariance` — two multiplicatively independent integer
  dilations force momentum symmetry, via differentiability of the translation orbit plus density of
  the two-generator period group.  Capstones at the actual Hedenmalm theta source:
  `existsUnique_temperateSpectralRepresentation_supported_realDivisor_of_two_dilation`,
  `canonicalMeasure_atomic_of_two_dilation`,
  `exists_temperateSpectralRepresentation_theta_carried_by_xiRealDivisor`.  Axiom-clean.
- **Section 4 `(22)`: NOT closed; reduced to one analytic `Prop`.**  New modules
  `HTGeometry/GridCancellationZeroCount.lean` and `RHTower/XiSuperlinearFromCancellation.lean`
  prove `GridCancellationSurplus f → SuperlinearSamples xiRealDivisor` for any continuous `f` whose
  zeros are `Xi`-zeros, plus the clamped variant in which the per-cell bound is automatic, plus
  `(23)` with the Selberg citation replaced by that `Prop`.  The remaining analytic core, the ruled
  out routes and the identification of the single crux (the mollified second moment
  `∫_T^{2T}|ζM|² ≪ T`) are in
  `docs/drafts/pipeline/1-in-progress/selberg-superlinear-xi-density-programme.md`.
- **Card status:** stays in `2-fully-proven`.  Sections 1–3, 5–7 are Lean-certified; section 4's
  `(22)` is the one open item.

## 2026-08-18 (second entry) — `gauss-component-quasi-inner-residue-hierarchy` section 6 closed

Section 6 (equation (15)) is now Lean-certified for the **actual** operator, replacing the paper's
appeal to the Lord–Sukochev–Zanin eigenvalue comparison theorem for weakly `V_0`-modulated operators
by an elementary two-scale compression argument.

New modules (all `lake build` green, `#print axioms` = `[propext, Classical.choice, Quot.sound]`,
all wired into `GaloisForLFunctions/RHTower.lean`):

| module | content |
|---|---|
| `RHTower/PositiveOperatorDiagonalResidue.lean` | `sum_singVal_le_diagonal_add_tail`: `∑_{n<N} s_n(T) ≤ ∑_{j∈S}⟨b_j,T b_j⟩ + √(2N)·E_S` |
| `RHTower/SingularValueLogMean.lean` | `tendsto_sum_singVal_div_log_of_diagonal`: band diagonal log-mean + column decay `≲|n|^{-1+δ}` ⟹ singular-value log-mean |
| `RHTower/GaussTwoPieceL2Bound.lean` | `norm_sq_le_of_twoPieceAmplitude`: Parseval from the two-piece amplitude class |
| `RHTower/GaussIterateNormBound.lean` | `exists_gaussClass_principalStepInner`, `exists_norm_gaussPrincipalStep_pow_le`: `‖R_I^m 1‖ ≤ C(1+I)^ρ` for every `ρ>0` |
| `RHTower/GaussColumnDecay.lean` | `exists_norm_gaussQuasiInnerG_pow_fourierLp_le`: `‖G^m e_n‖ ≤ C|n|^{-1+ρ}` |
| `RHTower/GaussChannelOperator.lean` | `gaussChannelOperator`, `tendsto_sum_singVal_gaussChannelOperator`, `isDixmier_gaussChannelOperator`, `hasSchattenLogResidue_gaussChannelOperator` |

The key unlock was noticing that the outermost factor of `R_n = B S B^{-2} S* B` is a *bounded
multiplication operator*, so only the inner four factors need the tied class — and those obey the
weaker constraint `c + 1/(2m) < 1`, which the `(m-1)`-st iterate satisfies.

Card status: section 1 (the Connes–Consani one-prime Hankel decomposition) remains a **cited
classical input**, as declared in the card's own "Source boundary".  Everything the card adds over
that source is now Lean-certified.

### Remaining across the four `other` cards

* `gauss-component-quasi-inner-residue-hierarchy` — §1 Connes–Consani source reduction (cited).
* `torusless-quasi-abelian-fixed-factor-all-order-jet-ampleness` — the growth stability lemma
  (`AbePositiveFactorPresentation.gaussianMajorant`), the damped packet lift
  (`AbeDampedFactorExtension.liftPacket`), and Abe's structure theory (`IsAbePositiveTorusless`).
  The first of these needs exponential-type bounds for `complexIntegerSinc` and
  `integerTranslateSine` — the separator data is currently obtained by choice and carries no growth
  clause, so the clause has to be added to `FlatIntegerLatticePacketSeparatorData` and proved for
  the explicit sinc/sine construction.
* `finite-archimedean-gamma-product-boundary-law` and
  `archimedean-relative-prime-cocycle-curvature` — the shared blocker is the all-orders
  Stirling/transseries model injecting the shifted-Gamma jet field into `ℂ(log s)((s^{-1}))[Γ^{±1}]`.

## 2026-08-18 (third entry) — `torusless-quasi-abelian-…-jet-ampleness`: the analytic layer is closed

New/extended modules (each `lake env lean`-checked, single-module `lake build`, wired into
`GaloisForLFunctions/HTGeometry.lean`; `#print axioms` = `[propext, Classical.choice, Quot.sound]`):

| module | content |
|---|---|
| `HTGeometry/MultivariateEntireStripBound.lean` (new) | `StripBoundedOne`/`StripBounded` + closure package + `norm_complexSin_le_exp_abs_im` |
| `HTGeometry/QuasiAbelianIntegerLatticeSeparator.lean` (extended) | strip bounds for sinc/sine; `StripBounded` clause added to both separator existence theorems and to `FlatIntegerLatticePacketSeparatorData` |
| `HTGeometry/QuasiAbelianGaussianLatticeDecay.lean` (new) | `‖G(x+k)‖ ≤ C·exp(−∑σᵢkᵢ²/2)` |
| `HTGeometry/QuasiAbelianPolynomialLatticeGrowth.lean` (new) | `‖P(x+k)‖ ≤ C·∏(1+\|kᵢ\|)^{degᵢP}` |
| `HTGeometry/QuasiAbelianGaussianFlatSeed.lean` (extended) | `damping_eq` field |
| `HTGeometry/QuasiAbelianFlatSeedLatticeBound.lean` (new) | the seed half of the majorant, **unconditional** |
| `HTGeometry/QuasiAbelianAbePositivityReduction.lean` (new) | `HasLatticeExponentialGrowth`, `gaussianMajorant_of_…`, `abePositiveFactorPresentationOfGrowth`, `jetAmpleEveryFiniteOrder_of_hasLatticeExponentialGrowth` |

The blocker found and removed: the separator was produced by `Classical.choice` with **no growth
clause at all**, so no majorant could ever be proved about it.  The correct clause is a *strip*
bound (the lattice is real), not exponential type.

Card status: the analytic layer of the growth stability lemma is closed and the rank-zero base case
now follows from a checkable growth condition.  Open: `liftPacket` (induction step) and
`IsAbePositiveTorusless` (Abe's structure theory).

## 2026-08-18 — cards A/B: the blocker localized, and the corpus assets that will build it

`finite-archimedean-gamma-product-boundary-law` and `archimedean-relative-prime-cocycle-curvature`
share exactly one open analytic input: the **sectorial all-orders Stirling expansion of `log Γ`
with remainder**, and the resulting injection of the shifted-Gamma differential field into
`ℂ(log s)((s^{-1}))[Γ^{±1}]` ("no flat cancellation in the archimedean residue field").

Why the existing single-pole arguments do not extend: the product `G(s) = e^{αs}∏Γ(λ_j s + μ_j)`
has *commensurable* scales `n_j = Hλ_j ∈ ℕ`, so every shift lies in one arithmetic progression and
integer relations are everywhere — the opposite of the `NoIntegerRelation` hypothesis the current
boundary-datum theorem assumes.  Separating monomials therefore needs the full Stirling signature

```text
log ∏_j Γ(λ_j s + μ_j)^{n_j}
  = (∑ n_j λ_j) s log s + (∑ n_j λ_j (log λ_j − 1)) s + (∑ n_j (μ_j − ½)) log s + c + O(1/s),
```

whose three leading data separate distinct exponent vectors.

Corpus assets to build on (searched, not to be duplicated):
* `HTGeometry/AsymptoticExpansionAlgebra.lean` — `IsAsymptoticExpansion` with `.add`, `.mul`,
  `isBigO_one`; `HTGeometry/AsymptoticPolynomialCoefficients.lean`.
* `RHTower/BarnesCanonicalProductExpansion.lean` + `RHTower/BarnesTailAsymptoticExpansion.lean` —
  a working Mellin–Barnes contour ladder producing descending expansions at `+∞` with
  `x^{-(J+1/2)}` remainders. This is the engine to reuse for the Stirling ladder.
* `HTGeometry/DigammaAsymptotic.lean`, `DigammaBounds.lean`, `DigammaValuationBoundary.lean`,
  `GammaProjectiveBoundary.lean` — the vertical digamma/polygamma asymptotics, including
  `re_digamma_vertical_bound_uncond` and the Bell identity for `Γ^{(n)}/Γ`.
* Already Lean and downstream of the blocker: the Bohr-rank law
  (`AutonomousCarrierRegularity`, `StripSolutionPhaseRankSharp`), the divisor observable
  (`CarrierDivisorObservable`), and `finiteProjectiveRelationCollapse`.

Next concrete brick: `log Γ(z) = (z − ½) log z − z + ½ log 2π + O(1/|z|)` on a sector, then the
Bernoulli ladder on top of it via the Barnes contour engine.

## 2026-08-18 (fourth entry) — cards A/B: the Stirling ladder is started

`HTGeometry/GammaStirlingCubicLog.lean` (new, wired, `#print axioms` clean) is the first brick of
the sectorial Stirling expansion that cards A and B share.

**Design decision.** The cards do *not* need `log Γ` or the constant `½ log 2π`: the three data that
separate monomials of `e^{αs} s^β (log s)^γ ∏_j Γ(λ_j s + μ_j)^{n_j}` are all visible in the
*logarithmic derivative*

```text
G'/G(s) = α + (∑ n_j λ_j) log s + ∑ n_j λ_j log λ_j
            + [β + ∑ n_j (μ_j − ½)] / s + O(s^{-2}),
```

so the whole argument stays inside the differential field and needs only
`ψ(z) = log z − 1/(2z) + O(|z|^{-2})`.  That removes the branch-of-`log Γ` layer entirely.

Landed:
- `norm_log_one_add_sub_taylor_two_le` — `‖log(1+u) − u + u²/2‖ ≤ ‖u‖³` on `‖u‖ ≤ ½`, from
  mathlib's `Complex.hasSum_taylorSeries_log` by dropping three terms and summing the geometric
  tail.  (mathlib only has the *quadratic* bound `norm_log_one_add_sub_self_le`.)
- `log_add_one_sub_log` — `log(z+1) − log z = log(1 + 1/z)` on the right half-plane, via
  `Complex.log_mul_eq_add_log_iff` and the `|arg| < π/2` bound on both factors.
- `digammaStirlingDefect z = ψ(z) − log z + 1/(2z)`, and
  `digammaStirlingDefect_step`: the functional equation `ψ(z+1) = ψ(z) + 1/z` turns into
  `g(z+1) − g(z) = 1/z − log(1+1/z) − 1/(2z(z+1))`.
- `norm_digammaStirlingDefect_step_le` — **the cubic gain**: `‖g(z+1) − g(z)‖ ≤ 2/‖z‖³` for
  `Re z > 0`, `‖z‖ ≥ 2`.  The quadratic parts of the two terms cancel exactly; this one order of
  gain is what makes the telescoping series converge.

Next: telescope `g(z) = −∑_{k≥0}(g(z+k+1) − g(z+k))` using the vanishing anchor
`g(z+n) → 0` (the corpus's `digamma_vertical_anchor_tendsto` /
`digamma_natCast_add_one_sub_log_tendsto` supply it), and sum `∑_k ‖z+k‖^{-3} = O(‖z‖^{-2})` to
obtain `ψ(z) = log z − 1/(2z) + O(|z|^{-2})`.  Then the monomial-signature separation of §5.

## 2026-08-18 (fifth entry) — cards A/B: the digamma anchor

`HTGeometry/GammaDigammaShiftAnchor.lean` (new, wired, axioms clean) supplies the second Stirling
brick, the one that makes the telescope converge to **zero** rather than to an unknown constant.

The observation that makes it cheap: Gauss's formula `ψ(s) = lim_n (log n − ∑_{j≤n} 1/(s+j))`
carries the `log n` *independently of `s`*, so the divergent part cancels in a difference and

```text
ψ(s) − ψ(t) = lim_n ∑_{j≤n} (1/(t+j) − 1/(s+j)),  summand = (s−t)/((s+j)(t+j)).
```

- `sum_inv_mul_succ_le` — `∑_{j≤n} 1/((N+j)(N+j+1)) ≤ 1/N`, by the exact telescope
  `= 1/N − 1/(N+m)`.
- `norm_digamma_shift_sub_le` — **the anchor**: for `Re z ≥ 0` and `N ≥ 1`,

```text
‖ψ(z+N) − ψ(1+N)‖ ≤ ‖z−1‖ / N.
```

Both `gauss_digamma` (corpus, `RHTower`, in `DigammaAsymptotic`) and
`digamma_natCast_add_one_sub_log_tendsto` were reused rather than rebuilt.

Remaining for `ψ(z) = log z − 1/(2z) + O(|z|^{-2})`: assemble the telescope
`g(z) = g(z+N) − ∑_{k<N} (g(z+k+1) − g(z+k))` with the cubic gain
(`norm_digammaStirlingDefect_step_le`) and the anchor above, using
`‖z+k‖³ ≥ ‖z‖(‖z‖+k)²/2` and `∑_k 1/(‖z‖+k)² ≤ 1/‖z‖² + 1/‖z‖`.

## 2026-08-18 (sixth entry) — cards A/B: **the shared analytic blocker is closed**

`HTGeometry/GammaDigammaStirlingBound.lean` (new, wired, axioms clean) completes the Stirling input
that `finite-archimedean-gamma-product-boundary-law` and
`archimedean-relative-prime-cocycle-curvature` share:

```lean
theorem norm_digammaStirlingDefect_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖ψ z - log z + 1/(2z)‖ ≤ 6 / ‖z‖ ^ 2
```

i.e. **`ψ(z) = log z − 1/(2z) + O(|z|⁻²)` on the right half-plane, with an explicit constant.**

The three ingredients, all built here:
- `sum_inv_sq_shift_le` / `sum_inv_sq_shift_head_le` — `∑_{k<N} (a+k)⁻² ≤ a⁻² + a⁻¹`, by the exact
  telescope `(a+k)⁻¹ − (a+k+1)⁻¹`.
- `norm_le_norm_add_natCast`, `norm_add_natCast_cube_ge` — on the right half-plane
  `‖z+k‖² ≥ ‖z‖² + k²`, hence `‖z+k‖³ ≥ ‖z‖(‖z‖+k)²/2`.
- `log_sub_log_of_re_pos`, `tendsto_digammaStirlingDefect_shift_zero` — the anchor: the shifted
  defect vanishes, decomposed as (digamma shift) + (integer anchor) − (log quotient) + (1/2z), the
  four pieces going to zero by `norm_digamma_shift_sub_le`,
  `RHTower.digamma_natCast_add_one_sub_log_tendsto`, continuity of `log` at `1`, and `1/‖z+N‖ ≤ 1/N`.

Then the telescope `g(z+N) − g(z) = ∑_{k<N}(g(z+k+1) − g(z+k))` with the cubic gain, and `N → ∞`.

**No `log Γ` branch, no Binet integral, no Bernoulli numbers, no `½log 2π`** — the design decision
recorded in the fourth entry (work with `G'/G` rather than `log G`) removed all of that.

What cards A and B now need is no longer analytic: it is the §5 *signature separation*, i.e. that
the three data

```text
(∑ n_j λ_j,   ∑ n_j λ_j log λ_j + α,   β + ∑ n_j (μ_j − ½))
```

read off from `G'/G = α + (∑n_jλ_j) log s + ∑n_jλ_j logλ_j + [β+∑n_j(μ_j−½)]/s + O(s^{-2})`
separate distinct exponent vectors — an arithmetic statement about the shift data, now that the
expansion producing those data is Lean-certified.

## 2026-08-18 (seventh entry) — cards A/B: the affine Stirling signature

`HTGeometry/GammaAffineStirlingSignature.lean` (new, wired, axioms clean) delivers the expansion in
the exact form §5 of `finite-archimedean-gamma-product-boundary-law` consumes:

```lean
theorem exists_norm_digamma_affine_expansion_le {lam : ℝ} (hlam : 0 < lam) (mu : ℂ) :
    ∃ C R, 0 ≤ C ∧ 0 ≤ R ∧ ∀ s, 0 < s.re → 0 < (lam * s + mu).re → R ≤ ‖s‖ →
      ‖ψ (lam * s + mu) - (Real.log lam + log s + (mu - 1/2) / (lam * s))‖ ≤ C / ‖s‖ ^ 2
```

i.e. **`ψ(λs+μ) = log λ + log s + (μ−½)/(λs) + O(|s|⁻²)`** with an explicit constant
`C = (24 + ‖μ‖² + ‖μ‖)/λ²` and threshold `R = max(2‖μ‖/λ, 4/λ)`.

The three signature data — the constant `log λ`, the coefficient `1` of `log s`, and the `1/s`
residue `μ − ½` — are now readable from a Lean-certified estimate.  Summing over `j` with weights
`n_j λ_j` gives the card's

```text
G'/G(s) = α + (∑ n_j λ_j) log s + ∑ n_j λ_j log λ_j + [β + ∑ n_j (μ_j − ½)]/s + O(|s|⁻²),
```

which is the "no flat cancellation in the archimedean residue field" statement: a nonzero exponent
vector produces a nonzero signature, uniformly, with no room for a flat error to hide.

Ingredients used, none duplicated: mathlib's `Complex.log_ofReal_mul` (a positive real scale leaves
the branch alone), `Complex.norm_log_one_add_sub_self_le`, and the corpus's own
`norm_digammaStirlingDefect_le` and `log_sub_log_of_re_pos` from the previous two entries.

## 2026-08-18 (eighth entry) — cards A/B: **no flat cancellation is Lean-certified**

`HTGeometry/ArchimedeanNoFlatCancellation.lean` (new, wired, axioms clean):

```lean
theorem three_term_expansion_eq_zero {a b c : ℂ} {K R : ℝ}
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t → ‖a + b * (Real.log t) + c / t‖ ≤ K / t ^ 2) :
    a = 0 ∧ b = 0 ∧ c = 0
```

The three archimedean scales `1`, `log s`, `1/s` are **independent modulo `O(|s|⁻²)`**.  This is
§5's "no flat cancellation in the archimedean residue field", now a theorem: a nonzero Stirling
signature cannot hide inside the remainder.

Proof shape (all three steps constructive, with explicit witnesses rather than filters):
`0 ≤ K` is forced by the hypothesis at one point; `‖b‖ log t ≤ K + ‖a‖ + ‖c‖` for every `t ≥ 1`
then kills `b` at `t = exp(M/‖b‖ + 1)`; `‖a‖ ≤ (K+‖c‖)/T` kills `a` at
`T = (K+‖c‖)/‖a‖ + 1`; and `‖c‖ T ≤ K` kills `c` at `T = K/‖c‖ + 1`.

Combined with `exists_norm_digamma_affine_expansion_le`, subtracting the expansions of two
monomials of `e^{αs} s^β ∏_j Γ(λ_j s + μ_j)^{n_j}` and applying this theorem to the difference
gives the separation of the three signature data

```text
(∑ n_j λ_j,   α + ∑ n_j λ_j log λ_j,   β + ∑ n_j (μ_j − ½)).
```

That is the whole content of §5.  What is left on cards A and B is the bookkeeping that assembles
the per-factor expansion into the product expansion and feeds the separation into the boundary-datum
theorem in place of `NoIntegerRelation`.

## 2026-08-18 (ninth entry) — cards A/B: **the archimedean separation of monomials is closed**

`HTGeometry/GammaProductStirlingSignature.lean` (new, wired, axioms clean) assembles the per-factor
signature into the product and proves the separation.

```lean
def gammaProductLogDeriv (lam) (mu n) (al be) (s) : ℂ :=
  al + be / s + ∑ j, n j * lam j * Complex.digamma (lam j * s + mu j)

def gammaProductSignature (lam) (mu n) (al be) : ℂ × ℂ × ℂ :=
  (al + ∑ j, n j * lam j * Real.log (lam j),   ∑ j, n j * lam j,   be + ∑ j, n j * (mu j - 1/2))

theorem exists_norm_gammaProductLogDeriv_expansion_le :
  ∃ C R, … ‖G'/G(s) − (A + B log s + C₀/s)‖ ≤ C / ‖s‖²

theorem gammaProductSignature_eq_of_logDeriv_eq :
  (logarithmic derivatives agree on a real ray) → signatures agree
```

So for `G(s) = e^{αs} s^β ∏_j Γ(λ_j s + μ_j)^{n_j}` with positive real scales:

```text
G'/G(s) = [α + ∑ n_j λ_j log λ_j] + [∑ n_j λ_j] log s + [β + ∑ n_j (μ_j − ½)]/s + O(|s|⁻²),
```

and two such products with the same logarithmic derivative have the *same three signature data*.
That is §5 of `finite-archimedean-gamma-product-boundary-law` and the archimedean half of
`archimedean-relative-prime-cocycle-curvature`, now Lean-certified — and it holds for
**commensurable scales**, precisely the case `NoIntegerRelation` could not reach.

The Stirling chain for cards A/B is therefore complete end to end:

```text
Complex.hasSum_taylorSeries_log  →  norm_log_one_add_sub_taylor_two_le   (cubic gain)
Complex.digamma_apply_add_one    →  norm_digammaStirlingDefect_step_le
RHTower.gauss_digamma            →  norm_digamma_shift_sub_le            (anchor)
                                 →  norm_digammaStirlingDefect_le        ψ = log z − 1/2z + O(z⁻²)
Complex.log_ofReal_mul           →  exists_norm_digamma_affine_expansion_le
                                 →  three_term_expansion_eq_zero         (no flat cancellation)
                                 →  gammaProductSignature_eq_of_logDeriv_eq
```

What remains on these two cards is to substitute this separation for the `NoIntegerRelation`
hypothesis in the existing boundary-datum theorem
(`HTGeometry/ShiftedGammaFieldIndependence`, `GammaJetNormalFormDatum`) — a rewiring of statements
already in the tree, with no new mathematics.

## 2026-08-18 (tenth entry) — cards A/B: `NoIntegerRelation` removed from the boundary datum

`HTGeometry/GammaJetNormalFormSeparation.lean` (new, wired, axioms clean).

Inspecting `exists_hasShiftTubeDatum_jetGammaNormalForm` shows `NoIntegerRelation lamf` — *no*
nonzero integer combination of the shifts is an integer — is used in exactly **one** place, to show
the dominant class is a singleton, and only for the differences of the actual exponent vectors.
Abstracting that use:

```lean
def ShiftExponentSeparating (lamf : Fin rr → ℝ) (ee : Fin Mm → Fin rr → ℕ) : Prop :=
  ∀ (α β : Fin Mm) (m : ℤ),
    (∑ k, (ee α k : ℤ)) = ∑ k, (ee β k : ℤ) →
    (∑ k, (((ee α k : ℤ) - (ee β k : ℤ)) : ℝ) * lamf k) = (m : ℝ) → α = β

theorem exists_hasShiftTubeDatum_jetGammaNormalForm_of_separating … (hsep : ShiftExponentSeparating lamf ee) …
theorem shiftExponentSeparating_of_noIntegerRelation (hindep) (hee : Injective ee) : ShiftExponentSeparating lamf ee
```

This is a strict generalization: the old hypothesis is the special case, and injectivity of `ee` is
no longer needed as a separate assumption.  Crucially `ShiftExponentSeparating` **can hold for
commensurable scales** — the case `λ_j = n_j/H` of the card, where `NoIntegerRelation` is false by
construction — because it only constrains the finitely many exponent vectors that actually occur.

This is the socket the Stirling signature plugs into: `gammaProductSignature_eq_of_logDeriv_eq`
supplies the extra separating datum `∑_k e_k λ_k log λ_k` that `NoIntegerRelation` never saw.

Remaining on cards A/B: exhibit `ShiftExponentSeparating` for the card's actual shift data from the
signature separation — an arithmetic step about `log λ_k` for commensurable `λ_k`, on top of two
theorems both now in the tree.

## 2026-08-18 (eleventh entry) — correction: cards A/B need the *finite-order* Stirling ladder

The ninth and tenth entries said what remains on cards A/B is "an arithmetic step".  Working it out
shows that is **wrong**, and the correction matters, so it is recorded rather than quietly fixed.

In the card's normal form the Gamma factors are `Γ(s + λ_k)^{e_k}`: every *scale* is `1` and the
`λ_k` appear as *shifts*.  Feeding that into `gammaProductSignature` gives

* `log s` coefficient `= ∑_k e_k`  — this is the datum `d` the coarse boundary datum already has;
* constant `= α`, because `log λ = log 1 = 0` — **no new information**;
* `1/s` residue `= β + ∑_k e_k (λ_k − ½)`.

So the Stirling signature contributes exactly one genuinely new number, `∑_k e_k λ_k`, and its value
is *exact* rather than only-mod-`ℤ` (the coarse datum sees `a + ∑ e_k λ_k` with `a ∈ ℤ` unknown).
That is a real gain — it is why `NoIntegerRelation` can be dropped — but two linear conditions
(`∑ e_k` and `∑ e_k λ_k`) cannot pin down an exponent vector in `ℕ^{rr}` for `rr > 2`.

What does pin it down is the **finite-order ladder**: `ψ(s+λ) = log s + ∑_{m=1}^{M} P_m(λ)/s^m +
O(|s|^{-(M+1)})` with `P_m` of degree `m` and leading coefficient `(−1)^{m+1}/m`.  Reading the
`1/s^m` residues for `m = 1 … rr` gives the power sums `∑_k e_k λ_k^m` by a triangular change of
basis, and a Vandermonde argument on distinct `λ_k` then determines `e` uniquely.  This is exactly
the card's §5 "complete Stirling signature".

So the correct statement of what remains on cards A and B is: **extend the Stirling ladder from
order 1 to arbitrary finite order `M`**, then read off the power sums and invert the Vandermonde.
The three-term instalment already landed is the `M = 1` case and supplies all the machinery the
induction needs — the telescope, the anchor, and the no-flat-cancellation principle generalize to
`M` terms with the Bernoulli recursion replacing the single cubic gain.

`ShiftExponentSeparating` (tenth entry) remains the right socket: it is what the ladder will feed.

## 2026-08-18 (twelfth entry) — cards A/B: the two routes to the finite-order separation

Working out the ladder shows the remaining obstruction precisely, and that there are two routes.
Recording both so the next session starts from the analysis rather than redoing it.

### Route 1 — the finite-order Stirling ladder (the card's own §5)

Target: `∀ M, ∃ c : Fin M → ℂ, ∃ K R, ∀ z, Re z > 0 → R ≤ ‖z‖ →
‖ψ z − log z + ∑_{m<M} c m / z^(m+1)‖ ≤ K / ‖z‖^(M+1)`.

Note this is an **existence** statement in the coefficients — the Bernoulli numbers need never be
computed.  The induction is the one already built at `M = 1`:

* one-step difference `h_M(z+1) − h_M(z)`, with `ψ(z+1) − ψ(z) = 1/z`,
  `log(z+1) − log z = ∑_{m≥1} (−1)^{m+1}/(m z^m)` and
  `1/(z+1)^m − 1/z^m = −m/z^{m+1} + O(z^{-(m+2)})`;
* the coefficient `c_m` is *determined* by cancelling the order-`z^{-(m+1)}` term — the system is
  triangular because adding `c_m/z^m` moves only that order and below;
* then the same telescope + anchor as at `M = 1`, with `∑_k ‖z+k‖^{-(M+2)} = O(‖z‖^{-(M+1)})`.

Substituting `w = s + λ` then gives `ψ(s+λ) = log s + ∑_m P_m(λ)/s^m + O(s^{-(M+1)})` with `P_m` of
degree `m` and leading coefficient `(−1)^{m+1}/m`, so the residues at `1/s^m`, `m = 1 … rr`, give
the power sums `∑_k e_k λ_k^m` by a triangular change of basis, and Vandermonde on distinct `λ_k`
determines `e`.  The independence of `1, log s, 1/s, …, 1/s^M` modulo `O(s^{-(M+1)})` generalizes
`three_term_expansion_eq_zero` by the same three-step argument.

### Route 2 — residues instead of asymptotics

`ψ` has a simple pole with residue `−1` at every nonpositive integer, so `∑_k e_k ψ(s + λ_k)` has a
simple pole at `s = −λ_k − n` with residue `−e_k` **whenever the `λ_k` are pairwise incongruent
mod `ℤ`** — which is exactly the hypothesis `hincong` already carried by the tree's theorems.  So
the exponent vector is recoverable from the polar data of `G'/G`, with no asymptotics at all.

Route 2 is much shorter but does **not** by itself discharge `ShiftExponentSeparating`, because that
predicate is about which summands share a *boundary datum* `(d, ω, b)`, and with commensurable
scales distinct exponent vectors genuinely can share one.  Discharging it needs the datum itself
refined to carry the exact `∑_k e_k λ_k` (the card's §6 "product-field valuation"), which is what
Route 1 supplies.  Route 2 is therefore the right tool for the *uniqueness* half of the card and
Route 1 for the *separation* half.

Neither is blocked; both are multi-stage builds.  Route 1's `M = 1` case, its telescope, its anchor
and its independence principle are all already in the tree.

## 2026-08-18 (thirteenth entry) — cards A/B: descending powers are independent at every order

`HTGeometry/ArchimedeanPowerIndependence.lean` (new, wired, axioms clean) generalizes
`three_term_expansion_eq_zero` from three scales to all of them:

```lean
theorem eq_zero_of_norm_le_const_div {x : ℂ} {C R : ℝ}
    (h : ∀ t, R ≤ t → 1 ≤ t → ‖x‖ ≤ C / t) : x = 0

theorem power_expansion_eq_zero : ∀ (M : ℕ) (a : ℕ → ℂ) (K R : ℝ),
    (∀ t : ℝ, R ≤ t → 1 ≤ t → ‖∑ m ∈ Finset.range (M+1), a m / (t : ℂ) ^ m‖ ≤ K / t ^ (M+1)) →
    ∀ m ∈ Finset.range (M+1), a m = 0
```

The scales `1, 1/t, …, 1/t^M` are independent modulo `O(t^{-(M+1)})`, at every order `M`.  The
induction is two moves: the constant coefficient is killed by `t → ∞` (its competitors carry at
least one factor `1/t`), and what is left is `1/t` times an expansion of one order less, so
multiplying by `t` restores the shape and the inductive hypothesis applies.

This is the *reading* half of Route 1 for the finite-order Stirling ladder: once the expansion
`ψ(s+λ) = log s + ∑_{m≤M} P_m(λ)/s^m + O(s^{-(M+1)})` exists, this theorem is what turns "two
products have the same logarithmic derivative" into "all `M` residues agree", hence into the power
sums `∑_k e_k λ_k^m` and the Vandermonde inversion.

What remains of Route 1 is the *producing* half: the ladder itself, by the induction described in
the twelfth entry.  Its `M = 1` case, telescope, anchor and now its reading principle at every
order are all in the tree.

## 2026-08-18 (fourteenth entry) — cards A/B: the second rung of the ladder

`HTGeometry/GammaStirlingQuarticLog.lean` (new, wired, axioms clean):

- `norm_log_one_add_sub_taylor_three_le` — `‖log(1+u) − (u − u²/2 + u³/3)‖ ≤ ‖u‖⁴` on `‖u‖ ≤ ½`,
  by dropping four terms of `Complex.hasSum_taylorSeries_log`.
- `digammaStirlingDefectTwo z = ψ(z) − log z + 1/(2z) + 1/(12 z²)` and
  `digammaStirlingDefectTwo_step`.
- `norm_digammaStirlingDefectTwo_step_le` — **the second-rung gain**:
  `‖g₂(z+1) − g₂(z)‖ ≤ 4/‖z‖⁴` for `Re z > 0`, `‖z‖ ≥ 2`.

The mechanism, now visible twice and identical at every rung: in the variable `u = 1/z` the three
cubic contributions of the one-step difference,

```text
u − log(1+u)      →  +u²/2 − u³/3
−1/(2z(z+1))      →  −u²/2 + u³/2
(1/12)(1/(z+1)² − 1/z²)  →  −u³/6,
```

sum to `(−1/3 + 1/2 − 1/6) u³ = 0`.  The coefficient `1/12` is *forced* by that cancellation, and at
rung `m` the coefficient `c_m` is likewise forced by the order-`u^{m+1}` cancellation — which is why
the ladder can be built by induction without ever naming a Bernoulli number.

With `power_expansion_eq_zero` (thirteenth entry) supplying the reading principle at every order,
the two halves of Route 1 are: this rung pattern, generalized to arbitrary `M` by an induction on
the Taylor order of the explicit function
`F_M(u) = u − log(1+u) + ∑_{m≤M} c_m u^m((1+u)^{−m} − 1)`,
and the telescope, which is order-independent and already written twice.

## 2026-08-18 (fifteenth entry) — cards A/B: the second rung, telescoped

`HTGeometry/GammaStirlingSecondRung.lean` (new, wired, axioms clean):

```lean
theorem norm_digammaStirlingDefectTwo_le {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖ψ z − log z + 1/(2z) + 1/(12 z²)‖ ≤ 12 / ‖z‖ ^ 3
```

i.e. **`ψ(z) = log z − 1/(2z) − 1/(12 z²) + O(|z|⁻³)`**, with an explicit constant.  Supporting:

- `norm_add_natCast_fourth_ge` — `‖z+k‖⁴ ≥ ‖z‖²(‖z‖+k)²/2` on the right half-plane, which turns the
  quartic one-step gain into the *same* `∑_k (‖z‖+k)⁻²` sum the first rung used;
- `tendsto_digammaStirlingDefectTwo_shift_zero` — the anchor, from the first-rung anchor plus
  `1/(12(z+N)²) → 0`.

Both rungs are now complete end to end, and the telescope is verbatim the same at each: the *only*
order-dependent inputs are the Taylor bound for `log(1+u)` (one more term per rung) and the
elementary inequality `‖z+k‖^{2m} ≥ ‖z‖^{2m−2}(‖z‖+k)²/2`.  Everything else — the anchor, the
`∑_k (‖z‖+k)⁻²` bound, and the passage to the limit — is order-independent and already written.

Reading rung 2 at `w = s + λ` gives the second signature datum `∑_k e_k λ_k²`, so the separation now
covers every normal form with at most three distinct shifts; the general case is the induction over
rungs.

## 2026-08-18 (sixteenth entry) — cards A/B: the telescope, once and for all

`HTGeometry/GammaStirlingTelescope.lean` (new, wired, axioms clean) extracts the order-independent
half of the ladder as a single reusable theorem about an *arbitrary* function:

```lean
theorem norm_add_natCast_pow_ge {z : ℂ} (hz : 0 < z.re) (N k : ℕ) :
    ‖z‖ ^ N * (‖z‖ + k) ^ 2 / 2 ≤ ‖z + k‖ ^ (N + 2)

theorem norm_le_of_step_bound {L : ℂ → ℂ} {N : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hstep : ∀ w, 0 < w.re → 2 ≤ ‖w‖ → ‖L (w+1) − L w‖ ≤ K / ‖w‖ ^ (N+2))
    {z : ℂ} (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖)
    (hanchor : Tendsto (fun n : ℕ => L (z + n)) atTop (𝓝 0)) :
    ‖L z‖ ≤ (3 * K) / ‖z‖ ^ (N + 1)
```

Both rungs already built are instances.  The inequality `‖z+k‖^{N+2} ≥ ‖z‖^N (‖z‖+k)²/2` is what
makes every order reduce to the *same* sum `∑_k (‖z‖+k)⁻² ≤ ‖z‖⁻² + ‖z‖⁻¹`.

**Cost accounting for the remaining induction.**  With this in place a rung of the ladder now costs
exactly two things:

1. the Taylor bound `‖log(1+u) − ∑_{j<n} (−1)^{j+1} u^j / j‖ ≤ ‖u‖^n` on `‖u‖ ≤ ½` — proved twice
   already (`n = 3, 4`) by dropping terms of `Complex.hasSum_taylorSeries_log`, and uniform in `n`;
2. the algebraic cancellation that *forces* the rung's coefficient, an identity between explicit
   rational functions of `u = 1/z`.

Everything else — anchor, telescope, limit passage, reading principle — is now order-independent and
certified.

## 2026-08-18 (seventeenth entry) — cards A/B: the log Taylor bound at every order

`HTGeometry/ComplexLogTaylorUniform.lean` (new, wired, axioms clean) removes the first of the two
per-rung costs identified in the sixteenth entry:

```lean
theorem norm_log_one_add_sub_taylor_le {u : ℂ} (hu : ‖u‖ ≤ 1/2) {n : ℕ} (hn : 1 ≤ n) :
    ‖log (1 + u) − ∑ j ∈ Finset.range n, (−1)^(j+1) * u^j / j‖ ≤ 2 * ‖u‖^n / n

theorem norm_log_one_add_sub_taylor_le' (hu) {n} (hn : 2 ≤ n) :
    ‖log (1 + u) − ∑ j ∈ Finset.range n, (−1)^(j+1) * u^j / j‖ ≤ ‖u‖^n
```

Mathlib has only the quadratic case (`Complex.norm_log_one_add_sub_self_le`).  The proof is the one
used twice already, now uniform in `n`: drop the first `n` terms of
`Complex.hasSum_taylorSeries_log`, bound the `k`-th tail term by `(‖u‖^n/n)‖u‖^k`, and sum the
geometric series.  The cubic and quartic bounds of the first two rungs are the cases `n = 3, 4`.

Remaining per-rung cost is now the single algebraic item: the identity between explicit rational
functions of `u = 1/z` that forces the rung's coefficient.  Everything else in the ladder —
Taylor bound at every order, telescope at every order, anchor, limit passage, and the reading
principle `power_expansion_eq_zero` — is certified and order-independent.

## 2026-08-18 (eighteenth entry) — cards A/B: the third rung, and the first use of the uniform tools

`HTGeometry/GammaStirlingThirdRung.lean` (new, wired, axioms clean):

```lean
theorem norm_digammaStirlingDefectTwo_step_le' (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖g₂(z+1) − g₂(z)‖ ≤ 4 / ‖z‖ ^ 5

theorem norm_digammaStirlingDefectTwo_le' (hz : 0 < z.re) (h2 : 2 ≤ ‖z‖) :
    ‖ψ z − log z + 1/(2z) + 1/(12 z²)‖ ≤ 12 / ‖z‖ ^ 4
```

i.e. **`ψ(z) = log z − 1/(2z) − 1/(12 z²) + O(|z|⁻⁴)`**.

Two things worth recording:

* **The third rung is free.**  `ψ` has no `1/z³` term, and that appears here as a second exact
  cancellation: the quartic contributions `+u⁴/4`, `−u⁴/2`, `+u⁴/4` of the one-step difference sum
  to zero with the *same* coefficients `1/2, 1/12` already fixed.  No new constant is introduced.
* **The uniform tools did their job.**  The bound was assembled from
  `norm_log_one_add_sub_taylor_le'` at `n = 5` and `norm_le_of_step_bound` at `N = 3`, both proved
  once and for all in the two preceding entries; the whole rung reduced to three exact algebraic
  remainders, each an explicit rational function of `u = 1/z`.

Reading rung 3 at `w = s + λ` gives the third signature datum `∑_k e_k λ_k³`, so the archimedean
separation now covers every normal form with at most four distinct shifts.

## 2026-08-18 (nineteenth entry) — cards A/B: the fourth rung, `c₄ = −1/120`

`HTGeometry/GammaStirlingFourthRung.lean` (new, wired, axioms clean):

```lean
def digammaStirlingDefectFour z = ψ z − log z + 1/(2z) + 1/(12 z²) − 1/(120 z⁴)

theorem norm_digammaStirlingDefectFour_step_le : ‖g₄(z+1) − g₄(z)‖ ≤ 9 / ‖z‖ ^ 6
theorem norm_digammaStirlingDefectFour_le      : ‖g₄ z‖ ≤ 27 / ‖z‖ ^ 5
```

i.e. **`ψ(z) = log z − 1/(2z) − 1/(12 z²) + 1/(120 z⁴) + O(|z|⁻⁵)`**.

This rung is the first that is *not* free: the quintic contributions `−1/5`, `+1/2`, `−1/3` sum to
`−1/30`, and the coefficient is forced by `−1/30 − 4c₄ = 0`.  The value `−1/120` reproduces the
classical `B₄/4 = −1/120` without any Bernoulli input — it comes out of the cancellation.

Four rungs are now built, and the pattern is fully exposed:

| rung | new coefficient | forced by |
|---|---|---|
| 1 | `1/2`   | quadratic cancellation |
| 2 | `1/12`  | cubic cancellation `−1/3 + 1/2 − 1/6 = 0` |
| 3 | none    | quartic cancellation `1/4 − 1/2 + 1/4 = 0` |
| 4 | `−1/120`| quintic cancellation `−1/5 + 1/2 − 1/3 + 1/30 = 0` |

Every rung after the first was assembled from `norm_log_one_add_sub_taylor_le'` and
`norm_le_of_step_bound`, both order-uniform, plus exact rational-function remainders.  Reading the
four rungs at `w = s + λ` gives the signature data `∑_k e_k λ_k^m` for `m = 1 … 4`, so the
archimedean separation now covers every normal form with at most five distinct shifts.

## 2026-08-18 (twentieth entry) — cards A/B: rung-5 data, and the shape of the general induction

Recording the next rung's arithmetic so it is not recomputed, and the exact form the general
induction should take.

### Rung 5 is free

The sextic contributions of the one-step difference of `g₄` are

```text
u − log(1+u)                     →  +1/6
−1/(2z(z+1))                     →  −1/2
(1/12)(1/(z+1)² − 1/z²)          →  +5/12
−(1/120)(1/(z+1)⁴ − 1/z⁴)        →  −1/12
```

and `1/6 − 1/2 + 5/12 − 1/12 = 0`.  So no `1/z⁵` coefficient is needed (as expected: `ψ` has no odd
terms past `−1/(2z)`), `‖g₄(z+1) − g₄(z)‖ = O(‖z‖⁻⁷)`, and the telescope gives
`‖g₄ z‖ = O(‖z‖⁻⁶)`.  The four exact remainders are, in `u = 1/z`:

```text
A = u − log(1+u) − (u²/2 − u³/3 + u⁴/4 − u⁵/5 + u⁶/6)            ‖A‖ ≤ ‖u‖⁷
B = −1/(2z(z+1)) + (u²/2 − u³/2 + u⁴/2 − u⁵/2 + u⁶/2) = u⁷/(2(1+u))
C = (1/12)(1/(z+1)² − 1/z²) + u³/6 − u⁴/4 + u⁵/3 − 5u⁶/12
E = −(1/120)(1/(z+1)⁴ − 1/z⁴) − u⁵/30 + u⁶/12
```

`B` follows from `∑_{i≤4} (−1)^i u^i = (1+u⁵)/(1+u)`; `C` and `E` are the corresponding truncations
of `(1+u)^{−2}` and `(1+u)^{−4}`.

### The general induction

Everything reduces to one polynomial statement.  With `T_N(u) = ∑_{j=2}^{N} (−1)^j u^j / j` and

```text
Q_M(u) = T_{M+1}(u)·(1+u)^M + ∑_{m<M} c_m u^{m+1}((1+u)^{M−m−1} − (1+u)^M),
```

`Q_M` is a *polynomial*, the rational part of the one-step difference is `Q_M(u)/(1+u)^M`, and the
whole ladder is the claim that the `c_m` can be chosen so that `u^{M+2} ∣ Q_M`.  That system is
triangular with diagonal entries `−(m+1) ≠ 0`, so it is solvable by strong recursion on `m`.

Once `Q_M = u^{M+2} S_M`, the bound is immediate: `‖Q_M(u)/(1+u)^M‖ ≤ 2^M ‖S_M‖_∞ ‖u‖^{M+2}` on
`‖u‖ ≤ ½`, and `norm_le_of_step_bound` finishes.  The order-uniform Taylor bound
`norm_log_one_add_sub_taylor_le'` supplies the transcendental half.

So the remaining work on cards A and B is a `Polynomial`-API induction, with every analytic
ingredient already certified.

## 2026-08-18 (twenty-first entry) — cards A/B: the second signature datum, in the card's own shape

`HTGeometry/GammaShiftSignatureTwo.lean` (new, wired, axioms clean):

```lean
theorem exists_norm_digamma_shift_expansion_two_le (mu : ℂ) :
    ∃ C R, 0 ≤ C ∧ 0 ≤ R ∧ ∀ s, 0 < s.re → 0 < (s + mu).re → R ≤ ‖s‖ →
      ‖ψ (s + mu) − (log s + (mu − ½)/s + (−μ²/2 + μ/2 − 1/12)/s²)‖ ≤ C / ‖s‖ ^ 3
```

with `C = 48 + ‖μ‖³ + 2‖μ‖² + 2‖μ‖` and `R = max (4‖μ‖) 4`.

This is stated at **unit scale**, which is the card's own normal form (`Γ(s + λ_k)^{e_k}`: all
scales are `1`, the `λ_k` are shifts) — so it is directly consumable rather than a general-`λ`
statement that would then have to be specialized.  Weighted by `e_k` and summed, the `1/s²` residue
is

```text
−(∑_k e_k λ_k²)/2 + (∑_k e_k λ_k)/2 − (∑_k e_k)/12,
```

so the **second power sum `∑_k e_k λ_k²` is recovered** once `∑_k e_k` and `∑_k e_k λ_k` are known —
and those are exactly the first two data, already certified.

All four remainders are exact rather than estimated:
`1/(s+μ) = 1/s − μ/s² + μ²/(s²(s+μ))` and `1/(s+μ)² = 1/s² − (2sμ+μ²)/(s²(s+μ)²)`, with the
transcendental part supplied by `norm_log_one_add_sub_taylor_le'` at `n = 3` and the Stirling input
by the third-rung bound `norm_digammaStirlingDefectTwo_le'`.

Combined with `power_expansion_eq_zero`, the archimedean separation of monomials in the card's
normal form is now unconditional for **three distinct shifts**, and each further rung extends it by
one.

## 2026-08-18 (twenty-second entry) — cards A/B: the third signature datum

`HTGeometry/GammaShiftSignatureThree.lean` (new, wired, axioms clean), compiled on the first check:

```lean
theorem exists_norm_digamma_shift_expansion_three_le (mu : ℂ) :
    ∃ C R, … ‖ψ (s + mu) − (log s + (mu − ½)/s + (−μ²/2 + μ/2 − 1/12)/s²
                              + (μ³/3 − μ²/2 + μ/6)/s³)‖ ≤ C / ‖s‖ ^ 4
```

with `C = 217 + ‖μ‖⁴ + 2‖μ‖³ + ‖μ‖²` and `R = max (4‖μ‖) 4`.

Weighted and summed, the `1/s³` residue is
`(∑_k e_k λ_k³)/3 − (∑_k e_k λ_k²)/2 + (∑_k e_k λ_k)/6`, so the **third power sum** is recovered
from it and the earlier data.  With `power_expansion_eq_zero`, the archimedean separation in the
card's normal form is now unconditional for **four distinct shifts**.

That this module compiled on the first attempt is the real signal: the per-datum cost has settled
into a fixed routine — one Stirling rung, one uniform Taylor bound, and the exact expansions
`1/(s+μ) = 1/s − μ/s² + μ²/s³ − μ³/(s³(s+μ))`,
`1/(s+μ)² = 1/s² − 2μ/s³ + (3sμ² + 2μ³)/(s³(s+μ)²)`.
The general datum needs the same routine with the general rung, i.e. exactly the polynomial
induction recorded in the twentieth entry.

## 2026-08-18 (twenty-third entry) — cards A/B: the fourth datum, and its one sticking point

The fourth signature datum was written out and all but two goals discharged; it is **not** landed,
because two arithmetic steps in the last remainder did not close.  Recording the working so the next
attempt starts from it.

Target:

```text
ψ(s + μ) = log s + (μ − ½)/s + (−μ²/2 + μ/2 − 1/12)/s² + (μ³/3 − μ²/2 + μ/6)/s³
             + (−μ⁴/4 + μ³/2 − μ²/4 + 1/120)/s⁴ + O(|s|⁻⁵),
```

whose `1/s⁴` residue gives `∑_k e_k λ_k⁴`.  Four of the five remainders go through unchanged from
the third-datum routine.  The sticking point is the fifth,
`E₅ = 1/(120 w⁴) − 1/(120 s⁴)`, where the expanded numerator
`4s³μ + 6s²μ² + 4sμ³ + μ⁴` needs `‖·‖ ≤ 6‖s‖³‖μ‖`, and `nlinarith` will not chain
`‖μ‖ ≤ ‖s‖/4` through four degrees at once.

**Better route for the next attempt**: factor instead of expanding.

```text
s⁴ − w⁴ = (s − w)(s + w)(s² + w²) = −μ (s + w)(s² + w²),
```

so `E₅ = −μ (s+w)(s²+w²) / (120 s⁴ w⁴)`, and with `‖s‖/2 ≤ ‖w‖ ≤ (5/4)‖s‖` this gives
`‖E₅‖ ≤ ‖μ‖ · (9/4)‖s‖ · 3‖s‖² · 16 / (120 ‖s‖⁸) ≤ ‖μ‖/‖s‖⁵` in three easy steps rather than a
four-degree chain.  The upper bound `‖w‖ ≤ (5/4)‖s‖` follows from `‖μ‖ ≤ ‖s‖/4`.

Everything else in the module is already verified.

## 2026-08-18 (twenty-fourth entry) — cards A/B: the fourth signature datum lands

`HTGeometry/GammaShiftSignatureFour.lean` (new, wired, axioms clean).  The route recorded in the
twenty-third entry worked:

```lean
theorem exists_norm_digamma_shift_expansion_four_le (mu : ℂ) :
    ∃ C R, … ‖ψ (s + mu) − (log s + (mu − ½)/s + (−μ²/2 + μ/2 − 1/12)/s²
                              + (μ³/3 − μ²/2 + μ/6)/s³
                              + (−μ⁴/4 + μ³/2 − μ²/4 + 1/120)/s⁴)‖ ≤ C / ‖s‖ ^ 5
```

with `C = 864 + ‖μ‖⁵ + 2‖μ‖⁴ + 2‖μ‖³ + ‖μ‖` and `R = max (4‖μ‖) 4`.

Two lessons for the remaining rungs, both about `nlinarith` rather than mathematics:

* **Factor, don't expand.**  `s⁴ − w⁴ = −μ (s+w)(s²+w²)` turned a four-degree coefficient chain
  into three independent estimates (`‖s+w‖ ≤ (9/4)‖s‖`, `‖s²+w²‖ ≤ 3‖s‖²`, `‖w‖⁴ ≥ ‖s‖⁴/16`).
* **Chain products with `mul_le_mul`, not `nlinarith`.**  Degree-3 products of unknowns defeat
  `nlinarith`; `mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)` followed by
  `mul_le_mul_of_nonneg_right` closes them immediately.  The needed upper bound
  `‖w‖ ≤ (5/4)‖s‖` comes from `norm_add_le` and `‖μ‖ ≤ ‖s‖/4`.

The `1/s⁴` residue is `−(∑ e_k λ_k⁴)/4 + (∑ e_k λ_k³)/2 − (∑ e_k λ_k²)/4 + (∑ e_k)/120`, so with
`power_expansion_eq_zero` the archimedean separation in the card's normal form is now unconditional
for **five distinct shifts** — it was two when this session began.

## 2026-08-18 — entry 25: the general Stirling ladder is closed at every finite order

The open core recorded in entry 20 is proved. Four new Lean modules, all axiom-clean
(`propext, Classical.choice, Quot.sound`), all built individually in the foreground:

1. `HTGeometry/PolynomialVanishingOrderBound.lean` —
   `exists_norm_polyEval_div_pow_le_of_dvd : X^N ∣ P → ∃ C ≥ 0, ∀ ‖u‖ ≤ ½, ‖P(u)/(1+u)^k‖ ≤ C‖u‖^N`.
   The analytic half of the reduction; constant explicit in the coefficients of the cofactor, the
   denominator costing only `2^k` because `‖1+u‖ ≥ ½` on the half disc.

2. `HTGeometry/GammaStirlingLadderPolynomial.lean` — the **algebraic heart**. The key discovery is
   that the cleared numerator obeys a *linear* recursion,

   `P_{M+1} = (1+X)·P_M + ((-1)^M/(M+2))·X^{M+2}(1+X)^{M+1} + c_M·X^{M+1}(1 - (1+X)^{M+1})`,

   in which **all three summands are already divisible by `X^{M+2}`**. So only the single degree
   `M+2` coefficient has to be killed, and it is killed by

   `c_M = (P_M.coeff (M+2) + (-1)^M/(M+2)) / (M+1)`,

   the denominator `M+1` being the `u^1` coefficient of `1 - (1+u)^{M+1}` and never zero. Theorem
   `X_pow_dvd_ladderPoly : ∀ M, X^(M+2) ∣ ladderPoly M`, by induction with
   `Polynomial.X_pow_dvd_iff`. This replaces the triangular-system argument of entry 20: no linear
   algebra, no Bernoulli input, no `M`-dependence in the coefficients — they are *forced*.

3. `HTGeometry/GammaStirlingLadderStep.lean` — `ladderPoly_eval`: for `1 + u ≠ 0`,
   `(ladderPoly M).eval u = (1+u)^M (ladderRatPart M u + taylorTail M u)`; `ladderDefect_step`;
   `taylorTail_eq` (`u - T_M(u)` *is* the degree-`M+1` Taylor polynomial of `log(1+u)`); and
   `exists_norm_ladderDefect_step_le : ∃ K ≥ 0, ‖g_M(z+1) - g_M(z)‖ ≤ K/‖z‖^{M+2}` on
   `Re z > 0, ‖z‖ ≥ 2`. The split is rational part + logarithmic Taylor tail, the two bounds coming
   from item 1 and `norm_log_one_add_sub_taylor_le'` at `n = M+2`.

4. `HTGeometry/GammaStirlingLadder.lean` — the anchor at infinity
   (`tendsto_ladderDefect_shift_zero`, from `tendsto_digammaStirlingDefect_shift_zero` plus
   `‖z+n‖ → ∞`) and the capstone

   `exists_norm_ladderDefect_le (M) : ∃ K ≥ 0, ∀ Re z > 0, ‖z‖ ≥ 2,`
   `‖ψ z - log z + ∑_{m<M} c_m z^{-(m+1)}‖ ≤ K/‖z‖^{M+1}`,

   via `norm_le_of_step_bound` at `N = M`. Restated as
   `exists_norm_digamma_ladder_expansion_le`.

The four hand-built rungs (`GammaStirlingCubicLog`, `SecondRung`, `ThirdRung`, `FourthRung`) and the
four hand-built signature data are now special cases of a single theorem valid at every order. The
archimedean separation in the cards' normal form is therefore available at *arbitrary* order, not
only up to five distinct shifts.

## 2026-08-19 — entry 26: the shifted ladder, its coefficient polynomials, and the §5 separation

Six further Lean modules, all axiom-clean and built individually in the foreground.

1. `HTGeometry/GammaStirlingTelescopeThreshold.lean` — `norm_le_of_step_bound_ge`: the telescope
   above an arbitrary threshold `R ≥ 2`. Needed because a *shifted* ladder only has its step bound
   for `‖s‖ ≥ R(μ)`; the telescope never leaves `{z + k}`, where `‖z+k‖ ≥ ‖z‖`.

2. `HTGeometry/GammaShiftLadderPolynomial.lean` — `shiftLadderPoly`, `shiftLadderCoeff`,
   `X_pow_dvd_shiftLadderPoly`. **The shifted numerator obeys the same recursion with the same
   forced coefficient `ladderCoeffOf`**: the extra factor `1 + μX` has constant term `1`, so it
   never touches the degree `M+2` obstruction, and `μ` only moves the base case from `0` to `-μX²`.
   Telescoping directly in `s` avoids expanding the unshifted ladder at `z = s+μ`, which would have
   needed a binomial-series remainder at every order; the only new ingredient is the single rational
   function `1/(s+μ) = u/(1+μu)`.

3. `HTGeometry/GammaShiftLadder.lean` — `shift_ne_neg_natCast` (beyond `2‖μ‖` the shifted argument
   misses every digamma pole), `shiftLadderPoly_eval`, `shiftLadderPoly_eval_div`,
   `shiftLadderDefect_step`, `exists_norm_shiftLadderDefect_step_le`,
   `tendsto_shiftLadderDefect_shift_zero`, and the capstone

   `exists_norm_shiftLadderDefect_le (μ) (M) : ∃ K ≥ 0, R ≥ 2, ∀ Re s > 0, ‖s‖ ≥ R,`
   `‖ψ(s+μ) - log s + ∑_{m<M} d_m(μ) s^{-(m+1)}‖ ≤ K/‖s‖^{M+1}.`

   The four hand-built signature data are the cases `M = 1,2,3,4`.

4. `HTGeometry/GammaShiftLadderDifference.lean` — `shiftLadderCoeff_succ_sub`:
   `d_m(μ+1) - d_m(μ) = -(-μ)^m`, for every `m` and every complex `μ`. Proof: the functional
   equation `ψ(s+μ+1) = ψ(s+μ) + 1/(s+μ)` expands into a plain geometric series with an exact
   remainder (`inv_add_eq_geom_add_rem`); the ladder bounds both defects by `O(t^{-(M+1)})`, and
   `power_expansion_eq_zero` kills the bracket at each order. No new analysis.

5. `HTGeometry/GammaShiftLadderGraded.lean` — the shift is restored as a second indeterminate.
   `Graded`/`SubGraded` (Y-degree bounded by X-degree, resp. X-degree minus one) are closed under
   the ring operations in the exact pattern the recursion uses; `shiftLadderPolyTwo` is SubGraded;
   `map_shiftLadderPolyTwo` specialises it back. Consequence: `shiftLadderCoeff mu M` **is** a
   polynomial in `mu`, `shiftLadderCoeffPoly M`, of degree at most `M+1`.

6. `HTGeometry/GammaShiftLadderCoeffTop.lean` — the forward difference of a polynomial of degree
   `≤ M+1` reads off its top coefficient with the factor `M+1`, so items 4 and 5 force

   `(shiftLadderCoeffPoly M).coeff (M+1) = (-1)^{M+1}/(M+1) ≠ 0`,  `natDegree = M+1` exactly.

   No Bernoulli input anywhere: the coefficients are forced twice over, once by the polynomial
   obstruction and once by the functional equation.

7. `HTGeometry/GammaShiftLadderSeparation.lean` — the card's §5 mechanism.
   `sum_eval_eq_zero_of_ladder_moments` (triangularity: `1, d_0, …, d_{r-2}` have degrees
   `0,1,…,r-1`, so they span every polynomial of degree below `r`) and

   `eq_zero_of_ladder_moments_vanish : lam injective → ∑_k g_k = 0 →`
   `(∀ m, m+2 ≤ r → ∑_k g_k d_m(λ_k) = 0) → ∀ k, g_k = 0`,

   proved by feeding in the Lagrange basis of the shifts. **Distinctness of the shifts is the only
   hypothesis** — no `NoIntegerRelation`, which is exactly the commensurable-scale situation that
   defeated the order-one signature (ledger entries 12 and 20).

## 2026-08-19 — entry 27: the analytic all-order separation is closed

Two more modules complete the chain from the ladder to the card's §5 statement.

8. `HTGeometry/GammaLogPowerIndependence.lean` — `log_power_expansion_eq_zero`: if
   `‖b log t + ∑_{m≤M} a_m t^{-m}‖ ≤ K t^{-(M+1)}` for all large real `t`, then `b = 0` and every
   `a_m = 0`. The power part is bounded on `t ≥ 1` while `log t` is not, so `b` dies first (choose
   `t = exp((K+∑‖a_m‖+1)/‖b‖)`); `power_expansion_eq_zero` finishes. This is
   `three_term_expansion_eq_zero` at arbitrary order.

9. `HTGeometry/GammaShiftSumSeparation.lean` —
   `ladder_moments_of_digamma_shift_sum_small`: if `∑_k g_k ψ(t+λ_k) = O(t^{-(M+1)})` along the real
   ray then `∑_k g_k = 0` and `∑_k g_k d_m(λ_k) = 0` for every `m < M`; and the capstone

   `eq_zero_of_digamma_shift_sum_small : lam injective →`
   `(∀ large real t, ‖∑_k g_k ψ(t+λ_k)‖ ≤ K/t^r) → ∀ k, g_k = 0.`

**What this closes.** The card's §5 ("no flat cancellation in the archimedean residue field") for
the logarithmic-derivative layer is now unconditional in Lean, at *every* order, with distinctness
of the shifts as the only hypothesis. The obstruction recorded in entries 12 and 20 — that in the
normal form all scales are `1`, so the order-one signature yields only the two data `∑_k e_k` and
`∑_k e_k λ_k`, which cannot pin down an exponent vector in `ℕ^{rr}` for `rr > 2` — is removed: the
ladder supplies `rr` independent data, and Lagrange interpolation converts them into `e` itself.

**Route note for whoever continues.** The whole ladder programme rests on one observation worth
keeping: after clearing denominators, the one-step difference of the ladder defect satisfies a
*linear* recursion whose three summands are already divisible by `X^{M+2}`, so a single coefficient
has to be killed and the divisor `M+1` is never zero. Everything else (shifted version, degree
bound, leading coefficient, separation) is bookkeeping on top of that. No Bernoulli numbers, no
Binet integral, no `log Γ`, no branch analysis — only `ψ`.

## 2026-08-19 — entry 28: card C — the damped extension step is now derived, not assumed

Four Lean modules, axiom-clean, built individually.

10. `HTGeometry/QuasiAbelianCosetPoincareSeries.lean` — **the partial Poincaré series**. Abe's step
    does not sum a lower form over the whole upper lattice (that would repeat every value
    infinitely often); it sums over a *complement* of `ΓH` in `Γ`. The module supplies
    `complementEmbedding`, `cosetPoincareSeries`, and the two theorems that make it usable:

    - `cosetPoincareSeries_shift` — **the partial sum is `Γ`-automorphic**. The proof is purely
      formal: writing `δ = η + comp w`, the cocycle turns the shifted argument into a shifted index,
      the `ΓH`-part `η` is absorbed by the seed's own transformation law (this is where
      `upper.factor|_{ΓH} = lower.factor` is used), and the complement part is a translation of the
      summation index. No convergence hypothesis: `tsum_mul_left` and `Equiv.tsum_eq` are
      unconditional.
    - `cosetPoincareSeriesEntire_mem_forms`, plus continuity and line-entirety of the sum.
    - `cosetPoincareSeries_eq_seed_add_tail` — the card's decomposition `F = m·G + R` at the level
      of values: index `0` contributes the seed, everything else is the complement remainder.

11. `HTGeometry/QuasiAbelianCosetPoincareJet.lean` — the same decomposition at the level of mixed
    jets. Every jet observation is a *continuous linear functional*, so it passes through the
    locally normally convergent sum: `hasSum_cosetPoincareTermEntire_of_summableLocallyUniformly`
    and `jet_cosetPoincareSeriesEntire_eq_seed_add_tail`.

12. `HTGeometry/QuasiAbelianDampedLiftConstruction.lean` — **`liftPacket` is no longer an
    unverified structure field.** `AbeDampingPacketData` collects only primitive, checkable data:
    a complement embedding with the decomposition property, and a `B`-family of lower seeds that
    (a) have the packet jets of the given lower column and (b) whose complement Poincaré terms obey
    the polynomial-Gaussian damping bound. `AbeDampingPacketData.toLift` *derives* the whole
    `AbeDampedJetPacketLift`, and `abeDampedFactorExtensionOfDampingFamily`,
    `jetAmpleEveryFiniteOrder_of_hasAbeDampingFamily`,
    `isAbePositiveTorusless_of_hasAbeDampingFamily` carry it to the card's conclusions. This is the
    same move that turned `AbePositiveFactorPresentation.gaussianMajorant` into a consequence of
    `HasLatticeExponentialGrowth` at the base of the tower.

13. `HTGeometry/QuasiAbelianDampingFamilyNonvacuous.lean` — **the interface is inhabited.**
    `hasAbeDampingFamily_self`: a factor extends itself with a rank-zero complement, the partial sum
    being the seed and the majorant vacuous. Also `summableLocallyUniformlyOn_of_fintype`. This
    guards against the failure mode recorded elsewhere in this repository, where a gap theorem is
    stated over hypotheses no object satisfies.

**Card C status.** Item 1 of "Remaining on this card" is reduced to a single named predicate,
`HasAbeDampingFamily c lower upper` — Abe's Proposition 8.2 estimate and nothing else. Item 2,
`IsAbePositiveTorusless`, is *definitionally* "reachable from an Abe presentation by damped
extensions", and both its constructors (`isAbePositiveTorusless_of_presentation`,
`isAbePositiveTorusless_of_hasAbeDampingFamily`) are now available, the base one from a checkable
growth condition. What remains is the estimate itself for a concrete positive factor: a
`ΓH`-invariant multiplier family that is the identity on the packet jets and exponentially small on
the complement translates.

### Correction to the card-C Lean model (2026-08-19)

Attempting to *construct* `HasAbeDampingFamily` exposes a mismatch between the landed interface and
Abe's actual argument, worth recording before anyone tries again.

The construction that would work is `m_B = E^{⌈B⌉}` with `E` an entire multiplier that is the
identity on the packet jets and uniformly `< 1` in modulus on every nonzero complement translate of
the packet points. The corpus already has both halves of such an `E`: the separator bumps
(`flatIntegerLatticePacketSeparatorData`, `StripBounded`, so bounded along real lattice translates)
and the flat Gaussian damping `1 − (1 − gaussian)^m` of `gaussianFlatSeedData`, which is *by
construction* the identity to order `m` at its centre. Their sum over the packet is the identity on
every packet jet and Gaussian-small on translates, and raising it to the power `⌈B⌉` converts that
into `C·B^r e^{−δB}` times a polynomial-Gaussian weight — exactly the required majorant.

The obstruction is `ΓH`-invariance. `seed B j = m_B · (lowerColumn j)` lies in `lower.forms` only if
`m_B` is `ΓH`-invariant, so `E` may depend on the complement coordinates alone. Two packet points
can then share their complement coordinates, or differ there by a nonzero complement lattice vector
— `PairwiseDistinctModulo Γ w` does not forbid a difference that is non-lattice in the `ΓH`
directions and integral in the complement direction. In that case `E ≡ 1` at one point forces
`|E| = 1` at a nonzero translate of another, and no uniform `ρ < 1` exists.

Abe avoids this because he does **not** lift the whole packet at once: he peels one extremal block
at a time (card §"Induction step"), the subgroup interpolants having already been arranged to vanish
to the prescribed order at the earlier points, and chooses the damping ray for that block only.

Consequence: `AbeDampedJetPacketLift`, which demands one damped lift reproducing *every* packet jet
of *every* lower column simultaneously, is stronger than Proposition 8.2 supplies. Closing item 1
therefore needs the inner peeling induction modelled as well — a per-block interface with an ordered
packet and a vanishing hypothesis at the earlier blocks — not merely a proof of the present
`liftPacket`. Everything else built above (partial Poincaré series, its automorphy, the jet
decomposition, the reduction of the majorant to primitive data) is reusable unchanged.

## 2026-08-19 — entry 29: card D — equation (1) of the source reduction is Lean-proved

Two modules, axiom-clean, built individually.

14. `RHTower/CircleReflectionOperator.lean` — the reflection `I` on `L²(ℝ/ℤ)`.
    `measurePreserving_neg_circle`, `circleReflectionCLM` (composition with `x ↦ -x`, an isometry
    since negation preserves Haar measure), `circleReflectionCLM_coeFn`,
    `circleReflectionCLM_apply_self` / `_comp_self` (`I² = 1`),
    `circleReflectionCLM_fourierLp` (`I e_n = e_{-n}`), `dense_span_fourierBasis`, and

    `circleReflection_gaussDiagonalBlock_conj : I D I = D*`,

    which is where the reality relation `d_{-n} = conj d_n` (`gaussSampleValue_neg`, already in the
    tree) is consumed.

15. `RHTower/GaussQuasiInnerSquare.lean` —
    `lpBoundedMulCLM_comp_circle`, `circleReflection_lpBoundedMul_conj` (the reflection conjugates a
    multiplier into the reflected multiplier), `volume_singleton_addCircle`,
    `haar_singleton_addCircle`, `ae_ne_zero_addCircle`,

    `gaussPrimeScaleCircle_neg_sq : b_p(1−x)² = p · b_p(x)^{−2}` off the single point `0`,
    `circleReflection_gaussPrimeScaleSq_conj : I B² I = p · B^{−2}`,

    and the card's equation (1):

    `gaussPairedBlock hm k p := B ∘ D ∘ I ∘ B`,
    `gaussPairedBlock_sq : C ∘ C = gaussQuasiInnerG hm k p`.

The identity is genuinely algebraic once `I` exists: `I² = 1` lets one insert `I I` between the two
copies of `C`, and the two conjugations do the rest. The symbol computation is exact — the
representative of `−z` in `(0,1]` is `1 − t`, so `b_p(1−t)² = p^t = p · b_p(t)^{−2}` — and it fails
at exactly one point, `z = 0`, whose Haar measure is zero (proved here from
`AddCircle.volume_closedBall` and `AddCircle.volume_eq_smul_haarAddCircle`, since the tree has no
`NullSingletonClass` instance for `haarAddCircle`).

**Card D status.** §1 had two components: the algebraic identity `G = C²` (equation (1)) and the
Connes–Consani statement that `|E_{m,k,p}|^{2m}` agrees with `((p−1)/p)^{2m} G^m` up to trace class.
The first is now Lean-proved. The second remains a *cited* classical input — the one-prime
decomposition of the Hankel operator `H = (1−P)M_ρ P` — and is not new content of this card.

**Elaboration trap worth recording.** `QuasiMeasurePreserving.ae` has an implicit predicate `p`;
leaving it to unification makes the elaborator diverge (1M heartbeats, ~50 s, then failure). Supply
`(p := fun y => …)` explicitly and the same proof elaborates in two seconds. Same family as the
`.comp _` higher-order unification trap already recorded for this repository.

## 2026-08-19 — entry 30: the citable form of the separation

16. `HTGeometry/GammaShiftMonomialSeparation.lean` —
    `exponent_eq_of_digamma_shift_sum_eq` and its natural-number form
    `natExponent_eq_of_digamma_shift_sum_eq`: if two exponent vectors give the same
    `∑_k e_k ψ(t+λ_k)` on a real ray, and the shifts are distinct, the vectors are equal.

Since `(∏_k Γ(s+λ_k)^{e_k})'/(∏_k Γ(s+λ_k)^{e_k}) = ∑_k e_k ψ(s+λ_k)`, this is exactly "distinct
Gamma monomials have distinct logarithmic derivatives", the statement both archimedean cards cite,
with **distinctness of the shifts as the only hypothesis**. The pair `Γ(s+α)Γ(s+β)` against
`Γ(s+α+β)Γ(s)` — which `archimedean-relative-prime-cocycle-curvature` names as the example that
defeats the leading-shape datum — is separated by it.

### Running total for this sweep

Twenty-one modules, every one `lake build`-green and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), no `sorry`/`admit`/`axiom`/`opaque`/`unsafe`, each
wired into its umbrella exactly once, the formal lint gate reporting nothing against any of them.

## 2026-08-19 — entry 31: the card-C obstruction of entry 28 was mis-stated; the route is open

The "correction to the card-C Lean model" appended above is **wrong in its key step**, and the error
is worth naming because it would stop anyone who repeated it.

I argued that the damping multiplier `m_B` must be `ΓH`-invariant, therefore "may depend on the
complement coordinates alone", therefore cannot separate two packet points sharing those
coordinates. The middle step is false. `ΓH` is a *discrete lattice*, so `ΓH`-invariance is
periodicity, not constancy along the real directions `ΓH` spans; a `ΓH`-periodic entire function is
perfectly free to separate points that differ inside those directions.

What such a multiplier genuinely cannot do is separate a packet point from a `ΓH`-translate of
itself — and that never has to happen:

17. `HTGeometry/QuasiAbelianDampedExtensionBasis.lean` —
    `AbeDampedFactorExtensionBasis`, requiring the damped lift **only for columns realizing the
    standard jet basis of the packet**. Inspecting `AbeDampedFactorExtension.jetAmpleEveryFiniteOrder`
    shows those are the only columns it ever uses, so nothing downstream is lost;
    `AbeDampedFactorExtensionBasis.jetAmpleEveryFiniteOrder`, `AbePositiveFactorTowerBasis`,
    `IsAbePositiveToruslessBasis` and its jet-ampleness theorem, plus `AbeDampedFactorExtension.toBasis`
    and `AbePositiveFactorTower.toBasis` so every prior instance survives. With the columns pinned to
    the jet basis the multiplier needs no normalisation at all: `E ≡ 1` to order `m` at the packet
    forces `E^n ≡ 1` there too, so the jet matrix of the lifted columns is the identity plus the
    remainder.

18. `HTGeometry/QuasiAbelianComplementSeparation.lean` — `packet_translate_not_congruent` and
    `packet_translate_pairwiseDistinct`: for a genuine complement (`comp` injective,
    `comp(ℤ^c) ∩ ΓH = 0`), a **nonzero** complement translate of a packet point is never
    `ΓH`-congruent to any packet point. The proof is three lines: `w_i + comp z − w_j ∈ ΓH` gives
    `w_i − w_j ∈ Γ`, which `PairwiseDistinctModulo Γ w` forbids for `i ≠ j`, while `i = j` forces
    `comp z ∈ ΓH`, hence `z = 0`.

So the damping multiplier is not obstructed. What it now has to be is explicit: an entire,
`ΓH`-periodic `E` with `E − 1` vanishing to order `> m_i` at each `w_i` and `|E|` bounded by a fixed
`ρ < 1` — indeed Gaussian-small — at every `w_i + comp z` with `z ≠ 0`. In the standard model
(`ΓH` spanned by the first coordinates, `comp` the last) it is `E = ∑_i b_i g_i`: `b_i` a
sine-ratio separator, periodic in the `ΓH` coordinates, flattened by `1 − (1 − ·)^{m+1}`; `g_i` the
corpus's flat separator times the Gaussian damping in the complement coordinate. For each pair
`i ≠ j` the difference `w_i − w_j` leaves `Γ` in one of the two groups of coordinates, and whichever
group it is supplies the vanishing factor.

## 2026-08-19 — entry 32: the reading principle on vertical rays

The archimedean boundary data live on **vertical** tubes — the real part stays fixed while the
imaginary part escapes — but every reading principle in the tree was stated along the real ray.
The ladder itself already covers vertical directions, since it holds on `Re s > 0`, `‖s‖ ≥ R`; only
the reading had to be generalized.

19. `HTGeometry/PowerExpansionAlongRay.lean` —
    `eq_zero_of_eventually_norm_le_div`,
    `power_expansion_eq_zero_ray` (descending powers independent along **any** sequence with
    `‖S n‖ → ∞`), and `log_power_expansion_eq_zero_ray` (the logarithm dies first, because
    `‖log s‖ → ∞` while every power term stays bounded once `‖s‖ ≥ 1`). Nothing in the argument uses
    the direction: peel the constant term, multiply by the variable, recurse.

20. `HTGeometry/GammaShiftSumSeparationRay.lean` —
    `ladder_moments_of_digamma_shift_sum_small_ray`,
    `eq_zero_of_digamma_shift_sum_small_ray`, `tendsto_norm_verticalRay`, `re_verticalRay`,
    `tendsto_norm_log_of_tendsto_norm`, and

    `eq_zero_of_digamma_shift_sum_small_vertical` — on the vertical line `σ + i t` with `σ > 0`,
    a combination `∑_k g_k ψ(s + λ_k)` that is eventually `O(‖s‖^{-r})` has `g = 0`, provided the
    shifts are distinct.

This is the separation in exactly the geometry the boundary datum of
`archimedean-relative-prime-cocycle-curvature` uses.

### What card B now needs, stated sharply

With the separation available in the card's own geometry, the remaining obligation can be named
precisely, and it is *not* "read the higher moments from the datum".

`HasShiftTubeDatum M lam φ d ω b c` is `c ≠ 0` together with `φ / gammaShiftShape lam σ d ω b → c`
on the tube. So the framework already has room for subleading information: one more order in `1/s`
is simply a datum with `ω` lowered. What it does not have is a proof that the *difference* obtained
after a leading-order cancellation still has a datum.

The obstruction is genuine and is not repaired by the signature alone. Within one dominant class the
ratios `R_α = ∏_k Γ(s+λ_k)^{e_α − e_β}` all tend to nonzero constants, so distinctness of their
asymptotic expansions does **not** give linear independence — `1`, `1 + 1/s`, `1 + 2/s` have
pairwise distinct expansions and satisfy `(1 + 2/s) − 2(1 + 1/s) + 1 = 0`. What is needed is the
honest statement

> **Linear independence of Gamma monomials.** If `∑_α P_α(s) ∏_k Γ(s+λ_k)^{e_{α,k}} = 0` identically,
> with the `e_α` pairwise distinct, the `λ_k` pairwise incongruent mod `ℤ`, and the `P_α` in the
> algebraic-logarithmic coefficient field, then every `P_α = 0`.

and the natural Lean route to it is by **poles, not asymptotics**: at `s = −λ_j − n` the factor
`Γ(s+λ_j)^{e_{α,j}}` contributes pole order `e_{α,j}` and, by incongruence, no other factor
interferes for large `n`; picking `α` maximizing `e_{α,j}` and reading the leading Laurent
coefficient kills `P_α`, and one iterates. That argument needs the Laurent expansion of `Γ` at its
poles and the incongruence hypothesis the card already carries — both are within reach, and neither
needs any of the transseries machinery.

## 2026-08-19 — entry 33: the signed shift-orbit obstruction, and the route to linear independence

The card-B obligation isolated in entry 32 — linear independence of Gamma monomials — has a purely
*algebraic* proof that needs no transseries at all, and its main ingredient is an asset this
repository already owns in unsigned form.

**The argument.** A Gamma monomial satisfies `M(z+1) = ρ(z) M(z)` with `ρ(z) = ∏_k (z+λ_k)^{e_k}`
rational and determined by the exponent vector. Given a relation `∑_α P_α M_α = 0`, shifting and
subtracting `ρ_{α₁}` times the original produces a strictly shorter relation, so by induction on the
number of terms one reaches `Q · M_α = 0`, hence `Q = 0`, and back-substitution needs exactly:

> no nonzero rational `P` satisfies `P(z+1)/P(z) = ∏_k (z+λ_k)^{n_k}` when some `n_k ≠ 0`.

Taking two logarithmic derivatives turns that into the shift equation
`τ(z+1) − τ(z) = −∑_k n_k (z+λ_k)^{−2}` — which is *precisely* the equation §3 of
`finite-archimedean-gamma-product-boundary-law` forbids, except that its exponents are signed.

21. `HTGeometry/SignedShiftOrbitMass.lean` — `laurentCoeff_weightedSumInvSq` and
    `not_shiftDifference_weightedSumInvSq_orbit`: the Laurent-mass computation and the obstruction
    with **arbitrary complex weights**. Nothing in the telescoping argument uses positivity; only
    the total mass on the orbit matters. Built from the exported pieces of
    `ShiftOrbitMassObstruction` (`sum_Ico_laurentCoeff_shiftDiff_eq_zero`, `laurentCoeff_sum`,
    `laurentCoeff_invSq_self`, `laurentCoeff_invSq_of_ne`, `laurentCoeff_congr`).

22. `HTGeometry/IncongruentShiftObstruction.lean` —
    `not_shiftDifference_signedInvSq_of_incongruent`: when the shifts are pairwise incongruent
    modulo `ℤ` every unit orbit carries exactly one of them, so a **single** nonzero weight already
    forbids the shift equation. This is the hypothesis both archimedean cards carry
    (`hincong`, and `primeLog_indep_mod_one` on the prime-cocycle card).

What is left on this route, in order: `deriv (logDeriv ∏_k (z+λ_k)^{n_k}) = −∑_k n_k (z+λ_k)^{−2}`
(the corpus has the multiplicity-one case, `deriv_logDeriv_prod_sub`, and `logDeriv_zpow`); the
rational-solution form, exactly as `not_rational_shiftDifference_negSumInvSq` does it for the
unsigned case; and the Casoratian induction on the number of monomials.

## 2026-08-19 — entry 34: card B, steps one and two of the linear-independence route

23. `HTGeometry/SignedShiftProductLogDeriv.lean` — `logDeriv_shift_zpow`,
    `differentiableAt_shift_zpow`, `logDeriv_zpowShiftProd`, `deriv_sum_shift_inv`,
    `deriv_logDeriv_zpowShiftProd` (`deriv (logDeriv ∏_k (z+λ_k)^{n_k}) = −∑_k n_k (z+λ_k)^{−2}`,
    integer exponents of either sign — the corpus had only the multiplicity-one case), and

    `not_shiftDifference_deriv_logDeriv_zpowShiftProd`: with pairwise incongruent shifts and one
    nonzero exponent, that second logarithmic derivative is not the unit shift difference of any
    meromorphic function with finitely many poles.

24. `HTGeometry/RationalShiftRatio.lean` — `logDeriv_congr_eventually` and the second step,

    `not_rational_shiftRatio_zpowShiftProd`: **no rational function satisfies
    `F(z+1) = (∏_k (z+λ_k)^{n_k}) F(z)`** when some exponent is nonzero and the shifts are pairwise
    incongruent mod `ℤ`. Taking one logarithmic derivative turns the relation into
    `v(z+1) − v(z) = logDeriv ρ (z)`; differentiating once more lands exactly on item 23. That
    `deriv v` is meromorphic with finitely many poles is where rationality of `F` is used —
    `MeromorphicAt.deriv` and `AnalyticAt.deriv` supply both halves.

25. `HTGeometry/GammaMonomialShift.lean` — `gammaMonomial`, `gammaMonomial_shift`,
    `gammaMonomial_shift_of_re`, `gammaMonomial_ne_zero`, `re_pos_of_gt_sum_abs`. The bridge:
    `M_n(s+1) = (∏_k (s+λ_k)^{n_k}) M_n(s)`. The identity needs the arguments to miss the poles of
    `Γ` and the origin, which a right half plane arranges uniformly — note this is *not* a cofinite
    condition, since the poles of `Γ` are infinite in number, and that is the one place where the
    argument has to leave the cofinite filter.

### The remaining step, precisely

To conclude `¬ ∃ rational F with M_n = F`, the half-plane identity of item 25 has to be transported
to the cofinite identity item 24 consumes. Both sides of
`y(z+1) − y(z) = deriv (logDeriv ρ) z` are analytic off a finite set, the complement of a finite set
in `ℂ` is open and connected, and the two agree on a half plane minus finitely many points; the
identity theorem then gives agreement on the whole domain, hence cofinitely. After that,
linear independence of Gamma monomials follows by the shift-and-subtract induction on the number of
terms, whose base case is exactly "no nontrivial monomial is rational".

## 2026-08-19 — entry 35: a nontrivial Gamma monomial is never rational

The transfer named at the end of entry 34 is done, and with it the base case of the linear
independence of Gamma monomials.

26. `HTGeometry/AnalyticCofiniteTransfer.lean` — `isPreconnected_compl_finite` (the complement of a
    finite set in `ℂ` is preconnected, because `ℂ` has real rank two) and
    `eventuallyEq_cofinite_of_analytic_compl_finite`: two functions analytic off a finite set that
    agree on a nonempty open piece of the complement agree **cofinitely**. This is the identity
    theorem, and it is what moves the Gamma functional equation off the half plane, where it lives,
    onto the cofinite filter, where the orbit-mass obstruction can see a whole orbit `a + ℤ`.

27. `HTGeometry/GammaMonomialNotRational.lean` — `analyticAt_shift_zpow`, `analyticAt_polyEval`, and

    `not_rational_gammaMonomial` : **`∏_k Γ(s+λ_k)^{n_k}` is not a rational function**, when the
    shifts are pairwise incongruent modulo `ℤ` and some exponent is nonzero.

28. `HTGeometry/GammaMonomialPairIndependence.lean` — `gammaMonomial_sub`,
    `gamma_ne_zero_of_gt_sum_abs`, and

    `not_rational_gammaMonomial_ratio` : **two distinct Gamma monomials are not proportional over
    the rational function field**.

This is exactly the separation `archimedean-relative-prime-cocycle-curvature` says the leading shape
cannot supply. Its own example, `Γ(s+α)Γ(s+β)` against `Γ(s+α+β)Γ(s)`, shares degree, weighted
shift and leading constant; the two are separated here because their *ratio* is a nontrivial Gamma
monomial, and a nontrivial Gamma monomial is not rational.

The chain, end to end and with no analytic estimate anywhere in it:

```text
Γ(z+1) = z Γ(z)                            gammaMonomial_shift_of_re
  ⟹  M(s+1) = (∏_k (s+λ_k)^{n_k}) M(s)     on a right half plane
  ⟹  a rational M would satisfy that shift relation      (identity theorem: entry 26)
  ⟹  logDeriv twice: τ(z+1) − τ(z) = −∑_k n_k (z+λ_k)^{−2}   entries 23, 24
  ⟹  zero orbit mass at the orbit of −λ_{k₀}             entries 21, 22
  ⟹  n_{k₀} = 0.
```

What remains for the full linear independence is the shift-and-subtract induction on the number of
monomials, whose base case is exactly item 27.

## 2026-08-19 — entry 36: linear independence of Gamma monomials is proved

29. `HTGeometry/GammaMonomialClearedFactor.lean` — `clearedShiftFactor`,
    `eval_clearedShiftFactor`, `clearedShiftFactor_ne_zero`, `exists_clearing_power`. Multiplying
    the shift factor `ρ_e(s) = ∏_k (s+λ_k)^{e_k}` by `∏_k (s+λ_k)^m` for one `m` large enough for
    the whole finite family makes every factor a polynomial at once. That is what keeps the
    shift-and-subtract induction inside polynomial coefficients.

30. `HTGeometry/GammaMonomialLinearIndependence.lean` — `eval_comp_X_add_one`, `shiftEliminate`,
    `shiftEliminate_self`, `polynomial_eq_zero_of_half_plane`, and

    `gammaMonomial_linearIndependent` : **if `∑_α R_α(s) ∏_k Γ(s+λ_k)^{e_{α,k}} = 0` on a right
    half plane, with polynomial `R_α` and pairwise distinct exponent vectors, then every
    `R_α = 0`** — assuming only that the shifts are pairwise incongruent modulo `ℤ`.

The elimination is the classical one, arranged so that no rational-function machinery is needed.
From the relation and its shift by one, the combination

`C_β = R_{α₀}(X+1)·A_{α₀}·R_β − R_{α₀}·R_β(X+1)·A_β`,  `A_β = clearedShiftFactor lam (e β) m`,

kills the distinguished index identically (`shiftEliminate_self`) and leaves a relation over one
fewer monomial, whose coefficients are again polynomials. The induction hypothesis forces `C_β = 0`,
and that polynomial identity says exactly that the rational function `R_β / R_{α₀}` has shift ratio
`∏_k (s+λ_k)^{e_{α₀,k} − e_{β,k}}` — forbidden by `not_rational_shiftRatio_zpowShiftProd` for
distinct exponent vectors. So every `R_β` with `β ≠ α₀` vanishes, the relation collapses to a single
term, and `polynomial_eq_zero_of_half_plane` finishes it.

### Card B: the three named steps of entry 33 are all closed

```text
deriv logDeriv of a signed product      entry 34, item 23
the rational-solution form              entry 34, item 24
the shift-and-subtract induction        entry 36, item 30
```

What remains on `archimedean-relative-prime-cocycle-curvature` is the re-fitting of
`GammaJetNormalFormDatum`: its `HasShiftTubeDatum` records only `(degree, ω, b, c)`, and the
`hclass` hypothesis of `exists_hasShiftTubeDatum_gammaCoeffSum` asks for the sum of constants over
the dominant class to be nonzero. Linear independence is what makes that hypothesis *derivable*
rather than assumed, because a vanishing class sum would exhibit a nontrivial relation among the
monomials of that class.

### A tactic note

`linear_combination` failed on goals whose atoms are `Finset.prod` terms with `zpow` exponents,
where a plain `calc` with `ring` on each step succeeded. When `linear_combination h` reports "ring
expressions not equal" but the identity is a visible rearrangement, split it into `ring` steps
around the hypothesis rather than searching for the right coefficient.

## 2026-08-19 — entry 37: independence over the rational functions

31. `HTGeometry/GammaMonomialRationalIndependence.lean` — `exists_threshold_above_roots` (a nonzero
    polynomial is nonvanishing on a far enough right half plane) and

    `gammaMonomial_linearIndependent_rat` : the same independence with **rational** coefficients,
    which is the form a normal-form element of a shifted Gamma field actually has.

The reduction is clearing denominators, and the one thing it costs is moving the half plane to the
right of every root of `∏_β Q_β`; `gammaMonomial_linearIndependent_of_threshold` (the same induction
stated at an arbitrary threshold `Rb ≥ ∑_j |Re λ_j|`) is what makes that free. The identity genuinely
fails at the roots of the denominators, so the threshold cannot be avoided by working cofinitely.

### Running total for this sweep

Thirty-seven modules, each `lake build`-green and axiom-clean
(`[propext, Classical.choice, Quot.sound]`), no `sorry`/`admit`/`axiom`/`opaque`/`unsafe`, each
wired into its umbrella exactly once, the formal lint gate reporting nothing against any of them.

## 2026-08-19 — entry 38: the step bound of the Gamma-monomial-ratio ladder

The datum refit needs the subleading behaviour of a Gamma-monomial ratio inside a dominant class.
That ratio satisfies an exact functional equation, `R(s+1) = ρ_g(s) R(s)` with `ρ_g` **rational**, so
the same telescope that produced the Stirling ladder applies — no integration of a logarithmic
derivative is needed. Two modules supply the step bound.

32. `HTGeometry/RationalVanishingOrderBound.lean` — `exists_radius_norm_polyEval_ge` and
    `exists_norm_polyEval_div_le_of_dvd`: if `X^N ∣ P` and `Q(0) ≠ 0` then
    `‖P(u)/Q(u)‖ ≤ C‖u‖^N` on a small enough disc. This generalizes
    `exists_norm_polyEval_div_pow_le_of_dvd`, whose denominator had to be `(1+u)^k`; the shift ratio
    produces an arbitrary denominator that is merely nonzero at the origin, bounded below there by
    its own value.

33. `HTGeometry/ShiftRatioExpansion.lean` — `coeff_one_mul`, `coeff01_shift_pow`,
    `coeff01_prod_shift`, `prod_zpow_const`, `zpow_eq_toNat_div`, `shiftNumer`, `shiftDenom`,
    `X_sq_dvd_shiftNumer_sub_shiftDenom`, and

    `exists_norm_shiftRatio_sub_one_le` : with `∑_k g_k = 0` and `∑_k g_k λ_k = 0` — exactly the
    two conditions defining a dominant class —

    `‖∏_k (s+λ_k)^{g_k} − 1‖ ≤ K/‖s‖²`.

The proof is the numerator/denominator split at `u = 1/s`: `∏_k (1+λ_k u)^{g_k} = P(u)/Q(u)` with
`P`, `Q` products of `(1 + λ_k X)^{n}`, both with constant term `1`, and with equal degree-one
coefficients precisely when `∑_k g_k λ_k = 0`. So `X² ∣ P − Q`, and item 32 finishes it.

### What the ladder still needs

`R(s+1) − R(s) = (ρ_g(s) − 1) R(s)`, so with the bound above the telescope
`norm_le_of_step_bound_ge` gives `R(s) = C + O(1/s)` **as soon as `R` is bounded** on the half plane.
Boundedness along a single orbit is immediate from the functional equation
(`∏_j (1 + K/‖s+j‖²)` converges); uniform boundedness on the half plane needs a bound on one
fundamental strip, which is where the corpus's `gammaLine` estimates have to be brought in. After
that the rungs proceed exactly as in the Stirling ladder, with the coefficients forced at each order.

## 2026-08-19 — entry 39: the strip bound was already in the corpus

Entry 38 ended by saying the ratio ladder still needs "a bound on one fundamental strip, which is
where the corpus's `gammaLine` estimates have to be brought in". That understated what the corpus
already has: `hasShiftTubeDatum_gammaProd` gives the boundary datum of a Gamma monomial on every
vertical tube, with constant exactly `1`. Two monomials in the same dominant class have the *same*
shape, so their ratio is a quotient of two things tending to `1`.

34. `HTGeometry/GammaProdRatioTubeLimit.lean` —

    `tubeLimit_gammaProd_ratio` : if `∑_i e_i = ∑_i f_i` and `∑_i e_i λ_i = ∑_i f_i λ_i`, then
    `(∏_i Γ(σ+λ_i+it)^{e_i}) / (∏_i Γ(σ+λ_i+it)^{f_i}) → 1` uniformly on every tube.

Four lines of actual content: rewrite the second datum along the two class equalities so the shapes
coincide, divide, and cancel the shape with `field_simp` where it is nonzero (`t ≥ 3`).

**Two corrections to earlier entries.** `TubeLimit.inv` (`UniformDominantRatio`) and `TubeLimit.div`
(`UniformGammaFieldDatum`) already exist; I wrote both before the "already declared" error caught it.
And the strip bound named as missing in entry 38 is not missing — it is one rewrite away from the
corpus's own monomial datum.

### Card B, what is left after this

With the ratio bounded (indeed convergent to `1`) on tubes and
`exists_norm_shiftRatio_sub_one_le` giving `‖ρ_g(s) − 1‖ ≤ K/‖s‖²`, the step difference
`R(s+1) − R(s) = (ρ_g(s) − 1)R(s)` is `O(‖s‖^{-2})`, so `norm_le_of_step_bound_ge` yields
`R(s) = 1 + O(1/s)`. The remaining work is bookkeeping of the same kind as the Stirling ladder:
the rungs at each order, then the datum refit that reads the first nonvanishing coefficient.

## 2026-08-19 — entry 40: the orbit bound, and what the ratio ladder still needs

35. `HTGeometry/GammaMonomialOrbitBound.lean` — `gammaMonomial_shift_nat` (iterating the functional
    equation: `M(s+n) = (∏_{j<n} ρ_g(s+j))·M(s)`), `two_mul_norm_add_natCast_sq_ge`
    (`(‖s‖+j)² ≤ 2‖s+j‖²` on the right half plane), and

    `exists_prod_norm_shiftRatio_le` : `‖∏_{j<n} ρ_g(s+j)‖ ≤ e^{4K}` for every `n`, uniformly on
    `‖s‖ ≥ max(R₀,1)`.

    The exponents sum to `K ∑_j ‖s+j‖^{-2} ≤ 2K ∑_j (‖s‖+j)^{-2} ≤ 2K(‖s‖^{-2} + ‖s‖^{-1}) ≤ 4K`,
    the middle step being the corpus's `sum_inv_sq_shift_head_le`. So a Gamma monomial in a dominant
    class is bounded along every orbit by a constant times its value at the base point.

### The remaining gap in the ratio ladder, stated exactly

`norm_le_of_step_bound_ge` needs a **single** function `L = R − C`, so the limit `C` must not depend
on the orbit. Two of the three ingredients are in place:

* on any tube `0 < σ ≤ M`, `R → 1` as `t → ∞` (`tubeLimit_gammaProd_ratio`);
* along any orbit, `R(s+n) = R(s)·∏_{j<n} ρ_g(s+j)` with the product bounded (item 35) and
  `∑_j ‖ρ_g(s+j) − 1‖` convergent, so the orbit limit `C(s) := lim_n R(s+n)` exists.

What is missing is that `C ≡ 1`. `C` is `1`-periodic and, by locally uniform convergence of the
product, analytic in `s`; the tube limit gives `C = 1` wherever `|Im s|` is large; the identity
theorem then forces `C ≡ 1`. Formalizing that needs the locally uniform convergence of
`∏_{j} ρ_g(s+j)` — which the bound of item 35 already supplies pointwise — upgraded to analyticity
of the limit, i.e. one application of the corpus's `SummableLocallyUniformlyOn` machinery in
multiplicative form.

After that the rungs proceed exactly as in the Stirling ladder.

## 2026-08-19 — entry 41: the orbit Cauchy estimate

36. `HTGeometry/GammaMonomialOrbitCauchy.lean` —

    `exists_norm_gammaMonomial_orbit_sub_le` : `‖M(s+n) − M(s)‖ ≤ A·‖M(s)‖/‖s‖` for **every** `n`,
    uniformly on `‖s‖ ≥ Rb`, for a Gamma monomial in a dominant class.

Telescoping the functional equation gives `M(s+n) − M(s) = ∑_{j<n} (ρ_g(s+j) − 1) M(s+j)`; each
summand is `O(‖s+j‖^{-2})` times the orbit bound of item 35, and `∑_j ‖s+j‖^{-2} = O(1/‖s‖)`. So the
orbit limit exists **with a rate**: letting `n → ∞`,

`‖C(s) − M(s)‖ ≤ A ‖M(s)‖ / ‖s‖`,   `C(s) := lim_n M(s+n)`.

### The one remaining link, restated after this

Everything the ratio ladder needs is now proved except `C ≡ 1`, and the shape of that obstruction is
worth stating plainly, because two natural routes do **not** close it.

* Applying the Cauchy bound at `s+m` and letting `m → ∞` only re-derives the definition of `C`.
* The tube limit gives `M(σ+it) → 1` as `t → ∞` for bounded `σ`, hence `C(σ+it) → 1`; but that is a
  limit in `t`, not an identity, and `C` is constant along orbits, which move in `σ`.

What does close it: `C` is `1`-periodic, and analytic (it is `M(s) + ∑_{j≥0} (ρ_g(s+j) − 1) M(s+j)`,
a locally uniformly convergent series of analytic functions — the bound of item 36 is exactly the
domination needed). A `1`-periodic analytic function on a right half plane descends through
`q = e^{2πis}` to `ℂ∖{0}`, and the tube limits at `t → ±∞` say it extends holomorphically to both
`q = 0` and `q = ∞` with value `1`; so it is constant. Formalizing that needs the descent and two
removable-singularity arguments — the only genuinely new analytic step left on this card.

## 2026-08-19 — entry 42: the monomial is analytic on the half plane

37. `HTGeometry/GammaMonomialAnalytic.lean` — `analyticAt_Gamma_of_re_pos`,
    `analyticAt_Gamma_shift_zpow`, `analyticAt_gammaMonomial`,
    `analyticAt_gammaMonomial_of_gt_sum_abs`.

`Γ` is differentiable off its poles, hence analytic and nonvanishing on `{Re z > 0}`; integer powers
and finite products preserve both. This is the first half of the periodicity argument: the orbit
limit `C(s) = M(s) + ∑_{j≥0} (ρ_g(s+j) − 1) M(s+j)` is a series of analytic functions dominated,
by entry 41, by `A‖M(s)‖ ‖s+j‖^{-2}` locally uniformly, so `C` is analytic.

### Status of the ratio ladder

Proved: the step bound (entry 38), the tube limit (entry 39), the orbit bound (entry 40), the orbit
Cauchy estimate (entry 41), analyticity of the monomial (entry 42). What remains is exactly the
identification `C ≡ 1`, by the descent `q = e^{2πis}` and removable singularities at `q = 0, ∞`.
Note this is *not* a formality: the two shortcuts one would try — applying the Cauchy bound further
along the orbit, or reading the tube limit at a fixed height — both fail, the first because it only
restates the definition of `C`, the second because the tube threshold `T` depends on the abscissa
bound and so degrades as one moves along the orbit.

## 2026-08-19 — entry 43: the crux lemma, by maximum modulus rather than descent

Entry 42 said `C ≡ 1` needed "the descent `q = e^{2πis}` and removable singularities at `q = 0, ∞`".
It does not. The maximum modulus principle applies directly on the half plane, and periodicity is
needed only to move an arbitrary point into a fixed compact block.

38. `HTGeometry/PeriodicHalfPlaneVanishing.lean` — `periodic_shift_nat`,
    `periodic_shift_nat_sub`, `exists_block_translate` (every point of the half plane has a translate
    with the same value in the block `R₀+1 ≤ Re s ≤ R₀+3`, reached by shifting up past `R₀+2` and
    then down), `isCompact_vertical_block`, and

    `eq_zero_of_periodic_of_vertical_decay` : a `1`-periodic function differentiable on
    `{Re s > R₀}` whose norm tends to `0` as `|Im s| → ∞`, uniformly in `Re s`, is identically zero.

The argument: if `F s₁ ≠ 0`, set `ε = ‖F s₁‖/2`; the decay hypothesis confines `|Im s₁|` and puts a
translate of `s₁` in the compact block `K`, so the maximum of `‖F‖` over `K` exceeds `ε`. That
maximum dominates `‖F‖` everywhere — off the block by the decay, on it by translating back — so it
is a global maximum at an interior point of the half plane, which is convex, hence preconnected.
`Complex.eqOn_of_isPreconnected_of_isMaxOn_norm` makes `F` constant, and the decay makes that
constant `0`, contradicting `‖F z‖ > ε`.

### What `C ≡ 1` now needs

Only the two hypotheses of item 38, for `F = C − 1`:

* **differentiability**: `C(s) = M(s) + ∑_{j≥0} (ρ_g(s+j) − 1) M(s+j)`, a series of analytic
  functions (entry 42) dominated locally uniformly by `A‖M(s)‖‖s+j‖^{-2}` (entry 41);
* **vertical decay**: from `‖C(s) − M(s)‖ ≤ A‖M(s)‖/‖s‖` (entry 41) together with the tube limit
  (entry 39), which is uniform in `σ` over one period and extends to all `σ` by periodicity.

## 2026-08-19 — entry 44: a general locally uniform M-test

39. `HTGeometry/LocallyUniformMTest.lean` —

    `summableLocallyUniformlyOn_of_locally_bounded` : a summable dominating bound valid on a
    neighbourhood of each point gives `SummableLocallyUniformlyOn`.

`tendstoUniformlyOn_tsum` is mathlib's M-test for a bound uniform on the whole set. Local normal
convergence only needs one near each point, which is the situation for the series defining the orbit
limit of a Gamma monomial: the dominating constant there depends on the distance to the boundary of
the half plane. The corpus had several bespoke local-normal-convergence bridges
(`summableLocallyUniformlyOn_of_polynomialGaussianLattice_bound`,
`summableLocallyUniformlyOn_primeLogHerglotz_on_off_poles`, and others) but no general one.

With this, the differentiability half of `C ≡ 1` is a direct application: on a ball around any
`s₀` in the half plane, `‖(ρ_g(s+j) − 1) M(s+j)‖ ≤ A·sup_ball‖M‖·2/(r + j)²`, which is summable.

## 2026-08-19 — entry 45: the orbit series

40. `HTGeometry/GammaMonomialOrbitLimit.lean` — `orbitTerm`,
    `gammaMonomial_orbit_telescope` (`M(s+n) = M(s) + ∑_{j<n} orbitTerm j`), and

    `summable_orbitTerm` : the orbit series is absolutely summable on `‖s‖ ≥ Rb`, with the explicit
    majorant `2K·B·‖M(s)‖ · (j+1)^{-2}`.

So the orbit limit is the honest series `C(s) = M(s) + ∑'_j orbitTerm lam g s j`, and `M(s+n) → C(s)`
is the convergence of its partial sums.

### The path from here, module by module

1. `tendsto_gammaMonomial_orbit` — partial sums of a summable series converge; one line from item 40.
2. `C` is `1`-periodic — `C(s+1) = C(s)`, by reindexing the series (or by uniqueness of the orbit
   limit).
3. `C` is differentiable on the half plane — `summableLocallyUniformlyOn_of_locally_bounded`
   (entry 44) with the majorant of item 40 on a ball, plus `analyticAt_gammaMonomial` (entry 42).
4. `‖C(s) − 1‖ → 0` as `|Im s| → ∞`, uniformly in `Re s` — from `‖C(s) − M(s)‖ ≤ A‖M(s)‖/‖s‖`
   (entry 41) and the tube limit (entry 39), uniform over one period and extended by periodicity.
5. `C ≡ 1` — `eq_zero_of_periodic_of_vertical_decay` (entry 43) applied to `C − 1`.
6. `M(s) = 1 + O(1/‖s‖)` — `norm_le_of_step_bound_ge` with `L = M − 1`, whose anchor is item 5.
7. The rungs, exactly as in the Stirling ladder, and then the datum refit.

## 2026-08-19 — entry 46: steps 1, 2 and the limit form of the Cauchy bound

41. `HTGeometry/GammaMonomialOrbitLimitValue.lean` — `gammaMonomialOrbitLimit`,
    `tendsto_gammaMonomial_orbit` (the series really is the limit along the orbit), and
    `gammaMonomialOrbitLimit_shift` (**`C(s+1) = C(s)`**, by uniqueness of limits: the shifted
    sequence is a tail of the original).

42. `HTGeometry/GammaMonomialOrbitLimitBound.lean` — `norm_gammaMonomialOrbitLimit_sub_le`:
    `‖C(s) − M(s)‖ ≤ A‖M(s)‖/‖s‖`, the Cauchy estimate of entry 41 passed to the limit.

That is steps 1 and 2 of the path in entry 45, together with the quantitative input of step 4.
Remaining on that path: differentiability of `C` (step 3, a direct application of the M-test of
entry 44 with the majorant of entry 45), the vertical decay of `C − 1` (step 4, from item 42 above
and the tube limit of entry 39), then `C ≡ 1` (step 5, entry 43), the first rung (step 6), the
higher rungs, and the datum refit.

## 2026-08-19 — entry 47: the explicit majorant for the M-test

43. `HTGeometry/GammaMonomialOrbitMajorant.lean` — `exists_orbitTerm_majorant`
    (`‖orbitTerm lam g s j‖ ≤ D·‖M(s)‖·(j+1)^{-2}`, with the base-point dependence isolated into the
    single factor `‖M(s)‖`) and `summable_inv_succ_sq`.

`summable_orbitTerm` (entry 45) proves summability; the locally uniform M-test needs the majorant
itself, in a form where the only `s`-dependence is a factor that is bounded on any compact. That is
what this supplies, so step 3 of the path (differentiability of `C`) is now: cover a point of the
half plane by a closed ball inside it, bound `‖M‖` on that ball by compactness, and feed
`D·(sup ball ‖M‖)·(j+1)^{-2}` to `summableLocallyUniformlyOn_of_locally_bounded`.

A tactic note, second instance of the same shape: `nlinarith` failed on
`(2K·a)·c ≤ (2K·b)·c` from `a ≤ b`, `c ≥ 0`, `2K ≥ 0`, where
`mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left · ·) ·` closes it immediately. On monotone
rearrangements of products, name the monotonicity lemma rather than calling a solver.

## 2026-08-19 — entry 48: the half-plane boundary law is proved

44. `HTGeometry/GammaMonomialOrbitAnalytic.lean` — `analyticAt_orbitFactor`,
    `analyticAt_gammaMonomial_shift`, `analyticAt_orbitTerm`,
    `differentiableOn_gammaMonomialOrbitLimit`.
45. `HTGeometry/GammaMonomialStripLimit.lean` — `gammaMonomial_conj`, `toNat_sub_toNat_neg`,
    `gammaProd_ratio_eq_gammaMonomial`, `exists_strip_gammaMonomial_sub_one`.
46. `HTGeometry/GammaMonomialHalfPlaneLimit.lean` — `gammaMonomialOrbitLimit_eq_one`,
    **`exists_norm_gammaMonomial_sub_one_le`**.

The theorem: for real nonnegative shifts `λ` and integer exponents `g` with `∑ g = 0` and
`∑ g_i λ_i = 0`,

```text
∃ A R₀, ∀ s, R₀ < Re s → ‖∏ Γ(s + λ_i)^{g_i} − 1‖ ≤ A / ‖s‖.
```

The corpus's tube framework gives this only on a **bounded** vertical strip `0 < σ ≤ M`; the content
here is that it holds on the whole half plane, uniformly, with no upper bound on `Re s`.

The mechanism, now complete in Lean:
1. `C(s) := lim_n M(s + n)` exists (orbit series, entry 45), is `1`-periodic (entry 45),
   is differentiable (item 44 above), and satisfies `‖C − M‖ ≤ A‖M‖/‖s‖` (entry 46).
2. On a bounded strip the tube limit gives `M → 1` at height infinity (item 45 above). The
   two-sided statement comes from `Γ(conj z) = conj Γ(z)` with real shifts, so only the
   one-sided tube limit is needed.
3. `C − 1` is differentiable, `1`-periodic, and — by translating any point into the block
   `R₀+1 ≤ Re s ≤ R₀+3` via `exists_block_translate` — decays at height infinity **uniformly in
   `Re s`**. `eq_zero_of_periodic_of_vertical_decay` then forces `C ≡ 1`.
4. Feeding `C ≡ 1` back into `‖C − M‖ ≤ A‖M‖/‖s‖` bounds `‖M‖ ≤ 2` and yields `‖M − 1‖ ≤ 2A/‖s‖`.

Steps 1–6 of the path recorded in entry 45 are therefore closed. Note the direction of the argument:
periodicity converts a strip estimate into a half-plane estimate, which is exactly the step the tube
formalism cannot take on its own.

## 2026-08-19 — entry 49: opening the all-orders transseries model

47. `HTGeometry/GammaMonomialLogDeriv.lean` — `gamma_shift_ne_zero_of_re_pos`,
    `logDeriv_Gamma_zpow`, `logDeriv_Gamma_shift_zpow`, `differentiableAt_Gamma_shift_zpow`,
    `logDeriv_gammaMonomial`, `deriv_gammaMonomial` (`M' = L·M` with `L = ∑ g_k ψ(·+λ_k)`).
48. `HTGeometry/RayIntegralDecay.lean` — `integral_inv_sq_shift_le`, `norm_add_real_ge_half`,
    **`norm_le_of_deriv_decay`**: `f` analytic on a right half plane, `‖f'‖ ≤ A‖s‖^{−(k+2)}`, and
    `f → 0` along every horizontal ray ⟹ `‖f‖ ≤ 2^{k+2}A‖s‖^{−(k+1)}`.

### Why this is the next brick, and what it is for

Reading the two consumer theorems settled the architecture question. `zeta_no_gammaShift_relation`
needs, for each coefficient, a limit `F_α(σ+it)/gammaShiftShape → c_α ≠ 0`, and the shape is
`Γ(σ+λ+it)^d · s^ω · (log s)^b` with **real** `ω`. So a `1/s` correction is a shape with `ω` one
lower: the hierarchy is graded by powers of `1/s`, and reading a datum past a leading cancellation
means knowing the expansion to that order.

`GammaJetNormalFormDatum` uses `NoIntegerRelation` in exactly one place — to prove the dominant
class is a singleton. Under the card's own `primeLog_indep_mod_one` the class condition collapses to
*equal degree and equal first moment*, so within a class every ratio `M_α/M_β` is a **balanced**
monomial. Entry 48 proves each such ratio tends to `1`; what a datum needs is the first nonvanishing
coefficient of its expansion in `1/s`. The card's own example `Γ(s+α)Γ(s+β)` against
`Γ(s)Γ(s+α+β)` is exactly this: the ratio is balanced, the leading terms cancel, and the true
datum sits one power of `1/s` down, at a coefficient proportional to `∑ g_k λ_k² = 2αβ ≠ 0`.

So the class sum **can** vanish — `hclass` is not provable as stated — and the honest route is the
all-orders expansion. Its three ingredients: the ladder (`ψ(s+μ)` to every order, already owned),
`M' = L·M` (item 47), and the constant of integration, which is `C ≡ 1` (entry 48) — the part that
looked hardest and is already done. Item 48 is the analytic step that turns an expansion of the
logarithmic derivative into one of the function: integrate along a horizontal ray, using
`‖s+x‖ ≥ (‖s‖+x)/2` and `(‖s‖+x)^{k+2} ≥ ‖s‖^k(‖s‖+x)^2` so that only `∫₀^∞ (a+x)^{-2} = 1/a` is
ever needed — no Euler–Maclaurin, no Bernoulli numbers.

## 2026-08-19 — entry 50: the forced inverse-power ladder

49. `HTGeometry/GammaMonomialDigammaSum.lean` — `balancedLadderCoeff`,
    `shiftLadderCoeff_zero_eq`, `balancedLadderCoeff_zero`,
    `exists_norm_logDeriv_gammaMonomial_expansion`: for `∑ g = 0`,
    `∑_k g_k ψ(s+λ_k) = −∑_{m<M} D_m s^{−(m+1)} + O(‖s‖^{−(M+1)})` with `D_m = ∑_k g_k d_m(λ_k)`,
    and `D_0 = 0` as soon as the first moment vanishes (`d_0` has degree one).
50. `HTGeometry/TruncatedInverseSeries.lean` — `truncSeries`, `truncSeries_eq_head_add`,
    `hasDerivAt_truncSeries`, `analyticAt_truncSeries`, `tendsto_norm_shift_ray`,
    `tendsto_truncSeries_ray`.
51. `HTGeometry/InverseSeriesLadder.lean` — `lamPoly`, `expLadderCoeffOf`, `expPoly`, `resPoly`,
    `lamPoly_succ`, `X_dvd_lamPoly`, `coeff_one_lamPoly`, `coeff_zero_expPoly`, `resPoly_succ`,
    **`X_pow_dvd_resPoly`**.

### The change of variable that makes the expansion a ladder

Writing `u = 1/s`, the equation `M' = L·M` becomes `u²P'(u) = −Λ(u)P(u)` with
`Λ(u) = −∑ D_m u^{m+1}`. So the object to construct is a polynomial `P_N` whose **residual**
`Λ_N·P_N + X²·P_N'` is divisible by `X^{N+2}` — a statement entirely inside `ℂ[X]`, with no
analysis in it at all.

Adding `c_N X^{N+1}` to `P_N` moves the degree-`(N+2)` coefficient of the residual by exactly
`(N+1)c_N` and moves nothing lower: the cross term `Λ_N·c_N X^{N+1}` contributes
`c_N·(Λ_N).coeff 1 = −c_N D_0 = 0`, and extending the truncation of `Λ` changes it only in degree
`N+2` and above. So one coefficient per step is forced, with divisor `N+1 ≠ 0` — the same shape as
the Stirling ladder of entries 25–30, and it needs no antidiagonal convolution.

That is the whole combinatorial content of the transseries model. What remains is analytic:
transport `X^{N+2} ∣ resPoly` to a bound on `‖M − P_N(1/s)‖` by induction, each step running
`norm_le_of_deriv_decay` (entry 49) once.

## 2026-08-19 — entry 51: the transseries model is proved

52. `HTGeometry/PolynomialInverseEval.lean` — `hasDerivAt_polyEval_inv`,
    `differentiableAt_polyEval_inv`, `analyticAt_polyEval_inv`, `tendsto_polyEval_inv_ray`,
    `norm_polyEval_inv_le`.
53. `HTGeometry/GammaMonomialExpansion.lean` — `gammaLadderCoeff`, `gammaExpPoly`,
    `eval_lamPoly_inv`, `eval_zero_expPoly`, `exists_tendsto_gammaMonomial_ray`,
    **`exists_norm_gammaMonomial_expansion`**.
54. `HTGeometry/InverseSeriesFirstCoefficient.lean` — `coeff_lamPoly`, `natDegree_expPoly_le`,
    `expCoeffSeq`, `expPoly_succ_eq`, `expPoly_eq_one_of_coeffs`,
    `forall_eq_zero_of_expPoly_eq_one`, `exists_first_expCoeffSeq_ne_zero`.
55. `HTGeometry/GammaMonomialLeadingDeviation.lean` — `exists_gammaLadderCoeff_ne_zero`,
    **`exists_gammaMonomial_leading_deviation`**.

The two theorems:

```text
∀ N, ∃ A R₀, ∀ s with Re s > R₀ :
    ‖∏ Γ(s+λ_k)^{g_k} − P_N(1/s)‖ ≤ A/‖s‖^{N+1},        P_N = expPoly (ladder moments) N

and, when g ≠ 0 and the shifts are distinct,
∃ m c A R₀,  c ≠ 0  ∧  ∀ s with Re s > R₀ :
    ‖∏ Γ(s+λ_k)^{g_k} − 1 − c·s^{−(m+1)}‖ ≤ A/‖s‖^{m+2}.
```

The second is the statement the card asks for: the **exact** leading deviation of a nontrivial
balanced monomial from `1`, with a nonzero constant, which is precisely a boundary datum for
`M − 1`. Its proof chains: if every ladder coefficient vanished then the residual would be the
truncated moment series itself, whose divisibility forces every moment `D_m` to vanish, and then
the corpus's Vandermonde separation `eq_zero_of_ladder_moments_vanish` forces `g = 0`.

So the card's example `Γ(s+α)Γ(s+β)` versus `Γ(s)Γ(s+α+β)` is fully resolved in Lean: the ratio is
balanced, tends to `1`, and its deviation has an exact nonzero leading coefficient at some finite
order.

### What the datum refit still needs, stated exactly

`Φ = ∑_α Q_α M_α`. Dividing by the dominant monomial makes every in-class ratio `R_α` balanced with
`R_β = 1`, so `Φ/M_β = (∑_α Q_α) + ∑_α Q_α(R_α − 1)`, and every summand now has a datum — the first
from `exists_hasShiftTubeDatum_jetFieldPolyFun`, the rest from item 55 above. If the maximal class
of *that* collection has nonzero constant sum, the datum follows. If not, the process must recurse,
and termination is a genuine statement, not bookkeeping:

> the map from the exponent lattice to `1 + uℂ[[u]]`, `α ↦ (expansion of R_α)`, is an **injective
> character** of a free abelian group into the units of a field of formal transseries.

Injectivity is exactly item 55. Given it, Dedekind's independence of characters makes the `R_α`
linearly independent over the coefficient field, so the total expansion of `Φ/M_β` is nonzero and
its first nonvanishing coefficient is the datum. Completing this needs the coefficient side too:
the transseries of `jetFieldPolyFun`, i.e. of `ψ^{(k)}(s+λ)` for every `k`.

A route that does **not** work, recorded so it is not retried: obtaining the `ψ^{(k)}` expansions
from the `ψ` expansion by Cauchy's estimate. On a half plane the distance to the boundary does not
grow with `‖s‖`, so the estimate gives no gain in the exponent. Each `ψ^{(k)}` needs its own ladder,
built from `ψ^{(k)}(z+1) = ψ^{(k)}(z) + (−1)^k k!/z^{k+1}` — the same architecture as the shifted
ladder, and with no `log` term for `k ≥ 1`.

## 2026-08-19 — entry 52: the corpus already owns the transfer layer; the refit has a route

Searching before building (again) changed the plan. The corpus already contains, axiom-clean:

```text
HTGeometry/RatApproximant.lean        HasRatApprox f  — on every tube, to every order in the
                                      height, f is a quotient of polynomials up to C/t^N;
                                      closed under +, −, ·
HTGeometry/LogRatApproximant.lean     HasLogRatApprox f — same with logarithmic polynomials;
                                      closed under +, −, ·; HasRatApprox.hasLogRatApprox
HTGeometry/ShiftedJetFieldDatum.lean  hasLogRatApprox_jetFieldPolyFun  — EVERY jet polynomial
                                      exists_hasShiftTubeDatum_of_logRatApprox — a log-rational
                                      approximant that is not vertically negligible HAS a datum
HTGeometry/AsymptoticExpansionAlgebra.lean
                                      IsAsymptoticExpansion + the algebra + the transfer
                                      aeval_powerSeries_eq_zero_of_eq_zero
HTGeometry/ShiftedDigammaExpansionVertical.lean
                                      exists_iteratedDeriv_digamma_shift_expansion — every
                                      polygamma jet of every real shift, to every order
```

So the polygamma ladders I was about to build already exist, and the coefficient side of the datum
is entirely handled by an approximation class closed under the ring operations.

**What this makes of the refit.** The missing piece is exactly the Gamma side, and entry 51 supplies
it: a *balanced* monomial satisfies `M(s) = P_N(1/s) + O(‖s‖^{−(N+1)})`, and `P_N(1/s)` is a
rational function, so a balanced monomial is `HasRatApprox` — hence `HasLogRatApprox`, hence
multipliable into the jet coefficients. The half-plane statement transfers to a tube through the
shift relation `M(s) = M(s+n)·ρ_n(s)^{-1}` with `ρ_n` rational and `ρ_n → 1`.

Then a normal-form sum is grouped by the pair `(degree, first moment)` of the exponent vector.
Within a block every ratio `M_α/M_{β_i}` is balanced, so the block coefficient
`Ψ_i = ∑_{α∈B_i} Q_α·(M_α/M_{β_i})` is `HasLogRatApprox` and has a datum `(0, a_i, b_i, c_i)`,
`c_i ≠ 0`, as soon as it is not vertically negligible. Multiplying by `M_{β_i}` gives a datum for
each block with `ω = (moment of B_i) + a_i` and `a_i ∈ ℤ`.

**And now the lattice hypothesis does the work `NoIntegerRelation` used to do, but correctly.** Two
distinct blocks collide only if their moments differ by an integer; their moments lie in
`Λ = ℤ log p + ℤ log q`, and `primeLog_indep_mod_one` says a nonzero element of `Λ` is never an
integer. So distinct blocks never collide, every dominance class is a single block, and `hclass`
holds with the block's own nonzero constant. This is the exact point at which the card's own
arithmetic input replaces the false hypothesis.

Two obligations remain, both now sharply stated:
1. `HasRatApprox (gammaMonomial λ g)` for balanced `g` — entry 51 plus the shift transfer.
2. `¬ IsVerticallyNegligible Ψ_i` for a nonzero block coefficient — the one place where linear
   independence of Gamma monomials (entry, `gammaMonomial_linearIndependent`) has to be upgraded
   from "the function is nonzero" to "the function is not negligible".

## 2026-08-19 — entry 53: obligation 1 closed — a balanced monomial is rationally approximable

56. `HTGeometry/GammaMonomialRatApprox.lean` — `hasRatApprox_shift_zpow`,
    `HasRatApprox.finsetProd`, `HasRatApprox.finsetSum`, `hasRatApprox_of_tube_eq`,
    `tube_add_real_ne_zero`, `hasRatApprox_polyEval_inv_shift`,
    `gammaMonomial_shift_nat_of_ne`, **`hasRatApprox_gammaMonomial`**.
57. `HTGeometry/GammaBlockSumDatum.lean` — `HasLogRatApprox.finsetSum`,
    `hasLogRatApprox_balancedBlockSum`, `exists_hasShiftTubeDatum_balancedBlockSum`.

`hasRatApprox_gammaMonomial`: a gamma monomial with real nonnegative shifts, vanishing degree and
vanishing first moment belongs to `HasRatApprox`. Two ingredients: the transseries truncation of
entry 51 is a polynomial in `1/s`, and the corpus's own `eval_inv_eq_div` turns that into a quotient
of polynomials in `s`; and the half-plane statement reaches the tube through the `n`-fold functional
equation, whose multiplier is a product of `n` factors each within `K/t²` of `1`
(`exists_norm_shiftRatio_sub_one_le`, which needs **no** half-plane hypothesis), so the multiplier is
bounded by `2ⁿ` and the transferred error is still `O(t^{-(N+1)})`.

A version of the `n`-fold functional equation with no half-plane hypothesis was needed
(`gammaMonomial_shift_nat_of_ne`): on a tube the real part can be arbitrarily small, and all the
equation actually needs is `s + j + λ_k ≠ 0`, which the nonzero imaginary part supplies.

Item 57 packages what follows: a block sum `∑_α Q_α·M_α` with every exponent vector balanced is
`HasLogRatApprox`, and `exists_hasShiftTubeDatum_of_logRatApprox` then hands over a datum with
nonzero constant **given only** `¬ IsVerticallyNegligible`.

### The single remaining gap on card B, and the route to it

`¬ IsVerticallyNegligible (∑_α Q_α M_α)` for a nonzero balanced block. The corpus establishes the
same thing for jet polynomials alone in `JetNonNegligible.not_isGermNegligible_shiftedJetEval`,
through the germ algebra at `upperEndFilter` and the rational-increment Hölder eliminator.

The route for the block: modulo `O(t^{-N})` the block sum equals `shiftedJetEval` of
`∑_α T̃_α^{(N)}·P_α`, where `T̃_α^{(N)} ∈ RatFunc ℂ` is the order-`N` transseries truncation of
`M_α`, so negligibility of the block forces a **fixed** nontrivial `RatFunc`-linear relation among
the truncations for all large `N`, hence among the full formal expansions. Those expansions form an
**injective character** of the exponent lattice into the units of the field of formal series —
injectivity being exactly `exists_gammaMonomial_leading_deviation` — so Dedekind's independence of
characters (mathlib's `linearIndependent_monoidHom`) forbids such a relation.

## 2026-08-19 — entry 54: the singleton-block datum is unconditional

58. `HTGeometry/GammaSingleBlockDatum.lean` — `tubeLimit_gammaMonomial`,
    `exists_norm_gammaMonomial_ge_half`, `not_isVerticallyNegligible_mul_gammaMonomial`,
    `not_isVerticallyNegligible_jetFieldPolyFun`,
    **`exists_hasShiftTubeDatum_jetGammaBalanced`**.

```text
lam real ≥ 0, shifts pairwise incongruent mod ℤ, idx injective, P ≠ 0,
∑ e = 0, ∑ e_i λ_i = 0
  ⟹  ∃ a b c, c ≠ 0 ∧ HasShiftTubeDatum M 0 (jetFieldPolyFun · P · gammaMonomial · e) 0 a b c
```

No `NoIntegerRelation`, no negligibility hypothesis, no premises at all beyond the card's own
arithmetic input. The mechanism is short once the right observation is made:

> a **balanced** monomial tends to `1` uniformly on every vertical tube, so multiplying by it
> neither creates nor destroys negligibility.

That is `tubeLimit_gammaMonomial` (the corpus's `tubeLimit_gammaProd_ratio` read through
`gammaProd_ratio_eq_gammaMonomial` of entry 48) plus `exists_norm_gammaMonomial_ge_half`. So the
non-negligibility of the product reduces to that of the jet polynomial alone, which the corpus
already owns through the germ eliminator, and the approximant class supplies the rest.

The same reduction also normalises the general case: factoring out `M_β` turns any block into one
whose reference monomial is `1`, since `∑_α Q_α M_α = M_β·∑_α Q_α(M_α/M_β)` and `M_α/M_β` is
balanced.

So the remaining gap on card B is now exactly:

> `¬ IsVerticallyNegligible (∑_α Q_α S_α)` for balanced `S_α` with distinct exponent vectors,
> `S_{α₀} = 1`, and jet polynomials `Q_α` not all zero.

Note that this case is genuinely needed and not vacuous: two exponent vectors share a block iff
`∑_k (e_α − e_β)_k λ_k = 0`, and for a finite subset of the rank-two lattice `Λ` with three or more
elements the `λ_k` are ℤ-dependent, so nontrivial blocks occur — the card's own example
`Γ(s+α)Γ(s+β)` against `Γ(s)Γ(s+α+β)` is one.

## 2026-08-19 — entry 55: the termination condition already exists in the corpus

59. `HTGeometry/GammaMonomialTubeGrowth.lean` — `hasTubePolyGrowth_gammaMonomial`,
    `IsVerticallyNegligible.mul_gammaMonomial`,
    **`isVerticallyNegligible_mul_gammaMonomial_iff`**: a balanced monomial is a *unit* for
    negligibility — multiplying by it changes nothing in either direction.

### The proof of the remaining gap, in full, with every input identified

Goal: `∑_{α∈A} Q_α S_α` negligible, `S_α` balanced with distinct exponent vectors, `Q_α` jet
polynomials ⟹ every `Q_α = 0`. Induction on `|A|`.

* `|A| = 1`: `Q S` negligible ⟺ `Q` negligible (item 59) ⟹ `Q = 0` by the corpus's germ eliminator.
* `|A| ≥ 2`: pick `α₀` with `Q_{α₀} ≠ 0` (else drop it and use induction). Apply the unit shift `σ`,
  which preserves negligibility (`IsVerticallyNegligible.shift`), and cross-multiply:

  ```text
  σ(Q_{α₀})·Φ  −  ρ_{α₀}^{-1}·Q_{α₀}·σ(Φ)  ≡  0     (mod negligible)
  ```

  Multiplication by a jet polynomial or by a rational function preserves negligibility
  (`IsVerticallyNegligible.mul_polyGrowth`). Since `σ(S_α) = ρ_α S_α` with
  `ρ_α = ∏_k (s+λ_k)^{e_{α,k}}`, the `α₀` term cancels **identically**, leaving `|A| − 1` terms.
  By induction every new coefficient vanishes:
  `σ(Q_{α₀})Q_α = Q_{α₀}σ(Q_α)·(ρ_α/ρ_{α₀})`, i.e. with `u = Q_α/Q_{α₀}`,

  ```text
  σ(u) = u · (ρ_{α₀}/ρ_α),   exponent vector  e_{α₀} − e_α ≠ 0.
  ```

  That is exactly

  ```text
  ShiftedGammaFieldIndependence.no_multiplicative_coboundary_digammaField
      (u : digammaField lam) (hu : u ≠ 0) (mm : Fin r → ℤ) (i₀) (hmm : mm i₀ ≠ 0) :
    digammaFieldShift lam u ≠ u * ∏ i, (gammaFactor lam i) ^ (mm i)
  ```

  already in the corpus, unconditional, and proved from pairwise incongruence alone. So every
  `Q_α = 0` for `α ≠ α₀`, the relation collapses to one term, and the base case kills `Q_{α₀}` —
  contradicting `Q_{α₀} ≠ 0`.

Every step's input now exists. What remains is engineering, not mathematics: the induction has to be
run where both objects live at once. The coefficients change type under the shift
(`Polynomial ℂ` → `RatFunc ℂ`), so the natural home is the germ layer at `upperEndFilter`, where the
corpus already evaluates jet polynomials over `RatFunc ℂ` (`shiftedJetEval`) and where negligibility
is an ideal-like subgroup stable under the shift and under rational multiples. The two bridges to
build are the germ of a Gamma monomial with its shift equation, and the passage from a germ identity
between jet polynomials to the corresponding identity in `digammaField lam`.

A route that does **not** work, recorded: eliminating with the *derivation* instead of the shift.
The identity is prettier — `S_α' = L_α S_α` with `L_α = ∑_k e_{α,k}ψ(s+λ_k)` in the jet field, and
the cross-multiplied combination cancels the `α₀` term just as well — but negligibility is not
stable under differentiation on a tube, since the distance to the tube boundary does not grow.

## 2026-08-19 — entry 56: both algebraic bridges for the shift elimination

60. `HTGeometry/JetPolynomialShift.lean` — `jetShiftPoly`, `jetShiftPoly_C`, `jetShiftPoly_X`,
    **`aeval_jetShiftPoly`**: the endomorphism of `MvPolynomial (Fin M) (RatFunc ℂ)` sending
    `X k ↦ X k + C (familyIncrement …)` and acting on coefficients by `ratShift` induces the unit
    shift on jet values, `aeval ∘ jetShiftPoly = addTranslationMeroEquiv 1 ∘ aeval`.
61. `HTGeometry/JetPolynomialCoboundary.lean` — **`no_jetPoly_multiplicative_coboundary`**:

```text
P ≠ 0, Q ≠ 0, mm i₀ ≠ 0,
jetShiftPoly rj P * Q = C (∏ i (X + C λ_i)^{mm i}) * (P * jetShiftPoly rj Q)   ⟹   False
```

The corpus's obstruction `no_multiplicative_coboundary_digammaJets` is stated for the *quotient*
`aeval P / aeval Q` in the meromorphic field; the shift elimination produces instead a
**cross-multiplied** identity between polynomials, because dividing is not available in the ring the
elimination runs in. Item 61 is that restatement: evaluate, use item 60 for the shift, use
`algebraicIndependent_digammaJet` to know both values are nonzero, and divide once at the end.

So the elimination step is now fully supported. What remains for the block non-negligibility is the
induction itself, which must run in the germ layer at `upperEndFilter` — the coefficients acquire
denominators under the shift, so `RatFunc ℂ` coefficients are forced, and `shiftedJetEval` is the
corpus's evaluation of exactly that ring into germs. The remaining pieces are the germ of a Gamma
monomial with its shift equation `σ(S_e) = ratFuncGerm(ρ_e)·S_e`, and stability of negligibility
under multiplication by a `shiftedJetEval` germ.

Note the shape of the induction's conclusion: the inductive hypothesis returns that the new
coefficients vanish **as polynomials**, not merely as germs, which is precisely the hypothesis
`no_jetPoly_multiplicative_coboundary` consumes.

## 2026-08-19 — entry 57: the germ layer for the shift elimination is complete

62. `HTGeometry/GammaMonomialGerm.lean` — `gammaMonomialGerm`, `gammaShiftFactor`,
    `gammaShiftNumer`, `gammaShiftDenom`, `gammaShiftFactor_eq_div`,
    `ratFuncGerm_gammaShiftFactor`, **`upperEndTranslateGerm_gammaMonomialGerm`**:
    `σ(S_e) = ratFuncGerm(ρ_e)·S_e`, the eigen-equation the elimination runs on.
63. `HTGeometry/JetGermPolyGrowth.lean` — `exists_polyGrowth_rep_shiftedJetEval`,
    `IsGermNegligible.mul_shiftedJetEval`, `IsGermNegligible.mul_coe`.
64. `HTGeometry/JetGermShift.lean` — **`upperEndTranslateGerm_shiftedJetEval`**: the polynomial
    shift of item 60 induces the unit shift on germs as well as on the meromorphic field.

Every ingredient the induction consumes now exists:

```text
base case          isVerticallyNegligible_mul_gammaMonomial_iff  (entry 55)
                   not_isGermNegligible_shiftedJetEval           (corpus)
eigen-equation     upperEndTranslateGerm_gammaMonomialGerm       (item 62)
shift carrier      jetShiftPoly, upperEndTranslateGerm_shiftedJetEval, aeval_jetShiftPoly
stability          IsGermNegligible .sub .shift .mul_ratFuncGerm .mul_shiftedJetEval
termination        no_jetPoly_multiplicative_coboundary          (entry 56)
```

The elimination itself, to be assembled next: with `Φ = ∑_{α∈S} shiftedJetEval(P_α)·S_{e_α}`
negligible and `P_{α₀} ≠ 0`, the combination

```text
Ψ := ratFuncGerm(ρ_{α₀})·shiftedJetEval(σP_{α₀})·Φ  −  shiftedJetEval(P_{α₀})·σ(Φ)
```

is negligible, and expanding it with the two shift laws gives
`Ψ = ∑_{α∈S} shiftedJetEval(C ρ_{α₀}·σP_{α₀}·P_α − C ρ_α·P_{α₀}·σP_α)·S_{e_α}`,
whose `α₀` coefficient vanishes identically — note this form needs **no inverses**, which is why the
elimination can live in the polynomial ring rather than its fraction field. Induction on `|S|` then
kills every new coefficient, and dividing by the unit `C ρ_{α₀}` puts the surviving identity in
exactly the shape `no_jetPoly_multiplicative_coboundary` refutes, with `mm = e_α − e_{α₀} ≠ 0`
supplied by injectivity of `e`.

## 2026-08-19 — entry 58: the shift elimination is proved; the block datum is unconditional

65. `HTGeometry/GammaJetElimination.lean` — `shiftedJetEval_C`, `shiftedJetEval_mul`,
    `shiftedJetEval_sub`, `shiftedJetEval_zero`, `eq_zero_of_isGermNegligible_single`,
    `gammaShiftFactor_ne_zero`, `gammaShiftFactor_add`,
    **`eq_zero_of_isGermNegligible_gammaCombination`**.
66. `HTGeometry/GammaBlockNonNegligible.lean` — `not_isVerticallyNegligible_balancedBlockSum`,
    **`exists_hasShiftTubeDatum_balancedBlock`**.

```text
lam real ≥ 0, shifts pairwise incongruent mod ℤ, idx injective,
e injective with every e α balanced, some P β ≠ 0
  ⟹  ∃ a b c, c ≠ 0 ∧ HasShiftTubeDatum M 0 (∑_α jetFieldPolyFun·P α · gammaMonomial·e α) 0 a b c
```

No `NoIntegerRelation`, no negligibility hypothesis, no premises beyond what the card already
carries. This closes the obligation opened in entry 54.

Two points worth keeping. First, the induction has to be stated with the coefficient family
**universally quantified**, because the elimination replaces one family by another; fixing `Pf`
outside the induction makes the hypothesis unusable — that was the first thing that failed. Second,
the elimination is inverse-free by design:

```text
Ψ = ratFuncGerm(ρ_{α₀})·shiftedJetEval(σP_{α₀})·Φ − shiftedJetEval(P_{α₀})·σ(Φ)
  = ∑_α shiftedJetEval(C ρ_{α₀}·σP_{α₀}·P_α − C ρ_α·P_{α₀}·σP_α)·S_{e_α},
```

so it lives in the polynomial ring and never needs the fraction field; the single division happens
at the very end, cancelling the unit `C ρ_{α₀}` to reach the shape
`no_jetPoly_multiplicative_coboundary` refutes.

What remains on this card is assembly, not mathematics: regroup a normal-form sum by
`(degree, first moment)`, give each block its datum by item 66, and observe that distinct blocks
never collide because `primeLog_indep_mod_one` forbids a nonzero element of `Λ` from being an
integer. That makes every dominance class a single block and discharges `hclass` — the hypothesis
`NoIntegerRelation` was there to supply and could not.

## 2026-08-19 — entry 59: the block datum over an arbitrary finite index, and the regrouping plan

67. `HTGeometry/GammaBlockFinset.lean` — `gammaMonomial_add`, `gammaProd_eq_gammaMonomial`,
    **`exists_hasShiftTubeDatum_balancedBlockFinset`**: the datum of entry 58 with the block
    indexed by a `Finset` rather than a `Fin`, which is what the regrouping produces.

### The regrouping, without any re-indexing

The obvious route — partition `Fin Mm` into blocks and re-index them by `Fin n` — needs an
equivalence and a great deal of transport. There is a way to avoid it entirely. Put

```text
key α  = (Γ-degree of e_α, first moment of e_α),      rep α = min of α's fibre,
n α    = card of α's fibre,                            F α = (1/n α) · (block sum over rep α's fibre).
```

Then `∑_α F α = ∑_α Q_α M_α`, because each block is counted `n` times with weight `1/n`; each `F α`
has a datum (the block datum times a nonzero constant); the dominance class of `β` is exactly the
fibre of `rep β`; and the class sum is `n·(c/n) = c ≠ 0`. So `exists_hasShiftTubeDatum_sum_class`
applies **on the original index set**, with `hclass` discharged by construction rather than by a
hypothesis.

The non-collision of distinct blocks is where the card's arithmetic enters, and it is robust to the
coefficients: block shapes are `(d_i, a_i + moment_i, b_i)` with `a_i ∈ ℤ`, so two blocks share a
shape only if `moment_i − moment_j ∈ ℤ`, which `primeLog_indep_mod_one` forbids unless the moments
are equal — i.e. unless the blocks coincide.

Also cleaned: eleven Lean warnings across six modules from earlier in this run (`simpa`→`simp`,
`push_neg`→`push Not`, `tendsto_finset_sum`→`tendsto_finsetSum`,
`DifferentiableAt.fun_finset_prod`→`…fun_finsetProd`, unused simp arguments and one unused binder).
The formal lint gate fails on warnings, so these had to go before the sweep can be declared clean.
