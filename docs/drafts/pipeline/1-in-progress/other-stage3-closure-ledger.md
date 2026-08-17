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

- [ ] `abelian-multiplication-tail-manin-horizon`
- [ ] `active-quasi-abelian-palette-exact-ht-dimension-classification`
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
- [ ] `prime-valuation-dyadic-fermion-normal-cone-law`
- [ ] `prime-wold-accelerated-type-modular-drift-law`
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
