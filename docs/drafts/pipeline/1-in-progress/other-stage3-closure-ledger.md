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
- [ ] `prime-completion-annihilates-hypertranscendence-at-even-temperature`
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
