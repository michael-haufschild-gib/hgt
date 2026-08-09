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
- [ ] `additive-heat-aperture-shifted-zeta-echo-ladder`
- [ ] `additive-heat-aperture-zeta-zero-echo`
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
- [ ] `eigenplurivolume-log-crepant-orbifold`
- [ ] `embedded-manin-horizon-isogeny-reconstruction`
- [ ] `finite-archimedean-gamma-product-boundary-law`
- [ ] `fixed-divisor-full-complex-translation-freeness`
- [ ] `floquet-orbifold-tail-emergence`
- [ ] `gauss-component-quasi-inner-residue-hierarchy`
- [ ] `irrational-triptic-source-effectivity-character`
- [ ] `isogeny-tail-maurer-cartan-holography`
- [ ] `jet-horizon-translation-gauge-classification`
- [ ] `noncompact-period-quotient-facet-escape-law`
- [ ] `nonlinear-rational-observation-curve-horizon-reconstruction`
- [ ] `nonreal-factorial-slope-formal-hypertranscendence`
- [ ] `orbifold-tail-holographic-reconstruction`
- [ ] `periodic-pencil-intrinsic-ht-dimension-two`
- [ ] `power-canonical-product-exact-moment-borel-lattice-law`
- [ ] `prescribed-gap-process-order-one-maximal-ht-profield`
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
- [ ] `scalar-ht-horizon-celestial-sphere`
- [ ] `symmetry-caged-fixed-divisor-full-orbit-freeness`
- [ ] `toric-log-calabi-yau-tail`
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
