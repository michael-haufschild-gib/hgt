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
