# Goal: five stage-2 cards → stage 3 (opened 2026-08-19)

1. `fixed-shell-angular-dephasing-static-local-plateau-law` — Theorem A largely assembled
2. `fixed-shell-transversality-onset-hardening-cone-law`
3. `cusp-spectrum-radius-law`
4. `determinant-defect-completion-law`
5. `markovian-return-recovery-complexity-reflection-law` — **DONE, in 3-formalized**
   (memory `quantum_recurrence/markovian_channel_lean_stack_2026_08_19`).

## Card 1 — angular dephasing, Theorem A (fixed-shell nonflatness)

### Landed 2026-08-19 (HTGeometry, umbrella-wired, axiom-clean, lint-clean, all built)
- `QuadraticRateOrbitPolynomialField.lean` — labeling-orbit obstruction over an arbitrary
  **characteristic-zero integral domain** (generalised from Field; `esymmAlgEquiv` needs only
  CommRing, and the arithmetic used is only "2 is not a zero divisor" + "a square vanishes only at
  0").  This generality is what lets the *rate* be carried as a variable, by instantiating at
  `K := MvPolynomial θ ℂ`.
  Declarations keep the `fieldQuadraticRate…` prefix.
- `QuadraticRateMatrixObstruction.lean` — `quadraticRateObstructionPullback`,
  `eval_quadraticRateObstructionPullback`,
  `exists_mem_eval_quadraticRateObstructionPullback_ne_zero`.
- `QuadraticRateAnalyticEscape.lean` — chart escape → complex witness → nowhere flatness on real
  parameters.
- `LocalExtensionQuadraticRateFlatCollapse.lean` — **Lemma A2 without `hL`**
  (`localExtension_quadraticRate_eq_zero_unconditional`) plus the `hlabel` interface
  `exists_localField_quadraticRate_not_eventually`.
- `BellEndpointCompleteBasis.lean` — **base case of Lemma A1**:
  `reducedTransition ψ φ = reshape φ * (reshape ψ)ᴴ`, so a maximally entangled orthonormal basis
  is endpoint complete with no case analysis.  `exists_endpointComplete_twoQubit_witness`.

### Still missing for Theorem A
(a) **Induction genericity**: propagate simplicity + distinct nonzero ordered gaps across the
    attached qubit (endpoint completeness already propagates via
    `eventually_forall_layerGerm_endpoint_ne_zero`).
(b) **Rate-as-variable instantiation**: use `K := MvPolynomial θ ℂ`,
    `c := fun i => C (c₀ i)`, `κ := C κ₀ * (M * M).trace`.  This avoids needing
    `∑ᵢ λᵢ² = Tr(H²)` (a real mathlib gap: only order one exists,
    `Matrix.trace_eq_sum_roots_charpoly`; no Schur triangulation in mathlib).  Along the extension
    slice, `Tr((D + gV)²) = Tr(D²) + g² Tr(V²)` directly, because `layerCrossPerturbation_diagonal`
    says `V` has zero diagonal.
    What this still needs: base-change naturality of the construction under a ring hom
    `f : K →+* L` — trivial for the relation and the orbit, but naturality of
    `MvPolynomial.esymmAlgEquiv` is not in mathlib.
(c) Bridge the `(z,g)` extension chart to a `Fin m → ℂ` polynomial-matrix chart.  Linear template:
    `TwoLocalRealSliceGenericity.lean` + `BlockSplitBranchEscape.lean`.  NB the two-local *edge*
    slice is block-decoupled, so it cannot serve the quadratic case: the crown argument needs
    `M α β * M β α ≠ 0` for ALL α ≠ β, i.e. the endpoint-complete layer-split slice.

### Why the quadratic case cannot reuse the parent card's witness
`GoodObserverSpectralSystem.observerFamily_good` = `HermitianObserverFamilyGood` asks only that the
transition support graph be preconnected and non-bipartite.  The crown argument needs it complete.

## Card 2 — transversality.  Theorem E complete; both infrastructure blockers closed.
Theorem B `(17)` consumes card 1's Theorem A as `(13)`.

## Card 3 — cusp.  Only gap: Kaczorowski–Perelli standard-twist continuation, general class member.

## Card 4 — determinant defect.  Gap: `det_p` on Schatten-`p` and `(DC)`.  Corpus owns the p = 2
analytic input (`entireDet2`, `tendsto_entireDet2_of_hsNorm_sub_tendsto_zero`, `fredholmDet1`).

## Session traps
- `open Matrix` INSIDE `namespace GaloisForLFunctions.HTGeometry` shadows `_root_.Matrix` and kills
  the `ᴴ` notation — put all `open`s BEFORE the namespace.
- `omit [inst] in` goes BEFORE the docstring, never between docstring and `theorem`.
- `⊗ₖ` needs `open scoped Kronecker`.
- `Matrix.PosSemidef` is Finsupp-based; use `posSemidef_iff_dotProduct_mulVec` and friends.
- `by classical; exact ∏ σ : Equiv.Perm I, …` inside a def creates a Fintype instance that is not
  `rfl`-equal to the `DecidableEq`-derived one; require `[DecidableEq I]` instead.
