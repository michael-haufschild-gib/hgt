# JAS completed-theta Mellin landing and full-density obstruction

- **ID:** JAS-CTML
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-GO CLASSIFICATION (Lean)
- **Source:** read-only `rh-current-frontier-map.md` · JAS literal completed-theta/Xi
  comparison burden; corpus theta arithmetic-translation, positive truncation-seam, exact
  reflection, tail cancellation, and Xi cosine identities
- **Statement:** Actual differentiated theta atoms form an injective arithmetic family in the
  maximal singular-Mellin domain and satisfy exact reciprocal-index covariance.  They cannot be
  operator eigenvectors, their positive-half translates acquire a mandatory nonzero boundary
  current, and their unrenormalized completed sum cannot lie in full-line `L²`.  The strongest
  survivor is the exact reflection-renormalized source `rho - rawTail = 4 Phi`, which belongs to
  the maximal domain and whose positive cosine current is literally `XiC`.

## Goal

Attack JAS at the hardest completed-source analytic gate: determine whether actual completed-theta
arithmetic atoms, rather than an abstract carrier, land in the closed singular-Mellin framework and
compare directly with Xi.  Apply hostile terminal tests before investing in a global sewing map.

## Gates

- [x] 0 → 1 in-progress: mandatory corpus search, source-derived conjectures, terminal hostile
  tests, current primary-literature search
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact Lean source check, leaf build, axiom audit, umbrella wiring
- [ ] 3 → 4 publication-ready: standalone exposition and independent novelty review

## Conjecture loop and result

1. **C1 — arithmetic indices can land coefficientwise as eigenvalues of the singular-Mellin
   operator.** **Killed.**  Multiplication by `exp x` on Lebesgue `L²(ℝ)` has empty point spectrum:
   an eigen-equation forces the vector to vanish away from one null level set.  An injective
   coefficient family of eigenvectors is therefore impossible. **[PROVED HERE]**
2. **C2 — actual differentiated theta atoms land in the maximal domain while retaining their
   coefficients.** **Proved.**  The first atom and its `exp`-weighted form are in `L²`; logarithmic
   translation and critical `n⁻¹ᐟ²` normalization give every positive-index atom.  The operator
   transforms it with exact reciprocal-index covariance, and the resulting family is injective in
   `n` by its exact norm. **[PROVED HERE]**
3. **C3 — positive-half completion commutes with arithmetic translation.** **Killed.**  Every
   nontrivial translate has an explicit swept-boundary current on `(-log n, 0]`, and that current
   is strictly positive at `-log(n)/2`.  Bare translated completion is therefore false.
   **[PROVED HERE]**
4. **C4 — the canonical unrenormalized completed density is a full-line `L²` vector, so atomwise
   domain landings can be summed without subtraction.** **Killed.**  Its exact reflection law
   contains a half-exponential mode; assuming full-line `L²` would make the constant function
   integrable on an infinite ray. **[PROVED HERE]**
5. **C5 — the full-density no-go leaves no literal Xi source.** Failed as a falsifier.  Exact
   cancellation gives `rho - rawTail = 4 Phi`.  The even completed source `Phi` and its `exp` weight
   are in `L²`, hence `Phi` lies in the same maximal singular-Mellin domain, and its positive cosine
   current is exactly `XiC`. **[PROVED HERE]**

## Hard-frontier significance and exact remaining burden

This is structural, not numerical.  It terminates two tempting JAS constructions before a global
proof is built on them:

- arithmetic coefficients cannot be encoded as point spectrum of the singular-Mellin operator;
- raw completed density cannot be used as a full-line Hilbert vector, and positive completion
  cannot discard translation-boundary provenance.

The positive survivor closes the literal completed-theta/Xi **analytic landing** layer: one
explicit reflection-renormalized completed source lies in the maximal domain and its cosine
current is Xi, while the actual arithmetic atoms remain coefficient-faithful there.

This does not prove RH and does not close JAS.  Remaining hard gate is a noncircular
prime-support/valuation/history map into this renormalized completed source, carrying the explicit
swept-boundary current and reflection orientation, and upgrading the value-current comparison to
the source-linear first-jet sewing required by the prime-Poisson theorem.  Any construction that
uses the raw density, treats arithmetic atoms as eigenvectors, or suppresses the boundary current
is now a proven dead end.

## Lean artifact

- Module: `GaloisForLFunctions.RHTower.JointAncestryCompletedThetaMellinLanding`
- Empty point spectrum and eigenlanding no-go:
  - `jointAncestry_exp_ne_eigenvalue_of_ne_exception`
  - `jointAncestry_ae_eq_zero_of_exp_mul_eq`
  - `jointAncestrySingularMellinOperator_has_no_eigenvector`
  - `not_jointAncestryCoefficientwiseMellinEigenlanding`
- Actual arithmetic atom landing:
  - `jointAncestryThetaDensitySeedDomain`
  - `jointAncestryThetaDensityAtomDomain`
  - `jointAncestrySingularMellinOperator_thetaDensityAtom`
  - `jointAncestryThetaDensityAtomDomain_injective`
- Completion seam and raw-density no-go:
  - `positiveThetaCuspTailSecondDensityAtom_translation_seam`
  - `forwardTranslationBoundary_thetaDensityAtom_one_pos`
  - `positiveThetaCuspTailSecondDensityAtom_ne_bare_translate`
  - `not_memLp_two_thetaCuspTailSecondDensity_fullLine`
- Strongest positive survivor:
  - `thetaCuspFullSource_memLp_two`
  - `exp_mul_thetaCuspFullSource_memLp_two`
  - `jointAncestryCompletedThetaSourceDomain`
  - `jointAncestryCompletedThetaSource_eq_renormalizedDensity`
  - `XiC_ofReal_eq_jointAncestryCompletedThetaSourceL2_cosine`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/JointAncestryCompletedThetaMellinLanding.lean` —
    PASS
  - `lake build GaloisForLFunctions.RHTower.JointAncestryCompletedThetaMellinLanding` — PASS
    (`Built ...`, 11s)
  - scoped `#print axioms` for the eigenlanding no-go, atom injectivity, raw-density no-go, and Xi
    comparison — only `propext`, `Classical.choice`, `Quot.sound`
  - forbidden-declaration scan and scoped `git diff --check` — PASS
  - leaf wired into `GaloisForLFunctions.RHTower`; no full or umbrella build run
  - global `scripts/formal_tools.py lint` reports unrelated concurrent un-wired RHTower and
    HTGeometry modules; this leaf is reachable and absent from every reported failure

## Literature audit (as of 2026-08-28)

- Connes--Consani, *The Scaling Hamiltonian* (arXiv:1910.14368), studies a semilocal `L²` scaling
  Hamiltonian and obstruction to a positivity route, not this exact arithmetic-atom covariance,
  truncation seam, raw-density `L²` exclusion, and reflection-renormalized Xi landing.
- Coffey, *Theta and Riemann xi function representations from harmonic oscillator eigensolutions*
  (arXiv:math-ph/0612086), supplies theta/Mellin/xi representations, not this maximal-domain
  classification or full-line density no-go.
- Corpus search found related completed-source maximal-coordinate-domain and Fourier identities,
  but no prior theorem combining the actual differentiated arithmetic atoms, coefficient
  faithfulness, nonzero completion seam, and exact raw-density exclusion proved here.
- Targeted current primary searches found no paper containing the exact combined theorem.  Empty
  point spectrum of multiplication operators and theta/Xi integral representations are classical
  components. **Novelty status:** `[NOVELTY UNVERIFIED]` pending independent expert review.

## Door passport

- **Unconditional source:** corpus theta identities, Lebesgue measure, explicit maximal
  multiplication operator, actual differentiated theta atoms, exact reflection and cancellation.
- **No RH leakage:** no Xi zero, RH premise, zero enumeration, computation, new axiom, or
  target-fitted choice enters any declaration.
- **Burden removed:** literal completed-theta analytic landing; classification of three invalid
  direct landings; coefficient-faithful arithmetic atom family; mandatory renormalization and
  boundary provenance.
- **Burden not removed:** prime-support/valuation/history-to-completed-source functor,
  source-linear first-jet sewing, infinite arithmetic synthesis, reflection-orientation selection,
  and a positivity/spectral consequence forcing Xi zeros onto the wall.

## Log

- 2026-08-28 — coefficientwise eigenlanding killed by empty point spectrum.
- 2026-08-28 — actual theta atoms placed in maximal domain with exact covariance and injectivity.
- 2026-08-28 — positive truncation proved to create mandatory nonzero boundary current.
- 2026-08-28 — raw full density excluded from full-line `L²`; exact renormalized completed source
  retained in the maximal domain with direct Xi cosine comparison; frontier map remained read-only.
