# Classification of RH criterion classes: no-gos, a duality, and one lane closure

- **ID:** rh-criterion-class-no-go-cluster
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/rh-criterion-reencoding-audit.md §§44–73
- **Statement:** Every examined class of zero-set functional is provably incapable of deciding RH,
  and the prime-side and zero-side descriptions of the rectangular window are transform duals.

## Goal

The corpus contains ~96 RH producers and a large rectangular/CCM apparatus. The question this
cluster settles is not whether any of them proves RH — none does — but **which whole classes are
provably incapable**, so that effort is not spent re-deriving a criterion inside a closed class.
Each entry below is an unconditional Lean theorem, not a judgement about difficulty.

## Gates

- [x] 0 → 1  well-posed: each class stated as a hypothesis shape on a functional of the zero set
- [x] 1 → 2  fully-proven: all six results proved on paper before formalization
- [x] 2 → 3  formalized: modules below, `lake build GaloisForLFunctions.RHTower` and
      `GaloisForLFunctions.HTGeometry` green, all theorems `[propext, Classical.choice, Quot.sound]`
- [ ] 3 → 4  publication-ready: not attempted; the individual results are small, the value is the
      classification

## Results

| # | Class or fact | Killing theorem | Module |
|---|---|---|---|
| 1 | zero-density envelopes | `envelope_dichotomy`, `density_estimate_never_forces_vanishing` | `RHTower/DensityEnvelopeNoGo` |
| 2 | functional-equation symmetry | `exists_conjSymmetric_family_re_sum_sq_neg` | `HTGeometry/ConjugateSymmetryNoPositivity` |
| 3 | nonnegative-sum criteria | `forall_prop_of_tsum_bound`, `tsum_bound_iff_forall_prop` | `HTGeometry/NonnegativeSumCriterionNoGo` |
| 4 | phase spreading | `sum_sq_spacedPhase_eq_zero`, `single_phase_saturates` | `HTGeometry/EquidistributedPhaseThreshold` |
| 5 | rectangular carrier structure | `xiScrewWindowCurvature_eq_tsum_sq`, `riemannHypothesis_iff_screwTotalEnergy_bounded` | `RHTower/ScrewCurvatureSumOfSquares` |
| 6 | prime/zero duality | `tent_transform_eq_four_mul_amplitude_sq` | `RHTower/TentTransformAmplitude` |

Supporting: `RHTower/RectangularTentReduction` (four tents reduce to two on the arithmetic range),
`RHTower/PrimeMassLowerBound` (`(log 2/2)√X ≤ ∑_{n≤X}Λ(n)/√n ≤ 2 log X·√X`, via mathlib's Chebyshev
bound), `RHTower/PrecisionGapExponent` (the `X^{−θ}` versus `log X/√X` crossing, as pure analysis).

## The classification, stated

1. **Density envelopes.** RH is `N(σ,T) = 0`; `N` is integer-valued, so an upper bound decides RH
   iff its envelope drops below `1`. Every literature envelope `C·T^{θ(1−σ)}(log T)^A` is `≥ 1`
   throughout the strip for `T ≥ e`, at every `θ ≥ 0`. No sharpening crosses this.
2. **Functional-equation symmetry.** `Re ∑gᵢ² = ∑‖gᵢ‖² − 2∑(Im gᵢ)²`; conjugation symmetry forces
   the sum *real* and constrains nothing else. Witness `{i, −i}`: sum of squares `−2`, energy `+2`.
3. **Nonnegative-sum criteria.** A bounded sum of nonnegative terms bounds every term with the same
   constant, so such a criterion is at least as strong as its per-member conjunction — never a
   weakening. Nonnegativity is what does it: a signed family can have zero sum with unbounded terms.
4. **Phase spreading.** `N ≥ 2` equally spaced phases give `∑gₖ² = 0` exactly; a lone phase gives
   `−r²`. Sign failure is a *sparse* phenomenon, which is why methods tuned to detect *many*
   exceptional contributions are mistuned.
5. **The rectangular carrier.** Unconditionally `xiScrewWindowCurvature L x = 16 ∑_ρ g_ρ²`, hence
   `= 16(total energy − 2·imaginary energy)`, hence RH ⟺ one nonnegative spectral sum stays bounded.
   By (3) that criterion is exactly RH-per-zero — no slack, no test vector helps.
6. **Duality.** The tent transform equals four times the squared amplitude, so the prime-side tent
   picture and the zero-side squared-amplitude picture are one function in conjugate variables. The
   square on the zero side is the transform image of the tent being a self-convolution. **The two
   sides are related by an isometry, not an inequality** — nothing is lost passing between them, so
   nothing can be won.

## Relation to prior corpus work

`RHTower/DegreeClassificationClosure` and `RHTower/BetaBlindnessAndDesignConditions` already contain
a design-condition classification: (i) a functional excludes a zero only if its term is comparable
to the total; (ii) the term must see the real part. Nyman–Beurling satisfies (i) and fails (ii);
correlation statistics fail (i). **This cluster was derived independently and overlaps at the
programme level**; results 1–4 and 6 are not in those modules, and (i)/(ii) do not follow from (3)
or vice versa. Anyone extending this work should read both before deriving a new specification —
see §52 of the audit for the method failure that made this correction necessary.

## No-go closure

- **Exact killing mechanism:** per class, the theorem in the table. For the largest class
  (explicit-formula functionals) the mechanism is (6): prime and zero sides are isometric, so the
  criterion's content is the prime error term `ψ(x) − x`, which is the hypothesis.
- **Strongest positive survivor:** the exact unconditional factorization
  `xiScrewWindowCurvature L x = 16 ∑_ρ (sinh(Lw/2)cosh((x−L)w/2)/w)²` and its energy form. These are
  identities, not inequalities, and hold with no hypothesis on zero location.
- **New insight:** the textbook "Weil functional `= ∑_ρ|ĝ(ρ)|²`" is a *consequence* of RH, not an
  unconditional identity. Unconditionally it is `∑_ρ g_ρ²`, and the entire gap is `2∑(Im g_ρ)²` —
  an explicit convergent sum supported exactly on the off-line zeros.
- **Status:** dependency-closed and formalized. *(Earlier revisions of this card cited an
  unformalized "archimedean budget order" as the sole remaining derivation. §56 retracted the
  framing that made it relevant — the criterion fixes the window width `L` and grows the aperture,
  so there is no polynomial-versus-exponential comparison to complete. The entry is withdrawn.)*
  The genuine remaining gaps are the two formalization ceilings listed below, neither of which is
  load-bearing for any theorem above.

## Log

- 2026-07-28 — created directly in 3-formalized; all modules built, registered, axiom-audited, and
  passing `scripts/formal_tools.py lint`. Two claims were retracted during the work (§43's
  significance, §53's variable error); both retractions are recorded in the audit and in the Lean
  docstrings rather than only in prose.

## Later additions (§§65–73)

| result | theorem | module |
|---|---|---|
| moment ladder `∂ₜmₙ = −m_{n+1}` (term-by-term interchange proved) | `hasDerivAt_xiGaussianHeatMoment` | `RHTower/HeatMomentDerivativeLadder` |
| RH ⟹ heat trace completely monotone (forward Bernstein only) | `xiGaussianHeatMoment_re_nonneg_of_riemannHypothesis` | same |
| prime mass `√X` up to a log, two-sided, via Chebyshev | `primeMassHalf_two_sided` | `RHTower/PrimeMassLowerBound` |
| window mass `≥ (log2/2)√y` past the Chebyshev ratio | `eventually_sqrt_le_primeMassWindow_ratio` | `RHTower/PrimeMassWindow` |
| four tents reduce to two on the arithmetic range | `rectangularTwoEdgeAutocorrelation_log_eq_two_tents` | `RHTower/RectangularTentReduction` |
| secular tail from a cofinal floor, no growth hypothesis | `exists_secular_tail_bound_of_trace` | `RHTower/SecularTailFromTrace` |
| CCM `hsum`/`hbessel` discharged; `hl0`/`hl1` targets pinned | `ccm_constraint_hypotheses_eventually` | `RHTower/CCMHypothesisDischarge` |
| **CCM radial floor is false for factorial amplitudes** | `factorial_amplitude_no_uniform_floor` | `RHTower/FuchsFloorNoGo` |
| `‖Γ(1/2+it)‖² = π/cosh(πt)`, hence `≤ 2π e^{−π\|t\|}` | `normSq_Gamma_half_add_mul_I_le` | `HTGeometry/GammaCriticalLineModulus` |
| `x^{−θ}` vs `log x/√x` crossing at `θ = 1/2` (pure analysis) | `precision_wall_at_one_half` | `RHTower/PrecisionGapExponent` |
| growing-index-set form of the nonnegative-sum no-go | `rates_nonpos_of_bounded_exponential_family` | `HTGeometry/NonnegativeSumCriterionNoGo` |

**Lane closure recorded.** The CCM/prolate source lock — the corpus's own designated open core in
`RiemannHypothesisSOTA2026` — is **closed, not blocked**: `hgrow` enters only via `ccm_struct`, whose
output is a radial floor `A₂ ≤ A_{j+2}·lam^{8j}` uniform in `j`, and the Fuchs amplitudes decay
factorially so that floor is false. No weakening of `hgrow` yielding the floor can work. What remains
open there is the ledger's own operator-asymptotic wall (`hl0`/`hl1` convergence), untouched.

**Two formalization ceilings located.** No PNT in mathlib or corpus (only Chebyshev bounds), so no
leading-order explicit-formula cancellation is formalizable. No Hamburger solvability or
Bernstein–Widder anywhere, so the complete-monotonicity criterion cannot be closed to an iff.

## Corrections made during the work

Six claims of mine were retracted and repaired **in the Lean source**, not only in prose: §43
(significance), §53/§56 (wrong variable — `L` fixed, aperture grows), §60/§62 (scope — the PSD/moment
family survives), §65 (declined a feasible step on a misdiagnosed obstruction), §68/§70 (two of five
CCM hypotheses discharged, not four), §71/§72 (judged the Möbius premise through `M` instead of its
Mellin transform).

Five of six came from reading adjacent material; the sixth from carrying the analysis through the
right representation. The operative lesson: **reading first is necessary but not sufficient — a first
pass through the wrong representation fails even when the reading is done.**
