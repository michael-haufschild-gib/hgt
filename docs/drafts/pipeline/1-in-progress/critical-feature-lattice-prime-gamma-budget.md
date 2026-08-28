# Critical-feature lattice-summed prime–Gamma budget

- **ID:** `critical-feature-lattice-prime-gamma-budget`
- **Label:** W-H205
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / QUANTITATIVE SOURCE BUDGET
- **RH status:** open
- **Computation used:** historical receiver audit only; numerical certificate retired
- **Source:** `HedenmalmCriticalFeatureHolomorphicSectorCoercivity.lean` and
  `HedenmalmWardDefectTransverseGreenSource.lean`
- **Statement:** Sum the explicit real-centered critical-feature prime–Gamma diagonal over the
  nearest-integer height lattice, with a sharp enough window budget to feed an exact 75% receiver.

## Goal

For a height cutoff `T`, construct a finite source-only quantity from the explicit pole, Gamma,
and absolutely convergent von Mangoldt terms in
`criticalFeaturePrimeGammaSourceDiagonal k`, `k : ℤ`, and prove a quantitative upper bound whose
leading constant is below the `1/8` off-line census threshold after the existing
`64/2025` nearest-integer Ward–Green quantum is applied.

The result must be proved from the pre-divisor prime–Gamma formula.  An inequality stated directly
for a sum over Xi zeros is a receiver restatement and does not discharge this card.

## Exact dependency-closed receiver

Already Lean-proved:

1. every strict-right Xi multiplicity copy is detected by its nearest integer feature with charge
   at least `64/2025`;
2. every fixed-feature Ward–Green trace is bounded by an explicit prime–Gamma source diagonal;
3. total zero multiplicity splits as on-line multiplicity plus twice strict-right multiplicity.

Needed source estimate: a lattice-window bound strong enough to imply that strict-right
multiplicity is at most one eighth of total multiplicity.

The maintained receiver uses three adjacent lattice centers.  The conceptual nearest-plus-adjacent
argument gives `84/25` units of Hermitian mass per strict-right copy, hence `42/25`
corrected-source charge after global holomorphic scalarization.  Therefore a corrected lattice
ceiling `(21/100) N` implies strict-right multiplicity at most `N/8` and at least `3N/4` copies on
the line.  In particular the requested stronger ceiling `(4/25) N` is already sufficient.

## Approach

1. Expand the four source cups defining `criticalFeaturePrimeGammaSourceDiagonal` into pole,
   Gamma, and von Mangoldt terms.
2. Sum each rational Cauchy translate over a finite integer lattice before any divisor expansion.
3. Use exact rational-lattice identities or monotone integral comparison for tails; preserve
   cancellation between reflected source cups whenever absolute values lose the required constant.
4. Compare the resulting leading term symbolically with the Riemann–von Mangoldt census.
5. Formalize the strongest dependency-closed source theorem.  If the `1/8` margin fails, record the
   exact sharp obstruction and derive the best proportion coefficient instead.

## Hostile falsifiers

- Summing `xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceDiagonal` after rewriting it
  as a zero sum is circular for this producer.
- The existing uniform constant `fiveShiftWardGreenUpperConstant` is intentionally coarse and may
  destroy every useful density constant.
- Replacing the lattice window by the whole real line may reconstruct nonholomorphic divisor mass
  rather than yield an independently bounded source.
- Absolute-value bounds on all four prime–Gamma cups may lose the reflection cancellation needed
  for 75%.
- A theorem whose premise is already the desired lattice budget is only an interface, not progress.

## Gates

- [x] 0 → 1: well-posed source-pure target and exact receiver identified
- [x] explicit finite lattice source formula
- [x] exact rational `1/8` receiver margin proved
- [x] hostile circularity audit passed for raw and corrected algebraic budgets
- [x] complete paper proof of raw no-go, exact diagonal subtraction, and 75% receiver
- [x] Lean theorem and targeted build
- [x] axiom and module lint audit (standard `propext`/choice/quotient axioms only; global lint's
      remaining failures are unrelated pre-existing umbrella reachability defects)
- [x] exact spectral classification of the corrected excess
- [x] construct a genuinely pre-divisor replacement for the zero-indexed critical-line subtraction
- [ ] prove its pole--Gamma--von-Mangoldt upper bound at scale `(4/25) N`

## Submicroscopic scalar-covariance no-go

The new thin-strip contour and centered real-shift extractor remove the old provenance objection:
both are defined from continued prime--archimedean source values before a zero list is formed.  The
remaining issue is quantitative, not definitional.

Let `K : R -> R` be a continuous even finite-displacement selector with `K(0)=1`.  For a packet of
two distinct simple points separated by `d`, its scalar diagonal approximation is

```text
2 + 2 K(d).
```

Continuity at zero forces `K(d)>0` for some nonzero arbitrarily small `d`, so this approximation is
strictly larger than exact diagonal mass `2`.  Consequently no continuous normalized scalar shift
kernel can be an unconditional lower approximation to diagonal multiplicity on all finite packets.
The two canonical source shifts expose the obstruction explicitly:

```text
transverse/positive-s-real shift:  K_eps(d) = eps^2 / (d^2 + eps^2) > 0,
real-height centered shift:        K_eps(d) = eps^2 / (eps^2 - d^2) > 0
                                  whenever 0 < |d| < eps.
```

For the corrected budget, subtracting either finite-shift scalar extractor therefore gives the
wrong majorant direction in the presence of a close pair.  Taking `eps -> 0` first recovers exact
diagonal multiplicity, but loses the uniform submicroscopic estimate needed when zero spacing is
`1 / log T`.

**Hostile scope audit.** This does not prove that Xi has close pairs, nor rule out an Xi-specific
arithmetic cancellation.  It rules out deriving the needed majorant from continuity, normalization,
and scalar shift extraction alone.  A live successor must keep signed off-diagonal matrix covariance
through scalarization or add a genuine quantitative zero-repulsion/pair-correlation input.

## No-go closure

- **Exact killing theorem/mechanism:**
  `card_mul_thirtyTwo_twentyFive_le_rawLatticeBudget` proves every multiplicity copy deposits at
  least `32/25` in the raw nearest-integer prime--Gamma diagonal.  The nominal 75% source scale is
  `8/2025`; `(32/25)/(8/2025)=324`.  Therefore
  `rawLatticeBudget_threeQuartersScale_forces_empty` proves that raw target can hold only for an
  empty packet.  Summing uncorrected diagonals is dead.
- **Strongest positive survivor:** subtract the exact critical-line feature energy before lattice
  summation.  `criticalFeatureHermitian_add_line_le_two_sourceDiagonal` sharpens the sector bound
  on the line, and
  `finite_strictRight_card_mul_thirtyTwo_twentyFive_le_offLineLatticeBudget` gives the corrected
  count without the coarse Ward constant.  The exact receiver is
  `three_quarters_line_of_sharp_primeGammaOffLineLatticeBudget`.
- **New insight:** diagonal subtraction changes the useful source threshold from the impossible
  raw `8/2025` scale to the sharp corrected `4/25` scale.  Abel traces converge to the correction,
  but are still divisor-indexed; the remaining producer must evaluate or dominate the corrected
  Abel lattice budget using only pole, Gamma, and von Mangoldt data.
- **Status:** active.

## Hostile source audit of the corrected budget

The notation `criticalFeaturePrimeGammaOffLineExcess` does not make the corrected quantity
pre-divisor.  Its second term is `criticalLineCriticalFeatureEnergyTrace`, an explicit sum over the
Xi divisor restricted by the predicate `Re rho = 1/2`.  The Abel approximants retain the same
zero-indexed trace.  Therefore the requested statement

```text
correctedBudget <= (4/25) N
```

is not yet a pole--Gamma--von-Mangoldt theorem: with the current definition it is an off-line
spectral-energy estimate whose proved receiver is the desired 75% zero-proportion statement.

Lean now proves the exact two-sided classification

```text
(1/2) offLineEnergy(t)
  <= criticalFeaturePrimeGammaOffLineExcess(t)
  <= offLineEnergy(t).
```

Equivalently, `offLineEnergy <= 2*excess` is the existing sector bound and the new theorem
`primeGammaOffLineExcess_le_offLineCriticalFeatureEnergyTrace` is its converse comparison.  It also
proves:

```text
criticalFeaturePrimeGammaOffLineExcess(t)=0  <-> RH,
correctedLatticeBudget(K)=0 <-> RH           (K nonempty).
```

This is the exact obstruction: a successful producer must build the discontinuous critical-line
projector before divisor expansion, or replace it by a centered source covariance with a proved
arithmetic ceiling.  Merely expanding the first term into four source cups and retaining the
zero-indexed subtraction is circular.

## Log

- 2026-08-16 — card created after improved declaration search found an unconditional nearest-integer
  Ward–Green quantum and fixed-feature prime–Gamma Hermitian majorant, but no lattice-summed source
  budget.
- 2026-08-16 — Formalized raw lattice no-go, exact line/off-line source separation, corrected
  lattice budget, Abel convergence, multiplicity-exact count, and sharp 75% receiver in
  `HedenmalmCriticalFeatureLatticePrimeGammaBudget.lean`.  Targeted Lean build passed.  mpmath
  confirmed the raw factor-324 obstruction and exposed the old Ward constant `C ≈ 4645.542`; the
  sharp corrected receiver eliminates `C` entirely.
- 2026-08-16 — Hostile pre-divisor audit found that the correction itself is a zero-indexed
  critical-line projector.  Formalized the reverse comparison `excess <= offLineEnergy`, the
  fixed-channel zero iff RH theorem, and the nonempty lattice zero iff RH theorem.  Current
  `(4/25)N` target remains the 75% arithmetic core, not a proved source consequence.
- 2026-08-28 — Formalized the three-center Hermitian quantum.  The maintained conceptual proof
  gives local floor `84/25`; corrected charge `42/25` makes `(21/100)N` sufficient and therefore
  already accepts the requested `(4/25)N` premise.  Retired the sharper 49-coefficient Bernstein
  certificate because it changed only receiver slack while imposing substantial elaboration cost.
- 2026-08-28 — Tested joint three-center holomorphic phase cancellation.  An exact `59/100`
  certificate existed but required 121 rational Bernstein coefficients, compiled in roughly three
  minutes, and could not lift to a source-only lattice inequality without divisor-dependent channel
  selection.  Retired that implementation.  Preserved the strongest cheap positive survivor:
  nearest-cell coercivity `3/5` and local three-center holomorphic quantum `242/125`.  These local
  theorems are explicitly not claimed as a global budget improvement.
- 2026-08-28 — Confluent fixed-safe-pole audit: Cayley/Malmquist jets can supply many local modes
  without moving the pole toward the Euler boundary, and the corpus already gives exact Cauchy-jet,
  Toeplitz, all-derivative Euler, and Poisson order-space laws.  Scaling shows depth divided by pole
  distance is effective prime bandwidth; reaching zero spacing `1/log T` still reaches prime length
  `T`.  Existing Gamma-sewn recovery is contractive but first-jet transparent, so it cannot supply
  coefficient-faithful quadratic Weil covariance.  Survivor: preserve the full confluent source
  matrix and seek a direct prime covariance bound; scalar contraction and residue extraction are
  not producers.
- 2026-08-28 — Rectangular prime--polar audit: the corpus now gives an exact source-only finite
  formula and identifies its negative part with square-sampled positive excess of the von Mangoldt
  window.  The available near-linear square-energy bound is equivalent to an RH-strength abscissa
  statement, not an unconditional density estimate; using it for `75%` would merely rename the
  open prime-cancellation problem.
- 2026-08-28 — Source-aligned restricted-Weil audit: every finite nonpositive block injects into a
  finite peripheral Gamma--Slepian head, and every nonpositive vector forces literal finite
  von-Mangoldt compression to overcompensate scalar Gamma plus polar mass by `3/4` of head norm.
  This is a genuine pre-divisor source obstruction.  Two quantitative bridges are absent:
  asymptotic finrank/trace control of the moving Gamma--Slepian head, and an unconditional
  divisor-free comparison from restricted-Weil Morse index to off-line zero multiplicity.  These,
  not stronger local receiver constants, are the viable next conjecture targets.
- 2026-08-28 — Formalized the submicroscopic scalar-covariance no-go.  Every continuous normalized
  scalar displacement kernel is positive at some nonzero arbitrarily close separation and therefore
  overcounts the exact diagonal on a two-point packet.  The transverse Poisson and centered
  real-height kernels exhibit the obstruction explicitly.  Positive survivor: preserve signed
  matrix covariance through scalarization or prove genuine quantitative pair repulsion.
- 2026-08-28 — Formalized the archimedean contour reduction.  The exact corrected source budget is
  von Mangoldt plus pole--Gamma minus thin contour; when lattice cardinality is `o(N)`, the uniformly
  bounded von Mangoldt channel contributes `o(N)`.  Thus the requested `4/25` theorem is equivalent
  up to `o(N)` to a pole--Gamma/thin-contour upper bound.  Prime-window optimization and further
  receiver constants cannot close this leading target.
