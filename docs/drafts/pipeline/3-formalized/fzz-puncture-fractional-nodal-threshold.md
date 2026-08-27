# FZZ puncture sharp fractional nodal threshold

- **ID:** FZZ-P-FNT
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + SHARP BOUNDARY + POSITIVE SURVIVOR
- **Parent:** FZZ-P-GSL
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION] [SHARP BOUNDARY] [POSITIVE SURVIVOR]` A target-centered fractional FZZ source germ `x^α 1_(0,1)` admits a nonzero embedded `L²` continuum mode exactly when `α>1/2`; solution is unique almost everywhere.

## Goal

Replace coarse “first-order node” survivor by exact local regularity wall. Determine weakest pure-power
source cancellation that removes resolvent pole in `L²`.

This does not prove RH and does not derive source exponent or node location from FZZ dynamics.

## Gates

- [x] 0 → 1 in-progress: target-centered fractional germ frozen after corpus search
- [x] 1 → 2 fully-proven: exact `L²` iff, pointwise equation, nonzero state, uniqueness
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claim

For real exponent `α`, define source and formal state in target-centered coordinate `x` by

`v_α(x)=x^α 1_(0,1)(x)`,

`f_α(x)=-x^(α-1)1_(0,1)(x)`.

Let a fractional point mode mean existence of nonzero `f∈L²(ℝ)` satisfying

`x f(x)+v_α(x)=0`

almost everywhere. Then

`FZZPunctureFractionalPointMode α ↔ 1/2 < α`.

Every solution equals `f_α` almost everywhere. In particular, `α=1/2` is excluded and
`α=3/4` is realized unconditionally.

## Complete paper proof

Away from null singleton `{0}`, continuum equation divides uniquely by `x`, so any solution is
`f_α=-x^(α-1)1_(0,1)` almost everywhere. Its square norm is

`|f_α(x)|²=x^(2(α-1))1_(0,1)(x)`.

The endpoint integral `∫₀¹x^β dx` is finite iff `β>-1`. Taking `β=2(α-1)` gives

`2(α-1)>-1 ↔ α>1/2`.

Source and state cancel pointwise by `x·x^(α-1)=x^α` for `x>0`. State is nonzero on the positive-
measure interval `(0,1)`. This proves necessity, sufficiency, and uniqueness.

## Hostile review and priority verdict

- Half-order threshold is target-centered local model. Translation to arbitrary energy is
  measure-preserving but not needed for route invariant.
- Pure powers do not cover logarithmic corrections or arbitrary Hölder germs.
- Result classifies representative continuum equation, not full self-adjoint interacting operator,
  coupling self-consistency, multiplicity, or generalized spectrum.
- Square-root boundary is excluded because squared state is `x⁻¹`, with logarithmic divergence.
- A strict sublinear node such as `α=3/4` already works. Earlier first-order survivor was sufficient,
  not sharp.
- Any fixed `α>1/2` works in every target-centered chart. Local regularity is nonselective and cannot
  locate zeta ordinates.
- Classical Friedrichs/resolvent literature treats embedded states and threshold resonances; audited
  primary sources include arXiv:hep-ph/9811383, math/0604277, math-ph/0509062, and arXiv:1108.5813.
  No audited source states this exact FZZ-puncture fractional iff or provides Lean formalization.

Verdict: power-integrability mechanism `[REDISCOVERED]`; exact route-specialized classification and
corrected FZZ boundary `[NEW] [BRIDGE]`, external priority provisional.

## Failed conjecture before pivot

Conjecture C9 proposed excluding every fixed finite exponential-type source using zeta-zero density.
Corpus theorem `exists_xiSimpleCriticalZeroCount_linear_of_cofinite_exponentialType_zeros` yields only
a linear envelope if such source vanishes on cofinite simple critical ordinates. Available
unconditional Lean census `exists_log_le_xiPosCriticalZeroCount` is logarithmic and does not
contradict that envelope; superlinear simple-critical density is open. C9 was not promoted.

## No-go closure

- **Killed shortcut:** FZZ embedded occurrence requires a full first-order analytic node.
- **Strongest positive survivor:** source vanishing order strictly greater than `1/2`; state is unique
  and its singularity order is strictly better than `-1/2`.
- **Sharp excluded wall:** `α=1/2` and all weaker pure-power nodes.
- **New insight:** local carrier burden is exactly more-than-half-order cancellation, not analyticity
  or integer order. This widens possible singular/nonanalytic FZZ interactions but makes selectivity
  problem sharper: source dynamics must globally locate nodes and control their local order.
- **Remaining core:** derive target set and `>1/2` cancellation coefficient-faithfully from literal
  winding-condensate equations, with self-consistent spectral construction and Mellin landing.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/FZZCigarPunctureFractionalNodalThreshold.lean`
- Integrability threshold: `fzzPunctureFractionalFormalState_memLp_iff`
- State uniqueness: `fzzPunctureFractionalEigenEquation_state_unique`
- Exact occurrence law: `fzzPunctureFractionalPointMode_iff`
- Premise-free boundary witnesses: `not_fzzPunctureFractionalPointMode_at_half`,
  `fzzPunctureFractionalPointMode_three_quarters`
- Direct `lake env lean` passed.
- Targeted build
  `lake build GaloisForLFunctions.RHTower.FZZCigarPunctureFractionalNodalThreshold`
  passed (`11557/11557`).
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- Formal lint was run; it is blocked only by unrelated concurrent unwired modules
  `QuantumRecurrenceScalarResolvedSeparationLaw`, `Sieve.MatomakiTeravainenC1PaperScale`,
  `Sieve.MatomakiTeravainenC1Schedule`, `ThetaCuspLikelihoodFourthSixthSpectralDomination`, and
  `UniversalQuantumRecurrenceInformationHierarchyLaw`. This module is directly reachable from
  umbrella and passes direct/targeted checks.

## Log

- 2026-08-27 — finite-exponential-type density conjecture failed at missing unconditional
  superlinear simple-zero census; pivoted using corpus endpoint-power integrability.
- 2026-08-27 — exact half-order threshold, unique state, excluded borderline, and strict fractional
  witness paper-proved and formalized.
