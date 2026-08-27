# BM second-harmonic Peierls-response odd-charge classification

- **ID:** HB-BM-PROC
- **Stage:** 3-formalized
- **Type:** CLASSIFICATION + COUNTERMODEL + NO-GO
- **Parent:** HB
- **Statement:** `[LEAN-PROVED] [NEW] [CLASSIFICATION]` Any response-corrected reflected BM current cancels iff composite source--response--exponent charge is reflection-odd. Pointwise oddness alone admits unconditional singular correction and cannot imply RH.

## Goal

Replace vague missing Peierls-response premise by exact necessary-and-sufficient law, then test whether
that law alone has RH content.

## Gates

- [x] 0 → 1 in-progress: odd-charge conjecture frozen after corpus search
- [x] 1 → 2 fully-proven: exact factorization, global classifier, unconditional countermodel
- [x] 2 → 3 formalized: direct Lean, targeted build, umbrella, axiom audit
- [ ] 3 → 4 publication-ready: external priority review

## Exact frozen claims

For response correction `K(q)`, literal source amplitude `A(q)`, and BM exponent `λ(q)`, define

`H_K(q)=A(q)K(q)λ(q)`.

Then corrected reflected current is exactly

`J_K(q)=-(H_K(q)+H_K(Jq))`.

Consequently `J_K(q)=0 ↔ H_K(Jq)=-H_K(q)`, and universal cancellation is precisely global
reflection oddness of `H_K`.

Define pointwise correction

`K_height(q)=Im(q)/(A(q)λ(q))`.

Its charge equals `Im(q)` off wall and zero on wall. This is reflection-odd, so `J_K(q)=0` for every
Xi fibre unconditionally.

## Complete paper proof

Canonical current is `-λ`; distributing corrected source coefficient gives exact negative charge
sum. Zero-sum algebra yields oddness classifier.

Off wall, `A(q)` and `λ(q)` are nonzero, so cancellation in quotient defining `K_height` gives
`H(q)=Im(q)`. On wall, angular mixing makes `A(q)=0`; division-by-zero convention and outer source
factor give `H(q)=0`. Functional-equation reflection preserves wall condition and negates Xi height,
so piecewise charge is odd. Exact classifier gives universal zero current with no RH premise.

## Hostile review and novelty verdict

- Countermodel is deliberately pointwise and singular at source-vanishing wall. It is not claimed to
  be a physical retarded-minus-advanced propagator.
- This is its purpose: it proves algebraic reflection oddness alone is insufficient and locates
  missing physical content in regularity/locality/causality.
- Canonical left connection covectors do not exclude countermodel; they only fix radial coordinates.
- Primary-source searches on Peierls/QNM reflection and excitation coefficients found no exact
  source--response--exponent charge classifier or punctured-height countermodel.

Verdict: odd-cocycle algebra `[REDISCOVERED]`; coefficient-faithful BM/Peierls classification and
countermodel `[NEW] [CLASSIFICATION]`, external priority provisional.

Primary audit: Green et al., arXiv:2210.15935; Spiers--Pound--Moxon, arXiv:2305.19332;
Mitman et al., arXiv:2208.07380; Silva et al., arXiv:2404.11110.

## No-go closure

- **Exact killing mechanism:** unconstrained response correction may divide by literal source and
  exponent, manufacturing any reflection-odd charge.
- **Strongest positive survivor:** composite incidence charge `H=A K λ` is unique invariant; its
  reflection oddness is necessary and sufficient for cancellation.
- **New insight:** remaining HB theorem must derive `K` from one global augmented Peierls propagator
  with analytic/causal regularity strong enough to forbid punctured-height correction. Oddness,
  radial normalization, and coefficient matching alone are exhausted.
- **Status:** dependency-closed paper proof and Lean formalization complete.

## Lean formalization

- Module:
  `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSecondHarmonicPeierlsResponseOddChargeClassification.lean`
- Exact charge factorization:
  `d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_neg_charge_add`
- Pointwise/global oddness classifiers:
  `d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff`,
  `forall_d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent_eq_zero_iff_odd`
- Countermodel charge law:
  `d4BMXiSecondHarmonicPuncturedHeightResponseCharge_eq`,
  `d4BMXiSecondHarmonicPuncturedHeightResponseCharge_reflection_odd`
- Unconditional cancellation:
  `forall_d4BMXiSecondHarmonicPuncturedHeightResponseCorrectedReflectionCurrent_eq_zero`
- Direct `lake env lean` passed.
- Targeted module build passed.
- `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.

## Log

- 2026-08-27 — conjectured from corpus reflection-odd charge laws and exact BM current.
- 2026-08-27 — charge classification and unconditional punctured-height countermodel proved in Lean.
