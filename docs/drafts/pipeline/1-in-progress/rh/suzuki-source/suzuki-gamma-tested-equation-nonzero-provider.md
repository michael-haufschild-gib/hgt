# Nonzero provider for the Suzuki-Gamma tested equation

- **ID:** suzuki-gamma-tested-equation-nonzero-provider
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiGammaMollifiedEquation.lean`
- **Statement:** Construct an explicit nonzero admissible profile `V` and function `G` satisfying `SuzukiGammaTestedEquation σ τ V G` in a nonempty parameter range.

## Goal

Replace the weak-equation premise in Suzuki-Gamma domain-upgrade theorems by a substantive source,
not merely prove logical consistency through the zero solution.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem `<name>`, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Corpus audit

The corpus contains four consumers of `SuzukiGammaTestedEquation` and no nonzero producer.  The
mollified-equation theorem starts from this tested identity; the later weak-domain upgrades retain
the same premise.  Existing Gamma-jump transpose and convolution lemmas provide downstream
regularity only after a weak solution is supplied.

The unconditional theorem `suzukiGammaTestedEquation_zero` proves consistency for every `σ,τ`.
It does not discharge the substantive existence problem because all resulting mollified fields
vanish.

## Exact mathematical obstacle

For a chosen nonzero `V`, the displayed test functional must be representable by integration
against an actual function `G`, rather than only by an abstract distribution.  This requires:

1. distributional integration by parts for `V′ - σV`;
2. transposition of the nonlocal Gamma jump;
3. sufficient regularity/integrability for the resulting operator to have a function-valued
   representative.

This is an analytic existence/domain problem.  It cannot be discharged for arbitrary `V,G`, and
definitional unfolding does not supply a nonzero witness.

## Candidate route

Start at `σ = 0` with a smooth compactly supported nonzero `V`.  Define the candidate response by
the strong expression corresponding to `(2L + R₀ - τ)V′ + V`.  Prove the strong-to-tested bridge
using compact-support integration by parts and the existing Gamma-jump transpose lemmas.  Then
audit the candidate response's measurability and integrability required by downstream upgrades.

## Hostile review

- Constant profiles are attractive formally but are outside the `L²` hypotheses used downstream.
- Defining `G` as an arbitrary distribution would change the declared interface and is rejected.
- An almost-everywhere nonzero-at-one-point artifact would be functionally zero and is not a
  substantive provider.
- No claim of nonzero existence is made until a function-valued strong-to-tested bridge is closed.

## Door passport

- **Door-1:** exact producer gap isolated; zero solution formalized separately.
- **Door-2:** SOTA/novelty audit deferred until a dependency-closed theorem exists.
- **Door-3:** proposed Lean route reuses existing transpose and mollifier infrastructure.

## Log

- 2026-08-13 — project-Prop audit nominated the tested equation (four consumers).
- 2026-08-13 — corpus search confirmed no producer; zero witness proved in Lean source.
- 2026-08-13 — nonzero function-valued representability isolated as open core; advanced to Stage 1.
