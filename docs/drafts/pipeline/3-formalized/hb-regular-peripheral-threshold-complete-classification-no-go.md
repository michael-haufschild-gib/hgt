# HB regular peripheral threshold: complete cancellation classification

- **ID:** hb-regular-peripheral-threshold-complete-classification-no-go
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** In the regular finite-variation peripheral HB class, asymptotic AIME cancellation is impossible with a phase-blind threshold atom and automatic but uniquely target-fitted with phase-adapted atoms.

## Goal

Kill the complete regular peripheral-spectrum HB producer class in the chain

`regular HB response -> radiative ++ cancellation -> fixed Ward orientation -> shared HB/FZZ-P/PW-B/RBH extinction -> RH`.

## Corpus basis

- `d4BMPassivePeripheralSpectralPhaseFullPoleNumerator_tendsto_zero_iff_zeroMode`: cancellation iff the threshold coefficient equals minus AIME plus passive mass.
- `d4FundamentalQNMCrossBranchAIMENumerator_neg`: half-turn seed covariance is odd.
- `d4FundamentalQNMCrossBranchAIMENumerator_xi_ne_zero_iff`: the AIME numerator is nonzero on every Xi descendant for nonzero seed amplitude.
- `d4BMPassivePeripheralSpectralPhaseBlindThresholdCancellationRouteKilled`: one source-independent threshold atom cannot cancel both half-turn sectors.

## Paper proof

Write `A(a,q)` for the AIME numerator and `M(m,q)` for the passive stationary mass numerator. Strictly damped finite-variation modes and the `L¹` real-axis continuum tend to zero. Hence a regular peripheral completion with zero-frequency atom `z` cancels asymptotically iff

`z = z*(a,m,q) := -(A(a,q) + M(m,q))`.

This proves both existence and uniqueness: choosing `z*` cancels every admissible transient spectrum, while every cancelling choice equals `z*`. Cubic half-turn covariance gives

`z*(-a,m,q) - z*(a,m,q) = 2 A(a,q)`.

For `a != 0`, the right side is nonzero at every Xi descendant. Therefore the two canonical atoms differ: a phase-blind atom cannot cancel both sectors. Conversely, allowing phase dependence makes cancellation automatic by inserting the unique target value `z*`; existence then contains no spectral selection. Thus every response in this regular class is either impossible as a source-independent completion or tautologically target-fitted as a source-adapted completion.

## No-go closure

- **Exact killing mechanism:** terminal-value uniqueness reduces all regular spectral data to one threshold atom; half-turn covariance makes a common atom impossible, while the unique phase-adapted atom cancels by construction.
- **Strongest positive survivor:** an independently source-derived zero-mode law must force the exact odd jump `2 A(a,q)` before the desired cancellation is imposed. Otherwise the response must leave the class through singular non-Rajchman/infinite-variation or domain-sensitive dynamics.
- **New insight:** phase sensitivity alone does not rescue HB. Its zero mode must be predeclared by the physical source law; post hoc phase adaptation is nonselective.
- **Status:** paper proof and Lean formalization dependency-closed. Internal corpus search found the two boundary cases but no combined complete classification. August 2026 literature audit (`2112.11168`, `2305.19332`, `2605.16492`, `2607.19492`) found AIME, second-order sources, and QNM perturbation frameworks, not this third-order threshold classification.

## Formalization

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingAIMERegularPeripheralThresholdCompleteNoGo`.

Closed capstone: `d4BMPassiveRegularPeripheralThresholdCancellationRouteKilled`.

`lake env lean` and target-only `lake build` pass. Axioms: `propext`, `Classical.choice`, `Quot.sound` only. Global lint is blocked only by unrelated concurrently unwired modules; this module is umbrella-reachable and lint-clean.

## Gates

- [x] 0 -> 1: source-pure route class and RH chain identified
- [x] 1 -> 2: complete paper proof, `[PROVED HERE]`
- [x] 2 -> 3: Lean theorem, target build, axiom audit
- [ ] 3 -> 4: publication-ready preprint
