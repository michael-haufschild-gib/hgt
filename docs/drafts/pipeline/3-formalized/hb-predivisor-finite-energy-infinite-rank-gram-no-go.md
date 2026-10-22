# HB pre-divisor finite-energy infinite-rank Gram no-go

- **ID:** HB-FEIRG
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** The exact polarized HB cancellation kernel has no finite-energy complex-Hilbert Gram realization on `(0,1/2)`: its diagonal susceptibility dominates `x⁻²` and is not integrable.

## RH chain attacked

`source-selected infinite-rank Schwarz/Hermitian two-leg incidence → opposite HB Ward sign / radiative ++ extinction → common clock coherence → RH` cannot use a positive finite-energy Hilbert feature field.

## Corpus frontier

- `[CORPUS]` `d4PreDivisorOpticalCancellationPolarizedKernel_not_hasPositiveOpenSquareSeparationRankAtMost`: every finite-rank factorization is impossible.
- `[CORPUS]` `d4PreDivisorOpticalCancellationSusceptibility_at_xi`: pre-divisor profile is coefficient-faithful to the physical Xi-fibre susceptibility.
- `[CORPUS]` `routeP_not_integrableOn_translated_inverseSquare`: `x⁻²` is not locally integrable.
- `[OPEN CORE]` Infinite-dimensional positive Hilbert incidence can remain only with infinite hard-edge energy; indefinite, singular, or domain-changing incidence is not excluded.

## External frontier

- Pound--Wardell survey treats perturbative Einstein/Teukolsky and multiscale source evolution, not this susceptibility or its Gram-energy boundary: <https://arxiv.org/abs/2101.04592>.
- AIME work computes nonlinear excitation by contour overlaps, not a pre-divisor Hilbert Gram completion: <https://arxiv.org/abs/2112.11168>.
- Teukolsky QNM conserved-current work stresses its pairing is symmetric bilinear, neither positive definite nor known complete; it does not supply this positive finite-energy completion: <https://arxiv.org/abs/2210.15935>.

No exact analogue was found through 2026-08. General inverse-square nonintegrability is standard; candidate novelty is the exact source-faithful HB hard-edge obstruction and route classification.

## Paper theorem and proof

`[PAPER-PROVED]` For every complex inner-product space `E` and feature field `Phi : ℝ → E`, pointwise Gram equality
`inner (Phi x) (Phi y) = d4PreDivisorOpticalCancellationPolarizedKernel x y` on `(0,1/2)^2` forces
`¬ IntegrableOn (fun x => ‖Phi x‖^2) (0,1/2)`.

For `0<x<1/2`, put `A=x(3-x)`, `B=(1-x)(2+x)`, and
`N=A²(2-B)+B²(2-A)+2AB`. Then `0<A,B<2`, so every summand is nonnegative and `N≥B²(2-A)`. Also `A≤3x`, `2-A≥1/2`, and `(2-x)(1+x)≥3/2`. The reduced exact formula
`S(x)=54N(2-x)(1+x)/(A²B²)` therefore gives
`S(x)≥54·B²·(1/2)·(3/2)/(9x²B²)=(9/2)x⁻²≥x⁻²`.

If `S` were integrable on `(0,1/2)`, domination would make `x↦x⁻²` integrable there, contradicting the exact `integrableOn_Ioo_rpow_iff` endpoint criterion. For a Gram realization, setting `y=x` gives `inner (Phi x) (Phi x)=S(x)` and hence `‖Phi x‖²=S(x)`. Finite feature energy would therefore make `S` integrable, the same contradiction. No unproved dependency remains.

## Hostile verdict

`ROUTE CLASS KILLED`. Arbitrary infinite analytic expansions do not help because positive Gram diagonal equals feature norm-square. Result does not exclude indefinite Krein, renormalized/distributional, domain-excluding, support-changing, or sheet-changing incidence.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingPreDivisorFiniteEnergyInfiniteRankGramNoGo`
- Hard-edge bound: `d4PreDivisorOpticalCancellationSusceptibility_rpow_neg_two_le`
- Infinite susceptibility energy: `not_integrableOn_d4PreDivisorOpticalCancellationSusceptibility`
- Dimension-free Gram obstruction: `not_integrableOn_normSq_of_d4PreDivisorOpticalCancellationGram`
- Closed route theorem: `d4HBPreDivisorFiniteEnergyInfiniteRankGramRouteKilled`
- Direct `lake env lean` and targeted `lake build` pass; axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.

## Gates

- [x] 0 → 1: corpus-derived, exact RH chain, external audit, falsifiable statement
- [x] 1 → 2: complete paper proof and hostile boundary audit
- [x] 2 → 3: exact unconditional Lean theorem and axiom audit
