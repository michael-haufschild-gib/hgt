# PW absolutely admissible unbounded matrix endpoint tomography

- **ID:** PW-AAUPM
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every symmetric pairwise-positive countable PW matrix with `∑ₙ |aₙ|q₀ⁿ < ∞` is zero if its antidiagonal endpoint energy is dark at every physical node; no entry bound is assumed.

## RH chain killed

`PW endpoint darkness → positive response uniqueness → source balance → Borel partner balance → shared Ward endpoint → RH` cannot use an unbounded but absolutely endpoint-admissible positive quadratic matrix history.

## Proof

For `q_j=exp(-(j+1))`, set `bₙ=aₙq₀ⁿ`. Absolute admissibility bounds `b` and proves endpoint-energy summability at every `q_j`. The exact law `q_{j+1}=q₀q_j` turns shifted endpoint darkness into bounded power-series darkness, so corpus zero-sequence uniqueness gives `aₙ=0`. Even-antidiagonal induction and pairwise positivity kill every matrix row.

The Gram kernel `K(i,j)=2ⁱ2ʲ` has `aₙ=(n+1)2ⁿ`, is absolutely admissible because `2q₀<1`, pairwise-positive, and not uniformly bounded. Thus theorem strictly extends bounded corpus result.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekAbsolutelyAdmissibleMatrixEndpointTomography`
- Route kill: `schwarzschildParikhWilczekAbsolutelyAdmissiblePairwisePositiveEndpointDarkRouteKilled`
- Semantic convergence: `summable_pwMatrixEndpointEnergy_of_absoluteAdmissible`
- Strict witness: `pwExponentialGramKernel_absolutelyAdmissible`, `pwExponentialGramKernel_not_uniformlyBounded`
- `lake env lean` PASS; targeted `lake build` PASS.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella wired. Repository-wide lint remains red only on unrelated concurrent unwired modules; this module is not reported.

## Survivor

PW-B must use an indefinite, non-absolutely-summable/singular, nonlinear, nonclosed/domain-excluding, or nonpointwise source law.

## Novelty audit

Corpus searches found only bounded pairwise-positive tomography. Literature searches through 2026-08 found no PW endpoint-tomography/countable-kernel analogue; classical power-series uniqueness is an ingredient, not this route no-go.
