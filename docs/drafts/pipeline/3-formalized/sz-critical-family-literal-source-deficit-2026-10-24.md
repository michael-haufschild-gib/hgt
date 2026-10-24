# Literal Suzuki deficit on the compact critical family

- **ID:** sz-critical-family-literal-source-deficit-2026-10-24
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** compact-L² critical first variation and compact critical-family positivity.
- **Statement:** Every sufficiently high nonzero dyadic critical source has a strict positive first-order deficit for its own literal Suzuki pairing, at every allowed compact truncation.

## Proof route and blocker

The complete signed source must acquire a source-derived critical bound. The compact-L²
first variation removes the regularity restriction from the literal source limit. This
application removes the smoothing sequence from the existing critical-family result:
the actual arithmetic source itself satisfies the finite-shift inequality. The
restricted family does not exhaust all receiver tests; universal arithmetic sign and
uniform growing-aperture control remain open.

## Exact statement

There is an integer M₀ such that, whenever M≥M₀, V>0,
V≥criticalTruncationThreshold, S is a dyadic scale block at M, and b is a nonzero
real coefficient pattern on S, the source g=criticalTruncatedTest(V,S,b) satisfies

`E(g)=compactFullWeilEnergy(g)>0`,

and, for all sufficiently small positive ω,

`ω E(g)/2 < autocorr(g,0) - suzukiCriticalSourcePairing(g,ω)`.

In particular `suzukiCriticalSourcePairing(g,ω)<autocorr(g,0)`.
The positive-shift neighbourhood may depend on V, S, and b. There is no smoothing
index and no claim of one neighbourhood uniform over growing truncations.

## Dependency-closed paper proof

1. `criticalTruncatedTest` is continuous with compact support, hence belongs to L².
   `exists_lipschitz_criticalTruncatedSource` supplies its global Lipschitz bound.
   `integrableOn_levy_of_lipschitz` therefore proves finite Lévy energy; this is
   derived from the concrete source, not imposed as an extra analytic premise.
2. The compact-L² first-variation theorem gives the extended-real limit

   `(autocorr(g,0)-sourcePairing(g,ω))/ω → J(g)+γ₀ autocorr(g,0)-2 fullPairing(C_g)`.

   Here J is the nonnegative extended integral. The integrability from step 1
   identifies J with the ordinary real Lévy integral. The exact compact finite-jump
   Weil formula identifies the displayed finite limit with E(g).
3. `exists_compactFullWeilEnergy_criticalTruncatedTest_pos` gives a common M₀ and
   E(g)>0 at all allowed truncations and all nonzero dyadic patterns. The open
   extended-real interval `(E(g)/2,+∞]` contains the limit. Eventual membership and
   ω>0 imply the stated strict deficit after multiplication by ω.

All prime, Gamma, and polar terms remain in the source and energy. No continuity
of a divergent totalized Bochner integral is used.

## Conjecture outcome and next question

The conjecture that the actual critical source inherits the strict finite-shift
deficit is proved in Lean: the larger source-domain theorem removes the
smoothing step. It does not turn family positivity into universal positivity.
The remaining question is a signed, norm-controlled transfer from these concrete arithmetic sources to all receiver
tests, or a direct bound on the complete prime-lag source.

Verdict: **BRIDGE**. No external novelty claim.

## Gates

- [x] Concrete source statement and complete paper proof.
- [x] Finite energy and positivity derived from existing source theorems.
- [x] Compact-L² capstone compiled and audited.
- [x] Literal-family theorem compiled and all public transitive axioms audited.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalLiteralFamilyContraction.lean`.

- `RHTower.tendsto_suzukiCriticalLiteralFamily_firstVariation`
- `RHTower.exists_suzukiCriticalLiteralFamily_strict_deficit`

The direct canonical check passed:

```sh
cd formal
lake --old env lean GaloisForLFunctions/RHTower/Suzuki/SuzukiCriticalLiteralFamilyContraction.lean
```

Both declarations and all 42 declarations of the compact-L² prerequisite chain
were inspected with `#print axioms`. Every transitive axiom is one of `propext`,
`Classical.choice`, and `Quot.sound`. No analytic input is left as an assumption
interface; finite energy and positivity come from the specified concrete family.
