# One-prime rough-primitive Hardy tail — Lean certificate

- **ID:** `suzuki-one-prime-rough-primitive-hardy-tail-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:**
  `../../../2-fully-proven/new_scientific_knowledge/suzuki/suzuki-one-prime-rough-primitive-hardy-closure.md`
- **Lean module:**
  `formal/GaloisForLFunctions/RHTower/SuzukiOnePrimeRoughPrimitiveHardyTail.lean`
- **Status:** `[FORMALIZED ANALYTIC CORE] [AXIOM-CLEAN] [NOT RH]`

## Certified theorem surface

| Statement | Lean declaration |
|---|---|
| far-end squared tail | `suzukiPolynomialIBPFarTailNormSq` |
| near-diagonal squared remainder | `suzukiPolynomialIBPNearTailNormSq` |
| exact far-end threshold `κ < σ` | `integrableAtTop_suzukiPolynomialIBPFarTailNormSq_iff` |
| exact depth threshold `κ + 3/2 < N` | `integrableAtTop_suzukiPolynomialIBPNearTailNormSq_iff` |
| exact joint threshold | `integrableAtTop_suzukiPolynomialIBPTails_iff` |
| concrete `(κ,σ,N)=(2/3,3/4,3)` | `suzukiOnePrimeThirdIBPTails` |

These are the two load-bearing frequency tails produced by the paper proof's far/near split after
repeated integration by parts. Both directions of both thresholds are formalized; the boundary
cases diverge.

## Scope boundary

This module does not represent the vector-valued Fourier transform, polynomial group propagator,
or completed Suzuki mode by an abstract premise. Backward block-primitive preservation and the
operator one-block estimate remain formalization gates. The paper theorem composes those analytic
arguments with already paper-proved literal source assembly, complementary flux, and formalized
dyadic coverage.

## Gates

- [x] exact far-end threshold formalized
- [x] exact near-diagonal threshold formalized
- [x] concrete one-prime point formalized
- [x] wired into `GaloisForLFunctions.RHTower`
- [ ] formalize backward block-primitive preservation
- [ ] formalize vector-valued polynomial-group one-block estimate
- [ ] formalize full one-prime completed-source corollary after infrastructure exists
