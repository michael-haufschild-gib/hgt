# HB arbitrary unbounded dissipative diagonal response polarity no-go

- **ID:** HB-UNBDD-DIAG-POLARITY
- **Stage:** 3-formalized
- **Type:** ROUTE-CLASS NO-GO THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` HB source-fixed two-leg opposite-sign core
- **Statement:** For arbitrary unbounded dissipative/antidissipative partial operators, every existing exact response on a tilted reflected Xi pair has strict standard-passive diagonal source polarity; it cannot supply HB's opposite sign.

## Goal

Kill chain `exact tilted Teukolsky source -> arbitrary linear passive resolvent response -> diagonal source-response optical observable -> opposite HB full-cokernel sign -> Ward cancellation -> RH`.

## Gates

- [x] 0 → 1 in-progress: corpus chain and exact arbitrary-domain statement fixed
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PAPER-PROVED]`
- [x] 2 → 3 formalized: direct Lean, targeted build, axiom audit
- [ ] 3 → 4 publication-ready: standalone paper

## Conjecture loop

1. `[FALSIFIED]` Diagonal passive response could produce the missing HB sign. Corpus theorem
   `hbXiPeierlsCanonicalFullCokernelTwoLevelKMSResponseAt_I_im_neg_of_tilt` proves standard
   passivity has the opposite polarity off wall.
2. `[CONJECTURE]` The obstruction is universal: for any partial dissipative `A`, `Im z>0`, nonzero
   source `s`, and response `(A-z)x=s`, one has `Im <x,s><0`; the antidissipative lower-half-plane
   law is reversed. Apply both laws to the exact Schwarz Xi pair.

## Proof [PAPER-PROVED]

Let `(A-z)x=s`, with `s != 0`. Then `x != 0`, since every partial linear map sends its zero-domain
vector to zero. Sesquilinearity gives
`Im<x,s> = Im<x,A x> - Im(z)||x||^2`.

If `A` is dissipative and `Im z>0`, the first term is nonpositive and the second is strictly
negative, so `Im<x,s><0`. If `A` is antidissipative and `Im z<0`, the first term is nonnegative
and subtracting `Im(z)||x||^2` is strictly positive, so `0<Im<x,s>`. No closedness, maximality,
density, or surjectivity is used.

For tilted `q`, corpus source incidence makes the exact source at `q` and `copyConj q` nonzero.
The angular parameter has nonzero imaginary part, and its Schwarz-copy parameter has the negative
imaginary part. Split on its sign and apply the two preceding laws to every possible response on
the matching dissipative/antidissipative legs. Thus every existing diagonal response has strict
standard-passive polarity and none can have HB's required opposite polarity.

## Hostile audit

- Strictness fails for zero source; exact tilted Teukolsky sources are corpus-proved nonzero.
- No surjectivity is claimed: source exclusion remains an invalid/no-response branch, not an opposite-sign response.
- Result kills only diagonal response-as-left-leg observables. Independently transforming left-QNM legs remain the exact HB survivor.
- Operator identity is classical. New claim is exact arbitrary-domain reflected Xi/Teukolsky route closure.

## Formal certificate

- Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingHBArbitraryUnboundedDissipativeDiagonalResponsePolarityNoGo`
- Theorem: `d4HBArbitraryUnboundedDissipativeDiagonalResponsePolarityRouteKilled`
- Direct `lake env lean` and targeted `lake build` pass.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella wired. Global lint has only pre-existing unreachable-module failures; this module is reachable and clean.

## Novelty audit through August 2026

The dissipative pairing identity is classical. Corpus and literature searches found no theorem applying it to the exact tilted reflected Xi/Teukolsky source pair to rule out every arbitrary-domain passive diagonal HB producer. Exact route-class closure is the new result.

## No-go closure

Killed: arbitrary unbounded partial linear passive response used itself as HB left leg through diagonal source pairing. Positive survivor: independently transforming left-QNM leg. Other logical escapes require nonpassive, nonlinear, or no-response dynamics.
