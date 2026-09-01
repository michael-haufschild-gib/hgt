# HB bounded dissipative reflected forcing no-go

- **ID:** HB-DISS-REFLECT
- **Stage:** 3-formalized
- **Type:** ROUTE-CLASS NO-GO
- **Source:** `rh-current-frontier-map.md` HB opposite-sign/source-Ward open core
- **Statement:** Every bounded dissipative/antidissipative angular pair has unique nonzero forced responses on the matching half-planes of both conjugate members of each tilted Xi orbit; bounded nonnormal passivity cannot force HB source extinction.

## Goal

Kill chain `exact tilted 2s Teukolsky source -> bounded causal dissipative boundary exclusion -> universal source extinction -> RH`.

## Gates

- [x] 0 → 1 in-progress: exact corpus interfaces and reflected proof chain identified
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: direct Lean, targeted build, axiom audit green
- [ ] 3 → 4 publication-ready: standalone paper

## Proof [PROVED HERE]

For bounded dissipative `A`, imaginary-part expansion and Cauchy--Schwarz give
`Im(z) ||x|| <= ||(A-z)x||` for `Im(z)>0`. Hence `A-z` is injective with closed range.
A vector orthogonal to its range, tested against itself, vanishes by dissipativity; range is dense,
therefore surjective. Reversing signs proves the lower-half-plane result for bounded
antidissipative `B`. Every nonzero source has a unique nonzero response with
`|Im(z)| ||x|| <= ||source||`.

Corpus identity `xiSpectralPoint(copyConj q)=-conj(xiSpectralPoint q)` makes conjugate quadratic
angular parameters have opposite nonzero imaginary parts. Corpus source incidence makes both exact
`2s` source vectors nonzero off wall. Applying upper/lower resolvents proves both reflected
responses exist uniquely and are nonzero.

## No-go closure

- **Killed:** bounded linear nonnormal dissipative/antidissipative boundary extinction.
- **Positive survivor:** boundary exclusion must be unbounded and maximal-domain-sensitive, nonlinear, or change reflected half-plane orientation.
- **Significance:** removes full bounded passive operator class, not a numerical regime or bound.

## Formalization

Module:
`GaloisForLFunctions.RHTower.ThetaCuspHawkingHBBoundedDissipativeReflectedForcingNoGo`

Main theorem:
`d4HBBoundedDissipativeReflectedForcingExclusionRouteKilled`

Audit: direct `lake env lean` PASS; targeted `lake build` PASS; axioms only
`propext`, `Classical.choice`, `Quot.sound`; umbrella wired.

## Novelty audit through 2026-08

Corpus search found self-adjoint/unbounded forcing and source incidence, but no bounded nonnormal
reflected-pair theorem. Primary QNM literature audited: Birmingham--Mokhtari exact gravitational
QNMs (hep-th/0609028), topological black-hole stability (0709.2388), and Kerr QNM conserved-current
work with branch-cut caveats (2210.15935). No exact Xi/Teukolsky reflected-forcing no-go was found.
General dissipative resolvent theory is classical; new result is exact route-class application and
formal closure.

