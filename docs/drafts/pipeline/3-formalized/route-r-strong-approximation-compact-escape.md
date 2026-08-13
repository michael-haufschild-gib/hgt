# Route R strong-approximation compact escape

- **ID:** route-r-strong-approximation-compact-escape
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route R strong compact-approximation blindness, positive-survivor audit
- **Statement:** At every nonneutral grade, unit-ball images of Route R's compact strong approximants escape every common compact subset of physical Hilbert space.

## Goal

Identify exact uniform defect by which compact stages converge strongly to Route R's noncompact
receiver, and close collective compactness as a possible hidden source producer.

## Gates

- [x] 0 → 1 in-progress: common-envelope claim isolated from strong-topology counterexample
- [x] 1 → 2 fully-proven: dependency-closed proof below
- [x] 2 → 3 formalized: `RouteRStrongApproximationCompactEscape`, targeted build and axiom audit green
- [ ] 3 → 4 publication-ready

## Exact theorem and proof

Let `K_i,T` be bounded operators on Route R's physical Hilbert space and suppose `K_i x→T x` for
every `x`. If one compact set `C` contains `K_i(B)` for every stage `i`, where `B` is the open unit
ball, then `T` is compact. Indeed, for fixed `x∈B`, every `K_i x` lies in closed set `C`; its limit
`T x` also lies in `C`. Thus `T(B)⊆C`, which is the compact-operator criterion.

For Route R's canonical Hilbert-basis truncations, pointwise convergence to the fixed `(2,3)`
receiver is already proved. If at positive aperture and nonzero grade one compact `C` contained all
stage images of `B`, preceding theorem would make receiver compact, contradicting exact Calkin
classification `compact ↔ grade=0`. Hence for every compact `C` there are a stage and `x∈B` whose
image lies outside `C`.

More generally, existence of compact strong approximants with one common compact unit-ball envelope
is equivalent to compactness: forward implication is preceding theorem; reverse implication uses
constant approximating sequence and compact envelope supplied by compact operator definition.
Therefore on fixed receiver collective compactness is equivalent to neutral grade and globally
equivalent to RH.

For the canonical Hilbert-basis truncations themselves, the envelope property is also equivalent
to neutral grade. At grade zero Lean proves the fixed commutator is literally zero, every canonical
truncation is zero, and `{0}` is a common compact envelope; the converse is the compact-escape
argument.

## No-go closure

- **Exact killing theorem/mechanism:** Finite-stage compactness plus strong convergence lacks uniform
  tightness; adding common compact envelope forces compact limit immediately.
- **Strongest positive survivor:** Explicit compact-escape law for actual canonical truncations.
- **New insight:** Nonneutral horizontal atom reappears geometrically as unavoidable escape of
  unit-ball images from every compact physical reservoir. A viable source law cannot hide inside
  strong convergence; it must supply exactly this missing tightness, which is globally RH-equivalent.
- **Status:** `[LEAN-PROVED]` in `RHTower/RouteRStrongApproximationCompactEscape.lean`; targeted
  build green; all seven public theorems use only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-13 — extracted compact-escape survivor and completed proof.
- 2026-08-13 — exact theorem formalized, umbrella-wired, targeted build and axiom audit green;
  moved to Stage 3.
