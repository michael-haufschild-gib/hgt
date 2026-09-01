# HB maximal-domain radial response no-go

- **ID:** HB-MDRR
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Every complex Xi-copy coefficient profile has a closed densely-defined maximal diagonal realization containing every coordinate state and reproducing every requested diagonal matrix element.

## Goal
Kill `closed/dense/unbounded coefficient-faithful response exists → two-leg Peierls incidence → radiative ++ extinction → RH` at its first arrow.

## Gates
- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

## Proof
For arbitrary `a : ι → ℂ`, use maximal domain `{x ∈ ℓ² | (aᵢxᵢ) ∈ ℓ²}`. Its graph is the intersection of kernels of continuous coordinate defects `yᵢ-aᵢxᵢ`, hence closed. Coordinate span lies in the domain and is dense. Each coordinate vector is an eigenvector and its matrix element is `aᵢ`. Apply to every target and to `hbXiPeierlsRadialWeight n`.

## No-go closure
- **Exact killing theorem:** `d4HBUnboundedRadialCoefficientExistenceRouteKilled`.
- **Strongest positive survivor:** literal Einstein–Teukolsky dynamics must identify a stricter PDE graph/domain and prove independent source/left-QNM Peierls incidence; closed maximal-domain fidelity alone is empty of arithmetic selection.
- **New insight:** unboundedness is necessary for exact BM radial fidelity but not selective; even closedness, density, maximality, and all coordinate incidences fit arbitrary profiles.
- **Status:** module `ThetaCuspHawkingHBMaximalDomainRadialResponseNoGo`; targeted build passed; axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella wired.

Corpus search found bounded-fidelity obstruction and real/special-complex maximal diagonals, but no arbitrary-complex HB universal realization. Primary-literature audit through 2026-08: Birmingham–Mokhtari `hep-th/0609028`; Marolf `hep-th/9308150`; Ching–Leung–Suen–Young `gr-qc/9408043`; none identifies abstract maximal diagonal fitting with physical Peierls incidence or states this HB obstruction.
