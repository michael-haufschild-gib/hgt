# Proper exponential fiberwise addition

- **ID:** proper-exponential-fiberwise-addition
- **Stage:** 2-fully-proven
- **Type:** THEOREM (Lean)
- **Source:** irregular microlocal Riemann--Hilbert foundations
- **Statement:** For continuous real phases, fiberwise addition from the fiber product of their closed exponential epigraphs to the epigraph of the phase sum is a proper surjection.

## Goal
Supply the exact support-level properness needed before defining proper-support convolution. This proves no sheaf, derived, enhanced, ind-sheaf, D-module, or Riemann-hypothesis claim.

## Gates
- [x] 0 → 1  in-progress: well-posed; support-pure; conjugate by slack coordinates to `id_X × ((a,b) ↦ a+b)` on nonnegative reals
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: theorem and targeted build pass, but authoritative repository lint remains blocked by unrelated unreachable modules recorded in session report
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Use slack coordinates `a = u + φ(x)` and `b = v + ψ(x)`. They identify the source with `X × (ℝ≥0 × ℝ≥0)` and the target with `X × ℝ≥0`; restricted fiberwise addition becomes `id_X × ((a,b) ↦ a+b)`.

## Proof

`[PROVED HERE]` Let `K ⊆ ℝ≥0` be compact. Addition `σ(a,b)=a+b` is continuous, so
`σ⁻¹(K)` is closed. Since `K` is bounded, choose `r` with `K` contained in the closed ball of
radius `r` about zero. If `(a,b) ∈ σ⁻¹(K)`, nonnegativity gives `a ≤ a+b ≤ r` and
`b ≤ a+b ≤ r`; hence `σ⁻¹(K)` is bounded in the product metric. The product `ℝ≥0 × ℝ≥0` is a
proper metric space, so the closed bounded preimage is compact. Thus `σ` is proper.

The product of `σ` with `id_X` is proper. For continuous `φ,ψ`, source and target slack-coordinate
maps and their displayed inverses are homeomorphisms. Restricted fiberwise addition is conjugate to
`id_X × σ`, so it is proper. Given `(x,t)` in the target epigraph, choose
`u=t+ψ(x)` and `v=-ψ(x)`; then `u+v=t`, `u+φ(x)=t+φ(x)+ψ(x)≥0`, and
`v+ψ(x)=0`. Hence the map is surjective.

## Lean certificate

- Module: `GaloisForLFunctions.HTGeometry.StokesProperEpigraphAddition`
- Main results:
  - `nnrealAdd_isProperMap`
  - `epigraphFiberwiseAddition_slack_commutes`
  - `epigraphFiberwiseAddition_isProperMap`
  - `epigraphFiberwiseAddition_surjective`
- Direct module check: PASS.
- Targeted module build: PASS.
- New-declaration axiom audit: only `propext`, `Classical.choice`, `Quot.sound`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** Not applicable.
- **Strongest positive survivor:** Not applicable.
- **New insight:** Properness is intrinsic to nonnegative slack coordinates and needs no compactness or separation hypothesis on the base.
- **Status:** Dependency-closed paper proof and Lean formalization complete; full irregular-RH sheaf machinery remains open.

## Log
- 2026-08-24 — created in 1-in-progress after corpus search found no reusable properness theorem for nonnegative addition or exponential-support fiberwise addition.
- 2026-08-24 — paper proof completed; Lean module checked and targeted build passed; moved to 2-fully-proven.
