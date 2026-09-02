# PCS co-shift-natural singular boundary no-go

Status: formalized

## RH chain closed

For each Xi zero `ρ`, PCS must place the reflection-odd profile
`Ψρ - Ψ(1-conj ρ)` in a source differential range. Its vanishing forces
`Re ρ=1/2`; global vanishing is RH.

## New classification

Let `d0 : A → (ℕ₊ → ℂ)` be any complex-linear differential and
`U : A → A`. Assume only 2-co-shift covariance
`C₂ ∘ d0 = d0 ∘ U`. If `Re s ≠ 1/2`, then

`Ψ_s - Ψ_(1-conj s) ∈ range(d0)`

iff both `Ψ_s` and `Ψ_(1-conj s)` lie in `range(d0)`.

No topology, boundedness, closure, finite presentation, or summability is
assumed. Therefore every selective co-shift-natural non-`ℓ²` PCS boundary is
impossible. A survivor must break co-shift covariance or erase both singular
source modes.

Key theorems:

- `reflectionOdd_mem_sourceNaturalBoundary_iff_both_groundFuns_mem`
- `reflectionOdd_not_mem_sourceNaturalSelectiveBoundary`
- `forall_xiZero_reflectionOdd_mem_sourceNaturalSelectiveBoundary_iff_RH`

Proof: forward/reflected profiles are 2-co-shift eigenvectors with distinct
eigenvalues off wall. Applying `C₂` to their difference and eliminating one
eigenvalue isolates each profile.

## Audit

- `lake env lean GaloisForLFunctions/RHTower/PrimeCoShiftNaturalSingularBoundaryNoGo.lean`: pass.
- `lake build GaloisForLFunctions.RHTower.PrimeCoShiftNaturalSingularBoundaryNoGo`: pass.
- Axioms: only `propext`, `Classical.choice`, `Quot.sound`.
- Wired into `GaloisForLFunctions/RHTower.lean`.

Literature search through August 2026 found work on Hilbert spaces of Dirichlet
series, shift-invariant subspaces, and RH-related weighted-composition
semigroups, but no reflected PCS quotient or this exact source-differential
classification. Novelty claim is limited to this route-specific theorem and
operator-class kill; underlying two-eigenvalue elimination is elementary.
