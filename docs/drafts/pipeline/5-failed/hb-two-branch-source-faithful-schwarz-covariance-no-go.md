# HB two-branch source-faithful Schwarz covariance no-go

Status: failed route with positive survivor
Route: HB
Completed: 2026-08-28

## Failed conjecture

A different field representation, bilinear quadratic residual, branch square root, Peierls form,
or radial normalization might realize the literal `++` and `--` BM sources while making
functional-equation reflection swap two branches away from the critical line.

## Exact obstruction

False. For nonzero seed amplitude, equality of the two canonical source packets under reflection
holds exactly when `Re(q) = 1/2`. Equality of branch fields forces equality of their quadratic
residuals, so every source-faithful two-branch realization is rigid on the same locus. The theorem
uses an arbitrary complex field space and arbitrary bilinear residual; no Peierls or PDE structure
can evade it.

Global source fidelity and two-branch reflection covariance imply RH.

## Positive survivor

At every tilted Xi zero, any finite support closed under functional-equation reflection and complex
conjugation and containing the physical return weight has cardinality at least four. Hence a
source-faithful off-wall continuation must use the complete FE--Schwarz quartet and replace
individual-fibre incidence by orbit-level landing.

This survivor is formalized jointly by:

- `hbXiPeierls_tilted_sourceFaithful_noGo_and_realClosure_ge_four`
- `d4ThetaTeukolsky_tilted_closedPacket_card_ge_four`

in
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceFaithfulBranchCovarianceNoGo.lean`.

## Consequence

Retire all two-branch, source-faithful covariance repairs, including changes of carrier, action,
quadratic map, pairing, propagator, basis, and square-root phase. Continue HB only through a
four-sector FE--Schwarz orbit construction or through a derivation that explicitly changes source
semantics and proves why that change is physical.
