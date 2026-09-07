# Selberg quarter conjecture corpus audit and Chain A formalization (2026-09-07)

Report: `docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecture-corpus-audit.md`.

Conjecture remains open. Added ten closed Chain A infrastructure modules, all imported by `RHTower.lean`:
1. `MaassHomogeneousSpaceCorrespondence.lean`: exact Γ-invariant functions on ℍ ↔ left-Γ/right-K invariant functions ↔ spherical vectors in right regular representation.
2. `MaassSpectralTransport.lean`: conjugates arbitrary linear operators across correspondence; preserves eigen-equations, nonzero eigenvectors, eigenvalues.
3. `CongruenceMaassCorrespondence.lean`: specializes to Mathlib Gamma/Gamma0/Gamma1 via SL2Z → SL2R.
4. `AutomorphicCoinduction.lean`: exact representation equivalence with Mathlib algebraic coinduction from trivial Γ.
5. `RealUpperBorelPrincipalSeries.lean`: real upper Borel, |a|^σ character, exact unitary-character locus {0}, algebraic coinduced principal series.
6. `SymmetricPowerArchimedeanExponents.lean`: Sym^d packet (d-2j)ν; exact positive-degree strip; all degrees/all even degrees force ν=0; eigenvalue image {1/4}; fixed degree strict lower bound.
7. `RankOneComplementarySeriesBound.lean`: factorized first spherical norm obstruction positive iff |ν|<1/2; equals Selberg eigenvalue positivity.
8. `RealSphericalHarishChandra.lean`: finite-support spherical K-type model; [h,e]=2e, [h,f]=-2f, [e,f]=h; Casimir scalar s²/4; shifted Casimir at s=2ν equals 1/4-ν².
9. `RealSphericalUnitarity.lean`: positive-definite Hermitian and e†=-f invariance definitions; derives raising-norm identity and closed necessary unitarity bound |s|<1, hence |ν|<1/2.
10. `GenericUnitaryExponentBounds.lean`: finite packet block form positive iff every exponent lies in half-strip; rank-one unitarizable packet gets pointwise bound; all/all-even symmetric-power degrees force ν=0.

Verification: every module passed `lake env lean <file>` and targeted `lake build <module>`; no full or umbrella build. Final capstone #print axioms audit reported only propext, Classical.choice, Quot.sound. No sorry/admit/axiom/opaque/unsafe. Final `python3 scripts/formal_tools.py lint` passed with existing large-file warnings. No Lean processes started here remain.

Exact boundary: algebraic homogeneous-space dictionary is complete, but smoothness, growth, cuspidality, L², actual coordinate hyperbolic Laplacian = automorphic Casimir, adelization/restricted tensor products are absent. Local explicit spherical SL2(R) model and necessary unitarity bound are formalized; full GL(n,R) generic-unitary classification bridge is absent. Automorphic symmetric-power functoriality for arbitrary weight-zero Maass forms in unbounded degree is open mathematics, so no Selberg proof is claimed.