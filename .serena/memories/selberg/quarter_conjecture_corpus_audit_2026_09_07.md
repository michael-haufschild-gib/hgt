# Selberg quarter conjecture corpus audit and Chain A formalization (2026-09-07)

Report: `docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecture-corpus-audit.md`.

Conjecture remains open. Custom corpus search must precede each new theorem family/module: `python3 scripts/formal_tools.py research ...`.

Chain A formalization now wired into `formal/GaloisForLFunctions/RHTower.lean`:

1. `MaassHomogeneousSpaceCorrespondence.lean`: exact Γ-invariant functions on ℍ ↔ left-Γ/right-K invariant functions ↔ spherical right-regular vectors.
2. `MaassSpectralTransport.lean`: conjugates linear operators; preserves eigen-equations, nonzero eigenvectors, eigenvalues.
3. `CongruenceMaassCorrespondence.lean`: Gamma/Gamma0/Gamma1 specializations.
4. `MaassCuspAutomorphicCorrespondence.lean`: real C² predicate via `ContDiffOn ℝ 2`; positive hyperbolic Laplacian via real Fréchet derivatives on ℂ; nonzero eigenfunction and cusp decay after every integral scaling matrix; exact spherical automorphic equivalence; Gamma/Gamma0/Gamma1 specializations.
5. `MaassCyclicAutomorphicRepresentation.lean`: group-algebra span of nonzero spherical Maass vector; actual cyclic right-regular subrepresentation and nonzero generator.
6. `AutomorphicCoinduction.lean`: algebraic coinduction equivalence.
7. `RealUpperBorelPrincipalSeries.lean`: real upper Borel, |a|^σ characters, exact unitary-character locus, algebraic principal series.
8. `SymmetricPowerArchimedeanExponents.lean`: Sym^d exponent packets, exact strips, all/all-even degrees force ν=0.
9. `RankOneComplementarySeriesBound.lean`: first rank-one norm obstruction.
10. `RealSphericalHarishChandra.lean`: spherical K-finite model, sl₂ commutators, Casimir and shifted Laplacian.
11. `RealSphericalIrreducibility.lean`: every (𝔤,K)-submodule is bottom/top for |s|<1.
12. `RealSphericalUnitarity.lean`: invariant positive Hermitian forms and necessary |s|<1.
13. `RealSphericalComplementaryWeights.lean`: positive product K-type weights and two-sided recurrence.
14. `RealSphericalComplementarySeries.lean`: explicit diagonal Hermitian form, positivity, e†=-f invariance, exact unitarity loci (-1,1) and (-1/2,1/2).
15. `GenericUnitaryExponentBounds.lean`: explicit rank-one packet unitarizable iff pointwise half-strip; symmetric-power all/all-even exact locus {0}.
16. `SphericalExponentPacketUnitarity.lean`: one product Harish-Chandra model and one positive invariant Hermitian form for a finite exponent packet; exact iff pointwise half-strip; symmetric-power all/all-even exact locus {0}.
17. `SelbergExceptionalSphericalModel.lean`: bundled 0<λ<1/4 gives ν=sqrt(1/4-λ)∈(0,1/2), unitarizable irreducible local model with shifted Casimir λ, and failure of explicit local unitarity in some positive even symmetric-power degree.

Verification: every changed/new module passed `lake env lean <file>` and its targeted `lake build <module>`; no full or umbrella build. Capstone `#print axioms` checks report only `propext`, `Classical.choice`, and `Quot.sound`. No sorry/admit/axiom/opaque/unsafe. Final `python3 scripts/formal_tools.py lint` passed with existing large-file warnings. No Lean processes started by this work remain.

Remaining known-foundation boundary:
- prove pointwise cusp decay equivalent to Fourier zero constant terms and quotient L²;
- define derived right-regular Lie algebra action and prove coordinate positive Laplacian equals shifted Casimir;
- identify algebraic coinduction with explicit spherical Harish-Chandra model;
- formalize generic-unitary classification for arbitrary GL(n,ℝ), including local factor compatibility.

Open mathematical boundary: compatible unbounded-degree symmetric-power lifts for arbitrary weight-zero Maass forms. Thus Selberg 1/4 is not proved.