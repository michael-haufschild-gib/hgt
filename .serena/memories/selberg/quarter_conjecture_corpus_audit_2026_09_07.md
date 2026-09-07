# Selberg quarter conjecture / Chain A formalization (2026-09-07)

User requires custom corpus search `python3 scripts/formal_tools.py research ...` before each new theorem family/module; all new families below were searched first.

Closed Lean infrastructure now includes prior Maass/automorphic, local spherical, complementary-series, packet, and exceptional-scalar modules, plus:
- `RealPrincipalSeriesCompactPicture.lean`: canonical Iwasawa B/K factors and linear equivalence between Borel coinduction and twisted compact-picture functions.
- `RealPrincipalSeriesCompactAction.lean`: conjugated principal-series representation with explicit Iwasawa action formula.
- `RealPrincipalSeriesKTypes.lean`: explicit `K ≃* Circle`, distinct/linearly independent even characters, compact K-type vectors, injective finite Fourier embedding.
- `RealPrincipalSeriesCompactKAction.lean`: K-type eigenvector theorem, diagonal K representation on Finsupp, actual K-action intertwining.
- `RealPrincipalSeriesKFiniteCoinduction.lean`: injective normalized K-finite embedding into algebraic coinduction, explicit basis/Iwasawa formula, K-action intertwining and invariant range.
- `RealPrincipalSeriesCompactHarishChandra.lean`: finite compact submodule, actual restricted K-representation, transported H/E/F with exact coefficients, sl2 relations, Casimir and shifted Laplacian scalars.
- `RealPrincipalSeriesCompactIrreducibility.lean`: compact K-type projections and irreducibility for |s|<1.
- `RealPrincipalSeriesCompactUnitarity.lean`: transported positive Hermitian form and exact compact unitarity locus (-1,1), proved both directions.
- `SelbergExceptionalCompactModel.lean`: every 0<λ<1/4 gives unitarizable irreducible compact complementary model with shifted Casimir λ.

All are wired into `GaloisForLFunctions/RHTower.lean`. Targeted `lake env lean` and `lake build <modules>` pass. Capstone #print axioms shows only propext, Classical.choice, Quot.sound. Targeted forbidden-token scan is empty.

Remaining known-math formalization gaps:
1. smooth vectors and proof transported H/E/F equal derivatives of explicit compact right action;
2. coordinate positive hyperbolic Laplacian equals derived right-regular Casimir;
3. quotient L²/Fourier zero-term correspondence and automorphic irreducible/local factor decomposition;
4. arbitrary generic GL(n,R) unitary classification/exponent theorem and local symmetric-power parameter compatibility.

Remaining open math: compatible automorphic symmetric-power lifts of unbounded degree for general weight-zero Maass forms, with infinity compatibility and constituent control. This is the actual obstruction to Selberg 1/4 via Chain A.

Latest global lint exit 1 only because unrelated concurrent `MontgomeryTruncationIntegrals.lean` is unreachable and contains a sorry at line 97; Chain A files are clean.