Selberg quarter-conjecture Chain A formalization status (2026-09-07).

Always run `python3 scripts/formal_tools.py research "<query>" --no-refresh` before adding a theorem family. User explicitly requires corpus-first searches.

Formalized closed, unconditional infrastructure:
- Maass homogeneous-space, congruence, spectral transport, analytic cusp/automorphic correspondence, cyclic automorphic representation.
- Algebraic Borel coinduction, explicit Iwasawa compact picture, transported action.
- Explicit K ≃ Circle, even K-characters, finite K-type embeddings, actual restricted K-action.
- Explicit spherical Harish-Chandra H/E/F, sl2 relations, Casimir/Laplacian, complementary-series positive form, exact unitarity and irreducibility.
- Finite exponent packets and exact generic half-strip; symmetric-power amplification and exceptional local models.
- New: RealPrincipalSeriesCompactKDerivative.lean constructs rotation subgroup, proves finite Fourier vectors rotation-smooth, differentiates actual K action, and identifies derivative pointwise with iH on basis K-types.
- New: RealPrincipalSeriesDiagonalDerivative.lean constructs positive diagonal subgroup, differentiates compact action at K identity, and identifies it with transported E+F on basis K-types there.
- New factorization theorem compactRealPrincipalSeries_factor_apply in RealPrincipalSeriesCompactAction.lean.

Normalization correction:
- Existing Harish-Chandra coefficients (s-1∓2m)/2 require inducing Borel exponent s-1, not s+1.
- Corrected RealPrincipalSeriesKFiniteCoinduction.lean, RealPrincipalSeriesCompactHarishChandra.lean, and RealPrincipalSeriesCompactKDerivative.lean.
- Closed theorem positiveDiagonal_matches_spherical_E_add_F_at_one verifies the normalization through actual differentiation.

Verification:
- Direct `lake env lean` passed for all changed/new files.
- Targeted builds passed for compact action, normalized coinduction, compact HC, compact irreducibility/unitarity, K derivative, diagonal derivative, and exceptional compact model.
- Nine derivative capstone `#print axioms` checks show only propext, Classical.choice, Quot.sound.
- Targeted forbidden-token scan empty; git diff check clean; global `python3 scripts/formal_tools.py lint` passed with only large-file warnings.
- Umbrella imports include RealPrincipalSeriesCompactKDerivative and RealPrincipalSeriesDiagonalDerivative.
- Do not commit/push unless user explicitly asks.

Remaining genuine gaps:
1. Extend positive-diagonal derivative from K identity to all K, add second noncompact subgroup, separate E and F, derive Casimir.
2. Coordinate hyperbolic Laplacian = derived right-regular Casimir.
3. Fourier zero-term ↔ cusp decay/quotient L2 and Hilbert completion/irreducible decomposition/local factor.
4. Generic unitary GL(n,R) classification bridge; current exact half-strip theorem is only for explicit rank-one product model.
5. Compatible automorphic symmetric-power lifts in unbounded degree/local compatibility; this is open mathematics and would imply Selberg.
6. Arithmetic exclusion of exceptional complementary-series cusp representations remains Selberg itself.

Audit report: docs/drafts/pipeline/1-in-progress/selberg-quarter-conjecture-corpus-audit.md.