# Exact unipotent Fourier filter for the original Maass source

- **Stage:** 1-in-progress
- **Type:** POSITIVE EXACT SOURCE IDENTITY
- **Statement:** The complete upper-unipotent average is an exact spectral filter on the actual Maass Fourier coefficients. Its complementary energy is the mass of the discarded residue-frequency channels, with no path-length estimate.

## Positive target and paper proof

The full Selberg quarter goal remains active. The previous turn proved a level-scaled physical gap, principal levels 1–7 exclusion, and all-level scalar deck cancellation. This loop attacks the missing connection between finite-group mixing and physical Fourier energy.

Let L = N + 1 and let a_n(y) be the vector of literal Fourier coefficients of the original deck fields. Each field has period L. Changing variables in its normalized coefficient integral gives the exact shift law: translation by j multiplies a_n(y) by exp(2 pi i n j/L). Original modular equivariance therefore identifies a_n(y) as an eigenvector of the finite upper-unipotent translation action.

The complete residue average of that character is one for the trivial residue character and zero otherwise. Consequently the actual upper-block projection keeps exactly frequencies divisible by L; its complement keeps all other frequencies. Parseval for the actual projected fields identifies block-variance mass with the corresponding original coefficient mass. Lower blocks are transported by the already-proved inversion formula. No uniform physical comparison is assumed.

## Corpus discovery

- Arithmetic OR discovery (unipotent, property tau, congruence expansion, Hecke averaging, projective plane): 357 declarations in 87 modules.
- Comparison OR discovery (displacement energy, path comparison, canonical paths, Markov type, hyperbolic averaging): 19 declarations in 14 modules.
- Fourier OR discovery (Fourier translation, cyclic Fourier, twisted periodic, frequency projection, unipotent Fourier): 61 declarations in 11 modules.
- Inspected the existing `SelbergMaassGeneratorComparison`, `SelbergMaassUnipotentBlocks`, and relevant `SelbergMaassUnipotentPaths` source. The actual composite-level four-block factorization and uniform algebraic coefficient 16 are already proved. The current-path estimate retains the exact moment N(2N+1)/12; do not re-prove it.
- Inspected `FiniteRegularBlocks` and `FieldOneFiniteCyclicFourierParseval`: exact subgroup orthogonal projections and cyclic character orthogonality are the positive mechanisms to reuse.

## Gates

- [x] Original-source target and prior-work check.
- [x] Kernel-checked coefficient shift law and actual finite translation eigenspace law.
- [x] Complete unipotent Fourier projection and physical Parseval identity.
- [x] Final single-module build, axiom audit, unique umbrella wiring, and complete index/API coverage.
- [ ] Repository-wide formal lint: nine unrelated `HTGeometry.ConservativeDissipative*` modules are currently unreachable from their umbrella. This card stays in progress until that shared-tree gate clears.

The uniform comparison with the physical gradient is a subsequent proof target. The exact spectral filter is intended to retain the information lost by the path-moment bound.

## Completed paper proof and Lean realization

For each original deck component, write F_q(z) for the literal complex-chart field, and a_q,n(y) for its normalized level-L Fourier coefficient. The kernel multiplication law and periodic integral change of origin prove the shift identity at every real shift; specializing integer shifts identifies its phase with the standard additive character on ZMod L. Original quotient-form multiplication and the literal upper matrix action identify this phase law with the actual upper-block action on the complete coefficient vector.

Define A_q as the actual complete upper-block average of F_q and C_q = F_q - A_q. Finite sums commute with the normalized integral because every original field is continuous on the upper half-plane. Primitive additive-character orthogonality then proves coefficient(A_q,n) = a_q,n when L divides n and zero otherwise. Thus coefficient(C_q,n) is zero when L divides n and a_q,n otherwise. Both statements hold for every original Maass eigenvalue, without an exceptional-eigenvalue restriction.

Continuity of C_q permits the existing physical Parseval theorem to be applied even when the projected field vanishes. Summing over every deck coordinate and interchanging the finite sum with the genuinely integrable squared-norm slice gives

    sum_{n : L does not divide n} sum_q |a_q,n(y)|^2
      = L^-1 integral_0^L ||V(x+iy) - P_upper V(x+iy)||^2 dx.

The theorem supplies HasSum, so convergence and the exact normalized value are both proved. The equality with the pre-existing arithmetic blockAverage is proved from its actual Reynolds definition, rather than introducing an unrelated projection. Every coordinate and every common zero is retained.

Source: `formal/GaloisForLFunctions/RHTower/SelbergMaassUnipotentFourier.lean`; 20 public declarations and four private analytic helpers. Main declarations: `coefficient_upperAverageField`, `coefficient_upperComplementField`, `upperBlock_variance_hasSum`, and `coefficientVector_upperBlock`.

## Further corpus discovery and next conjecture

The explicit OR search for entropy, uncertainty, Fourier support, additive energy, and Kloosterman returned 1885 declarations in 363 modules. The full retrieval is saved in `/tmp/selberg_unipotent45_uncertainty.json`. Of these, the Kloosterman modules contribute 509 declarations in 56 modules. Inspected `Sieve/KloostermanTransform` and `KloostermanBilinear` supply an exact two-Fourier-transform factorization with unit-residue inversion and its original finite energy identities. Inspected `ArchimedeanConcentrationGain` suggests tracking high-frequency mass explicitly, but its source concentration inequality is a premise and is not available for the Maass source without proof.

Next positive candidate: construct every character-weighted upper-unipotent projector, prove its exact original frequency-class filter n congruent to r modulo L, and transport these projectors through the actual modular inversion to obtain the lower-block coupling. This retains the low-frequency channels that the trivial-character projection alone cannot distinguish. Any use of the finite Kloosterman operator must first identify it with that actual coupling; no such identification or uniform gradient comparison is asserted here.

## Verification

- Complete scratch check and exact source check passed.
- Final single-module build passed in 7.3 seconds and rebuilt only `SelbergMaassUnipotentFourier`; `/tmp/selberg_unipotent45_build.log`.
- All 20 public declarations passed the post-build `lake env lean /tmp/selberg_unipotent45_axioms.lean` check. Only `propext`, `Classical.choice`, and `Quot.sound` occur; the source hash stayed unchanged. Audit artifacts: `/tmp/selberg_unipotent45_axioms.log`, `_manifest.json`, and `_audit.json`.
- Index refresh passed. All 20 public declarations and four private helpers are searchable; all 20 public API rows exist; the new umbrella import occurs exactly once. `/tmp/selberg_unipotent45_coverage.json` and `_index.log`.
- `scripts/formal_tools.py lint` ran and reported nine unreachable modules in the unrelated `HTGeometry.ConservativeDissipative*` family: Compression, Constraints, Flow, Hodge, Operator, Polynomial, Quantum, Spectrum, Spin. No lint error names this Selberg module. Existing large-file warnings remain. `/tmp/selberg_unipotent45_lint.log`.
- The positive source theorem is proved and individually audited. The global lint gate and the all-level quarter proof are not marked complete.
- No full or umbrella build, added axiom, admission, numerical experiment, commit, or push.

The further OR projector search returned 48 declarations in 16 modules (`/tmp/selberg_unipotent45_projectors.json`). Inspected `ConnesCharacterProjection` proves finite character-average intertwining, idempotence, and the exact character-eigenspace fixed-point criterion. Reuse that construction for the next source instantiation. Its representation hypotheses must be discharged by the actual deck action; Hilbert orthogonality additionally uses the actual unitary action and must not be inferred from the file's introductory prose alone.
