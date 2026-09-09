# Full original character filters and inversion coupling

- **Stage:** 3-formalized
- **Type:** POSITIVE ORIGINAL-SOURCE COUPLING
- **Goal:** Preserve all original residue-frequency channels while coupling upper and lower unipotent motion through actual modular inversion. The all-level Selberg quarter proof remains the goal.

## Conjecture and paper proof plan

At level L=N+1 and each residue r, form the finite character average P_r = L^-1 sum_j conjugate(chi(r*j)) U_upper(j) in the actual deck representation. The corpus Connes character-projector construction supplies intertwining and idempotence once its hypotheses are discharged by the actual source action. Character orthogonality should give a complete resolution, pairwise orthogonality, and exact source Fourier support n congruent to r modulo L. These are positive identities, not assumed source estimates.

The literal matrix identity lower(j)=S upper(-j) S^-1 should yield Q_r = U_S P_(-r) U_S^-1. Applied to the original source vector, this determines the exact lower-character field at z from the upper-character field at S^-1 z. Keeping this height-changing source coupling is necessary before any finite Kloosterman or frequency-concentration estimate can be used.

## Corpus inputs

Previous positive cycle43: `SelbergMaassUnipotentFourier` proves the exact trivial-character filter and physical variance Parseval identity, with targeted build and all20 public axiom checks passed. Its source hash was revalidated unchanged for this loop.

The new explicit OR search for character average, conjugate projection, unipotent, and residue character returns409 declarations in105 modules (`/tmp/selberg_character46_corpus.json`). Reuse `ConnesCharacterProjection`, `FiniteRegularReynolds`, `SelbergMaassUnipotentBlocks`, `SelbergMaassUnipotentPaths`, and the exact source coefficient law. The previous projector search returned48 declarations in16 modules; do not re-prove generic Connes idempotence. Any use of the Kloosterman transform requires a proved source identification.

## Gates

- [x] Revalidate actual prior source and perform broad corpus discovery.
- [x] Actual character representation and complete orthogonal projectors.
- [x] Literal source residue-frequency filters with physical Parseval.
- [x] Actual inversion conjugation and source coupling.
- [x] Targeted builds, axiom checks, unique umbrella imports, complete index/API coverage, and repository lint.

## Positive paper result

The complete character decomposition and physical source coupling are proved in scratch and both exact source modules. For each actual block homomorphism p, P_r is the corpus Connes average with all representation and character hypotheses discharged. Primitive finite-character orthogonality gives P_r P_s = delta_rs P_s and sum_r P_r = identity. Applying one actual unitary block element with parameter1 distinguishes every pair of residue characters, proving orthogonality in the original deck inner product. This yields self-adjointness and exact sum_r ||P_r v||^2 = ||v||^2.

Literal upper integer matrices reduce to the original residue class. Their lower conjugation identity descends to lowerBlock(j) = [S] upperBlock(j^-1) [S^-1]. Reindexing the complete character average by parameter inversion proves Q_r = U_S P_-r U_S^-1, including its sign. Original modular equivariance gives Q_r V(z) = U_S P_-r V(S^-1 z), and hence the exact channel-energy equality at the actual inverted point.

For the source Fourier bridge, original component continuity supplies genuine vector-valued integral existence. Continuous linear maps commute with that finite-period Bochner integral. Coordinate projections identify its value with the already-existing literal coefficient vector a_n(y); thus every continuous linear readout, including every character projector coordinate, has the corresponding actual Fourier coefficient. The old coefficient-vector unipotent eigenspace law and the new orthogonal projectors imply P_r a_n = a_n when n mod L = r and zero otherwise. Physical Parseval then gives each original upper-channel mass as precisely that residue-class coefficient energy.

Define the actual finite transfer C_rs = P_r U_S^-1 P_s. Its coordinates are the literal two-parameter character sum against v(q upper(a) [S^-1] upper(b)), normalized by L^-2. Its full column energy is exactly ||P_s v||^2. The lower source channel has the exact physical Parseval formula

    L^-1 integral_0^L ||Q_r V(x+iy)||^2 dx
      = sum_n ||C_(-r, n mod L) a_n(y)||^2.

All sums in the physical formula are HasSum statements; every original coordinate, frequency, and zero is retained. The finite coupling has now been identified with the original source. A bound on this coupling relative to the signed physical frequency and full-domain gradient is the next proof target, not a hypothesis of these identities.

## Source certificate

- `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterProjection.lean`:24 public declarations. Actual character phases/action, corpus projector instantiation, pair annihilation, complete resolution, Hilbert orthogonality, self-adjointness, exact energy sum, literal lower conjugation, and original source transport.
- `formal/GaloisForLFunctions/RHTower/SelbergMaassCharacterFourier.lean`:20 public declarations. Original vector-valued Fourier integral, readout naturality, every residue filter, physical HasSum identities, explicit original inversion transfer, exact column-energy conservation, lower-character source Parseval, and complete finite coordinate kernel.
- Both complete scratch and exact source checks passed. Only the first module's olean was produced for the second module's import; no umbrella build ran.

## Next mathematical test

The original finite coupling is now explicit, not a supplied operator-identification hypothesis. Expand its Gram kernel by the actual two-unipotent parameter map and retain the diagonal and off-diagonal arithmetic fibres. Test whether that structure controls the original signed-frequency energy, with the original height-changing inversion relation retained. Search the existing finite Kloosterman/Gram modules for the fibre mechanism before introducing a new estimate. The Selberg endpoint still requires the congruence-uniform comparison of source mass with four times physical full-domain gradient; neither a generic finite contraction nor a qualitative character decomposition proves that bound.

## Final verification

Both final single-module builds passed and rebuilt only their named target: CharacterProjection8.6s and CharacterFourier4.3s. Logs `/tmp/selberg_character46_projection_build.log` and `_fourier_build.log`. Cached EvenL2LogUnitary informational output was replayed; no new-module warning occurred. No full or umbrella build ran.

All44 public declarations passed `lake env lean /tmp/selberg_character46_axioms.lean` after the builds. Dependencies are only the standard `propext`, `Classical.choice`, and `Quot.sound` axioms. Both source hashes stayed unchanged. Artifacts `/tmp/selberg_character46_axioms.log`, `_manifest.json`, and `_audit.json`.

Index refresh and repository formal lint passed, with existing large-file warnings. All44 public declarations are searchable and appear in the exact module's API rows; the search returns45 entries including the local normality instance. Both umbrella imports occur exactly once. `/tmp/selberg_character46_index.log`, `_coverage.json`, and `_lint.log`. The prior turn's nine unrelated ConservativeDissipative umbrella errors were resolved outside this task; the latest successful lint also clears that earlier source card's remaining gate.

No added axioms, admissions, numerical experiments, commit, or push. The positive coupling conjecture is completed and audited. The all-level Selberg quarter proof remains active and unproved.
