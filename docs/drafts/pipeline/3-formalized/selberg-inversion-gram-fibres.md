# Arithmetic fibres of the actual inversion Gram kernel

- **Stage:** 3-formalized
- **Type:** POSITIVE EXACT ARITHMETIC GRAM LAW
- **Goal:** Derive the arithmetic structure of the actual source inversion Gram operator, retaining every composite-level fibre before attempting the uniform physical energy estimate.

## Positive conjecture and proof route

Cycle44 identifies C_rs=P_r U_S^-1 P_s with the actual original Maass Fourier coupling. Its Gram operator is P_s Q_-r P_s. Expanding this actual operator gives complete upper–lower–upper parameter sums.

Conjecture: over every commutative ring, two words U(a') L(b) U(c') and U(a) L(b) U(c) agree exactly when b(a'-a)=0 and a'+c'=a+c. Equivalently their parameter fibre is the translate (a+t,c-t), with t in the annihilator of b. The character weight for the two outer upper blocks depends only on a+c, so it is constant on each entire collision fibre. This should give an exact multiplicity-weighted Gram kernel at composite levels, rather than a field-only cancellation argument.

Compare matrix entries: the two diagonal entries determine b(a'-a) and b(c'-c). Once these agree, the mixed term a'bc' equals abc, so the upper-right entry determines a'+c'. Conversely annihilator translation preserves every matrix entry. The resulting explicit fibre equivalence supplies exact cardinalities without enumeration.

## Corpus evidence

Revalidated both cycle44 source hashes unchanged. Explicit OR search for collision fibre, kernel fibre, annihilator, Bruhat, and Gram kernel returns2086 declarations in515 modules (`/tmp/selberg_gram47_corpus.json`). The unfiltered Bruhat-family output was too large; subsequent inspection separates the actual matrix-factorization and fibre leads.

Inspected `HTGeometry/BruhatCellUniqueness`: matrix entries recover Bruhat parameters with unit diagonal parameter. Inspected `HTGeometry/Sl2ElementaryFactorization`: the three-factor formula requires a field and nonzero lower entry. Reuse actual `FiniteRingSl2.upper/lower` and its unit-factorization theorem. The current conjecture concerns complete nonunit fibres over arbitrary commutative rings, which those unit/field formulas do not classify.

## Gates

- [x] Actual-source revalidation and broad corpus discovery.
- [x] Complete nonunit parameter-fibre classification and phase conservation.
- [x] Actual Gram operator, source energy identity, and finite coordinate expansion.
- [x] Fibre aggregation with exact arithmetic multiplicities, exact support/magnitude, and character-independent absolute probability law.
- [x] Targeted builds, axioms, umbrella wiring, index, lint.

The required comparison of original full-domain mass with four times physical gradient remains an unproved target; no such comparison is assumed.

## Paper continuation: exact Gram operator and phase-coherent probability law

The actual operator is G_rs = P_s Q_-r P_s. Self-adjointness of the proved character projectors and unitarity of the actual inversion give Re <G_rs v,v> = ||C_rs v||^2. Its literal coordinate expansion is the complete triple sum with weight chi(r*b-s*(a+c)), normalized by L^-3. The generic annihilator-fibre equivalence transfers through the proved deck/residue equivalence, and the conserved outer sum makes that exact character phase constant on every fibre.

Grouping the finite sum by actual deck elements proves a genuine convolution kernel, with no source-identification premise. At g=U(a)L(b)U(c), its value is L^-3 times the cardinality of Ann(b), multiplied by chi(r*b-s*(a+c)). Its magnitude is therefore |Ann(b)|/L^3. Its support is exactly the image of the three-factor parameter map, at every prime or composite level including the zero ring. At the identity the coefficient is exactly L^-2.

A stronger positive conjecture emerged from this formula: the absolute kernel should be independent of r,s and have total mass1. Paper proof: at any supported element its amplitude is the same nonnegative value as the neutral kernel K_00; outside support both are zero. The neutral triple average sends the constant vector to itself and has normalization L^-3 over L^3 parameters. Hence K_00(g)=|K_rs(g)| and sum_g |K_rs(g)|=1. This is an exact probability law with source-specific character phases, rather than an assumed abstract Markov kernel.

The explicit OR search for probability kernel, phase weighted, phase frustration, and twisted Markov returned51 declarations in31 modules (`/tmp/selberg_gram47_probability_corpus.json`). Inspected `CoherentHistoryMechanics.coherentHistory_energy_decomposition`, which decomposes actual finite-fibre energy after a proved fibre-response identity, and `CalibrationSpectrumMechanics.markedVariationDefect_serialAncestry`, which retains phase residuals under actual kernel composition. They suggest the next exact phase-defect identity, but their response hypotheses must be supplied by the present original-source kernel rather than assumed.

Next positive candidate after the kernel audit: express ||v||^2-||C_rs v||^2 as the average squared displacement under the actual three-parameter unitary motions twisted by chi(r*b-s*(a+c)). Every phase has norm1, so direct polarization with the exact normalization proves this paper identity. The intended subsequent estimate must use original Fourier eigenspace constraints and physical gradient; an unweighted Markov contraction alone is not the Selberg quarter bound.

## Lean source certificate

- `formal/GaloisForLFunctions/HTGeometry/FiniteUnipotentFibres.lean`:10 public declarations. Actual word entries, complete fixed/full parameter collision classification, explicit annihilator-fibre equivalence, and exact cardinality.
- `formal/GaloisForLFunctions/RHTower/SelbergMaassInversionGram.lean`:29 public declarations. Actual positive Gram identity, original three-factor phase, reduction/fibre transport, exact convolution, support, sharp magnitude, identity coefficient, physical source HasSum, and exact absolute probability law.

Both complete scratch checks and exact source checks passed. Only the generic fibre module's olean was produced for the Gram module's import. The final audit names both modules individually; no umbrella build is authorized or needed. Main declarations: `triple_collision_full`, `fibreEquiv`, `transferGram_convolution`, `gramKernel_at_word_norm`, `gramKernel_ne_zero_iff`, `neutral_gramKernel_eq_norm`, `sum_norm_gramKernel`, and `source_lower_gram_hasSum`.

## Final verification — 2026-09-09

Both serialized final single-module builds passed, rebuilding exactly their named target: `FiniteUnipotentFibres` in1.9s and `SelbergMaassInversionGram` in6.6s. All39 public declarations passed the post-build scratch axiom audit with only `propext`, `Classical.choice`, and `Quot.sound`; both source hashes remained unchanged. Every public declaration is searchable and appears under its exact module in the API catalog. Each module is imported exactly once by its area umbrella. Index refresh and repository formal lint passed; lint retains existing large-file warnings. Every task-owned Lean/build handle is terminal. No full or umbrella build, numerical experiment, commit, or push ran.

Audit artifacts: `/tmp/selberg_gram47_audit.json`, `/tmp/selberg_gram47_manifest.json`, `/tmp/selberg_gram47_axioms.log`, `/tmp/selberg_gram47_fibres_build.log`, `/tmp/selberg_gram47_operator_build.log`, `/tmp/selberg_gram47_coverage.json`, `/tmp/selberg_gram47_index.log`, and `/tmp/selberg_gram47_lint.log`.

The exact arithmetic kernel and its probability law are proved. The next phase-defect identity has the paper proof above but is not yet formalized. The uniform comparison with four times physical gradient, and hence the full Selberg goal, remain unproved and active.
