# SQB original congruence source averaging

Status: original-source averaging and complete current decomposition formalized;
quantitative quarter comparison remains open. No RH proof.
Frontier map is read-only.

Full chain: original modular source → source-derived occurrence/order comparison
→ critical-line classifier → RH. On the Maass face of SQB, the missing quantitative
step is a quarter comparison retaining the original finite congruence components,
their phase and pair currents, and their core, cusp and nodal contributions.

## Current proved construction

The actual quotient `Deck N` is a finite group. The original Maass component
`quotientForm N f q` obeys the exact right-quotient action under integral
pullback. Existing source current identities preserve all complex pair brackets
and the total phase current. They do not supply a quantitative mixing estimate.

The literal finite regular unitary action and its averaging operator are now
constructed. The operator acts on the complete original congruence value family.
Its exact Reynolds loss is the full source variance. The mean and complete
remainder preserve the actual Maass equation and every integral cusp condition.
The mean is either zero or an actual full-modular cusp eigenform of the same
eigenvalue; the remainder retains the original congruence invariance.

The original pair energy equals centered pair energy plus deck-cardinality
times the sum of mixed mean/remainder bracket squares. The original phase is
the sum of mean and centered phases before squaring. The complete regularized
curvature numerator retains both directional current sums and the entire
regulator-gradient term. Mixed brackets satisfy the original common-equation
conservation law and give a nonnegative lower part of that numerator. The
common-zero locus is preserved exactly.

When the mean vanishes identically, every mixed bracket vanishes and the
centered family equals the full original source. Thus the mixed-channel lower
bound alone does not address this case. A quantitative comparison must retain
the complete centered currents, combined phase square, nodal residual, and
normalization by the full original amplitude.

## Work plan

- [x] Broad OR corpus searches and actual congruence/Reynolds source inspection.
- [x] Construct the finite regular averaging operator and exact source identification.
- [x] Derive actual averaged and complementary Maass equations and cusp conditions.
- [x] Retain complete variance, pair/phase currents, nodes and regulator-gradient terms.
- [x] Identify the zero-average case and exact scope of the mixed-current lower bound.
- [x] Scratch-check, individually build, audit all 58 public declarations and wire modules.
- [x] Construct a finite comparison between centered variance and actual S/T source displacements.
- [ ] Prove a uniform current comparison controlling the full retained contributions.

Broad OR discovery for congruence, mixing, entropy, Poincare and Hecke returned
4,282 declarations in 825 modules. Reynolds, averaging, barycenter, variance and
projection returned 6,241 in 1,641. These counts describe metadata coverage;
the actual congruence trace, Maass definitions, pullback construction, pair/phase
identity and Reynolds-energy proof were inspected before this proposal.

Further geometric/uncertainty OR discovery covered 2,954 declarations in 509
modules; expansion/Poincare/congruence covered 3,188 in 594. Inspected coframe
completion, L² Fourier uniqueness, and torus Poincare statements have additional
structural requirements not yet supplied by this modular source.

[Dependency-closed proof, exact equations, full scope and final audit](../../../3-formalized/sqb-congruence-source-mixing.md).
Three new modules contain 58 public declarations. All individual builds, axiom
checks, index/wiring checks and repository formal lint passed. The global
`totalOrbitCurvature >= amplitudeMass/8` comparison remains open, as does the
independent full-Xi occurrence handoff required for RH.

The [actual generator-cost construction](sqb-congruence-generator-cost.md) now
controls complete centered variance by literal S/T displacements at each fixed
level and preserves its normalized chord law at original nodes. Its quadratic
word-cost coefficient provably diverges over levels, even for least-cost words;
changing complete representatives cannot make this recipe uniform. A sharper
source/current estimate remains necessary. This does not classify the optimal
S/T spectral gap.
