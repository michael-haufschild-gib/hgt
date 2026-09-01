# Standard-integer additive--multiplicative coherence forces neutral grade

- **ID:** `ULF-AOC-001`
- **Stage:** 5-failed
- **Type:** FALSIFIED / REDISCOVERED BRIDGE
- **Statement:** `[FALSIFIED]` Exact successor subdivision, multiplicative ancestry, and standard-integer occurrence force every compatible Mellin character to have neutral real grade.

## Big-picture higher law attempted

Replace post-divisor geometry by a pre-zeta arithmetic formation law.  Ordinary integers carry two
simultaneous histories: additive successor and multiplicative factorization.  Multiplication by
`q` subdivides one coarse successor edge into `q` fine edges.  The attempted law asserted that a
character compatible with every such mixed formation diamond must be unitary, so its horizontal
Mellin grade vanishes.

## Corpus audit before the conjecture

- `[CORPUS]` `blockSubdivisionSum_successorEdge` proves exact additive subdivision, and
  `criticalBlockSubdivisionAverage_successorEdge_of_multiplicative` makes every multiplicative
  character a joint eigenvector (`CCMFirstClockBlockSubdivisionTransfer.lean`).
- `[CORPUS]` `pathQuiet_symmetricMultiplicativeCarrier_eq_one` proves a much stronger conclusion
  only after adding the nontrivial cofinal quiet-path estimate
  (`PathQuietMultiplicativeCarrierRigidityUniversalityLaw.lean`).
- `[CORPUS]` additive Euler--Maclaurin data can see a zero while pinned prime-local maps and
  multiplicative sigma jets are trivial
  (`additive_carrier_multiplicative_source_mismatch_positive`).
- `[CORPUS]` modular cocycles, KMS detailed balance, profinite-integer actions, additive--
  multiplicative Haar transport, and critical unitarity interfaces are already present throughout
  `RHTower` and `HTGeometry`.
- `[LITERATURE]` Klurman--Mangerel classify several rigid additive-correlation regimes of completely
  multiplicative functions; exceptional functions are twisted characters `chi(n)n^(it)`
  (arXiv:1707.07817).
- `[LITERATURE]` Tao--Teräväinen obtain the same pretentious character obstruction for higher
  additive correlations at almost all scales (arXiv:1809.02518).
- `[LITERATURE]` Bergelson--Richter develop disjointness of additive and multiplicative semigroup
  actions, under dynamical hypotheses (arXiv:2002.03498).
- `[LITERATURE]` Connes--Consani's arithmetic and scaling sites already geometrize the
  `N^times`-action on arithmetic/profinite data (arXiv:1405.4527, 1507.05818, 1603.03191).

## Exact RH closure that was attempted

An off-line Xi zero of horizontal grade `a = 2 Re(rho)-1` supplies existing prime-scale characters
whose modulus is nonunitary exactly when `a != 0`.  If mixed standard-integer coherence forced all
compatible characters to be unitary, existing corpus equivalences would give `a = 0`, hence
`Re(rho)=1/2` for every nontrivial zero.

## No-go closure

- **Exact killing theorem/mechanism:** Mixed subdivision is an eigenvalue identity, not a
  neutrality law.  For every complex exponent `z`, `F_z(n)=n^z` is completely multiplicative and
  exact telescoping gives

  `q^(-1/2) sum_{j<q} (F_z(qn+j+1)-F_z(qn+j))
    = q^(z-1/2) (F_z(n+1)-F_z(n))`.

  Thus every real grade survives all stated successor--multiplication diamonds; the law records the
  grade as eigenvalue `q^(z-1/2)` instead of forcing it to zero.  The Bost--Connes system supplies
  the same representation lesson externally: exact standard arithmetic supports KMS states across
  noncritical inverse temperatures, so standardness plus modular/KMS compatibility does not select
  one temperature.
- **Verdict:** `REDISCOVERED/BRIDGE` for additive--multiplicative rigidity; `FALSE` for neutral-grade
  selection.
- **Strongest positive survivor:** The mixed block-subdivision spectrum is an exact detector of
  modular grade.  Neutrality is equivalent to unit-modulus eigenvalues for all `q`, but an
  independent cofinal dissipativity/quietness theorem is necessary to select them.  This survivor
  already exists in stronger corpus forms (`SourceNormalClockCurvatureLaw`,
  `PathQuietMultiplicativeCarrierRigidityUniversalityLaw`, and critical half-density unitarity).
- **New insight:** Exact occurrence of standard integers distinguishes generalized-prime
  countermodels but still does not constrain analytic continuation.  Algebraic formation laws
  transport arbitrary modular bias.  A viable replacement must couple formation to an irreversible
  law not satisfied by the full Bost--Connes/KMS temperature family, and that law must be proved
  before Xi specialization.
- **Status:** `NO POSITIVE NEW SALVAGE FOUND`.  Existing positive survivor is already Lean-proved;
  no Lean work warranted.

## Relentless-interrogation replacement

The killing mechanism rules out static coherence, categorical standardness, joining existence,
and KMS compatibility as selectors.  Stronger search question:

> What literal arithmetic law distinguishes the actual continuation not by which states or
> characters exist, but by which changes of modular grade are executable without creating or
> destroying integer occurrences?

This replacement is not yet a conjecture.  It requires a corpus and literature audit of
grade-changing intertwiners, spectral flow, and arithmetic occurrence conservation before an exact
claim is stated.

## Log

- 2026-09-01 — conjecture formulated after countermodel audit; killed by the universal power
  character and existing block-subdivision eigenlaw; external rigidity/site/KMS literature confirms
  the representation is occupied; retired without Lean work.
