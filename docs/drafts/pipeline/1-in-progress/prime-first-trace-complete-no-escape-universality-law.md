# Prime first-trace complete no-escape universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`

## Theorem-generated discovery

Two terminal first-trace laws expose complementary levels of one obstruction:

- `primeFirstTraceClock_closedRelationRiggingUniversality` computes the exact closed graph, proves
  every closed linear extension is multivalued, and transfers nonclosability to exact-norm complete
  riggings;
- `primeFirstTraceClock_topologicalNonlinearRiggingNoEscapeUniversality` extends failure to
  arbitrary closed single-valued relations, nonlinear closed graphs, and topology-preserving source
  realizations.

The first module additionally proves the stronger hereditary statement
`primeFirstTraceClock_closedRelationExtension_contains_zeroVacuum`: every closed linear extension
contains the entire zero-vacuum vertical Hardy hyperplane.  No corpus theorem records that
universal fibre statement together with every nonlinear, topological, and rigging failure.

## Universal law

For the actual-prime first-trace clock, simultaneously:

1. a pair lies in the minimal closed graph exactly when its response has zero vacuum coordinate;
2. every closed linear relation extension contains every vertical pair `(0,y)` with `y(0)=0`;
3. no closed linear extension can have trivial vertical fibre;
4. no arbitrary closed relation containing the graph can be single-valued;
5. no nonlinear map extending the clock has a closed graph;
6. every topology-preserving source realization of the clock has nonclosed graph;
7. every exact-source-norm/exact-clock-norm complete rigging remains sequentially nonclosable.

The zero-vacuum hyperplane is therefore the common obstruction across all completion categories.

## Paper proof

Invoke `primeFirstTraceClock_closedRelationRiggingUniversality` for the exact graph, closed linear
extension, and rigging conclusions.  Invoke
`primeFirstTraceClock_topologicalNonlinearRiggingNoEscapeUniversality` with the same source and
clock realizations for the arbitrary relation, nonlinear graph, topological graph, and rigging
conclusions.  For an arbitrary closed linear extension `G`, apply
`primeFirstTraceClock_closedRelationExtension_contains_zeroVacuum` directly.  All statements use
the identical graph and exact-norm data.

## Corpus inputs

- `RHTower.primeFirstTraceClock_closedRelationRiggingUniversality`
- `RHTower.primeFirstTraceClock_topologicalNonlinearRiggingNoEscapeUniversality`
- `RHTower.primeFirstTraceClock_closedRelationExtension_contains_zeroVacuum`

## Novelty protocol

No literature search was performed before exact Lean proof passed.

Post-proof searches covered closable operators, graph closures, multivalued linear relations,
hereditary multivalued parts under extension, Hardy-space operators, and nonlinear closed-graph
extensions.

Nearest sources:

- Shi--Xu--Ren, *Boundedness and closedness of linear relations*, arXiv:1604.07979, develops
  closedness, closability, and boundedness criteria for multivalued linear relations:
  <https://arxiv.org/abs/1604.07979>
- Tarcsay--Sebestyén, *Canonical Graph Contractions of Linear Relations on Hilbert Spaces*,
  arXiv:2007.00954, studies closed graph relations, their multivalued parts, and regular
  decompositions:
  <https://arxiv.org/abs/2007.00954>
- Mogilevskii, *Symmetric extensions of symmetric linear relations (operators) preserving the
  multivalued part*, treats extension theory with a prescribed multivalued part:
  <https://mfat.imath.kiev.ua/article/?id=1055>

No source found the exact arithmetic law: the actual-prime first-trace clock has graph closure
equal to all source vectors paired with the zero-vacuum Hardy hyperplane, every closed linear
extension inherits that full hyperplane, and arbitrary linear, nonlinear, topological, and
exact-norm rigging escapes fail simultaneously.  Novelty claim is restricted to this formal
statement.

## Lean target

`formal/GaloisForLFunctions/RHTower/PrimeFirstTraceCompleteNoEscapeUniversalityLaw.lean`

## Verification

- exact and warning-free:
  `lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceCompleteNoEscapeUniversalityLaw.lean`
- wired into `formal/GaloisForLFunctions/RHTower.lean`
- final module, axiom, and lint audits deferred to terminal pass
