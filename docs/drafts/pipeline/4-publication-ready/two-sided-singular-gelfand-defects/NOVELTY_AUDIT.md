# Novelty and collision audit

Search date: 3 August 2026.

Status: `[NOVELTY UNVERIFIED]` pending independent operator-theory expert and MathSciNet/zbMATH
priority review. Search absence is evidence, not proof of priority.

## Exact mathematical delta

Paper proves three results not found together or separately in searched literature:

1. Compatible closed negative embeddings below a fixed Hilbert positive embedding are exactly
   closed bi-dense subspaces of canonical inverse-adjoint graph.
2. Proper closed bi-dense graph subspace exists iff both graph coordinate maps lack uniform lower
   bound. Equivalently, canonical inverse-adjoint is unbounded and not bounded below. A
   codimension-one hyperplane always suffices.
3. Explicit positive self-adjoint diagonal model on `ell2({0,1} x N)` supplies Hilbert pre-quasi
   Gelfand triple which is not quasi, falsifying published Conjectures 6.7 and 6.8.

New knowledge is theorem/counterexample content above. Pipeline movement, terminology, Lean
translation, and paper production are not counted as novelty.

## Primary direct source

Nathanael Skrepek, *Quasi Gelfand Triples*, Integral Equations and Operator Theory 97, article 1
(2025), DOI 10.1007/s00020-024-02780-9:

- Definition 4.1 gives exact pre-quasi hypotheses used by counterexample: complete dual pair;
  closed, densely defined, injective embeddings with dense range; pivot pairing identity.
- Quasi condition is `dom iota_+^* = ran iota_-`.
- Lemma 4.5 constructs maximal compatible extension `(iota_+^*)^{-1}` but does not prove every
  original embedding saturated.
- Conjecture 6.7: every Hilbert pre-quasi triple is quasi.
- Conjecture 6.8: every pre-quasi triple is quasi.
- Author states attempts to prove weak conjecture failed and notes positive solution would imply a
  weak/strong boundary-trace equality route.

Definition and conjecture wording were checked against published Springer version, not only arXiv
metadata.

## Collision matrix

| Source/area | Existing result | Why no collision |
|---|---|---|
| Cojuhari--Gheondea, *Triplets of Closely Embedded Hilbert Spaces* (2015) | Hilbert triples with full Hamiltonian/adjoint compatibility | Starts on saturated canonical graph; does not classify proper bi-dense restrictions or prove automatic saturation |
| Skrepek, *Quasi Gelfand Triples* (2025) | Canonical extension, Gram operators, decomposition, Conjectures 6.7--6.8 | Poses exact automaticity question; does not give counterexample or sharp graph criterion |
| Closed-operator graph theory | Graph norm, coordinate maps, closed-range criteria | Supplies ingredients; searched sources do not state simultaneous dense-projection hyperplane criterion as pre-quasi classification |
| Linear-relation decomposition theory | Operator/multivalued decomposition after graph closure | Present defect is a proper closed single-valued subrelation; it is not multivalued part or nonclosability |
| Skrepek--Pauly, weak/strong tangential traces (2025) | PDE-specific equality under Lipschitz hypotheses | Does not prove abstract automaticity; compatible with one-sided lower bound supplied by PDE structure |
| Port-Hamiltonian descendants | Use quasi Gelfand triples for boundary systems | Begin with completed quasi structure or application-specific estimates; no abstract conjecture resolution found |

## Searches performed

Search families included:

- exact phrases: `"pre-quasi Gelfand triple"`, `"every pre-quasi Gelfand triple"`,
  `"Conjecture 6.7" "quasi Gelfand"`;
- title/citation descendants of Skrepek 2025;
- `closed restriction`, `proper closed restriction`, `dense domain dense range`, `graph
  hyperplane`, and `inverse adjoint` combined with quasi Gelfand terms;
- closely embedded Hilbert triplets, singular operator relations, boundary trace equality, and
  port-Hamiltonian uses;
- exact proposed phrase `two-sided singular` with operator graphs, to detect terminology or theorem
  collision.

Current web/index results expose Skrepek paper, closely embedded Hilbert predecessors, PDE-specific
trace work, and applications. No source found with counterexample or iff criterion. Generic search
results for “two-sided singular” concerned singular stochastic control, not operator graph geometry.

## Hard novelty attacks

### “This is already Lemma 4.5”

No. Lemma 4.5 says compatible embedding can be extended to maximal inverse-adjoint partner.
Present theorem classifies every closed compatible restriction and shows proper bi-dense ones can
exist. Counterexample is exactly failure of original embedding to equal extension.

### “This is a trivial core restriction”

Arbitrary proper restriction loses closedness, dense domain, or dense range. Paper proves exact
existence boundary and constructs a graph-closed codimension-one restriction invisible under both
coordinate closures. Simultaneous density is substantive condition that published conjecture
predicted would force saturation.

### “This is merely an example”

No. Explicit example is consequence of classification and universal sharp criterion. Criterion is
necessary and sufficient for every closed canonical graph in standard Hilbert model.

### “This is standard singular linear-relation decomposition”

No. Canonical relation remains graph of injective single-valued closed operator. Defect is a proper
closed subgraph with both coordinate projections dense; no multivalued part appears.

### “Counterexample depends on exotic spaces”

No. All three spaces are same separable Hilbert space with standard complete anti-dual pairing.
Canonical operators are positive self-adjoint diagonals. Defect has graph codimension one.

## Significance audit

Positive factors:

- settles two explicit recent published conjectures;
- supplies classification explaining all failure modes in natural Hilbert subclass;
- proves sharp positive replacement theorem;
- gives minimal codimension-one counterexample with positive self-adjoint diagonal data;
- identifies exact extra estimate application-specific theories must prove;
- carries unconditional machine-checked formalization of headline surface.

Limits stated in manuscript:

- no specific PDE weak/strong trace counterexample;
- no claim of Banach-space defect classification;
- no claim that graph norms, adjoint closed-range theorem, or diagonal operators are individually
  new;
- priority remains provisional until independent database/expert audit.

## Publication assessment

At claim level, result fits renowned general mathematical journal’s concise problem-solving paper
category: recent explicit conjectures are resolved, mechanism is classified, strongest positive
replacement is sharp, proof is self-contained, and counterexample is minimal. General-audience
reach comes from rigged Hilbert spaces, unbounded operators, and boundary-trace implications.
Likely journal shape is a strong short article rather than long foundational treatise.

Independent specialist priority review remains mandatory before submission.
