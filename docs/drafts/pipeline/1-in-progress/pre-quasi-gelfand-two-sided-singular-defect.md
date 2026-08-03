# Two-sided singular defects in pre-quasi Gelfand triples

- **ID:** `pre-quasi-gelfand-two-sided-singular-defect`
- **Stage:** 1-in-progress
- **Type:** FALSIFICATION / CLASSIFICATION CANDIDATE
- **External target:** Skrepek, *Quasi Gelfand Triples*, IEOT 97 (2025),
  Conjectures 6.7 and 6.8
- **Exact claim:** Hilbert pre-quasi Gelfand triples need not be quasi.  Proper defects are exactly
  proper closed subspaces of a canonical singular graph with both coordinate projections dense;
  a codimension-one defect exists exactly when the canonical operator is unbounded and not bounded
  below.

## Status labels

- `[LITERATURE]` Skrepek's Conjecture 6.7 asserts every Hilbert pre-quasi Gelfand triple is quasi;
  Conjecture 6.8 asserts the Banach analogue.
- `[LOCAL-RESEARCH]` Corpus contains ordinary rigged triples, graph-closure vertical-fibre laws,
  and dense-core relation saturation, but no pre-quasi/quasi discriminator or attack on these
  conjectures.
- `[CONJECTURE]` Exact classification and counterexample above.
- `[OPEN CORE]` Prove the canonical graph-subspace equivalence with all duality conventions, then
  prove both directions of the two-sided-singularity criterion without a hidden closed-range or
  surjectivity assumption.
- `[NOVELTY UNVERIFIED]` Exact-phrase and parent-theory searches found no resolution through
  2026-08-03; citation-descendant and equivalent-formulation audit remains open.

## Candidate explicit counterexample

Let all three Hilbert spaces be `ell2(N)` with their standard duality.  On even/odd coordinates set

```text
b_(2k)   = k+1,
b_(2k+1) = 1/(k+1),
B = diag(b_n),
A = B^(-1).
```

On the graph domain of `B`, define

```text
c_(2k)   = 1,
c_(2k+1) = 1/(k+1),
L(x) = sum_n c_n x_n,
D = ker L.
```

The candidate embeddings are

```text
i_+ = A : dom A -> ell2,
i_- = B|D : D -> ell2.
```

The coefficient tests are designed so that `L` is graph-norm continuous, while `c` and `c/b` are
both outside `ell2`.  Therefore `D` and `B(D)` should both be dense in `ell2`, although `D` is a
proper graph-closed codimension-one subspace.  The pairing identity is

```text
<i_- g, i_+ f> = <B g, A f> = <g,f>.
```

Since `dom(i_+^*) = dom A = ran B` but `ran(i_-) = B(D)` is proper, this is pre-quasi but not quasi.

## Proposed classification

Let `A : dom A subset X_+ -> X_0` be a closed densely defined injective operator with dense range,
after identifying the Hilbert anti-dual `X_-` with `X_+`.  Put

```text
B = (A^*)^(-1).
```

Every compatible pre-quasi negative embedding is a closed restriction of `B`.  Its graph is a
closed subspace `M` of `graph B` whose two coordinate projections are dense.  Conversely every such
`M` gives a pre-quasi triple.  It is quasi exactly when `M = graph B`.

For the graph Hilbert space `G(B)`, write `P(x,Bx)=x` and `Q(x,Bx)=Bx`.  A codimension-one defect
`M=v^perp` has both projections dense exactly when

```text
v notin ran(P^*) union ran(Q^*).
```

Such a `v` exists exactly when neither adjoint is surjective, equivalently when `B` is unbounded and
not bounded below.  This is the proposed sharp boundary between automatic quasi triples and
singular defective triples.

## Hostile attacks required

1. Check that a complete Hilbert dual pair can be normalized by the correct linear/anti-linear
   unitary without changing adjoint domains.
2. Check that `B=(A^*)^(-1)` is closed, densely defined, injective, and dense-range under exactly the
   stated hypotheses.
3. Prove the graph-subspace converse, not only the explicit diagonal example.
4. Prove `P^*` surjective iff `B` is bounded and `Q^*` surjective iff `B` is bounded below, including
   domain/range closure details.
5. Search `triplets of closely embedded Hilbert spaces`, closed restrictions, boundary trace
   spaces, and equivalent Gram-operator formulations for an existing counterexample or theorem.
6. Determine whether counterexample survives published 2025 definition rather than only arXiv
   notation.

## No-go closure if candidate fails

- **Exact killing theorem/mechanism:** pending.
- **Strongest positive survivor:** pending; target is a sharp sufficient condition for automatic
  quasi-ness, not a weakened example.
- **New insight:** candidate mechanism predicts failure only from simultaneous ultraviolet and
  infrared singularity of the canonical graph.
- **Status:** Stage 1; no paper-proof or Lean claim yet.

## Lean gate

No Lean implementation before the paper proof and priority audit close.  Intended exact formal
surface, if promoted, is the abstract graph-subspace theorem plus the explicit unconditional
`ell2` counterexample; no finite-dimensional surrogate counts.

## Log

- 2026-08-03 — external frontier exposed Skrepek Conjectures 6.7--6.8; froze two-sided singular
  graph-defect candidate and explicit alternating diagonal attack.
