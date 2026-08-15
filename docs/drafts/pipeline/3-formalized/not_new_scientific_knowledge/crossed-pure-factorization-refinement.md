# Crossed pure factorizations force fourfold refinement

- **ID:** `crossed-pure-factorization-refinement`
- **Stage:** 3-formalized
- **Type:** PURE-TENSOR RIGIDITY / FACTORIZATION-PROFILE BRIDGE
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../../1-in-progress/history-nonseparability-unification-law.md`
- **Physical target:** `../../1-in-progress/event-relative-independence-spacetime-law.md`
- **Formalized companion:**
  `crossed-pure-factorization-refinement-formalized.md`

## Exact theorem

Let \(\Bbbk\) be a field and let \(I,J,K,L\) be arbitrary index types. Suppose

\[
x:I\times J\to\Bbbk,\qquad y:K\times L\to\Bbbk,
\]
\[
u:I\times K\to\Bbbk,\qquad v:J\times L\to\Bbbk
\]

satisfy

\[
x_{ij}y_{k\ell}=u_{ik}v_{j\ell}                                   \tag{1}
\]

for every \(i,j,k,\ell\). If \(x\neq0\) and \(y\neq0\), then there exist functions

\[
a:I\to\Bbbk,\quad b:J\to\Bbbk,\quad
c:K\to\Bbbk,\quad d:L\to\Bbbk
\]

such that

\[
x_{ij}=a_i b_j,\qquad y_{k\ell}=c_kd_\ell.                         \tag{2}
\]

Consequently the common four-index tensor refines to four one-index factors:

\[
x_{ij}y_{k\ell}=a_i b_j c_k d_\ell.                               \tag{3}
\]

In tensor language, a nonzero four-party pure tensor that factorizes across both crossed
bipartitions

\[
IJ\mid KL
\qquad\text{and}\qquad
IK\mid JL
\]

factorizes across their common four-block refinement

\[
I\mid J\mid K\mid L.
\]

## Proof

Because \(x\neq0\), choose \(i_0,j_0\) with

\[
x_{i_0j_0}\neq0.
\]

Because \(y\neq0\), choose \(k_0,\ell_0\) with

\[
y_{k_0\ell_0}\neq0.
\]

Define

\[
a_i=u_{ik_0},
\qquad
b_j=\frac{v_{j\ell_0}}{y_{k_0\ell_0}},
\]

\[
c_k=\frac{u_{i_0k}}{x_{i_0j_0}},
\qquad
d_\ell=v_{j_0\ell}.                                                \tag{4}
\]

Putting \(k=k_0\) and \(\ell=\ell_0\) in `(1)` gives

\[
x_{ij}y_{k_0\ell_0}=u_{ik_0}v_{j\ell_0}.
\]

Division by the nonzero scalar \(y_{k_0\ell_0}\) and `(4)` give

\[
x_{ij}=a_i b_j.
\]

Putting \(i=i_0\) and \(j=j_0\) in `(1)` gives

\[
x_{i_0j_0}y_{k\ell}=u_{i_0k}v_{j_0\ell}.
\]

Division by the nonzero scalar \(x_{i_0j_0}\) gives

\[
y_{k\ell}=c_kd_\ell.
\]

Multiplying these two identities proves `(3)`. ∎

## Hostile audit

The proof is elementary Segre-tensor rigidity. Multipartite pure-state separability is already
organized by the partition lattice. Szalay develops the lattice structure of partial separability
and entanglement classes:

- S. Szalay, *Multipartite entanglement measures*,
  <https://arxiv.org/abs/1503.06071>;
- S. Szalay, *Quantum entanglement in finite-dimensional Hilbert spaces*,
  <https://arxiv.org/abs/1302.4654>.

The exact crossed-coordinate statement above is therefore `[REDISCOVERED]`. No mathematical or
physical novelty claim is permitted.

## Strongest positive survivor

The theorem removes one false source of ambiguity:

> Relative to a fixed family of pure-history ports, two crossed exact factorizations cannot encode
> two incompatible indivisible worlds. Their coexistence forces a strictly finer factorization.

Thus the factorization profile of a nonzero pure history has a local meet/refinement law. In the
four-block crossing, factorization data determine a common atomic refinement without choosing
between the two cuts.

The research consequence is negative but precise:

> The missing spacetime primitive is not a rule for choosing one tensor cut from several exact pure
> cuts. The hard datum is the source-generated port family to which any cut refers.

## Physical boundary

The theorem assumes all of the structure that the Theory-of-Everything programme must derive:

1. four supplied port types \(I,J,K,L\);
2. a common scalar field;
3. one common coordinate presentation;
4. an exactly pure rank-one factorization across each bipartition; and
5. exact equality rather than operational approximation.

It does not construct ports, define physical independence, survive arbitrary gauge or quantum
reference-frame change, handle gravitational dressing, or derive spacetime.

The purity hypothesis is especially restrictive. Operational process tensors, reduced states, and
coarse-grained histories are generally mixed. Convex decompositions can depend on the partition,
so pure-state refinement cannot simply be transferred to mixed dynamics. A physical successor must
either:

1. derive a source-pure/extremal history lift and prove presentation-independent descent; or
2. retain the complete boundary record of the convex decomposition instead of using state
   separability alone.

This aligns with the boundary-colligation programme: loss of purity cannot be discarded if the
record is supposed to generate the next independence law.

## Exact insight delta

```text
bare compatibility graph
  -> arbitrary, no spacetime rigidity;

one preferred tensor split
  -> transported by any dynamics, no invariant interaction;

all exact pure factorizations over fixed ports
  -> crossed cuts refine canonically;

remaining open datum
  -> source-generated relational ports plus full mixed-history record.
```

The next status-changing target is not another pure tensor theorem. It is a relational intervention
groupoid whose objects and admissible port families are generated from source-complete physical
tests, together with a process/colligation functor whose extremal refinement descends under gauge
and quantum-reference-frame changes.

## Lean target

Formalize `(2)` and `(3)` for arbitrary index types over an arbitrary field, reusing the existing
coordinate Segre rigidity module where useful.

Required declarations:

1. `crossedBlockFactorization_refines`;
2. `crossedPureFactorization_refines_to_four`.

No finite-dimensional, nonempty-index, Hilbert-space, positivity, or computation hypothesis is
needed.

## Gates

- [x] exact claim and quantifiers fixed
- [x] dependency-closed proof
- [x] hostile rediscovery audit
- [x] strongest positive survivor and physical limitation recorded
- [x] exact theorem formalized unconditionally in Lean
- [ ] source-generated relational port family constructed
- [ ] mixed/extremal descent proved

## Log

- 2026-07-30 — extracted the four-block crossing theorem from the open relational-factorization
  profile and proved it by two nonzero coordinate contractions.
- 2026-07-30 — classified the theorem as standard pure-state partition-lattice rigidity; isolated
  source-generated ports and mixed-history descent as the remaining physical core.
- 2026-07-30 — formalized both exact coordinate theorems unconditionally in
  `HTGeometry/CrossedPureFactorizationRefinement.lean`; focused build and axiom audit passed.
