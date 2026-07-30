# Independent-composition boundary-record conservation

- **ID:** `independent-composition-boundary-record-conservation`
- **Stage:** 2-fully-proven
- **Type:** SHARP FINITE-DIMENSIONAL THEOREM / MINIMAL RECORD COMPLETION
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `finite-carrier-spacelike-compression-defect.md`
- **Physical target:** `../../1-in-progress/event-relative-independence-spacetime-law.md`

## Exact theorem

Let \(K\) be a field. Let \(V\) and \(E\) be finite-dimensional \(K\)-vector spaces and put

\[
d=\dim_KV.
\]

Consider a public compression and a complementary record

\[
\mu:V\otimes_KV\longrightarrow V,
\qquad
R:V\otimes_KV\longrightarrow E.
\]

If the combined map

\[
(\mu,R):V\otimes_KV\longrightarrow V\oplus E                         \tag{1}
\]

is injective, then

\[
\boxed{\dim_KE\geq d^2-d.}                                          \tag{2}
\]

If the record has the minimal possible dimension

\[
\dim_KE=d^2-d,                                                       \tag{3}
\]

then all of the following hold:

1. `(1)` is a linear equivalence:

   \[
   V\otimes_KV\simeq V\oplus E;                                     \tag{4}
   \]

2. \(\mu\) is surjective;
3. the kernel has the sharp dimension

   \[
   \dim_K\ker\mu=d^2-d;                                              \tag{5}
   \]

4. the restricted record is a linear equivalence:

   \[
   R|_{\ker\mu}:\ker\mu\simeq E.                                    \tag{6}
   \]

Thus a faithful minimal record contains exactly the independent-composition directions erased by
the public compression, and public output plus record reconstructs the whole tensor input.

## Proof

The finite-carrier tensor-compression theorem gives

\[
d^2-d\leq\dim_K\ker\mu.                                             \tag{7}
\]

Injectivity of `(1)` implies that \(R|_{\ker\mu}\) is injective: if \(x,y\in\ker\mu\) and
\(R(x)=R(y)\), then

\[
(\mu(x),R(x))=(0,R(x))=(0,R(y))=(\mu(y),R(y)),
\]

so \(x=y\). Therefore

\[
\dim_K\ker\mu\leq\dim_KE.                                          \tag{8}
\]

Combining `(7)` and `(8)` proves `(2)`.

Assume `(3)`. Tensor multiplicativity and finite-dimensional additivity give

\[
\dim_K(V\otimes_KV)=d^2
\]

and

\[
\dim_K(V\oplus E)=d+(d^2-d)=d^2.
\]

Hence the injective map `(1)` is bijective, proving `(4)`. Projecting its surjectivity onto the
first factor proves that \(\mu\) is surjective. The sharp tensor-compression theorem then gives
`(5)`. Equations `(3)` and `(5)` show that the already-injective map
\(R|_{\ker\mu}:\ker\mu\to E\) has equal-dimensional source and target, so it is bijective. This
proves `(6)`. ∎

## Exact conservation form

The result can be read as the split finite-dimensional identity

\[
\boxed{
\text{independent joint capacity}
=
\text{public capacity}
+
\text{minimal complementary record capacity}.
}
\tag{9}
\]

More sharply, `(6)` identifies the record with the erased subspace, not merely with a space of the
same dimension.

This is the exact finite shadow sought after the direct-sum totalization no-go:

```text
typed sequential change
  -> always fits in one larger fixed direct-sum theory;

independent tensor composition compressed to one finite public carrier
  -> exact missing capacity d²-d;

faithful minimal complementary record
  -> erased joint directions ≃ record
  -> tensor input ≃ public output ⊕ record.
```

## Hostile mathematical verdict

This theorem is an immediate combination of tensor-product dimension, rank--nullity, and the
equal-dimension injective--surjective equivalence. It is `[REDISCOVERED]`, not new mathematics.

The record \(R\) is supplied. Injectivity of \((\mu,R)\) assumes the desired faithfulness. The
theorem does not:

1. canonically construct \(R\) from \(\mu\);
2. prove that a physical composite uses the full tensor product;
3. prove that a bounded physical region has finite exact capacity;
4. show that \(E\) is localized on a geometric boundary;
5. turn dimension into entropy or area;
6. derive gauge constraints, locality, gravity, or holography; or
7. show that an actual event creates a new independence relation.

In particular, defining \(E=\ker\mu\) and \(R\) as a chosen projection would make the completion
tautological. Physical content can arise only from a source law that independently derives the
record, its observability, and its localization.

## Strongest positive survivor

`[PAPER-PROVED] [LEAN-PROVED]`

For a finite carrier, exact independent composition cannot be both compressed and faithfully
forgotten. At minimal overhead, conservation is rigid:

\[
\ker\mu\simeq E
\quad\text{and}\quad
V\otimes V\simeq V\oplus E.
\]

This supplies an exact target for a non-tautological physical derivation:

> Derive a source-selected record \(E\) and prove that it is the operational boundary data
> required to preserve independently composable alternatives.

If that derivation also forces boundary localization and an area scaling in a continuum limit,
`(9)` becomes a candidate microscopic holographic conservation law. Neither step is presently
proved.

## Relation to gauge and gravitational factorization

Gauge theories and gravity weaken naive tensor factorization of spatial regions. Edge modes,
gravitational dressing, centers, constraints, and relational frames can all alter the physical
composite. Those facts do not contradict the theorem; they challenge its physical hypotheses.

The result must therefore be used conditionally:

```text
IF a source-derived finite carrier has exact tensor-independent composition,
AND a source-derived public event compresses it into one carrier,
AND public output plus source-derived record is faithful,
THEN record capacity obeys (2), with rigidity (4)--(6) at equality.
```

Bare nonfactorization is not gravity. The open physical target is a dynamically changing law of
independent composition whose comparison, rather than its mere failure, reproduces geometry and
forces.

## Literature boundary

- Tensor-product dimension, rank--nullity, and finite-dimensional completion are standard linear
  algebra; no novelty claim is permitted.
- Casini, Huerta, and Rosabal analyse how gauge constraints and choices of regional algebra obstruct
  naive Hilbert-space factorization: <https://arxiv.org/abs/1312.1183>.
- Donnelly and Freidel construct gauge and gravitational regional phase spaces with boundary
  degrees of freedom: <https://arxiv.org/abs/1601.04744>.
- Donnelly and Giddings show that gravitationally dressed observables do not furnish ordinary local
  commuting subalgebras: <https://arxiv.org/abs/1607.01025>.

These works motivate the boundary question but do not turn this elementary theorem into a physical
law.

## Lean status

The exact lower bound, minimal boundary dimension identity, full bijectivity, forced surjectivity,
kernel--record bijection, and both linear equivalences are proved unconditionally in

`formal/GaloisForLFunctions/HTGeometry/IndependentCompositionBoundaryRecord.lean`.

Direct source check passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/IndependentCompositionBoundaryRecord.lean
PASS
```

Focused build and axiom audit are recorded on the Stage-3 card.

## Gates

- [x] exact theorem stated
- [x] dependency-closed paper proof
- [x] equality case and rigidity extracted
- [x] tautology and rediscovery boundary explicit
- [x] physical hypotheses and escape routes explicit
- [x] exact theorem formalized in Lean
- [ ] source-selected physical record derived
- [ ] finite physical carrier and tensor-independence derived
- [ ] boundary localization and continuum scaling derived

## Log

- 2026-07-30 — combined the finite tensor-compression debt with complementary-event-record
  injectivity and extracted the exact minimal completion law.
- 2026-07-30 — hostile audit classified the result as standard finite-dimensional algebra and
  isolated the missing physics: source-selection, localization, and dynamical independent
  composition.
