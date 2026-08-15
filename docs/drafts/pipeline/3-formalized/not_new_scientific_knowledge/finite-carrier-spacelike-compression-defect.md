# Finite-carrier spacelike compression defect

- **ID:** `finite-carrier-spacelike-compression-defect`
- **Stage:** 3-formalized
- **Type:** SHARP FINITE-DIMENSIONAL THEOREM / MONOIDAL CAPACITY NO-GO
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `universal-typed-event-network-fixed-carrier-no-go.md`
- **Physical target:** `../../1-in-progress/event-relative-independence-spacetime-law.md`
- **Formalized companion:**
  `finite-carrier-spacelike-compression-defect-formalized.md`

## Exact theorem

Let \(K\) be a field and let \(V\) be a finite-dimensional \(K\)-vector space of dimension

\[
d=\dim_K V.
\]

For every linear compression

\[
\mu:V\otimes_K V\longrightarrow V,
\]

the information-loss subspace obeys the sharp lower bound

\[
\dim_K\ker\mu\ \geq\ d^2-d.                                       \tag{1}
\]

Consequently:

1. if \(d\geq2\), then \(\mu\) is not injective;
2. if \(\mu\) is injective, then \(d\leq1\); and
3. if \(\mu\) is surjective, equality holds in `(1)`:

   \[
   \dim_K\ker\mu=d^2-d.                                            \tag{2}
   \]

Thus no finite nonclassical carrier admits a faithful linear encoding of two independent copies
back into the same carrier.

## Proof

Finite-dimensional tensor-product multiplicativity over the field \(K\) gives

\[
\dim_K(V\otimes_KV)=d^2.                                           \tag{3}
\]

Rank--nullity for \(\mu\) gives

\[
\dim_K\operatorname{range}\mu+\dim_K\ker\mu=d^2.                   \tag{4}
\]

Since \(\operatorname{range}\mu\) is a subspace of \(V\),

\[
\dim_K\operatorname{range}\mu\leq d.                               \tag{5}
\]

Subtracting `(5)` from `(4)` proves `(1)`.

If \(d\geq2\), then \(d^2>d\). An injective \(\mu\) would imply
\(\dim(V\otimes V)\leq\dim V\), contradicting `(3)`. Equivalently, `(1)` gives
\(\dim\ker\mu\geq d(d-1)>0\). This proves items 1 and 2.

If \(\mu\) is surjective, its range is \(V\), so `(4)` becomes

\[
d+\dim_K\ker\mu=d^2,
\]

which proves `(2)`. ∎

## Sharpness

The lower bound is attained by every surjection \(V\otimes_KV\to V\). Such surjections exist for
every nonzero finite-dimensional \(V\): choose a nonzero linear functional on one factor and use
the induced contraction

\[
v\otimes w\longmapsto\lambda(v)w.
\]

Sharpness is recorded only at paper level. The Lean target needs no choice of functional: it proves
the bound for every map and equality under an explicit surjectivity hypothesis.

## Relation to the universal fixed-carrier theorem

The direct-sum theorem proves that every typed **sequential** event network fits faithfully inside
one fixed carrier. Only one source type is active on each typed arrow, so orthogonal corners retain
all information.

Spacelike independence is different. Two independently variable copies carry the tensor product
\(V\otimes V\), whose finite dimension multiplies. Compressing that tensor product back into the
same finite carrier loses at least \(d^2-d\) linear dimensions.

This gives the first exact finite-resource certificate that survives the direct-sum no-go:

> A fixed finite carrier can preserve arbitrary typed sequential composition, but it cannot
> preserve faithful independent self-composition unless it is classical-trivial.

## Hostile physical verdict

The theorem is elementary finite-dimensional linear algebra and is not new scientific knowledge.
It does not prove that nature creates possibility carriers.

Four escape routes remain:

1. an infinite-dimensional separable Hilbert carrier can be isomorphic to its tensor square;
2. two spacelike regions may use a larger composite carrier rather than the original carrier;
3. gauge and gravitational constraints can replace the full tensor product by a matched physical
   subspace; and
4. a bounded region's exact quantum-gravitational carrier has not been proved finite-dimensional
   in general.

Consequently the theorem does not establish gravity, locality, holography, or the frozen physical
conjecture. Its physical value is exact:

> Any finite-capacity realization of event-created independence must either enlarge the carrier,
> lose independent information, or deny exact tensor independence.

This is the first sharp boundary between the fixed-carrier sequential dilation and a genuinely
monoidal physical requirement.

## Strongest positive survivor

`[PAPER-PROVED]` Define the finite spacelike compression debt of \(\mu\) by

\[
\mathfrak d(\mu)=\dim\ker\mu.
\]

Then

\[
\mathfrak d(\mu)\geq d(d-1),
\]

with equality for every surjective compression. The debt is zero exactly when a faithful
self-compression is dimensionally possible, which forces \(d\leq1\).

This supplies a quantitative finite-resource target for the physical programme. A successful
holographic or operational bridge would have to derive a finite carrier \(V(R)\) for a bounded
region, derive spacelike composition independently, and identify how the unavoidable debt is
stored in boundary, gauge, or gravitational data.

## Literature and rediscovery audit

- `[LITERATURE]` Tensor-product dimension multiplicativity and rank--nullity are standard linear
  algebra. The theorem is their immediate sharp combination.
- `[LITERATURE]` Casini, Huerta, and Rosabal show that gauge constraints obstruct naive regional
  Hilbert factorization and that regional algebra choices can carry boundary ambiguities:
  <https://arxiv.org/abs/1312.1183>.
- `[LITERATURE]` Donnelly and Freidel restore gauge-invariant regional phase spaces by boundary
  degrees of freedom:
  <https://arxiv.org/abs/1601.04744>.
- `[LITERATURE]` Donnelly and Giddings show that gravitational dressing obstructs ordinary local
  commuting subalgebras:
  <https://arxiv.org/abs/1607.01025>.
- `[LITERATURE]` Spalvieri, Garmier, and Giacomini give an operational field-mediated
  entanglement criterion without local Hilbert tensor factorization, confirming that
  nonfactorization alone is not interaction:
  <https://arxiv.org/abs/2512.19806>.

The mathematical result is `[REDISCOVERED]`. No novelty claim is permitted.

## Lean status

The exact lower bound, noninjectivity for \(d\geq2\), injectivity classification, equality for
surjective compression, and tensor-square equivalence corollary are `[LEAN-PROVED]` in
`formal/GaloisForLFunctions/HTGeometry/FiniteCarrierSpacelikeCompression.lean`.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.FiniteCarrierSpacelikeCompression
✔ [1558/1558] Built GaloisForLFunctions.HTGeometry.FiniteCarrierSpacelikeCompression
Build completed successfully (1558 jobs).
```

The axiom audit for every declaration reports only:

```text
propext
Classical.choice
Quot.sound
```

Repository formal lint passed.

## Gates

- [x] exact sharp theorem stated
- [x] dependency-closed proof
- [x] sharpness and equality case
- [x] direct-sum relation and physical boundary
- [x] hostile rediscovery audit
- [x] strongest positive survivor extracted
- [x] exact theorem formalized in Lean
- [ ] finite physical carrier and boundary-debt bridge derived

## Log

- 2026-07-29 — isolated the first finite-resource obstruction that survives universal
  fixed-carrier sequential dilation: independent tensor composition cannot be faithfully
  compressed into the same nonclassical finite carrier.
- 2026-07-29 — corrected the coefficient hypothesis from a division ring to a field, then
  formalized the sharp kernel bound and all stated corollaries; focused build, axiom audit, and
  repository lint passed.
