# Smooth Stein order-two autonomous-ADE frequency rank

- **ID:** `smooth-stein-order-two-autonomous-ade-frequency-rank`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / CROSS-OPERATOR TRANSDUCTION
- **Scientific status:** `[PAPER-PROVED] [BRIDGE / NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** A compact smooth minimal hull globally realized by a real-holomorphic flow in a
  Stein complex surface has real dimension at most two. Consequently, a globally smooth
  Stein-realizable order-two autonomous-ADE hull has rational Bohr-frequency rank at most two.

## Geometric theorem

Let `S` be a Stein complex surface with complex structure `J`. Let `K subset S` be a compact,
embedded, boundaryless smooth real manifold invariant under a real-holomorphic vector field `X`
defined on a neighbourhood of `K`:

```text
L_X J=0.                                                     (1)
```

Assume that the restricted real flow is minimal on `K`.

`[PAPER-PROVED]` Then

```text
dim_R K<=2.                                                  (2)
```

No orientability or coorientation hypothesis is required.

## 1. A three-dimensional hull has an invariant CR plane field

Suppose first that `dim_R K=3`. Its complex-tangent distribution

```text
H=TK intersect J(TK)                                        (3)
```

has real rank two. Invariance of `K` and `(1)` make `H` flow-invariant. Consider its Frobenius,
equivalently Levi, tensor

```text
L_p : exterior^2 H_p -> T_p K/H_p,
      u wedge v |-> [u,v] mod H_p.                           (4)
```

The zero set of `(4)` is closed and flow-invariant. Minimality therefore leaves exactly two cases:
`L` vanishes everywhere or nowhere.

## 2. The Levi-flat case is impossible in a Stein surface

If `L=0`, the distribution `H` integrates into complex curves. Choose a strictly
plurisubharmonic exhaustion `rho` of `S`. Compactness gives a point at which `rho|K` is maximal.
The complex leaf through that point lies locally inside `K`, so the strictly subharmonic
restriction of `rho` to the leaf has a local maximum. This is impossible.

Thus a compact smooth Levi-flat real hypersurface cannot occur in a Stein surface.

## 3. The contact case makes the minimal flow a Reeb flow

If `L` is nowhere zero, `H` is a contact plane field. Minimality first implies that `X` has no
zero. The tangency set

```text
A={p in K:X_p in H_p}                                       (5)
```

is closed and invariant, so it is empty or all of `K`. If `A=K`, then

```text
H=span_R{X,JX}.                                              (6)
```

But `(1)` gives

```text
[X,JX]=J[X,X]=0,                                             (7)
```

making the plane field in `(6)` integrable, contrary to contactness. Hence `X` is everywhere
transverse to `H`.

There is now a unique global one-form `beta` on `K` with

```text
ker beta=H,       beta(X)=1.                                 (8)
```

The flow preserves both `H` and `X`, so uniqueness in `(8)` gives `L_X beta=0`. Cartan's formula
then yields

```text
i_X d beta=L_X beta-d(beta(X))=0.                            (9)
```

Thus `X` itself is the Reeb field of the contact form `beta`; no time change is used. Taubes's
three-dimensional Weinstein theorem supplies a closed Reeb orbit. That orbit is a nonempty closed
invariant proper subset of the three-manifold `K`, contradicting minimality.

Therefore `dim_R K!=3`.

## 4. Real dimension four is impossible

If `dim_R K=4`, the inclusion of the boundaryless four-manifold `K` into the real four-manifold
underlying `S` is open by invariance of domain. Compactness makes its image closed, so it is a
compact connected component of `S`. A positive-dimensional Stein component cannot be compact; a
strictly plurisubharmonic exhaustion gives the same maximum-principle contradiction. Hence
`dim_R K!=4`, completing `(2)`.

## Order-two autonomous-ADE corollary

Let `f` be a holomorphic uniformly almost-periodic strip function satisfying a minimal autonomous
algebraic differential equation of order two. Assume its Bohr hull `X_f` admits one smooth
translation-equivariant embedding

```text
E:X_f -> S                                                    (10)
```

into a Stein complex surface such that translation is the restriction of a real-holomorphic vector
field near `E(X_f)`. The character rank of the compact connected abelian hull equals its covering
dimension, which here is its manifold dimension. Applying `(2)` gives

```text
rank_Q Gamma(f)<=2.                                         (11)
```

This proves the sharp autonomous frequency/order conjecture for every smooth globally
Stein-realizable order-two hull.

## Exact limitation: singular branch switching remains load-bearing

The current unconditional order-two ADE argument does **not** automatically supply `(10)`. It gives
a finite closed cover

```text
X_f=F_1 union ... union F_m                                  (12)
```

and separate regular-time embeddings of the `F_j` into the affine regular jet surface. Different
pieces may use different times and different implicit branches. The `F_j` can have rough boundary,
and gluing their local complex charts need not produce one Hausdorff Stein surface or one global
holomorphic vector field.

Consequently `(11)` is not the unrestricted order-two theorem. It kills smooth global
realizations; the remaining problem is precisely the singular-chart gluing or transversely rough
protorus case.

## Significance

This is a successful positive residue from the attempted no-go. It excludes all smooth rank-three
and rank-four hull counterexamples in one global affine/Stein phase surface. Any counterexample to
the sharp order-two bound must be genuinely nonsmooth, non-Stein after gluing, or obstructed by
singular branch switching. Ordinary smooth quasiperiodic three-tori are not viable.

## Literature and novelty audit

1. A. Adachi, *On a global estimate of the Diederich--Fornaess index of Levi-flat real
   hypersurfaces*, Publ. RIMS **50** (2014), 727--741,
   <https://doi.org/10.4171/PRIMS/127>. Remark 2.1 records the strictly-plurisubharmonic maximum
   obstruction to compact Levi-flat hypersurfaces in Stein manifolds.

2. C. H. Taubes, *The Seiberg--Witten equations and the Weinstein conjecture*, Geom. Topol.
   **11** (2007), 2117--2202, <https://doi.org/10.2140/gt.2007.11.2117>. This supplies the closed
   Reeb orbit in the contact case.

3. M. Abate, *Iteration theory, compactly divergent sequences and commuting holomorphic maps*,
   Ann. Scuola Norm. Sup. Pisa **18** (1991), 167--191,
   <https://www.numdam.org/item/ASNSP_1991_4_18_2_167_0.pdf>. Proposition 2.16 is the adjacent
   total-reality theorem for a holomorphic torus action on a taut Stein limit manifold.

The theorem is a short synthesis of standard Stein, CR/contact, and Weinstein results. It is
classified as a bridge, not new scientific knowledge.

## Lean status

`[NOT LEAN-FORMALIZED]` The proof requires CR plane fields, the Stein Levi-flat obstruction,
contact/Reeb normalization, the three-dimensional Weinstein theorem, and invariance of domain.
These are not present as reusable project theorems. No hypothesis asserting `dim K<=2` is accepted
as a formalization of `(2)`.

No Lean build or numerical computation was used for this theorem.

## Gates

- [x] exact global geometric hypotheses
- [x] Levi-flat branch excluded
- [x] contact branch reduced to an actual Reeb flow
- [x] dimension-four branch excluded
- [x] order-two ADE corollary stated without suppressing the realization hypothesis
- [x] singular-chart limitation isolated
- [x] conservative literature verdict
- [ ] unconditional Lean formalization

## Log

- 2026-07-17 -- Proved and hostile-audited during the sharp-frequency continuation of research
  programme 2.
