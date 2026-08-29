# Thermodynamic divisor charge is a finite ancestor or a nonliftable boundary index

- **ID:** `thermodynamic-divisor-charge-finite-ancestor-or-boundary-index`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE OPERATOR-ALGEBRAIC CARRIER CLASSIFICATION
- **Scientific status:** `[PROVED; BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** positive successor to `finite-prime-af-topological-charge-no-nucleation`; separate from
  RHTower Routes A--D
- **Statement:** A nonzero divisor winding in a finite-prime thermodynamic model must either descend
  from a nonzero finite-stage winding, or be carried by a source-defined quotient symbol that fails
  to lift and has nonzero K-theory boundary index. The missing object is therefore a finite ancestor
  or a boundary anomaly, not a charge created inside a regular bulk limit.

## 1. Finite-ancestor carrier

Let

```text
A_N=M_(D_N)(C),
A_(N+1)=A_N tensor M_(d_(N+1))(C),
d_(N+1)>0.                                                     (1)
```

Let `U_N` be an invertible matrix loop over a spectral contour. Independent prime enlargement is

```text
U_(N+1)=U_N tensor I_(d_(N+1)).                               (2)
```

Write `q_N=wind(det U_N)`. The formalized determinant and winding laws give

```text
q_(N+1)=d_(N+1) q_N.                                          (3)
```

Therefore

```text
q_(N+1)!=0  =>  q_N!=0.                                       (4)
```

Iterating `(4)` proves the positive finite-ancestor theorem:

```text
every nonzero charge in an independently enlarged finite system
has a nonzero charge at every earlier positive-dimensional stage.             (5)
```

For the AF norm limit, K-theory continuity strengthens `(5)`: every class in
`K_1(C(S^1) tensor A)` is represented at some finite stage. Thus a regular quasi-local divisor
charge is not emergent in the sense of having no finite representative; it is the continuation of a
finite source charge.

## 2. Boundary-index carrier

Suppose instead that the infinite-volume completion is singular and is represented by a unital
C-star extension

```text
0 -> J -> E --pi--> Q -> 0.                                  (6)
```

The six-term exact sequence contains

```text
K_1(E) --pi_*--> K_1(Q) --partial--> K_0(J).                  (7)
```

`[PROVED]` For every quotient symbol class `[u] in K_1(Q)`,

```text
partial[u]!=0
  iff
[u] is not in image(pi_*).                                    (8)
```

### Proof

Exactness at `K_1(Q)` says

```text
ker(partial)=image(pi_*).                                     (9)
```

Hence `partial[u]=0` exactly when `[u]` lies in the image. Negating both sides gives `(8)`. QED.

Equation `(8)` is constructive. A nonzero thermodynamic charge with no finite bulk ancestor must
be represented by a quotient unitary that has no invertible lift to the completed bulk algebra.
Its integer is not assigned separately; it is the obstruction to lifting.

## 3. Exact Xi carrier specification

Let `Gamma` be a zero-avoiding contour and let

```text
m_Gamma(Xi)=sum_(rho inside Gamma) ord_rho(Xi).                (10)
```

An operator-algebraic source construction crosses the divisor wall if it produces, without using
the Xi zeros, an extension `(6)`, a distinguished positive generator `[e] in K_0(J)`, and a quotient
symbol `u_Gamma` satisfying

```text
partial[u_Gamma]=m_Gamma(Xi) [e].                             (11)
```

This is the positive target forced by the preceding theorems.

The requirements are now explicit:

1. **Source selection:** `E`, `J`, and `u_Gamma` are constructed from completed Euler--Gamma data,
   not from the Xi divisor or a zero list.
2. **Nonliftability:** `[u_Gamma]` has no bulk lift; this must be proved, not declared.
3. **Index identity:** the connecting class equals `(10)` with multiplicity.
4. **Contour functoriality:** nested contours give additive charges and shrinking contours recover
   local multiplicity.
5. **Reflection polarization:** the source involution acts on the index so that off-line pairs are
   distinguished from critical-line fixed points.

If `(11)` is established and the reflection action forces the boundary class to be supported only
on fixed contours, RH follows. The hard theorem is therefore not “there is an index”; it is the
source derivation and polarization of this exact boundary symbol.

## 4. Corpus reconciliation

The positive specification `(11)` is not a previously absent project target. The research corpus
already supplies almost every categorical component:

| Positive requirement | Existing theorem or construction | Exact status |
|---|---|---|
| finite Euler--Gamma bulk has no divisor charge | `weld-tower-free.md` | formalized coherent root tower; all finite welds are monodromy-free |
| regular finite-unit quotient is only the divisor | `prime-euler-unit-tangent-completeness.md` | candidate-new paper theorem; finite Euler-unit tangents are complete |
| a connecting homomorphism reaches deck charges | `weld-charge-connecting-map.md` | formalized; every abstract deck charge is realized by an explicit weld cohomology class |
| a nonliftable algebraic boundary carrier exists | `mplus-torsion-seam-extension.md` | formalized torsion presentation, Fitting boundary, and coefficient/nonmembership witness |
| finite source member carries exact Xi multiplicity | `sem-integral-fitting-charge.md` | formalized attached integral defect reads `ord_rho(Xi)` at every modulus |
| evident unit and phase symbols lift | `marcinkiewicz-tail-residue-yoneda-splitting.md` | paper theorem; their K-theory boundary is zero |
| canonical singular residue pairing classified | `singular-corona-residue-incidence-trilemma.md` | paper theorem; it is zero, RH-equivalent, or loses quantization |
| all prime-grade monodromy retains exactly the divisor | `prime-grade-monodromy-divisor-mobius-equivalence.md` | paper theorem; faithful divisor coordinates, no joint incidence |

The corpus therefore already proves the positive architectural statement:

```text
a successful charge must be an integral, nonliftable,
determinant-transverse seam boundary retained before scalar extension.          (12)
```

The exact missing theorem is narrower:

```text
actual completed arithmetic/analytic seam defect
  -> presentation-invariant integral boundary
  = attached SEM multiplicity model,                              (13)
```

with the first arrow constructed without a zero list or divisor-fed carrier. After `(13)`, a
source law must force the reflected boundary support onto the fixed line without merely re-reading
multiplicity.

Thus the AF/topological-phase pivot does not open a new project route. It independently lands on the
same torsion-seam boundary already isolated by the corpus. Under the mandate to explore far from
existing RH routes, `(13)` should not be pursued in this lane.

## 5. Symbols already excluded

The evident symbols do not satisfy the positive specification.

- The quotient unit `[1_Q]` lifts to `[1_E]`, so `partial[1_Q]=0`.
- A bounded prime phase already present as a unitary in `E` lifts, so its boundary class is zero.
- A finite Euler--Gamma unit has a coherent bulk root tower and zero divisor winding.
- The canonical prime-tail residue graph is closable exactly on RH and is then zero; it is not an
  unconditional closed source cycle.

Thus `u_Gamma` must be a genuinely joint source--completion symbol whose failure to lift is created
by the infinite weld. It cannot be the unit, a phase orbit, or a renamed zero residue.

## 6. Physical reading

In topological-matter language, `(11)` is a bulk--boundary correspondence:

```text
finite prime bulk data
  -> singular infinite-volume boundary symbol
  -> nonliftability index
  -> divisor multiplicity.                                   (14)
```

The “external clock” is optional in this formulation. If a crossed product by a clock action is
used to construct `E`, the clock earns its role only by producing the nonliftable symbol and index
identity `(11)`. Merely adding time or modular flow supplies no charge.

For a state-sector rather than an extension model, the analogous positive requirement is a
source-selected infinite-volume GNS sector not quasi-equivalent to the finite vacuum sector, with a
sector index satisfying the same contour additivity as `(10)`. This is a separate carrier category,
not a counterexample to the AF theorem.

## 7. RH verdict

The result does not prove RH, but it replaces the no-go with an exact construction problem:

```text
Build u_Gamma from the completed source,
prove it does not lift,
compute its boundary index,
prove the reflection-polarized support is the critical line.  (15)
```

A successful operator-algebraic pivot must deliver `(13)`. Any finite or thermodynamic theorem
that produces only a zero bulk charge has not yet constructed the required object.

## 8. Lean surface

`formal/GaloisForLFunctions/RHTower/PrimeQuasiLocalCharge.lean` proves the finite positive
implication

```text
PrimeQuasiLocalCharge.nonzero_winding_has_finiteAncestor,
```

from the actual Kronecker determinant and integer winding APIs.

`formal/GaloisForLFunctions/RHTower/ThermodynamicBoundaryIndexCarrier.lean` proves the
boundary-index half unconditionally. The exact segment `E -> Q -> J` of the six-term sequence is
recorded as a structure carrying only exactness at the middle term, `boundary.ker = lift.range`;
every theorem below is derived from that single equation and nothing else. No K-theory axiom,
`sorry`, `admit`, `opaque`, or `unsafe` declaration is used, and `#print axioms` on each theorem
reports exactly `propext`, `Classical.choice`, `Quot.sound`.

| Card statement | Lean theorem |
|---|---|
| `(8)`, `partial[u] != 0 iff [u] not in image(pi_*)` | `ThermodynamicBoundaryIndex.ExactSegment.boundary_ne_zero_iff_not_mem_liftRange` |
| complementary form: zero boundary iff liftable | `ThermodynamicBoundaryIndex.ExactSegment.boundary_eq_zero_iff_mem_liftRange` |
| section 5, every lifted symbol has zero boundary | `ThermodynamicBoundaryIndex.ExactSegment.boundary_lift` |
| sections 1-2 dichotomy: a regular completion carries no boundary charge | `ThermodynamicBoundaryIndex.ExactSegment.lift_surjective_iff_boundary_trivial` |
| a nonzero index forces a genuinely singular completion | `ThermodynamicBoundaryIndex.ExactSegment.not_surjective_lift_of_boundary_ne_zero` |
| the index is a complete invariant of the nonliftable class | `ThermodynamicBoundaryIndex.ExactSegment.quotientLiftRangeEquivBoundaryRange` |
| two symbols share an index iff they differ by a liftable symbol | `ThermodynamicBoundaryIndex.ExactSegment.boundary_eq_iff_sub_mem_liftRange` |
| `(11)` index identity forces nonliftability | `ThermodynamicBoundaryIndex.multiplicity_ne_zero_iff_not_mem_liftRange` |
| the multiplicity is uniquely determined | `ThermodynamicBoundaryIndex.index_unique` |
| section 3.4 contour additivity of charges | `ThermodynamicBoundaryIndex.HasIndex.add` |
| a liftable contour symbol has multiplicity zero | `ThermodynamicBoundaryIndex.HasIndex.eq_zero_of_mem_liftRange` |

The remaining external input is the existence of the six-term sequence for a C*-extension. It is
imported parent theory and is *not* encoded as a Lean hypothesis of any theorem above: each theorem
quantifies over an arbitrary exact segment of abelian groups, which is exactly the hypothesis its
paper proof uses.

## 9. Parent boundary

The finite-ancestor statement is the parameterized form of continuity of operator K-theory for AF
inductive limits. The boundary carrier theorem is exactness of the six-term K-theory sequence.
Both are standard parent theory; the carrier specification `(11)` is a project research target, not
a proved new mechanism. Accordingly this card is a positive bridge rather than new scientific
knowledge.

## Gates

- [x] every regular nonzero charge assigned a finite ancestor
- [x] every singular extension charge assigned a nonliftable quotient carrier
- [x] boundary nonzero iff lift obstruction proved
- [x] exact Xi index specification stated
- [x] reconciled against existing formal weld, torsion-seam, SEM, and corona surfaces
- [x] lifted unit and phase symbols excluded
- [x] finite positive theorem formalized in Lean
- [x] boundary-index equivalence, index identity, uniqueness, and contour additivity formalized
- [x] standard-axiom audit on every new theorem
- [ ] construct `u_Gamma` from the completed source without divisor input
- [ ] prove the reflection-polarized support theorem

## Log

- 2026-08-29 -- formalized `(8)`, the regular/singular dichotomy, the complete-invariant quotient
  isomorphism, the `(11)` index identity with uniqueness, and contour additivity in
  `RHTower/ThermodynamicBoundaryIndexCarrier.lean`; module builds and passes the standard-axiom
  audit.  Card promoted to `3-formalized`.
