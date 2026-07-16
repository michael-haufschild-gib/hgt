# Normal-crossing criticalization has a rank-one exterior base-change defect

- **ID:** `normal-crossing-derived-critical-base-change-defect`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM / DERIVED BASE-CHANGE LAW / UNIFIED-FIELD CONJECTURE
- **Scientific status:** `[GENERATOR-LEVEL SPLITTING LEAN-FORMALIZED] [KOSZUL SPLITTING PROVED]`
  `[DERIVED-GEOMETRY INTERPRETATION IS PARENT THEORY] [HT COMPLETENESS CONJECTURAL]`
  `[NOVELTY UNVERIFIED] [NOT AN RH RESULT]`
- **Parents:**
  - `normal-crossing-relative-minimalization-descent-gerbe.md`
  - `normal-crossing-exterior-coherence-capacity-law.md`
  - `hypertranscendental-algebraic-bulk-completion-boundary.md`
- **Statement:** Derived criticalization does not commute with normal-crossing source-face
  restriction.  Restricting one structural coordinate retains one normal derivative, so the
  base-changed higher critical Koszul object is the lower critical Koszul object tensored with a
  rank-one exterior zero-differential factor.  Source-labelled minimalizations are splittings of
  this canonical base-change defect, and their differences are the already proved star classes.
  The intrinsic candidate unified object is therefore the polarized bifiltered
  source/critical diagram before totalization, not the groupoid of presentations and not any
  one-parameter total complex.

## 1. The exact base-change defect `[PROVED]`

Let

```text
R_N=F[x_1,...,x_N],
f_N=product_(i=1)^N x_i,
m_i^N=partial_i f_N,
K_N=K(m_1^N,...,m_N^N;R_N).
```

Embed the rank-`N` source face in rank `N+1` by `x_(N+1)=1`.  Restricting the higher gradient gives

```text
(m_1^(N+1),...,m_(N+1)^(N+1))|_(x_(N+1)=1)
  =(m_1^N,...,m_N^N,f_N).                                (1)
```

The final term in `(1)` is the derivative normal to the face.  It is absent from the intrinsic
gradient of the restricted function `f_N`, but it is classically redundant because

```text
f_N=x_i m_i^N                                              (2)
```

for every `i`.  Fix `i` and change the terminal Koszul basis by

```text
eta_i=e_terminal-x_i e_i.                                  (3)
```

Then `d eta_i=0`, and the change of basis is invertible.  Therefore

```text
K(m_1^N,...,m_N^N,f_N)
  ~= K(m_1^N,...,m_N^N,0)
  ~= K_N tensor Lambda_R_N(R_N eta_i),    d eta_i=0.        (4)
```

Consequently the derived pullback of the rank-`N+1` critical locus is not the rank-`N` critical
locus.  It is its rank-one exterior excess extension.  In particular,

```text
H_p(restricted K_(N+1))
  ~= H_p(K_N) directSum H_(p-1)(K_N) eta_i.                (5)
```

The isomorphism `(4)` is noncanonical as a displayed splitting, but the derived base-change
object and its excess line are canonical.  Choosing another factorization in `(2)` changes the
splitting, not the defect.

## 2. Minimalization classes are transition functions `[PROVED + LEAN]`

For two source directions `i,k`, the corresponding closed excess generators satisfy

```text
eta_i-eta_k=x_k e_k-x_i e_i.                              (6)
```

Relative to one base direction, `(6)` is exactly the normal-crossing star syzygy.  From three
lower-rank coordinates onward it is not a Koszul boundary.  Thus the earlier
relative-minimalization gerbe is not the invariant itself: it is an atlas of splittings of the
canonical exterior excess line, and the star classes are its transition functions.

This is the strong positive successor to the presentation no-go:

```text
[POSITIVE THEOREM]
The first normal-crossing derived excess is the transition class between splittings of the
rank-one critical base-change defect.  It survives arbitrary-presentation gauge because the
lower gradient is irredundant and because the defect is defined by source restriction.
```

Lean formalizes:

- the augmented restricted presentation and every elimination in
  `formal/GaloisForLFunctions/HTGeometry/NormalCrossingMinimalizationDescent.lean`;
- the invertible presentation untwisting, equality of relation maps, and identification of each
  elimination with the terminal zero direction in
  `formal/GaloisForLFunctions/HTGeometry/NormalCrossingCriticalBaseChange.lean`.

Capstones:

- `cofacePresentationUntwist`;
- `splitAugmentedCofaceRelation_untwist`;
- `cofacePresentationUntwist_elimination`;
- `splitAugmentedCofaceRelation_terminal_zero`;
- `cofaceEliminationDifference_not_boundary`.

The exterior-algebra lift of an invertible generator change is standard Koszul functoriality and
is proved on paper in `(3)`--`(4)`; the current Lean certificate stops at the exact generator and
relation maps rather than introducing a second local Koszul-complex library.

## 3. Higher-codimension face law `[PROVED]`

Restrict `q` structural coordinates of `f_(N+q)` to one.  The restricted gradient consists of

```text
(m_1^N,...,m_N^N, f_N,...,f_N),                           (7)
```

with `q` copies of the normal derivative `f_N`.  Applying `(3)` independently to the `q` terminal
generators gives

```text
K_(N+q)|_(q-face) ~= K_N tensor Lambda_R_N(E_q),
rank(E_q)=q,             d|_(E_q)=0.                      (8)
```

Hence a codimension-`q` source face carries exact exterior base-change capacity `2^q`, and its
branching law is Pascal:

```text
H_p(q+1) ~= H_p(q) directSum H_(p-1)(q).                 (9)
```

This is derived excess-intersection theory in an explicit source hierarchy, not a new general
theorem of derived algebraic geometry.  Its role is to identify which canonical object the HT
source data realize.

## 4. Diagonal purity of the normal-crossing chart `[PROVED + LEAN]`

The coefficient of a `p`-fold source-labelled splitting coherence is the squarefree monomial

```text
x_J=product_(j in J)x_j,          |J|=p.                 (10)
```

Therefore its polynomial degree equals its coherence depth:

```text
totalDegree(x_J)=|J|.                                    (11)
```

Lean proves `(11)` for every finite `J` as
`relativeMinimalizationCoherenceCoefficient_totalDegree`, and proves that the distinguished
degree-two star-wedge coefficient has total degree two as
`cofaceStarWedge_distinguished_totalDegree`.

Equation `(11)` gives a genuine bifiltration: internal critical homological degree and structural
source degree agree on the normal-crossing exterior chart.  The equality is a bridge theorem, not
by itself a novelty claim.  Its possible significance is that it supplies a natural purity axis
for a future polarization of the totalized object.

## 5. The derived-critical descent field

Let `Face(F)` be the category of finite source faces of a finitely sourced analytic HT system.
For a face `U`, let

```text
Crit_DA(U)
```

be the derived critical object of its DA-relative source law.  For a face map `V -> U`, compare

```text
L res_(U,V)^* Crit_DA(U)   and   Crit_DA(V).              (12)
```

Their homotopy fiber/cofiber is the **critical base-change defect** `E_(U,V)`.  Higher face chains
give the coherence maps among these defects.  The resulting cosimplicial stable object has two
independent gradings:

```text
p = internal critical/Koszul degree,
q = source-descent/face degree.                           (13)
```

Define provisionally the **derived-critical constraint-Hodge object**

```text
CH(F)=Rees_(p,q)(U |-> Crit_DA(U), E_(U,V)),               (14)
```

where the rank-two Rees notation means that the internal and source filtrations remain separate.
Direct-sum, direct-product, Tate, and weighted scalar totalizations are realization functors of
`CH(F)`, not its definition.  No additive scalar grading `N^2 -> N` is injective, so none of those
one-parameter receivers can be conservative on an unbounded object by itself.  This no-go is
Lean-formalized in `BifilteredScalarizationNoGo.lean`.  Its positive successor is exact: the two
nonparallel views `(p+q,p+2q)` are jointly injective, so two transverse scalar realization chains
recover the complete bidegree even though either chain alone loses it, provided a comparison map
pairs their observations of the same class.  Separate marginal spectra still admit an explicit
two-packet ambiguity, also formalized in that file.  The normal-crossing bidegree multiplicities,
constraint cone, duality, and `3^N` total labelled capacity are Lean-formalized in
`NormalCrossingConstraintHodgeDiamond.lean` and developed conceptually in
`../1-in-progress/hypertranscendental-constraint-hodge-duality.md`.

The full object is equipped with shifted-symplectic duality, source normalization, analytic
completion data, and signed Hermitian polarization.

This gives a precise five-way dictionary:

```text
continuation failure    = failure of descent/effectivity in q;
monodromy               = holonomy of the face comparison diagram;
spectral incompleteness = surviving internal cohomology in p;
boundary noncanonicity  = inequivalent completions or totalizations of the bifiltration;
positivity failure      = absence of a positive real polarization compatible with bidegree duality.
```

These are not declared equivalent predicates.  They are candidate realization functors or
spectral sequences of one bifiltered object.

```text
[CONJECTURE -- HT CONSTRAINT-HODGE COMPLETENESS]
For every regular finitely sourced analytic hypertranscendental system, the polarized
derived-critical constraint-Hodge object CH(F) is source-faithful, and its natural analytic,
monodromic, spectral, Hermitian, boundary, and scalar-totalization realization functors are jointly
conservative.
Every persistent reconstruction obstruction is a differential, extension, totalization defect,
or polarization defect of this one object.
```

The conjecture is falsified by either:

1. two analytically inequivalent HT sources with equivalent polarized `CH` objects; or
2. a source-natural persistent obstruction invisible to every layer of `(12)`--`(14)`.

For zeta, only as a downstream hypothesis, the critical zeros would be the self-dual degeneracy
spectrum common to conservative realizations of `CH(zeta)`.  No construction or result here
identifies that spectrum or proves any statement about RH.

## 6. Novelty and anti-theatre gate

The following are established parent theory:

- Koszul models of derived zero and critical loci;
- canonical `(-1)`-shifted symplectic structures on derived critical loci;
- exterior excess bundles and formality/base-change results for derived intersections;
- relative derived critical loci and Lagrangian-correspondence composition;
- the splitting of a Koszul complex after adjoining a redundant generator.

Therefore `(4)`, `(5)`, and `(8)` are not claimed as new general derived geometry.  The
relative-minimalization gerbe has been demoted from proposed fundamental object to a splitting
atlas of the base-change defect.

The candidate new residue is the conjunction:

```text
normal-crossing source restriction
  -> explicit critical base-change exterior defect
  -> star homology as transition between source-labelled splittings
  -> the same defect in independent HT special-function hierarchies
  -> a polarized constraint-Hodge object whose scalar totalizations are provably nonfaithful
     separately but conjecturally jointly conservative with the other realizations.          (15)
```

Searches located no source applying the derived-critical base-change defect in `(15)` to
hypertranscendental difference hierarchies, nor a theorem that the five analytic obstruction
types are jointly conservative realizations of `(14)`.  This is still `[NOVELTY UNVERIFIED]`:
absence from targeted search is not a priority result.

The proved normal-crossing theorem is paper-significant structural evidence, but not a
Fields-scale discovery alone.  Fields-scale promotion requires construction of `(14)` for a
nontrivial analytic HT class and a proof of source faithfulness or joint conservativity.

## References checked

- G. Vezzosi, *Derived critical loci I -- Basics*, arXiv:1109.5213.
- T. Pantev, B. Toen, M. Vaquie, G. Vezzosi, *Shifted Symplectic Structures*,
  arXiv:1111.3209.
- D. Arinkin, A. Caldararu, M. Hablicsek, *Formality of derived intersections and the orbifold
  HKR isomorphism*, arXiv:1412.5233.
- A. A. Khan, *Virtual excess intersection theory*, arXiv:1909.13829.
- M. Anel, D. Calaque, *Shifted symplectic reduction of derived critical loci*,
  arXiv:2106.06625.

## Gates

- [x] prove one-face generator-level base-change splitting
- [x] identify every source-labelled elimination with the common zero direction
- [x] recover star classes as changes of splitting
- [x] prove the `q`-face exterior splitting on paper
- [x] formalize the diagonal purity coefficient law
- [x] collide the claim with derived critical/excess-intersection parent theory
- [x] demote the presentation gerbe to a coordinate atlas
- [ ] formalize the full Koszul DGA splitting rather than its generator-level certificate
- [ ] construct the source-face cosimplicial derived critical object
- [x] prove that no scalar additive totalization can retain the full bifiltration
- [x] formalize the exact normal-crossing constraint diamond and its exterior duality
- [ ] construct its polarized constraint-Hodge object for one analytic HT hierarchy
- [ ] prove one nontrivial pair of realization functors jointly conservative
- [ ] complete specialist novelty and significance audit

## Log

- 2026-07-16 -- proved and Lean-formalized the invertible critical base-change presentation
  splitting; identified minimalizations as splitting charts; proved the higher-face exterior law
  and diagonal purity; replaced the gerbe conjecture by the intrinsic derived-critical descent
  field and ran the first derived-geometry collision audit.
