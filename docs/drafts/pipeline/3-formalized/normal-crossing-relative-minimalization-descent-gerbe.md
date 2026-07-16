# Normal-crossing derived excess is the obstruction to canonical minimalization descent

- **ID:** `normal-crossing-relative-minimalization-descent-gerbe`
- **Stage:** 3-formalized / needs independent audit
- **Type:** THEOREM / PRESENTATION NO-GO / RELATIVE-MINIMALIZATION CONJECTURE
- **Scientific status:** `[ALGEBRAIC CORE LEAN-FORMALIZED] [CROSS-RANK THEOREM PROVED]`
  `[UNIFIED GERBE CONJECTURAL] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `normal-crossing-derived-critical-excess-phase-law.md`
  - `normal-crossing-exterior-coherence-capacity-law.md`
  - `../1-in-progress/hypertranscendental-conormal-integrability-correspondence.md`
- **Statement:** Arbitrary derived presentation data are nonintrinsic because redundant generators
  manufacture exterior homology without changing the classical constraint.  Minimalization fixes
  this at one source rank but fails to be canonical under rank restriction.  In the normal-crossing
  hierarchy, the differences between the source-labelled minimalizations of one restricted
  gradient generator are exactly the nonzero star Koszul classes; their exterior products are the
  previously proved exponential coherence family.  The natural unified object is therefore the
  homotopy-coherent gerbe of relative minimalizations across source faces, not a single Koszul
  complex and not a quotient by DA functions.

## 1. Arbitrary presentation is impossible `[PROVED; PARENT THEORY]`

Let `a=(a_1,...,a_n)` generate an ideal `I` in a commutative ring.  Adjoin `q` zero generators:

```text
a^+=(a_1,...,a_n,0,...,0).
```

Then

```text
(a^+)=I,                                                  (1)
```

but the new coordinate vectors are `q` independent first relations.  At the Koszul level,

```text
K(a^+) ~= K(a) tensor Lambda(R^q)                         (2)
```

with zero differential on the second factor.  Thus the same ideal and the same `H_0=R/I` admit
presentations with arbitrarily amplified exterior homology.

```text
[NO-GO] The stable category of all source-presented DA objects, without a minimalization or
        stabilization equivalence, is an intrinsic HT invariant.
```

The positive replacement at one local stage is classical: use a minimal generator sequence, or
invert the exterior stabilization `(2)`.  Kirby and Avramov--Iyengar--Miller prove that minimal
generator sequences of one ideal over a local ring have isomorphic Koszul complexes and that a
nonminimal sequence splits as in `(2)`.  This section is `[SEARCH]`, not scientific novelty.

## 2. Normal-crossing excess survives the artifact test `[PROVED + LEAN]`

For

```text
f_N=product_(i=1)^N x_i,
m_i=partial_i f_N=product_(j!=i)x_j,
I_N=(m_1,...,m_N),
```

the gradient presentation is irredundant:

```text
m_i notin (m_j:j!=i).                                    (3)
```

Indeed every `m_j`, `j!=i`, is divisible by `x_i`, so their ideal lies in `(x_i)`, while `m_i`
is not divisible by `x_i`.

Therefore the normal-crossing exterior coherence law is not exterior gauge created by zero or
dependent generators.  Its positive homology belongs to a minimal source presentation.

Lean:

```text
formal/GaloisForLFunctions/HTGeometry/MinimalConstraintPresentation.lean
```

Capstones:

- `presentedIdeal_appendZeroPresentation`;
- `zeroRelationDirection_linearIndependent`;
- `redundantExteriorLabel_count`;
- `cofaceMonomial_not_mem_cofaceOthersIdeal`.

## 3. Rank restriction creates a canonical nonminimal presentation `[PROVED]`

Pass from `N+1` normal-crossing coordinates to `N` by setting the last structural coordinate to
one.  The `N+1` higher-rank gradient components specialize as follows:

```text
m_i^(N+1) |_(x_(N+1)=1) = m_i^N,       1<=i<=N,
m_(N+1)^(N+1) |_(x_(N+1)=1) = f_N.                    (4)
```

Thus a minimal `N+1`-component gradient presentation restricts to the augmented lower-rank
presentation

```text
(m_1^N,...,m_N^N,f_N).                                  (5)
```

The final generator is redundant because

```text
f_N=x_i m_i^N,                                           (6)
```

for every `i`.  Removing it recovers the minimal lower-rank gradient presentation and leaves the
critical ideal unchanged.

Equation `(4)` is direct substitution in the squarefree products.  Equations `(5)`--`(6)` and the
ideal equality are Lean-formalized in

```text
formal/GaloisForLFunctions/HTGeometry/NormalCrossingMinimalizationDescent.lean
```

as `augmentedCofaceIdeal_eq_veroneseIdeal` and
`augmentedCofaceRelation_elimination`.

## 4. Minimalization is noncanonical, and its differences are derived classes `[PROVED + LEAN]`

Let `E_i` be the elimination relation obtained from `(6)`:

```text
E_i=e_terminal-x_i e_i.                                  (7)
```

There are `N` source-labelled eliminations of the same redundant terminal generator.  Fix `E_1`.
For `i>1`,

```text
E_i-E_1=x_1e_1-x_ie_i=-s_i,                              (8)
```

up to the chosen sign convention, where `s_i` is the canonical star cycle of the lower-rank
Koszul complex.  Hence two valid minimalizations of one restricted source presentation differ by
a genuine first derived class.  From `N>=3` onward this difference is not a Koszul boundary.

Lean proves the exact signed identification and nonboundary statement as:

- `cofaceEliminationDifference_zero_succ`;
- `cofaceRelation_eliminationDifference_zero_succ`;
- `cofaceEliminationDifference_not_boundary`.

Combining `(8)` with the exterior coherence theorem gives the cross-rank interpretation

```text
s_(i_1) wedge ... wedge s_(i_p)
  = p-fold coherence among competing source-face minimalizations.       (9)
```

The classes in `(9)` are independent for `1<=p<=N-2`; at least `2^(N-1)-2` positive coherence
classes survive.  The algebraic independence is proved in the parent exterior-capacity card.  The
identification of their entire algebra with the homology of a minimalization nerve remains
conjectural.

## 5. The relative-minimalization gerbe

Let `Face(F)` be the category of finite source faces of a finitely sourced HT system.  For a face
`U`, let

```text
I_U=Ann_DA(q_U)
```

and let `MinKos(I_U)` be the groupoid of minimal cotangent/Koszul presentations of `I_U`.  A face
map `V -> U` base-changes a presentation but may make some generators redundant.  Define

```text
Min_(U,V)
```

to be the derived space of source-compatible eliminations from the restricted presentation to a
minimal presentation on `V`.

The objects `MinKos(I_U)`, transition spaces `Min_(U,V)`, and all higher compatibilities form the
proposed **relative-minimalization gerbe**

```text
M_F over Face(F).                                        (10)
```

It is source-pure: every ideal, face map, and elimination comes from the finite source laws before
an analytic target obstruction is chosen.

```text
[CONJECTURE -- RELATIVE MINIMALIZATION COMPLETENESS]
For every regular finitely sourced HT system, the common obstruction object is the polarized
homotopy limit of M_F coupled to the infinite Kahler--Tate observable packet.  The algebraic
cyclic DA quotient is its H_0 shadow.  Continuation, monodromy, spectral, positivity, and boundary
obstructions are conservative realization functors of this one relative-minimalization object.
```

This is strictly more precise than a generic presentation stack:

1. arbitrary exterior stabilization is quotiented out at each face;
2. the noncanonical *transition between minimal faces* is retained;
3. the normal-crossing hierarchy supplies explicit nonzero transition classes;
4. source restriction, not an invented flow, indexes the object.

## 6. Five obstruction representations

Under the conjecture, the five familiar failures have exact candidate meanings:

```text
continuation failure   = no coherent extension of a minimalization across the source face site;
monodromy              = holonomy of the minimalization groupoid around a face loop;
boundary noncanonicity = multiple components or automorphisms of the homotopy limit;
spectral incompleteness= positive tangent homology of a realized transition complex;
positivity failure     = absence of a real positive self-dual orientation of the same limit.
```

These are not asserted to be equal predicates.  The claim is that they are functorial shadows of
one source-built object, and that a suitable family of realization functors is jointly
conservative.

## 7. Strong no-go and positive statement

The combined theorem separates three levels that were previously conflated:

```text
arbitrary presentation homology = gauge-amplifiable and nonintrinsic;
minimal fixed-rank homology      = intrinsic up to isomorphism but has no canonical transition;
relative minimalization data    = source-restriction coherence and the first viable field object.
```

```text
[POSITIVE THEOREM]
In the normal-crossing HT hierarchies, the first derived excess is exactly the obstruction to
canonical agreement between source-labelled minimalizations after one rank restriction.  It is
not merely a singularity invariant and not merely a relation in the DA quotient.
```

This theorem does not construct the analytic realization or prove the five-way conservativity
conjecture.

## 8. Novelty and anti-theatre gate

Parent theory includes:

- generator-independence of minimal Koszul complexes over local rings;
- exterior splitting for nonminimal generator sequences;
- Koszul homology of perfect and monomial ideals;
- relative perfect complexes and base-change theory;
- orientation data for derived and d-critical loci;
- homotopy limits and gerbes of local choices.

Targeted searches located work on each parent separately, including Kirby's *Isomorphic Koszul
complexes*, Avramov--Iyengar--Miller's explicit minimal/nonminimal splitting lemma, relative
perfect complexes, relative Koszul homological algebra over posets, and Jacobian syzygies.  No
located source identifies normal-crossing star homology with competing minimalizations created by
rank restriction, or uses that transition object as a receiver for HT obstruction realizations.

The raw commutative-algebra statements are `[SEARCH]` or `[BRIDGE]`.  The cross-rank identification
and the HT relative-minimalization object are `[NOVELTY UNVERIFIED]`; priority remains provisional
until a specialist audit of deformation theory, derived critical loci, and special-function
difference modules is complete.

The theorem is paper-significant because it converts static derived excess into a functorial
transition obstruction and removes arbitrary presentation dependence.  It is not Fields-scale by
itself.  Fields-scale content would be the completeness theorem in Section 5 plus construction of
jointly conservative analytic realizations.

## Gates

- [x] prove arbitrary-presentation exterior amplification
- [x] identify the established minimal-Koszul parent theorem
- [x] prove normal-crossing coface irredundance
- [x] prove higher-to-lower rank restriction produces one redundant terminal generator
- [x] construct every source-labelled elimination relation
- [x] identify differences of eliminations with nonzero star classes
- [x] Lean-formalize the algebraic core
- [x] run preliminary exact/equivalent/mechanism literature searches
- [ ] construct the full simplicial minimalization nerve
- [ ] prove its homology is the truncated exterior coherence algebra in the normal-crossing tower
- [ ] construct Barnes and multiple-elliptic-gamma analytic realization functors of the nerve
- [ ] prove two obstruction realizations jointly conservative
- [ ] complete specialist novelty and significance audit

## References checked

- D. Kirby, *Isomorphic Koszul complexes*, Mathematika 20 (1973), 53--58.
- L. L. Avramov, S. B. Iyengar, C. Miller, *Homology over local homomorphisms*, especially the
  minimal/nonminimal Koszul splitting lemma.
- W. Chacholski, A. Guidolin, I. Ren, M. Scolamiero, F. Tombari, *Koszul complexes and relative
  homological algebra of functors over posets*, arXiv:2209.05923.
- A. Dimca, G. Sticlaru, *Syzygies of Jacobian ideals and weighted homogeneous singularities*,
  arXiv:1407.0168.
- B. Hassanzadeh, J. Naeliton, *Residual Intersections are Koszul--Fitting ideals*,
  arXiv:1810.05134.

## Log

- 2026-07-16 -- killed arbitrary presentation homology by exterior stabilization; proved
  normal-crossing irredundance; identified rank restriction as the source of a redundant terminal
  generator; proved that competing eliminations differ by the nontrivial star classes; isolated
  the relative-minimalization gerbe as the repaired unified object.
