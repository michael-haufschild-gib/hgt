# Coherent cyclotomic descent inside the rational-Witt presentation

- **ID:** `deninger-rational-witt-coherent-cyclotomic-descent`
- **Stage:** 3-formalized
- **Type:** SOURCE DESCENT CONSTRUCTION THEOREM
- **Label:** `DAC_DENINGER_WRAT_COHERENT_CYCLOTOMIC_DESCENT`
- **Parent:** `deninger-square-zero-first-suspension-cross-effect`
- **Scientific status:** `[FORMALIZED] [SOURCE-SPECIFIC NOVELTY; EXTERNAL PRIORITY UNVERIFIED]`
- **Claim:** although the current finite rational-Witt embeddings choose primitive roots
  independently at every modulus, their images inside the common complexified rational-Witt
  presentation canonically induce injective, strictly composable stage transitions.  The finite
  cyclotomic Wrat algebras therefore form an honest directed source system, not merely a family
  of unrelated surjective witness theorems.

## 1. Coherence debt in the current corpus

For a rational prime \(p\) and every \(n>0\) prime to \(p\), the existing construction chooses a
primitive \(n\)-th root
\[
 \zeta_{p,n}\in\overline{\mathbb F}_p^\times
\]
using classical choice and defines an injective root homomorphism
\[
 e_{p,n}:\mathbb Z/n\mathbb Z
   \hookrightarrow \overline{\mathbb F}_p^\times,\qquad
 j\longmapsto \zeta_{p,n}^{\,j}.                               \tag{1}
\]
It then extends `(1)` to the finite cyclotomic group algebra
\[
 \iota_{p,n}:
 \mathbb C[\mathbb Z/n\mathbb Z]
 \hookrightarrow
 \mathbb C[\overline{\mathbb F}_p^\times]
 \cong
 \mathbb C\otimes W_{\rm rat}(\overline{\mathbb F}_p).          \tag{2}
\]

Each map `(2)` is valid, but independently chosen roots do not definitionally satisfy
\[
 \zeta_{p,m}^{m/n}=\zeta_{p,n}
\]
when \(n\mid m\).  Therefore the existing individual finite-stage Wrat witness theorem does not
by itself construct a filtered source object.  This is invisible after fixing one stage and
becomes mandatory for Route L's sheafified source-to-packet restriction.

## 2. Range inclusion theorem

Fix \(n\mid m\), both nonzero and prime to \(p\).  Every element in the image of \(e_{p,n}\) is an
\(n\)-th root of unity, hence an \(m\)-th root:
\[
 x^n=1,\quad n\mid m\quad\Longrightarrow\quad x^m=1.           \tag{3}
\]
Since \(\zeta_{p,m}\) is primitive of order \(m\), its powers enumerate all \(m\)-th roots of
unity in the algebraic closure.  Thus
\[
 \operatorname{range}(e_{p,n})
 \subseteq
 \operatorname{range}(e_{p,m}).                                \tag{4}
\]

Both root maps are injective.  Consequently there is a unique injective group homomorphism
\[
 \tau_{p;n,m}:\mathbb Z/n\mathbb Z
   \hookrightarrow\mathbb Z/m\mathbb Z                         \tag{5}
\]
such that
\[
 \boxed{\quad e_{p,m}\circ\tau_{p;n,m}=e_{p,n}.\quad}           \tag{6}
\]
Explicitly, `(5)` is the inverse of \(e_{p,m}\) on its range, restricted along `(4)`.

## 3. Strict directed-system law

`[PROVED HERE] [DAC_DENINGER_WRAT_COHERENT_CYCLOTOMIC_DESCENT]`

For \(n\mid m\mid r\),
\[
 \tau_{p;m,r}\circ\tau_{p;n,m}
   =\tau_{p;n,r},\qquad
 \tau_{p;n,n}=\operatorname{id}.                               \tag{7}
\]

### Proof

Apply the injective map \(e_{p,r}\) to the two sides of the first identity.  Twice using `(6)`
gives \(e_{p,n}\) on the left, while one use gives \(e_{p,n}\) on the right.  Injectivity of
\(e_{p,r}\) proves equality.  The identity law is the same argument with \(r=n\).  Injectivity of
\(\tau_{p;n,m}\) follows from `(6)` and injectivity of \(e_{p,n}\). \(\square\)

Hence the transition is coherent even though the primitive roots were not chosen coherently.
The common Wrat presentation rigidifies all pairwise choices automatically.

## 4. Group-algebra lift

Extend `(5)` coefficientwise:
\[
 T_{p;n,m}:
 \mathbb C[\mathbb Z/n\mathbb Z]
 \hookrightarrow
 \mathbb C[\mathbb Z/m\mathbb Z],\qquad
 [j]\longmapsto[\tau_{p;n,m}(j)].                              \tag{8}
\]
Then:
\[
\begin{aligned}
 T_{p;m,r}T_{p;n,m}&=T_{p;n,r},\\
 T_{p;n,n}&=\operatorname{id},\\
 \iota_{p,m}T_{p;n,m}&=\iota_{p,n}.                            \tag{9}
\end{aligned}
\]
Every \(T_{p;n,m}\) is injective because `(5)` is injective and group-algebra basis vectors have
distinct supports.

Multiplication by \(p\) commutes with every additive group homomorphism `(5)`:
\[
 \tau_{p;n,m}(pj)=p\,\tau_{p;n,m}(j).                          \tag{10}
\]
Therefore the finite Frobenius endomorphisms commute with `(8)`, and Frobenius-fixed orbit traces
remain fixed under transition.  The directed system lives in the actual common
complexified-rational-Witt presentation and retains arithmetic Frobenius, rather than being an
abstract colimit of vector spaces.

## 5. Strongest positive consequence

The finite Wrat source needed by the tensorized first-suspension cross-effect can now be formed as
the strict filtered union
\[
 \mathscr W_{p,\mathrm{fin}}
 =
 \varinjlim_{(n,p)=1}
   \mathbb C[\mathbb Z/n\mathbb Z]
 \subset
 \mathbb C[\overline{\mathbb F}_p^\times].                     \tag{11}
\]
This closes one precise gap in the prior phrase “contains cofinal finite rational-Witt stages”:
the source stages have actual compatible inclusions in one published Wrat presentation.

The next comparison is not automatic.  Relative to arbitrary primitive-root choices,
\(\tau_{p;n,m}\) may differ from the standard additive index inflation
\[
 j\longmapsto (m/n)j
\]
by a unit automorphism.  Dually, evaluation functions may be permuted by a finite cyclotomic
gauge.  Route L must either:

1. construct a globally compatible primitive-root gauge in which \(\tau\) is standard inflation;
   or
2. prove the packet restriction and tensor cross-effect are natural under the induced gauge.

This is now a finite, explicit descent comparison rather than an undefined sheafification claim.

## 6. Hostile theatre audit

- **Not merely “filtered colimits exist.”**  Equations `(4)`, `(6)`, and `(9)` place every stage
  in the same actual rational-Witt presentation and prove strict compatibility there.
- **Not a canonical-root claim.**  Roots remain noncanonical.  Transition maps are canonical
  relative to the already-fixed embeddings.
- **Not packet descent yet.**  The dual finite quotient transition can carry a unit twist.  The
  analytic packet/Wrat gauge comparison remains open and is stated exactly.
- **Not source selection after seeing a target.**  The transition is forced uniquely by equality
  in the common Wrat presentation before any Meyer or Hodge target is introduced.
- **No RH input.**  Only roots of unity, injective group maps, and group algebras occur.

## 7. Novelty audit

Abstract range-restricted factorization of injective cyclic-group embeddings is elementary.
Claimed new content is its application to repair the exact coherence gap between the repository's
independently chosen finite cyclotomic Wrat embeddings, while preserving arithmetic Frobenius and
producing the strict source system required by the newly exposed Calderón/packet cross-effect.

Repository search found individual finite-stage inclusions, quotient refinement maps, root-index
inflation, and Wrat evaluation surjectivity, but no transition between the Wrat algebras and no
commuting triangle `(9)`.  Primary-source search found Deninger's rational-Witt presentation and
finite correspondence framework, but no statement of this Route L descent system.  External
priority remains provisional pending specialist review.

## 8. Gates

- [x] exact coherence debt isolated
- [x] range inclusion and unique transition proved on paper
- [x] strict composition, injectivity, Wrat inclusion, and Frobenius compatibility proved
- [x] unconditional Lean formalization
- [ ] identify dual packet transition up to finite cyclotomic gauge
- [ ] tensor cross-effect descent through that gauge

## 9. Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/DeningerRationalWittCoherentCyclotomicDescent.lean`.

Formal capstones:

- `deningerPrimeFiniteWittRootEmbedding_range_mono`;
- `deningerPrimeFiniteWittRootTransition_unique`;
- `deningerPrimeFiniteWittRootTransition_comp`;
- `deningerPrimeFiniteCyclotomicWittTransition_injective`;
- `deningerPrimeFiniteCyclotomicWittTransition_comp`;
- `deningerPrimeFiniteCyclotomicWittTransition_frobenius`;
- `deningerPrimeFiniteCyclotomicWittInclusion_transition`;
- `deningerPrimeFiniteCyclotomicWittTransition_unique`;
- `deningerPrimeFiniteCyclotomicWittStageImage_directed`;
- `deningerPrimeFiniteCyclotomicWittSource_mem_iff`.

The last theorem proves that the source supremum is literally the filtered
union of finite stage images, rather than an algebraic closure that silently
adds elements.

Verification:

- `lake env lean GaloisForLFunctions/RHTower/DeningerRationalWittCoherentCyclotomicDescent.lean`
  passes;
- targeted
  `lake build GaloisForLFunctions.RHTower.DeningerRationalWittCoherentCyclotomicDescent`
  passes;
- capstone axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  https://arxiv.org/abs/2508.05329.

## Log

- 2026-08-02 — independent primitive-root choices identified as the first unproved Wrat
  sheaf-descent interface after the cross-effect obstruction.
- 2026-08-02 — common-presentation range factorization constructed; strict cyclotomic Wrat source
  system and Frobenius compatibility proved on paper.
- 2026-08-02 — unconditional Lean formalization completed, including transition uniqueness,
  Frobenius naturality, directed stage images, and exact filtered-union membership.
