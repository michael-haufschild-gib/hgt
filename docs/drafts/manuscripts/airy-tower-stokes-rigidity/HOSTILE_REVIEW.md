# Final hostile referee report

Manuscript: *Formal-contact covariance, zero-loop rigidity and exact recognition for ramified
nonabelian Hodge diagrams*

Date: 2026-08-03

Review type: internal red-team review, not an external journal report.

Target bar: renowned general mathematics journal in the Compositio/IMRN/Advances range. No
Annals/Inventiones-level claim is made.

## Recommendation

**Pass: publishable at the stated target bar after ordinary external peer review.**

No correctness gap, semantic formalization gap, located priority collision, or material overclaim
remains. The universal covariance theorem is elementary by itself; the publication case rests on
the package it organizes: a strict sign theorem, exact zero-loop classification, arithmetic and
Fourier consequences, strict contact tomography, an additive negative-type tree metric, exact
two-circle spectra, finite decorated fibres, and a necessary-and-sufficient arbitrary-size
recognition theorem with explicit simultaneous Puiseux reconstruction.

The strongest new result is Theorem 9.1. The most conceptually useful result is the covariance
principle joining tangent coordinate changes, contact thresholds, and the negative Airy Fourier
chart. The manuscript correctly avoids presenting the elementary valuation lemma alone as the
publication-level discovery.

## Publication-blocking attacks applied

### 1. “Universal law” could be a renamed tautology

Tangent substitution preserves Laurent valuation because it sends the uniformizer to a
uniformizer times a unit. Applying the same fact to `f-g` preserves contact. This observation is
standard in spirit and cannot carry the paper.

The manuscript survives this objection for two reasons. First, it states and proves the exact
automorphism, including the `E`th root and inverse, and then proves invariance of every threshold
partition rather than merely one valuation. Second, it identifies the reciprocal negative-Fourier
coordinate

```text
t^E u(t)^(-1) = phi(t^E)
```

and couples it to an actual Weyl-algebra Fourier identity. The law is therefore an organizing
mechanism for genuinely new rigidity and recognition theorems, not a novelty claim detached from
them.

**Verdict:** acceptable framing. The conclusion’s word “shadows” is interpretive synthesis; each
mathematical component is separately proved.

### 2. Galois-sheet formulas might be copied inputs disguised as new work

The loop and edge formulas are known and are cited as such. The manuscript’s source propositions
derive their coarea form from cyclic stabilizers and from the kernel of the difference map on two
cyclic sheet groups. No new correspondence theorem is claimed.

Internal verification uses genuine complex roots of unity, finite Puiseux polynomials, cyclic
translation actions, stabilizer cardinalities, ordered sheet pairs, and the exact common-pair
kernel. The source is not a natural-number record with the desired answer stored in a field.

**Verdict:** source chain is honest; novelty begins at strictness, equality cases, and global
reconstruction.

### 3. The first-deviation sign law might fail through the tail

Let the first gcd drop be `R -> E` and first numerator be `beta`. The gcd hypothesis excludes the
open arithmetic region around `R+E`:

```text
beta < R+E  =>  beta <= R-E,
beta > R+E  =>  beta >= R+2E.
```

On the low branch, the strict tail estimate keeps the full weighted sum below `R^2-1`. On the high
branch, the first summand already exceeds `R^2-1`. At `beta=R+E`, the contribution is exactly
`R^2-E^2`, leaving the identical tail problem at ramification `E`. Induction gives the sign of the
first noncanonical level.

Inconsequential coefficients do not lower the gcd and do not enter the loop formula; the paper
explicitly classifies level data rather than all polynomial representatives.

**Verdict:** correct and sharp.

### 4. Divisor-chain and enumeration claims might confuse ordered data

At zero loop, every numerator is forced to be `e_(i-1)+e_i`. Conversely, any strict divisor chain
produces decreasing numerators with the required gcd. The quotients `a_i=e_(i-1)/e_i` form an
ordered factorization, and tail products recover the chain. Thus the correspondence is bijective,
not a counting analogy.

For `p^k`, ordered factorizations are compositions of `k`, giving `2^(k-1)`. For squarefree `r`,
they are ordered set partitions of the prime factors, giving the ordered Bell number.

**Verdict:** exact.

### 5. Fourier resolution could be arithmetic relabelling

The development constructs the free noncommutative operator algebra, its polynomial
multiplication/differentiation semantics, the Weyl quotient by `DX-XD-1`, the descended Fourier
automorphism `X -> D`, `D -> -X`, its fourth-power identity, and polynomial gauge automorphisms.
It proves

```text
F(D^R-X^E)=(-X)^R-D^E.
```

Independently, the Laurent chart proves the reciprocal transformed coordinate has order `E` and is
tangent-conjugate to `t^E`, with full contact-hierarchy preservation. The finite resolution applies
this exact package at every successive characteristic tail and records the strictly decreasing
rank trace ending at one.

The paper does not claim a general analytic Fourier equivalence for arbitrary meromorphic
connections, nor that the displayed generalized-Airy operator contains every lower Stokes
coefficient. Its stated zero-loop Airy resolution is exactly the proved operator/Laurent package.

**Verdict:** no arithmetic-certificate theatre and no analytic overclaim.

### 6. Strict tomography and energy might be generic tree facts with no Stokes content

Tree-metric four-point and negative-type statements are indeed general once a strictly increasing
contact coordinate is available. The Stokes content is the strict complementary-contact formula:
positive reciprocal ramification makes every genuine continuation and nested fission event
strict. This shows the decorated core retains the multi-leaf branching hierarchy even while losing
unary, height, ramification-profile, and sibling-type information.

The energy identity then polarizes the same core contact matrix. Positive cut lengths are
constructed from the rooted contact tree; they are not supplied as a certificate. The strict
negative-type proof uses pendant cuts to separate every nonzero zero-sum vector.

**Verdict:** appropriate division between Stokes theorem and tree consequence.

### 7. Exact pair spectrum might omit contact mechanisms

All nine oriented mechanisms are exhausted:

- two unramified circles;
- unramified/ramified base and high cases in both orientations;
- unequal-ramification base and high cases;
- equal-ramification low and high cases.

High integral difference gives positive multiples of `rs`. Unequal mandatory levels give
`max(r,s)`. Equal mandatory coefficients in distinct root-of-unity orbits give `r`; aligned
mandatory terms followed by a lower difference give every value `0,...,r-1`. Together this yields
the displayed exact spectra, including mixed and unramified cases.

**Verdict:** exhaustive and constructive. The missing edge `3` for two ramification-two vertices
is a genuine two-vertex obstruction invisible to ultrametricity.

### 8. Decorated finite-fibre theorem could be a finite-subtype tautology

This objection was taken seriously. Finiteness is established before applying compatibility:

1. fixed diagonal entry and ramification fix a weighted sum `W_i`;
2. every local characteristic numerator is bounded by `W_i`, and the exact characteristic type is
   finite;
3. for each pair and discrete prefix/sibling case, the affine equation is

   ```text
   B_ij + r_i r_j = C + s_d g,
   ```

   with `g>0` dividing `r_j`;
4. hence `C`, `g`, and `s_d` are bounded, and fixed `(C,g)` determines at most one `s_d`;
5. complete local and pair codes are finite; imposing all fission compatibility axioms takes a
   subtype and cannot enlarge the fibre.

The signed-diagonal case is not silently coerced to natural numbers. A separate signed diagram
type retains `B_ii` in `ℤ`, proves that `W_i<0` makes the fibre empty, and injects every nonempty
signed local characteristic into the finite type at `W_i.toNat`.

The manuscript defines the canonical full-data presentation being counted and explicitly excludes
arbitrary inconsequential polynomial support. It does not count analytic representatives.

**Verdict:** genuine finite encoding, not “finite because assumed finite.”

### 9. Recognition sufficiency might assemble incompatible pairwise choices

This was the main semantic risk. The proof now uses one global stage set and one coefficient family,
not independently chosen pair witnesses. Strict-threshold classes are equivalence classes by the
acute-isosceles law. Positive integer complex coefficients distinguish their child clusters.

The exact pair spectrum selects a highest separating stage for each pair. Equal rational exponents
are collected into actual finite Puiseux polynomials. Exponent collisions cannot cancel the
selected difference: high, mandatory, and lower ranges are separated, while equality within a
range forces equality of stage indices.

The internal theorem was strengthened after hostile review in two noncosmetic ways:

- every output polynomial has proved elementary support, and a ramified polynomial has a proved
  nonzero mandatory Airy monomial after coefficient collection;
- the capstone no longer returns a bare highest exponent or an auxiliary stage assertion. It
  returns an actual highest difference exponent `e` together with a stage-free relation recovering
  the prescribed `B_ij` directly from `e`, `r_i`, and `r_j` by the three geometric edge formulas.

Thus the theorem cannot succeed by hiding the desired edge in a constructor field.

**Verdict:** simultaneous sufficiency is dependency-closed and materially new.

### 10. Complexity claim might be inflated

The claimed schedule is exhaustive and unit-cost: all ordered pairs and ordered triples. Its exact
cardinality is `n^2+n^3`, bounded by `2n^3` for `n>0`. No bit-complexity or optimized-algorithm
claim is made.

**Verdict:** exact within its stated model.

## Internal proof audit

The following current modules passed direct `lake env lean <file>` checks and targeted module
builds:

- `ElementaryStokesGlobalPuiseuxRealization`
- `ElementaryStokesRecognitionComplexity`
- `StokesDecoratedFiniteFiber`
- `StokesSignedDecoratedFiniteFiber`
- `StokesNegativeFourierResolution`
- `AiryTowerExamples`
- `FiniteContactDendrogram`

All are wired into the `HTGeometry` umbrella. The strengthened realization and recognition
modules were rebuilt after the final semantic changes.

`/tmp/hgt_stokes_final_axioms.lean` audits the principal capstones. Each depends only on standard
foundations (`propext`, `Classical.choice`, `Quot.sound`); no project axiom appears. Source lint
finds no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration in the paper modules.

Repository-wide lint currently exits nonzero solely because unrelated concurrently added
`RHTower` modules have not yet been imported by their own umbrella. It reports no Stokes module
error. This shared-repository integration defect is not evidence against the paper, but it must not
be misreported as a global green gate.

The manuscript itself contains no mention of Lean, proof assistants, formal verification,
toolchains, or internal declaration names. Verification is private quality control only.

## Novelty audit

Primary sources checked through 2026-08-03 include Biquard--Boalch, Hiroe,
Boalch--Yamakawa, Boalch--Douçot--Rembado, Boalch’s untwisted counting paper, Douçot’s twisted-graph
and enriched-tree papers, and Douçot’s 2026 Fourier/Argyres--Douglas paper.

Known inputs are separated from new conclusions:

- loop and edge formulas are known;
- rescaled ultrametric necessity is known;
- fission-tree realization/classification is known;
- the local Fourier congruence criterion is known;
- no source located the first-deviation sign law, zero-loop equality classification, ordered
  factorization bijection, exact ramified pair spectra, decorated finite-fibre theorem, strict core
  tomography/energy package, or elementary arbitrary-size sufficiency theorem.

Exact-phrase and neighboring-concept searches found no collision. This is a documented negative
search, not a guarantee against unpublished or differently worded work.

## Venue judgment

The local sign law alone is too narrow for a renowned general journal, and the covariance lemma
alone is too elementary. Combined package clears the stated bar:

1. it turns a diagrammatic equality into exact arithmetic, Fourier, and topological structure;
2. it identifies what the decorated diagram remembers and forgets via strict tomography and
   finite fibres;
3. it discovers infinitely many local obstructions missed by the known global criterion;
4. it proves complete arbitrary-size recognition on a genuinely ramified locus with explicit
   reconstruction.

Presentation is concise, proofs are self-contained relative to clearly cited source formulas, and
scope limitations are explicit. The 17-page A4 PDF compiles without warnings; every page was
rendered and inspected with no clipping, overlap, broken glyph, orphan page, or unreadable display.

## Residual nonblocking risks

- External peer review may know differently worded prior art not found in the audit.
- A journal may prefer a specialist venue because the motivating objects are Stokes/fission data.
- The paper does not classify every twisted loopless graph or compare analytic wild character
  varieties with equal diagrams.

These are ordinary publication risks, not unresolved correctness or proof gaps.
