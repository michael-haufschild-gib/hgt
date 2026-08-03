# Hostile referee report: *Zero-loop rigidity and exact recognition for ramified nonabelian Hodge graphs*

Date: 2026-08-03

Review type: internal red-team report written to the standard of a skeptical referee. It is not an
external journal report and is not represented as one.

Target bar: a renowned general mathematics journal in the Compositio/IMRN/Advances range. This is
not an Annals/Inventiones-level claim.

## Recommendation

**Acceptable for publication at the stated target bar.**

No unresolved correctness gap, novelty collision, or material overclaim remains. The paper is short
but contains a coherent theorem package rather than one isolated calculation: a strict sign law, an
equality classification, arithmetic enumeration, a Fourier-resolution consequence, exact local
edge spectra, a decorated finite-fibre theorem, and a necessary-and-sufficient recognition theorem
for arbitrary finite graphs on a natural ramified locus. The strongest result is Theorem 8.1.

The review initially raised two publication-blocking concerns:

1. the finite-fibre proof only said that the edge formula was affine in the fission exponent;
2. the recognition proof invoked fission-tree realization without exact source coordinates.

Both were corrected in the reviewed manuscript. The proof now displays

`B_ij = C + s_d g - r_i r_j`, with `g >= 1`, and cites Boalch--Douçot--Rembado,
Theorem 3.27 and Corollary 3.28. These changes close the objections rather than hiding them.

## 1. Claims tested

I treated the following as claims that must independently survive attack.

1. The sign of the diagonal multiplicity is determined by the first noncanonical level.
2. Zero diagonal multiplicity is equivalent to `beta_i = e_{i-1} + e_i` at every level.
3. Such characteristics are exactly strict divisor chains, hence ordered multiplicative
   factorizations.
4. They lie on Hiroe's negative local-Fourier branch, with the stated converse under the large-step
   hypothesis.
5. The separated core depends only on first factorization quotients.
6. The displayed two-circle spectra contain every and only possible edge multiplicity.
7. Fixing the core matrix and ramification decoration leaves only finitely many labelled fission
   trees.
8. Pair-spectrum membership plus rescaled ultrametricity is sufficient on the elementary locus.
9. The Lean development verifies the claimed arithmetic/combinatorial core without pretending to
   formalize analytic irregular connections.
10. The package is new enough and broad enough for the stated venue class.

All ten survive.

## 2. Local sign law

### Attack: the forbidden interval may have missed coprimality edge cases

Write `R = aE` and `beta = cE`. The gcd hypothesis is exactly `gcd(a,c)=1`. Since `a >= 2`,
`c=a` is impossible. Thus `c<a+1` forces `c<=a-1`, while `c>a+1` forces `c>=a+2`.
Multiplication by `E` gives the stated gaps. No parity assumption or hidden primality hypothesis is
used.

### Attack: later exponents could reverse the first sign

They cannot. On the low branch the total drop is `R-1`, and every later exponent is strictly below
the first. This gives the strict tail estimate. On the high branch the first summand alone is at
least `R^2`; every later summand is nonnegative. At the canonical value,
`(R+E)(R-E)=R^2-E^2`, so the functional reduces exactly to the tail normalized at `E`.
Induction therefore proves a lexicographic sign law, not merely a zero test.

### Attack: inconsequential Puiseux terms produce extra zero cases

They do not change the cumulative gcd and have zero coefficient in the loop formula. The paper
states this limitation explicitly. The classification concerns characteristic level data, not every
polynomial representative.

**Verdict:** correct and sharp.

## 3. Arithmetic classification and Fourier consequence

### Attack: divisor chains may fail exponent monotonicity

For `beta_i=e_{i-1}+e_i`,

`beta_i-beta_{i+1}=e_{i-1}-e_{i+1}>0`.

Also `gcd(e_{i-1},beta_i)=gcd(e_{i-1},e_i)=e_i`. The construction therefore produces the exact
characteristic, and the sign theorem gives zero loop. The inverse map is forced term by term.

### Attack: ordered-factorization counts confuse ordered and unordered factors

They do not. A chain yields `a_i=e_{i-1}/e_i`, whose ordered product is `r`; partial products recover
the chain. For `p^k`, this is a composition of `k`, hence `2^(k-1)`. For squarefree `r`, it is an
ordered set partition of the prime factors, hence the ordered Bell number.

### Attack: the Hiroe citation is only suggestive

Primary-source text was checked. Hiroe, Theorem 3.10, says resolution by local Fourier transforms
and additions is equivalent to `e_{i-1} congruent to +/- e_i (mod beta_i)`. The Airy equality gives
the negative congruence exactly. Conversely, divisibility of `e_{i-1}+e_i` by `beta_i`, together
with `e_i<e_{i-1}<beta_i`, leaves the unique positive multiple `beta_i` below `2 beta_i`.

The paper does not claim that the knot alone classifies analytic Stokes moduli.

**Verdict:** correct; source use is exact.

## 4. Separated cores and hidden fibres

### Attack: simultaneous leading separation may be impossible for repeated slopes

For a fixed first factor `a`, only finitely many leading coefficients are required. Their `a`th
powers can be chosen pairwise distinct over `C`; this is precisely separation of the corresponding
`mu_a`-orbits. Unequal leading slopes are automatically separated.

### Attack: later ordered factors might alter the matrix

With common part zero, the larger leading slope alone enters the zero-common-part edge formula.
Substitution gives

`B_ij = r_i r_j / min(a_i,a_j)`.

Later levels do not enter. They remain visible in each full fission branch, so the hidden fibre is
the product of ordered-factorization counts of `r_i/a_i`.

**Verdict:** correct. The paper carefully claims different fission data/admissible deformation
classes, not nonisomorphic wild character varieties.

## 5. Exact pair spectra

This is the first place where a plausible-looking argument could easily omit cases.

### Attack: common integral trunks change the low spectrum

They do not. Their ramification is one, so the common-level gcd differences vanish in the rescaled
edge formula. Only the fission term remains.

### Attack: high differences produce values other than the displayed multiples

If the first difference occurs at integer degree `d>=2`, then the rescaled edge is `d-1`; hence the
edge is `rs(d-1)`. This is exactly the positive multiples of `rs`.

### Attack: equal ramification has missing fractional cases

When the mandatory coefficients lie in different `mu_r`-orbits, the edge is `r`. After aligning
them, the first lower difference occurs at `j/r`, `1<=j<=r`, and the common-level formula gives
`j-1`. Thus the low branch is exactly `{0,...,r}`. Together with the high branch it is
`{0,...,r} union r^2 N_{>0}`.

### Attack: mixed and unramified pairs have overlooked degree-one cases

Mixed separation at the Airy level gives `1`; high integer separation gives `r N_{>0}`. Two
unramified circles give `deg(q-q')-1`, hence all nonnegative integers. Coefficient choices realize
every listed value while preserving the single mandatory ramified level.

**Verdict:** exhaustive and constructive. The missing edge `3` for two ramification-two vertices is
a genuine obstruction invisible to any triangle condition.

## 6. Decorated finite-fibre theorem

### Attack: arbitrary inconsequential support makes the fibre infinite

Only if one counts polynomial representatives. The theorem counts labelled fission trees, whose
data are levels and pairwise fission exponents. The paper explicitly discards arbitrary support on
inconsequential rays.

### Attack: level numerators may be unbounded at fixed loop and ramification

For vertex `i`, the fixed weighted sum is `W_i=B_ii+r_i^2-1`. Each gcd drop is positive, so each
level numerator lies in `[1,W_i]`; there are also only finitely many strict divisor chains from
`r_i` to one.

### Attack: pairwise fission exponents may still vary infinitely

After fixing the finite common-level case, the exact formula is

`B_ij=C+s_d g-r_i r_j`, `g>=1`.

Thus fixed `B_ij` determines at most one numerator `s_d`, and hence one fission exponent, in that
case. There are finitely many pairs and cases. Boalch--Douçot--Rembado, Lemma 3.21, says labelled
fission data determine the labelled tree.

**Verdict:** finite and effectively enumerable. The revised proof is sufficient for publication.

## 7. Elementary recognition theorem

This is the main theorem and received the most hostile reading.

### Necessity

Pair spectra follow from the exact two-circle theorem. Rescaled ultrametricity is Douçot's Theorem
4.2. No issue.

### Attack: the ultrametric dendrogram is built from the wrong quantity

The construction uses the rescaled weights `w_ij=B_ij/(r_i r_j)`, exactly the quantities satisfying
the acute-isosceles law. On the elementary spectra every positive weight is either an integer, a
mandatory value `1/r`, or a lower value `b/r^2`. These three forms correspond monotonically to the
three coefficient stages used in the proof.

### Attack: mandatory ramification blocks can conflict globally

Let `r` be the smallest unresolved ramification. Pair spectra force:

- an `r`-leaf and every larger/unramified leaf to have weight `1/r`;
- two `r`-leaves to have weight at most `1/r`;
- two larger/unramified leaves to have weight strictly below `1/r`.

The strict-threshold classes therefore consist of `r`-blocks plus at most one residual block. Assign
nonzero coefficients whose `r`th powers are distinct to the `r`-blocks and coefficient zero to the
residual block. This is exactly the unique possible empty child in the fission-tree axioms.

### Attack: lower fractional stages introduce new levels

They do not. The mandatory exponent `(r+1)/r` has already reduced the cumulative gcd to one. Terms
at `(b+1)/r`, including `1/r`, are inconsequential for the loop and only control fission.

### Attack: pairwise constructions might not assemble into one irregular class

The dendrogram supplies common ancestors globally, not independently chosen pair data. Coefficients
are assigned to child clusters, so every pair first differs at its least common ancestor. The
mandatory and admissible sibling conditions are checked at each node. Theorem 3.27 and Corollary
3.28 of Boalch--Douçot--Rembado then give realization. This is the correct source theorem.

### Attack: the algorithmic claim is inflated

It is explicitly a unit-cost rational-comparison bound. Pair membership is quadratic; checking all
triangles and forming threshold partitions is cubic. No bit-complexity claim is made.

**Verdict:** sufficiency is correct, constructive, and materially new. It upgrades known necessary
twisted ultrametric conditions to a complete recognition theorem on an arbitrary-size ramified
locus.

## 8. Formal verification audit

Six theorem-specific modules were checked individually and through the `HTGeometry` umbrella:

- `AiryTowerStokesRigidity`
- `AiryTowerFactorization`
- `AiryTowerSeparatedCore`
- `AiryTowerFiniteFiber`
- `ElementaryStokesPairSpectrum`
- `ElementaryStokesGraphRecognition`

Each targeted module build passed. The umbrella build passed with 13,635 targets. Repository formal
lint passed. A separate `#print axioms` scratch audit of the principal theorems reports only standard
mathlib foundations (`propext`, `Classical.choice`, `Quot.sound` as applicable), with no project axiom,
`sorry`, `admit`, `opaque`, or `unsafe` declaration.

The formalization boundary is honest. Lean proves the arithmetic characteristic, finite-fibre
spine, exact pair presentations, and finite cophenetic recognition equivalence. Complex coefficient
selection and the published analytic fission-tree realization theorem remain paper mathematics.
The manuscript says so. This is not formalization theatre.

## 9. Novelty and priority audit

Primary sources checked through 2026-08-03 include Biquard--Boalch, Hiroe,
Boalch--Yamakawa, Boalch--Douçot--Rembado, Boalch's untwisted counting paper, and Douçot's 2025/2026
papers on twisted graphs and enriched trees.

Known inputs are correctly separated from new conclusions:

- loop and edge formulas are known;
- rescaled ultrametric necessity is known;
- fission-tree realization/classification is known;
- local Fourier resolution criterion is known;
- the strict first-deviation sign law, zero-loop equality classification, ordered-factorization
  bijection, exact ramified pair spectra, decorated finite-fibre theorem, and elementary sufficiency
  theorem were not located in those sources.

No collision was found. This is a documented search conclusion, not a guarantee against unpublished
or differently worded results.

## 10. Significance and venue judgment

The local equality theorem alone would not justify a renowned general journal. The assembled package
does, for three reasons.

1. It converts a diagrammatic zero-loop constraint into exact arithmetic, Fourier, and cabling data.
2. It finds infinitely many local obstructions absent from the only previously known global test.
3. It proves a complete recognition theorem for arbitrary finite size on a genuinely ramified
   class, with an explicit reconstruction algorithm.

The subject remains specialized, and the paper does not attempt a classification of all twisted
nonabelian Hodge graphs. That prevents an Annals/Inventiones claim. It does not prevent publication
in a respected general journal that accepts concise, exact advances in geometry and representation
theory.

## 11. Presentation audit

- Manuscript compiles without TeX warnings.
- All 12 pages were rendered and visually inspected after the last mathematical revision.
- No clipping, overlap, broken glyph, orphan address page, or unreadable table remains.
- The abstract states the strongest results and the formalization boundary.
- Source theorem numbers are now exact where realization and Fourier reduction are invoked.
- Scope exclusions prevent the most tempting moduli-space and knot-classification overclaims.

## Final verdict

**Publishable at a renowned general-journal level, subject only to ordinary external peer review.**

No major revision is required on the present evidence. External referees may request expanded
background or different notation, but there is no remaining mathematical or evidentiary defect that
should block submission.
