# Simple-horizon rank-to-depth transmutation law

- **ID:** `simple-horizon-rank-to-depth-transmutation-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / UNIVERSAL LOCAL NORMAL FORM / POSITIVE SURVIVOR
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [GENERAL CONSTRAINT-HORIZON LAW]`
  `[CLASSICAL INGREDIENTS] [NO RH CLAIM] [LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`
- **Statement:** at simple common-normal horizon, redundant constraint rank is transmuted into
  derived type-`A` excess and observer jet depth rather than stronger underived codimension.

## Setup

Let `R` be discrete valuation ring with uniformizer `a`, residue field `k=R/(a)`, and fraction
field `K`. Fix `N>=1` units `u_1,...,u_N in R^times` and constraints

\[
 f_i=a u_i.
 \tag{1}
\]

Let

\[
 h:R^N\to R,
 \qquad
 h(e_i)=u_i,
 \qquad
 E=\ker h,
 \tag{2}
\]

and let `K(f_1,...,f_N)` be Koszul differential graded algebra.

For observer part assume residues

\[
 \bar u_i\in k
 \tag{3}
\]

are pairwise distinct. Put

\[
 P(T)=\prod_{i=1}^N(T-f_i),
 \qquad
 A=R[T]/(P),
 \tag{4}
\]

and define sheet-evaluation observer

\[
 J:A\to R^N,
 \qquad
 g(T)\mapsto(g(f_1),\ldots,g(f_N)).
 \tag{5}
\]

## Theorem 1: underived saturation and derived excess

Underived ideal and support are already fixed by one constraint:

\[
 (f_1,\ldots,f_N)=(a).
 \tag{6}
\]

But derived common intersection has

\[
 \boxed{
 H_\bullet K(f_1,\ldots,f_N)
 \cong
 k\otimes_R\bigwedge\nolimits^\bullet E,}
 \tag{7}
\]

so

\[
 \dim_kH_j=\binom{N-1}{j}.
 \tag{8}
\]

Moreover units canonically normalize constraint legs:

\[
 s_i=u_i^{-1}e_i,
 \qquad
 h(s_i)=1,
 \tag{9}
\]

and give isomorphism

\[
 \boxed{
 E\cong
 \left\{(b_i)\in R^N:\sum_ib_i=0\right\},
 \quad
 (b_i)\mapsto\sum_i b_i s_i.}
 \tag{10}
\]

Thus degree-one excess is type-`A_(N-1)` root module before specialization.

### Proof

Each `f_i=a u_i` with unit `u_i`, proving `(6)`. Since `h` split surjective, choose `v` with
`h(v)=1` and decompose `R^N=Rv direct-sum E`. Koszul differential is contraction by `a h`, so

\[
 K(f_1,\ldots,f_N)
 \cong
 K(a)\otimes_R(\bigwedge^\bullet E,0).
\]

Uniformizer is nonzerodivisor; `H_0K(a)=k`, higher homology zero. This proves `(7)`--`(8)`.
Vectors `(s_i)` are basis and `h(sum b_i s_i)=sum b_i`, proving `(10)`. QED.

## Theorem 2: observer Smith staircase

Observer `J` is injective and over `R` is equivalent to diagonal map

\[
 \boxed{
 J\sim\operatorname{diag}(1,a,a^2,\ldots,a^{N-1}).}
 \tag{11}
\]

Hence

\[
 \boxed{
 \operatorname{coker}J
 \cong\bigoplus_{j=1}^{N-1}R/(a^j).}
 \tag{12}
\]

Its length is `binom(N,2)`, and `a`-adic grade dimensions are

\[
 N-1,N-2,\ldots,1.
 \tag{13}
\]

These equal numbers of positive type-`A_(N-1)` roots of heights `1,...,N-1`.

### Proof

In monomial basis, evaluation matrix is

\[
 J=(u_i^{j-1})_{i,j}
 \operatorname{diag}(1,a,\ldots,a^{N-1}).
 \tag{14}
\]

First factor reduces modulo `a` to Vandermonde on distinct residues `bar u_i`, hence is invertible
over local ring `R`. This proves Smith form. Nonzero determinant gives injectivity. Cokernel and
length follow. In grade `q`, summands `R/(a^j)` with `j>q` contribute, giving `(13)`. Positive
roots are intervals of simple roots; `N-h` have height `h`. QED.

## Theorem 3: orientation, discriminant, and cotangent square law

Let `m=binom(N,2)` and `C=coker J`. Then

\[
 \boxed{
 \operatorname{Fitt}_0(C)=(a^m),
 \qquad
 \operatorname{Fitt}_0^R(\Omega_{A/R})=(a^{2m})
 =\operatorname{Fitt}_0(C)^2.}
 \tag{15}
\]

Equivalently,

\[
 \operatorname{ord}_a\det J=m,
 \qquad
 \operatorname{ord}_a\operatorname{Disc}(P)=2m=N(N-1).
 \tag{16}
\]

### Proof

Smith form gives determinant and first Fitting ideal of observer cokernel. For `i!=j`,

\[
 f_j-f_i=a(u_j-u_i),
\]

and `u_j-u_i` is unit because residues are distinct. Vandermonde root formula gives determinant
order `m` and discriminant order `2m`. Monogenic cotangent/Fitting theorem identifies
`Fitt_0^R(Omega_(A/R))` with discriminant ideal, proving `(15)`--`(16)`. QED.

## Theorem 4: successor persistence law

Under same normal-form hypotheses, adding one more sheet changes observer defect abstractly by

\[
 \boxed{
 C_{N+1}\cong C_N\oplus R/(a^N).}
 \tag{17}
\]

Thus one new transverse constraint direction becomes persistence bar length `N`, contributes one
class in each normal grade `0,...,N-1`, and accounts for `N` new positive roots.

### Proof

Apply Smith classification `(12)` at ranks `N` and `N+1`. QED.

Isomorphism is not canonical without ordered source transition/trivialization.

## The transmutation principle

At simple common-normal horizon:

\[
 \boxed{
 \begin{array}{c}
 \text{extra underived codimension}=0,\\
 \text{derived excess rank}=N-1,\\
 \text{maximal observer jet depth}=N-1,\\
 \text{orientation order}=\binom N2,\\
 \text{discriminant order}=N(N-1).
 \end{array}}
 \tag{18}
\]

Constraint rank is not destroyed. It is transmuted from transverse codimension into derived root
directions and normal persistence depth. This gives rigorous mechanism behind corpus pattern
“making several faces exact does not add selection”: underived locus saturates immediately while
derived/observer complexity grows.

## Scope and falsifiers

1. Distinct leading units are essential for full Smith staircase. Colliding residues produce
   different partitions; their classification is next singularity problem.
2. Higher common vanishing order `f_i=a^r u_i` rescales every Smith exponent by `r`; mixed orders
   require Newton-polygon/valuation classification.
3. Nonmonogenic observers need determinantal/Fitting replacement.
4. Theorem is local normal form, not source selector; it identifies horizon once common normal
   coordinate is given.
5. Same theorem applies to generalized primes and unrelated analytic sheets. It cannot force RH.
6. Generic ingredients are classical Koszul, Smith, Vandermonde, and discriminant theory. New
   contribution is exact joint transmutation dictionary motivated by corpus.

## Applications now proved

- prime radial defects `p^(Ma)-1`: source-specific root frame, Todd half-density, phase curvature;
- positive shell common divisor: generic Koszul face already in corpus;
- quadratic collision `N=2`: one Tor/conormal line and inverse exponent one;
- prediction for `N`-sheet HT/observer collision: persistence partition must be
  `(1,2,...,N-1)` in simple common-normal class.

## Lean-return note

Formalized; see `simple-horizon-rank-to-depth-transmutation-law-formalized.md`.  The instruction to
reuse existing Koszul infrastructure after a corpus search was followed literally: the augmentation,
its split, the relation basis and the row-reduced Koszul homology are all cited from
`HTGeometry.CommonFactorKoszulHomology` and `HTGeometry.PhysicalCharacteristicIncidence`, not
rebuilt.

## Gates

- [x] dependency-closed paper proof
- [x] sharp hypotheses and singularity falsifiers
- [x] source-specific prime application
- [ ] external novelty audit
- [x] Lean formalization

## Log

- 2026-08-08 — abstracted prime-radial result to universal simple common-normal horizon theorem.
