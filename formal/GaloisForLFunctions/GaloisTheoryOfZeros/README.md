# Galois theory of zeros

## Motivation

For a curve over a finite field, Frobenius eigenvalues are algebraic numbers and
purity identifies complex conjugation with reciprocal duality. For the Riemann
zeta function the corresponding permutations of the entire zero set are
`c(ρ) = conjugate ρ` and `ι(ρ) = 1 − ρ`. RH says `c = ι`. Their composite preserves
the ordinate; hence RH also says that the ordinate separates distinct zeros.

The programme asks whether arithmetic can identify these two permutations
without assuming the positivity that already characterizes RH. A large symmetry
group, another equivalent criterion, or a calculation on finitely many zeros
does not supply that identification.

## Objects and language

- **Coordinates:** `ρ` denotes an original ξ zero; `w=(ρ−1/2)/i` denotes its
  centered spectral coordinate. Conjugation of `w` represents `ρ↦1−conj(ρ)`;
  negation of `w` represents `ρ↦1−ρ`. A change involving `i` does not identify
  the generated fields over ℚ unless that scalar is also adjoined.
- **Zero carrier:** all distinct zeros of ξ; the zero divisor additionally records
  analytic multiplicity. Statements about permutations and statements about
  multiplicity spaces must be distinguished.
- **Zero algebra:** functions on the carrier, with reflection involution
  `f*(ρ) = conjugate (f(1 − conjugate ρ))`. Summability, topology and domains of
  trace functionals are part of its definition, not implicit assumptions.
- **Relation group:** the integer span of the zeros with its actual additive
  relations. Its character group carries the exponential flow; prime time is
  `log p`. Relations forced by the functional equation are known; further
  relations are an open arithmetic question.
- **Local equation:** a Weierstrass polynomial for zeros inside a contour,
  including multiplicity. Contour power sums specify its coefficients. A field
  of coefficients must be specified before its Galois group has meaning.
- **Covers:** multiplicity spaces of Artin L-functions and their virtual
  characters. A group acting on these spaces is not automatically a group acting
  transitively on the zeros of ζ.
- **Approximants:** Jensen polynomials and their discriminants and resultants.
  Any conclusion about ξ requires a proved passage through unbounded degree.
  A shift must be specified: translating the Taylor centre, shifting coefficient
  indices, and first passing to the even-coefficient sequence give different
  families. The centered reversed sections `R_d(Ξ)` retain negation symmetry.
- **Other places:** Carlitz–Goss valuations as a calibration for separation;
  Iwasawa characteristic series as a possible arithmetic comparison object.

## Mechanisms

1. **Separation:** an invariant separating roots forces the symmetry to fix
   them. The required archimedean invariant must come from arithmetic; assuming
   ordinate injectivity would assume RH.
2. **Trace and index:** reflection exchanges off-line pairs. Their antisymmetric
   directions give negative squares. Existing Weil-form index laws make this
   precise on the infinite zero carrier. A new contribution must recover more
   arithmetic information or prove a bound on that index.
3. **Arithmetic descent:** specify which prime-side observables are fixed by a
   proposed group, and prove that its action extends to the full zero algebra.
   Determine exactly which observables already force the action to be trivial.
4. **Local-to-global equations:** reconstruct contour polynomials, compare
   overlapping contours and control passage to the whole divisor. Finite
   polynomials are tools for this passage, not a replacement for it.
5. **Character descent:** convert restriction and induction of multiplicity
   characters into exact laws for off-line index, including non-abelian covers.
6. **Discriminant transport:** relate signs and vanishing of discriminants to
   conjugation on approximating roots, with multiplicity and limiting collisions
   explicitly controlled.

## Foundational pillars and present limits

Existing corpus results supply the following foundations; they are not claims
of new theorems in this directory.

| Foundation | What it establishes | What it leaves open |
|---|---|---|
| Functional equation and conjugation | Two commuting permutations; RH identifies them | Arithmetic reason for their equality |
| Weil/Pontryagin index laws | Negative index counts distinct right zeros | An independent index bound |
| Ordinary Dirichlet constituent obstructions | Wiener and bounded constituents with zeros cannot factor ξ in the specified classes | Other genuinely arithmetic notions of conjugacy |
| Finite-field calibration | Integral traces and reciprocal symmetry alone allow impure data | A purity-producing structure |
| Carlitz–Goss digit calculus | Greedy carry-free compositions are uniquely optimal | Archimedean substitute for valuation separation |
| Jensen approximation | Finite non-real counts detect off-line multiplicity in the limit | Arithmetic control uniform in degree |

### Source fields and the entire divisor

A ground field can contain too much local information. Let `L=ℚ(all w)`.
First continued-source traces over all admissible rational rectangles already
generate `L`: a rational isolating contour recovers each zero by dividing its
first trace by its positive integer multiplicity. All nonnegative local moments
generate the same field; counts alone generate ℚ. An arbitrary automorphism of
ℂ fixes every first trace exactly when it fixes every centered zero, without
any continuity assumption. Thus all local traces leave a trivial relative
zero-field action. This uses the analytically continued source, not an
absolutely convergent prime series in the critical strip.
[Contour-field theorem](TheFieldOfAllLocalContourMoments.lean).

Complete ordinate fibres retain a smaller source field `K`. Its generators
are stable continued prime–archimedean contour moments: the value is uniform
over all sufficiently narrow slabs and transverse bands sufficiently close
to the whole critical strip. These moments equal the full fibre power sums
with analytic multiplicity. Consequently `K⊆ℝ` and `K` is exactly the field
generated by the coefficients of all complete fibre polynomials `P_t`.
Each `P_t` is monic, has degree equal to the full analytic fibre mass, and
recovers its entire root multiset. The extension `L/K` is algebraic and normal,
the compositum of these source splitting fields.
[Complete-fibre source equations](TheFieldOfCompleteFibreTraces.lean).

The first trace of a nonempty fibre is its mass times its ordinate, so `t∈K`.
Every source automorphism therefore preserves that finite fibre and commutes
with centered conjugation `c_L`, since `conj(w)=2t−w` there. Every critical-line
zero is fixed individually; no action on all zeros can be transitive over this
base. Moreover `K=L` exactly when every centered zero is real. Centrality is
unconditional, while identifying conjugation with the identity remains open.

For each ordinate let `Z_t` be the finite distinct-root support, `m_t` its
analytic multiplicity, and `c_t` its conjugation permutation. Define

```
C_t = {π∈Sym(Z_t) : πc_t=c_tπ and m_t∘π=m_t}.
```

The action `Gal(L/K) → ∏_t C_t` is faithful and continuous, with closed image.
Each finite-coordinate permutation has an open kernel in the Krull topology.
Multiplicity is transported through the actual source polynomial; artificial
copy labels contribute no permutations. A prescribed family extends uniquely
exactly when every finite coordinate selection is realized by a source
automorphism. Compactness supplies the simultaneous extension. This criterion
ranges over all finite selections of the full infinite divisor; equality of
the arithmetic image with the whole product is not asserted.
[Full divisor action](ThePermutationActionOnAllZeroFibres.lean).


These ambient groups have exact signed coordinates. Let `B_(t,m)` consist
of the roots in `Z_t` with positive imaginary part and analytic multiplicity
`m`. Each is a canonical conjugate-pair representative, and

```
C_t ≅ ∏_m (C₂ ≀ Sym(B_(t,m))).
```

An element is a pair permutation `π` and one sign `ε` per output pair;
it sends `(p,u)` to `(πp,ε(πp)u)`. Multiplication is
`(ε,π)(η,τ)=(ε·(η∘π⁻¹),πτ)`. The possible real root is unique and fixed.
Every independent family of such block actions assembles into a symmetry
of the complete fibre divisor. Thus the entire arithmetic action is a closed
faithful subgroup of the product over all `(t,m)` of these finite signed
groups. Centered conjugation is uniform sign reversal, with no permutation
of the positive-root labels. Transporting finite-source compatibility through
these coordinates describes exactly which signed families are arithmetic.
[Weighted signed-permutation classification](TheSignedPermutationsOfTheZeroFibres.lean).

This extension criterion also has an intrinsic form using finite extensions.
For a finite set `S` of ordinates, let `L_S` be the splitting field inside `L` of
`∏_(t∈S) P_t`. Each `L_S/K` is finite Galois, these fields increase with `S`,
and their supremum is `L`. A full family `π∈∏_t C_t` extends uniquely exactly
when, for every finite `S`, an automorphism of `L_S/K` realizes its selected
root permutations. Normality extends each finite-stage automorphism to `L`;
compactness then imposes all coordinates simultaneously. Thus finite arithmetic
compatibility is checked in the actual source equations, with a proved passage
to the entire divisor.
[Finite source composita and intrinsic gluing](TheFiniteSourceCompositaOfTheZeros.lean).


The topology is already recovered by a countable cofinal tower. Let `H_n`
be the complete source splitting field of all occupied fibres with `|t|≤n`.
The strip bound makes each selection finite and preserves whole fibres.
Every finite source compositum lies in some `H_n`, so `sup_n H_n=L`.
Restriction gives both a group isomorphism and a homeomorphism
`Gal(L/K) ≅ lim_n Gal(H_n/K)`, with compatibility along the actual inclusions.
Thus the complete height tower retains all source automorphisms and the full
Krull topology, with no fixed height cutoff.
[Complete height tower](TheHeightTowerOfTheZeroField.lean).

### Width fields and the geometric involutions

Write `w_q=t_q+iδ_q`, with `δ_q=1/2−Re ρ_q`, and define

```
E = K(δ_qδ_r : all q,r),    F = K(δ_q : all q),
M = L(i) = ℚ(i, all ρ).
```

The real parts have exact field descriptions:
`E=L∩ℝ`, `F=M∩ℝ`, and `M=F(i)`. Both `E/K` and `F/K` are normal.
Restriction to `F` and sign on `i` give the unconditional equivalence

```
Gal(M/K) ≅ Gal(F/K) × C₂.
```

Ordinary conjugation occupies `(id,−1)`. Every automorphism of `F/K` extends
to `M`, with either Gaussian sign. These are statements about the entire
infinite fields.
[Maximal real subfield](TheMaximalRealSubfieldOfTheZeroField.lean),
[real-width Galois group](TheRealWidthFieldOfTheZeros.lean).

The widths themselves have complete source equations. Set `Q(X)=P_t(X+t)`
and let `n` be the fibre mass. Gaussian rotation gives

```
Q(iX) = i^n ∏_q (X−δ_q).
```

The product has real coefficients. Each differs from a source coefficient
by a Gaussian phase; an imaginary phase forces vanishing. Thus all its
coefficients lie in `K`. These hyperbolic equations, with full analytic
multiplicities, generate `F` as their infinite splitting-field compositum.
Source automorphisms send a width to another width in its complete fibre.
Any simultaneous width reversal is therefore central in `Gal(F/K)`.
Hyperbolicity here does not assert that the widths vanish.
[Source width equations](TheSourceEquationsOfTheZeroWidths.lean).

If `δ₀≠0`, then

```
L = E(iδ₀),     [L:E]=2,     F = E(δ₀),
F=E ⇔ δ₀∈E ⇔ i∈L.
```

Indeed `iδ_q=(δ₀δ_q/δ₀²)iδ₀`, so one nonzero width controls the whole
centered extension. The entire Gaussian field has relative degree two or four:

```
F=E:  M=E(i),                  [M:E]=2;
F≠E:  M=E(δ₀,i), δ₀∉E,         [M:E]=4.
```

In the second case its quadratic intermediate fields are exactly the three
distinct fields `F=E(δ₀)`, `E(i)`, and `L=E(iδ₀)`. Every `z∈M` with
`z²∈E` lies on one of the four `E`-lines generated by `1,δ₀,i,iδ₀`.
Completing the square supplies such a nonbase generator for every quadratic
intermediate field. If all widths vanish, `L=K` instead.
[Biquadratic classification](TheBiquadraticDiagramOfTheZeroField.lean).

The quadratic width extension has an intrinsic arithmetic class. Every
nonzero `δ_q²` represents the same `ω∈E×/(E×)²`; set `ω=1` when all
widths vanish. Every automorphism of `E/K` fixes `ω`, and

```
ω=1 ⇔ F=E,
Gal(F/K) → Gal(E/K) splits continuously ⇔ ω comes from K×/(K×)².
```

For a nonzero anchor, descent means `δ_q²=a u²`, with `a∈K×` and
`u∈E×`. Fixing `δ_q/u` gives the continuous section. Conversely, the
closed image of a section cuts out a quadratic field over `K`, disjoint
from `E`; its square-root generator gives the descent witness. Infinite
Galois correspondence controls this argument on the entire fields.
Invariance is established, but actual descent remains open.
[Global width square class and descent](TheDescentOfTheGlobalWidthSquareClass.lean).

Source norms impose an arithmetic restriction on failure of descent. For a
nonzero width put `d=δ_q²`, `D=K(d)`, and `n=[D:K]`. The exact identity is

```
[Norm_(D/K)(d)] = ω^n   in E×/(E×)².
```

Every embedding of `D` into `E` extends to a source automorphism of `E`,
so all norm factors have class `ω`. An odd `n` therefore supplies an
explicit source representative and a continuous section of the entire
width restriction. Otherwise, failure of splitting forces every nonzero
squared-width degree to be even and every signed-width degree to be
divisible by four: `K(δ_q)/K(δ_q²)` is then quadratic. No actual source
degree has been proved odd, and even degrees do not imply non-descent.
[Source norms and degree obstructions](TheSourceNormsOfTheZeroWidthSquares.lean).

Complete multiplicity blocks also produce arithmetic sign characters. For
`B=B_(t,m)` and `r=#B`, define the source product and offset radical

```
a = ∏_(p∈B) δ_p² ∈ K×,     b = ∏_(p∈B) (w_p−conj(w_p))/2 ∈ L×.
```

Multiplying the independent pair signs gives a continuous character
`χ_(t,m):Gal(L/K)→{±1}` with `σ(b)=χ_(t,m)(σ)b`,
`b²=(−1)^r a`, and `χ_(t,m)(c_L)=(−1)^r`. Its kernel fixes exactly
`K(b)`, an extension of degree one or two, and degree two for odd `r`.
The complete product descends because every source automorphism permutes
its squared-width factors. Its class is `[a]=ω^r`. Hence any odd block
splits the entire width restriction continuously; nonsplitting forces even
pair counts in every ordinate and analytic-multiplicity block. No actual
odd block is known from these arguments, and even counts do not imply
nonsplitting.
[Arithmetic block characters and their fixed fields](TheArithmeticSignsOfTheZeroFibres.lean).

Functional-equation reflection on the original zeros lifts to a source-field
automorphism precisely when `i∉L`, equivalently when `−1` is not a square
in `L`; its lift `ι` is unique. Preservation of nonzero ordinates forces that
lift to reverse `i` and fix `L`. Its action on the centered generators therefore
accounts for the scalar `i` as well as the original zeros. In this regime

```
Gal(M/K) ≅ Gal(L/K) × C₂,     ι=(id,−1),     c=(c_L,−1).
```

Simultaneous negation of all widths exists exactly in the same regime and is
unique. For a nonzero anchor this is equivalent to `δ₀∉E`.
[Gaussian obstruction and lift](TheGaussianExtensionOfTheZeroField.lean),
[width reversal](TheRealWidthFieldOfTheZeros.lean).

Let `ν=cι`, reflection across the critical line. The geometric fixed fields are

```
M^c = F,       M^ι = L,       M^ν = E(i),       M^{c,ι} = E.
```

Both `ι` and `ν` are central. An explicit homomorphism
`C₂×C₂→Gal(M/K)` contains all three actions and is injective whenever a width
is nonzero. In the pure case `ν=id` and `c=ι`. Thus the fixed-field diagram
distinguishes centrality from equality of the geometric involutions, without
deciding which Gaussian regime occurs or whether any width is nonzero.
[Geometric actions and fixed fields](TheGeometricInvolutionsOfTheZeroField.lean).

### Jensen equations, folding, and discriminants

For a monic real polynomial `Q` of degree `n`, folding has the exact identities

```
disc(Q(X²))   = 4^n (−1)^n Q(0)   disc(Q)²,
disc(XQ(X²))  = 4^n (−1)^n Q(0)³  disc(Q)².
```

The doubled equation is separable exactly when `Q` is separable and `Q(0)≠0`.
Its discriminant retains branch-point information while squaring away the
quotient discriminant sign; collisions and degree zero are included.
[Universal folding identities](FoldedDiscriminant.lean).

For the actual centered reversed sections, put `μ_k=xiMoment(1/2,k)` and
normalize `P_d=R_d/μ₀`. Monic quotient equations satisfy

```
P₂ₙ=Eₙ(X²),                  P₂ₙ₊₁=X Oₙ(X²),
disc(P₂ₙ)   = 4^n (μ₂ₙ/μ₀) disc(Eₙ)²,
disc(P₂ₙ₊₁) = 4^n ((2n+1)μ₂ₙ/μ₀)³ disc(Oₙ)².
```

The moment factors are strictly positive. Every full centered discriminant,
including the unnormalized one, is nonnegative; vanishing is exactly quotient
inseparability. Eventual nonvanishing remains open, so this does not prove
eventual constancy in `{0,+}`.
[Centered discriminants and collision criteria](CenteredJensenDiscriminant.lean).

Let `K_J=ℚ(μ₂ₙ/μ₀ : n≥0)` and `m_n=μ₂ₙ/μ₀`. This is exactly the field
generated by all even quotient coefficients; odd quotient coefficients also
lie in `K_J`. There are `s_n,t_n∈K_J` with

```
disc(P₂ₙ)   = m_n s_n²,
disc(P₂ₙ₊₁) = (2n+1)m_n t_n².
```

These identify the nonzero square classes. The field adjoining every full
monic discriminant square root to `K_J` lies in ℝ and is fixed by conjugation.
[Coefficient and discriminant fields](CenteredJensenDiscriminantField.lean).

Folding nevertheless retains the full off-line census. Nonzero imaginary
roots are absent from every centered section. If `Q_d` counts its first-quadrant
roots, `N_d` its nonreal roots, and `M_d` the nonreal roots of its quotient,
all with multiplicity, then

```
N_d=4Q_d=2M_d,       Q_d and M_d are nondecreasing,
sup_d 2M_d = the entire off-line divisor multiplicity in ℕ∞.
```

A finite off-line divisor of size `4m` gives eventual `M_d=2m`; an infinite divisor
forces `M_d→∞`. The full conjugation parity `(-1)^(N_d/2)` is always one,
while the quotient retains the complete finite-or-infinite census.
[Quartet exhaustion](JensenQuartetExhaustion.lean),
[folded exhaustion](FoldedJensenExhaustion.lean).

## Research questions

1. **Relations:** determine integer relations beyond
   `ρ + (1 − ρ) = 1`, and their effect on the flow's character group.
2. **Ground field:** construct fields from prime-side contour data; determine
   the actual automorphisms of the resulting local equations and their
   compatibility as contours increase.
3. **Conjugation:** find structural generators commuting with `c`, and determine
   when such centrality can imply purity rather than follow from it.
4. **Separating invariant:** obtain a prime-side invariant separating ordinates
   uniformly in height without first locating the zeros.
5. **Covers:** establish character-by-character index laws for non-abelian Artin
   factors, with all analytic inputs proved rather than assumed.
6. **Other places:** construct, or identify an obstruction to, an object whose
   p-adic characteristic series and archimedean trace recover the two zeta
   theories.
7. **Discriminants:** decide eventual constancy of Jensen discriminant signs at
   each shift, treating repeated roots and unbounded degree.
8. **Irreducibility:** find a notion of arithmetic constituent outside excluded
   Dirichlet classes that carries usable information about the full divisor.

## Tools to develop

An infinite zero algebra with explicit operator domains; contour-polynomial
descent and coefficient fields; arithmetic automorphism and centralizer
calculi; trace-form reconstruction; index-valued Heilbronn characters; Jensen
discriminant transport; and a comparison of valuation separation with
archimedean observables. Each tool must have a concrete application to the
questions above.

## Traps

- Functional equation, Gamma factor and zero count admit impure models.
- Trace positivity is Weil's criterion; renaming it does not prove it.
- Centrality of conjugation in a pure finite-rank example does not establish
  purity in infinite rank.
- Fixing all individual root evaluations may define the trivial group before
  any arithmetic enters. Fixing aggregate traces is a different requirement.
- Zeros of ξ are not known to be algebraic; a splitting field over an unspecified
  field is not an arithmetic construction.
- A finite window, bounded degree or finite set of prime times cannot replace a
  theorem about the entire divisor without a proved uniform passage.
- Actions on approximating splitting fields do not automatically act on limit
  zeros: preservation of convergence is an additional theorem to prove.
- An Artin-holomorphy, RH, simplicity, independence or summability premise cannot
  be concealed in a structure or imported interface.

## Place in the wider research

`ArithmeticCastelnuovoSeveri` supplies the zero-side Krein form and exact index
laws. `ArithmeticOrientationGeometry` supplies flow, observable visibility and
the distinction between geometric identities and orientation. `HTGeometry`
constrains differential equations and arithmetic constituents. `SquareRootThreshold`
provides infinite zero configurations and quantitative visibility. Finite-field
and Carlitz–Goss theories are calibrations, not substitutes for the archimedean
problem. This programme owns the arithmetic symmetry, equations and descent of
the zero divisor; it should reuse those existing interfaces.

## Contribution and success criteria

A contribution must answer one of the research questions, construct a tool that
actually advances it, or classify a genuine obstruction together with its
strongest positive survivor. It must address the infinite object or prove the
uniform passage to it. New terminology, isolated finite examples, improved
constants without a stronger conclusion, and wrappers around known RH criteria
do not qualify.

Every mathematical claim needs a dependency-closed proof and Lean formalization
without additional unproved analytic premises. All programme modules belong in
this directory and are imported by `../GaloisTheoryOfZeros.lean`.

Full success requires answers to the eight questions and the advertised tools,
including an arithmetic mechanism that locates conjugation. These remain open;
this foundational document does not claim that the programme is complete.
