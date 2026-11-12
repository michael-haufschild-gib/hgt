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

The same descent obstruction governs every continuous quadratic character:

```
∃ continuous χ:Gal(L/K)→{±1}, χ(c_L)=−1
  ⇔ the width restriction splits and some width is nonzero.
```

Every detecting character has a nonzero purely imaginary eigenradical
`b∈L`, with `b²∈K`, `σ(b)=χ(σ)b`, and exact fixed field
`L^ker χ=K(b)` of degree two. Its eigenradicals differ by source units.
Closed-kernel Galois correspondence supplies `d` moved by conjugation;
`b=d−c_L(d)` realizes the character. Dividing by any nonzero imaginary
zero offset puts the ratio in `E`, recovering width-class descent.
Conversely, descent constructs the radical `iδ/u` and its continuous sign
character. Restriction and character value give both a group isomorphism
and homeomorphism `Gal(L/K) ≅ Gal(E/K) × C₂`, with `c_L=(1,−1)`: the
radical generates `L` over `E`, and conjugation adjusts the sign of any
extended real-field automorphism. Nonsplitting therefore prevents every
continuous quadratic character from detecting centered conjugation.
Actual descent remains undecided.
[Full quadratic detection criterion](TheQuadraticCharactersOfConjugation.lean).

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

### Squared-width quotient and arithmetic sign kernel

Put `D=K(δ_q² : all q)⊆E`. This is a normal extension of `K`: each source
automorphism sends an imaginary offset to another offset in the same ordinate
fibre and therefore permutes their squares. Restriction is continuous and
surjective, with exact sequence

```
1 → Gal(L/D) → Gal(L/K) → Gal(D/K) → 1.
```

The kernel admits an explicit arithmetic classification. Index all nonzero
widths by `q`, put `b_q=iδ_q` and `a_q=−δ_q²∈D`, and prescribe signs `ε_q`.
There is a unique automorphism of the entire `L/D` with
`σ(b_q)=ε_q b_q` exactly when

```
∀ finite S, (∏_(q∈S) a_q is a square in D) ⇒ ∏_(q∈S) ε_q=1.
```

This gives both a group isomorphism and a homeomorphism onto the closed
subgroup of compatible signs. It includes relations across distinct ordinates
and forces consistency between repeated divisor copies. No independence of
width square classes is assumed. Relations are tested over `D`, before the
pairwise width products are adjoined to form `E`.

A product sign character is trivial precisely when its radical product lies
in `D`, by infinite Galois correspondence. That is precisely the displayed
square condition. Finite sign characters separate each finite coordinate image;
compactness realizes all coordinates simultaneously. The offsets and the
source ordinates generate the whole field, proving uniqueness.

Conjugation is uniform sign reversal. Every square relation has even parity,
since its imaginary radical product must be fixed by conjugation. This locates
conjugation within the relation description. The actual relation space and
splitting of this exact sequence remain undetermined; no width is proved nonzero.
[Full Kummer sign kernel](TheKummerRelationsOfTheZeroWidths.lean).

### Arithmetic splitting of additive relations

The field `D=K(δ_q² : all q)` also controls additive relations. For nonzero
widths put `b_q=iδ_q`, `a_q=b_q²=−δ_q²∈D`, and declare

\[
q\sim r\quad\Longleftrightarrow\quad a_qa_r\in D^{\times2}.
\]

These classes are exactly the distinct quadratic characters through which
`Gal(L/D)` acts on the offsets. Within a class the offsets differ by a
nonzero scalar in `D`; offsets from distinct classes are linearly independent
over `D`. Thus every `D`-linear relation splits separately in each class.
The proof applies all kernel automorphisms to the relation and uses
Dedekind independence of multiplicative characters. Passing from `D` to the
maximal real field `E` collapses these classes, since every pairwise width
product belongs to `E`.

For every finitely supported integer family `(n_q)` on the entire zero
divisor, this yields the exact equivalence

\[
\sum_q n_qw_q=0
\quad\Longleftrightarrow\quad
\sum_q n_qt_q=0
\quad\text{and}\quad
\forall C,\ \sum_{q\in C}n_qb_q=0.
\]

Here `C` ranges over the nonzero width classes; zero offsets contribute
nothing. Conjugation separates the ordinate sum from the offset sum.
Repeated divisor copies are retained, and no height cutoff occurs.
The square-class partition and the integer relations within each class
remain arithmetic questions; the theorem does not assert rational
independence of the ordinates or widths.

[Arithmetic classes of additive relations](TheArithmeticClassesOfAdditiveZeroRelations.lean).

### Integral zero motive and its central weight

Let `Γ` be the integer span of all centered zeros inside `L`. It retains
exactly their additive relations. The full source Galois group acts
faithfully on `Γ` and fixes its ordinate projection. Let `T,B⊆ℝ` be the
ordinate and width images, and `Γ⁺,Γ⁻` the pure real and imaginary subgroups.

The common coordinate gluing group is

```
Q = Γ/(Γ⁺+Γ⁻) ≅ T/T₀ ≅ B/B₀,
```

where `T₀` and `B₀` consist of coordinates realized with the other coordinate
zero. The group `Γ` is exactly the fibre product of `T` and `B` over these
identified quotients. Moreover `2Q=0`: the integral elements `z+conj(z)`
and `z−conj(z)` separate `2z` into its real and imaginary parts.
The gluing group can be infinite; its vanishing is not assumed.

For a group `H`, write `H^∨=Hom(H,ℂˣ)`. Divisibility of `ℂˣ` gives the exact
sequence of complex character groups

```
1 → Q^∨ → T^∨ × B^∨ → Γ^∨ → 1.
```

The kernel consists uniquely of opposite characters of the common gluing
quotient and is killed by two. Conjugation fixes the ordinate character
factor and inverts the width factor. The normalized exponential flow has
the canonical lift `exp(iut) exp(−ub)`; prime time is `u=log p`.

Centering requires an additional integral correction. For the integer span
`Δ` of the original zeros `ρ`, functional-equation pairing gives `1∈Δ`, and

```
A = Δ + (1/2)ℤ = (1/2)ℤ + iΓ.
```

The quotient `A/Δ` is cyclic and killed by two. Every character of `Δ`
extends to `A`; its extension is determined by its value `h` on `1/2`,
with `h²=χ(1)`. Thus there are at most two central extensions. The canonical
flow satisfies `exp(uρ)=exp(u/2) exp(iuw)` at every original zero.
This restores the original motive without treating centering as an integral
coordinate change.

The actual coordinate relations, gluing group, and membership of `1/2`
in `Δ` remain undetermined.
[Integral zero motive](TheIntegralZeroMotive.lean).

### Prime-time sampling and exact algebraic identities

The full zero motive has coordinate algebra `ℂ[Δ]`, whose basis elements
`[z]` satisfy `[z][w]=[z+w]`. Each element has finite support in the entire
integer zero group; the algebra itself has no height cutoff. Its complex
algebra points are exactly the characters `Δ→ℂˣ`. This equivalence identifies
the established exponential flow with evaluation `[z]↦exp(uz)`.

Evaluation at prime times is injective even after any finite set of primes
is discarded:

```
ℂ[Δ] → ∏_(p prime, p∉E) ℂ,       f ↦ (f(χ_log p))_p.
```

Every nonzero regular function is detected outside any prescribed finite
prime set. Thus prime-time points are Zariski dense in the coordinate-algebra
sense.
For a regular function `f=Σ c_z[z]`, its flow evaluation is an entire finite
exponential sum. Vanishing at every prime logarithm contradicts the linear
zero-count bound for nonzero functions of finite exponential type:
Chebyshev's prime count supplies exponentially many distinct zeros.
A polynomial vanishing at the omitted logarithms restores the full sampling
hypothesis without leaving finite exponential type. Independence of distinct
exponential characters then forces every `c_z=0`.

A polynomial in the zero coordinates therefore vanishes at all but finitely
many prime times exactly when, for each exponent `z`, the coefficients of all
its monomials with total zero exponent `z` sum to zero. These exponent collisions
are the actual additive relations among the original zeros. Neither
independence of ordinates nor simplicity of zeros is assumed.

This gives faithful algebraic sampling and a complete relation test. It
does not give a bounded sampling inverse, determine the relation group,
or produce a purity criterion.
[Prime-time density](ThePrimeTimePointsOfTheZeroMotive.lean).

### Two-prime dynamics and commuting symmetries

On `A=ℂ[Δ]`, translation by the prime-time point acts as
`T_p([z])=p^z[z]`. The pair `(2^z,3^z)` distinguishes all complex exponents:
a common exponential period would give an integer relation between
`log 2` and `log 3`, contradicting unique factorization.

The joint eigenspaces of `T_2,T_3` are therefore precisely the individual
character lines. Every complex-linear operator commuting with both is a
unique diagonal coefficient multiplier. Among these, the algebra
endomorphisms are exactly

```
T_χ([z]) = χ(z)[z],       χ∈Hom(Δ,ℂˣ).
```

All are invertible; requiring the identity point to be fixed leaves only
the identity map. Thus a complex-linear symmetry commuting with both prime
translations cannot permute distinct character exponents.

The only ideals stable under both translations are `0` and `A`. Indeed,
a nonzero stable ideal has an element of least coefficient-support size.
If two exponents occur, subtracting a suitable eigenvalue times that
element from one prime translate reduces its support without killing it.
The resulting contradiction leaves a single character, which is a unit.

Every nonnegative two-prime orbit through every complex motive point is
consequently Zariski dense: its vanishing ideal is stable and proper, hence
zero. In particular, values at all times `log(2^m 3^n)`, `m,n≥0`, determine
every regular function on the entire motive. The finite support of each
regular function imposes no height cutoff on the zero group.

This classification concerns complex-linear maps. Passing to the real base
recovers ordinary conjugation as follows; arithmetic descent remains open.
[Prime translations and their centralizer](TheCentralizerOfPrimeTranslations.lean).

### The real structure selected by prime translations

On the same full algebra `A=ℂ[Δ]`, conjugating coefficients and exponents gives

```
J(Σ a_z[z]) = Σ conjugate(a_z)[conjugate(z)].
```

This real-algebra involution commutes with every prime translation. Conversely,
every real-algebra endomorphism commuting with `T_2,T_3` has exactly one form

```
T_χ  or  T_χ ∘ J,       χ∈Hom(Δ,ℂˣ).
```

Indeed, the common fixed subspace of the two translations is the constant
line. A commuting map therefore preserves the coefficient field. Its scalar
action is identity or conjugation, reducing both cases to the complex-linear
classification. Every such endomorphism is invertible. The two forms are
distinguished by their action on the constant `i`.

Preserving the identity point means preserving the augmentation ideal
`ker(ε)`, where `ε([z])=1`. The resulting centralizer is exactly `{1,J}`.
A translation preserving this ideal satisfies `χ(z)−1=0` for every `z`,
by evaluating its image of `[z]−1`; hence its character is trivial. Thus the unique nonidentity pointed real
symmetry commuting with the two prime translations is ordinary conjugation,
and it sends every actual zero coordinate `[ρ]` to `[conjugate(ρ)]`.
Conjugation preserves the ideal but conjugates the value of `ε`; requiring
`ε∘J=ε` would incorrectly exclude it.

On translating points, put `κχ(z)=conjugate(χ(conjugate(z)))`. Then
`κ²=1` and `J T_χ=T_(κχ) J`, which determines composition in this centralizer.
This locates the real structure on the entire motive using two prime
translations. Its base is all of `ℝ`; descent to the arithmetic source field,
comparison with functional-equation reflection, and purity remain open.
[Real structure of prime translations](TheRealStructureOfPrimeTranslations.lean).

### Scalar descent of the prime centralizer

The restriction to real scalars can be removed. Define the actual joint spectrum

```
S = {(2^z,3^z) : z∈Δ} ⊂ ℂ².
```

Every rational-algebra endomorphism commuting with the two prime translations
is injective and has the unique form

```
F(a[z]) = σ(a) χ(z)[φ(z)].
```

Here `σ:ℂ→ℂ` is a scalar embedding preserving `S`, `χ:Δ→ℂˣ` is an arbitrary
character, and the additive injection `φ` is uniquely recovered from
`(2^(φz),3^(φz))=(σ(2^z),σ(3^z))`. Conversely, every such pair `(σ,χ)`
defines a commuting endomorphism. No continuity or real-line preservation
is assumed.

The common fixed subspace forces preservation of constants. Semilinearity
then makes the image of each character a joint eigenvector. Distinctness of
the spectrum forces a single exponent, and multiplication recovers both
`φ` and `χ`. Injectivity also follows directly from difference simplicity:
the kernel is a stable proper ideal and hence zero.

Preserving the augmentation ideal is exactly `χ=1`. Thus scalar restriction
identifies pointed commuting endomorphisms with scalar embeddings preserving
`S`. For automorphisms the condition is invariance in both directions:
`(σ×σ)(S)=S`. A commuting algebra automorphism restricts to an actual scalar
automorphism, and the lift of every admissible scalar automorphism is unique.
Fixing any ground subfield `K⊂ℂ` is precisely fixing `K` in this scalar action.

This gives an exact arithmetic descent problem on an explicit infinite
spectrum. It does not determine its stabilizer over the prime-side source
field, assert that arbitrary scalar automorphisms preserve it, or identify
functional reflection with conjugation.
[Scalar descent of prime translations](TheScalarDescentOfPrimeTranslations.lean).

### The maximal arithmetic quotient

Prime-time density does not make the prime points algebraic. For any
complex exponent `z` and any three distinct primes `p,q,r`,

```
p^z, q^z, r^z algebraic over ℚ  ⇔  z∈ℚ.
```

If `1,z` are rationally independent, the six-exponentials theorem applied
to those two rows and the three prime logarithms excludes simultaneous
algebraicity. For rational `z`, a positive integer power of each exponential
is rational.

Consequently a character subgroup `H≤Δ` has algebraic values at three
prime times exactly when `H≤R=Δ∩ℚ`; equivalently, all prime-time values
on `H` are algebraic. Algebraicity concerns the canonical form `ℚ[H]`,
or its character basis, rather than arbitrary complex coefficients.
The quotient with character group `R` is therefore maximal among these
arithmetic quotients. It has rational rank one and contains the unit weight.
Moreover `R` is saturated, so `Δ/R` is torsion-free.

On complex points, restriction gives the exact sequence

```
1 → (Δ/R)^∨ → Δ^∨ → R^∨ → 1.
```

Every admissible character restriction factors uniquely through `R^∨`.
Every actual zero lies outside `R`, since no zero is real. The kernel
contains the injective real family `u↦(z↦exp(u·Im z))`, witnessed by any
actual zero. Thus retaining three algebraic prime-time points forces a
proper quotient that loses a full family of ordinate characters.

The denominators occurring in `R` remain unknown; no finite-type assertion
is made. This classification does not identify conjugation with functional
reflection or prove purity.
[Maximal arithmetic quotient](TheMaximalArithmeticQuotientOfTheZeroMotive.lean).

### The prime spectral field and its effective action

Retaining every prime translation singles out the coefficient field

```
E = ℚ(p^z : p prime, z∈Δ) = ℚ(p^ρ : p prime, ξ(ρ)=0).
```

Integer relations add no generators beyond the original zero values:
exponent sums and negatives give products and inverses. A scalar embedding
lifts to a unique pointed map commuting with every prime exactly when,
for each `z∈Δ`, there is one `φ(z)∈Δ` satisfying
`σ(p^z)=p^(φ(z))` simultaneously at all primes. Two primes determine `φ`;
the remaining primes impose additional compatibility conditions.

Every such embedding preserves `E`. Two compatible embeddings induce the
same exponent action exactly when they agree on `E`. Thus the scalar
kernel invisible on exponents is precisely pointwise fixing of `E`.
Compatible scalar automorphisms in both directions restrict to automorphisms
of `E` and act by additive automorphisms of the full zero group.
The effective action is faithful after this restriction.

These actions fix more than the unit weight. Since rational constants are
fixed, the joint spectrum of `φ(1)` is `(2,3)`, giving `φ(1)=1`. Clearing
denominators then gives `φ(r)=r` for every `r∈R=Δ∩ℚ`. Consequently the field

```
E_rat = ℚ(p^r : p prime, r∈R)
```

is fixed pointwise by every compatible scalar embedding. It is real and
algebraic over `ℚ` and is a proper subfield of `E`: otherwise every prime value would
be algebraic, contrary to the three-prime theorem for an actual nonreal zero.
The full spectral field therefore contains a transcendental element.

Ordinary conjugation preserves the full prime spectrum and defines a
nonidentity automorphism of `E`. For each actual zero, at least one of its
values at two and three is nonreal; otherwise two-prime separation would
make that zero real.

The field uses actual prime-time values. Its mixed-prime polynomial relations,
its spectral stabilizer, and its relation to the contour-trace source field
remain open. No normality over `ℚ` or purity conclusion is asserted.
[Prime spectral field](ThePrimeSpectralFieldOfTheZeros.lean).

### Algebraic monomial relations across all primes

The prime spectral field has a constrained family of multiplicative relations.
For an integer vector `m` with finite prime support, write

`L(m)=Σ_p m_p log p`, `V_z(m)=exp(z L(m))`,
`K_z={m : V_z(m) is algebraic over ℚ}`.

Unique factorization makes `L` injective. The subgroup `K_z` is saturated:
if a nonzero integer multiple of a vector belongs, so does the vector.
For every actual zero `ρ`, any three vectors in `K_ρ` satisfy a nontrivial
integer relation. If `Re ρ` is irrational, any two do. These bounds concern
mixed products at every prime, with arbitrary positive and negative exponents.

Consequently two members of `K_ρ` have supports whose union contains the
support of every member. One member suffices when `Re ρ` is irrational.
Thus a fixed finite set `S_ρ` captures every algebraic monomial: any prime
product with a nonzero exponent outside `S_ρ` is transcendental.
The finite set is a conclusion about the entire prime family; no prime
cutoff enters the definition or proof.

The mechanism is the six-exponentials theorem. The first bound uses the
independent rows `1,ρ` and three prime-log frequencies. For the sharper
bound, `1,ρ,conjugate(ρ)` are independent when `ρ` is nonreal with irrational
real part; two independent frequencies would then give six algebraic
exponentials again. In particular, algebraicity of two distinct prime values
at an actual zero forces its real part to be rational.

Compatible arithmetic scalar embeddings preserve `K_z` exactly. Ordinary
conjugation and functional reflection also preserve it, since the value at
`1-z` is the rational prime product at one divided by the value at `z`.
This lattice therefore constrains arithmetic orbits but cannot alone
separate horizontally reflected zeros. Exact algebraic monomial values,
non-binomial relations, and the actual ranks and generators remain open.

[Algebraic prime relations](TheAlgebraicPrimeRelationsOfTheZeros.lean).

### A prime-source trace field with an actual zero action

The full mixed traces give a concrete ground field that forces the spectral
compatibility required above. At each absolute ordinate, retain both complete
fibres and every analytic multiplicity. For an integer prime vector `m`, take

`T_t(m)=Σ_{Im ρ=t or −t} exp(ρ Σ_p m_p log p)`.

Let `B` be the field generated by all these traces, over every height and every
prime vector. It is also the field generated by paired full-width germs of the
continued prime–archimedean source contour, tested against the entire function
`w ↦ exp((1/2+iw) Σ_p m_p log p)`. Admissible slabs and their stable complete-fibre
limits are proved; no analytic continuation or admissibility premise is left
in the field construction.

The full prime spectral field `E` is algebraic and normal over `B`. Newton
identities give the exact equations of each prime monomial on each paired
fibre. The compositum of all their splitting fields is `E`, with no terminal
height or finite-prime restriction. The field `B` is real, contains a
transcendental element over `ℚ`, and is strictly smaller than `E`.

Every embedding `E→ℂ` over `B` transports each zero's entire prime pattern to
one actual zero, retaining the absolute ordinate and the character divisor
with multiplicity. The mechanism is Dedekind independence: zeros give distinct
multiplicative characters of the free prime group, and equality of every mixed
trace determines their finite atomic measures. Independent permutations at
different primes cannot satisfy these trace identities.

Thus `Gal(E/B)` acts faithfully on the entire actual zero support. Ordinary
conjugation is a nonidentity member and acts as `ρ↦conjugate(ρ)`. Every group
element commutes with `ρ↦1−ρ` on zeros. This commutation does not assert that
functional reflection itself extends to a field automorphism.

An ambient scalar embedding fixing `B` automatically preserves the full prime
spectrum on the integer zero group. Its previously reconstructed exponent
map therefore sends actual zeros to actual zeros of the same absolute height.

The actual Galois group, its orbit partition, centrality of ordinary conjugation,
and a lift of functional reflection remain open. Neither normality nor the
source identification proves purity. Comparison with the earlier contour
power-trace field is a further arithmetic question.

[Prime trace Galois group](ThePrimeTraceGaloisGroupOfTheZeros.lean).

### Prime residue fields and reflection pairs

Over the complete mixed-trace base `B`, each actual zero has two concrete
arithmetic fields inside the normal spectral extension `E`:

```
F_ρ = B(p^ρ : p prime),
H_ρ = B(p^ρ + p^(1−ρ) : p prime).
```

Any two distinct prime values generate `F_ρ`; any two distinct symmetric
prime values generate `H_ρ`. More sharply, a single prime value generates
`F_ρ` exactly when it is nonreal. A single symmetric coordinate generates
`H_ρ` exactly when it is nonreal or `ρ` is critical. Each field therefore has
a primitive generator among its coordinates at any two distinct primes. These are finite extensions of `B`, attached
to every actual zero. Globally, two entire prime-coordinate families generate
all of `E` over `B`. The base still contains every mixed prime-source trace.

Their fixing subgroups are the stabilizer of `ρ` and the stabilizer of
`{ρ,1−ρ}`, respectively. Two-prime injectivity gives the first assertion.
For the second, equality of `p^z+p^(1−z)` leaves two possible prime values;
three primes force two choices to agree. Absolute-height preservation
then sharpens this to two primes: one exponential determines the real
part, leaving only the zero and its conjugate at that height. A nonreal
coordinate excludes the latter. Infinite Galois correspondence recovers
the fields and the sharp generator criteria from these stabilizers.

Reflection preserves `F_ρ`, and `H_ρ⊆F_ρ`. A prime coordinate distinguishing
`ρ` from `1−ρ` generates `F_ρ/H_ρ` and satisfies

```
X² − (p^ρ+p^(1−ρ))X + p = 0.
```

Consequently `[F_ρ:H_ρ]≤2`. The degree is two exactly when some arithmetic
automorphism exchanges `ρ` with `1−ρ`; otherwise the fields coincide.
This decides the local extension from the arithmetic orbit without assuming
a global field lift of functional reflection.

In the chosen complex embedding, `H_ρ` is real exactly when `Re ρ=1/2`.
In that case `H_ρ=F_ρ∩ℝ` and `F_ρ/H_ρ` is genuinely quadratic. Every
arithmetic conjugate of `H_ρ` is real exactly when the whole arithmetic
orbit of `ρ` lies on the critical line. Rational-weight rigidity below
proves that critical-line membership is arithmetic invariant and that
`H_ρ=B` at every critical zero. Universal realness remains open.
The ground field is transcendental over `ℚ`, so these
extensions are not asserted to be number fields.
[Prime residue fields](ThePrimeResidueFieldsOfTheZeros.lean).

### The prime reflection kernel and its lifting obstruction

Let `H` be the compositum of every reflection-pair residue field inside `E`.
It is normal over the complete prime-source trace field `B`. Restriction
is continuous and surjective, with exact sequence

```
1 → Gal(E/H) → Gal(E/B) → Gal(H/B) → 1.
```

For every prime and actual zero, write

```
U_(p,ρ) = p^ρ + p^(1−ρ),
d_(p,ρ) = p^ρ − p^(1−ρ),
D_(p,ρ) = U_(p,ρ)² − 4p.
```

Then `d²=D∈H` and `p^ρ=(U+d)/2`. Thus these actual radicals generate all
of `E/H`. Discard zero radicals and let `I` index the rest. The full kernel
is isomorphic, with its Krull topology, to

```
{ ε∈{±1}^I : ∏_{i∈S} ε_i=1 whenever ∏_{i∈S} D_i is square in H },
```

where `S` ranges over every finite subset of `I`. This characterizes
simultaneous signs on the infinite extension; it imposes every finite
relation and proves global realization. The kernel is abelian of exponent
two. At a fixed zero, products of two reflection differences already lie
in its pair field, so changing the prime preserves the discriminant square
class. Relations can still couple different pairs.

Conjugation acts on the sign group by conjugating zero labels. It centralizes
the whole orientation kernel exactly when `D_i D_conjugate(i)` is square in
`H` for every nonzero radical. This tests its action on the kernel; centrality
in the entire arithmetic group still requires control of the quotient.

Functional reflection lifts to an automorphism of `E/B` exactly when every
square product of nonzero discriminants has an even number of factors.
This is the condition for uniform sign reversal to respect all relations.
Whenever a lift exists, it is unique, central, nonidentity, and involutive.
The parity condition itself remains unproved.

Ordinary conjugation acts trivially on `H` exactly when all actual zeros
are critical. Consequently an existing functional-reflection lift equals
conjugation exactly under that same purity condition. A lift and purity
are distinct arithmetic questions: the first concerns square-class parity,
the second the conjugation action on the normal pair quotient.
[Prime reflection Kummer theory](ThePrimeReflectionKernelOfTheZeros.lean).

### Rational weights separate reflection orbits

The arithmetic action on actual zeros extends faithfully to their complete
integral relation group `Δ`. Each automorphism transports every prime
character, fixes the unit weight, and therefore fixes `Δ∩ℚ` pointwise.
Consequently all prime values of rational zero weights already lie in the
mixed-trace ground field `B`. This is an internal action of `Gal(E/B)`;
no extension of its elements to automorphisms of `ℂ` is needed.

This action gives a complete orbit classification for rational real parts:

`Gal(E/B)·ρ={ρ,conjugate(ρ)}` whenever `Re ρ∈ℚ`.

In particular, critical-line membership is invariant under the full
arithmetic action. This does not require conjugation to be central in
the full group. For rational real parts it also gives

`1−ρ ∈ Gal(E/B)·ρ  ⇔  Re ρ=1/2`.

For the mechanism, `q=2 Re ρ` is a fixed rational weight. The inverse image
`ζ=σ⁻¹ρ` has ordinate `±Im ρ`, so
`conjugate(ζ)=ζ∓(2ρ−q)`. Applying `σ` shows that `σcσ⁻¹ρ` has horizontal
displacement from `Re ρ` equal to `∓2(Re σρ−Re ρ)`. Thus the bounded set
of absolute horizontal displacements in the complete orbit is closed
under doubling. Its supremum forces every displacement to vanish.
Absolute-height preservation leaves exactly the conjugate pair.

The reflection-pair field equals the trace ground field exactly at critical
zeros: `H_ρ=B ⇔ Re ρ=1/2`. Every arithmetic conjugate of a critical zero
therefore remains critical. The global pair field equals `B` exactly when
all actual zeros are critical. A rational-real-part zero off the line has
`F_ρ=H_ρ`. Every prime
reflection difference then belongs to its pair field; its discriminant
is a square in the global reflection field. The difference is nonzero
off the line, giving a singleton odd square relation that obstructs the
uniform functional-reflection lift. Conversely, an off-line zero whose
reflection belongs to its arithmetic orbit must have irrational real
part. Its algebraic prime-monomial lattice has rank at most one and one
relation support contains all others; two algebraic prime values are
impossible there.

This constrains actual arithmetic orbits and the existing infinite Kummer
kernel. It does not assert rationality of zero real parts, existence of a
global reflection lift, or purity.
[Rational weights and arithmetic orbits](TheRationalWeightsOfPrimeZeroOrbits.lean).

### The rational-real-part residue layer

Let `L_rat` be the subfield of the prime spectral extension generated over
`B` by all prime values at actual zeros with rational real part. This is a
field of nonreal zero exponents, distinct from the rational-weight prime
field. It contains the full residue field of every critical zero.

Each individual residue field in this layer is quadratic over `B`.
Rational-orbit rigidity places the conjugate-pair trace
`u=p^ρ+conjugate(p^ρ)` and norm `v=p^(2 Re ρ)` in `B`. A nonreal prime
coordinate generates the full residue field and satisfies `X²−uX+v`;
its degree cannot be one because `B` is real.

For every nonreal coordinate, `d=p^ρ−conjugate(p^ρ)` has square
`D=u²−4v∈B`, strictly negative in the chosen real embedding. These actual
radicals generate all of `L_rat`. Its entire Galois group, with its Krull
topology, is the sign group satisfying every finite discriminant
square-product relation. The extension is therefore abelian of exponent
two. Restriction from `Gal(E/B)` is continuous and surjective.

Ordinary complex conjugation is exactly uniform radical negation. Every
square product has even cardinality, and this uniform negative assignment
has a unique realization. Thus conjugation is central on the whole layer,
including the entire critical-zero residue field. Rationality of all real
parts, equality `L_rat=E`, and centrality on the remaining extension are
not asserted.
[Rational residue layer](TheRationalResidueLayerOfTheZeros.lean).

### The even-product field of original centered zeros

There is a separate field construction directly over `ℚ`. Let
`a_ρ=ρ−1/2`, let `L=ℚ(a_ρ : ρ an actual zero)`, and let
`K=ℚ(a_ρ a_τ : ρ,τ actual zeros)`. These fields use the entire divisor;
`K` is defined from zero products and is not identified with a prime-source
field.

Every anchor `a_ρ` is nonzero and generates `L` over `K`: each other
centered zero equals `(a_τ a_ρ)/a_ρ`. Thus `[L:K]≤2`. The degree is two
exactly when the anchor is outside `K`, a criterion independent of the
anchor. In that case quadratic conjugation negates every centered zero
and realizes the actual functional equation on the original coordinates.

Conversely, any rational field automorphism negating all centered zeros
fixes every even product. Such a lift exists exactly when `a_ρ∉K`; it is
unique, and its fixed field is precisely `K`. This classifies the lifting
obstruction without assuming that the geometric permutation preserves
all field relations.

Ordinary complex conjugation preserves both fields. The even-product
field is real exactly when every actual zero is critical. For the forward
implication, an unconditionally existing critical zero supplies a nonzero
purely imaginary anchor; reality of its product with every other centered
zero forces each real part to vanish. The converse follows directly from
the products. Neither reality of `K` nor exclusion of its anchors is assumed.
[Even-product field](TheEvenProductFieldOfTheZeros.lean).

### Functional-equation descent and coefficient weight

The permutation `ρ↦1−ρ` of zeros need not preserve their integer additive
relations. Retain coefficient weight by forming

```
R = ⟨(ρ,1) : ξ(ρ)=0⟩ℤ ⊆ ℂ×ℤ,
D = {n∈ℤ : (0,n)∈R}.
```

Projection `R→Δ` is onto. Functional-equation reflection always acts on
`R` by `(z,n)↦(n−z,n)`. The subgroup `D` records precisely the coefficient
weights of relations with zero complex value. Embedded as integer values
in `Δ`, it is the exact obstruction to descending reflection.

The following conditions are equivalent:

- `D=0`;
- coefficient weight descends to a homomorphism `Δ→ℤ` sending every zero to one;
- reflection of every zero extends to an additive automorphism of `Δ`;
- `(1/2)ℤ ∩ iΓ = {0}`.

The last condition isolates an additive obstruction inside the centered
integer span. It requires less than excluding `i` from the entire centered
field, which also contains products and quotients of zeros.

There is an unconditional replacement: `Δ/D` carries reflection. It is
universal among additive quotients admitting the specified action on every
zero. A complex character `χ` of `Δ` admits a reflected character precisely
when `χ(n)=1` for all `n∈D`. For the real-time exponential flow, this becomes

```
reflection of χᵤ exists  ⇔  u=0 or D=0.
```

Thus even one nonzero real-time character detects the entire descent
obstruction. The actual subgroup `D` remains undetermined; the functional
equation alone supplies its augmented lift, not its vanishing.
[Reflection descent](TheDescentOfFunctionalEquationReflection.lean).

### Euclidean topology and arithmetic action

Give `L` its inherited complex topology while keeping the Krull topology on
`Gal(L/K)`. The Euclidean-continuous source automorphisms are exactly `1`
and `c_L`; equivalently, these are exactly the automorphisms bounded on the
whole field's unit ball. Every other source automorphism satisfies

```
∀ ε,M>0, ∃ z∈E: |z|<ε and |σ(z)|>M.
```

Indeed `Gal(L/E)={1,c_L}` by closed-subgroup Galois correspondence.
An automorphism outside this pair moves a real `a∈E`. Rational approximation
makes `N(a−q)` arbitrarily small while its image becomes arbitrarily large.
Yet every source automorphism moves every centered zero by less than one:
ordinate preservation and the open strip bound control the whole zero carrier.
Any action outside `{1,c_L}` would obey this bound while remaining unbounded
near zero on the generated field.

Every fixed-element orbit map from the Krull group is continuous. Joint
continuity of `Gal(L/K) × L → ℂ`, or continuity of every individual field
automorphism, is equivalent to `E=K`. In that case the group has at most two
elements. This locates the exact obstruction to treating the arithmetic action
as an analytic action; it neither identifies `E` with `K` nor asserts that an
automorphism outside `{1,c_L}` exists.
[Euclidean action and amplification](TheEuclideanTopologyOfTheZeroField.lean).

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
