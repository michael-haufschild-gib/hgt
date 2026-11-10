# Carlitz–Goss RH from greedy compositions

- **Stage:** 1-in-progress
- **Source:** review-0911 §11.4.

## Exact target

For every prime power `q=p^s`, `s>0`, and every `y∈ℤ_p`, the zeros in `x`
of the Goss zeta function of `𝔽_q[T]` are simple and belong to
`𝔽_p((T⁻¹))`. The domain for `x` is the nonzero elements of the completed
algebraic closure of `𝔽_q((T⁻¹))`.

## Proof dependencies

[Sheats, Theorems 1.1–1.4 and §2](https://arxiv.org/pdf/math/9801158):

1. Among carry-free compositions of `N`, with all but the final part
   positive and divisible by `q−1`, the reversed-lexicographic maximum
   uniquely maximizes the weighted sum of the parts.
2. Finite-field power sums and Lucas's theorem identify the leading
   coefficient of each monic-polynomial power sum. The unique maximum
   prevents cancellation.
3. Greedy-composition inequalities give strictly increasing consecutive
   coefficient valuations. For general `y∈ℤ_p`, digit truncations stabilize
   those valuations.
4. Every Newton-polygon segment has horizontal length one. Its root is
   simple and belongs to the coefficient field.

`SignFreePurityMechanisms/SeparationForcesRationality.lean` supplies a
polynomial Galois-invariance principle. The same owner's
`TheUltrametricNewtonPolygonSeparatesTheRoots.lean` proves simplicity,
separation and splitting of polynomials with strictly log-concave
coefficient norms (`HasSimpleSlopes.derivative_eval_ne_zero`,
`splits_of_strict_logConcave`). The composition theorem, actual Goss
coefficients and passage to the entire series remain necessary.

## Lean status

Modules under `SignFreePurityMechanisms/CarlitzGoss/`:

| Module | Proved statement |
|---|---|
| `DigitContents` | Positive integer divisibility by `p^s−1` iff its content is `Ea` with positive integral `a`; explicit inverse and integrality propagation |
| `ContentRounding` | `exists_integral_content_layer`: inverse coordinates `>m≥1` admit a proper positive integral layer with inverse coordinates `≥m` |
| `ContentPartitions` | `hasContentPrefix_iff`: `k` divisible positive parts and an unrestricted positive last part exist iff every inverse-content coordinate exceeds `k` |
| `DigitAllocations` | `tokenPrefix_iff_inverseContent`: the vector criterion partitions actual finite digit occurrences |
| `DigitValues` | Divisible content iff divisible integer value; `digitTokenPrefix_iff` for the canonical base-`p` digits of every `N` |
| `DigitCompositions` | Indexed carry-free compositions satisfy the same criterion; both maxima exist; greedy and optimal coincide for two parts |
| `DigitExchanges` | Same-residue swaps preserve content; exact weight change; greedy and optimal allocations are increasing within each residue class; every realized content matrix admits an increasing allocation |
| `IncreasingAllocations` | Increasing allocations of a fixed content matrix have unique numerical part values, by equality of all prefix values |
| `InitialCompositions` | Deleting the last part preserves greediness and optimality; admissible replacements of the initial composition retain divisible parts |
| `ContentBounds` | A proper sublayer of constant content `p−1` has every inverse coordinate `<1`; divisible content has integral inverse coordinates |
| `TopDigits` | Digits below exponent `k` have value `<p^k`; the whole highest digit block has value `>N/2` and content at most `p−1` in each class |
| `LastBlockOperations` | Adding a common last block preserves reverse lexicographic comparisons; deleting digits from a still nonempty last part preserves optimality and greediness |
| `TopBlockFeasibility` | Every nonempty content layer bounded by `p−1` fits in the last part of a divisible composition; some last part has value `>N/2` |
| `GreedyWeightBounds` | For divisible total `N`, every greedy or optimal `m`-part composition satisfies `(m−1)N<weight≤mN` |
| `PrefixBoundary` | The initial prefix has minimum inverse coordinate exactly `m−1`; last-part deletion remains feasible iff that part stays nonempty |
| `CommonCoordinate` | All proper parts of an optimal or greedy composition share an inverse-content coordinate equal to one |
| `SingleResidueOptimality` | For `q=p`, greediness is equivalent to weight optimality and maximizing numerical part values are unique |
| `BoundaryFeasibility` | A non-strict inverse threshold gives either a positive last remainder or one fewer part with divisible total; one integral inverse coordinate forces integrality everywhere |
| `DigitShifts` | Exponent shifts preserve cardinality and divisibility, scale values by a power of `p`, and translate content and inverse-content coordinates |
| `ShiftCompositions` | Exponent shifts preserve optimality and greediness; a suitable shift moves the common inverse-content coordinate to zero |
| `PowerSelection` | Powers dividing a target contain an exact target-sum subcollection once their total reaches it; the same selection applies to cyclic weighted digit contents |
| `LastResidueMaximum` | An occupied last-part residue contains a largest available power; equal-power labels can be aligned without changing values, and common deletion preserves equality of value vectors |
| `BlockExchanges` | Congruent nonempty blocks can be exchanged; exact weight change forbids a larger congruent block in an earlier part of an optimum |
| `CyclicOrder` | Changing the origin cannot reverse the cyclic order of three residue classes |
| `ResidueBlockObstruction` | Equal cyclic weighted contents imply congruent values; a later part of smaller powers cannot attain an earlier digit's residue weight using only smaller residue weights |
| `DeletionReduction` | A shared last-part residue produces a smaller nongreedy optimum by digit or part deletion; disjoint last residues force a larger greedy last-part digit |
| `TwoDigitFeasibility` | A non-strict threshold after two-digit deletion reserves either digit for the last part; reserving a larger power yields a smaller nongreedy optimum |
| `MinimalCounterexamples` | Any nongreedy optimum yields a normalized least counterexample with at least three parts and two residues, disjoint last residues, and a deficient coordinate after each relevant two-digit deletion |
| `DeficientCoordinates` | A deficient two-digit deletion pins both divisible prefixes to the integral boundary; last-part cyclic weights agree and lie below the combined deleted weights |
| `DeficientOrder` | At a deficient coordinate, a larger available digit precedes the deleted last-part digit in cyclic order; the opposite order would admit an improving congruent block exchange |
| `SingletonLast` | A minimal nongreedy optimum has a singleton last part: two distinct last-part digits would force opposite cyclic orders around a larger greedy digit |
| `NormalizedLast` | When proper parts have zeroth inverse coordinate one, a singleton last part and any competing last part containing another digit have equal zeroth cyclic weight |
| `MinimalStructure` | Any nongreedy optimum yields a normalized counterexample with singleton last part `p^k`; the greedy last part contains a larger power, has equal zeroth cyclic weight, and uses only residues below `k mod s` |
| `PrefixCarryRecursion` | Descending inverse-prefix rows preserve the floor, nested nonnegative content, and `p−1` digit gaps; the boundary loses at least `p` terminal digits |
| `ContentMatrixRealization` | Every admissible content matrix has an increasing allocation of the actual digit collection |
| `GeometricPrefixCost` | Exponent gaps bound total prefix weight by the finite double-geometric sum |
| `ResiduePrefixGaps` | Removing `n(p−1)` largest occurrences of one residue lowers retained exponents by at least `ns` |
| `SingletonBoundary` | Every singleton boundary fixes competing last-part cyclic weight and excludes smaller residue representatives |
| `SingletonInverseGap` | At the singleton residue, its proper prefix exceeds the competing prefix by exactly one inverse-content unit |
| `ResiduePrefixCost` | Residue-count gaps give the double-geometric bound for actual base-`p` prefix values, including empty prefixes |
| `GeometricCarryGain` | The terminal geometric bound and prefix estimate imply a strictly positive gain for all `p≥2`, `q≥p²` |
| `IntegralPrefixContents` | Actual proper prefixes have integral inverse coordinates with positive increments; a last minimal coordinate selects the carry interval |
| `CarryInterval` | The complete interval recursion preserves inverse floors and content gaps; terminal content gains one at the top and loses digits below |
| `SingletonCarryBoundary` | Actual normalized singleton and competing compositions determine the carry interval and contain the competing last support within it |
| `PrefixMatrixRealization` | Integral inverse prefixes with positive increments, nested contents, and a positive last remainder yield an actual increasing composition with those exact prefixes |
| `PrefixWeightIdentity` | Weight differences are the reversed differences of the sums of actual proper-prefix values |
| `CarryModifiedComposition` | Actual normalized compositions admit an increasing carry modification with unchanged outside prefixes, singleton absorption at the top, terminal digit loss below, and all positive prefix gaps |
| `IncreasingPrefixCosts` | Actual increasing compositions satisfy the geometric residue-prefix cost and the retained-to-last exponent gap; equal outside prefix counts give equal values |
| `CarryWeightComparison` | The actual singleton carry modification strictly increases weight, by cancellation of unchanged prefixes and the two geometric bounds |
| `GreedyOptimality` | For every `p≥2`, positive residue degree and composition length, greedy compositions are exactly the weight maxima; maximizing numerical part values are unique |
| `PrefixCostGrowth` | Consecutive greedy prefix costs more than double and have strict successive slopes; the greedy cost of a divisible total is below that total |
| `MonicPowerSums` | Exact binomial recurrence for the actual polynomial power sums over all monic polynomials of a fixed degree; all finite-field coefficient moments evaluated |
| `CarryFreeBinomial` | In every ring of prime characteristic, a binomial coefficient is nonzero exactly when the lower argument's base-`p` digits fit coordinatewise inside the upper argument's digits |
| `DigitSelection` | Those nonzero binomial coefficients correspond exactly to values of actual subsets of the given digit collection |

Listed modules passed direct Lean checks and are wired into the umbrella.
Transitive axiom audits through `CarryFreeBinomial` use only the three
standard axioms. No further axiom audit was run for `DigitSelection`.

General greedy optimality is formalized and audited; see
`../3-formalized/greedy-carry-free-compositions-are-uniquely-optimal.md`.
The actual Goss coefficient valuations, their identification with the proved
strict combinatorial slopes, and the entire-series argument remain. The target
includes every prime power and every `p`-adic parameter.

## Combinatorial mechanism

Write `Γ(N)_h` for the number of base-`p` digits of `N`, counted with
multiplicity, whose exponents are `h mod s`. Put
`(Ea)_h=p a_{h+1}−a_h`, with cyclic indices. The entries of `E⁻¹` are
positive; its rows are the cyclic rotations of `(1,p,…,p^(s−1))/(p^s−1)`.
Thus `Γ(N)` is the content of a positive `(q−1)`-multiple precisely when
`E⁻¹Γ(N)` has positive integral coordinates. A carry-free composition
into `m` positive parts, the first `m−1` divisible by `q−1`, exists
precisely when `min(E⁻¹Γ(N))>m−1` (Sheats, Proposition 4.3).

The rounding step has a closed form. For `u=Ec≥0` integral and
`c_h>m≥1`, put `b_h=⌈c_h⌉−1` and
`d_h=min_{0≤k<s} p^k b_{h+k}`. Then `m≤d_h<c_h` and
`d_h=min(b_h,p d_{h+1})`. If `d_h=p d_{h+1}`, then `(Ed)_h=0`;
otherwise `d_h=b_h` and `(Ed)_h<u_h+1`, hence `(Ed)_h≤u_h` by
integrality. Thus `0≤Ed≤u`, with both `Ed` and `u−Ed` nonzero by
invertibility of `E`. This supplies the recursive decomposition into
positive divisible parts without choosing a coordinate of minimum `c`.

The constant content layer `ρ_h=p−1` has `E⁻¹ρ=1`. If `v≤ρ` and
`v≠ρ`, positivity of every entry of `E⁻¹` gives `E⁻¹v<1` in every
coordinate. Removing such a layer from content with inverse coordinates
at least `m` leaves the strict feasibility threshold `>m−1`. In the
boundary case `v=ρ`, the remainder is still divisible and has inverse
coordinates at least `m−1`.

For divisible `N`, take the whole highest base-`p` digit block. It exceeds
`N/2` and its content is bounded by `ρ`. The preceding dichotomy constructs
an admissible composition whose last part contains this block. Thus the
greedy last part exceeds `N/2`; induction on the initial composition gives
`(m−1)N<wt(G)≤mN`. The same lower bound holds for every optimum.
Consequently, an optimal or greedy composition's initial prefix cannot
admit another part: otherwise repartitioning that prefix and enlarging the
last part improves weight or reverse lexicographic order. Its minimum
inverse-content coordinate is exactly `m−1`, so all first `m−1` parts
share a coordinate equal to one. These are the boundary facts needed
before the minimal-counterexample argument.

For `s=1`, that coordinate is the entire inverse vector. Each proper part
therefore has exactly `p−1` digits. Every optimal or greedy composition has
the same content matrix, including its final column by subtraction from
the total. Uniqueness of increasing allocation proves greedy optimality
and uniqueness of numerical part values for `q=p`.

For a fixed content matrix, increasing allocation uniquely maximizes weight.
Choose a nongreedy optimum minimizing first the number of parts, then digits.
A common last-part residue permits common deletion, contradicting minimality.
Thus the two last supports are disjoint, and the greedy last part has a larger
digit `y`. Deleting `y` and any optimal last-part digit `x` must make some
inverse coordinate deficient. Integrality pins both proper prefixes to the
same boundary there. Their last-part cyclic weights agree and are below the
combined weights of `x,y`; an improving block exchange forces `y` to precede
`x` in cyclic order. Two distinct optimal last-part digits would force opposite
cyclic orders, so that part is a singleton `p^k`.

Shift the common proper-part inverse coordinate to zero. Deleting the
singleton and a greedy last-part digit is then deficient at zero itself,
giving equal zeroth cyclic weights. Positivity and disjoint residue supports
put every greedy last-part residue below `β=k mod s`. These are the formalized
structural conclusions of Proposition 5.1.

For prefix contents `θ_j` and `w_j=E⁻¹θ_j`, choose `α<β` with
`w_{α,m−1}=m−1` and `w_{h,m−1}>m−1` for `α<h≤β`.
Keep the coordinates outside `(α,β]`. Within it, descending recursion
`d_{h,m−1}=min(w_{h,m−1}−1,p d_{h+1,m−1})` and
`d_{h,j}=min(d_{h,j+1}−1,p d_{h+1,j})` gives admissible prefix contents
`δ_j=Ed_j`. Their increasing digit allocation defines another composition
`Z`. Successive nonzero prefix contents in each affected class differ
by at least `p−1` digits (Lemma 6.2).

The exact prefix-weight identity cancels unchanged residues. The geometric
estimate below bounds the remaining losses and gives `wt Z>wt O`
uniformly for `p≥2`, contradicting optimality.

For the optimality proof, a carry-free digit collection can be represented
by a finite subset of `ℕ×Fin(p−1)`: `(e,r)` has value `p^e` and colour
`e mod s`. Each exponent occurs at most `p−1` times. An admissible
composition partitions this set into nonempty parts, all but the last
having value divisible by `p^s−1`. Its weight is the sum of part values
times their one-based positions. Deletion and exponent shifts preserve
this model, so minimality can use `(number of parts, number of digits)`.

## Geometric prefix-cost argument

Put `q=p^s`, so `q≥p²`, and `c=(p−1)q/(q−1)²`. In one residue class,
suppose nested prefixes have positive counts increasing by at least `p−1`.
If the terminal prefix's largest digit is `p^e`, the sum of all preceding
prefix values is at most `c p^e`. Indeed, a digit at exponent `e−sℓ`
can occur in at most `ℓ` preceding prefixes; there are at most `p−1`
occurrences per exponent. The finite weighted geometric identity bounds
their total by `(p−1)q p^e/(q−1)²`.

For the carry modification above, let `P` be the largest digit in the new
last part and `S` the sum of the retained terminal digits in residues
`α,…,β−1`. The greedy last part is supported in this interval: the boundary
coordinate `w_{α,m−1}=m−1` fixes its cyclic weight to `p^(β−α)`, excluding
every residue below `α`. Every occupied residue in this interval loses digits
under the modification, so the new last part contains its largest available
digit. Hence `P≥p p^k`. Losing at least `p−1` digits also gives a full
residue-degree gap, so `S≤pP/(q(p−1))`.

The affected residue `β` has retained terminal digit `p^k`; unchanged
residues cancel in the weight difference. Thus
`wt(Z)−wt(O)≥P−(1+c)p^k−cS`, which is positive because
`(1+c)/p + cp/(q(p−1)) < 1`. After clearing positive denominators, this is
`(p−1)(q²−3q+1)>p²`; it follows from `q≥p²≥4` and
`(p−1)(p²+1)−p²=(p−2)p²+p−1>0`.
This bound handles `p=2` without a separate equal-degree case.

`CarryWeightComparison.exists_strict_weight_improvement` formalizes this
comparison for the actual compositions. Its direct check and transitive
axiom audit use only the three standard axioms.

## Actual coefficient reduction

For `S_d(N)=Σ_{a monic, deg a=d} a(T)^N`, separating the constant
coefficient and summing its powers over `𝔽_q` gives
`S_0(N)=1` and
`S_{d+1}(N)=−Σ_{1≤j≤N, (q−1)|j} binom(N,j) T^(N−j) S_d(N−j)`.
Iterating yields the multinomial expansion indexed by `d` positive
`(q−1)`-multiples and a nonnegative final remainder. Lucas's theorem
selects the carry-free terms. Their polynomial degree is composition
weight minus `N`.

The final remainder may be zero, whereas `DigitComposition` requires
positive parts. A zero remainder forces `(q−1)|N`. If a positive-remainder
composition exists, its greedy weight is `>dN`; every zero-remainder
composition has weight `≤dN`. Otherwise the zero-remainder terms are
exactly the admissible `d`-part compositions, since divisibility of `N`
forces their final part divisible too. Thus the positive-part optimality
theorem covers both cases.

`MonicPowerSums.lean` formalizes the recurrence on actual monic polynomials
in `monicPowerSum_succ`. The finite-field moment is zero at exponent zero
and otherwise equals `−1` exactly on multiples of `q−1`. Its direct check
and transitive axiom audit pass. `CarryFreeBinomial` formalizes the Lucas
nonvanishing criterion, and `DigitSelection` realizes it by actual digit
subsets. Leading-coefficient identification and valuation stabilization remain.

## Greedy prefix-cost growth

Write `v(C)=mN−wt(C)` for an `m`-part composition of `N`, and `P(C)`
for the value of its proper prefix. The greedy weight bound on that
divisible prefix gives `v(C)<2P(C)`. For consecutive greedy compositions
`C,D` on the same digits, merge the last two parts of `D`. Greediness of
`C` and the half-total bound on `D`'s initial composition give
`2P(C)<P(D)`. Optimality of `C` against that merge gives
`v(D)−v(C)≥P(D)`. Hence `v(D)>2v(C)`, which implies strict successive
slopes since all prefix costs are nonnegative. For divisible total `N`,
the half-total bound also gives `v(C)<N`; the zero-remainder endpoint's
increment `N` is therefore strictly larger than the preceding slope.

`PrefixCostGrowth` formalizes the doubling, strict-convexity, and
divisible-total inequalities. Its direct check and three endpoint axiom
audits pass. Identifying them with the actual coefficient valuations remains.

## Digit-selection bridge

For a finite set `S⊆ℕ×Fin(p−1)`, let `N=Σ_{x∈S}p^x.exp`.
Its digit in position `e` is exactly the number of occurrences of exponent
`e`: lower powers sum to less than `p^e`, and higher powers are divisible
by `p^(e+1)`. Lucas's theorem therefore makes `binom(N,k)` nonzero in
characteristic `p` exactly when every digit of `k` is at most the available
occurrence count. Independent selection in each exponent fibre then gives
`T⊆S` of value `k`. In `DigitSelection.lean`, `cast_choose_ne_zero_iff_subset`
proves this bridge for every ring of prime characteristic. Its source passed the
direct Lean check without an additional axiom audit.
