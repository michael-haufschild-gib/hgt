# The theta compact inverse has an infinite zero-Jordan history

- **ID:** `theta-compact-inverse-zero-jordan-history`
- **Stage:** 2-fully-proven (paper)
- **Type:** THEOREM and operator-architecture obstruction
- **Routes:** STC, CSB, U, K-RVM, MPLF, RHist, theta source transport
- **Status:** `[PROVED HERE ON PAPER] [LEAN FORMALIZATION OPEN] [NOT AN RH PROOF]`
- **Dependencies:** the literal theta density and all-order first-atom derivative bounds in `ThetaCuspFirstAtomAllOrderApproximation.lean`; the positive source envelope in `HedenmalmThetaKernelEnergy.lean`; the source/quantile inverse identity in `HedenmalmShiftedSourceEquation.lean`; density of the centered inverse range in `HedenmalmClosedWeightedDerivative.lean`; ordinary `L²` theta translation cyclicity in `XiThetaL2Cyclicity.lean`.

## Theorem

Let `k` be the literal positive even completed-theta density, `M=∫ℝ k`,
and let `H_s=L²(ℝ,k(x)⁻¹dx)`. Write `U:H_s≃L²(0,1)` for the source
quantile unitary and `B` for its compact pinned source inverse. For
every integer `r≥0`, put

```text
v_r = U(k⁽ʳ⁾).
```

These are well-defined Hilbert vectors, are linearly independent,
and satisfy the **exact infinite Jordan chain at zero**

```text
B v₀=0,                 B v_r=i v_(r−1)   (r≥1).         (1)
```

Here `v₀=√M·1` and `v_r` has zero mean for every `r≥1`. On the
mean-zero quotient `H₀=1⊥`, let `D=P B|_(H₀)`. Then

```text
D v₁=0,                 D v_r=i v_(r−1)   (r≥2),        (2)
```

so the determinant-bearing quotient itself has an infinite
zero-Jordan chain.

Both `B` on `L²(0,1)` and `D` on `H₀` have dense range and
nontrivial kernel. Consequently their adjoints are injective,
and **neither operator has a bounded injective intertwiner with
its adjoint**:

```text
There is no bounded injective G with GB=B*G;
there is no bounded injective G₀ with G₀D=D*G₀.  (3)
```

In particular, no bounded positive injective or bounded coercive
Hilbert metric can symmetrize the full inverse or its quotient.
This is unconditional and uses no assertion about locations of Xi
zeros. It does not rule out unbounded metrics, degenerate forms,
or a different source-faithful carrier.

There is a canonical candidate for such a different carrier. Let
`R` be the closed linear span of the vectors `v_r`, `r≥0`.
It is a proper `B`-invariant subspace, `B|_R` is quasinilpotent,
and the compact quotient operator `B̄` on `L²(0,1)/R` retains
**every nonzero Xi eigenvalue with its algebraic multiplicity**.
This quotient removes the zero-Jordan history before asking a
spectral-reality question; it is defined from the literal source
without selecting or assuming any zero.

The zero-history space also has an exact **translation boundary**.
For real `a`, set `k_a(x)=k(x+a)` and `a_*=log(2)/2`. Then

```text
k_a ∈ H_s  ⇔  |a|<a_*;
R = closure span{U k_a : |a|<a_*}.                    (4)
```

Every prime dilation has `a=log p≥log 2>a_*`, so its literal
translate is outside `H_s`. More generally, a nonzero finite
combination of distinct positive prime translates is outside
`H_s`. Thus the exact quotient kills every source-admissible
local translation, whereas no literal prime translation is even a
vector on this Hilbert carrier. Prime arithmetic can reach its
nonzero divisor only through a singular/rigged extension or a
different carrier; extending the local translation calculus inside
`H_s` cannot supply the missing orientation.

## Weighted derivative admission

For fixed `r`, the complete theta derivative obeys a first-atom
relative bound on the positive tail: the all-order first-atom
decomposition gives constants `C_r,d_r,x_r` such that

```text
|k⁽ʳ⁾(x)| ≤ C_r exp(d_r x) k₁(x)      (x≥x_r),
k(x) ≥ c k₁(x) > 0,
```

where `k₁` is the explicit first Gaussian theta atom. Its
double-exponential factor `exp(−π exp(2x))` makes
`exp(2d_r x)k₁(x)` integrable. Therefore

```text
∫_(x_r)^∞ |k⁽ʳ⁾(x)|²/k(x) dx < ∞.
```

Evenness of `k` transfers the same estimate to the negative tail;
the compact middle interval is harmless. The same Gaussian
derivative bounds show `k⁽ʳ⁾(x)→0` at both ends. For `r≥1`,
the fundamental theorem of calculus then gives
`∫ℝ k⁽ʳ⁾=0`. These facts justify every vector and integral in
(1), without a formal derivative of the coarse action asymptotic.

## Exact source action and quotient chain

In source coordinates the inverse is

```text
(B_s f)(x)=i ∫_(−∞)^x [f(y)−M⁻¹(∫ℝ f)k(y)]dy.
```

For `f=k`, the bracket vanishes identically. For `f=k⁽ʳ⁾`,
`r≥1`, its total integral is zero, so the endpoint identity
above gives

```text
B_s k⁽ʳ⁾=i k⁽ʳ⁻¹⁾.
```

The corpus's source/quantile inverse identity transports this to
(1). Since `U k=√M·1` and
`⟨1,U(k⁽ʳ⁾)⟩=M⁻¹/²∫ℝ k⁽ʳ⁾=0` for `r≥1`, projection kills the
last step `Bv₁=i v₀` and leaves every later step unchanged,
proving (2). The vectors are independent: if a finite linear
combination ending at `v_N` vanished, applying `B^N` would
force its top coefficient to vanish because `B^N v_N=i^N v₀≠0`;
descend inductively. In particular `v₁≠0`.

## Sharp translation boundary and history orbit

The first-atom asymptotic already present in the corpus gives,
using evenness and the explicit seed polynomial,

```text
k(T) ~ 4π² exp(9T/2 − π exp(2T))       (T→+∞).
```

For `a>0`, the dangerous tail of the weighted norm is `x=−T`:

```text
|k(−T+a)|²/k(−T)
  ~ 4π² exp(9T/2−9a)
       · exp(−π(2 exp(−2a)−1) exp(2T)).
```

The positive tail has coefficient `2 exp(2a)−1>0` and is
integrable. The displayed negative tail is integrable precisely
when `2 exp(−2a)>1`. At equality its remaining factor grows as
`exp(9T/2)`, so the boundary is excluded. Reflection gives the
same criterion for `a<0`, proving the first part of (4). If
`a_1<⋯<a_m` are positive and the last coefficient is nonzero,
`k(x+a_j)/k(x+a_m)→0` as `x→−∞` for every `j<m`;
the largest shift therefore cannot be canceled by the others.

For the second part of (4), write `k(w)` by its all-integer theta
series, holomorphic for `|Im w|<π/4`; the real modular reflection
identity extends holomorphically in that strip. Uniform first-atom
tail estimates show that

```text
a ↦ k(·+a) ∈ H_s
```

is a Hilbert-holomorphic map on the connected open domain
`Ω={a∈ℂ: |Im a|<π/4, 2 exp(−2|Re a|) cos(2 Im a)>1}`. This domain contains
the entire real admissible interval. Its Taylor coefficients at
zero are the admitted vectors `k⁽ʳ⁾`. Hence any bounded linear
functional annihilating every derivative vanishes on the map near
zero and, by the identity theorem, throughout `Ω`. Hahn–Banach
implies every admissible real translate belongs to the closed
derivative span. Conversely derivatives are norm limits of finite
difference combinations of these translates; both closed spans
are equal. This proves (4) without a zero-location premise.

The same asymptotic gives a transport law for the entire weighted
Hilbert scale. Define `H_q=L²(ℝ,k(x)^(−q)dx)` for `q>0` and
`T_a f(x)=f(x+a)`. For `a≠0` and `q,q'>0`,

```text
T_a:H_q→H_(q') is bounded  ⇔  q'<q exp(−2|a|).       (5)
```

Indeed its squared operator norm is the essential supremum of
`k(y−a)^(−q')/k(y)^(−q)`. The two tails have leading
double-exponential exponents proportional to
`q' exp(−2a)−q` and `q' exp(2a)−q`; strict negativity at
both ends is exactly (5). At equality on the dangerous tail,
the remaining factor grows like
`exp((9/2)(q−q')|y|)`, so boundedness fails. For `a=0`,
boundedness is simply `q'≤q`. A prime shift thus loses at least
the weight exponent factor `p^(−2)`, with strict slack. In
particular no nonzero translation acts boundedly on a fixed
`H_q`, and all-prime transport naturally belongs to a graded or
rigged family of spaces rather than one Hilbert operator.

There is a second, less obvious price of that grading. For every
`0<q<2`, the same tail calculation and holomorphic-orbit proof give

```text
k_a∈H_q  ⇔  |a|<log(2/q)/2,
closure_(H_q) span{k⁽ʳ⁾:r≥0}
  = closure_(H_q) span{k_a:|a|<log(2/q)/2}.          (6)
```

For any **finite** prime set, choose `q>0` small enough that all
its shifts `log p` satisfy (6). Its finite Euler combination of
translated source vectors then lies in the derivative-history
closure at that level. Thus grading admits finite arithmetic
translations but does not make their source orbit visible after
quotienting by zero-history. The unresolved arithmetic operation
is the singular infinite-prime completion and its failure to
commute with the source-history quotient; (5) alone does not
orient a Xi eigenvalue.

At the unweighted endpoint, the Hilbert history quotient vanishes,
but its tempered dual annihilator is precisely the real Xi divisor
with multiplicity. The full endpoint classification is (7)–(8)
below.

At the unweighted endpoint this quotient undergoes a sharp
collapse. Put `H_0=L²(ℝ,dx)` and let `R_q` denote the closed span
of all derivatives `k⁽ʳ⁾` in `H_q`. Then

```text
R_q ≠ H_q  for every 0<q<2,       R_0=H_0.          (7)
```

For `q>0`, choose any real Xi zero `z` (its existence is already
formalized in the corpus via Hardy's theorem). The evaluation
`L_z(f)=∫ f(x) exp(izx)dx` is bounded on `H_q`, because
`∫k(x)^q dx<∞`; it is nonzero and annihilates all derivatives
by integration by parts and `XiC(z)=0`. Thus `R_q` is proper.

At `q=0`, the map `a↦k(·+a)` is `L²`-holomorphic throughout the
connected strip `|Im a|<π/4`: the theta series converges there,
and the first-atom bounds give uniform `L²` control on compact
subsets. Any `L²` vector orthogonal to every derivative is
therefore orthogonal, by the identity theorem, to **every** real
translate of `k`. The Fourier transform of this translation
correlation is the product of that vector's Fourier transform
with `XiC` on the real line. It vanishes identically; since
`XiC` is entire and `XiC(0)=M>0`, its real zero set has measure
zero. Plancherel forces the vector to be zero, proving density.
The final translation-cyclicity step is already formalized for
the rescaled source `2πk(2πx)` as
`isCyclicFamily_xiThetaTranslationOrbit` in
`XiThetaL2Cyclicity.lean`; linear rescaling transfers it to `k`.
The new step is the analytic passage
from all derivatives to the translation orbit.

Hence the history quotient is nonzero and has Xi-zero
annihilators at each positive reciprocal theta weight, but
disappears precisely where arbitrary prime translations become
unitary. The compact operator and its Xi spectral multiplicity
have been constructed only at `q=1`; extending them through the
weighted scale is a separate task. Any arithmetic information
carried through `q↓0` must survive as a **renormalized boundary
defect** of the family, not as a nonzero vector in the endpoint
quotient. No such defect law is proved here.

The endpoint does have a **rigged survivor**, although its Hilbert
quotient is zero. Let `𝓢` be Schwartz space and `𝓢′` its tempered
dual. With the Fourier convention `k̂(t)=XiC(t)`,

```text
{T∈𝓢′ : T(k⁽ʳ⁾)=0 for every r≥0}
  = 𝓕⁻¹{Q∈𝓢′ : XiC·Q=0}.                           (8)
```

Indeed `a↦k(·+a)` is holomorphic into `𝓢` on
`|Im a|<π/4`, by uniform theta-series and reflected first-atom
bounds for every Schwartz seminorm. If `T` annihilates every
derivative, the scalar holomorphic function `T(k(·+a))` has all
Taylor coefficients zero; it vanishes for all real `a`.
Fourier transforming this vanishing translation correlation
gives `XiC·𝓕T=0`. The converse follows by reversing the argument.
Locally at a real Xi zero of multiplicity `m`, the solutions of
`XiC·Q=0` are linear combinations of
`δ_z,δ_z′,…,δ_z⁽ᵐ⁻¹⁾`; globally one takes locally finite sums
subject to tempered-growth conditions. Thus the rigged endpoint
remembers **exactly the real Xi divisor with multiplicity**, while
off-real exponential evaluations are not tempered distributions.

Equation (8) is a classification of what survives at the
unitary-translation boundary, not a proof that every Xi zero is
real. That remaining statement would require showing that every
complex zero functional from `H_q′` has a tempered boundary
representative, or an equivalent arithmetic phase law. The
corpus already proves a positive-measure real-zero support law
in `XiSchwartzSpectralMeasure.lean`; (8) also admits derivative
jets and ties the classification to zero-history.

## Why no bounded intertwiner survives

The corpus proves that the restriction of `B` to `H₀` has dense
range in the full quantile Hilbert space. Because `B1=0`, the
full `B` has the same range and is dense. Orthogonal projection
`P` is continuous and onto `H₀`, so the range of
`D=P B|_(H₀)` is dense in `H₀`. Thus `B*` and `D*` are
injective.

If a bounded `G₀` obeyed `G₀D=D*G₀`, apply it to the nonzero
kernel vector `v₁`. Equation (2) would give `D*(G₀v₁)=0`.
Injectivity of `D*` forces `G₀v₁=0`; hence `G₀` cannot be
injective. The identical argument with `v₀` applies to `B`.
Alternatively, the first two steps of (2) alone contradict a
positive injective symmetrizer by pairing `G₀Dv₂=D*G₀v₂`
with `v₁`: they force `⟨G₀v₁,v₁⟩=0`.

## The divisor survives the zero-history quotient

Every nonzero Xi zero `z` gives a bounded, nonzero source
functional

```text
L_z(f)=∫ℝ f(x) exp(izx)dx.
```

Boundedness follows by Cauchy–Schwarz in `L²(k⁻¹dx)` and the
finite exponential moments of the double-exponential theta
density. Integration by parts gives
`L_z(k⁽ʳ⁾)=(-iz)^r XiC(z)=0`, so `L_z` annihilates `R`; it is
not the zero functional, since it takes the positive value `M`
on `k(x)exp(−izx)`. For arbitrary source vectors, first on a
dense smooth class and then by continuity, the centered primitive
obeys

```text
L_z(B_s f) = −z⁻¹[L_z(f)−M⁻¹(∫ℝ f)XiC(z)]
           = −z⁻¹L_z(f)                        when XiC(z)=0.
```

Thus `L_z` descends to a nonzero left eigenfunctional of `B̄`
at `−1/z`. Since `B̄` is compact and this eigenvalue is nonzero,
it belongs to its point spectrum. This proves `R` is proper
without guessing a complement.

Conversely `B|_R` has no nonzero eigenvalue. If it had one,
compactness would give a nonzero left eigenfunctional at that
eigenvalue. It would annihilate every `v_r`, since a sufficiently
high power of `B` kills `v_r`, contradicting their dense span
in `R`. Hence `B|_R` is quasinilpotent. For a nonzero isolated
eigenvalue `λ` of `B`, its Riesz projection `P_λ` kills `R`:
`P_λv_r=0` because `B` is invertible on the `λ`-root block,
and continuity extends this to `R`. The spectral decomposition
`H=ran(P_λ)⊕ker(P_λ)` then descends to the quotient with the
same finite-dimensional `λ`-root block. Therefore its algebraic
multiplicity is unchanged. The corpus's determinant identity
identifies these blocks with the nonzero Xi divisor.

This uses the literal contour projector. Choose an isolating circle
`|ζ−λ|=r` with `0<r<|λ|`, so zero lies outside its closed disc.
Since `B^(n+1)v_n=0`, the resolvent on `v_n` is the finite sum
`Σ_(j=0)^n ζ^(-j-1) B^j v_n`. Every scalar term has its only
pole at zero, outside this disc; its contour integral vanishes.
Thus the actual Riesz projector kills each `v_n`. Its closed kernel
contains their closed span `R`. The bounded factor through `H/R`
induces `P̄_λπ=πP_λ`, with
`ran(P̄_λ)=⋃_(m≥0) ker((B̄−λI)^m)` and `ker(P̄_λ)=π(ker(P_λ))`.
Quotient projection itself identifies the two finite spectral
ranges and intertwines their operator actions. Both decompositions
are topological direct sums because their projectors are bounded.

There is an exact finite-level formulation. Write `π:H→H/R` and
fix `λ≠0`. For every integer `n≥0`, quotient projection identifies
`ker((B−λI)^n)` with `ker((B̄−λI)^n)`. The restriction
`(B|_R−λI)^n` is invertible. Given a quotient root vector, lift it
to `x`; then `(B−λI)^n x∈R`. Choose the unique `r∈R` whose
restricted shifted power equals this vector. The corrected lift
`x−r` is a full root vector with the same quotient class. Conversely,
a full root vector in `R` vanishes by restricted invertibility.
Thus projection is a linear isomorphism at every root level and
on their maximal union. Its intertwining identity also preserves
the operator action on these blocks.

There is a further quantitative consequence. Let `f_z` be the
canonical source eigenmode at a Xi zero, normalized by
`∫f_z=M`, and let `π:H_s→H_s/U⁻¹R` be the quotient map.
For **every** integer `A≥0`, there is a constant `C_A` such that

```text
‖π f_z‖ ≤ C_A(1+|z|)^(−A)
```

for zeros in the natural strip with `|Re z|` sufficiently large.
Indeed `f_z=iz exp(−izx)∫_(−∞)^x k(y)exp(izy)dy`.
Repeated integration by parts writes it as a finite sum of
`k,k',…,k⁽ᴬ⁾` with inverse powers of `z`, plus an inverse-power
remainder involving the oscillatory primitive of `k⁽ᴬ⁺¹⁾`.
At a zero, the full integral of that derivative vanishes, so
the primitive can be represented by either tail. The same
double-exponential derivative bounds used above give a uniform
`L²(k⁻¹dx)` bound on this remainder for `|Im z|≤1/2`.
Projection kills every finite derivative term, proving the
displayed bound. Thus the divisor on the quotient is a genuine
**beyond-all-orders source remainder** under the canonical
mean normalization; no finite derivative jet sees it.

## Meaning and limit

The determinant-bearing theta inverse is not an almost
self-adjoint operator with a small local defect at zero. Its
source has an **infinite nonsemisimple history at zero**, and
the centered quotient retains that history. This explains why
the [finite-range symmetrizer no-go](theta-cdf-no-finite-range-symmetrizer.md)
can be strengthened from all fixed Fourier ranges to *every*
bounded injective metric, regardless of range. The earlier
fixed-shift action lemma remains a separate property of the
Fourier representation, but its symmetrizer obstruction is now
subsumed by (3).

This is an architectural exclusion, not spectral reality: the
nonzero eigenvalues of `D` still carry the full Xi divisor, and
the Jordan history occurs for other smooth positive sources that
have off-line zeros. A successful RH route must orient the
nonzero divisor through an unbounded/singular representation
or a carrier such as `B̄`, rather than seek a bounded Hilbert
self-adjointization of the original inverse. Positivity of the
quotient Hilbert norm alone does not orient its eigenvalues:
the explicit positive, even, strictly log-concave mixture
`k_*(x)=exp(−x²)+exp(−2x²)` from the CDF-action quotient card
has the same derivative history and an off-real Fourier zero.
The next gate is a **literal arithmetic
phase law on this quotient's beyond-all-orders remainder**, not
another local metric estimate.

The weighted-scale law sharpens that gate: finite Euler source
orbits belong to derivative-history at some positive weight,
while the history quotient collapses at the unweighted endpoint
where all translations are unitary. The needed arithmetic law
must control a boundary defect of this singular passage. Merely
taking the endpoint quotient gives the zero space.

**Lean audit:** `ThetaPowerWeightedDerivativeHistory.lean` proves actual
derivative admission for every `0 < q < 2`. The literal source-coordinate
classes, their quantile images, both infinite zero-Jordan chains, linear
independence, orthogonally centered dense range and no-injective-intertwiner
theorem are now certified in `HedenmalmThetaDerivativeJordan.lean`.
`HedenmalmThetaDerivativeHistorySpectrum.lean` certifies invariance,
compactness, spectrum exactly `{0}` on history, and properness using
Hardy's actual real Xi zeros. The full-operator obstruction remains
certified in `HedenmalmThetaZeroHistoryNoGo.lean`.

Both new native leaf builds and final direct source audits passed without
warnings. All 44 new public declarations and four existing operator
capstones were audited in scratch with `#print axioms`: only the standard
`propext`, `Classical.choice`, and `Quot.sound` axioms appeared. Both leaves
are wired into `RHTower.lean`; generated indexes were refreshed.

Three additional leaves now certify the literal history quotient:
`GeneralizedEigenspaceQuotient.lean` gives exact transport of every
generalized root level and the maximal root space;
`CompactInvariantQuotient.lean` constructs the continuous quotient
operator and proves compactness through its bounded orthogonal section;
`HedenmalmThetaDerivativeHistoryQuotient.lean` discharges shifted
invertibility from the actual history spectrum `{0}`. It preserves the
entire nonzero spectrum, the canonical nonzero source eigenmodes, and
the full analytic Xi multiplicity at every complex zero. These three
leaves contain 41 public declarations. Their final native and direct
source checks passed without warnings; all 41 declarations and four
existing capstones had 45 complete standard-axiom reports. A 47-name
current-toolchain API witness passed. The leaves are wired into their
area umbrellas. No new source premise or zero-location hypothesis was
introduced.

`HedenmalmThetaDerivativeHistoryRiesz.lean` now certifies the literal
contour-projection clause in 24 public declarations. The existing
isolating theta radius excludes zero; the generalized-zero contour
lemma kills every actual derivative, and continuity kills their closed
history. The bounded projection factors through the literal quotient.
The induced projection commutes with the quotient inverse and gives a
topological range/kernel decomposition. Its range is exactly the full
quotient root block; its kernel is exactly the image of the original
kernel. Quotient projection itself is the equivalence of both finite
Riesz ranges, preserves the source action, and retains the analytic Xi
multiplicity. Final native leaf build and direct source audit passed
without warnings. A 22-name infrastructure witness and a 24-export
witness passed; all 24 exports and seven existing capstones have 31
complete axiom reports containing only `propext`, `Classical.choice`,
and `Quot.sound`. The leaf is wired into `RHTower.lean`.

`HedenmalmThetaDerivativeHistoryFourier.lean` certifies the literal
bounded left Fourier functional in 35 public declarations. For every
complex parameter and every actual weighted source vector, the bounded
conormal functional equals the ordinary integral `∫f exp(izx)`. Its
admitted test `k exp(-izx)` has exact value `M > 0`. The complete
centered-space shifted-range identity, with the actual source-density
vector separated off, gives the full mass correction. The existing
source-equation bridge identifies the output with the literal physical
centered primitive, so both the all-parameter integral identity and the
reciprocal formula for `z ≠ 0` hold for every source input. Every ordinary
source derivative is admitted under every complex tilt and has exact
transform `(-iz)^n XiC(z)`. At an actual Xi zero, closed-kernel minimality
annihilates the entire history. The bounded functional descends to the
literal quotient, retains the test value `M`, is surjective and nonzero,
and has exact left eigenvalue `-z⁻¹`. No density, source-admission,
zero-location or RH premise was added. Final native leaf build and direct
source audit pass without warnings. The exhaustive 35-export witness
passes; all 35 exports and seven existing analytic capstones have 42
complete axiom reports containing only `propext`, `Classical.choice`,
and `Quot.sound`. The leaf is wired into `RHTower.lean`; final generated
index and global lint results are recorded in the recursive ledger.

`ThetaRealShiftHistory.lean` certifies the sharp real-translation boundary
and both closed-span inclusions in 21 public declarations. For every
positive `q`, the literal translate is admitted exactly when
`q < 2 exp(-2|a|)`; equality fails, and both shift signs are covered. For
every `0 < q < 2`, actual weighted derivative history equals the closed
span of all intrinsically admitted real translates. This gives the exact
`log(2/q)/2` radius and its original `q=1` specialization.

`ThetaWeightedTranslationDomain.lean` adds 19 public declarations for the
full complex domain determined by Gaussian slack. For `0 < q < 2` it is
open, star-convex and connected;
every point has a strict weighted `L²` rectangle majorant. The literal
translation family is Hilbert-holomorphic throughout the domain, has the
actual ordinary theta derivatives as origin jets, and lies in derivative
history. Its reciprocal measure is exactly the original source measure.

`ThetaQuantileTranslationHistory.lean` adds 23 public declarations proving
the original-carrier form of (4). The canonical measure-congruence class
equals the original literal `toLp` vector. Actual derivative and
translation vectors transport through the original quantile unitary;
both closed-span inclusions hold, hence their closed histories are equal.
Every admitted local translate is killed by the actual history quotient.
Every nonzero finite prime word fails original source-space admission,
including arbitrary complex coefficients and zero coefficients. For
complex coefficients, a nonzero real or imaginary component reduces this
exclusion to the signed real terminal-prime case.

`L2MeasureCongruence.lean` supplies six public transport declarations.
These four leaves contain 69 public declarations. Native builds, all four
final direct source checks, and the exhaustive 69-export witness pass.
All 69 declarations and eight existing analytic/transport capstones have
77 complete axiom reports containing only `propext`, `Classical.choice`,
and `Quot.sound`. Current-toolchain API witnesses cover 145 entries.
All four leaves are registered once in their area umbrellas and included
in the regenerated catalogue. Exact diagnostics and recursive census are
recorded in the formalization ledger.

`ThetaGradedFiniteHistory.lean` certifies the finite arithmetic/Euler
clause in 20 further public declarations. The explicit weight
`q_D = exp(-2 Σ_(d∈D) |log d|)` lies in `(0,2)` and admits every letter,
independently of its complex coefficients. The full literal finite word's
`toLp` class equals its sum of actual translation classes, belongs to
ordinary derivative history, and is zero in the actual submodule quotient.
The existing exact Möbius expansion identifies the literal Euler deletion
source. Applying this weight to its squarefree alphabet admits every
individual prime letter and the whole Euler deletion simultaneously,
including the empty prime set. The capstone
`exists_pos_weight_finitePrimeEuler_history` discharges admission,
history membership and quotient vanishing for this one common carrier.
Native build, final direct check, all 20 export checks and all 26 axiom
reports pass; only the standard three axioms occur. A 40-entry API witness,
single umbrella registration and complete regenerated catalogue pass.

`ThetaWeightedHistoryProperness.lean` certifies positive-weight properness
in 17 public declarations. The complementary exponent `2-q` discharges
the literal reciprocal-density moment and every phase-twisted source's
admission. The two actual density unitaries cancel their square-root
weights, identifying the bounded functional with the physical integral
`∫f exp(itx)`. The admitted source test has value `M>0`; every actual
derivative has transform `(-it)^n XiC(t)`. Hardy's actual real Xi zero
annihilates their closed history, proving properness for every `0<q<2`.

`ThetaUnweightedDerivativeHistory.lean` certifies the endpoint in 18
public declarations. The exact `q=0` measure is Lebesgue measure. One
strengthening of the existing rectangle-majorant theorem includes the
nonnegative endpoint while preserving its original public signature.
Those literal Gaussian majorants give a Hilbert-holomorphic curve on the
full connected strip `|Im z|<π/4`. Its origin jets are the actual ordinary
derivatives, so analytic uniqueness includes the entire real translation
orbit in their history. Exact `2π` dilation identifies the existing
normalized cyclic orbit with this literal unscaled orbit; hence
`thetaWeightedDerivativeHistory 0 = ⊤`. The unconditional capstone
`thetaDerivativeHistory_endpoint_dichotomy` certifies both halves of (7).

All 36 new public declarations, including the majorant strengthening,
pass exhaustive export checks. Native named leaf builds and all three
final direct source checks pass without leaf warnings. All 36 exports
and ten existing capstones have 46 complete axiom reports containing
only `propext`, `Classical.choice`, and `Quot.sound`. A 63-entry API
witness passes; both new leaves are registered exactly once in the area
umbrella. Final catalogue, global lint and recursive queue evidence are
recorded in the formalization ledger.

The full card remains Stage 2. Complete exact certificates are still
required for the tempered annihilator classification with multiplicity
jets (8) and rapid normalized eigenmode decay in the quotient.
No computational certificate or RH/zero-location premise was introduced.
External novelty has not been established. Global lint diagnostics are
recorded in the recursive formalization ledger; other concurrent modules
remain outside this card's write scope.

### Exact inter-weight translation certificate

`ThetaTranslationDensityRatio.lean` supplies 20 public declarations for
the literal ratio `k(y-a)^(-q')/k(y)^(-q)`. Its envelope quotient tends to
the exact positive constant `(4π²)^(q-q')`. Both strict-margin tails decay;
the dangerous tail diverges beyond the threshold and at equality, where
the remaining positive linear exponent excludes boundedness. The exact
bounded-ratio classification includes every shift and the zero-shift
boundary for all real exponents.

`LpContinuousMultiplierNorm.lean` supplies four public declarations.
Actual finite-interval indicators force every continuous multiplication
symbol below its operator norm. Positive-volume open level sets identify
the literal essential supremum, including the squared norm.

`ThetaInterWeightTranslation.lean` supplies 28 public declarations. The
actual density unitaries construct the bounded translation when the ratio
is bounded, preserving `f(x+a)` for every actual input. Conversely every
bounded operator with that representative law conjugates to the literal
continuous multiplier and forces a bound on the ratio. Thus no extra
source-admission or operator-existence premise is imposed on (5).
The representative law is equivalent for Lebesgue and the actual output
weighted measure and determines the operator uniquely.

For `q,q'>0`, nonzero shifts admit that bounded operator exactly when
`q'<q exp(-2|a|)`; zero shift admits it exactly when `q'≤q`. Its squared
norm is precisely the essential supremum of the displayed actual ratio,
as both an extended-nonnegative and a real-valued equality. Equality at
the nonzero-shift threshold fails; no nonzero shift is bounded on a fixed
positive-weight carrier. Every prime specialization is exactly
`q'<q/p²`. These certificates discharge every assertion in paper (5).

All 52 public declarations pass exhaustive export checks. Named native
builds and final literal direct checks of all three sources pass with
empty direct logs. All 52 exports and eight prior capstones have 60 axiom
reports containing exactly `propext`, `Classical.choice`, and `Quot.sound`.
The 105-entry API witness passes. Final area-registration, catalogue,
global-lint and recursive-queue evidence is recorded in the formalization
ledger. The remaining exact obligations are (8) and rapid normalized
quotient eigenmode decay; no whole-card promotion is claimed.

### Exact real/off-real tempered evaluation boundary certificate

`ThetaTemperedEvaluationBoundary.lean` supplies 11 public declarations.
The actual complex tempered dual admits no off-real physical exponential
evaluator, even on the embedded real Schwartz functions with entire
Laplace transform. Conversely, at every real frequency `t`, the actual
Fourier transform of the Dirac at `-t/(2π)` agrees with `∫ exp(itx)f(x)dx`
on every complex Schwartz function. A tempered extension on the entire
exponential domain exists exactly when `Im z = 0`.

This proves the positive sharp boundary exposed by the off-real
obstruction. It certifies that subclause of (8), without replacing the
full annihilator identity or its local/global multiplicity classification.
The named native build, final literal direct check, all 11 export checks,
20-entry API witness, unique umbrella registration and regenerated
catalogue pass. All 15 export/capstone axiom reports contain exactly
`propext`, `Classical.choice`, and `Quot.sound`. Global lint remains
non-green on unrelated modules; exact diagnostics and complete recursive
queue evidence are recorded in the formalization ledger.

The card stays Stage 2. The full tempered annihilator/multiplicity claim
and rapid normalized quotient eigenmode decay remain open.


## Lean coverage: canonical all-order quotient decay

The exact rapid quotient-decay statement is now formalized by
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaDerivativeOscillatoryPrimitive.lean`,
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaDerivativePrimitiveBounds.lean`,
and `formal/GaloisForLFunctions/RHTower/HedenmalmThetaQuotientEigenmodeDecay.lean`
(12 + 18 + 19 public exports).

The quotient is the literal source quotient `H_s/(U⁻¹R)`. Exact
integration by parts removes every finite derivative term. The
remaining primitive is bounded by a constructed, actually admitted
`L²(k⁻¹dx)` majorant uniformly throughout `|Im z|≤1/2` at actual
Xi zeros. The existing canonical source vector keeps its integral
`M`, and its quotient is nonzero. For every natural `A`, the exact
bound `‖πf_z‖≤C_A(1+|z|)^(-A)` holds with threshold `|Re z|≥1` and
`C_A=2^A‖B_(A+1)‖`. No RH premise, free rescaling, assumed remainder
bound or admission hypothesis is used.

All named native and final literal leaf checks pass. All 49 export
witnesses and matching axiom reports pass using only the three standard
Lean axioms; 266 pinned API witnesses and exact generated-catalogue
coverage pass. The recursive ledger records the complete evidence and
unrelated global lint failures. This card stays Stage 2: the full
actual tempered annihilator/multiplicity classification (8) remains
open. The earlier real/off-real tempered-evaluation boundary is closed.
