# Floor-Free Arithmetic (FFA)

Namespace `GaloisForLFunctions.FloorFreeArithmetic`; umbrella `FloorFreeArithmetic.lean`.

## 1. Motivation

Every formulation of the Riemann hypothesis in the corpus is an equivalence with one open input,
and every route is a *receiver*: it turns a sign, a count or a growth rate into zeros on the line.
A *producer* is a theorem that supplies the input. The methods that exclude zeros
unconditionally — sizes, positivity of coefficients, exponential sums, density theorems, mean
squares over families — all stop at a boundary: each has a least depth `δ = Re ρ − ½` at which it
can still exclude a zero. A method with such a floor cannot prove the asymptotic abscissa law
(AAL), which has to hold for a top layer at every depth, however small, nor the Riemann
hypothesis, whatever its constants.

FFA is the theory of what is left. It does three things.

* It makes the **floor** of a mechanism a mathematical object and computes it, so that a proposed
  estimate can be discarded before any work is spent on it.
* It isolates the inequalities that have **no floor** — because they are exact — and proves the
  receivers that accept them, in forms that are the same statement at every depth.
* It takes each kind of floor-free inequality to its first theorem and to the theorem that says
  how far the kind can go: a *kill* (the kind cannot produce) or a *survivor* (the statement a
  producer of that kind must prove).

FFA adds no new equivalent of RH for its own sake and contains no producer. Its results say what
a producer has to be.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Mechanism | `Mechanism` | a property of zero configurations: the structures a method uses with the estimate it proves |
| Exclusion, model | `ExcludesBeyond M δ`, `HasModelAt M δ` | every configuration with the property has its zeros at depth `≤ δ`; a configuration with the property and a zero of depth `δ` |
| Floor | `floor M`, `FloorFree M` | least depth beyond which `M` excludes; floor zero |
| Finite stratum | `HasFiniteStratumModel M` | a model with a finite nonempty set of zeros right of the line (world I) |
| Normalized trace | `SurfaceOfSpecZ.normTrace Z b` | the spline trace `2 Re S(u)` divided by its rate `e^{bu}` |
| Top trace | `SurfaceOfSpecZ.topTrace Z b` | the part of the normalized trace carried by the zeros of depth exactly `b`: a real trigonometric polynomial when the layer is finite |
| Window non-attainment | `WindowNonAttainment Z b L` | on arbitrarily late windows of length `L` the trace is `o(e^{bu})` |
| Window moment | `∫ u in T..T+L, (2 Re S(u))^(2k)` | even moments of the trace on a window of fixed length |
| Right zeros of a line | `ZeroConfigurationGeometry.ConfigAbscissa.rightOf Z h`, `rightOfLine σ` | zeros with `Re ρ > ½ + h`; the half-plane `Re s > σ` without the pole |
| Split increment | `splitIncrement F ξ δ` | change of the linear statistic `Σ_ρ F(ξ_ρ)`, `ξ_ρ = (ρ−½)/i`, when the double point `ξ` of the line splits into the reflection pair `ξ ± iδ` |
| Symbols | `fourierSymbol g`, `heatSymbol t` | `∫ g(u)e^{iwu}du`: statistics with an explicit formula; `e^{−tw²}` |
| Tower quotient | `towerQuotient N` | `Λ(s)/Λ(s+N)`: secular function of the scattering tower of height `N` |
| Clock regulator | `HyperbolicArakelovTheory.greenWeilEnergy a r` | Weil's form of the aperture `a` with the archimedean jump kernel damped at the cutoff `r < 1` |
| Normalized translates | `NormalizedTranslatesBoundedOn c τ U` | local boundedness of `c_j ζ(· + iτ_j)` on `U` along a sequence of heights |
| Count and inner mass of a layer | `layerCount`, `layerInnerMass` | total multiplicity at depth `≥ a`; `Σ m_i (δ_i − a)₊` |

## 3. Language

- **Depth** of a zero: `Re ρ − ½`. **World I**: finitely many zeros right of some line, hence a
  finite top layer at a depth `b > 0` (the failure of AAL). **World II**: zeros approaching a line
  `Re s = Θ∞ > ½`.
- **Floor** of a mechanism: the least depth at which it can exclude a zero. **Floor-free**: floor
  zero; equivalently the mechanism forces purity on every configuration it applies to.
- **Model / fake**: a system with all structures a mechanism uses and a zero at positive depth.
  A model at depth `δ` is a proof that the floor is at least `δ`.
- **Receiver / producer**: a theorem converting a statement into information on zeros / a theorem
  proving the statement.
- **Own rate**: a statement *compares a quantity with its own rate* if it is normalized by the top
  exponent (`e^{bu}`, `x^Θ`). Such a statement is the same at depth `10⁻⁹` and at depth `¼`.
- **Attained / non-attained**: the trace reaches a fixed multiple of its rate on every late
  window / falls below every multiple on some late window.
- **Tangent form** of a mechanism: what remains of it after normalization by the top exponent.
- **Kinds of inequality without a floor.** (a) *Homogeneous*: some constant suffices, scaling
  turns any bound into the sharp one. (b) *Unit gap*: an integer below one is zero.
  (c) *Equality case*: a feasible point of a dual problem proves the optimum exactly.
  (d) *Amplification*: a parameter multiplies the depth and not the loss.
- **Kill / survivor** of a track: the theorem that a kind cannot produce / the exact statement a
  producer of that kind must prove.

## 4. Mechanisms

**The floor.** A model bounds the floor from below and exclusion bounds it from above; a stronger
mechanism has a lower floor; the floor is zero exactly for the mechanisms that force purity. A
mechanism with a model of positive depth proves purity of nothing, and one with a finite-stratum
model does not prove AAL. What holds for every tempered configuration with the reflection symmetry
— every identity of the explicit formula with its archimedean density — has floor `½`, the whole
strip.

**Non-attainment (kind a).** If AAL fails, the trace of `ζ` normalized by its top exponent is
`P(u) + o(1)` with `P` a nonzero real trigonometric polynomial with finitely many frequencies.
Sampling `P` at a small step turns it into a power sum with distinct unimodular nodes, and the
inverse Vandermonde matrix recovers a coefficient from consecutive samples; so `|P| ≥ ε`
somewhere on *every* window, however short, uniformly in its position. World I is therefore
uniformly bad: the error attains its own rate on every late window of every length. One length
with arbitrarily late windows on which the error is of smaller order than its own rate gives AAL;
so does a window moment of one order, the mean square for instance, that is of smaller order
than its own rate.
The same holds for `ψ(x) − x` on multiplicative windows `[x, λx]`: the prime number theorem with
its own exponent is attained on every window, or AAL holds. It holds already at the primes:
every point has a prime within the gap `x^{2/3}` below it and the trace moves by a smaller order
than its rate over such a gap.

**The tangent datum.** After normalization the trace keeps only its top trace, an absolutely
convergent trigonometric series whose Bohr coefficient at `λ` is the spline coefficient of the
point `b + iλ`. So the normalized trace tends to zero exactly when the top line is empty, and
two configurations with asymptotically equal normalized traces have the same top layer. There
is a dichotomy: the normalized trace tends to zero, or it is attained on every late window of
some length; non-attainment on windows of one length already leaves the top line of `ζ` empty or
infinite, also when other zeros accumulate at it. The datum is integral: the coefficient of a
zero `½ + z` of `ζ` is `2m B̂(−iz)²` with `m` its multiplicity, and it is the Cesàro mean of the
normalized trace against `e^{−iλu}`. A mean below the quantum `2|B̂|²` excludes the zero: a unit
gap at every candidate point, for which no a priori bound is known. The Dirichlet series of the
Möbius and the Liouville function, `1/ζ(s)` and `ζ(2s)/ζ(s)`, have at a zero right of the line
a pole of order the multiplicity, with leading coefficients that differ by the unit `ζ(2ρ)`:
the three top layers have the same support, and only that of `Λ` has integral coefficients.
The summatory function of `μ` attains its rate at an attained frontier with the logarithmic power
of the multiplicity: `M(x) ≠ o(x^Θ (log x)^{m−1})` at a zero of order `m` on `Re s = Θ` (corpus,
`RHTower.not_mertens_littleO_zetaZeroAbscissa_of_le_order`).
Linear
identities impose nothing on the datum: every depth `0 < b ≤ ½`, every finite set of positive
ordinates and every choice of multiplicities is the top layer of a finite configuration with the
reflection symmetry and the conjugation symmetry, so what holds on every tempered symmetric
configuration has a model with that top layer. Each structure alone realizes every top layer:
the reflection symmetry as above; positivity of the prime measure, for every finite datum below
`Re s = 1` (§6); and an Euler product with natural norms, natural coefficients, a simple pole
and linear counting, for every finite datum at every depth below `½`: the density of the datum
is discretized at its quantiles and the discrete primes are rounded up to integers, which
changes the zeta function by a factor holomorphic and without zeros right of the critical line
(the construction of the one-offs of `ArithmeticPositiveDuality`, for an arbitrary density);
for distinct positive ordinates the zeros have exactly the prescribed orders.
Rounding to the next rational prime instead gives an Euler product over the rational primes
with natural exponents, the Dirichlet series of a nonnegative multiplicative function on the
integers, with any finite layer at `17/30 < Θ < 1`: the prime gaps cost the strip up to `17/30`.
Multiplicativity, positivity and integrality of the coefficients therefore impose nothing on a
finite top layer; only the functional equation is missing from these models. Two refinements of
the models are constrained in the corpus. A system that only adds generalized primes to the
rational primes pays for a new zero with a real singularity of its logarithmic Euler factor at
or beyond the zero (`RHTower.landau_relative_rigidity`); the models above have none, so they
change the primes in both directions. And the models control the count of their integers to
first order only. For continuous systems a regular count does not constrain the zeros
(`RHTower.BeurlingRegularIntegers.regular_integers_do_not_constrain_zeros`); for the integers
free of a set of primes it quantizes the expansion of the deleted primes
(`RHTower.PrimeDeletion.residue_quantization_complex`). With the functional equation there is no
class left to build a model in: a discrete system of primes whose zeta function has the
completed functional equation is the system of the rational primes
(`ArithmeticPositiveDuality.beurlingSystem_rigidity_of_completed_functional_equation`). A finite
top layer is excluded, if at all, by a property of one function. What is known of a tangent
datum of `ζ` at a depth `b > 0`: it consists of conjugate pairs, with integer multiplicities,
at ordinates above the verified height
(`SurfaceOfSpecZ.ScaleLocality.sixtySeven_lt_im_of_positive_zeta_mode`), and `b < ½`. Nothing
else.

**Replication.** Along a phase return (`n^{−iτ_j} → 1` for every `n`) the translates
`ζ(· + iτ_j)` converge to `ζ` right of `Re s = 1`. If they stayed bounded on a domain joining a
zero of a finite layer to that half-plane, Hurwitz's theorem would replicate the zero at the
heights `τ_j` (`ArithmeticAuxiliaryDynamics`). So in world I the supremum of the translates over
such a domain tends to infinity along every phase return, and no normalization repairs this: if
`c_j ζ(· + iτ_j)` is locally bounded there, then `c_j → 0`, and every locally uniform limit of
normalized translates is identically zero. A normal family of translates at a top zero has
nothing for Hurwitz's argument to act on; replication needs a bound for `ζ` along a return.

**Unit gaps (kind b).** The zeros of `ζ` right of a vertical line pair off under conjugation and
none is real, so their number is even when finite: at most one is none. AAL is the statement that
every line has at most one or infinitely many zeros to its right. A unit gap survives locally
uniform limits (Hurwitz): functions analytic right of the line with at most one zero there and
limit `ζ` give RH; right of `Re s = σ` they give the zero-free half-plane; with at most `k`
zeros they leave `ζ` at most `k` zeros right of the line. The same count comes
from a form: if the zeros right of the line are eigenvalues, at their spectral points `i(ρ − ½)`,
of an operator symmetric for a form with `κ` negative squares, there are at most `κ` of them, and
none for `κ = 1`. The form with one negative square by construction exists in the corpus: Weil's
form without the pole term, archimedean minus primes, has a negative vector unconditionally, and
RH holds exactly when it is negative definite on no plane of tests
(`RHTower.exists_markovEnergy_neg`, `RHTower.riemannHypothesis_iff_not_exists_negDef_markovPlane`).
What is missing is a proof that its index is one, not the form. Of the regulators of the horizon, the scattering tower has the right zeros of
`ζ` at every height, and the clock lies below Weil's form at every cutoff: its negative
directions contain those of the limit, so a sign, a floor or an index bound before the limit is
at least as strong as the same statement in the limit. The de Bruijn–Newman heat flow is the
regulator that approaches `Ξ` from the good side: it has only real zeros from the time `1/8`
on, its number of nonreal zeros does not increase with the time, and a count of at most one on
times tending to zero gives RH; but when `Ξ` has finitely many nonreal zeros the flow has
exactly that number at every small time (`RHTower.DeBruijn`). No regulator of the corpus has a
unit gap before its limit.

**Amplification (kind d).** In world I the `2k`-th moment of the trace on a window of fixed
length lies between `η(c e^{bT})^{2k}` and `L(B e^{b(T+L)})^{2k}` with `c, η, B` independent of
`k`: the order multiplies the depth and nothing else. One growth exponent for all even moments,
with constants and windows depending on the order, gives AAL. The hypothesis is a sup bound in
disguise: the trace is Lipschitz with rate `e^{R/2}`, so a value `M` on a window forces the
`2k`-th moment to be at least `(M/2)^{2k} min(M/2K, L/2)`, and a bound `C e^{AT}` for that moment
gives `|2 Re S|^{2k+1} ≤ 2^{2k+1} G C e^{(A+1)T}` on the whole window with `G` independent of
`k`. Bounds for all moments with one exponent are therefore the same as bounds for all powers of
the sup norm with one exponent, which follow from a two-sided bound `C_ε e^{εT}` for every `ε`:
the bound of the Riemann hypothesis on some late windows. A bound of one order `2k` with the
exponent `A` excludes only the finite top layers of depth beyond `A/2k`.

**Symmetrization (the fourth track).** Projecting a reflection pair to the line changes a linear
statistic by the split increment, which is `−δ² Re F''(ξ) + O(δ⁴)`: the sign of the curvature of
the symbol on the line decides. A statistic monotone at every ordinate and all small depths has
a concave symbol on the line; a concave function on `ℝ` bounded below is constant. Hence every
convergent linear statistic — every functional an explicit formula evaluates — is lowered by
projection at some ordinates and raised at others, at arbitrarily small depth. The heat statistic
`Σ_ρ e^{−tξ_ρ²}` is lowered exactly below the height `(2t)^{−1/2}`: a floor in the height, none in
the depth. On the prime side, projection adds the smooth density `2cos(ξu)(cosh(δu) − 1)`.
Functionals that are not analytic in the zeros do decrease: an additive functional `Σ m ψ(δ)` of
the depths drops under projection by `∫ ψ'(a) N(a) da`, with `N(a)` the number of zeros at depth
at least `a`, and equals `ψ'(0) I(0) + ∫ ψ''(a) I(a) da` with `I(a) = Σ m (δ − a)₊` the inner
mass at the level `a`. Every such functional is a mixture of inner masses; it is monotone when
`ψ` increases, and its evaluation on `ζ` is Littlewood's formula for the inner mass. The track
ends there: what is missing is not a monotone functional but a reason for `ζ` to minimize one,
which is the equality case of Jensen's formula.

**Certificates (kind c).** RH holds exactly when every aperture admits some real weight system
with nonnegative Weil form, and the dual statement is that the archimedean-plus-pole functional
is nonnegative on positive-definite functions vanishing on `log ℕ`
(`ArithmeticOfSquareRootPrecision.riemannHypothesis_iff_feasible_at_every_aperture`,
`RHTower.riemannHypothesis_iff_primeBlindPositive_unconditional`). The feasible sets are convex
bodies around `Λ` (`SelectiveArithmetic`); a producer of this kind exhibits a point of each.
A system is feasible at an aperture `A` exactly when, for every test supported in `[−A', A']`,
the kernel `y ↦ W_λ(τ_y(f ⋆ f̃))` is positive definite on the nodes of `[−(A − A'), A − A']`.
Such a kernel need not be positive definite on the line, but its product with the
autocorrelation `φ ⋆ φ̃` of a taper supported in the same interval is: the Gram form of the
product is the integral over `x` of Gram forms whose nodes lie within the interval about `x`.
By Bochner's theorem every tapered kernel of a feasible system is the Fourier transform of a
finite positive measure, and a measure for one nonzero taper gives back the sign on the test: a
feasible system is a family of positive measures, with no extension theorem needed. A positive
definite kernel on an interval that vanishes at
`0` vanishes on the interval; so a feasible system is strictly positive on a test unless its
Weil functional vanishes on every admitted translate of the autocorrelation of the test. The
systems on the boundary of a feasible set are those annihilated in this way by a null vector.
The existence quantifier has no freedom in the limit: feasible systems are bounded in every
visible coordinate, a test reads finitely many coordinates, and the Weil cone has one point; so
every family of certificates at apertures tending to infinity converges to `Λ` in every
coordinate, and for each `n` and `ε` there is an aperture beyond which every feasible system has
`|λ(n) − Λ(n)| ≤ ε`. The pure objects made from `ξ` do not supply certificates. Each is a
dominant half with an Euler product plus its reflection, and the quotient of the halves is a
quotient of Gamma factors times a Dirichlet series: for the pencil `ξ(s+h) + ξ(s−h)` it has
size `≍ σ^{−h}` on the real axis (`2π (s−2)/(s(s+1)) · ζ(s−1)/ζ(s+1)` at `h = 1`), for the
cleared Eisenstein constant term at height `Y` it has size `≍ Y^{1−2σ} σ^{−1/2}`. A Dirichlet
series has an exponential scale at its first nonzero coefficient, `n^σ L(σ) → a_n`; an
amplitude that tends to zero more slowly than every exponential has none (the first coefficient
test). So no pencil and no constant term, divided by its dominant half, is a Dirichlet series:
the prime side has a density that starts at first contact and is not carried by `log ℕ`.

## 5. Pillar theorems

All proved in Lean. *Receiver*: an implication to AAL, a half-plane or RH from a floor-free
hypothesis. *Kill*: a source excluded for a whole kind.

| Pillar | Lean | Role |
|---|---|---|
| **Floors.** Floor calculus; floor zero ⇔ purity is forced; the explicit-formula class has floor `½` | `floor_eq_zero_iff_floorFree`, `floor_temperedConfig`, `floor_exponentialFloor` | calculus |
| **Uniform attainment.** A finite top layer is seen on every late window of every length | `exists_pos_forall_window_le_norm_realExpSum`, `finite_top_seen_on_every_window` | structure of world I |
| **Non-attainment ⇒ AAL**, for the trace, for `ψ(x) − x`, at the primes, in the mean of one order, and for every tempered symmetric configuration | `asymptoticAbscissaLaw_of_windowNonAttainment`, `asymptoticAbscissaLaw_of_psi_window_nonAttainment`, `asymptoticAbscissaLaw_of_moment_window_nonAttainment`, `abscissaLaw_of_windowNonAttainment_config` | receivers (a) |
| **The tangent datum.** Trace `o(e^{bu})` ⇔ empty top line; the trace determines the layer; attained or tending to zero | `tendsto_normTrace_zero_iff`, `topCoeff_eq_of_tendsto_normTrace_sub`, `tendsto_normTrace_zero_or_attained` | structure |
| **Integrality.** The multiplicity is a mean of the trace; a mean below the quantum excludes the zero; `μ` and `λ` have poles of order the multiplicity | `evenCoeff_zeta_eq`, `not_mem_zetaZeroConfig_of_mean_lt_quantum`, `meromorphicOrderAt_liouville` | receiver (b) |
| **The datum is free.** Every finite datum is the top layer of a finite symmetric configuration, of a positive prime density with a simple pole, and of an Euler product over natural norms with natural coefficients and linear counting | `exists_config_with_top_layer`, `exists_nonneg_density_with_layer`, `exists_integer_norm_euler_product_with_divisor` | kill: identities, symmetries, positivity, multiplicativity, integer norms |
| **Replication.** Translates at a finite layer blow up along every phase return; bounded normalizations tend to zero; every limit is zero | `forall_eventually_exists_lt_norm_translate`, `tendsto_normalization_zero`, `eqOn_zero_of_tendstoLocallyUniformlyOn_normalized` | kill: normal families |
| **Unit gaps.** AAL ⇔ at most one or infinitely many zeros right of every line; bounded counts pass to locally uniform limits; a realization of index `κ` has at most `κ` right zeros | `asymptoticAbscissaLaw_iff_encard_rightOf_le_one`, `riemannHypothesis_of_unit_gap_limit`, `riemannHypothesis_of_indexOne_realization` | receivers (b) |
| **Regulators.** The scattering tower keeps the count at every height; the clock lies below Weil's form at every cutoff; the heat flow has at least two nonreal zeros at every small time unless RH holds | `towerQuotient_unit_gap_iff`, `greenWeilEnergy_le_form`, `riemannHypothesis_of_greenWeilEnergy_floor`, `riemannHypothesis_of_frequently_nonrealZeroCount_le_one` | kill; receiver |
| **Certificates.** Feasibility at an aperture = positive definite spectral kernels on intervals = tapered kernels that are transforms of positive measures; null vectors annihilate; certificates converge to `Λ`; reflected halves (pencils at every shift, the cleared Eisenstein constant term) are not Dirichlet series | `aperturePositive_iff_spectralKernel_positiveDefiniteOnNodes`, `exists_measure_charFun_eq_taperedKernel`, `spectralKernel_eq_zero_of_null`, `tendsto_weight_of_aperturePositive_seq`, `not_lSeries_of_slow_amplitude`, `not_exists_lSeries_pencil_shift`, `not_exists_lSeries_constantTerm` | structure; kill (c) |
| **Amplification.** Window moments of a finite layer have rate `2k·b`; a bound of order `2k` with exponent `A` gives the law beyond the depth `A/2k`; one exponent for all orders ⇒ AAL; moment bounds of all orders are sup bounds | `finite_top_moment_lower_bound`, `abscissaLawAt_of_window_moment`, `asymptoticAbscissaLaw_of_window_moments`, `windowMomentsBounded_iff_windowSupPowersBounded` | receiver (d); kill |
| **Symmetrization.** Second-order law of projection; no convergent linear statistic is monotone; heat statistics are monotone below a height; additive functionals of the depths are mixtures of inner masses | `exists_splitIncrement_neg_and_pos`, `heatSymbol_splitIncrement_sign`, `sum_profile_sub_eq_innerMass` | kill |

## 6. The floor census

Floors of the mechanisms that exclude zeros, with the theorem that fixes each.

| Mechanism | Floor in the depth | Where |
|---|---|---|
| Identities of the explicit formula, temperedness, reflection symmetry | `½` | `floor_temperedConfig` |
| A floor `−Ce^{σv}` of the spline two-bump form (any size estimate of exponent `σ`) | exactly `σ` | `floor_exponentialFloor` |
| Laws that read only the ordinate counts | `½` | `floor_eq_half_of_countInvariant` |
| Sizes of the contacts (dominated box) | `½`: the trivial aperture | `SelectiveArithmetic.exists_trivialAperture_margin`, `exists_not_feasible` |
| Positivity of Euler coefficients | `½`: purchase ratio `≤ 2`, interior zeros invisible; every finite layer below `Re s = 1` has a positive prime density | `MultiplicativePositivityGeometry.multiFrequency_purchase_le_two`, `interior_zero_invisible`; `exists_nonneg_density_with_layer` |
| Euler product, natural norms, natural coefficients, simple pole, linear counting | `½`: every finite layer at every depth below `½` is realized | `exists_integer_norm_euler_product_with_layer`; pairs with further structure in `ArithmeticPositiveDuality…exists_two_scale_integer_norm_euler_product` |
| Euler product over the rational primes with natural exponents | every finite layer at depth beyond `1/15` is realized | `exists_rational_prime_euler_product_with_layer` |
| Mean square over a family, then Cauchy–Schwarz | `3/8` | `RHTower.fixed_slot_boundary`, `retunedBoundary_sharp_minimum` |
| One-sided floors on windows of one fixed length | finite strata: the isolated pair at the ordinate `2π/(3L)`; every length together is floor-free | `hasFiniteStratumModel_windowFloor`; `SurfaceOfSpecZ…asymptoticAbscissaLaw_of_lengthDependent_floors` |
| Linear statistics under projection | no sign at any depth | `exists_splitIncrement_neg_and_pos` |
| Heat statistics | no floor in the depth; the height `(2t)^{−1/2}` | `heatSymbol_splitIncrement_sign` |
| Window non-attainment, window moments with one exponent, unit gaps | none | §5 |

Positivity in tangent form: the one-sided bound that positivity of `Λ` gives for the trace is of
the order of the pole term, `e^{u/2}`; after normalization by `e^{bu}` it is `Ce^{(½−b)u}`. It
constrains the top trace only at `b = ½`, where it is the nonvanishing on `Re s = 1`
(`SurfaceOfSpecZ.tendsto_normTrace_half_of_re_lt_one`). Below that line it constrains nothing:
for every `Θ < 1`, all ordinates and all multiplicities, the density
`e^u − Σ 2m_j e^{Θu} cos(γ_j u) + 2M e^u 1_{u ≤ u₀}` is nonnegative on the half-line and its
Laplace transform is `1/(s−1) − Σ m_j (1/(s−ρ_j) + 1/(s−ρ̄_j))` plus an entire function: a
positive prime measure with a simple pole and the prescribed finite top layer
(`exists_nonneg_density_with_layer`).

## 7. What a producer must be

| # | Requirement |
|---|---|
| R1 | No floor: it acts at every depth |
| R2 | Its inequality is of kind (a), (b), (c) or (d) |
| R3 | It uses the functional equation and the Euler product jointly: it fails on the Liouville twist, on a lattice with a pair, on the integer-norm one-offs |
| R4 | It is pointwise in the zeros |
| R5 | It is not a mean square over a family and uses no large sieve |
| R6 | It proves no margin and no wrong constant, weight or scale |
| R7 | It does not follow from the explicit formula alone |
| R8 | For AAL it acts on the finite datum of the top layer, normalized by the top exponent |

**Tests for a proposed mechanism.** (1) Its floor. (2) Its kind and the receiver that takes it.
(3) The fakes: it must fail on each for a stated reason. (4) The limit `δ → 0`: statement and
constants must not degenerate. (5) No mean square over twists. (6) Its tangent form.

**Where each kind ends.** The first theorems leave one statement per kind for a producer to
prove, and exclude the sources listed.

| Kind | Excluded as a source | What a producer has to prove |
|---|---|---|
| Non-attainment (a) | identities of the explicit formula and both symmetries (every finite datum is a top layer); positivity below `Re s = 1` (every finite datum has a positive prime density); the Euler product with natural norms and coefficients (every finite datum is realized); normal families of translates (only the zero limit); integrality alone (a quantum without an a priori bound) | on some late windows of one length the smoothed prime error is of smaller order than its own rate |
| Unit gap (b) | the scattering tower (it keeps the count); the clock (it lies below its limit) | approximants of `ζ` with at most one zero right of the line; or a form with one negative square for which the zeros are a symmetric spectrum |
| Certificate (c) | non-arithmetic certificates in the limit (they converge to `Λ`) | a feasible weight system at every aperture |
| Amplification (d) | a bound of one order (it reaches the depth `A/2k` only) | a two-sided bound `C_ε e^{εT}` on some late windows, for every `ε` |
| Symmetrization | linear statistics (no sign); additive functionals (mixtures of inner masses) | minimality of `ζ` for the inner mass: the equality case of Jensen's formula, a certificate of kind (c) |

## 8. Tools

**Developed.** Floor calculus on zero configurations. The window bound for exponential sums
(Vandermonde sampling at a step adapted to the window). Uniform attainment and its transfer to
the spline trace, to window moments, to `ψ` and to the primes through prime gaps. Lipschitz and
sup bounds of top traces; their Bohr coefficients. The Lipschitz rate of the full spline trace
and the passage from a moment on a window to a pointwise bound. Quantile discretization of a
general prime density and rounding to natural norms (`PrimeDensity`): the Euler product of the
discrete primes is the zeta function of the density times a factor without zeros right of the
critical line. Parity of right zeros at every depth. Hurwitz
transfer of a unit gap. Second-derivative tests for pair sums on vertical lines; concave functions
on the line; Fourier and heat symbols. The taper argument that turns positive definiteness on
an interval into positive definiteness on the line. The first coefficient test for Dirichlet
series, with the two-sided bound `(z−1)^h Γ(z) ≤ Γ(z+h) ≤ (z+h)^h Γ(z)` for the amplitude of a
reflected half.

**To build.** The top traces of `μ`, `λ` and twisted multiplicative functions in world I on
windows (an explicit formula for their summatory functions), beyond the orders of their
Dirichlet series and the Ω-law of `M` at an attained frontier.
The boundary points of a feasible set as discrete pure objects (the measures of a system with a
null vector). A regulator of the horizon that approaches Weil's form from above. The prime side of
a reflected half on a window (the first coefficient test is global), and of symmetric
completions of zero-free Dirichlet polynomials.

## 9. Questions and open research topics

| # | Question | State |
|---|---|---|
| Q1 | Which mechanisms have floor zero? | receivers of the four kinds are in Lean; every estimate of the census has a positive floor |
| Q2 | Non-attainment for `ζ` (B170): is `ψ(x) − x` of smaller order than its own rate on some late windows? | open; equivalent to excluding world I; the top layer alone does not decide it (integer-norm one-offs, isolated pairs) |
| Q3 | A source of a unit gap (B117, B171): functions with at most one right zero and limit `ζ`; a form with one negative square in which the zeros are a symmetric spectrum | open; the form is Weil's form without the pole term, and its index is one exactly under RH (`RHTower.riemannHypothesis_iff_not_exists_negDef_markovPlane`); neither the tower (`towerQuotient_unit_gap_iff`), nor the clock (`greenWeilEnergy_le_form`), nor the heat flow (`eventually_two_le_nonrealZeroCount`) supplies it |
| Q4 | A functional that decreases under projection and has an arithmetic evaluation (B172) | no linear statistic; additive functionals of the depths are mixtures of inner masses; what is open is a minimality principle for `ζ`, the equality case of Jensen's formula (kind c) |
| Q5 | A bound for all moment orders with one exponent (B173) | on windows it is equivalent to a sub-exponential two-sided bound of the trace on those windows (`windowMomentsBounded_iff_windowSupPowersBounded`): open, and of the strength of the Riemann hypothesis on some late windows |
| Q6 | A certificate at every aperture that is not `Λ` | open at finite aperture (the feasible sets have nonempty interior where windows have margin); in the limit every family of certificates is `Λ` |
| Q7 | The tangent form of every mechanism of the corpus | positivity: only at depth `½`, void below (§6, `exists_nonneg_density_with_layer`); identities of the explicit formula, temperedness, both symmetries: void (`exists_config_with_top_layer`); the Euler product with natural norms: void (`exists_integer_norm_euler_product_with_layer`); integrality: the quantum of a multiplicity; verification: a lower bound for the ordinates; normal families of translates: void (`tendsto_normalization_zero`). What is not void is the joint use of the Euler product and the functional equation, for which no model is known |

Open topics: joint use of the two structures on the tangent datum; a bound for `ζ` along one
phase return on a domain reaching a top zero; nonlinear relations between the tangent data of
multiplicative functions; regulators that approach Weil's form from above; a discrete system of
generalized primes whose integers are counted with an error below the square root and whose
zeta function has a non-real zero right of the line (the integers have this regularity, no model
of the programme is known to; that no such system exists would contain RH).

## 10. Traps

| Trap | Truth |
|---|---|
| A better constant lowers the floor | The floor is fixed by the mechanism; models exist at every depth above it |
| A power saving is a step towards AAL | AAL needs every depth; a saving is a half-plane and has a floor |
| Long windows are needed to see a finite layer | Every window of every positive length sees it, two-sidedly; one-sided floors need length `> nπ/Γ` |
| Non-attainment needs an exponent | It compares the error with its own rate; no exponent is claimed |
| Higher moments carry more information about a finite layer | On a fixed window its `2k`-th moment has rate `2k·b`: the order multiplies the depth and nothing else |
| A bound uniform in the moment order is weaker than a pointwise bound | On windows the two are equivalent: the trace is Lipschitz at the rate `e^{u/2}` |
| The explicit formula can exclude a top layer | It holds on every tempered configuration; floor `½`; every finite datum is realized |
| Projection to the line lowers natural statistics | No convergent linear statistic is monotone; heat statistics only below a height |
| A regulator at finite cutoff has fewer right zeros | The tower has exactly those of `ζ` at every height; the clock has at least the negative directions of Weil's form; the heat flow has the nonreal zeros of `Ξ` at every small time |
| A suitable normalization makes the translates a normal family at a top zero | Only normalizations tending to zero are bounded; every limit is identically zero |
| A new monotone functional of the zeros is a new input | Additive functionals of the depths are mixtures of inner masses |
| Certificates may be non-arithmetic | Only at finite aperture: they converge to `Λ` in every coordinate |
| A receiver must fail on the fakes | Receivers hold on every configuration; it is the hypothesis that fails on the fakes |
| At most one zero is a weak statement | With the conjugate pairing it is none |
| Positivity of `Λ` survives normalization | Only at depth `½`; below it every finite layer has a positive prime density with a simple pole |

## 11. Context

FFA is the search programme for the case that every route stays a receiver
(`docs/reports/review-1011/obstacles-summary.md` §4). It reads the other programmes through two
questions: what is the floor of the mechanism, and which floor-free kind does the receiver accept.

| Neighbour | Relation |
|---|---|
| SurfaceOfSpecZ (scale locality) | supplies traces, top layers, one-sided floors; FFA adds two-sided attainment on every window, moments and the `ψ` form |
| ExceptionalLayerTheory | reads the top divisor by filters at escaping heights; FFA states the same world as non-attainment at the scale of the primes |
| ZeroConfigurationGeometry | abscissa laws, finite oscillation of the prime error, critical projection; FFA uses them as the language of world I |
| SelectiveArithmetic | prices and fakes by aspect on the ladder; its trivial aperture is the floor of sizes; its feasible sets are the certificates of kind (c) |
| MultiplicativePositivityGeometry | complete content of coefficient positivity: the floor `½` of that mechanism |
| FamilyContinuationTheory, MetaplecticMobiusDescent | the half-plane producer and its budget: a mechanism with floor `3/8` |
| ArithmeticPositiveDuality | integer-norm one-offs: models with an Euler product and a finite stratum; FFA applies their discretization and rounding to an arbitrary prime density and obtains every finite layer at every depth |
| ArithmeticOrientationGeometry, HeckeKreinToeplitz | index laws: the unit gap at the level of forms |
| ArithmeticOfSquareRootPrecision, RHTower (Weil cone) | feasibility at every aperture and uniqueness of the Weil cone, which FFA combines into the convergence of certificates |
| HyperbolicArakelovTheory | the scattering tower whose secular function FFA shows keeps the count; the clock regulator, which FFA shows lies below its limit |
| ArithmeticAuxiliaryDynamics | phase returns and the transport of a zero along a bounded return; FFA adds that no normalization of the translates is bounded |
| InfiniteRankWeilTheory | the Vandermonde window bound at integer levels, which FFA extends to real windows |

## 12. Success criteria and contributions

The programme succeeds if it produces one of: a producer satisfying R1–R8; or, for each track, the
theorem that decides it. A contribution is one of the following and nothing else.

1. A **floor**: a model that bounds the floor of a named mechanism from below, or an exclusion
   that bounds it from above, as a theorem.
2. A **receiver without a floor**: an implication to AAL, to a half-plane or to RH whose
   hypothesis is of kind (a)–(d), does not mention an exponent below the top one, and is the
   same statement at every depth.
3. A **kill or survivor** of a track: a theorem that a whole class of statements cannot produce,
   or the exact statement a producer of that class must prove.
4. A **tangent form**: what a mechanism becomes after normalization by the top exponent.
5. A **producer**: an unconditional theorem of the form required by a receiver of 2.

Not contributions: further equivalents of RH without a floor-free hypothesis; estimates with a
positive floor; one-structure calibrations that repeat an existing model; statements in law.
