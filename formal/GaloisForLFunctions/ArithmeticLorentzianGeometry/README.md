# Arithmetic Lorentzian Geometry

Arithmetic Lorentzian geometry studies how arithmetic constructions produce a quadratic form
with at most one positive square, and how that signature survives composition, restriction and
passage to a limit. Its target is the specified intersection form of the scaling surface,
including the infinite place, the pole plane and the diagonal. The Hodge index of that form is
equivalent to RH. A useful construction must therefore explain the origin of the sign, not
express the sign in another language.

The programme owns the construction and composition of signature certificates: elementary
objects with a proved signature, operations that preserve it, and the exact costs of combining
them. Over finite fields Weil's theorem has this shape: Bézout makes the Frobenius Gram Metzler,
Frobenius acts conformally with factor `q`, and the Hodge index is a trickle-down inequality on
one Frobenius ladder. Over `ℤ` the sign hypothesis is present in the Euler gauge, local forms are
present at every prime and at the infinite place, and the conformal symmetry is absent. The
programme asks which arithmetic structure replaces it.

Namespace: `GaloisForLFunctions.ArithmeticLorentzianGeometry`.
Umbrella: [ArithmeticLorentzianGeometry.lean](../ArithmeticLorentzianGeometry.lean).

## Mathematical target

Three problems must remain separate.

1. **Construction.** Build a form with a proved signature from elementary arithmetic objects.
2. **Identification.** Prove its equality with, pullback relation to, or domination of the actual
   intersection form, including the Γ-term, the two pole moments and the diagonal.
3. **Exhaustion.** Carry the comparison to every required signed test in a topology controlling
   the full pairing.

An abstract Lorentzian model solves only the first problem; a finite positive family solves a
restricted instance. Neither is an RH proof without the remaining bridges.

The decisive parameter of the atomic test families `f_x = Σ_{n≤N} x_n g(·−log n)` is the
**overlap ratio** `K = w/δ_N`, `δ_N = log(1 + 1/N)`, of the bump width to the spacing of the
atoms. Up to a fixed ratio the archimedean self-energy pays the prime form and, through the tilt
of the prime rows, the pole, for every bounded twist of the coefficients alike
(`TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing`); at unbounded overlap (fixed width) positivity of
the atomic Weil Grams is RH (SpacingScaleHarmonicAnalysis). In the language of this programme
small overlap is the **stability regime** of a Metzler form, which ends at the Robin–Euler threshold
`exp(2θ′(0) + κ_L(φ) + γ)` below the spacing, and the rest of bounded overlap is the
**trickle-down regime**. The programme's central conjecture is the trickle-down inequality for
`ζ`'s Euler-gauge intersection form at every fixed overlap ratio, uniformly in `N`; uniformity
in `K` is RH. Beyond `K = 1` the conjecture is a trickle-down inequality with a gap rather than a
Metzler one: no gauge of the atomic basis is Metzler there.

## Questions

1. **Hodge index without a surface.** Which forms on the atoms `log n` come from Lorentzian
   objects built from local factors and the scale map? Exactly the Lorentzian forms: every
   Hessian of the closure at a nonnegative point is symmetric, nonnegative and hyperbolic, and
   every such form is the Hessian of its own quadratic. The Euler-product Hessian is Lorentzian for
   every nonnegative local datum and is not the Weil pairing; the atomic intersection form of `ζ`
   has a negative diagonal and is reached only by identification, and its Hodge index is a
   trickle-down inequality.
2. **The sign as a hypothesis.** What is the positivity locus of the gauge torus? Modulo the
   archimedean characters `n^{iτ}` it is the Euler point: the sign is a gauge fixing by the
   archimedean place along the successor. A periodic successor holonomy is flat on the torus, so
   Dirichlet characters, whose holonomy is periodic, lie off it, and every other torus point has
   aperiodic holonomy. On the atomic family the Metzler sign rejects every twin that flips a prime
   of the horizon, while hyperbolicity alone does not.
3. **Transfer.** Which operations preserve the signature, and is the Euler product one? Pullback,
   domination, conditionally negative sums and products in disjoint variables do; sums do not. For
   Metzler forms local-to-global is `(TD)`, a sum-closed condition, and polar gluing prices a sum
   exactly. For polynomials the mixed Hessians of a Lorentzian polynomial trickle down, so the
   class is closed under differentiation, nonnegative substitution and products: the Euler
   product of Lorentzian local factors, composed with any nonnegative scale map, has one positive
   square at every nonnegative point. Signature along all nonnegative directions forces an
   M-convex support, so this mixed class is the class of Lorentzian polynomials in coefficient
   form. The closure is blind to the Euler point.
4. **Realization.** What replaces Frobenius? Over `ℤ` no conformal map: dilations are boosts, and a
   ladder of isometric translates with decaying couplings holds its Hodge index only in the
   stability regime, so its positive square must come from the pole plane or from couplings that
   grow along the ladder. Over `𝔽_q` the trickle-down inequality is a square-root count, a finite
   piece of the ladder decides,
   and the Frobenius ladder of the local factor at `p` has the Hodge index exactly when RH over
   `𝔽_p` holds for it. The local polynomial itself is Lorentzian only at the Weil bound, hence
   never at a prime: Ramanujan and Lorentzian are opposite inequalities. Over `ℤ`, at a
   fixed fraction of the spacing, the archimedean self-energy distributed by the tilt of the prime
   rows supplies `(TD_π)` and pays the polar dispersion. In Cayley coordinates `w = 1 − 1/s` the
   functional equation is the reflection `w ↦ 1/w̄` and multiplication by `w` acts on the Li
   ladder: it preserves the reflected pairing, and is conformal with factor `|w_ρ|²` on the
   evaluation at each zero. RH is reflection positivity of this ladder, and equivalently its Metzler
   sign; the trickle-down content sits inside the sign.
5. **The critical regime.** What happens at the spacing scale? The Metzler sign holds exactly up
   to overlap ratio one. The Hodge index, `(TD_π)` and hyperbolic links hold up to a fixed ratio
   `c★`, and eventually in `N` up to the fraction `K★(φ, ε)` at which the pole defect pays the
   pole. At `K★_∞(ε)` Weil positivity holds for every `C²` test supported in the windows
   `[log n, log n + w]`, whatever its profile. With sharp constants, the Fubini bound on window
   pairs and the prime number theorem the same mechanism reaches `≈ 0.108` of the spacing for
   plateau profiles, a quarter of the Robin–Euler threshold, and `≈ 0.072` for every profile.
   Paying the pole term in absolute value cannot pass about half of that threshold. A uniform
   margin stops at `K√(log N)`. The atom block leaves the stability regime at the Robin–Euler
   threshold `exp(2θ′(0) + κ_L(φ) + γ)`, where the pole vector carries a positive square of `−M`.
   At every width, Weil positivity on the atomic tests is exactly a gap of `M` on the pole
   complement `Σ x_n/√n = 0` and one scalar condition along the pole. Between `c★` and one the
   open content is `(TD_π)` for a connected Metzler form; beyond one no gauge of the atoms is
   Metzler.

## Objects and language

For a finite real symmetric matrix `Q`, write `B_Q(x,y) = xᵀQy` and `Q[x] = B_Q(x,x)`.
`IsHyperbolic Q` is the reverse Cauchy–Schwarz inequality `Q[x]Q[y] ≤ B_Q(x,y)²` whenever
`Q[x] > 0`; for symmetric matrices it is equivalent to at most one positive square. *Hyperbolic*
describes a quadratic form, not real-rootedness of a polynomial. `IsLorentzian Q` adds entrywise
nonnegativity in specified coordinates; `IsMetzler Q` asks only for nonnegative off-diagonal
entries. Both depend on the coordinates.

| Object | Mathematical role |
|---|---|
| Finite test spaces and their actual Gram matrices | Keep the target pairing visible throughout construction |
| Pole plane `⟨H,V⟩`, `H² = V² = 0`, `H·V = 1` | Supplies the positive direction and records global degree data |
| Positive anchor `e`, polar row `B_Q(e,−)/Q[e]` | Define the primitive hyperplane and the degree normalization of a local form |
| Schur reserve `R_Q(x) = B_Q(e,x)²/Q[e] − Q[x]` | Negative energy left after the positive direction is removed |
| Polar dispersion `V_e` and its matrix `C_e` | Exact incompatibility of local polar rows |
| Row sums `D = Q·1`, positive weights `π` | Separate the stability regime `Qπ ≤ 0` from the trickle-down regime `Qπ > 0` |
| Links `T_i` with `Σ T_i = Q`, `T_i·1 = Q e_i` | Local pieces whose signature yields the global one |
| Trickle-down defect `QD⁻¹Q − Q` | The positive semidefinite quantity that, unlike hyperbolicity, adds |
| Even and odd reflected Frobenius evaluation | Split the span Gram into a difference of positive Grams |
| Half-defect correction `C_n = E₋*E₋`; distinct outer spectrum | Coherent positive repair and its exact rank cost |
| Hodge completion `[[J,B],[B*,B*JB−G]]` | Transfer a repair while preserving the pole plane and its couplings |
| Prime ladders, successor, dilations `M_p S = S^p M_p` | Arithmetic operations and their compatibility relations |
| Gauges with fixed infinite place and pole | Distinguish changing coordinates from changing the completed source |
| Overlap ratio `K`; ratio and non-ratio prime lags | Locate where a form first reads the arithmetic gauge |
| Horizon counterterms, finite parts with local Euler constants `γ_p` | Renormalized local data of the prime place |
| Exhaustions with explicit norms | Specify what a finite signature theorem can reach |
| Lorentzian polynomials, mixed derivatives `∂_{v_1}⋯∂_{v_m}`, mixed Hessians | Signature certificates of higher degree and their closure operations |
| Isometric and conformal ladders `(λ^{min(i,j)} a_{|i−j|})` | Separate symmetries that can host the positive square from those that cannot |
| Covered measure of an atomic family | Measure what a family of tests can approximate |
| Cayley points `w_ρ = 1 − 1/ρ`, Li couplings `ℓ(n) = Re Σ_ρ m_ρ(2 − w_ρ^n − w_ρ^{−n})`, Cayley ladder `(ℓ(|i−j|))` | The functional equation as the reflection `w ↦ 1/w̄`; RH as reflection positivity |

Real quadratic and Hermitian forms have distinct APIs. Complex test spaces retain conjugation
and Hermitian inertia; a real calculation is not automatically its complex analogue.

## Foundational principles

**Fix the pairing.** Every signature claim names the full form and its test space. A positive
form manufactured from prime data is insufficient without identification or comparison in the
direction the target needs.

**Prove local signature from the source.** A link definition cannot contain the desired Hodge
inequality as an unproved field. Links belong to a class whose signature is proved by
arithmetic, counting or a valid closure operation.

**Measure compatibility.** Local signatures need not add. Polar directions can disagree;
overlapping tests have cross terms; local regulators can spend the same pole budget twice. These
costs belong in the theorem.

**Separate gauge selection from sign production.** The successor connection and the archimedean
kernel fix the Euler gauge; that does not establish Hodge index in that gauge. Prime-side unitary
equivalence can preserve spectrum while erasing the distinction a proof needs.

**Demand selectivity.** Estimates that use only coefficient sizes hold for every bounded twist
and stop at a finite overlap ratio. A certificate beyond it must fail for some twist and for the
golden fake datum, and the theorem must name why.

**Keep global resources global.** The two pole moments and the positive direction cannot be
allocated independently at every prime; a comparison must show how allocations recombine.

**Treat the limit as mathematics.** Growing dimension, shrinking support and fixed-scale
overlap are different properties. Prove density or a sufficient orbit criterion in the topology
the form requires.

**State the scope of an obstruction.** Failure of one localizer, counterterm or symmetry
mechanism does not exclude every geometry. Extract the sharp boundary or the positive
construction it exposes.

## Tools

- Degree-two signature calculus: reverse Cauchy–Schwarz, domination, pullback, CND closure.
- The block Hodge index theorem: with a hyperbolic pole plane, one positive square ⇔ nonnegative
  polar defect `2(d·H)(d·V) − d²`.
- The Metzler Hodge index theorem, its weighted and quantitative forms, and hyperbolic links.
- Gauge rigidity: unimodular rigidity of nonnegative entries, odd triangles, pole-row fixing.
- Polar gluing with its exact dispersion, and reflection splitting with the optimal repair.
- The Markov pairing of atoms: separation, the overlap law, tilted per-atom margins.
- Frobenius ladders, square-root counts and finite-depth criteria for curve data.
- Lorentzian polynomials: the Hessian and mixed-Hessian trickle-down theorems, the
  Alexandrov–Fenchel and Khovanskii–Teissier inequalities, strong log-concavity at nonnegative
  points, and closure under differentiation, nonnegative substitution and products.
- The Euler product closure for Lorentzian local factors of any degree, and the Ramanujan–Lorentzian
  rigidity of local L-factors at the Weil bound.
- The Turán layer of `ξ` and Laguerre's inequality for its Jensen polynomials on the half-line.
- The covered-measure bound: an atomic test of overlap ratio `K` lives on measure `≤ K`; adapted
  families cover the fraction `c` of their range and are Metzler below the Nyquist rate.
- The ladder dichotomy: isometric and conformal ladders with decaying normalized couplings hold
  the Hodge index only in the stability regime.
- The end of the stability regime: beyond the Robin–Euler threshold the atom block has a positive
  square along the pole vector.
- The multiplicative Hardy inequality `(Σ√n x_n)² ≤ C_H(N²/log N)(D_N + |x|²)`: the pole defect
  controls the `V`-row and pays the pole term.
- Exchange in a Lorentzian form (`Q_{ai}, Q_{jk} > 0 ⇒ Q_{aj} > 0` or `Q_{ak} > 0`), the
  M-convexity of mixed-Lorentzian supports and log-concavity of coefficients along exchange
  directions.
- Holonomy rigidity of the successor connection: periodic on the torus ⇒ flat.
- Window tests: the atomic estimates with per-atom profiles, coefficients the window norms, and
  the decomposition of every test supported near the logarithms into windows.
- The sharp stability toolkit: one-sided pair windows, sharp Lévy rows, the λ-parametrized
  top-atom payment, the `N^b`-split Hardy inequality and the `ρN/log N` pairing of the pole rows.
- The mass bound for window correlations `∫|c_mn| ≤ ‖G_m‖₁‖G_n‖₁`, and the up-row bound of the
  multiplicative Hardy inequality under the prime number theorem.
- The rank-two reduction: `Q + 2AB ≥ 0` iff `Q ≥ 0` on `ker A` and `Q + 2B ≥ 0` on `{A = 1}`. For
  atomic tests `A` is the pole functional `Σ x_n/√n` at every width.
- The Cayley reflection formula `Q_K[c] = −2 Re Σ_a m_a p_c(w_a) p_c(w_a⁻¹)` on primitive vectors,
  and depth-one probes `Q[e_n − e_0] = 2ℓ(0) − 2ℓ(n)`.

## Core theory

### Degree-two signature calculus

[LorentzianFormsAtDegreeTwo](LorentzianFormsAtDegreeTwo.lean): reverse Cauchy–Schwarz ⇔ no
positive definite plane ⇔ nonpositivity on a hyperplane. Pullback preserves hyperbolicity, and a
nonnegative map preserves the Lorentzian sign. A form dominated by a hyperbolic form is
hyperbolic (`IsHyperbolic.of_le`): subtracting a positive semidefinite counterterm never creates a
positive square. Sums fail (`not_isHyperbolic_add_rankOne`): two Lorentzian rank-one forms add to
the identity of `ℝ²`. Conditionally negative definite forms are hyperbolic and closed under sums:
the one class in which summation preserves the signature.

### The arithmetic bridge

[TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity](TheHodgeIndexOfTheScalingSurfaceIsHyperbolicity.lean):
RH holds iff every finite Hermitian Gram of the scaling surface satisfies `D²E² ≤ |D·E|²`
whenever `D² > 0`. Any form containing a hyperbolic plane becomes entrywise nonnegative after the
shift `f_i ↦ f_i + t(H + V)`, without changing inertia: nonnegativity carries information only
in a fixed basis.

### Links, trickle-down and the Metzler dichotomy

[TheHodgeIndexTricklesDown](TheHodgeIndexTricklesDown.lean): for a symmetric Metzler form with
positive row sums `D` and connected support,

\[
 \text{one positive square}\iff Q[v]\le\sum_i\frac{(Qv)_i^2}{D_i}\ \text{for all }v
 \iff\text{hyperbolic links exist},
\]

and the links may be taken rank one plus negative semidefinite. The middle inequality says that
`QD⁻¹Q − Q ⪰ 0`, a condition closed under addition: local-to-global for the Hodge index of a
Metzler form is a sum of local semidefinite defects. Connectivity and the Metzler sign are both
necessary. Quantitative trickle-down — the inequality up to `ε‖v‖²_D` together with a gap on the
primitive hyperplane — gives `Q ≤ μ₋(ε)D` there, `μ₋ = (1 − √(1 − 4ε))/2`.

[TheMetzlerDichotomy](TheMetzlerDichotomy.lean): if `Qπ ≤ 0` for some `π > 0` then `Q ≤ 0`
(stability regime); if `Qπ > 0` with connected support then hyperbolicity ⇔ weighted
trickle-down `(TD_π)`. Every unconditional positivity of Weil's form on atomic families has the
shape of the stability regime: the self-energy on the diagonal pays the row sums.

### Calibration over finite fields

[TheFrobeniusLadderIsMetzler](TheFrobeniusLadderIsMetzler.lean): the Frobenius Gram of
`H, V, Γ₀, …, Γ_K` splits as `Q[(p,d)] = 2(p_H + d·V)(p_V + d·H) − δ(d)`, so Hodge index ⇔ the polar
defect `δ` is nonnegative. It is Metzler iff the point counts are nonnegative (Bézout), and every
curve datum has a positive weight with positive image and connected support. Hence Hodge index ⇔
`(TD_π)`. The golden datum (`q = 5`, `β = φ, φ⁻¹`) is Metzler and connected and violates `(TD_π)`:
over `𝔽_q` the content of Weil's theorem is the trickle-down inequality, and integral
nonnegative counts, the functional equation and Bézout do not construct it.

[TheTrickleDownInequalityIsTheSquareRootCount](TheTrickleDownInequalityIsTheSquareRootCount.lean):
what does construct it is a count. Every span class lives on some ladder, so `(TD_π)` on every
Frobenius ladder ⇔ `|β_i| = 1` ⇔ the one-sided Lefschetz bound `N_k ≥ q^k + 1 − C q^{k/2}` for all
`k` (`forall_weightedTrickleDown_iff_exists_pointCount_ge`); the golden datum fails every such
bound. For `y² = f(x)`, `f` squarefree of odd degree over a finite field of odd characteristic, the
counts are point cardinalities over the extensions of every degree and the datum is unitary by
Stepanov's count, so every ladder satisfies `(TD_π)` and its weighted Gram has hyperbolic links
(`hyperelliptic_weightedTrickleDown`, `hyperelliptic_hasHyperbolicLinks`). This is Weil's theorem
for these curves as a trickle-down statement with no surface: the local-to-global inequality is
paid by an auxiliary function with many zeros, the input a construction over `ℤ` must replace.

[TheLocalFactorTricklesDownByRamanujan](TheLocalFactorTricklesDownByRamanujan.lean): a finite piece
of the ladder decides. If `H, V, Γ_0, …, Γ_{2g−1}` has the Hodge index, the span defect is a
nonnegative Toeplitz form of size `2g` on complex classes too, which forces `|β_i| = 1`; so
`(TD_π)` holds on every ladder (`forall_weightedTrickleDown_of_isHyperbolic`). For a local factor
`1 − aT + qT²` (genus one) the first ladder has the Hodge index iff `|a| ≤ 2√q`
(`frobeniusGram_one_isHyperbolic_iff`); depth zero never decides, the golden fake passes it
(`golden_depth_one_sharp`). The Kloosterman
sum is real, and by Weil's bound `|K(a)| ≤ 2√p` the Kloosterman factor `1 + K(a)T + pT²` is such a
datum: every ladder is Metzler, satisfies `(TD_π)` and has hyperbolic links
(`kloosterman_trickleDown`). The local Lorentzian input at a prime is the Riemann hypothesis over
`𝔽_p` for its local factor; with the Euler-product closure, which is Lorentzian for every
nonnegative local datum, the content of the Hodge index over `ℤ` lies entirely in the
local-to-global step.

[RamanujanAndLorentzianMeetOnlyAtTheWeilBound](RamanujanAndLorentzianMeetOnlyAtTheWeilBound.lean):
that input is a statement about the ladder, not about the local polynomial. Homogenize a
sign-normalized local factor `1 + a_1T + ⋯ + a_dT^d`. If it is Lorentzian its normalized
coefficients are log-concave, `b_k ≤ b_1^k` (`le_pow_of_logConcave`), and `a_d = (√q)^d` forces
`a_1 ≥ d√q` (`sqrt_le_of_isLorentzianPoly`). Ramanujan gives `a_1 ≤ d√q`, so the two meet only at
the maximal factor `(1 + √qT)^d` (`ramanujan_lorentzian_rigid`, `isLorentzianPoly_maximal`). At a
prime an integral trace cannot equal `d√p`, so no Ramanujan local factor over `𝔽_p` is Lorentzian
(`not_isLorentzianPoly_at_prime`). For elliptic curves `1 + aT + pT²` is Lorentzian iff `a² ≥ 4p`,
the reverse of the Hasse bound (`isLorentzianPoly_quadFactor_iff`, `not_isLorentzianPoly_of_hasse`).
The Lorentzian local inputs of a product closure cannot be the local L-factors.

### The atomic family of `ζ`

[TheAtomicFormIsMetzlerBelowTheSpacing](TheAtomicFormIsMetzlerBelowTheSpacing.lean): the Markov
pairing `M(f, d)`, polar form of `M = 2θ′(0)‖·‖² + levyEnergy − primeSum`, is symmetric and bilinear
on compactly supported `C²` tests, so `M(f_x) = Σ x_m x_n M(g_m, g_n)` on atomic tests. For a
nonnegative bump supported in `[0, w]` and atoms at log-distance `> w`, `M(g_m, g_n) ≤ 0`: the
overlap vanishes, the Lévy cross integrand is pointwise `≤ 0`, and the prime pairing is a sum of
nonnegative terms. Hence for `w < δ_N` the Gram of `H, V, g₁, …, g_N` — pole plane, pole row
`(∫ g_n e^{−u/2}, ∫ g_n e^{u/2})`, atom block `−M(g_m, g_n)` — is Metzler, connected through `H`, and
has an explicit positive weight with positive image. Its polar defect is Weil's form, so Weil
positivity on the separated atomic family ⇔ hyperbolicity ⇔ `(TD_π)`
(`weilQuad_finAtomicTest_nonneg_iff_weightedTrickleDown`). The sign hypothesis is a theorem for
`ζ` below the spacing; the content left there is the trickle-down inequality itself.

[TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing](TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing.lean):
at a fixed fraction of the spacing that content is a theorem. The row-by-row estimate of the
stability law gives `M(f) ≥ ‖g‖² Σ_m μ_m x_m²` with a per-atom margin, and at `w ≤ c★δ_N` the tilted
prime rows give `μ_m ≥ 1 + (m/8N) log m` (`one_add_le_atomMargin`): the margin grows along the atoms
that carry the pole moment. The pole term of Weil's form is `2AB`, `A = ∫ f e^{−u/2}`,
`B = ∫ f e^{u/2}`; weighted Cauchy–Schwarz with `Σ 1/(mμ_m) ≤ 1 + log N` and
`Σ m/μ_m ≤ 16N²/(1 + log N)` gives `A²B² ≤ 16e^w(wN)²‖g‖⁴X²`, `X = Σ μ_m x_m²`, so the pole costs at
most the margin (`sq_mul_poleMoments_le`, `two_mul_abs_poleMoments_le_margin`). Hence Weil's form is
nonnegative on every *signed* atomic test at every width `w ≤ c★δ_N`, uniformly in `N`
(`weilQuad_atomicTest_nonneg`), and the atomic intersection form of `ζ`, pole plane included, has
one positive square, satisfies `(TD_π)`, and its weighted Gram has hyperbolic links
(`atomicIntersectionGram_isHyperbolic`, `weightedTrickleDown_atomicIntersectionGram`,
`hasHyperbolicLinks_atomicIntersectionGram`). The central conjecture holds at every overlap ratio
`K ≤ c★`, inside the stability regime. The proof is twist-blind (`twin_markov_add_pole_nonneg`).

[TheUniformMarginPaysThePoleOnlyUpToARootLogarithm](TheUniformMarginPaysThePoleOnlyUpToARootLogarithm.lean):
the tilt is necessary. By the rank-two bound `2(a·d)(b·d) ≥ (a·b − ‖a‖‖b‖)‖d‖²`, sharp at
`d = ‖b‖a − ‖a‖b`, the margin model (pole plane, pole rows `a, b`, atom block `−m·1`) has one
positive square iff `‖a‖‖b‖ − a·b ≤ m` (`marginModel_isHyperbolic_iff`). The atomic pole rows are
`a_n = n^{−1/2}α`, `b_n = n^{1/2}β`, so the gap is `αβ(√(H_N S_N) − N) ≥ αβN(√(log(N + 1)/2) − 1)`;
at a fixed overlap ratio and fixed uniform margin the model fails for all large `N`
(`not_isHyperbolic_marginModel_eventually`). A uniform margin stops at `K√(log N) ≍ μ`; the pole is
paid by the growth of the margin along `(n^{1/2})`.

[TheOverlapFrustratesTheMetzlerGauge](TheOverlapFrustratesTheMetzlerGauge.lean): beyond the
spacing the sign of the atom block changes. For a narrow nonnegative Lipschitz bump with
`κ = 2θ′(0) + log(1/(2w)) > 0`, polarization `4M(a, b) = M(a + b) − M(a − b)` shows that atoms at
log-distance `s ≤ w` meet *positively* once the Lévy cost of `g − g(·−s)`, explicitly
`4e^{1/2}K²w²s + O(s²)`, is below `κ‖g‖²` (`markovPair_shift_pos`). Three such atoms form a negative
triangle of `−M`, and a negative triangle admits no unimodular nonnegative gauge
(`not_nonneg_gauge_of_neg_triangle`). Hence at fixed width, for every large `N`, no gauge makes the
atomic form Metzler (`atomicMarkovGram_frustrated_eventually`). The Metzler property is a theorem
below the spacing and fails in every gauge at unbounded overlap; a trickle-down certificate there
needs coordinates other than atoms.

[TheMetzlerThresholdOfTheOverlapRatioIsOne](TheMetzlerThresholdOfTheOverlapRatioIsOne.lean): the
threshold is exactly the spacing. The **overlap law** (`markovPair_shift_ge`): for a nonnegative
`K`-Lipschitz `C²` bump in `[0, w]`, `2w < log 2`, and `0 ≤ s ≤ w`,

\[
 M(g, g(\cdot - s)) \ge \big(2\theta'(0) + \log\tfrac{1}{2w}\big)\langle g, g(\cdot - s)\rangle
 - 2e^{1/2} K w \|g\|_1 .
\]

Beyond the joint support the mixed Lévy integrand is `2ω(y)⟨g, g(·−s)⟩`, so overlapping atoms meet
with their overlap times the self-energy, with constant one. Separated atoms meet *strictly*
negatively (`markovPair_atom_neg`), and a triangle with one negative and two positive entries
admits no unimodular nonnegative gauge (`not_nonneg_gauge_of_odd_triangle`). For the bump
`g₁(·/(Kδ_N))` of a Lipschitz `C²` profile positive on `(0, 1)` the atomic form is Metzler for
`K < 1`, and for every `K > 1` and all large `N` the overlapping atoms `N − 1, N` and the separated
atom `1` form an odd triangle, so no unimodular gauge makes it Metzler
(`metzlerThreshold_overlapRatio`). The sign hypothesis holds for `ζ`'s atomic form exactly up to
atomic resolution. Beyond it the gap on the primitive hyperplane, which Perron–Frobenius supplies
for connected Metzler forms, must be proved directly; quantitative trickle-down
(`qf_le_of_approxTrickleDown`) needs nothing else.

[TheAtomicMetzlerPropertyIsSelective](TheAtomicMetzlerPropertyIsSelective.lean): the sign hypothesis
selects the Euler point on the actual atomic family. The pole row is untouched by a twist of the
prime place and is strictly positive, so a nonnegative unimodular gauge is constant on the atoms
(`gauge_eq_of_poleRow`). For separated atoms only the lag `log p` meets the pair `(1, p)`, so the
twisted prime pairing is exactly `ω(p)(log p/√p)‖g‖²` while the Lévy cross energy is at most
`2wω(log p − w)‖g‖²`. Hence a real twin with `ω(p) = −1` at a prime `p ≤ N` has no Metzler gauge
below the spacing (`not_exists_nonneg_gauge_twinAtomicIntersectionGram`), while `ω ≡ 1` gives
`ζ`'s Metzler Gram.

[ThePoleDefectControlsTheVRow](ThePoleDefectControlsTheVRow.lean): the `V`-row `Σ√n x_n` of the
atoms is where a uniform margin loses `√(log N)`. The pole defect `D_N(x) = Σ_{mt≤N} Λ(t)(x_{mt} −
x_m/√t)²`, the deficit of the prime form below its sharp counterterm, recovers it: the
multiplicative Hardy inequality `(Σ_{n≤N} √n x_n)² ≤ C_H (N²/log N)(D_N(x) + |x|²)` holds for
`N ≥ 3` (`sq_vRow_le`). Since `Σ_{t∣n} Λ(t) = log n`, each atom spreads over its incoming edges,
`√(mt)x_{mt} = √(mt)(x_{mt} − x_m/√t) + √m x_m` splits each edge into a defect and an up-row
term, and Chebyshev's bound makes both `O(N²/log N)` (`vRow_eq`, `sq_edgePart_le`, `mul_upRow_le`).

[ThePoleDefectPaysThePole](ThePoleDefectPaysThePole.lean): keeping the defect in the finite-part
lower bound of the Markov form, `M(f) ≥ ‖g‖²(φ₀|x|² + c₀D_N(x))` with
`φ₀ = 2θ′(0) + log(1/(wN)) + κ_L(φ) + γ − ε − O(w + wN)` (`eventually_markovEnergy_ge_defect`),
and bounding the pole term by Cauchy–Schwarz on the `H`-row and Hardy on the `V`-row,
`2|AB| ≤ c_P e^{w/2} wN ‖g‖²(2|x|² + D_N(x))` (`two_mul_abs_poleMoments_le_defect`), Weil's form
is nonnegative on every atomic test once `φ₀ ≥ 2c_P e^{w/2} wN` and `c₀ ≥ c_P e^{w/2} wN`
(`eventually_weilQuad_atomicTest_nonneg_of_finitePart`). This holds at an explicit fraction
`K★(φ, ε)` of the spacing, eventually in `N` (`eventually_weilQuad_nonneg_at_fraction`,
`eventually_atomicIntersectionGram_isHyperbolic_at_fraction`): the minimum of two overlap bounds,
`1/(A + 2c_Pe^{1/2})` and `exp(2θ′(0) + κ_L(φ) + γ − ε − 2)` — between `10⁻⁴` and `6·10⁻⁴` once
`κ_L(φ) ≥ −2` and `ε ≤ 1/8` — against `c★ ≈ 10⁻¹¹` for the tilted margin at every `N`. The pole is paid by the
Dirichlet energy of the pole relations, not by a tilt; the remaining gap to the Robin–Euler
threshold is the Chebyshev constant `A` of the cross penalty.

[WeilsFormIsPositiveOnEveryTestNearTheLogarithms](WeilsFormIsPositiveOnEveryTestNearTheLogarithms.lean):
the profile is not needed. A window test `Σ_n G_n(· − log n)` carries an arbitrary `C²` profile
in `[0, w]` at each atom (`windowTest`). Below the spacing its norm is `Σ‖G_n‖²`, its prime sum is
the Weil kernel against the window Gram, at most `P_N(y)` with `y_n = ‖G_n‖₂`
(`primeSum_windowTest_le`), and its Lévy energy keeps the diagonal up to pair windows with
correlations at most `y_m y_n` (`levyEnergy_windowTest_ge_diag`). Each window has self-energy at
least `(log(1/w) + 2c_∞ − O(w))‖G_n‖²` (`levyEnergy_profile_ge`), since the shape term is
nonnegative. The defect argument therefore runs on `y`, and eventually in `N`, at every width
`w ≤ K★_∞(ε) δ_N`, Weil's form is nonnegative on every window test
(`eventually_weilQuad_windowTest_nonneg`). The fraction `K★_∞` is `K★` with `κ_L(φ)` replaced by
`2c_∞`. Every `C²` function vanishing off `⋃_{n ≤ N}[log n, log n + w]` is a window test
(`windowTest_of_support`). So Weil's form is nonnegative on the whole infinite-dimensional space
of `C²` tests supported within `K★_∞ δ_N` to the right of the logarithms of the integers up to `N`
(`eventually_weilQuad_nonneg_of_support`). The prime lags `log(n/m)` of these tests reach every
ratio of the horizon. What a fixed overlap ratio controls is the support near `log n`, not the
shape.

[TheArchimedeanCrossEnergyIsOneSided](TheArchimedeanCrossEnergyIsOneSided.lean),
[TheSharpMultiplicativeHardyInequality](TheSharpMultiplicativeHardyInequality.lean),
[TheStabilityRegimeReachesAFixedFractionOfTheRobinEulerThreshold](TheStabilityRegimeReachesAFixedFractionOfTheRobinEulerThreshold.lean):
the fraction `K★ ≈ 6·10⁻⁴` was a matter of constants, not of mechanism.
- Only the pairs `m < n` meet at positive Lévy shifts, and their window carries at most
  `2w ω(log(n/m) − w)` (`window_integral_le_of_pos`, `window_integral_eq_zero_of_neg`).
- The rows obey `Σ_{n ≠ m} 1/|log(n/m)| ≤ 2m(1 + log(N + 1)) + N` (`sum_inv_abs_log_sub_le`).
- With a free parameter, the top atoms cost `(1 + 1/λ)D_N + (1 + λ)B_ψ|y|²`, where
  `B_ψ = log 4 + 4/e` (`sum_top_le_poleDefect_param`).
- Together these give a cross penalty `wN((2(1 + 1/λ)/(1 − κ))D_N + L_λ,κ|y|²)` with constants about
  `6.7` and `16` (`levyEnergy_windowTest_ge_sharp`), where `236` and `1517` stood before.
- Splitting at `N^b` instead of `√N` makes the Hardy weights asymptotically sharp:
  `Σ n/log n ≤ (1/(2b) + η)N²/log N` and `Σ m R_m² ≤ (B_ψ²/b² + η)N²/log N`, eventually
  (`sq_vRow_le_split`, `eventually_edgeWeight_le`, `eventually_upWeight_le`).
- Pairing the pole rows with the parameter `ρ' = ρN/log N` instead of balancing them in a fixed
  ratio brings the pole cost from `107` to about `7.6` (`two_mul_abs_poleMoments_windowTest_le_sharp`).

Eventually in `N`, every window test whose profiles have shape term `β(G_n) ≥ β‖G_n‖²` has
nonnegative Weil form at every width `w ≤ K★_sharp(β, ε, a) δ_N`
(`eventually_weilQuad_windowTest_nonneg_sharp`), where
`K★_sharp = min(1/10, 1/(2C_D), a/C_X, exp(2θ′(0) + 2c_∞ + β + γ − ε − a − 1/25))`,
`C_X ≈ 24`, `C_D ≈ 7.4`. That is about `0.067` of the spacing for plateau profiles and about `0.048`
for every profile, against a Robin–Euler threshold of `≈ 0.43`, respectively `≈ 0.16`.

[TheCrossEnergyOfTwoWindowsIsBoundedByTheirMasses](TheCrossEnergyOfTwoWindowsIsBoundedByTheirMasses.lean),
[TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold](TheStabilityRegimeReachesAQuarterOfTheRobinEulerThreshold.lean):
two more losses are removable.
- The correlation of two windows has total mass `∫|c_mn| ≤ ‖G_m‖₁‖G_n‖₁ ≤ w y_m y_n` (Fubini,
  `integral_abs_pairCorr_le`). Since `ω` is decreasing, a pair at lag `s ≥ 2w` costs at most
  `ω(s − w)‖G_m‖₁‖G_n‖₁` (`integral_levy_abs_pairCorr_le`), and the cross penalty halves
  (`levyEnergy_windowTest_ge_fubini`).
- With `ψ(x) ≤ (1 + η)x` beyond some `X₀` (the prime number theorem), the up-rows of the low atoms
  obey `mR_m ≤ (1 + η)N/(b log N) + N^b`. The high atoms `N/m < X₀` form a harmonic tail of bounded
  size, so `Σ m R_m² ≤ ((1 + η)²/b² + o(1))N²/log N` (`sum_mul_upRow_sq_le_pnt`,
  `eventually_upWeightPNT_le`): Chebyshev's `B_ψ² ≈ 8.2` becomes `1`.

With `λ = 1/4`, `κ = 3/20`, `b = 19/20`, `θ = 2`, `ρ = 3/2`: eventually in `N` Weil's form is
nonnegative on every window test of shape `β` at every width `w ≤ K★_q(β, ε, a) δ_N`
(`eventually_weilQuad_windowTest_nonneg_quarter`), with `C_X ≈ 10.5`, `C_D ≈ 7.0` in place of
`24` and `7.4`. That is `≈ 0.108` of the spacing for plateau profiles, a quarter of `K_RE`, and
`≈ 0.072` for every profile. The method has a ceiling. Positivity needs
`log(K_RE/K) − ε ≥ K·C_X`, and `C_X` keeps the Lévy loss and the pole cost even with optimal
constants, so lower-bounding `M` and paying `|2AB|` stays below about `K_RE/2`. The rest of the
window needs the sign of the pole term.

[TheOverlapRatioIsTheCoveredMeasure](TheOverlapRatioIsTheCoveredMeasure.lean): an atomic test
vanishes off `⋃_n [log n, log n + w]`, of measure at most `Nw ≤ K` since `Nδ_N ≤ 1`
(`measureReal_atomCover_le`, `natCast_mul_atomSpacing_le_one`). So `∫_I (1 − f)² ≥ |I| − K` for
every interval `I` (`sub_le_setIntegral_sq_of_overlap`): at the ratio `c★`, where the Hodge index of
the atomic family is a theorem, no atomic test comes within `L²`-distance `√(1 − c★)` of the
indicator of a unit interval (`one_sub_fixedWidthRatio_le_setIntegral_sq`), and an atomic family
exhausting `[0, log N]` needs `K ≥ log N − ε²` (`le_overlap_of_setIntegral_sq_le`). Bounded overlap
is a statement about test functions of bounded support measure; the exhaustive regime is the
regime of unbounded overlap in which positivity of the atomic Weil Grams is RH. Adapted families,
with a bump of width `w_n ≤ c log(1 + 1/n)` at each atom, are separated for `c < 1`
(`adaptedCell_disjoint`) and cover the fraction `c` of `[0, log(N + 1)]`
(`measureReal_adaptedCover_le`, `sub_le_setIntegral_sq_adapted`): ratio one is their Nyquist
rate. Disjoint nonnegative bumps of any widths meet nonpositively in the Markov pairing
(`markovPair_nonpos_of_disjoint`), so below the Nyquist rate the adapted atomic Gram is Metzler
(`markovPair_adapted_nonpos`): adapted families are the families on which a Hodge index below the
Nyquist rate would approach exhaustion.

[TheStabilityRegimeEndsAtTheRobinEulerThreshold](TheStabilityRegimeEndsAtTheRobinEulerThreshold.lean):
where does the atom block leave the stability regime? The finite part of the Markov form at the
spacing scale is `2θ′(0) + log(1/(wN)) + κ_L(φ) + γ` and the pole vector `n^{−1/2}` attains it
(RenormalizedArithmeticPotentialTheory). Hence, eventually in `N`, once this finite part plus `ε`
is negative, the pole test has `M(f) < 0` (`eventually_markovEnergy_poleTest_neg`) and no positive
weight `π` has `(−M)π ≤ 0` (`eventually_not_stability_atomBlock`): the atom block carries a
positive square along the pole vector. Beyond the Robin–Euler threshold `exp(2θ′(0) + κ_L(φ) + γ)`
the Hodge index needs the pole plane to absorb that square, and it is exactly `(TD_π)`; the
stability regime cannot be extended there by sharper constants.

[TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar](TheHodgeIndexIsAGapOnThePoleComplementAndOneScalar.lean):
what exactly must hold beyond it? For an atomic test `f_x = Σ x_n g(· − log n)` the `H`-row is the
pole functional at every width, overlapping atoms included:
`∫ f_x e^{−u/2} = a₀ p(x)`, `a₀ = ∫ g e^{−v/2}`, `p(x) = Σ_{n ≤ N} x_n/√n`
(`integral_atomicTest_mul_exp_neg_half`). A quadratic plus a rank-two term is nonnegative iff
the quadratic is nonnegative on the kernel of one factor and the affine slice `{A = 1}` carries
`Q + 2B ≥ 0` (`forall_add_two_mul_nonneg_iff`). Hence Weil positivity on the atomic family is
exactly
- `M(f_x) ≥ 0` on the pole complement `p = 0`, and
- `M(f_x) + 2a₀ B(f_x) ≥ 0` on the hyperplane `p = 1`: one scalar, the infimum of a quadratic on an
  affine hyperplane
(`forall_weilQuad_atomicTest_nonneg_iff`). Beyond the Robin–Euler threshold the pole vector has
`M < 0` and `p = H_N > 0`. So if Weil's form is nonnegative on the family, `M` has exactly one
negative direction, transversal to the pole complement (`eventually_markovEnergy_pole_neg_and_gap`).
The crossing of `K_RE` is therefore a gap of the prime form below its pole on `p = 0`, and one
scalar inequality along `p = 1` that the pole term pays.

[HyperbolicityIsBlindTheSignIsNot](HyperbolicityIsBlindTheSignIsNot.lean): the twisted Markov
pairing is symmetric and bilinear, so the polar defect of a twin's Gram is the twin's Weil form
`M_ω(f) + 2AB` (`polarDefect_twin`). The stability law and the pole estimate are twist-blind, so at
every width `w ≤ c★δ_N` every completely multiplicative sign twin has a hyperbolic atomic
intersection Gram (`twinAtomicIntersectionGram_isHyperbolic`). For the Liouville twin
`λ(n) = (−1)^{Ω(n)}`, whose Dirichlet series `ζ(2s)/ζ(s)` has a pole on the critical line, the Gram
is hyperbolic at those widths and admits no Metzler gauge for `N ≥ 2`, while `ζ`'s is Metzler
(`liouville_isHyperbolic_and_not_metzler`). Where the Hodge index of the atomic family is a
theorem it carries no arithmetic; the sign hypothesis is the part that sees the Euler point.

### Conformal symmetry

[FrobeniusIsConformalHeckeIsABoost](FrobeniusIsConformalHeckeIsABoost.lean): over `𝔽_q`, `(F×1)^*`
sends `H ↦ qH`, `V ↦ V`, `Γ_k ↦ Γ_{k+1}` and satisfies `TᵀG_{K+1}T = qG_K`. Over `ℤ`, dilations
`n ↦ pn` preserve the coupled kernel of every twin and act on the pole plane by the boost
`diag(p^{−1/2}, p^{1/2})`: conformal factor one. Power maps `n ↦ n^k`, `k ≥ 2`, and the successor
are not conformal. These statements concern the specified kernels and maps.

[AnIsometricLadderCarriesNoPositiveSquare](AnIsometricLadderCarriesNoPositiveSquare.lean): what the
conformal factor buys. A ladder of isometric translates has a symmetric Toeplitz Gram
`(c_{|i−j|})`. With Metzler couplings it is negative semidefinite at every depth when
`c_0 + 2Σ_{k≤n} c_k ≤ 0` (`qf_toeplitzLadder_nonpos`); if the couplings decay and some depth has a
positive square, a vector and its far translate give two at a larger depth
(`not_isHyperbolic_toeplitzLadder`). So a decaying isometric ladder has the Hodge index at every
depth iff it is negative semidefinite at every depth (`forall_isHyperbolic_toeplitzLadder_iff`):
the single positive square cannot live on it. A ladder with the conformal law of Frobenius,
`G_{i+1,j+1} = λG_{ij}`, is congruent by `diag(λ^{−i/2})` to the Toeplitz ladder of its normalized
couplings `λ^{−k/2}a_k` (`diagConj_conformalLadder`), so it
carries a positive square only if these do not decay (`forall_isHyperbolic_conformalLadder_iff`):
Frobenius ladders carry it because their normalized couplings grow like `q^{k/2}`. Over `ℤ`, the
prime pairing of fixed-width atoms along a `p`-ladder does not decay: at lag `k log p` it weighs
the integers within `e^{±w}` of `p^k`, of total weight `≍ wp^{k/2}`
by the prime number theorem — the conformal weight of the pole plane, met by the pole term.

[RHIsReflectionPositivityOfTheCayleyLadder](RHIsReflectionPositivityOfTheCayleyLadder.lean): over
`ℤ` the role of Frobenius is played by multiplication by the Cayley point. For a weighted
configuration `(m_a, w_a)`, the Cayley ladder is the Toeplitz ladder of the Li couplings
`ℓ(n) = Re Σ_a m_a(2 − w_a^n − w_a^{−n})` (`cayleyLadder`). With `p_c(z) = Σ c_i z^i`, the
reflection formula `Q_K[c] = Re Σ_a m_a(2(Σc)² − 2 p_c(w_a) p_c(w_a⁻¹))` (`qf_cayleyLadder_eq`)
makes the ladder, on primitive vectors, `−2 Re` of the pairing of `p_c` with its reflection under
`w ↦ 1/w̄`. On the unit circle the reflection is conjugation, and `−Q_K[c] = Σ_a 2m_a|p_c(w_a)|²`
(`hasSum_evaluation_of_unitary`). The shift `c ↦ (0, c)` multiplies `p_c` by `z`
(`cayleyPoly_shift`). It preserves every reflected pairing (`cayleyPairing_shift`), and it is
conformal with factor `|w_a|²` for the evaluation at `w_a` (`norm_cayleyPoly_shift`). Depth-one
probes give `Q_{n+1}[e_n − e_0] = 2ℓ(0) − 2ℓ(n)` (`qf_toeplitzLadder_last_sub_zero`). For `ζ`,
`w_ρ = 1 − 1/ρ` and `ℓ(n)` is the paired Li coefficient `2λ_n` (`liCoupling_xi`). With Li's
criterion from the corpus, RH holds iff every Cayley ladder of `ζ` is negative semidefinite on
primitive vectors (`riemannHypothesis_iff_cayleyLadder_nonpos`), iff every ladder is entrywise
nonnegative (`riemannHypothesis_iff_cayleyLadder_nonneg`); under RH every ladder is Lorentzian
(`isLorentzian_cayleyLadder_of_rh`). On this ladder the Metzler sign implies the Hodge index: the
trickle-down step is contained in Li positivity. The couplings never decay
(`not_tendsto_xiLiPaired_re_zero`). If `2λ_n → 0`, Li's criterion with exponential slack gives RH;
every ladder is then hyperbolic, and a decaying isometric ladder would have to be negative
semidefinite, which fails at depth two because `2λ_1 > 0`. Over `𝔽_q` the same ladder on the
normalized eigenvalues has `ℓ(n) = 2(2g − Σβ_i^n)` (`liCoupling_curveDatum`). Its sign at depth
`n` is the Weil bound `N_n ≥ q^n + 1 − 2g q^{n/2}` with the sharp constant
(`liCoupling_nonneg_iff_pointCount_ge`). Reflection positivity of every ladder is RH for the
curve (`unitary_iff_cayleyLadder_nonpos`), and the golden datum fails it
(`golden_not_cayleyLadder_nonpos`).

### Gauge fixing and the successor

[TheSignIsAGaugeFixing](TheSignIsAGaugeFixing.lean): for `N ≥ 6` and relative prime weight `t ≥ 2`,
the coupled atomic kernel `A + t·conj χ(m)χ(n)P` of a completely multiplicative unimodular twin
has an entrywise nonnegative gauge on `[1, N]` iff `χ(p) = 1` for every prime `p ≤ N`; with the
archimedean kernel of `ζ(s − iτ)` the condition is `χ(p) = p^{iτ}`. The archimedean kernel fixes
the gauge along successor edges, where the prime kernel vanishes. The Lorentzian sign hypothesis
is therefore a gauge fixing performed by the archimedean place, invisible to every form built
from the prime kernel alone.

[TheSuccessorConnectionIsTheArchimedeanGaugeField](TheSuccessorConnectionIsTheArchimedeanGaugeField.lean):
in the gauge `conj χ` the archimedean kernel on the edge `(n, n+1)` carries the phase of the
successor connection, nonnegative on `[1, N]` iff the prime phases through `N + 1` are trivial.
The successor shift itself raises and lowers the atomic prime form on nonnegative profiles; its
connection, not a monotonicity, is the usable object.

[APeriodicSuccessorHolonomyIsFlat](APeriodicSuccessorHolonomyIsFlat.lean): a completely
multiplicative function without zeros whose successor ratio is periodic is `≡ 1`. Periodicity
gives `f(n + q) = c f(n)`, at `n = mq` this becomes `f(m + 1) = c f(m)`, and `f(4) = f(2)²` forces
`c = 1` (`eq_one_of_ratio_periodic`). On the torus the successor connection is periodic iff `ω` is
the Euler point (`succConn_periodic_iff_euler`). A periodic completely multiplicative function
other than `1` — a nontrivial Dirichlet character — must vanish somewhere
(`exists_eq_zero_of_periodic`). Holonomy separates the Dirichlet characters, whose holonomy is
periodic but which leave the torus, from the torus points, whose holonomy is aperiodic away from
the Euler point.

### Local factors and the Euler-product closure

[LocalFactorsAndTheEulerProductClosure](LocalFactorsAndTheEulerProductClosure.lean): the prime
kernel on a ladder `1, p, …, p⁵` is Metzler with two positive squares for every prime — no local
Lorentzian sign exists factor by factor. A nonnegative kernel minus its row sums is negative
semidefinite: a jump form, such as the archimedean place, contributes no positive square. The
Hessian of `∏_p ⟨L_p, y⟩` at a positive point is a positive multiple of the second elementary
symmetric form of the normalized local data, hence Lorentzian for every nonnegative local datum.
The product closure cannot distinguish the Euler point from other nonnegative Euler products,
and it contains neither the Γ-term, the pole plane nor the diagonal.

[TheEulerProductOfLorentzianLocalFactorsIsLorentzian](TheEulerProductOfLorentzianLocalFactorsIsLorentzian.lean):
the closure holds for local factors of every degree. Lorentzian polynomials in complementary
variables have a Lorentzian product (`IsLorentzianPolynomial.mul_of_supportedIn`): the support is
a product of M-convex sets, and each quadratic derivative of the product is a single product of
total degree two — a nonnegative multiple of a quadratic derivative of one factor, or the product
`symmProd` of two nonnegative linear forms. Placing the factors in the disjoint variables
`x_{p,·}` (`isLorentzianPolynomial_rename`, `isLorentzianPolynomial_disjointProd`) and merging by
the nonnegative substitution `x_{p,i} ↦ x_i` gives: every product of Lorentzian polynomials, and
its composition with any nonnegative substitution, is mixed-Lorentzian (`isMixedLorentzian_prod`,
`isMixedLorentzian_prod_subst`). For linear local factors the Hessian of `∏_p ⟨L_p, y⟩` is
Lorentzian at every `y ≥ 0`, with no positivity required of the local factors at `y`
(`isLorentzian_eulerHessian_of_nonneg`).

### Renormalized prime-place data

[TheTowerDeficitIsARowSum](TheTowerDeficitIsARowSum.lean): the tower finite part
`F_p = 2γ_p|b|² + log p(|b|² − K_q(b))` of RAPT has matrix `2γ_p` on the diagonal and
`−log p·q^{|i−j|}` off it, so `−F_p` is Metzler. The Kac–Murdock–Szegő row is at most
`(1 + q)/(1 − q)`, hence every row sum of `−F_p` is at most `2d_p` (`rowSum_neg_towerMatrix_le`),
and `F_p + c|·|² ≥ 0` on every depth iff `c` dominates every row sum
(`towerFinitePart_add_nonneg_iff_rowSum`): the sign law `c ≥ 2d_p` is the row-sum law of the
stability regime with weight `1`. The prime-place links of a renormalized decomposition are
therefore Metzler forms whose only obstruction is a positive row sum `2d_p` at the small primes,
to be cancelled by the row sums of the other places.

### Polar gluing and its exact price

[PolarGluingAndDispersion](PolarGluingAndDispersion.lean): for forms `Q_i` sharing a positive
anchor `e`, with `a_i = Q_i[e]`, `b_i = B_{Q_i}(e,−)`, `A = Σa_i`, `b = Σb_i`,

\[
 R_{\sum_iQ_i}=\sum_iR_{Q_i}-V_e,\qquad
 V_e(x)=\sum_ia_i\Big(\frac{b_i(x)}{a_i}-\frac{b(x)}A\Big)^2 .
\]

The sum is hyperbolic exactly when summed reserves pay the dispersion; with zero reserves,
exactly when normalized polar rows align. The corrected assembly `Glue_e(Q_i) = ΣQ_i − C_e`
preserves the total polar row, adds reserves exactly, is associative, decomposes into within- and
between-group corrections and commutes with pullback. It constructs a hyperbolic form; an
arithmetic application must identify or pay `C_e` in the actual pairing. The calibration
`Q_{±t,r} = [[1, ±t], [±t, t² − r]]`: each plane hyperbolic iff `r ≥ 0`, their sum iff `r ≥ t²`.

[TheTiltedMarginPaysThePolarDispersion](TheTiltedMarginPaysThePolarDispersion.lean): for `ζ` the
dispersion is paid in the stability regime. The atomic intersection form is exactly the tilted
diagonal model plus the residual `‖g‖² diag(μ) − M`, which the row-by-row stability law makes
negative semidefinite (`atomicIntersectionGram_eq_tiltedModel_add`, `qf_residual_nonpos`). The
model is the sum of source-defined atom pieces — the share `J/N` of the pole plane, the pole
couplings of one atom and its tilted margin — each with `Q_m[H + V] = 2/N` (`sum_atomPiece`). At
`w ≤ c★δ_N` the model has one positive square, so the dispersion of the local polar rows at the
anchor `H + V` is at most the sum of the local reserves (`polarDispersion_le_sum_anchorReserve`):
the archimedean self-energy, distributed by the tilt of the prime rows, pays it.

### Reflection splitting and the optimal repair

[TheHalfDefectIsTheOptimalHodgeRepair](TheHalfDefectIsTheOptimalHodgeRepair.lean): splitting
Frobenius evaluation under `r(z) = 1/conj z` gives `G_n + C_n = P_n ⪰ 0` with
`C_n[x] = ½Δ_n[x]`, half the reflection defect. On spectrum-complete windows `rank C_n` equals the
number `κ` of distinct outer eigenvalues and every repair has rank `≥ κ`; `G_n + tC_n ⪰ 0` iff the
datum is unitary or `t ≥ 1`; the same threshold holds in the Hodge completion for every pole row.
The repaired pairing differs from the original one: a proof of the original Hodge index must
eliminate the odd sector through a proved property of the source.

### Lorentzian polynomials and their closure

A polynomial `f = Σ_β c_β x^β` is Lorentzian of degree `d` (`IsLorentzianPoly`,
`IsLorentzianPolynomial`) when its coefficients are nonnegative, its support is M-convex and every
quadratic derivative `∂^α f`, `|α| = d − 2`, has one positive square. The programme proves the
basic theorems of the class by its own local-to-global principle: Euler's identity is the link
condition, so the weighted Metzler Hodge index theorem lifts signature from derivatives to the
whole polynomial.

[TheHessianOfALorentzianPolynomialTricklesDown](TheHessianOfALorentzianPolynomialTricklesDown.lean):
`∂_i f` is Lorentzian (`isLorentzianPoly_coeffDeriv`). The Hessian `∇²f(x) = Σ_{|α|=d−2}
(x^α/α!) Q_α` satisfies `(d − 2)∇²f(x) = Σ_i x_i ∇²(∂_i f)(x)` and
`∇²(∂_i f)(x) x = (d − 2)∇²f(x) e_i`
(`hess_succ_smul`, `sum_hess_coeffDeriv_mul`): the Hessians of the partial derivatives are links
weighted by `x`. Reverse Cauchy–Schwarz in each link gives `(TD_x)`; the M-convex path lemma
(`mconvex_path`) gives connectivity on the active variables; so `∇²f(x)` has one positive square
for `x > 0`, and by continuity for `x ≥ 0` (`isHyperbolic_hess`, `isHyperbolic_hess_of_nonneg`).

[TheMixedHessiansOfALorentzianPolynomialAreHyperbolic](TheMixedHessiansOfALorentzianPolynomialAreHyperbolic.lean):
the same induction runs on polarizations. With `dval c [v_1, …, v_m] γ = ∂_{v_1}⋯∂_{v_m}∂^γ f`, the
mixed Hessian along `v :: vs` is `Σ_i v_i H_i` with links `H_i` the mixed Hessians of `∂_i f` and
`H_i(u, v) = (Hu)_i` (`mixHess_cons`, `bil_mixHess_link`, `weightedTrickleDown_of_links`). Every
mixed quadratic derivative along nonnegative directions has one positive square
(`isHyperbolic_mixHess`). This is the Alexandrov–Fenchel inequality
`D(u, v, vs)² ≥ D(u, u, vs) D(v, v, vs)` for nonnegative `u, vs` (`alexandrov_fenchel`); along two
directions the mixed sequence `k ↦ D(u^k, v^{d−k})` is log-concave (`khovanskii_teissier`).

[TheLorentzianClassIsClosedUnderNonnegativeSubstitution](TheLorentzianClassIsClosedUnderNonnegativeSubstitution.lean):
a polynomial is mixed-Lorentzian (`IsMixedLorentzian`) when it has nonnegative coefficients, is
homogeneous, and every Hessian of `∂_{v_1}⋯∂_{v_{d−2}} p`, `v_t ≥ 0`, is hyperbolic. Lorentzian
polynomials are mixed-Lorentzian (`IsLorentzianPolynomial.isMixedLorentzian`, via
`hess0_dirDerivs`). The mixed class is closed under directional derivatives
(`IsMixedLorentzian.differentiate`) and nonnegative substitutions (`IsMixedLorentzian.subst`):
the chain rule pushes directions forward and pulls Hessians back. Its Hessian at every
nonnegative point has one positive square (`IsMixedLorentzian.isHyperbolic_hessAt`), and reverse
Cauchy–Schwarz against the point gives strong log-concavity
`d p(x) ∂_v²p(x) ≤ (d − 1)(∂_v p(x))²` (`IsMixedLorentzian.logConcave`): every restriction
`t ↦ p(x + tv)` satisfies the Newton inequality of a real-rooted polynomial of degree `d` at
`t = 0`.

[TheClosureProducesExactlyTheLorentzianForms](TheClosureProducesExactlyTheLorentzianForms.lean):
a matrix is Lorentzian iff it is the Hessian at a nonnegative point of a mixed-Lorentzian
polynomial (`isLorentzian_iff_exists_hessAt`); the Hessians of Euler products of Lorentzian local
factors after a nonnegative substitution are Lorentzian (`isLorentzian_hessAt_prod_subst`), and a
form with a negative entry is never such a Hessian (`not_exists_hessAt_of_neg`). Hessians of the
closure carry the Lorentzian signature and nothing else.

[TheSupportOfAMixedLorentzianPolynomialIsMConvex](TheSupportOfAMixedLorentzianPolynomialIsMConvex.lean):
the mixed class needs no support hypothesis. In a Lorentzian form, `Q_{ai} > 0` and `Q_{jk} > 0`
force `Q_{aj} > 0` or `Q_{ak} > 0`, since otherwise `e_a + t e_i` and `e_j + e_k` span a positive
definite plane for small `t` (`IsHyperbolic.exchange`); for a quadratic this is the exchange
property of its support. In higher degree, monomials sharing a variable `x_k` exchange inside
`∂_k p` (`exchange_of_common`). For coprime monomials `x^μ x_a x_i` and `x^ν x_k`, the exchange in
`∂_{e_a+e_k} p` either lands on the target or produces `x^μ x_j x_k`, which shares `x^μ` with the
first monomial (`exchange_disjoint`). By induction on the degree the support of every
mixed-Lorentzian polynomial is M-convex (`IsMixedLorentzian.isMConvex`), so the two classes
coincide (`isMixedLorentzian_iff_isLorentzianPolynomial`). Products, nonnegative substitutions
and derivatives of Lorentzian polynomials are Lorentzian in coefficient form
(`IsLorentzianPolynomial.mul`, `IsLorentzianPolynomial.subst`,
`IsLorentzianPolynomial.differentiate`), and so is the Euler product of Lorentzian local factors
composed with the scale map (`isLorentzianPolynomial_prod_subst`).

### The Turán layer

[LorentzianPolynomialsAndTheTuranLayer](LorentzianPolynomialsAndTheTuranLayer.lean): a bivariate
homogeneous polynomial with nonnegative coefficients is Lorentzian iff its support is an interval
and its binomially normalized coefficients are log-concave. Every homogenized Jensen polynomial
`Σ_k C(d,k) γ_{n+k} x^k y^{d−k}` of `ξ(½ + x) = Σ γ_k x^{2k}` at the centre is Lorentzian. Pólya's
criterion uses `k! γ_k`, whose Newton inequalities are stronger; Lorentzianity does not give
real-rootedness.

[TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine](TheJensenPolynomialsOfXiSatisfyLaguerreOnTheHalfLine.lean):
what Lorentzianity gives is Laguerre's inequality where the roots are not. The strong
log-concavity of the mixed class at `(s, 1)` along `(1, 0)` is `d J J'' ≤ (d − 1) J'²` at `s ≥ 0`
for the dehomogenization `J` of a Lorentzian bivariate form
(`laguerre_halfLine_of_isLorentzianPoly`):
`J^{1/d}` is concave on `[0, ∞)`. Every Jensen polynomial of `ξ` therefore satisfies Laguerre's
inequality on the nonnegative half-line (`xi_jensen_laguerre_halfLine`). A real-rooted polynomial
satisfies it on the whole line, and the Jensen polynomials of `ξ` have no positive roots: RH is the
same family of inequalities on the negative half-line, where the roots would lie. At `d = 2` the
inequality is the Turán inequality, independent of `s`.

## Research directions

**Trickle-down for `ζ`.** Decide whether `ζ`'s Euler-gauge atomic intersection form, completed by
its pole plane, is Metzler with connected support and positive image at bounded overlap, and
whether it satisfies `(TD_π)` — or quantitative trickle-down with a gap — uniformly in `N`. Below
the spacing (`K < 1`) the Metzler, connectivity and positive-image conditions are theorems and the
question is exactly `(TD_π)`; in the stability regime `K ≤ c₀` the atom block is negative
semidefinite, and for `K ≤ c★` its coupling to the pole plane is paid by the tilted margin, so the
central conjecture is a theorem there (`weilQuad_atomicTest_nonneg`). Between `c★` and the spacing
the Metzler structure holds and `(TD_π)` is open; beyond the Robin–Euler threshold the atom block
is provably outside the stability regime, so no row-sum argument reaches the window. At every
width the question is exactly a gap of `M` on the pole complement `Σ x_n/√n = 0` and one scalar
condition on `Σ x_n/√n = 1` (`forall_weilQuad_atomicTest_nonneg_iff`). Inside the stability regime
Weil positivity on window tests reaches `K_RE/4` for plateau profiles
(`eventually_weilQuad_windowTest_nonneg_quarter`), and
paying the pole term in absolute value has a ceiling near `K_RE/2`. Beyond the threshold the
Markov form loses positivity along the pole vector `(n^{−1/2})`, the top of the prime form with
finite part `−γ`
(RenormalizedArithmeticPotentialTheory), which is the `H`-row of the pole plane: the pole term pays
exactly that direction, and only in the Euler gauge. The remaining content is a gap of the Markov
form on the complement of the pole vector, coupled to the pole plane through the `V`-row `(n^{1/2})`
along which the tilted margin grows. For `K > 1` no gauge of the atoms is Metzler, so the question
becomes (TD) with a proved primitive gap, or `(TD_π)` in another basis. A proof through the Metzler
structure is selective by construction: at level `N` no twin flipping a prime `≤ N` admits a
Metzler gauge. The same questions stand for adapted families at a fixed fraction `c < 1` of the
local spacing: they are separated, their atoms meet nonpositively
(`markovPair_adapted_nonpos`), so their atomic Gram is Metzler, and they cover the fraction `c`
of the atomic range.

**The Metzler property beyond atomic resolution.** Decided for gauges of the atomic basis: the
threshold overlap ratio is exactly `K = 1` for every profile positive on `(0, 1)`. Open: a natural
non-atomic basis — differences, wavelets, Hecke orbits — in which the overlapping form is Metzler,
or a direct proof of the primitive gap `Q ≤ (1 − g)D` on the constraint hyperplane at a fixed
overlap ratio `K > 1`, which together with approximate (TD) is all quantitative trickle-down
needs.

**Renormalized links.** Build links of the atomic intersection form from source-defined local
pieces: the horizon finite parts of the prime place (tower forms `−2γ_p + log p(K_q − 1)`, Metzler
with row sums `≤ 2d_p`, the sign law being exactly the row-sum law), the archimedean jump Laplacian
(row sums zero) and the pole plane.
Account for who pays the deficits `2d_p` at the small primes. The first useful result is an exact
link decomposition with a residual controlled by quantitative trickle-down on an explicit
overlap family.

**Arithmetic polar compatibility.** Find a decomposition of the complete intersection form whose
anchors and reserves are source-defined, and determine whether the infinite-place cross energy,
section relations or the successor connection pay the polar dispersion. In the stability regime
the tilted archimedean margin pays it for the atom pieces, and the Dirichlet energy of the pole
relations pays the pole term itself through the multiplicative Hardy inequality up to `K★`; open
beyond the Robin–Euler threshold, where the finite part of the Markov form is negative and the
payment must come from cross terms.

**Coherent multiscale assembly.** Construct decompositions whose anchors and restriction maps
respect the gluing calculus, separate within-block and between-block costs, and seek bounds
uniform under refinement.

**Selectivity calibration.** For each certificate, identify the bounded twist (multiplicative or
not) and the fake curve datum on which it fails, and the term — pole, non-ratio lag, finite part
or successor phase — that distinguishes `ζ`. Calibrated so far: the Metzler sign fails for every
twin flipping a prime of the horizon; the margin certificate of the stability regime fails for no
sign twin, the Liouville twin included; over `𝔽_q` the square-root count fails for the golden datum.

**Conformal dynamics and reflection.** Study maps with `TᵀQT = λQ` and reflection forms on the
affine algebra arising from arithmetic constructions. A boost on an indefinite fibre does not
create a positive invariant metric, and an isometric ladder with decaying couplings carries no
positive square. Construct a conformal correspondence with `λ ≠ 1`, or a trickle-down structure
that supplies the Hasse–Weil inequality without one; the growth `wp^{k/2}` of the prime pairing
along `p`-ladders — the main term of the prime number theorem — is the candidate conformal weight.
In Cayley coordinates the reflection exists and RH is its positivity on the Li ladder, but the
ladder is built from the zeros. Open: a reflection-positive functional built from the source —
the prime and archimedean data — whose Cayley ladder is the Li ladder. The candidate is the
dynamical layer: the KMS states of the Toeplitz algebra of `ℕ ⋊ ℕ^×` under the scaling dynamics,
with their behaviour under the reflection `β ↦ 3 − β`. By Laca–Raeburn these states are unique
for `1 ≤ β ≤ 2`, the window that corresponds to the critical strip of `ζ(β − 1)`, which is their
partition function beyond it.

**Arithmetic elimination of reflection-odd classes.** Seek section, incidence or effectivity
identities that exclude the odd sector for actual arithmetic objects without assuming purity, and
determine what survives in infinite-spectrum limits.

**An inductive arithmetic class.** Construct sections or incidence objects whose links remain in
the class, with local signature proved by counting or another independent operation. Over finite
fields the construction must reject the golden and complex fake data for a named reason.

**Signed overlap and exhaustion.** Retain the overlap Gram, prime lag form, archimedean cross
form and both poles in one estimate, with errors in the overlap norm, and establish a transfer to
an exhaustive family. An atomic test of overlap ratio `K` is supported on measure `≤ K`, so a
single atomic family is exhaustive only when `K` grows at least like `log N`: a transfer must
either let the overlap grow with `N` or assemble tests across levels, where positivity does not
add. The shape is not the obstruction: at `K★_∞` positivity holds for every `C²` test supported in
the windows, so what remains is the measure of the support, not the span of the family.

**Higher-degree lifts and stability.** The mixed and coefficient classes coincide and are closed
under products, nonnegative substitutions and derivatives. Open: a Lorentzian lift of the Weil
pairing through the closure, with the Γ-term, pole plane and diagonal identified; an arithmetic
operation producing the factorially normalized Newton inequalities or real stability.

**Exceptional extinction.** Combine geometric defects with the energy and work theories of AES
and AID: a source estimate below the closed quantum of transverse energy or damped work would
exclude an off-line zero. Average rarity alone cannot.

## Traps and boundaries

| Tempting inference | Required correction |
|---|---|
| Every prime piece is positive, so the global form has Hodge index | Specify the forms, their common pole allocation, and the dispersion or cross-term payment |
| Subtracting a positive correction proves the original signature | It proves the signature of a different form; identify the target or prove the domination |
| Nonnegative coefficients and connectivity imply Hodge index | The golden datum passes both; the trickle-down inequality is the content |
| Stability-regime positivity carries the arithmetic | It holds for every bounded twist; the trickle-down regime is open |
| Sharper constants extend the stability regime to the spacing | They reach a quarter of the Robin–Euler threshold, and paying the pole term in absolute value stops near half of it; at the threshold the atom block acquires a positive square along the pole vector and the mechanism must change |
| A proved Hodge index on an atomic family is arithmetic | At a fixed fraction of the spacing it holds at the Liouville point; only the Metzler sign rejects that twin |
| Beyond the spacing a better gauge restores the Metzler sign | For `K > 1` an odd triangle of atoms frustrates every unimodular gauge; change the basis or prove the gap |
| A positive Euler product gives the arithmetic sign | Its Hessian is Lorentzian for every nonnegative local datum and is not the Weil pairing |
| The local L-factor at a prime is Lorentzian because of RH over `𝔽_p` | RH makes its Frobenius ladder trickle down; the polynomial is Lorentzian only at the Weil bound, never at a prime |
| Li positivity is a weak sign condition | On the Cayley ladder of `ζ` the Metzler sign is equivalent to RH: the trickle-down content sits inside the sign |
| A Hecke dilation can play the role of Frobenius | Dilations are isometries; Weil uses a conformal factor `q`, and an isometric ladder with decaying couplings carries no positive square |
| The scale map is the archimedean place | A substitution is not an identity with the completed Γ-term and finite part |
| A nef shift repairs the arithmetic form | It changes coordinates; a regulator subtraction changes the form |
| A common gauge proves positivity | It selects coordinates or a source; it does not prove a signature |
| Positive local sections exhaust the Weil criterion | Shrinking supports require a separate signed transfer theorem; an atomic test of overlap ratio `K` lives on measure `≤ K` |
| Fixed-scale averages control every signed vector | Quantifiers and norms differ; prove the passage |
| Lorentzian log-concavity implies Jensen real-rootedness | Real stability is stronger |
| A symmetry obstruction excludes every geometry | It applies to the specified localization and invariance mechanism |

## Relation to the surrounding research

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Scaling surface, pole plane, Hodge target, curve calibrations, independent arithmetic sections |
| SpacingScaleHarmonicAnalysis | Separated-regime stability, universality, diamagnetism, non-ratio lags, overlap kernels, the fixed-width RH criterion |
| RenormalizedArithmeticPotentialTheory; RenormalizedBiarithmeticGeometry | Counterterm rank, horizon tensor counterterms, finite parts, surviving domains |
| ArithmeticIntersectionTheory | Prime ladders, tower forms, transfers, renormalization cocycles |
| ArithmeticElectrostatics; ArithmeticIndexDescent | Currents, transverse energy, quantization, source work, index bounds |
| BiarithmeticGaugeGeometry; ArithmeticCorrelationGeometry | Prime gauge torus, successor connection, source selection |
| ArithmeticPolarization; ConjugateDiagonalGeometry | Reflected pairing, even–odd splitting, reflection defect |
| ArithmeticEffectivityTheory; ArithmeticOrientationGeometry | Counting, Riemann–Roch growth, Weil planes, Rosati signs |
| IncommensurableGaborPinching | Structural Gram slack discarded by scalar estimates |
| HTGeometry | Inertia, Schur complements and projection identities |
| RHTower (Li criterion) | Cayley images of the zeros, paired Li coefficients, Li's criterion with exponential slack |

## Success criteria

A contribution is an unconditional theorem about explicitly defined objects. General algebraic
criteria expose their structural conditions and prove them when applied to arithmetic; no
analytic estimate is hidden in a premise, instance or structure.

A contribution toward RH identifies the producer or transfer step it improves, explains its
behaviour on the relevant sign twin or fake datum, and, if it retires a mechanism, retains the
strongest positive boundary or replacement construction. Positivity of a modified form remains
distinct from positivity of the target.

Full success is a source-defined signature construction for the actual Weil intersection form on
an exhaustive signed family. Intermediate successes: the Metzler property or `(TD_π)` for `ζ` on
an explicit overlap family beyond the stability regime; a renormalized link decomposition with
controlled residual; a proved dispersion payment; an independently constructed link signature;
a quantitative overlap transfer; an exceptional-extinction theorem. Each states exactly which
domain it controls and which arithmetic step remains open.
