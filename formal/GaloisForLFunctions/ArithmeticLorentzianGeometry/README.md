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
atoms. Up to a fixed ratio `c₀` the archimedean self-energy pays the prime form and the pole, for
every bounded twist of the coefficients alike; at unbounded overlap (fixed width) positivity of
the atomic Weil Grams is RH (SpacingScaleHarmonicAnalysis). In the language of this programme
the separated regime is the **stability regime** of a Metzler form and bounded overlap is the
**trickle-down regime**. The programme's central conjecture is the trickle-down inequality for
`ζ`'s Euler-gauge intersection form at every fixed overlap ratio, uniformly in `N`; uniformity
in `K` is RH.

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

### Conformal symmetry

[FrobeniusIsConformalHeckeIsABoost](FrobeniusIsConformalHeckeIsABoost.lean): over `𝔽_q`, `(F×1)^*`
sends `H ↦ qH`, `V ↦ V`, `Γ_k ↦ Γ_{k+1}` and satisfies `TᵀG_{K+1}T = qG_K`. Over `ℤ`, dilations
`n ↦ pn` preserve the coupled kernel of every twin and act on the pole plane by the boost
`diag(p^{−1/2}, p^{1/2})`: conformal factor one. Power maps `n ↦ n^k`, `k ≥ 2`, and the successor
are not conformal. These statements concern the specified kernels and maps.

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

### Local factors and the Euler-product closure

[LocalFactorsAndTheEulerProductClosure](LocalFactorsAndTheEulerProductClosure.lean): the prime
kernel on a ladder `1, p, …, p⁵` is Metzler with two positive squares for every prime — no local
Lorentzian sign exists factor by factor. A nonnegative kernel minus its row sums is negative
semidefinite: a jump form, such as the archimedean place, contributes no positive square. The
Hessian of `∏_p ⟨L_p, y⟩` at a positive point is a positive multiple of the second elementary
symmetric form of the normalized local data, hence Lorentzian for every nonnegative local datum.
The product closure cannot distinguish the Euler point from other nonnegative Euler products,
and it contains neither the Γ-term, the pole plane nor the diagonal.

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

### Reflection splitting and the optimal repair

[TheHalfDefectIsTheOptimalHodgeRepair](TheHalfDefectIsTheOptimalHodgeRepair.lean): splitting
Frobenius evaluation under `r(z) = 1/conj z` gives `G_n + C_n = P_n ⪰ 0` with
`C_n[x] = ½Δ_n[x]`, half the reflection defect. On spectrum-complete windows `rank C_n` equals the
number `κ` of distinct outer eigenvalues and every repair has rank `≥ κ`; `G_n + tC_n ⪰ 0` iff the
datum is unitary or `t ≥ 1`; the same threshold holds in the Hodge completion for every pole row.
The repaired pairing differs from the original one: a proof of the original Hodge index must
eliminate the odd sector through a proved property of the source.

### The Turán layer

[LorentzianPolynomialsAndTheTuranLayer](LorentzianPolynomialsAndTheTuranLayer.lean): a bivariate
homogeneous polynomial with nonnegative coefficients is Lorentzian iff its support is an interval
and its binomially normalized coefficients are log-concave. Every homogenized Jensen polynomial
`Σ_k C(d,k) γ_{n+k} x^k y^{d−k}` of `ξ(½ + x) = Σ γ_k x^{2k}` at the centre is Lorentzian. Pólya's
criterion uses `k! γ_k`, whose Newton inequalities are stronger; Lorentzianity does not give
real-rootedness.

## Research directions

**Trickle-down for `ζ`.** Decide whether `ζ`'s Euler-gauge atomic intersection form, completed by
its pole plane, is Metzler with connected support and positive image at bounded overlap, and
whether it satisfies `(TD_π)` — or quantitative trickle-down with a gap — uniformly in `N`. The
stability regime `K ≤ c₀` is the base case. A proof would be selective by construction: at level
`N` no twin flipping a prime `≤ N` admits a Metzler gauge.

**The Metzler property beyond atomic resolution.** At overlap the entries of the intersection
form include the overlap Gram, the archimedean cross terms of overlapping atoms and the non-ratio
prime lags. Determine their signs in the Euler gauge, a gauge in which they are nonnegative, or
the obstruction to one.

**Renormalized links.** Build links of the atomic intersection form from source-defined local
pieces: the horizon finite parts of the prime place (tower forms `−2γ_p + log p(K_q − 1)` with the
sign law `c ≥ 2d_p`, `d_p = √p log p/(p−1) − γ`), the archimedean jump Laplacian and the pole plane.
Account for who pays the deficits `2d_p` at the small primes. The first useful result is an exact
link decomposition with a residual controlled by quantitative trickle-down on an explicit
overlap family.

**Arithmetic polar compatibility.** Find a decomposition of the complete intersection form whose
anchors and reserves are source-defined, and determine whether the infinite-place cross energy,
section relations or the successor connection pay the polar dispersion.

**Coherent multiscale assembly.** Construct decompositions whose anchors and restriction maps
respect the gluing calculus, separate within-block and between-block costs, and seek bounds
uniform under refinement.

**Selectivity calibration.** For each certificate, identify the bounded twist (multiplicative or
not) and the fake curve datum on which it fails, and the term — pole, non-ratio lag, finite part
or successor phase — that distinguishes `ζ`.

**Conformal dynamics and reflection.** Study maps with `TᵀQT = λQ` and reflection forms on the
affine algebra arising from arithmetic constructions. A boost on an indefinite fibre does not
create a positive invariant metric. Construct a conformal correspondence with `λ ≠ 1`, or a
trickle-down structure that supplies the Hasse–Weil inequality without one.

**Arithmetic elimination of reflection-odd classes.** Seek section, incidence or effectivity
identities that exclude the odd sector for actual arithmetic objects without assuming purity, and
determine what survives in infinite-spectrum limits.

**An inductive arithmetic class.** Construct sections or incidence objects whose links remain in
the class, with local signature proved by counting or another independent operation. Over finite
fields the construction must reject the golden and complex fake data for a named reason.

**Signed overlap and exhaustion.** Retain the overlap Gram, prime lag form, archimedean cross
form and both poles in one estimate, with errors in the overlap norm, and establish a transfer to
an exhaustive family.

**Higher-degree lifts and stability.** Extend the coefficient theory with products, nonnegative
substitutions and derivatives where a candidate lift requires them; find an arithmetic operation
producing the factorially normalized Newton inequalities or real stability.

**Exceptional extinction.** Combine geometric defects with the energy and work theories of AES
and AID: a source estimate below the closed quantum of transverse energy or damped work would
exclude an off-line zero. Average rarity alone cannot.

## Traps and boundaries

| Tempting inference | Required correction |
|---|---|
| Every prime piece is positive, so the global form has Hodge index | Specify the forms, their common pole allocation, and the dispersion or cross-term payment |
| Subtracting a positive correction proves the original signature | It proves the signature of a different form; identify the target or prove the domination |
| Nonnegative coefficients and connectivity imply Hodge index | The golden datum passes both; the trickle-down inequality is the content |
| Stability-regime positivity is a Hodge index | It holds for every bounded twist; the trickle-down regime is open |
| A positive Euler product gives the arithmetic sign | Its Hessian is Lorentzian for every nonnegative local datum and is not the Weil pairing |
| A Hecke dilation can play the role of Frobenius | Dilations are isometries; Weil uses a conformal factor `q` |
| The scale map is the archimedean place | A substitution is not an identity with the completed Γ-term and finite part |
| A nef shift repairs the arithmetic form | It changes coordinates; a regulator subtraction changes the form |
| A common gauge proves positivity | It selects coordinates or a source; it does not prove a signature |
| Positive local sections exhaust the Weil criterion | Shrinking supports require a separate signed transfer theorem |
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
