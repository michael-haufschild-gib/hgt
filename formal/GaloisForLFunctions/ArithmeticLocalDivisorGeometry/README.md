# Arithmetic Local Divisor Geometry

Arithmetic Local Divisor Geometry studies the finite divisor blocks of the completed zeta function and the arithmetic laws that could constrain their coefficients. Its central question is precise: **what independently proved property of the theta/Euler source forces the local divisor into the coefficient cone?** Equivalent alternatives ask for an arithmetic bound on collision charge, cancellation of the Ward cap, or zeroth-order contact at the Ward heat threshold.

The programme preserves local multiplicities, central zeros, moving boundaries and signed interactions. It does not define admissible arithmetic objects by imposing the desired sign. Its local algebra applies to impure configurations too; excluding those configurations for the actual source is the open arithmetic problem.

The central source inequality remains unproved. Exact factorization, reconstruction, polynomial positivity criteria and a local model classification do not establish it.

## Motivation and position

Route WD already has strong receivers. At each real height the horizontal Xi slice factors exactly into a finite head and a complementary tail. A radius-one head suffices, and the exact tail has nonnegative Taylor coefficients. Thus distant-tail approximation is unnecessary for the coefficient question. What remains is the sign of a finite polynomial whose degree and multiplicities vary with height.

That localization changes the mathematical object, but does not make it small uniformly. A norm square can have negative coefficients; a coefficient-positive product can contain a coefficient-negative factor; a real zero at the center creates vanishing coefficients that must be retained. These phenomena make local divisor geometry more specific than a theory of positive functions or Hermitian forms.

| Related programme | Interface |
|---|---|
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Studies source effectivity and the Hodge sign on the scaling surface. Here the unresolved sign is read through local factors and their coefficients. No equivalence of the possible producer constructions is assumed. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Distinguishes source identification from orientation and studies repairing ideals. Local divisor geometry retains multiplicity and local factors beyond spectral support. |
| [Arithmetic Orientation Geometry](../ArithmeticOrientationGeometry/README.md) | Studies scaling correspondences and orbit correlations. Ordered divisor channels provide a different representation of orientation; scalar reflection sums can erase them. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Teaches that normalization and relative estimates must retain the signed quantity on its moving support. Here the moving parameters are height, degree, radius and heat. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Prices visibility and separates fixed-depth, eventual-height and global-width conclusions. Those quantifiers also govern heated local factors. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Supplies the discipline of a single signed budget, including mixed terms and overlap. A Gram-minor certificate here must obey the same accounting. |
| `RHTower` | Supplies actual Xi, Ward caps, exact finite-head and heat transfers, collision laws and threshold criteria. These are existing inputs. |
| `HTGeometry` | Supplies polynomial heat products, contour root multisets, Newton inversion and holomorphic local factors, including multiple roots. |

## Objects and language

Write a spectral zero copy as `z = γ + iδ`, where `δ = 1/2 − Re ρ`. At a real center `t`, put `u = γ − t` and `y = x²`.

| Object | Data retained |
|---|---|
| Source germ | The theta definition or completed Euler–Gamma description, its analytic domain and transition identity |
| Finite local divisor | Every zero copy, its multiplicity, the center and the enclosing boundary |
| Local factor | A monic polynomial in `y`; central copies contribute exact factors `y` |
| Coefficient cone | All coefficients nonnegative, including coefficients that vanish |
| Heated cone | Nonnegative coefficients after forward horizontal polynomial heat; heat normalization is part of the datum |
| Contour moment | A logarithmic-derivative integral with a specified boundary avoiding zeros |
| Transition | The exact factor entering or leaving a boundary, with its degree and multiplicity |
| Source certificate | An independently defined source expression, an established sign, and a proved identity or bound landing on the required coefficient or charge |
| Collision observable | A specified charge: horizontal collision, global heat collision, or weighted Ward cap |

Three uses of “positive” must stay separate. Real-axis positivity means `P(x²)≥0`. Coefficient positivity means every coefficient of `P(y)` is nonnegative. Positive semidefiniteness concerns a particular matrix or quadratic form and requires a proved connection to `P`.

“Repair” below means multiplication moves a polynomial into the coefficient cone. It does not mean that an arithmetic obstruction has been removed. A chosen model multiplier is not an actual divisor factor until a source theorem identifies it.

## Exact local mechanisms

### Conjugate pairs and real factors

A conjugate pair contributes

\[
Q_{u,\delta}(y)=y^2+2(u^2-\delta^2)y+(u^2+\delta^2)^2.
\]

The identity

\[
Q_{u,\delta}(x^2)=(x^2+u^2-\delta^2)^2+4u^2\delta^2
\]

proves real-axis nonnegativity without any coefficient sign. Its coefficient cone is exactly `δ²≤u²`. At `u=0`, the factor is `(y−δ²)²`, with a positive root and a negative middle coefficient whenever `δ≠0`.

Adjoining a real divisor factor `y+c`, `c≥0`, gives two genuinely signed conditions:

\[
2(\delta^2-u^2)\le c,\qquad
2c(\delta^2-u^2)\le(u^2+\delta^2)^2.
\]

A choice of `c` exists exactly when `δ²≤3u²`. The choice `c=u²+δ²` works throughout that region. At its boundary the product is `y³+64u⁶`. Thus even one exact factor transition can conceal a coefficient defect in a smaller block. Dividing a positive polynomial by a positive factor is not a valid sign argument.

These laws are developed in [LocalFactors.lean](LocalFactors.lean). They classify a local transition rather than retiring the coefficient route.

### A sharp multiplicity cost

Normalize a nonzero pair by `r=u²+δ²` and `α=(δ²−u²)/r`. Adjoining `n` identical real factors `y+r` reduces to

\[
B_{\alpha,n}(z)=(1+z)^n(z^2-2\alpha z+1)
 =(1+z)^{n+2}-2(\alpha+1)z(1+z)^n.
\]

For every interior index `j+1`, its coefficient is

\[
\binom{n+2}{j+1}-2(\alpha+1)\binom nj.
\]

For `0≤j≤n`, the coefficient is nonnegative exactly when

\[
2(\alpha+1)(j+1)(n+1-j)\le(n+2)(n+1).
\]

The maximum of the quadratic index weight occurs at the middle integer or integers. Consequently the exact coefficient criteria are

\[
\begin{array}{c|c|c}
 n & \text{normalized criterion} & \text{geometric criterion}\\
 2m & \alpha(m+1)\le m & \delta^2\le(2m+1)u^2\\
 2m+1 & \alpha(m+2)\le m+1 & \delta^2\le(2m+3)u^2.
\end{array}
\]

The normalized identities and sharp cone criteria are developed in [BinomialMultipliers.lean](BinomialMultipliers.lean). They retain every order; fixed-order positivity would miss the middle obstruction. The multiplicity needed to mask a pair grows on the scale `δ²/u²` as the center approaches its ordinate. Equal-factor multipliers are a classified family, not an optimization over every possible multiplier.

Positive polynomial multipliers are classical. [Motzkin–Straus, Theorem 2.6](https://msp.org/pjm/1969/29-3/pjm-v29-n3-p13-p.pdf) gives the sufficient bound `α≤n/(n+2)` for this same family. It is sharp for even `n`; the exact odd threshold is `(n+1)/(n+3)`. Their Theorem 2.1 also gives the optimal degree for arbitrary quadratic multiples. The contribution here is the exact parity-sensitive formalization, its local divisor interpretation, and the singular limit at the adverse ordinate. Broader multiplier positivity is treated by [Powers–Reznick](https://www.math.emory.edu/~vicki/pub/polya2.pdf); no worldwide novelty claim is attached to the general principle.

### Central multiplicities and the adverse ordinate

Multiplication by `y^a` shifts coefficient indices and preserves their signs in both directions. Central zeros therefore require no strict margin and no division by the central value.

At an off-real pair's own ordinate, every nonzero polynomial multiple of `(y−δ²)²` retains a positive root. A nonzero polynomial with nonnegative coefficients is strictly positive at every positive argument. Thus adjoining other factors cannot repair that exact centered obstruction. Nearby-center repair and own-ordinate exclusion are compatible; their difference is precisely the centering cost.

The corpus already gives sharper detection-order information for an own-ordinate pair against arbitrary positive real factors in `HTGeometry/OffLinePairDetectionNewtonSharp.lean`. The equal-factor law above concerns off-center repair and does not replace that theorem.

### Which transitions can be reversed?

There is an exact universal classification. Multiplication by a real polynomial `Q` preserves and reflects coefficient nonnegativity for every polynomial precisely when

`Q=c y^a`, with `c>0` and `a` a nonnegative integer.

Every other nonzero coefficient-positive `Q` conceals a negative coefficient in some polynomial `P` that is strictly positive for every `y≥0`. A constructive witness has degree at most `2deg Q`: take the flat polynomial through degree `2deg Q` and lower its middle coefficient by a quantity determined by the sum and largest coefficient of `Q`. In the central convolution band, every coefficient of the flat product equals that sum, leaving enough reserve to hide the defect.

The degree bound is sharp. For `Q=1+y^D`, a defect cannot be hidden below degree `2D`, while

\[
(1+y^D)(y^{2D}-y^D+1)=1+y^{3D}
\]

attains the bound. The concealed factor is positive on the entire real axis. Thus real-axis positivity does not rescue universal cancellation. Central multiplicities and positive normalizations are exactly the reversible transitions; removing a nonmonomial shell requires additional signed information. The classification and explicit witnesses are developed in [UniversalReflectors.lean](UniversalReflectors.lean).

### Central multiplicity under heat

Reversibility of central factors is specific to the unheated cone. For the model

\[
P_m(X)=X^{2m}(X^2-a)^2,\qquad a>0,
\]

write the forward heat as `exp(sD²)`, and put `t=s/a`, `B=(2m+2)(2m+1)`, `C=(2m+4)(2m+3)`. Every even coefficient has the sign of one of the finite index weights

\[
F_t(k)=k(k+1)-2B(k+1)t+BCt^2,\qquad 0\le k\le m+1,
\]

apart from the positive leading coefficient. Index `k` corresponds to degree `2(m+1−k)`. Completing the square gives

\[
F_t(k)=(k-Bt+\tfrac12)^2+B(8m+10)t^2-Bt-\tfrac14.
\]

For `0<t<1/(8m+10)`, the explicit index `k=⌊Bt⌋` detects a negative coefficient. For `t≥1/(8m+5)`, every index weight is positive. Consequently the full heat-cone threshold satisfies

\[
\frac{a}{8m+10}\le\sigma_m\le\frac{a}{8m+5},
\qquad \sigma_m\sim\frac{a}{8m}.
\]

The threshold decreases strictly with multiplicity: adjacent rational brackets are disjoint.

The highest adverse coefficient alone detects only heat below `2a/C`, of order `a/m²`. Optimizing over the actual growing set of orders recovers a factor proportional to multiplicity; near threshold the detecting order lies near the middle. This is a polynomial model law. The existing masked-pair Hermite receiver still requires its signed Xi cofactor-deviation estimate. Its Gaussian parameter is `λ=2s`, so the constants must be doubled when crossing that interface.

The controlling order can be identified exactly. Put `h=⌊m/2⌋`. Throughout the whole threshold bracket,

\[
h<Bt<h+1,
\]

so `F_t(h)` is the unique smallest integer-index weight. Consequently

\[
\frac{\sigma_m}{a}
=\frac{B(h+1)+\sqrt{B(h+1)\bigl(B-(C-B)h\bigr)}}{BC}.
\]

At this first contact, exactly one even coefficient through the polynomial's degree vanishes: its degree is `m+2+(m mod 2)`. Every other even coefficient is strictly positive, including the constant coefficient. Odd coefficients vanish identically by symmetry. Thus higher-order first contact persists in a growing, explicitly classified family of norm-square models. An arithmetic theorem forcing zeroth-order contact must use information beyond these polynomial properties. The [middle-order contact proof](../../../docs/drafts/pipeline/2-fully-proven/masked-pair-middle-order-contact.md) gives the parity argument and the exact Gaussian normalization.

## From source to local factor

For a finite copy set closed under spectral conjugation, use the unnormalized real polynomial

\[
D_{t,S}(y)=\prod_{q\in S_{\mathrm{crit}}}\bigl(y+(\gamma_q-t)^2\bigr)
\prod_{q\in S_{\mathrm{up}}}Q_{\gamma_q-t,\delta_q}(y).
\]

At a radius head `S=S(t,R)`, `R≥0`, the exact canonical head is `H_{t,R}(z)=c_{t,R}D_{t,S}(z²)` with `c_{t,R}>0`. Its even Taylor coefficient is therefore `c_{t,R}[y^k]D_{t,S}`, and every odd coefficient vanishes. This description divides by neither `Ξ(t)` nor a vanishing constant coefficient. A split of the copy set gives an exact polynomial product and hence a full coefficient convolution; central factors and signed mixed terms survive the transition.

On an admissible contour the logarithmic derivative gives multiplicity-exact power sums:

\[
p_j(t)=\frac1{2\pi i}\int_\Gamma(z-t)^{2j}\frac{\Xi'(z)}{\Xi(z)}\,dz.
\]

Newton's identities recover the factor coefficients from these moments. The corpus already proves the relevant finite-contour identities, Newton inversion and holomorphic dependence of root symmetric functions. Multiple roots inside the contour are allowed; a boundary crossing changes the enclosed factor and must be handled by an exact transition.

The missing certificate is a sign theorem for the **signed Newton combinations**. Positivity of separate moments, uniqueness of reconstruction, or an integral representation alone does not supply it. A useful source construction could identify these combinations with Gram minors, a nonnegative count, or a telescoping expression whose full boundary remainder has the correct sign. Each proposed identity must be proved for the actual completed source, with no spectral sign in its premises.

## Heat and charge interfaces

Forward horizontal heat on the original slice and the de Bruijn–Newman evolution are different constructions. Their bridge involves Gaussian height averages; it is not pointwise equality of unaveraged slice moments. Polynomial heat already has an exact product formula and a coefficient-positivity closure theorem in `HTGeometry/PolynomialHeatProduct.lean`.

The existing heated-head transfer consumes the correct radius/heat inequality and the full retained polynomial. The available unconditional producer reaches heat `(17/25)/log|t|` at all sufficiently large heights. The detector for depth `δ` operates at the much smaller constant

\[
\kappa_0(\delta)=\frac{\delta^2}{200(\log(3/\delta)+1)}.
\]

Positivity propagates to larger heat. An eventual estimate at detector scale still needs finite-height accounting; allowing every positive rate eventually does not eliminate finite off-line exceptions.

The corpus also contains a stronger receiver for the retained polynomial itself. In [XiWardGlobalCapAndFiniteHeadArithmetic.lean](../RHTower/XiWardGlobalCapAndFiniteHeadArithmetic.lean), positivity at some `0≤λ(t)≤δ₀²/(320 log(180|t|))` for every `|t|≥73/5`, with a fixed head radius `1/2≤R≤1`, implies the global width bound `zetaZeroWidth≤δ₀`. This removes the logarithmic depth loss from that finite-head receiver. Its input still requires an independent producer: coefficient-positive tails cannot generally be canceled. The same module supplies polynomial heat inversion, a general degree-dependent root detector and a Prime–Cesàro identity for the first normalized head coefficient; these are existing tools.

| Endpoint | Required arithmetic output |
|---|---|
| Exact local coefficient cone | Radius-one heads have nonnegative coefficients at every real height, at every order up to their actual degree |
| Horizontal collision | The exact positive-height gross charge is below two on cofinal cutoffs |
| Global heat collision | Total future collision mass is below four on positive heats approaching zero |
| Ward cap | Almost-everywhere nonpositivity of the real completed cap at a suitable fixed positive parameter |
| Threshold contact | The actual source forces a zeroth-order contact at the Ward threshold |

The horizontal charge counts distinct same-height pairs with multiplicity. The heat charge counts disappearing nonreal multiplicity; evenness and nonvanishing at the origin pair its real collision points, producing the four-unit normalization. The Ward cap is a weighted real charge with no universal integer gap. Bounds for one currency cannot be substituted for another.

## Research questions and tools still required

1. **Signed source coefficients.** Construct and prove a source-only sign certificate for the Newton combinations. Contour reconstruction is an input, not the answer.
2. **Multiple-root transitions.** Carry certificates across changing contours by exact factor laws, including central powers. A generic-boundary proof must not assume simple zeros.
3. **Arithmetic selection.** Identify a law of the actual source that excludes impure configurations accepted by symmetry and norm-square positivity. The repair models show why a cone condition on isolated factors is stronger than one on the total block.
4. **Ordered curvature.** Preserve the prime/Gamma channel labels through a singularity-sensitive source-to-divisor map. Reflection scalarization can cancel the detector before it is estimated.
5. **Horizontal collision budgets.** Derive a source expression dominating gross charge and prove a cofinal bound below two, including all mixed and boundary terms.
6. **Detector-scale production.** Improve the low-order source integral or prove a finite-head certificate at `κ₀(δ)/log t`, with all required orders and the finite remainder controlled.
7. **Degree and clustering.** Replace model multiplicity prices by estimates on actual local divisors. The exact equal-factor cost supplies a calibration any proposed uniform argument must survive.
8. **Heat collision budgets.** Derive the heat-transformed source current and bound its cumulative collision mass uniformly towards heat zero. Positive-heat finiteness and the known jump law leave this unpaid.
9. **Contact rigidity.** Explain why actual arithmetic rules out a positive Ward threshold whose contacts all occur at higher orders. Generic polynomial positivity does not provide this rigidity.

## Traps

- Real-axis positivity does not imply coefficient positivity.
- Positive factors cannot be canceled from a coefficient-cone statement.
- A multiple zero is not a simple zero with negligible error.
- A changing local degree cannot be replaced by a fixed-order asymptotic.
- A zero-free boundary exists qualitatively without giving a quantitative separation bound.
- An ordered orientation sum may vanish by symmetry while the even collision defect remains positive.
- A nonnegative count equal to defect plus another nonnegative term gives no upper bound on the defect.
- A later zero heat charge does not force an earlier charge to vanish.
- Separate local certificates may spend the same Gamma/polar reserve more than once.
- Reflection-oddness is necessary for an odd orientation channel, not for every exclusion argument.
- A generic sign-preserving representation is not an arithmetic producer until its source identification is proved.

## Success and contribution criteria

A foundational contribution must prove an exact mechanism, a sharp classification, a quantitative stability law or a faithful source identity that was not already available. It must retain multiplicity and state every dependence on height, radius, degree, separation and heat. If a proposed mechanism fails, its strongest positive survivor must be extracted and proved.

An arithmetic contribution must additionally identify the actual source input, prove its selective force, account for all mixed and boundary terms, and name the established receiver consuming its output. An RH-equivalent condition is a receiver description until that input is independently established.

Full success requires answering the research questions with those tools and closing an arithmetic endpoint at its stated quantifiers. The local laws alone do not complete the programme. Proof and verification records belong in the [programme card](../../../docs/drafts/pipeline/1-in-progress/arithmetic-local-divisor-geometry.md), not in this foundational document.
