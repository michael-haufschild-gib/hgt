# Arithmetic Local Divisor Geometry (ALDG)

Namespace `GaloisForLFunctions.ArithmeticLocalDivisorGeometry`; umbrella `ArithmeticLocalDivisorGeometry.lean`.

**Question.** What independently proved property of the theta/Euler source forces the local
divisor of the completed zeta function into the coefficient cone? Equivalent endpoints ask for an
arithmetic bound on collision charge, cancellation of the Ward cap, or zeroth-order contact at the
Ward heat threshold.

ALDG studies the finite divisor blocks of `Ξ` at a real height and the polynomial laws governing their
coefficients — keeping local multiplicities, central zeros, moving boundaries and signed interactions.
It never defines admissible objects by imposing the sign. Its local algebra applies to impure
configurations too; excluding them for the actual source is the open arithmetic problem. The central
source inequality is unproved; factorization, reconstruction, polynomial positivity criteria and
model classification do not establish it.

---

## 1. Place in the research

Route WD already has strong receivers: at each real height the horizontal Xi slice factors exactly
into a finite head and a complementary tail; a radius-one head suffices and the exact tail has
nonnegative Taylor coefficients. What remains is the sign of a finite polynomial whose degree and
multiplicities vary with height. ALDG is the theory of that polynomial.

| Programme | Interface |
|---|---|
| ArithmeticCastelnuovoSeveri | Source effectivity and Hodge sign; here the sign is read through local factors |
| ArithmeticOrientationTheory | Repairing ideals; ALDG keeps multiplicity and local factors beyond spectral support |
| ArithmeticOrientationGeometry | Orbit correlations; heat-collision index `2(D+E)` is the dynamical count matching ALDG's collision budgets |
| ArithmeticCompensationTheory | Normalizations must retain the signed quantity on moving supports (height, degree, radius, heat) |
| SquareRootThreshold | Fixed-depth vs eventual-height vs global-width quantifiers also govern heated local factors |
| SignedArithmeticEnergyIncidence | Single signed budget discipline for Gram-minor certificates |
| `RHTower` | Actual Xi, Ward caps, finite-head/heat transfers, collision laws, threshold criteria (`XiWardGlobalCapAndFiniteHeadArithmetic.lean`) |
| `HTGeometry` | Polynomial heat products, contour root multisets, Newton inversion, holomorphic local factors (`PolynomialHeatProduct.lean`, `OffLinePairDetectionNewtonSharp.lean`) |

---

## 2. Why

Localization changes the object but does not make it uniformly small. A norm square can have negative
coefficients; a coefficient-positive product can contain a coefficient-negative factor; a central real
zero creates vanishing coefficients that must be kept. So local divisor geometry is more specific than
a theory of positive functions or Hermitian forms. Three positivities stay separate: real-axis
(`P(x²) ≥ 0`), coefficient (all coefficients of `P(y)` ≥ 0), PSD of a matrix (needs a proved link to `P`).

---

## 3. Objects and language

Spectral zero copy `z = γ + iδ`, `δ = ½ − Re ρ`; center `t`, `u = γ − t`, `y = x²`.

| Object | Data | Lean |
|---|---|---|
| Pair factor | `Q_{u,δ}(y) = y² + 2(u²−δ²)y + (u²+δ²)² = (y+u²−δ²)² + 4u²δ²` at `y = x²` | `pairFactor` |
| Local divisor polynomial | `D_{t,S}(y) = Π_crit (y + (γ−t)²) Π_pairs Q`; central copies give `y` | `localDivisorPolynomial`, `horizontalDivisorPolynomial` |
| Radius head | copies with `|z − t| ≤ R`; degree `N(t,R)` | `RHTower.xiSliceGaussianRadiusHead`, `sliceTrunc` |
| Coefficient cone | all coefficients ≥ 0 (incl. vanishing ones) | `CoeffNonneg` |
| Polynomial heat | `exp(sD²)`; forward semigroup | `forwardPolyHeat` |
| Heated cone | coefficient-nonneg after heat; normalization part of the datum | — |
| Hermite edge | `h_d` = largest root of `He_{2d−1}` | `hermiteEdge` |
| Hermite extremizer | `λ^d[He_{2d}(X/√λ) − He_{2d}(h_d)]` | `hermiteExtremizer`, `scaledHermiteExtremizer` |
| Masked pair | `X^{2m}(X² − a)²` | `centralMaskedPair`, `maskedPairHeatThreshold` |
| Disc factors | real linear/quadratic factors with roots in `|ρ| ≤ r` | `DiscFactor` |
| Contour moment | `p_j(t) = (2πi)⁻¹∮(z−t)^{2j}Ξ'/Ξ` | (HTGeometry) |
| Collision observables | horizontal collision; global heat collision; weighted Ward cap | (RHTower) |

**Words.** *Repair*: multiplication moving a polynomial into the cone (not removal of an arithmetic
obstruction; a model multiplier is not a divisor factor until a source theorem identifies it).
*Transition*: exact factor entering/leaving a boundary. *Source certificate*: an independently defined
source expression with established sign and a proved identity landing on the needed coefficient or charge.

---

## 4. Mechanisms

### Exact local algebra
1. **One pair, one real factor.** Pair cone exactly `δ² ≤ u²` (`coeffNonneg_pairFactor_iff`); adjoining
   `y + c` enlarges it to `δ² ≤ 3u²` (`exists_linear_repair_iff`), `c = u² + δ²` works, boundary product
   `y³ + 64u⁶` (`pairFactor_boundary_repair`). One transition can hide a defect of a smaller block.
2. **Multiplicity cost.** `n` equal factors: `B_{α,n}(z) = (1+z)^n(z² − 2αz + 1)`; exact criteria
   `δ² ≤ (2m+1)u²` (`n = 2m`), `δ² ≤ (2m+3)u²` (`n = 2m+1`) (`coeffNonneg_binomialRepair_iff`,
   `coeffNonneg_geometricRepair_even_iff`, `coeffNonneg_geometricRepair_odd_iff`). The middle coefficient is
   the obstruction; fixed-order positivity misses it. (Motzkin–Straus bound; exact parity formalized here.)
3. **Central multiplicities and the adverse ordinate.** `y^a` shifts indices, reflects signs both ways
   (`coeffNonneg_X_pow_mul_iff`); at a pair's own ordinate every multiple of `(y − δ²)²` keeps a positive root,
   so no factor repairs it (`coeffNonneg_pairFactor_at_center_mul_iff`).
4. **Universal reflectors.** Multiplication preserves and reflects the cone for every polynomial iff the
   multiplier is `c·y^a` (`universal_coefficient_reflector_iff`); every other positive multiplier hides a
   defect in a strictly positive polynomial of degree ≤ `2 deg Q`, sharp via `(1+y^D)(y^{2D}−y^D+1) = 1+y^{3D}`.

### Heat
5. **Heat cone evolution.** Forward heat is a semigroup preserving the cone; admissible times form a closed
   upper set (`coeffNonneg_forwardPolyHeat_mono`, `isClosed_forwardPolyHeat_cone`); dilation rescales heat by the
   squared scale (`coeffNonneg_heat_dilation_iff`); backward heat at ½ sends monomials to Hermite polynomials
   (`forwardPolyHeat_half_hermite`); every even nonnegative polynomial with a positive root has an attained
   positive first heat time (`exists_first_heat_time_of_even_nonnegative_root`).
6. **Masked pair threshold.** For `X^{2m}(X²−a)²`, coefficient signs reduce to one quadratic in the index;
   threshold `a/(8m+10) ≤ σ_m ≤ a/(8m+5)` (`maskedPairHeatThreshold_lower`, `maskedPairHeatThreshold_upper`),
   strictly decreasing; exact closed form (`maskedPairHeatThreshold_eq`); at first contact exactly one even
   coefficient vanishes, of degree `m + 2 + (m mod 2)` (`centralMaskedPair_heat_contact_iff`) — higher-order
   contact persists. Gaussian parameter is `λ = 2s` (`maskedPairMoments_nonneg_iff_threshold`).
7. **Hermite root barrier.** If `P ≥ 0` has degree `2d` and `exp((λ/2)D²)P` is coefficient-positive, every
   positive root satisfies `δ ≤ √λ·h_d` (`nonnegative_root_le_sqrt_mul_hermiteEdge`); equality forces the scaled
   Hermite extremizer (`scaled_nonnegative_edge_root_rigidity`), whose heated form has only constant and
   leading coefficients (`hermiteExtremizer_heat_middle_coeff`) — generic contact need not be at order zero.
   Extremizer: exact double roots, positive cofactor (`scaledHermiteExtremizer_positive_cofactor`). Edge:
   strictly increasing (`hermiteEdge_strictMono`), `h_d²/(2d) → 4` (`tendsto_hermiteEdge_sq_div_degree`); optimal
   fixed-depth heat `a/(2h_{m+2}²)` (`isLeast_fixed_depth_heat`); central masking costs asymptotically twice the
   optimum (`tendsto_central_to_optimal_heat_ratio`).
8. **Root-radius heat cone.** Any monic real polynomial of degree `N` with all roots in `|y| ≤ r` (any
   configuration: clusters, multiple roots, complex pairs) has `exp(s∂²)q(x²)` coefficient-positive once
   `32r ≤ sN` (`coeffNonneg_forwardPolyHeat_expand_of_discFactors`) — via Gaussian moments of Hasse derivatives.
   Order `r/N` is sharp: `(y − r)^N` needs it.

### From source to local factor
9. **Exact source factorization.** The canonical radius head is `c_{t,R}D_{t,S}(z²)`, `c > 0`, without dividing
   by `Ξ(t)` (`xiFiniteHead_eq_localDivisorPolynomial`, `xiFiniteHead_even_taylor`); splits give exact coefficient
   convolutions (`localDivisorPolynomial_split_coeff`). `D` is monic of degree = retained copies; the horizontal
   polynomial is monic, even, nonnegative (`horizontalDivisorPolynomial_nonneg`).
10. **Source Hermite obstruction.** A retained off-line copy gives a positive root at depth `δ` with its
    reflection (`N ≥ 2`); heat positivity at `λ/2` forces `δ² ≤ λh_N²` (`radiusHead_depth_sq_le_hermite_edge`).
11. **Counting repairs every head at large height.** Radius-`R` head roots lie in `|y| ≤ R²`, so heat
    `32R² ≤ sN(t,R)` suffices whatever the configuration (`coeffNonneg_heat_localDivisorPolynomial_radiusHead`);
    Riemann–von Mangoldt makes `N(t,R) → ∞` (`exists_le_card_radiusHead`); hence for every `R ≥ R₀` and `λ > 0` the
    heated head is coefficient-positive at all large heights (`exists_radiusHead_heat_coeffNonneg`), and through
    the head/tail transfer every heated slice coefficient is ≥ 0 there
    (`exists_xiSliceHeatTransfer_nonneg_of_head_counting`). This is a finite-head Ki–Kim–Lee from counting alone.
    **Scale gap:** counting gives heat `≍ R/log t`; the detector needs `≍ δ²/log t`. Configuration-free repair
    must cover pairs of depth up to `R`, so it cannot reach depth-`δ` resolution — sign information is required.
12. **Contour moments.** `p_j(t)` are multiplicity-exact power sums; Newton recovers coefficients (corpus).
    The missing certificate is a sign theorem for the signed Newton combinations.

### Heat and charge interfaces
Forward horizontal heat on the slice ≠ de Bruijn–Newman evolution (bridge via Gaussian height averages).
Existing producer: heat `(17/25)/log|t|` at large heights. Detectors: `κ₀(δ) = δ²/(200(log(3/δ)+1))` (older);
sharper finite-head receiver: positivity at some `λ(t) ≤ δ₀²/(320 log(180|t|))` for `|t| ≥ 73/5` with radius
`½ ≤ R ≤ 1` implies `zetaZeroWidth ≤ δ₀` (RHTower). Positivity propagates to larger heat; eventual estimates
need finite-height accounting.

| Endpoint | Required arithmetic output |
|---|---|
| Local coefficient cone | Radius-one heads coefficient-positive at every height, every order up to actual degree |
| Horizontal collision | Exact positive-height gross charge below two on cofinal cutoffs |
| Global heat collision | Total future collision mass below four on heats → 0 |
| Ward cap | A.e. nonpositivity of the real completed cap at a fixed positive parameter |
| Threshold contact | Actual source forces zeroth-order contact at the Ward threshold |

Currencies differ: horizontal charge counts same-height pairs with multiplicity; heat charge counts
disappearing nonreal multiplicity (four-unit normalization); the Ward cap is weighted with no integer gap.

---

## 5. Pillar theorems

1. One-factor and multiplicity repair laws (`exists_linear_repair_iff`, `coeffNonneg_geometricRepair_even_iff`).
2. Universal reflectors (`universal_coefficient_reflector_iff`).
3. Masked-pair threshold and contact (`maskedPairHeatThreshold_eq`, `centralMaskedPair_heat_contact_iff`).
4. Hermite root barrier and extremizers (`nonnegative_root_le_sqrt_mul_hermiteEdge`, `scaled_nonnegative_edge_root_rigidity`, `isLeast_fixed_depth_heat`).
5. Root-radius heat cone (`coeffNonneg_forwardPolyHeat_expand_of_discFactors`).
6. Exact source factorization and source barrier (`xiFiniteHead_eq_localDivisorPolynomial`, `radiusHead_depth_sq_le_hermite_edge`).
7. Large-height head repair from counting (`exists_radiusHead_heat_coeffNonneg`, `exists_xiSliceHeatTransfer_nonneg_of_head_counting`).

---

## 6. Traps

- Real-axis positivity does not imply coefficient positivity.
- Positive factors cannot be cancelled from a cone statement (only `c·y^a` reflect).
- A multiple zero is not a simple zero with negligible error; a changing degree is not a fixed-order asymptotic.
- A qualitative zero-free boundary gives no quantitative separation.
- An ordered orientation sum may vanish by symmetry while the even collision defect stays positive.
- A nonnegative count equal to defect plus another nonnegative term gives no upper bound on the defect.
- A later zero heat charge does not force an earlier one to vanish.
- Separate local certificates may spend the same Gamma/polar reserve twice.
- Counting-based heat repair (order `R/N`) is configuration-blind; it cannot reach depth-`δ` detector scale.
- Polynomial heat at `s` is Gaussian parameter `2s` — double constants at the Hermite interface.
- A generic sign-preserving representation is not a producer until its source identification is proved.

---

## 7. Open problems

1. **Signed source coefficients**: a source-only sign certificate for the Newton combinations.
2. **Sign control across nonmonomial transitions**: which source certificates survive adding/removing a shell.
3. **Arithmetic selection**: a law of the actual source excluding impure configurations accepted by symmetry and
   norm-square positivity.
4. **Ordered curvature**: keep prime/Gamma channel labels through a singularity-sensitive source-to-divisor map.
5. **Horizontal collision budget** below two, with all mixed and boundary terms.
6. **Detector-scale production**: retained-head coefficient positivity at `δ₀²/(320 log(180|t|))`, every order,
   with finite-height range. Counting reaches the right `1/log t` order but the wrong constant (`R` vs `δ²`);
   closing the gap needs configuration-sensitive (sign) input.
7. **Degree and clustering**: estimates on actual local divisors calibrated by the multiplicity cost.
8. **Heat collision budget** uniform as heat → 0.
9. **Contact rigidity**: why actual arithmetic excludes positive Ward thresholds whose contacts are all at higher
   orders (masked pairs and Hermite extremizers show polynomial properties alone do not).

---

## 8. Tools to build

A source sign certificate (Newton combinations, collision charge or Ward cap) at detector scale
$\delta_0^2/\log t$; configuration-sensitive head repair closing the $R$-vs-$\delta^2$ gap.

---

## 9. Contribution criteria

A foundational contribution proves an exact mechanism, sharp classification, quantitative stability law or
faithful source identity not already available; retains multiplicity; states every dependence on height,
radius, degree, separation and heat; extracts the positive survivor of a failed mechanism. An arithmetic
contribution identifies the actual source input, proves its selective force, accounts for all mixed and
boundary terms, and names the receiver consuming its output. An RH-equivalent condition is a receiver
description until its input is independently established.
