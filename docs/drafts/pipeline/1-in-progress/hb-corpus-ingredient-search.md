# HB: corpus ingredients for the complete causal pairing

- **ID:** HB-CORPUS-INGREDIENTS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE; inspected corpus ingredients and an interior paper construction
- **Source:** `scripts/formal_tools.py research`, actual Lean statements and proof bodies, [optical source reduction](hb-optical-source-tail.md).
- **Statement:** Assemble the complete optical boundary current from existing polynomial and Green identities, then prove its comparison with the original physical boundaries.

## Exact target

The chain is literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target is the complete pairing `2 Ω(B(p,p)/2,B(m,m)/2)=0`, retaining independent SS/SV/VV amplitudes and onset, horizon, AdS, temporal and cusp terms. The optical work gives explicit scalar coefficients multiplying the native angular kernel. The immediate source-specific target is their boundary reduction and comparison with the physical current. Neither the existence of a general Green formula nor construction of a propagator establishes that comparison.

RH remains unproved. This card records no exhaustive audit of the corpus and makes no claim that every missing ingredient already exists. The frontier map is read only.

## What the search tool covers

The legacy lexical index (`scripts/formal_tools.py:index_rows`, selected by `--mode lexical`) indexes names, module names and adjacent full docstrings, excluding theorem statements and proof bodies. Its prose coverage consists of gap-marker lines. A marker containing “missing” may describe a gap that the same file closes.

The current tool also has hybrid/deep discovery and `--retrieval-views statements|all`. Its inspected hybrid output includes actual theorem signatures and source-argument candidates, but reports incomplete source and semantic coverage. The inspected request reported 22571 indexed and 33302 stale/pending files among 55873 inventoried files; these are a changing indexing snapshot, not a theorem audit. Read the per-request coverage and `source_only`/compiler status before treating a result as validated. Lexical discovery remains useful for fast broad terms; hybrid/deep retrieval can then pursue the exact source equation within a bounded request budget.

The lexical conjunction and result caps affect discovery separately:

- Spaces mean AND; `--any` means OR. Exact phrases can miss equivalent terminology.
- Default output is 20 declarations, at most two per module, plus five exploration results. The printed total is larger than the inspected page.
- `--per-module 0` removes the module cap; pagination is still required when results exceed the limit.
- `--no-refresh` uses the cached index. Refresh after new source installation before treating a search as current.

In this intake, the exact phrase `"bilinear concomitant"` returned no declaration, while `Lagrange` exposed the actual complex derivative-to-boundary identity. `Goursat` exposed a constructive characteristic solver under a different module family. These observations establish retrieval limitations, not mathematical absence.

The broad named searches requested by the user also show why one ranked page is insufficient. Cached totals were `Fokas`: 3146 declarations/248 modules; `Higgs`: 297/29; `Einasto`: 572/37; `horizon`: 11271/1788. These are search metadata, with overlapping scopes, not counts of inspected or applicable theorems.

## Search procedure tied to a proof obligation

1. Write the exact desired equation, its domain and the actual source. For the optical step these include `D_star=∂L²(L²·)-∂z²(L²·)`, `Delta M=L²(M_LL-M_zz)`, and the original coefficient functions from the four radial primitives.
2. Search independent structural words across the whole corpus first: `Lagrange`, `Darboux`, `Goursat`, `telescoping`, `bidiagonal`, `transmutation`, `divided`. Use short synonym families with `--any`; inspect scarce terms separately so a common term cannot bury them.
3. Follow a promising family with `--module`, `--per-module 0` and complete pagination. Read the declarations' statements, section variables, relevant definitions and proofs with `rg` and bounded file reads.
4. Search the conclusion and each substantial hypothesis separately. Follow imports backward to its construction and theorem uses forward to actual applications. Record which assumptions those applications discharge.
5. Attempt a specific substitution into the HB source equation. Keep the measure, bilinear versus Hermitian pairing, original clock, boundaries and regularity domain explicit. The output is an instantiated identity or a precisely stated remaining bridge.
6. Continue the conjecture → proof/failure → pivot loop on that bridge. Reuse an inspected theorem without rebuilding it or repeating its axiom audit. Formalize a new source-specific statement only when its proof is closed.

Example discovery and focused queries used here:

```sh
python3 scripts/formal_tools.py research Lagrange --no-refresh
python3 scripts/formal_tools.py research '"Green identity"' --no-refresh
python3 scripts/formal_tools.py research Goursat --no-refresh
python3 scripts/formal_tools.py research Goursat --module ClockGoursat --per-module 0 --limit 100 --explore 0 --no-refresh
python3 scripts/formal_tools.py research '"divided difference"' --no-refresh
python3 scripts/formal_tools.py research 'cancellation conservation boundary' --any --module FokasLenells --no-refresh
rg -n 'SturmLagrangeIdentity|integral_sturm_pairing_sub_complex' formal/GaloisForLFunctions --glob '*.lean'
```

The earlier [arithmetic architecture audit](rh-corpus-architecture-audit-2026-09-05.md) already distinguishes ranked discovery from full statement inspection. Its route-specific exclusions describe that separate task; they do not restrict this HB ingredient search.

## Inspected ingredients and their exact use

Paths below are relative to `formal/GaloisForLFunctions/`. The statements and indicated construction paths were read; no existing module was rebuilt or re-audited.

| Needed operation | Existing declaration | What is supplied; remaining HB bridge |
|---|---|---|
| Convert an actual complex second-order pairing into endpoint brackets | `HTGeometry/SturmLagrangeIdentity.lean:74`, `HTGeometry.hasDerivAt_lagrangeBracket_complex`; integral form at line 84 | Product-rule identity and interval integration with actual derivative and integrability premises. Supplies each coordinate of the current below. Actual endpoint values remain to be compared. |
| Telescope a polynomial of a common operator without dividing by spectral gaps | `HTGeometry/DividedDifferencePolynomial.lean:35`, `GaloisForLFunctions.HTGeometry.poly_sub_eq_mul_dividedDifference` | A finite polynomial difference factors algebraically over any commutative ring. Its finite-sum proof supplies the polynomial-current construction below. Instantiation to commuting left/right actions must be made explicitly. |
| Integrate every boundary face of a truncated modular cusp | `RHTower/SelbergModularCurrentGreen.lean:173`, `GaloisForLFunctions.RHTower.SelbergModularCurrentGreen.current_green_identity` | Real C¹ currents on the upper half-plane give both vertical sides, top and both arc contributions. Complex HB currents require real/imaginary components and their actual C¹ proofs. Cusp limits remain separate. |
| Construct a characteristic initial-value solution | `HTGeometry/ClockGoursatGlobal.lean:43`, `GaloisForLFunctions.HTGeometry.exists_goursat_global` | Constructs a jointly continuous **real scalar** solution with local characteristic derivatives from a continuous bounded kernel. “Global” concerns the clamped continuous extension; the differential equation is local. An unbounded angular operator and global physical boundary conditions are additional obligations. |
| Prove cancellation through a primitive and its actual decay class | `HTGeometry/FokasLenellsRawQuinticMoments.lean:29,53`, `GaloisForLFunctions.HTGeometry.FokasLenells.integral_quartic_derivative`, `integral_coordinate_sq_derivative` | Constructs the Schwartz primitive of `q⁴q′` and evaluates `∫x²q′=-2∫xq` using the coordinate commutator. This is a concrete proof pattern. HB's finite characteristic domain and cusp remainder have not been identified with these Schwartz data. |

Reverse-use inspection adds useful precision. `RHTower/ProlateCommutationKernel.lean:55,116` constructs an actual two-variable kernel identity and then uses the Lagrange theorem; its endpoint cancellation follows from its explicit weight `1-t²`. `SelbergMaassDilationRellich` applies the modular Green identity to its original dilation current. These are source constructions to learn from, not boundary conditions to assign to HB.

Other inspected hits have a narrower role. `StrictlyLoweringFiltration.StrictlyLowering.pow_apply_eq_zero` requires a filtration actually lowered by the operator; the HB density derivative is not yet such an instance. `CyclicActionNoether.CyclicMaurerCartanLaw` includes Bianchi and cyclic identities as fields, and the inspected applications still take that structure as input. `XiWardCubicBoundaryResolventTransmuter` supplies a scalar rational Laplace transfer. `EinastoHorizonBalance` proves actual radial tail estimates for its Einasto density. None of these statements supplies the complete HB source/boundary comparison as written.

## Constructive use: the full finite optical transfer current

This is a paper identity on a smooth interior optical cell. It constructs the optical integration-by-parts terms explicitly. It does not claim physical boundary cancellation or a new Lean theorem.

Write `A=L²(∂L²-∂z²)` and `D_star F=∂L²(L²F)-∂z²(L²F)`. The angular variable is held separate. Let `M` be the native circle mean, with `A M=Delta M`; require the derivatives appearing below and commutation of angular and optical derivatives on the interior cell. The calculation is complex bilinear.

Define the two components

```
J_L(F,M) = ∂L(L²F) M - L²F ∂L M,
J_z(F,M) = L²F ∂z M - ∂z(L²F) M.
```

Expanding the two product derivatives cancels the first-derivative cross terms and gives

```
div J(F,M) = (D_star F) M - F Delta M.                 (1)
```

This is the complex Lagrange identity applied in each coordinate to `L²F` and `M`. For `P(X)=sum_(k=0)^N c_k X^k`, define the explicit finite current

```
J_P(F,M) = sum_(k=1)^N c_k
             sum_(j=0)^(k-1) J(D_star^(k-1-j) F, Delta^j M).
```

Equation (1) applied to each summand telescopes:

```
div J_P(F,M) = [P(D_star)F] M - F P(Delta)M.          (2)
```

Indeed the summand divergence is
`(D_star^(k-j)F)(Delta^j M)-(D_star^(k-1-j)F)(Delta^(j+1)M)`.
Only the first and last terms survive. This is the same finite difference-of-powers identity used by the corpus polynomial divided-difference proof. No root separation or spectral denominator is used.

For the literal logarithmic angular channel, put

```
T(X) = -X^4 + 4(2lambda+1)X^3
         -4(lambda+1)(4lambda+1)X² + 8lambda(4lambda+1)X.
```

The required current is therefore the following fixed ten-term expression:

```
J_T(F,M) =
 -J(D_star³F,M) - J(D_star²F,Delta M)
 -J(D_star F,Delta²M) - J(F,Delta³M)
 +4(2lambda+1)[J(D_star²F,M)+J(D_star F,Delta M)+J(F,Delta²M)]
 -4(lambda+1)(4lambda+1)[J(D_star F,M)+J(F,Delta M)]
 +8lambda(4lambda+1)J(F,M).                           (3)
```

This can be applied to the actual optical logarithmic coefficient. With the notation of the optical source card, define positive-real-base powers by `L^delta=exp(delta log L)` and set

```
d = L-z,
q_minus = max(L,d-1),
F_log = -3(L+d)/L² * (L^delta-L^(-delta))
          * log((d+1)/q_minus),
kappa = (lambda-2)(lambda-6)/64.
```

Up to the already retained common normalization and outer angular source, the logarithmic integrand is exactly `kappa F_log T(Delta)M`. This follows from the `F33` primitive and the formal coefficient factorization. Equation (2) represents its optical transfer with the current `kappa J_T(F_log,M)`.

For the principal source, the already formalized identity is `T(Delta)Q_principal=0`. When the required native-mean commutation is supplied, (2) gives the more explicit interior boundary identity

```
[T(D_star)F_log] M(Q_principal) = div J_T(F_log,M(Q_principal)).
```

For the complete source, the `T(Delta)M` term is retained. Equation (2) also applies separately to every rational coefficient of the four primitives, with the appropriate polynomial `R(X)`, `R(X)A_s(X)`, `R(X)A_t(X)` or `R(X)A_s(X)A_t(X)`. Summing these currents treats the full optical transfer, with polynomial degree at most four.

On a finite smooth cell, the oriented boundary form is `J_L dz-J_z dL`. At `z=-1` the formula for `q_minus` changes; the two cell traces must be combined. The logarithmic and rational pieces must be combined before judging interface cancellation. At `z=1-L`, characteristic right jets are required. Optical lower/upper edges, source edge `z=1`, compact onset transition, angular Green faces and physical current corrections remain in the comparison. Interior identity (2) does not by itself justify their limits.

## Source-specific use of the search results

The [source-polynomial boundary calculation](hb-optical-source-boundary-matching.md) applies this construction with the spin-two weight retained on the angular field. Only the degree-two source polynomial is transferred. The actual four radial caps then have enough flatness to cancel the internal interface and source-edge currents; the moving characteristic becomes an explicit corner primitive. This is a finite-domain paper result, leaving the explicit bulk and corrected cross-section flux for physical comparison.

A further broad jet search exposed `HTGeometry/IteratedDerivVanishing.lean`. Its actual derivative-factor and product theorems close the four [new scalar cap results](../3-formalized/hb-optical-source-boundary-caps.md), including the original moving target factor and both signs of cap length. This is an instantiated source identity obtained through corpus reuse, rather than a general theorem whose boundary premises are still supplied by hand.

For physical flux comparison, broad `Green`, `commutator`, `intertwiner` and `transmutation` searches were followed by the actual BM absorption family. The existing `ThetaCuspHawkingBMJointSourceTimeField.timeOriginalForcing_gradient_absorption` supplies an explicit lift whose subtraction removes angular derivatives from the forcing. Applying it in both slots of the complete physical current gives the [two-sided source reduction](hb-two-sided-source-current-reduction.md). Its onset derivative contributes a fixed rational correction; the complete reduced long-delay radial primitive has no logarithmic term. The lift's physical boundary currents remain attached to that bulk. A bounded deep search for the Green mechanism returned partial source-only candidates and no proof ideas or ingredient sets; its ranking was not treated as an applicability check.

## Next source-specific conjecture

### Existing full-source constructions found by following hypotheses

The principal-response hit is only the entrance to a larger construction. Following its uses and the complete source transform exposes these already proved ingredients:

| Existing declaration | Actual scope and use |
|---|---|
| `ThetaCuspHawkingBMJointSourceCausalCuspSourceIdentification.causalCuspSourceVector_laplace_original` | The literal assembled causal source, including all three cutoff channels, has exactly the admitted cusp-residual transform above its explicitly constructed threshold. |
| `ThetaCuspHawkingBMJointSourceForcedCausal.causalCuspSource_original_joint_response` | Constructs a frequency-independent response with causal support, weighted time `L²` admission and the original unbounded operator-domain equation. Its named Laplace identities hold in the stated right half-plane. |
| `ThetaCuspHawkingBMPhysicalResponseGreenIdentification.physicalCuspProfile_eq_completePhysicalGreenProfile` | Identifies each actual physical angular projection with its complete endpoint Green integral, with source admission and endpoint currents discharged internally. The statement retains its frequency chamber `3/2<Re(w)<2`, `Im(w)≠0`, and exterior radial domain. |

These entries identify modules and declaration names; their namespace is `RHTower.D4BMJointSource`. They remove the need to reconstruct those existing objects. They do not by themselves identify the newer native-circle integral with the whole unprojected response or evaluate its integrated action pairing. Different stated transform chambers must be connected by the actual continuation theorems, not treated as automatically overlapping.

Broad `Abel`, `Mehler`, `Legendre`, `spherical`, `transmutation` and `Casimir` discovery did not yield an inspected theorem evaluating the full native-mean pairing. This is a result of the inspected hits, not an absence claim about the corpus. In particular, `LegendreLaplaceHeine` is an asymptotic theorem for integer-degree polynomials, not the required full-angular transform. Broad `autocorrelation` discovery exposed `HTGeometry.HalfLineAutocorrelationPrimitive` and `PairedContactAutocorrelation`; their finite-integral and contact proof mechanisms motivate a direct calculation with the actual HB clock rather than substituting their different source classes.

That source-specific calculation is the [finite reduced-source clock transfer](hb-reduced-source-clock-transfer.md). It analytically transfers both original onset derivatives onto two explicit first-order native-kernel operators, retains the moving terminal contribution, and evaluates its characteristic contact using existing native jets. Its long-delay specialization reproduces the rational-tail coefficient; its zero-delay specialization uses the squared-onset clock. No new Lean theorem is claimed for that calculation.

The sum of the explicit currents in (2), the original angular Green terms and the physical current corrections has fixed traces whose complete finite-domain balance cancels the retained compact onset contribution. Proving this requires the actual source coefficients and every face; the first nonzero optical coefficient identified in the optical source card is part of that calculation.

The next search is for constructions that discharge this **specific trace comparison and remainder bound**. A general primitive, scalar Goursat solution or cyclic structure alone does not discharge it. If a candidate theorem has exactly that conclusion under auxiliary assumptions, each assumption becomes a separate source-specific search and proof obligation.

The initial search intake used source inspection and paper work. The subsequent four cap theorems passed scratch checks and one exact-module build against existing caches. No mathematical computations, existing-module rebuilds, existing axiom rechecks or frontier-map changes were made. No axioms were added.
