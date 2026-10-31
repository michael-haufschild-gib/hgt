# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates and the retired PW-B branch, checked against the Lean
corpus at `8ff22f82a4`. For every route: what is established, the obstacles that are **(A) just
work** (known mathematics, finite computation, effectivisation, formal closure), and the obstacles
that are **(B) open mathematics** (no known solution).

Legend. `[L]` Lean theorem, statement read. `[S]` Lean source unfinished or outside its umbrella.
`[map]` frontier-map status, statement not read here. Strength of a B-item: **RH** = equivalent to
RH; **≥qRH** = implies Lindelöf and a zero-free half-plane `Re s > ½ + α`; **sub** = strictly
weaker than RH or of unknown strength. Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme
codes as in the frontier-map source locator; RIT = RenormalizedIntersectionTheory.

## 0. Hardness calibration (applies to every route)

| Fact | Anchor | Consequence for routes |
|---|---|---|
| `κ(K_ζ) = #` right zeros, already on two primes; RH ⇔ `κ = 0` ⇔ `κ ≤ 1` | HKT `TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] | every index route ends in the same integer |
| `κ < ∞` ⇔ finite off-line support ⇒ Lindelöf + zero-free half-plane | same [L] | every finite-index waypoint for `K_ζ` is **≥qRH** |
| Künneth square is all-or-nothing: RH or `κ(K_ζ⊠K_ζ) = ∞`; `κ_ζ² ≤ κ(K_ζ⊠K_ζ)`; every Hadamard power `K_ζ^n` PD ⇔ RH | RIT `riemannHypothesis_or_negIndex_kunnethZeta_eq_top`, `sq_negIndex_zetaKernel_le_negIndex_kunnethZeta`, `riemannHypothesis_iff_isPosDefKernel_zetaKernel_pow` [L] | tensor or power amplification never softens the sign; any finite index ceiling for `K_ζ⊠K_ζ` is **RH** |
| Archimedean Weil state `κ(ratCorr(|a|) − c|a|^{−½}|b|) = κ_ζ + 1`; the same at every prime place; translation reading has exactly one square | AKG `WeilsArchimedeanStateCountsTheZeros`, `TheGluingFormulaAtEveryPlace`, `TheTwoReadingsAdd` [L] | RH ⇔ index one for one explicit affine state; the zeros live entirely in the multiplicative reading |
| Boost hyperplane = `v₁^⊥` = Markov hyperplane = harmonic hyperplane; `v₁` is the complete-Weil ground state | RIT `ThePoleClassIsTheGroundConductor`, `TheHodgeIndexAtGrowingOverlap` [L] | SC, the complete-Weil cluster and the Markov (SSHA) criterion are one sign problem on one hyperplane |
| Universal regime: tilted spline all-vector positive for `1 ≤ c ≤ (log N)^α`, `α < α* = min(1/500, 1/(60 C_cut))`, `C_cut` ineffective | CACT `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_powerLog` [L] | positivity proved without zero information at every power of `log N` below `α*` |
| RH regime: tilted spline full space at `2(log N)^{α>¼}`, `v₁^⊥` at `α>½`; every C^∞ profile on `v₁^⊥` at every `2(log N)^{α>0}`; sinc profile at `≍ L(log L)²`, `L = log log N` | RAPT `riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log`; RIT `riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log`; TM `TheSincProfileHasAnExactCriticalOverlap` [L] | a regime where positivity is proved unconditionally excludes no off-line zero beyond what is excluded unconditionally; RH sits at the detection edge between the regimes |
| Ground energy `E₁(c) ≍ τ(c)` (profile Fourier tail); at the sinc RH threshold `τ(c) log N ≈ 1` | RAPT completed energies; TM sinc [L] | at the edge every method must control the matrix to accuracy below `≈ 1/log N` on all vectors |
| One-sided count `ψ(x) − x ≤ C√x log²x` ⇔ RH; section shortfall rate ⇔ zero width | ACP, SPTL [L] | every exponent gain on a count is quasi-RH |
| Index twin-blind; glue pole-blind; glued test index `∞` on finite flips, `κ_ζ+1` on `Λ`; atomic Hodge index separates exactly submaximal margins | AKG `TheIndexIsTwinBlind`, `TheGluingSquareIsSharp`; RIT `TheGluedIndexSelectsZeta`, `TheAtomicHodgeIndexSeparatesExactlyTheSubmaximalMargins` [L] | selection must come from prime data; maximal-margin infinite twins are unselected |
| Heat: `κ(φ_c^{(t)}) = N(t)/2 + 1`, antitone, collision jumps, `1` for `t ≥ 1/8`; `0 ≤ Λ < 1/8` | AKG `TheHeatDeformedArchimedeanState`; RHTower `DeBruijnNewmanConstant` [L] | heat routes reduce to `Λ = 0`; positive-time finiteness is free, `t ↓ 0` is the problem |
| Pointwise local count bounds critical multiplicities; counting inputs give it only in density | SRT `TheLocalCountBoundsTheMultiplicity`, `CountingInputsDoNotBoundTheLocalCount` [L] | local-count hypotheses are off the RH path |

## 1. Shared obstacle blocks

### S1. Complete Weil matrix at growing overlap
Routes: HF, SRT, AIP, ACS-atomic, ACT, SC (finite resolution), CHMD-index; RW/EWU/OWU through the
ground minimum.

Established:
- universal regime: tilted spline, all vectors, `1 ≤ c ≤ (log N)^{α<α*}`: PosDef, floor `κ/(2c⁷)`,
  literal `weilQuad ≥ 0`, reserve `W ≥ (b/c²³) D_N` and `W ≥ (b/log N) D_N` [L] (CACT); mechanism:
  spectral-floor shift, low band `Q₁ = ⌊(log N)^{1/12}⌋`, exponential confinement at
  `log R' ≤ C c⁴⁶ + log Q₁`, coercivity above `Q₁` from the reverse defect gap
  `poleDefect ≥ (log Q/C_cut − 1)‖y‖²` [L];
- fixed packets `(log N)^{<1/19}` [L]; fixed `c` with gap on `v₁^⊥`: energy `≥ (E₁ + g/2 − ε)‖x‖²` [L];
- conductor averages at RH-complete overlap: `M = ⌊N^θ⌋`, `θ < ½`, `c²/log N → 0`: summed residual /
  `Σ E_m² → 0`, nonpositive-conductor fraction `→ 0`, nonpositive span dimension `o(M)` [L] (CAF);
- residuals `‖(W − E_m)v_m‖² ≤ K m⁴(c⁵/log N + c¹⁰(log N/N)² + c³/√log N)`, `m ≤ (log N)^A` [L];
  conductor-band operator bounds for overlap, non-ratio, prime, center, pole and separated errors on
  `conductorSubspace R N`, `R⁶ ≤ N` [L];
- RH regime and detection edge: see §0 [L];
- hyperplane positivity leaves at most one negative eigenvalue [L].

Location of the sign problem (interpretation of the anchors): the binding losses of the method are
(i) the norm residual against the floor (`Q⁵ c¹⁴ · rate ≤ 1/36`; fixed packets stop at `19 = 5 + 2·7`),
(ii) exponential confinement: nonpositive units have defect `≤ C c¹⁶`, which confines them only to
conductors `≤ exp(C c¹⁶)`, below `√N` only for `c ≤ (log N)^{<1/16}`. At RH-complete overlap the
ground energy is `≲ 1/log N` (sinc) or `(log N)^{−7/4}` (tilted), and every error must be beaten at
that scale.

| | Obstacle |
|---|---|
| A1 | Effectivise `C_cut` (explicit `α*`) and optimise the internal exponents of the power-log proof (`Q₁` exponent `1/12`, cutoff `c⁴⁶`, cubic `η` dependence) up to the method's ceilings (`1/19` floor ratio, `1/16` confinement) |
| A2 | Growing-packet head-pole cancellation, packets up to `exp(c√log Y)` (window PNT with classical error) |
| A3 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` |
| B1 | Positivity on an RH-complete schedule / on `v₁^⊥` across the detection edge — **RH** (Σ1, Σ14) |
| B2 | Signed (quadratic-form) estimate on the subthreshold conductor block (`m ≲ c`) beating the norm-residual-versus-floor exponent — **sub** (Σ13) |
| B3 | Defect bound for nonpositive vectors below `c¹⁶` (confinement below `√N` at larger overlap) — **sub** in the universal regime, **RH** at RH-complete overlap (Σ1c) |
| B4 | Exceptional conductors beyond `(log N)^A`: individual residual control — **sub** (Σ1g, Π9) |
| B5 | Conductors `N^{½} < m ≤ N`: frames or residual averages — **sub**, Elliott–Halberstam type (Σ1h) |
| B6 | Exact detection threshold of the tilted spline in `[α*, ¼]` — **sub** (Σ14) |

### S2. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD-index, SC, RIT-Künneth.

Established [L]: index = right-zero count; finite stratum TFAE; converse Krein–Langer for orbit
kernels; transverse energy pays each negative square; collision mass `= 2(κ + excess)` on the finite
stratum; `κ ≤ sup O`; Jordan pair signature `κ(Σ J_{u_i,P_i}) = Σ(deg P_i + 1)`; Künneth inertia law
and all-or-nothing dichotomy; finite-rank changes preserve finiteness of index.

| | Obstacle |
|---|---|
| A4 | Explicit capture stage for complete-cell indices (AID `TheCompleteCellsCaptureEveryFiniteIndex`, [S]) |
| B7 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ⊠K_ζ` (Σ5) |
| B8 | Converse Krein–Langer for kernels not presented by a zero configuration — **sub** |
| B9 | `κ₊(K_ζ)` on the infinite stratum — **sub** |

### S3. Heat flow, collision charge, integer readings
Routes: WD, LA, TH, TT, HCF, SC-heat; HEF receivers.

Established [L]: heat state `κ(φ_c^{(t)}) = N(t)/2 + 1` with continuity, lower semicontinuity,
antitone, collision drops, `1` for `t ≥ 1/8`; Hodge defect of `K_t` = future collision pairs;
`E(t)` dissipation; slice/flow thresholds (`Λ = sup Λ_X`, `c d²/log X ≤ Λ_X ≤ (2/3+ε)/log X`); reality
horizon `2πe^{(2/3+ε)/t}`; `λ_t log t → 0` ⇔ zeros tend to the line; collision charge `O ∈ 2ℕ`,
RH ⇔ `O < 2`; integer theta Wiener–Hopf operators with Fredholm index = charge on every window for
`n ≥ thetaWindowScale T`, `N ≥ thetaPrefixThreshold T n`; explicit constants, product-current error
`< 1/8` for every `T` at `n ≥ 6`, gap-calibrated rounding stage; RH ⇔ rounded readings vanish for all
`T`, `n ≥ 6`; index `0` on `T ≤ 3` (sectoriality); index transition only through window-boundary or
Zhukovsky-ellipse crossings; boundary ingress mandatory; first stabilized prefix unbounded in height.

| | Obstacle |
|---|---|
| A5 | Stronger subconvexity exponent to lower the heat floor `2/3 = 4μ(½)` (calibration) |
| A6 | Source-intrinsic stopping rule: prove the source-perforated and loop certificates sound and eventually complete; integrate the seam-smooth prefixes (CDG `SourceIntrinsicStoppingRule`, `SeamSmoothThetaPrefixes`, [S]) |
| A7 | Certified de Bruijn–Newman upper bound below the corpus value `1/8` (Polymath-type numerics) as an index-one time for the heat state |
| B10 | Subcritical heat count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub** |
| B11 | Pointwise horizon constant `< ½` — **≥qRH** |
| B12 | Source-side collision charge `< 2` on every window; no heat-index jump on `(0, 1/8]` — **RH** (Σ8, Σ16) |
| B13 | Uniform-in-height bound on the collision charge (any constant) — **sub**; implies critical fraction `→ 1` |
| B14 | Every `Λ_X = 0` — **RH** |
| B15 | Detection scale independent of the zero gap (a stage choice not depending on `collisionWindowGap`) — **sub**, needs zero-spacing control (Π13) |

### S4. Counts and producers
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity.

Established [L]: one-sided count ⇔ RH; prime-error budget `S ≥ 2 + γ − log 4π`; linear theta RR,
no quadratic Riemann inequality; integer Hecke stencils (integrality ⇔ step weight `≥ 0`); every
individual producer has slope `> 1`; ceilings `2 log 2`, `1 + 1/((P+1)(P+2))`, `31/30`, `exp(−0.87n)`;
growing-alphabet alternating producers: `ψ, θ ≤ (1+ε)x + C_ε log²x`.

| | Obstacle |
|---|---|
| A8 | Same-order mixed-jet recovery for `≥ 3` primes |
| A9 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer |
| B16 | ε-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3) |
| B17 | Any unconditional source input at square-root precision — **RH** (Π2) |
| B18 | Characteristic-0 quadratic effectivity — **RH** (Π11) |

### S5. Carriers, gluing and selection
Routes: SC, AKG, APD, Γ-candidates.

Established [L]: escape/mixing/height decay ⇒ `κ ∈ {0, ∞}`; local index wall at every prime and at
`∞` of `𝔽_q(X)`; Hasse principle for Hecke states; pole–successor `κ = κ₀ + 1` at every place; tower
signature `Σκ₀ + 1 ≤ κ ≤ Σκ₀ + 2`; gluing at every place; stable gluing; the glue absorbs exactly its
own pair and charges a double pole; shell identity of the archimedean form; Haar classification
`k = p + ψ∘slope + Q` and sharp punctured limits; global pole = extremal weight; no assembly of local
poles at two or more primes has one square; glued test index and atomic Hodge selection.

| | Obstacle |
|---|---|
| A10 | Relative splitting for general nonzero proper rational subgroup successors (Haar case done) |
| A11 | `𝔽_q(X)` calibration: local walls at higher-degree places, product formula for the global Hecke state, archimedean Weil state of a curve; function-field version of the extremal-weight gluing |
| A12 | Margins (hyperplane gaps) of infinite flip sets whose harmonic correlation decays slower than `(log N)^{−½}` |
| B19 | Exact sum-of-squares (shell) identity for Weil's dilation form on `ℓ = 0` — **RH** |
| B20 | Prime-local decomposition of `κ(K_ζ)` (signature formula for the Weil kernel) — **sub** |
| B21 | Zero-independent selection at the trivial gauge point — **RH** (Γ1) |
| B22 | Selection of maximal-margin infinite flip twins (flipped primes `≥ 11`, `S_N/H_N → 1`) — **sub** (Γ12) |
| B23 | Arithmetic correspondence acting as conjugation on the zero divisor (Frobenius at infinity) — **RH** (Γ4) |

## 2. Live routes

### WL — prime lag / Weil–Li energy
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔ RH +
simple; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; arithmetic Bézout; Landau-window cost
`(2 log 2 − ε)mn`; Adams `2^{qr}`; S4 producers up to the main term [L].
- A: A8, A9.
- B: one-sided prime-error bound (**RH**, Π1); B16; joint Möbius-moment / Mertens / sawtooth payment at
  square-root precision (**RH**, Π5).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0` ∀A ⇔ RH; RH ⇔ zeros approach the line ∧ `μ₀` subexponentially bounded below;
attained excess forces `μ₀(B) ≤ −c'e^{2ΘB}/B³` [L]; floors `≥ mass/5000` to `181/500`, `≥ mass/8000`
up to `A₊ < ½`; one sinc multiple `K` gives positivity on tests in `[−R, R]` with
`288e⌈1+e^{2(R+1)}⌉ < K/(4K_τ)` [L].
- A: certified positivity past the two-prime aperture `r ≥ ½ log 3`.
- B: all-aperture sign (**RH**, Σ1); subexponential floor for `μ₀` (**≥qRH** given zeros approaching the line).

### FU — Fourier/Abel prime scheduling
Established: completed Abel moment bounded above ⇒ RH; narrow-window negative prime channel [L].
- A: none identified.
- B: joint bound of seed, drift, prior, cross-block and endpoint terms (**RH**, Σ).

### CFC — first-clock sine coefficient
Established: RH ⇔ coefficient `≥ −C` on the aperture tail; unbounded below under ¬RH; phase-natural
transport is the identity [L].
- A: none.
- B: source lower bound retaining prime, archimedean and endpoint terms (**RH**, Σ).

### RP — normalized prime history
Established: RH ⇔ history `≥ −B(K+2)` eventually; unconditionally below `−δ(K+2)` cofinally; finite
prime-clock density cancellation [L].
- A: none.
- B: high-LCM pairs, moving core and singular transport at linear scale (**RH**, Σ/Π).

### PA — Hausdorff-order positivity
Established: each fixed order positive at large shifts [map].
- A: explicit shift threshold per order.
- B: all-order / all-shift positivity (**RH**, Σ4).

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`, RH iff the trivial point is typical;
cyclotomic remainder `≥ 0`; far modes `≤ 288N√(N+1)`; near modes at primitive conductor
`≥ (N+1)/⌈√(N+1)⌉`; uniform Dirichlet inputs and every inverse-log rate for `q ≤ (log x)^A`;
rough-packet large sieve; finite prime-clock cancellation; producers at the main term [L].
- A: none beyond the Siegel–Walfisz range.
- B: moving-scale half-power cancellation (**RH**, Π2); near-band cyclotomic energy `O(N^{3/2+ε})`
  (3/4 strip, **≥qRH**); head/leaf signed cancellation of finite prime clocks (Σ); trivial-point
  typicality (**RH**, Γ1).

### TT — theta seam / Wold
Established: seam, tail, Wold receivers; `t < ½` threshold; truncated theta transform `= −seed·B_N(ρ)`
at zeros; two-horizon windowed aperture modes [L].
- A: none.
- B: all-test directed covariance or complete odd positivity (**RH**, Σ3).

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; slice and flow thresholds; Vitali
blow-up; `λ_t log t → 0` ⇔ every fixed-depth strip contains all high zeros; strip ⇒ Littlewood
windows; right-half squared-depth moment `o(V)`; fixed-depth counts `o(V)` [L].
- A: explicit horizon per fixed degree; A5.
- B: all-degree / all-height signs (**RH**, Σ4); uniform tail narrowing (zeros tend to the line,
  **≥qRH**); shrinking-scale and exceptional-height control (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; central-gap receivers [map].
- A: none.
- B: matrix-complete decomposition with integer trace `< 1` on every disc (**RH**, Σ8).

### HF — Hodge/Hecke/complete cells
Established: S1 in full; Haar/prime-edge Gamma reserve; full Weil index `≤ R + A` for `R` coarse cells;
Hecke-defect and collided-form receivers; heat Hodge defect `= N(t)/2` [L].
- A: A1, A2, A3; A4.
- B: B1–B6; Hecke invariance of the collided form (**RH**, Γ4); Haar branch: non-arithmetic Gamma,
  signed potential, roots and poles jointly (Σ1b).

### CHMD — causal hyperbolic–modular duality
Established [L]: RH ⇔ `R ≤ ½` on the odd sector; prime wave `O(e^{|u|/2})`; every Haar piece except the
first-prime coarse layer has uniform finite index; Gamma graph pays the prime-two block; growing Euler
head alone unbounded; full prime window cancels the `√Y` pole on fixed packets.
- A: A2; fixed-cell first-prime / coarse / polar bookkeeping.
- B: uniform coarse-size control (finite index, **≥qRH**); odd-sector sign (**RH**, Σ3); joint
  positivity of non-arithmetic Gamma graph + signed diagonal + prime reserve + roots + poles (Σ1b).

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; `I₇(a) ≥ 0` on `0 < a < ½`; heated orthant signs all ranks;
all-rank signed-center positivity ⇔ RH [L].
- A: rank-8 strictness; ranks 9, 10.
- B: all-rank sign (**RH**, Σ4); rank-uniform signed flux payment (Σ4).

### RN — renewal
Established: compact cone-positive renewal operator with exact regularized determinant [map].
- A: none.
- B: directed mixed prime + Gamma `≥` pole (Σ); real spectrum from cone positivity fails; native
  unregularized synthesis is a no-go (Σ6).

### WD — Ward / collision / heat
Established: S3 in full; Ward/collision receivers; theta-prefix collision readings and integer
Fredholm index; low-window sectoriality; transition law; seam-smooth prefixes [S]; source-only
stopping predicate [S].
- A: A5, A6, A7.
- B: B10–B15; vanishing global depth energy as `t ↓ 0` (**RH**); tower branch arithmetic index ceiling
  (**≥qRH**).

### LI — guarded history zeros
Established: `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order [L].
- A: none.
- B: pay the outside budget at every guarded zero (Σ).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packet light-Gram identity; negative finite-cutoff
pairings of the Abel clock [L].
- A: none.
- B: uniform lower bound after complete source assembly (Σ).

### PM — physical / complete-energy realization
Established: complete-energy and gauge-mass receivers; half-damping admission; escape alternative;
PW-B optical tools (Ward law, positive response masses) as support [L].
- A: none.
- B: cofinal complete-energy bound as `ε ↓ 0` (**RH**); exterior tightness and exclusion of
  infinite-height escape (Γ/Π); half-parameter cusp selection (`Λ(s)` coefficient of `E*(·, s/2)`) —
  **RH**.

### JAS — joint ancestry
Established: positivity at growing logarithmic prime budget [map].
- A: none.
- B: square-root power budget (**RH**, Π).

### CTF — completion transfer
Established: Euler completion error `≤ 1/(n+1)`; equal limits of full and finite-source energies [L].
- A: none.
- B: full-source energy decay by signed covariance cancellation (Π); `B X^ε` receiver in the inner
  cutoff (Π).

### HCF — two-grid Hankel
Established: both `log 2`/`log 3` grids with polar cancellation ⇔ RH; one grid aliases [L].
- A: fixed-degree checks.
- B: both grid signs at every degree and height (**RH**, Σ4).

### XN — Newton dynamics
Established: RH ⇔ ξ-Newton source margin on discs; nonnegative Laplacian of the margin [map].
- A: none.
- B: cover every zero with nonnegative margin (**RH**, Γ).

### BAG — Bagchi recurrence
Established: RH ⇔ disc recurrence on every closed disc of the strip; Voronin universality [L].
- A: none.
- B: returns near every right-strip point including potential zeros (**RH**, Γ1).

### EWU — Euler weights
Established: RH ⇔ at every aperture some real weights make the full Weil functional nonnegative;
obstruction dual is a blind test [map].
- A: shares RW's fixed-aperture computations.
- B: nonnegative actual minimum at every aperture (**RH**, Σ1).

### GTA — transverse charge
Established: transverse-charge decay criterion; transverse energy pays each negative square [L].
- A: none.
- B: rank-uniform arithmetic transverse-energy decay (Σ4).

### OWU — odd Weil selectivity
Established: every `r > 27/50` has a smooth odd test on `[−r, r]` with `W_ζ > mass/25` and
`W_Liouville < −3 mass/10` [map].
- A: positivity on all odd tests slightly beyond `27/50` (shared with RW).
- B: all-test / all-aperture odd sign (**RH**, Σ1); companion forcing and conductor horizon are
  incompatible for `0 ≤ δ ≤ ½` [L] (no-go for that detector).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH [map].
- A: none.
- B: coefficient cancellation (**RH**, Π).

### RB — Robin / Nicolas
Established: large counterexamples need growing prime(-power) cores; colossally abundant reduction [L].
- A: none.
- B: square-root remainder on primorials (**RH**, Π).

### SRT — square-root threshold / zero visibility
Established: S1 in full; depth-gap visibility (aperture positivity forces deep companions); local
count ⇒ bounded critical multiplicity, not implied by counting or RH, true for density-one heights;
window depth-mass bound for all windows ⇒ zero-free strip; deep zeros `o(V)` and deep windows `o(T)`
centres; off-line local bound ⇒ critical fraction `→ 1`; Steklov full index for `β > 2` [L].
- A: A1, A3; explicit horizons.
- B: B1–B6; tower branch arithmetic index ceiling (**≥qRH**); unattained-depth detection (Σ5).

### ACT — collar transport
Established: explicit collar threshold pays every modulus outside nine atom-dominated moduli [L].
- A: the nine remaining moduli.
- B: one fixed shift paying every profile including exterior primes (Σ1).

### AIP — arithmetic incidence positivity
Established: S1 in full; all-aperture allocation receiver; full Weil index `≤ R + A` [L].
- A: A1, A2; mixed Schur debit on fixed blocks.
- B: all-aperture allocation (**RH**); B2–B6.

### ACS — arithmetic Castelnuovo–Severi
Established [L]: RH ⇔ effectivity ⇔ Hodge index ⇔ section count; Castelnuovo–Severi for rational
scaling correspondences ⇔ RH (RIT); the base theta `h⁰` does not extend; graded strip ⇔ zero width;
atomic branch = S1. `𝔽₃` elliptic curve: Euler product, adelic Haar, idele Haar modulus, radial kernel,
global adelic spectral integral `= ζ_E(u)/ζ_E(u/3)` on `Re s > 1`, simple-root sections equal to the
kernel, Weyl-series absolute convergence on `Re λ₀, Re λ₁ > 1`, affine polynomial cells, rotated
series and constant-term definition.
- A: measure-compatible Bruhat unfolding and constant-term evaluation on the `𝔽₃` loop group; S1 A-items.
- B: characteristic-0 quadratic effectivity (**RH**, Π11); a conformal correspondence over ℤ with factor
  `≠ 1` and bounded self-intersection (**RH**, Γ10); census displacement — projection may erase it
  (Π8); B1–B6.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) ≤ 1` → `κ_ζ = 0` → RH.
Established [L]: `κ(φ_c) = κ_ζ + 1` for every `c > 0`, also glued at any prime and for primitive
Dirichlet L-functions; `κ = κ^{(½)} + κ(Φ|_+)` with zero-blind translation reading `= 1`; on `ℓ = 0`
the form is Weil's dilation form plus shell squares; stable gluing at `0 < s < 1` with exact
absorption of its own pair; simple pole absorbed, double pole charged; Haar successors with
continuous dilation have `κ = ∞`, finite-index Haar kernels split uniquely with punctured limits
exactly the reals `≤ 0`; heat-deformed state `φ_c^{(t)}` source-defined with `κ = N(t)/2 + 1`,
antitone, `1` for `t ≥ 1/8`, RH ⇔ constant, `κ(φ_c) ≤ liminf κ(φ_c^{(t)})`; global pole =
extremal weight, no assembly of local poles at two or more primes has one square; Künneth/Hadamard
branch: RH-equivalent and
all-or-nothing; glued test index selects ζ against finite flips.
- A: A10, A11; A7 (heat calibration).
- B: independent `κ(φ_c) ≤ 1`, equivalently positivity on `v₁^⊥` (**RH**, Σ1); B19 (shell identity of
  the dilation form, **RH**); B20 (prime-local defects, **sub**); B12 on the heat branch (**RH**);
  B10 on the heat branch (**sub**); B7 for the Künneth square (**RH**).

## 3. Candidates and retired branch

| Candidate | Established | A (just work) | B (open) |
|---|---|---|---|
| APF | Fredholm index, cycle-trace reconstruction | — | zero-independent divisor exhaustion (Γ5) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (Γ5) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (Γ/Σ) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (Γ) |
| EGC | pole-safe contour | — | outer expanding-contour sign; raw decay cannot beat the Gamma floor (Σ/Π4) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (Γ5) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (Σ) |
| HJ | Hurwitz residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (Γ5) |
| IRK | rotation-algebra trace / winding | — | arithmetic Poisson / projective lift with integral count (Γ/Π) |
| MSC | Möbius–Sonin | — | bridge to nonnegative Sonin energy (Σ) |
| PCS | singular co-shift | — | source-natural wall annihilation; shift ≠ dilation (Γ) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port; lossless realization needs infinitely many resonances (Σ6) |
| RFHM | support grade; reversible sewing inverse-covariant | — | symmetry-breaking law (Γ) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (Γ5) |
| W1C | finite Lee–Yang + Ising receiver; Vitali obstruction | — | couplings converging to Riemann's measure (Σ6) |
| WBF | genealogy Gram | — | any arithmetic coupling (Γ5) |
| PW-B (retired) | zero-independent source family at every nonreal strip point; optical flux `−16(Re s−½)Im s·M₊M₋`, vanishing iff critical [L] | — | killed as a selector (fails at `s = 3/4 + i`); survivor: half-parameter cusp `Λ(s) = 0` receiver, needs zero-selecting scattering rigidity (**RH**) |

## 4. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ (critical sign) | RW, FU, CFC, RP, PA, TT, LA, TG, HF, CHMD, TH, RN, WD, LI, SZ, EWU, GTA, OWU, SRT, ACT, AIP, HCF, SC; FEL, MSC, EGC, PTR, W1C |
| Π (square-root precision) | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity; IRK |
| Γ (selection) | BAG, XN, PM, MC (typicality), ACS (conformal correspondence); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF; PW-B (retired) |

Within Σ the routes split by the face of the sign problem they meet first: the detection edge of the
complete Weil matrix (HF, SRT, AIP, ACS-atomic, ACT, SC, RW, EWU, OWU), the heat/collision integer
(WD, LA, SC-heat, TG), rank/degree uniformity (TH, HCF, PA, GTA, LA-Jensen), scheduled prime sums
(FU, CFC, RP, SZ, LI, FEL, EGC) and realization (RN, PTR, W1C).
