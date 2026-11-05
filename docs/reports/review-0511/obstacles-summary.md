# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, mechanism classes P1–P5),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (classes C1–C30). Corpus state: `1e8010c5b4`
plus working tree. Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[P]` pipeline-card paper proof;
`[D]` derived here from Lean statements; `[N]` numerical. Windows `[−c, c]` or half-windows `[−c, 0]`;
`w_n = Λ(n)n^{−1/2}`; `H` the archimedean–polar form (prime weights `0`), `P` the arithmetic part, `W = H − P`;
`𝒥` the Lévy energy; `𝒞_m(f) = 𝓗_m(f) − Σ_n w_n(f⋆f)(2m − log n)`; `a*(ζ)` the onset aperture;
`ℋ(c) = {t : H − tP ≥ 0 on [−c, c]}` the arithmetic Hardy interval; `L_T = ½log(T/2π)`;
`a₁ = successorWeilFloorAperture ∈ (0.362, 0.3621)`; `a_∞` the limit of the strictly increasing tower of floor
apertures starting at `a₁`; `log ρ ≈ 0.2812` (plastic number); `Θ = sup Re ρ`; `𝒜(c)` the finite-level Weil cone.

## 1. The big picture

### 1.1 One sign, one number, one inequality
RH ⇔ `a*(ζ) = ⊤` ⇔ `1 ∈ ℋ(c)` for every `c` [L: WVL, FADF]. Weil positivity is a **critical Hardy
inequality**: the arithmetic part `P` must be a Hardy term for the archimedean logarithmic jump operator with
the pole kept, `H ≥ P` on every window. Two halves of "optimal Hardy term" hold unconditionally: the multiple `1`
is the only multiple admissible on every window (scaling optimality, by uniqueness of the Weil cone), and no
Hardy weight survives on odd tests (criticality) [L]. The third half — admissibility on every window — is RH.
`ℋ(c)` is a closed interval, the whole line before the first prime, bounded after it [L]. Known:
`a*(ζ) ≥ a_∞`: floors `(1/20000)/2^k` hold on an infinite strictly increasing tower of apertures starting at `a₁`,
`a₁ − 181/500` positive and below `5×10⁻⁷`; the tower steps shrink like `e^{−C·2^k}`, so `a_∞` is finite and its
value is not identified [L/D].

### 1.2 The certificate format is exact on every window
On every reflection pair `W(f) − |𝒞_m(f)| = ½min(W(G₊), W(G₋))`, the coupling truncating to `2 ≤ n ≤ e^{2c}`
[L: SWC]. The even sector is represented exactly by a window-adapted, line-exact signed theta gauge with zero
pole charge (`2V ≤ J_{M⁺}`), the odd sector by a shifted ground state; nonnegativity of both on every window ⇔ RH
[L]. A window-independent nonsingular even gauge cannot carry nonnegative pole charge [L]. The gauge freedom acts
only in the pole direction: on the pole-neutral hyperplane every neutral gauge represents the even sector by the
raw form `archForm − primeSum`, whatever its pocket position, and receding pockets conserve the ground-state
outside deficit through the exterior jumps [L]. Below `log 5` the window is an exact three-power problem: the
`{2,3,4}` sliver band, with only `n = 2` acting in the half-window diagonal [L]. What is open is the inequality
the format states, not the format.

### 1.3 Frustration cannot be switched away
The even kernel `ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)` is Markov exactly for `c ≤ log ρ`; past it the even
band fails Beurling–Deny at every pole strength and all weights, and is frustrated in every sign gauge [L: SWC,
FADF]. The odd light cone is positive, and each acting prime power adds an anti-diagonal frustrated in every sign
gauge, from `½log 2` on [L]. The logarithmic diagonal forbids cheap nodes: every node of a sign gauge creates a
negative switched conductance next to it [L]. Robust Perron in the pole strength costs height; the arithmetic
pole sits within `O(λ₀)` of the positivity threshold [L]. The trivial zeros are not part of the frustration: they
are mirror mass minus reflected (even) or antireflected (odd) energy, paid by centre killing [L]. What remains to
pay: the constant potential, the pole square (odd), the prime reflections (both).

### 1.4 Size payment is finite; beyond it only sign
The summed edge law `|P_μ(f)| ≤ E_c(μ)𝒥(f)` certifies by size until `E_c = 1`; for ζ the unique crossing is
`c* ∈ (½log 5, ½log 6]` [L]. Size dies before that: `H` itself is negative on a window of half-width `≤ 21/40` (the
weight `w₂ = 0` is inadmissible there), and beyond a finite window one real test makes the prime part strictly
negative for the whole calibration space [L]. Below `log 5` the reflected kicks of `2, 3, 4` together use less
than `0.991` of the Lévy energy [L]. Each entering weight is confined two-sidedly with sharp logarithmic
constants (outer `1`, inner `η/2`), and beyond the sliver both bounds are bounded [L]. The primes pay by sign.

### 1.5 Finite matrices end before `log 6`
Positivity of any correlation form on a window is positivity of all finite rational Hecke graphs of smaller
log-spread [L: WTZ]; finite templates control spreads whose Hecke orbits are finite; at spread `6` the
×2/÷3 orbit in `[1,6)` is infinite, so no finite template exists there [L]. Exact Tate horizons are computed
through `log(81/16)`; positive Tate dimensions form `[0, κ(A)]` with `κ(A) → 0` [L]. The interval
`(log 5, log 6]` is where both the edge-law and the finite-template structure end [D].

### 1.6 The window tower is a de Branges chain until contact
Before contact every window carries a complete Weil Hilbert space realized by entire functions, a de Branges
space with an explicit Hermite–Biehler function, unitary zero-moving, antiunitary conjugation and isometric
inclusions; the Weil symbol is `1 + ½log(1 + ξ²)` minus a bounded convolution, and evaluation vectors are bounded
solutions of a logarithmic Dirichlet equation [L: CSTW]. The symbol factors through a logarithmic Poisson factor:
holomorphic on the slit plane, one simple negative zero, half-line support preserved, its reciprocal the Stieltjes
transform of a positive measure, its causal kernel a positive probability density with normalized renewal mass
[L] — a Wiener–Hopf factorization of the archimedean part [D]. Either RH, or at `a*` a fixed evaluation kernel
diverges monotonically while the contact window stays positive [L]. RH ⇔ the chain never reaches contact [D].
The Hamiltonian of the chain is not constructed.

### 1.7 Identification is complete; reality is the squared gap the camera reads
At aperture `λL_T`: `λ > 1` fixes RvM configurations up to near-collisions, `λ > ½` reads every isolated zero of
ζ with its multiplicity [L: ZCG]. Inside isolated clusters of radius `r ≤ T^{−(M'+κ_λ+1)}` the camera reads the
moments to `N r^{j+1}T^{M'+κ_λ} + e^{−K'log³T}`: centres, squared gaps, discriminants and point locations of
every polynomially small isolated cluster, from finitely many window images, the windows existing per cluster and
built from the configuration near it [L]. For a two-point
cluster `𝓗 = 4(W₁² − W₀W₂)/W₀²` equals the squared gap up to `O(r³P) + O(E)`; on-line pairs give `𝓗 ≈ Δ² ≥ 0`,
FE pairs `𝓗 ≈ −4δ² < 0` [L]. FE-pair squared gaps `≥ 0` at every zero ⇔ RH [L]. Unresolved: clusters of diameter
below `e^{−c log³T}`.

### 1.8 Continuation and finite free stability meet the same floor
`Λ_X ≤ (6600/9991 + ε)/log X`; the Gaussian saddle enters `Re s > 1` exactly at `½/log(X/2π)`; pair models with
Lindelöf size collide below every positive scale [L]. In finite free form: `e^{(t/d²)D²}J_d` is not real-rooted
for any `t > 0` (unboundedly many non-real roots, robust to Bernoulli shifts), while in the shift regime the
Jensen polynomials are asymptotically semicircular [L: FFP]. Normalized Euler factors are Hermite–Biehler stable
with forced drift `θ_S/2`; the ζ side, the Gamma side and pole pieces are unstable for every phase; the
source-faithful Γ ⊠ Θ split never certifies (Θ never real-rooted) [L]. RH ⇔ Möbius-mollified Jensen polynomials
stable at infinitely many degrees ⇔ their roots have bounded imaginary parts along infinitely many degrees;
off RH the imaginary parts grow linearly (`κd`) [L]. Every zero-free half-plane `Re s > σ` is equivalent to
stability of the Jensen polynomials of `ξ(σ + i·)` (strict and unconditional for `σ ≥ 1`), and `R_d(Ξ)` has
unboundedly many real roots (finite free Hardy theorem) [L]. These are receivers.

### 1.9 Every route is a face of the same sign
Exact identifications [L]: the reflection-pair prime-count band ⇔ Weil-lag ⇔ JAS ⇔ CTF ⇔ PBM ⇔ eventual Robin
(SWC); Suzuki first variation = complete Weil energy (SZ); the Cayley ladder = Toeplitz ladder of paired Li
coefficients, RH ⇔ every ladder NSD on primitive vectors ⇔ entrywise `≥ 0`, Hodge index = Metzler sign (ALG
[W]); inner-cap flux = off-line generating function (WD); single-prime stage transport ⇔ RH and Dirichlet-shift head stabilization for every `d` ⇔ RH (HF); two real
parameters `(γ, v)` decide the line (SRT); any nonnegative representation of the Mayer defect ⇔ RH (PM).

### 1.10 PM's second expression has the same sign
`−D_s(ψ_s) = |1 + p^{1−2s}|^{−2}∫_1^∞K_σ|T_{p,s}ψ_s|² = ∫_0^∞K_σ(x+1)|ψ_s(x) − (x+1)^{−2s}ψ_s(x/(x+1))|²`,
`K_σ ∝ (b^{2σ−½} − b^{−(2σ−½)})²`, `K_{1/4} ≡ 0` [L: RIT]. Infinitely many resonances lie on `Re s = ¼`, where
`D = 0` while every norm is positive: no positive multiple of a norm equals `D` [L]. PM's sign is `σ = ¼` in two
coordinate systems.

### 1.11 Visibility and the vacuity of short windows
`k·pairEnergy(δ,a) ≤ L` in lattice backgrounds, also for distinct clusters near one ordinate; unshielded clusters
excluded to doubly-exponential height; tapered crystals hide depth `1/a` above `e^{ca}`; doubly-exponential
non-locality [L: WVL]. For ζ the laws require positivity, known only to `a_∞` (≈ 0.362), where they are vacuous;
zero information starts at half-width `4` and, with present constants, `≈ 20` [D]. The effective form: positivity
at level `a` confines every zero with `|γ| ≥ 102` to `|β − ½| < 10⁶exp(−a/(480000 log(|γ|+3)))`, from the
unconditional local count `N(t, t+1] ≤ 240 log(|t|+3)` [L].

### 1.12 Criticality everywhere
Every exact reading sits on a zero-slack boundary: Weil cone a point; only the multiple `1` admissible; no Hardy
weight; lattices Szegő singular; reflection coefficients at `±1`; Perron exactly to `log ρ`; kernel blow-up at
contact; heat size horizon at the saddle; Gaussian finite free capacity `o(d⁻²)`; Euler drift exactly `θ_S/2`; PM
defect zero only at `σ = ¼`; numerical margins `10⁻⁴`–`10⁻¹²`, with free weights gaining a factor below `500` at the
computed windows (1.15) [L/N]. A proof must be an identity at the boundary
[D].

### 1.13 What is ruled out
| Mechanism | Verdict | Anchor |
|---|---|---|
| Markov / Perron certificates past `e^{−3/4}` / `log ρ` | refuted at every pole strength and weight | SWC [L] |
| Balancing by sign gauges (switching) | refuted: even past `log ρ`, odd from `½log 2` | FADF [L] |
| Size-only payment of the primes | dies before `21/40` (`H < 0`); edge law at `c* ∈ (½log5, ½log6]` | FADF, SWC [L] |
| Certificates without pole variance; window-independent even gauges | refuted | SWC [L] |
| Point-value certificates | Weil's form reads no point values | FADF [L] |
| Uncoupled stage loans; orthogonal twisted repair of untwisted modes | refuted at `21/20`; `O(1/K)`, refuted above an explicit critical multiple | AHD [L] |
| Non-orthogonal (Dirichlet-shift) repair of long windows | cancels every tail; leaves the head window `R₁(log d)` | AHD [L] |
| Gauge optimization off the pole direction | the representation is gauge-independent on the pole-neutral hyperplane | SWC [L] |
| Finite-template reduction at spread 6 | infinite Hecke orbit | WTZ [L] |
| Source-faithful finite free split; Dirichlet, ζ-side, Gamma, pole pieces | never real-rooted / unstable | FFP [L] |
| Degree-3 semicircle-free test | every real-rooted cubic passes | FFP [L] |
| Nonnegative multiple of PM norms as the defect | refuted on critical resonances | RIT [L] |
| Counts / Tate / Hodge index from counts | closed [D] | S3 |
| Height-local decision; universal density thresholds; domination as selector; size-only heat repair | refuted | WVL, ZCG [L] |
| Fixed / untruncated / truncated quartic theta cross-loads | fail at scales 6 and 8 / 32 / 6 | TCS [L] |
| Any finite-aperture certificate as a decision of RH | every bounded aperture is blind to every width; a property determined by a finite window implies the count for no weight | SRT, ArithmeticOfSquareRootPrecision [L] |
| Hadamard and tensor amplification | every power `K_ζ^n` carries RH | RIT [L] |
| Slack from other weights | free weights gain a factor below `500` for `c ≤ 0.66`; the cone is `{Λ}` or empty | RHTower [L]; 1.15 [N] |
| Integrality as a source of purity | `collide_or_repel` assumes the disc bound | ZCG [L] |

### 1.14 The live mechanism classes
| Class | Statement | First open test | Status |
|---|---|---|---|
| P1 signed criticality | `H ≥ P` on every window in the exact two-sector format, frustration unswitchable | `a*(ζ) ≥ ½` (odd unit window, margin `≈ 2×10⁻⁴`); `a*(ζ) ≥ log 2` (two weights) | live |
| P2 calibration | the arithmetic point inside every finite-level cone `𝒜(c)` | widths of `𝒜(c)` for `c ≤ ½log 6` | live |
| P3 PM reflection | a nonnegative expression of the defect without the `(b^{2σ−½} − b^{−(2σ−½)})²` factor | a PM-native zero-free region | reduced to `σ = ¼` |
| P4 square-root cancellation | the band in prime form; Li positivity; inner caps | — | live; classical |
| P5 continuation / stability | no collision below `½/log X`; finite free stability at infinitely many degrees | an Euler-product input inside the strip | live as a receiver |

### 1.15 What a finite window can and cannot decide
- **RH is an existence statement at finite levels.** RH ⇔ for every aperture `A` some real weights, of any sign and
  growth, make `H − P_λ ≥ 0` on `[−A, A]`; only `Γ`, the pole and the positions `log n` enter
  (`riemannHypothesis_iff_forall_level_exists_weilPositiveFullUpTo`). The Weil cone is `{Λ}` under RH and empty
  otherwise, with no hypothesis on `λ` or ζ (`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`, through the
  twisted arc minimum principle) [L: RHTower].
- **Every bounded aperture is blind to every width.** For every `a` and `δ ∈ (0, ½]` the off-line lattice
  `{½ ± δ + πik/a}` has width `δ` and a nonnegative form at aperture `a`, there literally the form of an on-line
  configuration. A certificate at a finite aperture, however large, is consistent with every width; the negativity
  rate along the lag family is the width [L: SRT `TheZeroWidthIsAnUnboundedApertureProperty`].
- **Deciding inputs.** A property of weights implying the count `ψ(x) − x = O(√x log²x)` (for `Λ`: RH) is
  parity-breaking, precision-faithful against `εn^{−η}`, `0 ≤ η < ½`, of unbounded aperture, with stabilizer in the
  square-root class. PNT, Guth–Maynard and every error law weaker than square root are inherited by weights failing
  the count [L: ArithmeticOfSquareRootPrecision].
- **The cone pins its coordinates while its margin collapses [N].**

| `c` | weights seen | margin of `Λ` | best margin over all weights | band width of `λ(2)` | band width of `λ(3)` |
|---|---|---|---|---|---|
| `0.40` | `2` | `1.8×10⁻⁴` | `6.1×10⁻⁴` | `0.19` | — |
| `0.45` | `2` | `1.6×10⁻⁵` | `1.4×10⁻⁴` | `1.5×10⁻²` | — |
| `0.50` | `2` | `9.4×10⁻⁷` | `1.4×10⁻⁵` | `8.9×10⁻⁴` | — |
| `½log 3` | `2` | `5.6×10⁻⁸` | `1.3×10⁻⁶` | `5.8×10⁻⁵` | — |
| `0.58` | `2, 3` | `6.9×10⁻⁹` | `5.0×10⁻⁷` | `2.4×10⁻⁵` | `0.17` |
| `0.62` | `2, 3` | `4.0×10⁻¹⁰` | `6.7×10⁻⁸` | `3.0×10⁻⁶` | `4.2×10⁻³` |
| `0.66` | `2, 3` | `1.6×10⁻¹¹` | `7.7×10⁻⁹` | `5.4×10⁻⁷` | `2.4×10⁻⁴` |

  Galerkin on Legendre polynomials of degree `< 36`, double precision; degree `< 48` agrees to `3%` at `c = 0.66`; the
  corpus margin `5.6×10⁻⁸` at `½log 3` is reproduced. Bands are outer approximations, since tests are restricted to the
  Galerkin space. Not formalized. Free weights gain a factor of `3` to `500`, and the collapse stays. With no prime
  input, positivity on `[−0.66, 0.66]` confines `λ(2)` to a band of width `5×10⁻⁷` containing `log 2` and `λ(3)` to width
  `2×10⁻⁴` containing `log 3`; `Λ(2)` sits near the upper edge (upper slack `2.5×10⁻⁸`, lower `5×10⁻⁷`). A proof at these
  windows certifies `log 2` to that precision, so approximate input does not suffice.

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit constants and horizons (`K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, `M(N) = o(c_N)`) | HF, SRT, AIP, ACS, SC | effectivization of proved limits |
| A2 | General profiles past `θ = 1/1080` | HF, SRT, SC | tilted-spline template |
| A3 | Joint twist families across different moduli | HF, SRT, AHD | parity grading and `L`-value coupling within one modulus proved |
| A4 | Certified ratio interval at its size-only optimum; receiving complement inside it | HF, AIP, SRT, CSAR | assembly of proved estimates (difficulty unverified) |
| A5 | Rigorous computer-assisted certificate of the two-weight membership on `(0.3621, log 2)`, odd unit window first | RW, OWU, EWU, ACT, SWC, HF | operator inequality with explicit kernels; margins `2×10⁻⁴` (odd unit), `1.5×10⁻⁵`, `5.6×10⁻⁸`, `≈ 10⁻¹²` at `log 2` [N]; decides cases, not the mechanism; no zero information; opens nothing (2.8) |
| A6 | Exact Tate horizons of the remaining stages below spread `6` | WTZ, CWS | finite templates exist there |
| A7 | Closed form of the first-stage complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit Schur complement |
| A9 | Literal channel norms critically small with growing periods, offsets, prime bands | AIP | proved sieve inputs (difficulty unverified) |
| A11 | Function-field calibration of the remaining receivers (ladders, Hardy intervals, de Branges chains of curves) | AHD, ACS, SC, HF | the sign is known there |
| A13 | Widths of the finite-level cones `𝒜(c)` | PBAP, ACS, RW, FADF | convex finite programs; entry bounds proved; computed to `c = 0.66` (1.15) [N] |
| A14 | PM classical identifications; mixed-parameter completion; Mayer transfer compatibility; boundary carrier; rational Weyl identification | PM, W1C | known theories |
| A15 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A17 | Theta fifth even section on `π ≤ q < 7` with an entry-preserving compensation other than the quartic (which fails at scale 6); then rank 9 | TH | compact finite-dimensional sign with exact capacities (difficulty unverified) |
| A18 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | effectivization |
| A19 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` where the pole pays nowhere | ACT | finite case analysis |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A21 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A23 | Depth law, star horizons, gcd strata | HF, ACS | effectivization |
| A24 | Census items; Voronoi; Zwegers | census, ACS, HF | classical |
| A25 | Künneth primitive `h¹` at small degree; mixed jets | ACS, WL | calibration |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | WTZ, HF | classical |
| A31 | Selberg-class degree-one classification | ACS, SEL | known theorem |
| A33 | Lévy sector margins at `c = ½log 3` | RW, OWU, EWU, SWC | numerical |
| A35 | Sharpen the explicit constants (`2²⁶·960`; detector `480000`, `10⁶`, count `240`) toward `4δL/k` | WVL, every P1 route | explicit test functions and counts in place |
| A36 | Remaining onset-law items (general shallow depth-mass bound under positivity; tapered crystal to `a ≍ log T`; interferometer) | WVL | paper items |
| A38 | Sub-Weyl strip profile from the best exponent pairs (horizon toward `½`) | LA, ZCG | known subconvexity; decides nothing about zeros |
| A39 | Sharp zero location: compose the negative test on the form (`exists_window_re_W_neg`, `not_hodgeIndex_below_nyquist_horizon`) with the camera's isolating windows at `a = λL_T`, `λ > 1`, tails to `e^{−c log³T}` | WVL, ZCG, SRT | test and windows exist; no on-line mimic needed; a receiver, vacuous at known apertures |
| A40 | Camera with real weights and Beurling–Selberg transfer of local counts to mimics | ZCG, SRT | the moment readout is linear in the weights; not needed for A39 |
| A41 | Hamiltonian of the precontact de Branges chain (de Branges ordering theorem), contact as its first singular length | RW, CSTW, SZ | classical theorem applied to a constructed chain; its regularity is B51 (RH), so it opens nothing |
| A42 | Effective `T₀` in the camera theorems | ZCG | constants |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window (≡ `1 ∈ ℋ(c)` ∀c ≡ band on reflection pairs ≡ growth steps contractions ≡ Li positivity ≡ Suzuki first variation ≡ two-parameter two-bump family) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every stage (≡ single-prime stage transport) | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF |
| B3 | The two-sector signed certificate inequalities on every window (`2V ≤ J_{M⁺}`; odd shifted-ground-state form) | RH; fixed length sub | P1 routes |
| B4 | Odd unit window (`w₂ ∈ unitBandWeights`) by a structural certificate | sub; finite window | OWU, RW, TT, SWC |
| B5 | Below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub; finite window, no door (2.8) | RW, OWU, EWU, ACT, TT, SWC, HF, ACS |
| B56 | Below `log 5` (`a*(ζ) ≥ ½log 5`): the `{2,3,4}` sliver band | sub; finite window | same as B5 |
| B6 | Twisted-sector positivity through all conductors and frequencies | sub | HF, SRT, AIP, AHD |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH all | HF, SRT, AIP, CSAR |
| B8 | General profiles past `log log N` on the full space | sub | HF, SRT, AIP, SC |
| B9 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT, GWZ |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, CWS, SRT |
| B14 | Collision exclusion below `½/log X` (≡ `Λ_X = 0` ∀X) | RH | TH, LA, HCF, PA, GTA, XN, ZCG |
| B15 | Scheduled prime energies bounded below (FU, CFC, RP, EGC, FEL) | RH | FU, CFC, RP, EGC, FEL |
| B16 | Window negativity exponent `< ½` | ≥qRH | window routes, HF, WD |
| B33 | HF-native sign: a window beyond the base certified by the complete family itself (`R₁(A) = ⊤ ⇔ A/2 ≤ a*`: the qualifier has no content) | sub; finite window | HF |
| B55 | Head-window thresholds `R₁(log d) = ⊤` for every `d` (residue of Dirichlet-shift stabilization) | RH | HF, AHD |
| B49 | Signed ground-state structure past `log ρ` compatible with unswitchable frustration | method | EWU, OWU, RW, ACT, SWC, FADF |
| B51 | No finite contact of the Weil de Branges chain (≡ regular Hamiltonian at every length) | RH | RW, CSTW, SZ |
| B58 | Effective uniqueness of the Weil cone: explicit `ε(n, c) → 0` with `|λ(n) − Λ(n)| ≤ ε(n, c)` on `𝒜(c)` | sub | PBAP, FADF |
| B59 | Margin law: decay of `max_λ λ_min(W_λ|[−c,c])` and of the band widths | sub | PBAP, FADF, RW |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B19 | Inner caps at every polynomial stage (≡ the off-line generating function is `L²(e^{−xt})` at every stage) | RH; fixed degree ≥qRH | WD, TG |
| B20 | `100%` critical-scale clustering | sub | WD, census, MC, HEF |
| B21 | `D_win` ≡ thin Planck shadows; `D_zero` | sub | WD, census |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH | WD |
| B23 | Distributional input beyond counts and moments | method | WD, HEF |
| B24 | Genus upper law | indep. | ACS |
| B25 | Logarithmic Serre duality, primitive part | sub | ACS, HF |
| B26 | `ε`-uniform producer; square-root source input | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B27 | First cyclotomic mode at square-root precision | RH | MC, WL |
| B28 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B29 | First Epstein real zero on the boost line | sub | ACS |
| B30 | Bounded damped cone coupling; unattained width | RH | SC, ACS |
| B31 | Finite-sieve Hodge positivity → global | RH | SC |
| B32 | Half-power law at the trivial gauge point | RH | MC, WL |
| B52 | Möbius-mollified Jensen stability at infinitely many degrees | RH | LA, FFP |
| B53 | A source-faithful stable finite free factorization of `J^{d,n}` other than Γ ⊠ Θ | method | FFP, TH |
| B57 | Self-improvement of a strip: `Θ < 1 ⇒ Θ = ½` (no mechanism; Hadamard and tensor powers carry RH) | sub | whole programme |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, GWZ, PM |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B36 | Selection at the trivial gauge point | RH | MC, BAG |
| B37 | FE twins inside the full class with off-line zeros | sub | HF, ACS, SC, SEL |
| B38 | A nonnegative expression of `D_s(ψ_s)` without the factor `(b^{2σ−½} − b^{−(2σ−½)})²` | RH | PM, W1C |
| B39 | Resonant-state statistic selecting the decay rate | method | PM |
| B40 | Source-faithful realization of unbounded rank | RH | RN, PTR, W1C, PM |
| B41 | Pre-divisor forcing | RH | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| B42 | Prime-blind positivity on signed blind combinations | RH | PBAP |
| B44 | `𝓗 ≥ 0` on every isolated near-coincident cluster of ζ (the squared gap, read at windows built from the cluster) | RH | ZCG, LA |
| B45 | Cross-tower gap through the archimedean channel | method | HF, AIP |
| B46 | PM-native zero-free region for `ζ(2s)` (route test: `β < 1 − c/log|γ|` reproves a classical region from the carrier alone) | sub | PM |
| B54 | Repulsion of distinct zeros of ζ at polynomial scale (open under RH; no implication for real parts; no route depends on it) | indep. | — |

### Settled questions (status-quo answers)
| Question | Answer | Anchor |
|---|---|---|
| Is Weil positivity a Hardy inequality? | yes: `H ≥ P` on every window; only the multiple `1` admissible; critical; optimal ⇔ RH | FADF [L] |
| Can frustration be switched away? | no: even past `log ρ`, odd from `½log 2`, every gauge | FADF [L] |
| Where does size payment end? | before half-width `21/40` (`H < 0`); edge law at `c* ∈ (½log5, ½log6]` | FADF, SWC [L] |
| Is the certificate format exact on every window? | yes: neutral signed theta gauge (even), shifted ground state (odd) | SWC [L] |
| What do the trivial zeros cost? | nothing: centre killing pays them mode by mode | FADF [L] |
| What boundary data can a certificate see? | `Ω`-weighted edge masses; no point values | FADF [L] |
| Is the window tower a canonical system? | a de Branges chain before contact; kernel blow-up at contact | CSTW [L] |
| Does window positivity reduce to finite matrices? | for correlation forms yes, via rational Hecke graphs; finite templates end at spread 6 | WTZ [L] |
| Can the camera read squared gaps at polynomial scale? | yes, from three prime-side images, error `O(r³T^{M'+κ}) + e^{−c log³T}` | ZCG [L] |
| Is reality at near-coincidences RH? | yes: FE-pair squared gaps `≥ 0` ⇔ RH | ZCG [L] |
| Does finite free probability certify Jensen polynomials? | no source-faithful split certifies; Gaussian capacity `o(d⁻²)`; Euler side stable, ζ/Gamma/pole unstable | FFP [L] |
| Does PM's second expression change the sign? | no: same `(b^{2σ−½} − b^{−(2σ−½)})²` factor | RIT [L] |
| What is WD's inner cap? | the generating function of the off-line zeros | CDG [L] |
| Are SZ and LI independent of Weil positivity? | no: Suzuki first variation = Weil energy; Cayley ladder = Li coefficients | RHTower, ALG [L/W] |
| Does HF transport one prime? | single-prime transport for all `A` ⇔ RH; unconditional across `p = 2` at `A₀` | AHD [L] |
| Can non-orthogonal twists repair untwisted negativity? | Dirichlet shifts couple at `O(1)`, cancel tails, leave the head `R₁(log d)` | AHD [L] |
| Does gauge optimization help? | only in the pole direction; the pole-neutral hyperplane is gauge-invariant | SWC [L] |
| How far is the window problem exact and finite? | below `log 5`: the `{2,3,4}` sliver band | SWC [L] |
| Is the excluded-depth law effective? | yes: `10⁶exp(−a/(480000 log(|γ|+3)))` | SquareRootThreshold [L] |
| Does a finite window decide anything about the width? | no: every bounded aperture is blind to every width | SRT [L] |
| Do other weights give slack? | no: the cone is `{Λ}` or empty; the gain is below `500` for `c ≤ 0.66` | RHTower [L]; 1.15 [N] |
| Is purity over `𝔽_q` a deformation argument? | no: `collide_or_repel` assumes the disc bound; the proofs use a sign or a count | ZCG [L] |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every assembly ends at the same sign, read in one of its coordinate systems
(Hardy inequality, prime count, squared gap, Krein form, Hamiltonian regularity). No assembly supplies a sign or an
input. F6 sharpens the constant of an existing location theorem; F7 restates the global sign as a scalar bound of RH
strength.

### F1. The gauge–tower assembly (P1)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ `1 ∈ ℋ(c)` ∀c ⇔ reflection pairs ⇔ two sectors | WVL, FADF, SWC | [L] |
| Exact two-sector format on every window; gauge freedom only in the pole direction | SWC | [L] |
| Floors to `a_∞` on windows and reflection pairs; exact `{2,3,4}` problem below `log 5` | AIP, SWC | [L] |
| Perron to `log ρ`; trivial zeros at the centre; entry law | SWC, FADF | [L] |
| Core: `2V ≤ J_{M⁺}` and the odd ground-state inequality on every window | — | B3; first instances B4, B5 |

### F2. Hardy induction (FADF ⊕ AHD ⊕ CSTW)
`1 ∈ ℋ(c)` is antitone; composite stages carry no fold; each prime-power entry is a compact interval in the newest
weight with sharp logarithmic softness; single-prime transport for all `A` ⇔ RH [L]. Residual: a margin at every
entry. Criticality forbids uniform margins (no Hardy weight; margins doubly-exponentially small), and the
first-fold stage loan fails at `21/20` [L]: the step must be an identity at zero slack, paid by the signed fold.
B2.

### F3. The complete-family assembly = the onset aperture
Subcritical PD + one critical multiple across all entries + threshold law + terminal polar source + receiving
charges [L]; orthogonal twists cannot repair untwisted modes [L]; Dirichlet-shift companions cancel every tail and
reduce each long window to its head `R₁(log d)` (unconditional for `d = 2`) [L]. Certifies exactly what the base
certifies. Residual: B55 (heads for every `d`), B33, B1.

### F4. The reflection assembly (P3)
Krein–Lax–Phillips space + window lift + defect formula in two coordinate systems [L]. Residual: B38; both
expressions carry `(b^{2σ−½} − b^{−(2σ−½)})²`.

### F5. The camera–continuation assembly (ZCG ⊕ heat)
| Segment | Supplied by | Status |
|---|---|---|
| Heat path real for `t ≥ 1/8`; RH ⇔ `Λ_X = 0` ∀X | RHTower | [L] |
| No collision above `(6600/9991 + ε)/log X`; saddle `½/log X` | ZCG | [L] |
| Collisions are near-coincidences; identification to `e^{−c log³T}`; `𝓗` reads `w²` at polynomial scale | ZCG | [L] |
| Core: `𝓗 ≥ 0` on every near-coincidence (≡ no collision below `½/log X`) | — | B44 = B14 |

### F6. The sharp location assembly (SRT ⊕ RHTower ⊕ ZCG)
| Segment | Supplied by | Status |
|---|---|---|
| An isolated off-line point makes the form negative on `f_A + cf_B`; positivity certifies what windows isolate | SRT | [L] |
| Positivity at `a ≥ 4((n + 1)log(10⁶/δ) + log(A₀(|γ| + 3)))` excludes depth `δ`, `n` the window count | RHTower | [L] |
| Isolating windows at `λL_T`, floors to `e^{−c log³T}` | ZCG | [L] |
| Composition at `a = λL_T`, `λ > 1`, with tail control | — | A39 |

Output [D]: positivity at `a` ⇒ every off-line zero at height `T ≤ 2πe^{2a/λ}` (`T ≥ T₀`) has depth `≤ e^{−c log³T}`. No
on-line mimic or Krein extension is needed: the test acts on the form directly. A receiver: it produces no sign and
is vacuous at known apertures. The converse (RH below `T` ⇒ positivity at `½log T`) is blocked by doubly-exponential
non-locality, so height induction stays closed.

### F7. The canonical-system assembly (CSTW ⊕ GWZ ⊕ SWC)
De Branges chain before contact + lattice Levinson recursion + continuum jet limits + parity split [L] +
Hamiltonian (A41). Output: RH ⇔ the evaluation kernels `K_a(z₀, z₀) = ∫_0^a⟨H(t)Y(t,z₀), Y(t,z₀)⟩dt` stay
bounded on bounded aperture intervals at every `z₀` of one set of uniqueness [D]. Residual: B51, RH-strength; the bound is
a coercivity `W(f) ≥ c|f̂(z₀)|²`, stronger than the sign on each test.

### F8. Finite free ⊕ Euler carriers (FFP ⊕ ZCG)
Normalized Euler products HB-stable with drift `θ_S/2` ≡ the carrier horizon `2πe^{θ_S}`; curved Gamma phase
supplies drift `θ'(t)` up to degree `≈ (θ'(t) − θ_S/2)²/θ''(t)` [L]. Residual: the same domination is shared by
every finite real carrier and twins are tilted at every height [L]: no ζ selection; the mollified criterion is a
receiver (B52).

### F9. Finite Hecke graphs ⊕ numerics (WTZ ⊕ A5)
Correlation-form windows are finite matrices below spread 6 [L]; certify `a*` numerically there. Residual: Weil's
form carries the archimedean Lévy part, not a correlation form; margins `10⁻⁵`–`10⁻⁸`; windows below half-width 4
carry no zero information.

### F10. Visibility–density (WVL ⊕ WD ⊕ DCI)
Unshielded clusters excluded to doubly-exponential height; shallow depth mass bounded; inner caps = off-line
generating function [L]. Residual: B1 at growing aperture and B21 (log-free occupancy).

## 2.4 A wildly different route

**Verdict: none.** Every route reads ζ's zeros through the explicit formula or through a function with ζ's divisor;
the three walls are the three components of that formula. Finite free probability, the farthest mechanism inside
the corpus, is worked out [L: FFP]: it meets P5 exactly (Gaussian capacity `o(d⁻²)` is de Bruijn–Newman criticality;
Szegő never applies to the source split; only the Möbius Euler side is stable). The corpus covers positivity,
precision, realization, deformation, recurrence, counts, function-field transfer, quasicrystals, Lee–Yang, moment
problems, Hermite–Biehler phases, finite free stability, visibility, identification, Bost–Connes, Deninger, Connes
trace formulas and Selberg/Maass traces.

**Integrality is not a route.** Over `𝔽_q` the proofs of purity use a sign or a count: Weil's Hodge index,
Stepanov–Bombieri's point count, Deligne's positivity on tensor powers. `collide_or_repel` [L: ZCG] takes the bound
`|z| ≤ 2√q` on all roots as a hypothesis, which is purity, and then bounds separations by a resultant. Integer
polynomials do not deform continuously, so "pure member + continuity + integrality" is no proof of purity and
there is nothing to transfer to ζ.

**Tensor amplification is closed.** Deligne's step from a fixed loss to purity has no analogue on Weil's kernel:
every Hadamard power `K_ζ^n` is positive definite iff RH, and a finite index at degree two already gives finitely
many off-line zeros [L: RIT `TheHadamardPowersOfWeilsKernel`].

**Absent from the corpus and far:** homogeneous dynamics (Zagier–Sarnak rate of closed-horocycle equidistribution
`≍ y^{3/4−ε}` ⇔ RH; its error term has poles at `ζ(2s) = 0`, the Mayer resonances, so it meets Γ24); asymptotically
exact towers of global fields (limit zeta functions; distributional, blind to single zeros, meets Σ26); the
Biane–Pitman–Yor Brownian representation of `ξ` (meets P5 through the Lee–Yang/Newman class). Each restates a wall.

## 2.5 Breakthrough questions below RH and quasi-RH

### Validity tests

A question stands in 2.5, 2.6 or 2.8 only if it passes these tests.

| Test | Requirement | Anchor |
|---|---|---|
| T1 Not RH | Not equivalent to RH. In 2.5 also: implied by RH, and not implying quasi-RH | equivalence web |
| T2 Decision | Answered only by a proof or a refutation of the stated inequality. Identity + obstruction + equivalence with RH is no answer | — |
| T3 Written consequence | YES ⇒ a named statement, by an argument that can be written down. "Template", "first instance", "one object", "becomes" do not count | — |
| T4 Aperture | Anything claimed to lead to RH is not determined by a finite window | `not_of_finite_window`, `exists_configWidth_eq_and_weil_nonneg_on_aperture` [L] |
| T5 Mimics | False on at least one corpus fake: off-line lattices, Liouville twin, `Λ + εn^{−η}`, Davenport–Heilbronn, `ζ(s)ζ(s−ε)`. A statement true on all of them carries no arithmetic | `deciding_input_necessary_properties` [L] |
| T6 Mechanism | Names an input not refuted by a Lean no-go. A method clause naming an exact format has no content, since every positive form has that format | — |
| T7 Shape | Not a shape answered in Lean without moving a wall (table below) | — |

| Shape | Lean output | Walls moved |
|---|---|---|
| Construct the object whose regularity is RH | de Branges chain, contact blow-up (CSTW) | none: B51 is RH |
| Express the sign in another coordinate | two `K_σ` expressions (RIT); exact gauges (SWC); inner cap = off-line generating function (CDG); `𝓗` = squared gap (ZCG) | none |
| Read a quantity at a finer scale | polynomial-scale readout (ZCG) | none: B44 is RH |
| Transport across one step | `stageTransport_across_prime_iff_riemannHypothesis`: induction on `k·log p` for an antitone threshold (AHD) | none |
| First window beyond a base | floor tower to `a_∞` (AIP) | none: no zero information below half-width `4` |
| Second expression + "any nonnegative one is RH" | `mayerDefect_nonneg_representation_iff`: `D_s ≤ 0` always (RIT) | none |

Every question answered in Lean was answerable from inputs already in the corpus, so its answer contains no
producer. The questions that stay open (`D_win`, windows past `a_∞`) need an input the corpus does not have [D].

**Audit of the question forms that fail.**

| Question form | Fails | Reason |
|---|---|---|
| Sign ⇒ location at `a = λL_T` via Krein mimics | T3 as a breakthrough | True in form and a receiver: a direct negative test on the form suffices (A39), no sign is produced, vacuous at known apertures |
| Mayer defect size law with corridor `|σ − ¼| < c/log|Im s|` | T1, T6 | The corridor implies `Θ = ½`, so it is above quasi-RH; the three-term and Hecke relations give `K_σ`-weighted equalities, not an upper bound |
| `R₁ = ⊤` through stage 2 and `log 3` "from the complete family" | T4, T6 | `R₁(A) = ⊤ ⇔ A/2 ≤ a*`, so the method clause is empty; a finite window seeing one or two numbers |
| Collide or repel for ζ (`|ρ − ρ'| ≥ T^{−C}`) | T1, T3 | Not implied by RH (open under RH); FE pairs may be well separated, so no location follows; its model theorem assumes the disc bound |
| Kernel bound on a set of uniqueness | T1, T6 | RH (Σ66); `W(f) ≥ c|f̂(z₀)|²` is stronger than the sign on each test, not free of it |
| Nonnegative expression of `D_s(ψ_s)` | T1, T2, T7 | `D_s ≤ 0` always, so such an expression is the statement `D_s = 0` |
| Off-line generating function in `L²(e^{−xt})` | T1, T2 | Integrability at every `x` says the off-line set is empty (`innerCap_allExponents_iff_offLineZeros_empty`) |
| Single-prime transport; head thresholds for every `d` | T1, T7 | Induction on an antitone threshold; `R₁(log d) = ⊤` ∀d is `a* = ⊤` |
| Head recursion over divisors | T1 | At prime `d` the only proper divisor is `1`, so its base case is `R₁(log p) = ⊤` ∀p, which is RH |
| `𝓗 ≥ −B` on isolated clusters | T1, T6 | `𝓗` is the squared gap by theorem; `pair_hankel_rvm` gives windows per cluster, built from the configuration, so it is no statement about explicit prime sums |
| `a*(ζ) ≥ log 2` as a door | T4, T5, T6 | 2.8 |
| Replacement for Allegretto–Piepenbrink; SOS identity on the pole-neutral hyperplane; signed ground state balanced after Kron reduction | T2, T6 | A positive form has an exact certificate by definition; no class of forms is named on which a criterion could differ from `λ_min ≥ 0` |
| Arithmetic part as an optimal Hardy weight | T1 | `question_one`: iff RH [L] |
| Gauge family carrying the pole without leakage | T7 | Freedom only at the pole; pockets conserve the deficit [L] |
| First-passage representation; scale-doubling map | T2, T3 | No statement that could be refuted |
| Stability preserver containing Euler factors and the Gamma phase | T3, T6 | The Euler product diverges in the strip, so no factorization of `Ξ` exists to preserve; ζ, Gamma and pole pieces are unstable [L] |
| Deformation from a pure object with integral structure | T3, T6 | 2.4 |

The sections below keep only what passes.

### 2.5.1 Whole programme — `100%` critical-scale clustering
**Question.** Prove `T⁻¹∫_T^{2T} log|ζ(½ + it)| dt → 0`; equivalently, for every `κ > 0`, all but `o(T log T)` zeros
in `(T, 2T]` lie within `κ/log T` of the line. Eight forms are equivalent, among them the truncated Euler-mollified
log mean, the linear-mollifier law and the dyadic horizontal moment `o(T)` [L:
`criticalClustering_logMean_mollifier_hecke_tfae`] (B20).
- **T1.** Implied by RH; allows sparse off-line zeros at every depth, so it implies neither RH nor quasi-RH.
- **T2.** Selberg's tail moment gives `Σ(β − ½) ≪ T` [L]; the question is `o(T)`, and no identity delivers it.
- **T3.** `Σ_{T<γ≤2T}(β − ½) = o(T)`: RH on average at the mean-spacing scale.
- **T5.** False for Davenport–Heilbronn, off-line lattices of bounded spacing and `ζ(s)ζ(s−ε)`: a proof must use
  the Euler product inside the strip.
- **T6.** By Jensen and Littlewood it follows from a mollifier with second moment `→ 1`, which requires length
  exponent `θ → ∞` [D]; mean values stop far below that: this is the Π wall.
- **Limit.** No door to RH: the sparse exceptions survive it.

### 2.5.2 Route PM — none
No breakthrough question passes. The defect relations are equalities with the same `K_σ`; a corridor at scale
`1/log|Im s|` is above quasi-RH. The valid item is a route test, not a breakthrough: B46, a zero-free region
`β < 1 − c/log|γ|` from the Lewis–Hecke carrier alone. It reproves a classical theorem; failure would show that the
carrier holds no arithmetic beyond identification. Risk: its positivity is the Euler product (A15).

### 2.5.3 Route WD — log-free window occupancy
**Question.** `D_win`: for every `A`, at most `ε(A)V` unit windows of `[V, 2V]` contain a zero of depth `≥ A/log V`,
`ε(A) → 0` [statement in Lean: CDG] (B21).
- **T1.** Implied by RH; sparse windows stay free, so no quasi-RH.
- **T2, T5.** A decision, false for Davenport–Heilbronn and `ζ(s)ζ(s−ε)`.
- **T3.** `D_zero ⇔ D_win` + vanishing giant-cluster tails, and `D_zero ⇒ D_win ∧` (2.5.1) [L]; `D_win ⇔` thin Planck
  shadows are rare [L].
- **T6 fails.** The Planck-scale and double-log forms are proved; `sparseModel` satisfies the uniform Planck bound
  and violates occupancy, `clusteredModel` makes the `(log V)²` factor unimprovable [L]. No input is named.
- **Limit.** Valid, open, no mechanism, no door.

### 2.5.4 Route HF — none
`R₁(A) = ⊤ ⇔ A/2 ≤ a*`, so an HF statement about a window is a window statement and "HF-native" adds no content
(B33). Finite windows are A5.

### 2.5.5 Route ZCG — none
What remains on ZCG is identification: A39 (sharp location, a receiver), A42 (effective `T₀`), and the sharp
mixed-depth threshold in `[5π/(6g), π/g]`, a valid question with no bearing on the sign.

## 2.6 Breakthrough questions that open the path to RH

**Verdict: no question passes.** A question opens the path only if `RH ⇔ Q ∧ R` with `Q`, `R` both strictly weaker
than RH and at least one of them reachable. Splitting counterexamples by depth or density always gives such a
factorization, so the content lies in a mechanism for one factor. The joint input must be parity-breaking,
precision-faithful and of unbounded aperture (`deciding_input_necessary_properties`); PNT, Guth–Maynard and every
error law weaker than square root are inherited by weights failing the count (`producers_are_precision_blind`,
`errorLaw_cannot_decide`) [L]. So a door has to name an unconditional input at square-root precision. The corpus has
none, and no question below names one.

### 2.6.1 Whole programme — none; the one door-shaped statement has no mechanism
**Statement (B57).** Self-improvement: `Θ < 1 ⇒ Θ = ½`, `Θ = sup Re ρ`. Then `RH ⇔ (Θ < 1) ∧` B57 [D], and B57 holds
vacuously if `Θ = 1`.
- **Passes T1–T5.** Not RH; a decision; written consequence; `Θ` is an unbounded-aperture property [L]; false for
  off-line lattices, and its analogue is false for `ζ(s)ζ(s−ε)` (Euler product, functional equation, width `ε/2`), so
  a proof must use degree one.
- **Fails T6.** The only known self-improvement is Deligne's tensor-power step, closed on Weil's kernel (2.4).
  Nothing shows it easier than RH.

### 2.6.2 Route PM — none
`D_s ≤ 0` always, so a nonnegative expression is `D_s = 0`, which is RH [L]. Both expressions carry `K_σ`; `T₂`
reverses sign under `s ↦ ½ − s̄` [L]. No input outside the three-term and Hecke relations is named.

### 2.6.3 Route WD — none
The RH-level statement is the emptiness of the off-line set in another form [L]. WD's valid content is below RH
(2.5.1, 2.5.3).

### 2.6.4 Route HF — none
Transport across one prime is induction on an antitone threshold [L]. Dirichlet-shift companions reduce long windows
to head windows `R₁(log d)` [L], and a head window is again a window (B55).

### 2.6.5 Route ZCG — none
`𝓗` is the squared gap [L], so `𝓗 ≥ 0` is reality, restated. The camera reads the sign and produces none.

## 2.7 Does closing RH need a new field?

**Assessment: two programmes, a receiver and a producer.**

- **Programme A — Critical Hardy theory of the window cone.** The exact theory of what a proof must deliver on
  windows. A new field: criticality, frustration and logarithmic boundary behaviour have no existing home.
- **Programme B — Arithmetic production at square-root precision.** Where the input comes from. The classical
  problem area of analytic number theory, with a sharp entry test proved in Lean.

Two and not more: edge theory, frustration and transport concern one object, the nested cones `𝒜(c)`, and are bound
by one limit theorem. Stability, deformation and integrality are candidates for one job, production, and are judged
by one test. Two and not one: A treats the weights as free and gets `Λ` as output, B works on `Λ` itself.

| Programme | Core question | Can deliver | Cannot deliver | Open walls | Corpus base |
|---|---|---|---|---|---|
| A | structure of `𝒜(c)`: uniqueness rate, margin law, edge calculus, Hamiltonian | exact finite-level theorems; the precise target for any input | a sign for ζ: bounded apertures are blind to every width [L], and uniform statements in `c` are RH or the width [L] | B58, B59, B3, B4, B5, B56, B49, B51, A13, A41 | FADF, SWC, ACT, CSTW, AHD, GWZ, WTZ, RHTower cone theory |
| B | an unconditional statement inside the strip that carries parity and square-root precision | averaged RH; density; possibly a route to the count | nothing yet: every known producer is precision-blind [L] | B20, B21, B23, B26, B57, B14, B44, B52, B53 | ArithmeticOfSquareRootPrecision, CDG, RHTower Sieve/Levinson, ZCG, FFP |

**The assessment that all routes converge on nonlocal arithmetic criticality** agrees with 1.1–1.12. Its two deepening
directions exist in Lean and stay inside Programme A:
- *Collective sliver cancellation in window-adapted signed gauges:* the gauge family is exact on every window, its
  freedom acts only in the pole direction, and on the pole-neutral hyperplane every neutral gauge reads the raw form
  `archForm − primeSum`; pockets sent to infinity conserve the outside deficit [L: SWC].
- *Non-orthogonal coupling of untwisted and twisted modes:* Dirichlet-shift companions
  `1_{d|n}g₀(log(n/N) + log d)/√n` couple at `O(1)` where orthogonal twists couple at `O(1/K)`, and annihilate every
  tail mode; the residue is the head window `R₁(log d)`; stabilization for every `d` ⇔ RH; `d = 2` unconditional
  [L: AHD].

Each reduces the sign to a smaller window object and supplies no input.

### 2.7.1 Programme A — Critical Hardy theory of the window cone

*What it is about.* Signed nonlocal quadratic forms on intervals, `W_λ = H − P_λ`: the logarithmic-order archimedean
jump form `1 + ½log(1 − D²)` up to a bounded convolution, the pole kept, jumps of length `log n` with free weights
`λ(n)`, and the nested convex cones `𝒜(c) = {λ : W_λ ≥ 0 on [−c, c]}`. Its anchor: RH ⇔ every `𝒜(c)` is nonempty, and
`⋂_c 𝒜(c)` is `{Λ}` under RH and empty otherwise; only `Γ`, the pole and the positions `log n` enter [L: RHTower]. It
includes the boundary theory (Wiener–Hopf factor `κ(s) ∼ √log s`, positive causal kernel, edge killing,
regional–edge splitting) and the transport theory (stage forms, fold energies, head windows, de Branges chain).

*What it is like.* Critical (no Hardy weight; margin collapse doubly exponential in `c`); frustrated in every sign
gauge past `log ρ` (even) and `½log 2` (odd); exact in format; convex in the weights; logarithmic at the boundary;
moment-theoretic in each sector.

*Limits proved in Lean.* Positivity at a finite aperture, however large, is consistent with every width. Uniform
statements in `c` are RH (`1 ∈ ℋ(c)` ∀c, transport, contact) or the width (negativity rate of the form =
`configWidth`). A proof must therefore be uniform in `c`, and A alone holds no input for that.

*Criteria it must meet.*
1. Reproduce `log ρ`, `½log 2`, the floors to `a_∞`, the margins and the bands of 1.15.
2. Pay the pole square (odd) and the cosh deficit (even) with retained variance; the trivial zeros at the centre.
3. Distinguish the datum (pole, conductor one) from no-pole data at high conductor, whose cone contains `0` as soon
   as `log q ≥ log π − ψ(¼)` [D] and is not a point.

*Questions, each passing T1–T3 and T7, none claimed as a door.*
1. **Effective uniqueness (B58).** Give explicit `ε(n, c) → 0` with `|λ(n) − Λ(n)| ≤ ε(n, c)` for all `λ ∈ 𝒜(c)`,
   unconditionally. Consequence: the class "choose other weights" is closed at each finite level. Mechanism: make the
   twisted-arc annihilating measure of `eq_vonMangoldt_of_weilPositiveFull` explicit.
2. **Margin law (B59).** Determine the decay of `λ*(c) = max_λ λ_min(W_λ|[−c,c])` and of the band widths. Does
   `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` [L] hold for `λ*`? Consequence: slack from free weights is excluded at a stated
   rate. Data: 1.15.
3. **Edge profile.** The exact boundary behaviour of window extremals and Riesz vectors, conjecturally
   `(log(1/dist))^{−1/2}` from `κ` [D]. Consequence: convergence rates for A5 and A13. Independent of arithmetic.
4. **A5, A13, A41.** Work items: numerical membership, cone maps, the Hamiltonian. A41's regularity is B51, RH.

*Tools.* Criticality theory and optimal Hardy weights for nonlocal operators; semidefinite duality
(`WeilPositivityLinearDuality`); Wiener–Hopf and renewal theory; logarithmic Laplacian and trace theory for nonlocal
Dirichlet forms; de Branges spaces and inverse spectral theory; Hamburger/Stieltjes moments; rational Hecke graphs.

*Objects and language.* Calibration cones, bands, best margin, Hardy intervals, stage fibres, neutral signed gauges,
pole-neutral hyperplanes, logarithmic Poisson factor, causal kernel, edge killing, head windows, evaluation kernels,
contact.

*Mechanisms it aims to discover.* An explicit form of cone uniqueness; the law of the cone's collapse; an edge
calculus. It does not aim at a sign for ζ without an input from B.

### 2.7.2 Programme B — Arithmetic production at square-root precision

*What it is about.* Unconditional statements about `Λ` or about ζ inside the strip that a proof of RH must contain:
inputs that separate `Λ` from its twin and from its perturbations by `εn^{−η}`.

*What it is like.* Analytic and parity-sensitive: mean values of long Dirichlet polynomials, bilinear forms, density
near the line. Exact identities (`Σ_{d|n}Λ(d) = log n`, functional equation) are precise but determine `Λ` outright
and give no inequality; asymptotic laws give inequalities and are precision-blind.

*Entry criteria, proved in Lean* (`deciding_input_necessary_properties`). Any input implying the count must be
1. parity-breaking: false for the Liouville twin;
2. precision-faithful: never true for both `a` and `a + εn^{−η}`, `0 ≤ η < ½`;
3. of unbounded aperture: every finite window extends to a weight failing it;
4. with stabilizer inside the square-root class.

*Candidates against the criteria.*

| Candidate | Result | Anchor |
|---|---|---|
| PNT, Guth–Maynard, error laws weaker than square root | precision-blind | `producers_are_precision_blind`, `errorLaw_cannot_decide` [L] |
| Finite-window positivity | fails aperture | `not_of_finite_window` [L] |
| Square-root integrality (Siegel, Liouville halves) | RH in each half; integrality exponent `= Θ` | `TheIntegralityExponentIsTheZeroWidth` [L] |
| Camera | precision-faithful and sign-free: reads, does not produce | ZCG [L] |
| Heat flow, finite free stability | criteria restate RH; size stops at `½/log X`; Gaussian capacity `o(d⁻²)` | ZCG, FFP [L] |
| Hadamard and tensor powers | every degree carries RH | RIT [L] |
| Integrality of Frobenius traces | assumes purity | `collide_or_repel` [L] |

*Questions.*
1. **`100%` critical-scale clustering (B20, 2.5.1).** Valid; mechanism: long mollifiers; blocked at the Π wall.
2. **`D_win`, `D_zero` (B21, 2.5.3).** Valid; no mechanism.
3. **Mollified second moment on the line at length `T^θ`, `θ → ∞`.** Valid; a classical open problem; implies 1 [D].
4. **Self-improvement (B57, 2.6.1).** Door-shaped; no mechanism.

*Tools.* Mean-value theorems for Dirichlet polynomials, large sieve, Type I/II sums and the parity problem; zero-density
methods; Levinson–Conrey mollification; Selberg's moments; Nair integrals.

*Objects and language.* Precision classes, the square-root class `𝒬`, Liouville twin, stabilizers, integrality halves,
mollifier length, critical-scale clustering, Planck shadows, giant clusters.

*Mechanisms it aims to discover.* A parity-breaking bilinear input at square-root precision. None is named in the
corpus or here.

### 2.7.3 How the programmes fit

- B alone can close RH: the count at square-root precision is RH. A is needed only if production arrives in a form
  weaker than the count.
- A alone cannot: its finite-level theorems are consistent with every width, and its uniform statements are RH.
- Outside both: counts and Hodge index; Markov, Perron and switched-balance certificates past their thresholds;
  size-only payment; point-value certificates; gauge optimization off the pole; orthogonal twisted repair; finite
  templates past spread 6; source-faithful finite free splits; PM line selectors; identification without sign;
  tensor amplification; integrality without purity.

## 2.8 The one question

**Answer: no question meets the standard.** No statement both is less hard than RH or quasi-RH and has a written
argument that it pushes the door open.

**`a*(ζ) ≥ log 2` (B5) fails as a door.** It stays a valid finite target (A5).

| Test | Result |
|---|---|
| T3 | No consequence for any other window can be written. "Template for B2/B3" is not an implication |
| T4 | Determined by the weights at `n ≤ 3` (`weilPositiveFullUpTo_congr`); a property determined by a finite window implies the count for no weight (`not_of_finite_window`); an off-line lattice of any width is positive at any given aperture [L] |
| T5 | True for every weight agreeing with `Λ` at `2, 3`, including `liouvilleTail Λ 3`, which fails the count [L]. The window holds no multiplicative relation: `Λ(4) = Λ(2)` enters at `c = log 2`, the first composite `Λ(6) = 0` at `½log 6` |
| T6 | "By the exact two-sector certificate" is empty: the format is exact, so every proof of positivity has it [L] |
| Zero content | No zero information below half-width `4` [D] |
| Class | Membership of two numbers in a compact convex set with margin `≈ 10⁻¹²` at `log 2` [N] |

**The strongest valid question is `100%` critical-scale clustering (2.5.1).** It is below RH and quasi-RH, passes T1–T5
and T7, has eight equivalent forms in Lean, and uses the Euler product inside the strip. It does not push the door:
sparse off-line zeros survive it, and its mechanism stops at the Π wall.

**What would meet the standard:** an unconditional inequality about `Λ` or ζ in the strip, false for the Liouville
twin and for `Λ + εn^{−η}`, not determined by a finite window, and not a consequence of a precision-blind law. None
is known to the corpus.
