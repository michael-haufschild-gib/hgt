# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates and the retired PW-B branch, checked against the Lean
corpus at `5c51362a92` plus working tree. `[D]` marks a statement derived here from `[L]` results and
not formalized. For every route: what is established, the obstacles that are **(A) just
work** (known mathematics, finite computation, effectivisation, formal closure), and the obstacles
that are **(B) open mathematics** (no known solution).

Legend. `[L]` Lean theorem, statement read. `[S]` Lean source unfinished or outside its umbrella.
`[map]` frontier-map status, statement not read here. Strength of a B-item: **RH** = equivalent to
RH; **≥qRH** = implies Lindelöf and a zero-free half-plane `Re s > ½ + α`; **LH** = implies the
Lindelöf hypothesis, no zero-free half-plane known to follow; **sub** = strictly weaker than LH or of
unknown strength. Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme codes as in the
frontier-map source locator; RIT = RenormalizedIntersectionTheory, EHT = EdgeHodgeTheory,
CSAR = CriticalScaleArithmeticRigidity, BOT = Bottcher.

## 0. Hardness calibration (applies to every route)

| Fact | Anchor | Consequence for routes |
|---|---|---|
| `κ(K_ζ) = #` right zeros, already on a two-prime test lattice; `κ_ζ` even; RH ⇔ `κ = 0` ⇔ `κ ≤ 1` | HKT `TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] | every index route ends in the same even integer |
| `κ < ∞` ⇔ finite off-line support ⇔ bounded heat counts ⇔ bounded collision masses ⇔ `sup_T O(T) < ∞` ⇒ Lindelöf + zero-free half-plane | HKT [L]; AOG `index_exit_first_rung_tfae` [L] | every finite-index or bounded-cumulative-charge waypoint is **≥qRH** |
| Künneth square all-or-nothing: `κ(K_ζ⊠K_ζ) ∈ {0, ∞}`, `0` ⇔ RH; every Hadamard power `K_ζ^n` PD ⇔ RH | RIT `TheKunnethSquareOfWeilsKernelIsRH`, `TheHadamardPowersOfWeilsKernel` [L] | tensor and power amplification never soften the sign |
| Glued Weil state `κ(φ_c) = κ_ζ + 1` at `∞` and at every prime; hence `κ(φ_c) ∈ {1, 3, 5, …, ∞}`, never `2` | AKG `TheGluingFormulaAtEveryPlace` [L]; `negIndex_weilArchState_ne_two` [S] | RH ⇔ `κ(φ_c) < 3` for one explicit affine state |
| Boost hyperplane = `v₁^⊥` = Markov hyperplane = harmonic hyperplane; `v₁` = complete-Weil ground state | RIT `ThePoleClassIsTheGroundConductor`, `TheHodgeIndexAtGrowingOverlap` [L] | SC, the complete-Weil cluster and the Markov criterion are one sign problem on one hyperplane |
| Detection edge `e_φ(N)` = first overlap `c ≥ 1` with `W_{φ,c,N}` not PSD; RH ⇔ `e_φ ≡ ∞` for every admissible profile; `e_φ ≤ 2(log N)^β` infinitely often for every `β > ¼` under ¬RH | EHT `TheEdgeOfTheCompleteWeilFamily` [L] | the edge is a defined invariant; RH is its nonexistence |
| Universal regime: tilted spline PD on all vectors for `1 ≤ c ≤ (log N)^α`, `α < α* = 1/144` (explicit); edge `≥ (log N)^α` eventually, `e → ∞` unconditionally | CACT `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_powerLog` [L]; EHT [L] | under ¬RH the tilted edge lies in `[(log N)^{1/144}, 2(log N)^{¼+}]` infinitely often |
| RH regime: tilted spline full space at `2(log N)^{α>¼}`, `v₁^⊥` at `α>½`; every C^∞ nonnegative profile on `v₁^⊥` at every `2(log N)^{α>0}` (unitBump explicit); sinc at `≍ L(log L)²` | RAPT, RIT `riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log`, TM [L] | the universal and the strongest RH regime use different profiles; no profile transfer exists |
| Threshold curve: `W_{φ,c,N}` PSD ⇔ `N < h(atom of width c/N)`; at fixed width positivity at all horizons ⇔ the atom sees no right zero; tilted `h(w) → ∞` as `w → 0⁺`; over a curve the edge is `≤ 2g` | EHT `TheEdgeIsAThresholdCurve`, `TheHorizonFlowAtFixedWidth`, `TheFunctionFieldFlowIsTrivial` [S] | complete-Weil, fixed-test and aperture families are sections of one function `h(w)` |
| Ground energy `E₁(c) ≍ τ(c)`; at the sinc threshold `τ(c) log N ≈ 1` | RAPT, TM [L] | at the edge every method must control the matrix to accuracy below `≈ 1/log N` |
| Coupling carries the index: for `|S| ≥ 2` the coupled assembly `K ∘ proj_S` has glued index `κ_ζ + 1`; on log-height `≤ L` the explicit formula with primes `≤ e^{2L+8}` equals `ratCorr`, window supremum `κ_ζ + 1`; coupled = axial (separable) + inter-tower coupling (coprime cross-differences, zero on axes); separable assemblies kill the coupling, cannot approximate `ratCorr`, are zero-blind when truncated and diverge when untruncated on the finite non-RH stratum; zero coupling + continuity ⇒ affine profile, `κ ≤ 2` | AKG `TowerCoupling/InterTowerCouplingRigidity`, `CoupledTowerSignatureFormula` [L]; `STruncatedExplicitTowers` [S] | finitely many primes suffice on every window; the zeros live in the coupling, not in any separable or single-tower datum; RH ⇔ bounded coupling [D] |
| One-sided count `ψ(x) − x ≤ C√x log²x` ⇔ RH; section shortfall rate ⇔ zero width | ACP, SPTL [L] | every exponent gain on a count is quasi-RH |
| Collision charge: `O(T)` cumulative; `n_off(T) ≤ ΔO(T) ≤ 2n(T)n_off(T)`, `ΔO ≪ log²T`; bounded `ΔO` ⇒ critical proportion `→ 1`; with Backlund's equivalence, `ΔO = o(log T)` ⇒ Lindelöf. Master inequality `H(γ) ≤ C(1 + log|γ|/L) − Re Π_{F_L} + 4E_γ(L)`; at `L = ¼ log log|γ|`, `H(γ) ≪ log|γ|/log log|γ| + E_γ` | CDG `CollisionChargeIncrements`, `HeckeDefectHorizontalMultiplicity` [L]; RHTower `BacklundLindelofConverse` [L] | per-window charge bounds are **LH**, cumulative `O(T) = o(N(T))` is density one (**sub**), bounded `O` is **≥qRH**; the Hecke defect controls fibre multiplicity |
| Falsification certificates: RH ⇒ unique upper periodic point of the Xi Donoghue map; RH ⇒ every Jensen section of `∏(1−c_iD)D^kΞ` splits (and RH ⇔ all Xi Jensen polynomials split); RH ⇒ strictly left-moving Ritz branches of the Xi heat-moment form | BOT, Jensen `XiJetObstruction`, MomentFlow `XiRitzVelocity` [L] | finite tests for ¬RH; none has a converse mechanism |
| Index twin-blind; glue pole-blind; glued test index `∞` on finite flips; edge of every single prime flip bounded; atomic Hodge index separates exactly submaximal margins | AKG, RIT, EHT `eventually_twinEdge_primeFlip_le` [L] | selection must come from prime data; dense/co-dense infinite twins of zero harmonic density remain |
| Heat: `κ(φ_c^{(t)}) = N(t)/2 + 1`, antitone, `1` for `t ≥ 1/8`; `0 ≤ Λ < 1/8` | AKG, RHTower [L] | heat routes reduce to `Λ = 0` |
| Crossing-free Hermitian path `A → I` exists iff `A` is PD; index constant on nondegenerate connected families | EHT `IntegersAlongPaths` [L] | homotopy invariance relocates the sign to noncrossing; deformation to a positive model is not a free input |

## 1. Shared obstacle blocks

### S1. Complete Weil matrix at growing overlap
Routes: HF, SRT, AIP, ACS-atomic, ACT, SC (finite resolution), CHMD-index; RW/EWU/OWU through the
ground minimum.

Established:
- universal regime: tilted spline, all vectors, `1 ≤ c ≤ (log N)^{α<1/144}`: floor `κ/(2c⁷)`, literal
  `weilQuad ≥ 0`, reserve `W ≥ (b/c²³) D_N ≥ (b/log N) D_N` [L]; mechanism: spectral-floor shift, low
  band `Q₁ = ⌊(log N)^{1/16}⌋`, high-tail cutoff `log R' ≤ C_R c¹⁶ + log Q₁`, coercivity above `Q₁` from
  `renormalizedPrimeEnergy ≥ (½ log Q − C)‖y‖²` with a numerical `C` (CAF `PrimePacketCoercivity`) [L];
- explicit confinement: every mass `≤ 1`, defect `≤ K` vector is approximated to squared error `η` in
  modes `m ≤ R`, `log R ≤ C_quad(K+1)/η²`, `C_quad` explicit; explicit reverse gap
  `‖y − P_Q y‖² > ‖y‖²/16 ⇒ poleDefect ≥ (log Q/(256 C_quad) − 1)‖y‖²`; explicit rough conditioning
  (`P(n) log n ≥ 1/128`); truncation error measured by the actual logarithmic class moment [L];
- fixed packets `(log N)^{<1/19}`, Hodge index on fixed and slowly growing initial packets below the
  nineteenth root; fixed `c` with gap on `v₁^⊥`: energy `≥ (E₁ + g/2 − ε)‖x‖²` [L];
- conductor averages at RH-complete overlap (`M = ⌊N^θ⌋`, `θ < ½`, `c²/log N → 0`): summed residual
  `= o(Σ E_m²)`, nonpositive-conductor fraction `→ 0`, nonpositive span dimension `o(M)` [L];
- single conductors above polylog: for every C² profile, `θ < ½`, `α < ¼`, `A > 8α`, every mode
  `(log N)^A ≤ m ≤ N^θ` has energy `≥ ((1−2θ)/4) log m`; no exceptional single conductor there [L];
  packet pole defect `≥ (log N − 3 log Q − 1) L_Q` [L];
- prime-incidence calculus: `√(p−1)/p` times a prime mode is `1_{p|n} − 1/p`; dilation jumps are the
  incidence events `[p|k ∧ p∤n]`; the generator is the nondivisibility sum `Σ_{p∤n} b_p log p/(p−1)`;
  complementary tails are nonnegative [L]; the coherent prime residual is bounded below by
  `≍ log P · (pole mass)²` beyond the scalar row's cost [L];
- packet arithmetic (CSAR): successor projection plus one dyadic pole reading control every
  nonconstant conductor, `(3/4)·mass ≤ energy`, sharp, kernel = constant packet, on windows longer
  than `Q(Q−1)` [L]; finite prime heads and the literal prime residual bounded relative to the
  adjunction energy `L_Q`: residual² `≤ [C(1+log Q)Σa² + 532(1+log Q)² L_Q]/log N`, and
  `≤ C(1+log Q)² L_Q/log N` after removing the constant conductor [S]; prime-pole response
  `B_Q² ≤ S_Q L_Q`, `S_Q = Σ_{p≤Q} log p/p = log Q + O(1)` sharp, surviving on every finite-horizon
  pole hyperplane [S];
- detection edge as a Lean object, edge window under ¬RH, threshold-curve form (§0) [L/S];
- hyperplane positivity leaves at most one negative eigenvalue [L].

Location of the sign problem: the binding terms of the 1/144 proof are the intermediate-band overlap
cost `c⁴/√Q₁` (needs `α < q/8`, `q` the low-band exponent) and the residual budget `Q₁⁵ c¹⁷/√log N`
(needs `5q + 17α < ½`); with the present inequalities the method optimum is `≈ 1/114`. Beyond that
sit the structural ceilings: residual-versus-floor `c¹⁹/log N` (fixed packets stop at `1/19`) and
confinement (nonpositive units have defect `≤ Cc¹⁶`, below `√N` only for `α < 1/16`). At RH-complete
overlap the ground energy is `≲ 1/log N` (sinc) or `(log N)^{−7/4}` (tilted).

| | Obstacle |
|---|---|
| A1 | Explicit horizon `N₀` for the power-log theorem; optimise its internal exponents (low-band exponent, overlap and residual budgets) up to the method optimum `≈ 1/114` |
| A2 | Exact complete Weil energy on prime-incidence packets, Gamma and both poles retained |
| A3 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` |
| A4 | Compare the CSAR rigidity and relative prime-residual energies with the complete Weil energy (Gamma, both poles, mixed Schur terms) on fixed and slowly growing packets |
| A5 | Growing-packet head-pole cancellation on the Gamma/polar side for packets up to `exp(c√log Y)` (window PNT with classical error); the prime side is controlled by `L_Q` |
| A6 | Edge dictionary: compute the edge exponent of a finite model zero configuration (one off-line pair of depth `δ`, height `γ`) for the tilted spline, i.e. the least `α` with a negative vector at `(log N)^α` |
| B1 | Positivity on `v₁^⊥` across the detection edge: tilted spline at its RH-complete rate, or any C^∞ profile at any `α > 0` — **RH** (Σ1, Σ14) |
| B2 | Signed (quadratic-form) estimate on the subthreshold conductor block (`m ≲ c`) beating the residual-versus-floor exponent `19` — **sub** (Σ13) |
| B3 | Defect bound for nonpositive vectors below `c¹⁶` — **sub** in the universal regime, **RH** at RH-complete overlap (Σ1c) |
| B4 | Low-conductor and exceptional spans: single modes are coercive above `(log N)^A`, but sublinear nonpositive span dimension does not bound the index — **sub** (Σ1g, Π9) |
| B5 | Conductors `N^{½} < m ≤ N`: frames or residual averages — **sub**, Elliott–Halberstam type (Σ1h) |
| B6 | Edge location of `ζ` inside `[(log N)^{1/144}, 2(log N)^{¼+}]` under ¬RH; sign-preserving profile transfer between the tilted spline and smooth profiles — **sub** (Σ14) |
| B7 | Mertens cancellation: the pole term with running counterterm `log N − γ` absorbs the coherent prime-pole cost `S_Q = log Q + O(1)` up to `O(1)·L_Q`, uniformly in `Q ≤ N^θ` (no adjunction-only bound is `Q`-uniform) — **sub** (Σ17) |
| B7a | Localization: near-edge nonpositive vectors lie within `o(1)` of the coherent prime sector — **sub** (Σ17) |

### S2. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD-index, SC, RIT-Künneth.

Established [L]: index = right-zero count, even; finite stratum TFAE including bounded cumulative
collision charge; converse Krein–Langer for orbit kernels; transverse energy pays each negative
square; collision mass `= 2(κ + excess)` on the finite stratum; `κ ≤ sup O`; Jordan pair signature;
Künneth all-or-nothing; finite off-line support forces `κ₊(K_ζ) = ∞`; finite-rank changes preserve
finiteness of index; fixed-test horizon defect `d_f(N)` nondecreasing with supremum the number of
right zeros the test sees, attained when finite; loop-Eisenstein band poles of `Λ(s)/Λ(s+1)` in
`−½ < Re s < 0` are counted by the Hodge defect.

| | Obstacle |
|---|---|
| A7 | Explicit capture stage for complete-cell indices (AID `TheCompleteCellsCaptureEveryFiniteIndex`, [S]) |
| B8 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ⊠K_ζ` (Σ5) |
| B9 | Converse Krein–Langer for kernels not presented by a zero configuration — **sub** |
| B10 | Emptiness mechanism for the loop-Eisenstein band poles (pole-order / noncancellation theorem for the constant term) — **RH** |

### S3. Heat flow, collision charge, integer readings
Routes: WD, LA, TH, TT, HCF, SC-heat; HEF receivers.

Established [L]: heat state `κ(φ_c^{(t)}) = N(t)/2 + 1`, antitone, `1` for `t ≥ 1/8`; Hodge defect of
`K_t` = future collision pairs; `E(t)` dissipation; slice/flow thresholds; reality horizon
`2πe^{(2/3+ε)/t}`; `λ_t log t → 0` ⇔ zeros tend to the line; collision charge `O ∈ 2ℕ`; integer theta
Wiener–Hopf operators with Fredholm index = charge on every window; explicit product-current error
`< 1/8` at `n ≥ 6`; index `0` on `T ≤ 3`; index transitions only through window-boundary or
Zhukovsky-ellipse crossings; first stabilized prefix unbounded in height; **root-free contour-loop
stopping certificate**: sound, eventually complete at every height and every stage
`n ≥ thetaWindowScale T`, no simplicity assumption; the least certified prefix reads the exact
charge; RH ⇔ the index at the stopping prefix vanishes eventually in scale at every integer
height; seam-smooth Gaussian prefixes preserve divisor and collision operator; unit-window
increments `n_off ≤ ΔO ≤ 2 n n_off`, `ΔO ≪ log²T`, `O(n) ≤ A + C n log²(n+1)`, bounded `ΔO` ⇒
density one; dyadic Hecke amplification: RH ⇔ dyadic Hecke defects `E(2^k)` subexponential, and a
bound at one large dyadic scale transfers losslessly to all smaller scales (RBG); Hecke-averaged
cosh coercivity `H(γ) ≤ D(twist_γ F_L)`, off-line defect `≤ 4E_γ(L) + C(1+log|γ|)/L²`, master
inequality `H(γ) ≤ C(1 + log|γ|/L) − Re Π_{F_L}(e^{2L+½}, −γ/2π) + 4E_γ(L)` for
`1 ≤ L ≤ 4 log(1+|γ|)`; `ΔO ≤ 2·max H·n_off`; at `L = c log T` bounded prime polynomial + Hecke defect
give `ΔO ≪ log T`; at `L = ¼ log log|γ|`, `H(γ) ≪ log|γ|/log log|γ| + E_γ(¼ log log|γ|)`.

| | Obstacle |
|---|---|
| A8 | Stronger subconvexity exponent to lower the heat floor `2/3 = 4μ(½)` |
| A9 | Certified de Bruijn–Newman upper bound below `1/8` as an index-one time for the heat state |
| A10 | Compose `CollisionChargeIncrements` with Backlund's converse: `ΔO(T) = o(log T)` ⇒ `OffLineSparse` ⇒ Lindelöf, as one Lean statement |
| A11 | Replace the compact minima of the stopping certificate by certified interval bounds (a computable stopping prefix per window) |
| B11 | Subcritical heat count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub** |
| B12 | Pointwise horizon constant `< ½` — **≥qRH** |
| B13 | Source-side collision charge `< 2` on every window; no heat-index jump on `(0, 1/8]` — **RH** (Σ8, Σ16) |
| B14 | Cumulative charge `O(T) = o(N(T))` from integer theta data — **sub** (density one) |
| B15 | Uniform increment bound `ΔO(T) ≤ M` (or `o(log T)`) — **LH** |
| B16 | Every `Λ_X = 0` — **RH** |
| B17 | Detection scale independent of the zero gap (a stage choice not depending on divisor separation and strip margins) — **sub** (Π13) |
| B17a | Hecke defect at doubly-logarithmic scale `E_γ(¼ log log|γ|) = o(log|γ|)`, hence every zero multiplicity `o(log|γ|)` — **sub** |
| B17b | Prime-side bound for `E_γ(c log T)` by the prime polynomial of length `T^{2c}`, uniformly on `[T, T+1)` — **RH** through dyadic amplification (Γ4) |

### S4. Counts and producers
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity.

Established [L]: one-sided count ⇔ RH; prime-error budget `S ≥ 2 + γ − log 4π`; linear theta RR, no
quadratic Riemann inequality; quadratic RR on the scaling surface ⇔ renormalized Hodge index
(constructing a Serre-dual `h⁰` with the required growth is RH); integer Hecke stencils; every
individual producer has slope `> 1`; ceilings `2 log 2`, `1 + 1/((P+1)(P+2))`, `31/30`,
`exp(−0.87n)`; growing-alphabet alternating producers: `ψ, θ ≤ (1+ε)x + C_ε log²x`.

| | Obstacle |
|---|---|
| A12 | Same-order mixed-jet recovery for `≥ 3` primes |
| A13 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer |
| B18 | ε-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3) |
| B19 | Any unconditional source input at square-root precision — **RH** (Π2) |
| B20 | Characteristic-0 quadratic effectivity / an unconditional Serre-dual `h⁰` — **RH** (Π11) |

### S5. Carriers, gluing and selection
Routes: SC, AKG, APD, Γ-candidates.

Established: escape/mixing/height decay ⇒ `κ ∈ {0, ∞}`; local index wall at every prime and at `∞`
of `𝔽_q(X)`; Hasse principle for Hecke states; pole–successor `κ = κ₀ + 1` at every place; tower
signature `Σκ₀ + 1 ≤ κ ≤ Σκ₀ + 2`; gluing at every place; stable gluing; the glue absorbs exactly its
own pair; shell identity of the archimedean form; global pole = extremal weight; no assembly of local
poles at two or more primes has one square [L]. Carrier classification: for every additive
`H ≤ ℚ`, a finite-index Hermitian carrier with translation reading `1_H` and continuous dilation at
`1` exists iff `H = {0}` or `H = ℚ`, both with PD carriers of dilation coefficient `1`; properness of
`H` ⇔ universal polynomial-fibre index preservation; saturated translations are two-sided periods
[L]. Local polar index on `ℤ`: `κ₀(k) = κ(Δ²k)`, decaying `Δ²` gives `{0, ∞}`, plus one pole pair
`{0, 1, ∞}` [S]. Tower coupling [L]: coupled assembly = axial (unique separable) + inter-tower
coupling (coprime cross-differences, zero on axes); `|S| ≥ 2` coupled assemblies carry `κ_ζ + 1`
exactly (also tempered orbit kernels, primitive Dirichlet L-functions); window explicit formula
with primes `≤ e^{2L+8}` exact on log-height `≤ L`, window supremum `κ_ζ + 1`; fixed-`S` global
truncated correlations `∈ {1, ∞}`; no separable net converges to `ratCorr`; zero coupling of a
continuous profile on two disjoint two-prime lattices ⇒ affine, `κ, κ₊ ≤ 2`; `ratCorr` has
`κ = ∞` or `κ₊ = ∞` and nonzero coupling on `⟨2,3⟩ × ⟨5,7⟩`; untruncated axial assemblies
diverge on the finite non-RH stratum. Separable `S`-truncated towers are zero-blind; diagonal
counterterms make `Λ` and a prime-flip twin both glued index `1` [S]. Selection [L]: prime-set
flips separated by the atomic Hodge index iff greatest gap `< 2 log 2`; thin, co-thin and cofinite
flips separated; every flip of relative logarithmic density `κ > ¼` separated (Wirsing–Gronwall);
edge of every single prime flip bounded.

| | Obstacle |
|---|---|
| A14 | Canonical relative split for general nonzero proper rational subgroup successors (integer-Haar split is the template) |
| A15 | `𝔽_q(X)` calibration: local walls at higher-degree places, product formula for the global Hecke state, archimedean Weil state of a curve; function-field extremal-weight gluing |
| A16 | Formalize RH ⇔ bounded inter-tower coupling of `ratCorr` (Hyers–Ulam on `ℝ` + density of two-prime log-lattices + continuity + `riemannHypothesis_of_norm_zetaKernel_le`) [D] |
| B21 | Exact sum-of-squares (shell) identity for Weil's dilation form on `ℓ = 0` — **RH** |
| B22 | Quantitative coupling transfer: local Hyers–Ulam with Baker-type constants, `sup_{|log u|≤L}|K(u) − K(1)| ≤ C L^k · sup|coupling|` — **sub** |
| B22a | Bounded inter-tower coupling of `ratCorr` on `⟨2,3⟩ × ⟨5,7⟩` — **RH** [D] |
| B23 | Zero-independent selection at the trivial gauge point — **RH** (Γ1) |
| B24 | Selection of flip sets of relative logarithmic density `0 < κ ≤ ¼`, zero-density sets with divergent `Σ 1/p`, and irregular densities — **sub** (Γ12) |
| B25 | Arithmetic correspondence acting as conjugation on the zero divisor (Frobenius at infinity) — **RH** (Γ4) |

## 2. Live routes

### WL — prime lag / Weil–Li energy
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔ RH +
simple; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; arithmetic Bézout; Landau-window cost
`(2 log 2 − ε)mn`; Adams `2^{qr}`; S4 producers up to the main term [L].
- A: A12, A13.
- B: one-sided prime-error bound (**RH**, Π1); B18; joint Möbius-moment / Mertens / sawtooth payment at
  square-root precision (**RH**, Π5).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0` ∀A ⇔ RH; attained excess forces `μ₀(B) ≤ −c'e^{2ΘB}/B³` [L]; floors
`≥ mass/5000` to `181/500`, `≥ mass/8000` up to `A₊ < ½`; one sinc multiple `K` gives positivity on
tests in `[−R, R]` with `288e⌈1+e^{2(R+1)}⌉ < K/(4K_τ)` [L]; fixed-test horizon index and threshold
curve tie aperture families to the complete-Weil edge [S].
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
Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every Xi Jensen polynomial
splits, and RH ⇒ every Jensen section of every real translate of `∏(1−c_iD)D^kΞ` splits; RH ⇒
strictly left-moving Ritz branches of the Xi heat-moment form; slice and flow thresholds; Vitali
blow-up; `λ_t log t → 0` ⇔ every fixed-depth strip contains all high zeros; strip ⇒ Littlewood
windows; right-half squared-depth moment `o(V)`; fixed-depth counts `o(V)` [L].
- A: explicit horizon per fixed degree; A8.
- B: all-degree / all-height signs (**RH**, Σ4); uniform tail narrowing (**≥qRH**); shrinking-scale and
  exceptional-height control (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; central-gap receivers [map];
finite-matrix index laws along paths [L].
- A: none.
- B: matrix-complete decomposition with integer trace `< 1` on every disc (**RH**, Σ8); a
  source-driven noncrossing path (Σ19).

### HF — Hodge/Hecke/complete cells
Established: S1 in full; Haar/prime-edge Gamma reserve; full Weil index `≤ R + A` for `R` coarse cells;
Hecke-defect and collided-form receivers; heat Hodge defect `= N(t)/2`; quadratic RR ⇔ Hodge index;
loop-Eisenstein band poles = Hodge defect [L].
- A: A1–A6; A7.
- B: B1–B7; Hecke invariance of the collided form (**RH**, Γ4); RR branch: an unconditional
  Serre-dual `h⁰` (**RH**); Haar branch: non-arithmetic Gamma, signed potential, roots and poles
  jointly (Σ1b).

### CHMD — causal hyperbolic–modular duality
Established [L]: RH ⇔ `R ≤ ½` on the odd sector; prime wave `O(e^{|u|/2})`; every Haar piece except the
first-prime coarse layer has uniform finite index; Gamma graph pays the prime-two block; growing Euler
head alone unbounded; full prime window cancels the `√Y` pole on fixed packets.
- A: A5; fixed-cell first-prime / coarse / polar bookkeeping.
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
Fredholm index; low-window sectoriality; transition law; seam-smooth prefixes; source-intrinsic
root-free stopping rule (sound and eventually complete); unit-window charge increments; dyadic
Hecke amplification; master inequality bounding fibre multiplicity and `ΔO` by prime polynomial +
Hecke defect [L].
- A: A8, A9, A10, A11.
- B: B11–B17, B17a (**sub**), B17b (**RH**); vanishing global depth energy as `t ↓ 0` (**RH**); tower
  branch arithmetic index ceiling (**≥qRH**).

### LI — guarded history zeros
Established: `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order [L].
- A: none.
- B: pay the outside budget at every guarded zero (Σ).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packet light-Gram identity; negative finite-cutoff
pairings of the Abel clock [L]; normalized Xi Donoghue map `m = −Ξ'/(cΞ)` fixes `i` with multiplier
in `(77/85, 1)`, RH makes `i` its only upper periodic point, so a second upper solution of
`Ξ' + czΞ = 0` falsifies RH [L].
- A: none.
- B: uniform lower bound after complete source assembly (Σ); no converse to the Donoghue
  falsification criterion is known.

### PM — physical / complete-energy realization
Established: complete-energy and gauge-mass receivers; half-damping admission; escape alternative;
PW-B optical tools as support [L].
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
Established: RH ⇔ ξ-Newton source margin on discs; nonnegative Laplacian of the margin [map]; the
distinct Donoghue map gives a falsification criterion (SZ) [L].
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
`W_Liouville < −3 mass/10` [map]; companion forcing and conductor horizon incompatible for
`0 ≤ δ ≤ ½` [L].
- A: positivity on all odd tests slightly beyond `27/50` (shared with RW).
- B: all-test / all-aperture odd sign (**RH**, Σ1).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH [map].
- A: none.
- B: coefficient cancellation (**RH**, Π).

### RB — Robin / Nicolas
Established: large counterexamples need growing prime(-power) cores; colossally abundant reduction [L].
- A: none.
- B: square-root remainder on primorials (**RH**, Π).

### SRT — square-root threshold / zero visibility
Established: S1 in full; depth-gap visibility; local count ⇒ bounded critical multiplicity, true for
density-one heights; window depth-mass bound for all windows ⇒ zero-free strip; deep zeros `o(V)` and
deep windows `o(T)` centres; off-line local bound ⇒ critical fraction `→ 1`; Steklov full index for
`β > 2`; unit-window collision increments [L].
- A: A1–A6; explicit horizons.
- B: B1–B7; tower branch arithmetic index ceiling (**≥qRH**); unattained-depth detection (Σ5).

### ACT — collar transport
Established: explicit collar threshold pays every modulus outside nine atom-dominated moduli [L].
- A: the nine remaining moduli.
- B: one fixed shift paying every profile including exterior primes (Σ1).

### AIP — arithmetic incidence positivity
Established: S1 in full; all-aperture allocation receiver; full Weil index `≤ R + A` [L].
- A: A1, A4, A5; mixed Schur debit on fixed blocks.
- B: all-aperture allocation (**RH**); B2–B7.

### ACS — arithmetic Castelnuovo–Severi
Established [L]: RH ⇔ effectivity ⇔ Hodge index ⇔ section count; renormalized Hodge sign ⇔
scaling-surface Hodge ⇔ a real Serre-dual quadratic RR section-growth package; Castelnuovo–Severi
for rational scaling correspondences ⇔ RH; loop-Eisenstein band poles = Hodge defect; base theta
`h⁰` does not extend; graded strip ⇔ zero width; atomic branch = S1. `𝔽₃` elliptic curve: Euler
product, adelic Haar, idele Haar modulus, radial kernel, global adelic spectral integral
`= ζ_E(u)/ζ_E(u/3)` on `Re s > 1`, simple-root sections, Weyl-series absolute convergence on
`Re λ₀, Re λ₁ > 1`, affine polynomial cells, rotated series and constant-term definition; over a
curve the window edge is `≤ 2g` [S].
- A: measure-compatible Bruhat unfolding and constant-term evaluation on the `𝔽₃` loop group; S1 A-items.
- B: an unconditional Serre-dual `h⁰` (**RH**, Π11); a conformal correspondence over ℤ with factor
  `≠ 1` and bounded self-intersection (**RH**, Γ10); census displacement (Π8); B1–B7; B10.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) < 3` → `κ_ζ = 0` → RH.
Established [L]: `κ(φ_c) = κ_ζ + 1` for every `c > 0`, glued at any prime and for primitive Dirichlet
L-functions; `κ = κ^{(½)} + κ(Φ|_+)` with zero-blind translation reading `= 1`; on `ℓ = 0` the form is
Weil's dilation form plus shell squares; stable gluing with exact absorption of its own pair; simple
pole absorbed, double pole charged; Haar and subgroup successors with continuous dilation have
`κ = ∞` except the trivial endpoints `H = {0}, ℚ`, whose carriers are PD; finite-index Haar kernels
split uniquely with punctured limits exactly the reals `≤ 0`; heat-deformed state `φ_c^{(t)}` with
`κ = N(t)/2 + 1`; global pole = extremal weight; Künneth/Hadamard branch RH-equivalent and
all-or-nothing; glued test index `∞` for every finite flip; coupled two-prime assemblies have glued
index exactly `κ_ζ + 1`; the window explicit formula with primes `≤ e^{2L+8}` is exact on log-height
`≤ L`; the zeros are carried by the inter-tower coupling; separable data are blind or overcount.
[S]: `κ(φ_c) ≠ 2`; local polar index `= κ(Δ²k)` with trichotomy `{0, 1, ∞}`; separable
`S`-truncated assemblies zero-blind. [D]: RH ⇔ bounded inter-tower coupling of `ratCorr`.
- A: A14, A15, A16; A9 (heat calibration); transfer of the universal regime to the glued state on
  atomic test families through the threshold curve.
- B: independent `κ(φ_c) < 3`, equivalently positivity on `v₁^⊥` (**RH**, Σ1); B22a (**RH**); B22
  (**sub**); B21 (**RH**); B13 on the heat branch (**RH**); B11 on the heat branch (**sub**); B8 for the
  Künneth square (**RH**); a source-defined noncrossing path to an index-one model (**RH**, Σ19).

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
complete Weil family (HF, SRT, AIP, ACS-atomic, ACT, SC, RW, EWU, OWU), the heat/collision integer
(WD, LA, SC-heat, TG), rank/degree uniformity (TH, HCF, PA, GTA, LA-Jensen), scheduled prime sums
(FU, CFC, RP, SZ, LI, FEL, EGC) and realization (RN, PTR, W1C). SC sits on two further seams: the
inter-tower coupling (Σ ∩ Π: bounded coupling is RH) and the noncrossing of index paths (Σ19). The
complete-Weil cluster meets a third seam: the coherent prime sector, where the prime part carries
its one uncancellable logarithmic excitation (Σ17).
