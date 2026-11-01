# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates and the retired PW-B branch of the frontier map,
checked against the Lean corpus at `fe2f109c3e`. For every route: what is established, the
obstacles that are **(A) just work** (known mathematics, finite computation, effectivisation,
composition of proved statements), and the obstacles that are **(B) open mathematics** (no known
solution).

Evidence. `[L]` Lean source read (statement or module docstring). `[M]` frontier
map or killed-routes entry, Lean not re-read. `[D]` derived here from `[L]` statements, not
formalized. `[P]` paper card in `2-fully-proven` without Lean.
Strength of a B-item: **RH** equivalent to RH; **≥qRH** implies Lindelöf and a zero-free
half-plane; **LH** implies Lindelöf; **sub** strictly weaker or of unknown strength.
Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme codes: as in the frontier-map source
locator; ACPL = ArithmeticCouplingTheory, EHT = EdgeHodgeTheory, RIT = RenormalizedIntersectionTheory,
CSAR = CriticalScaleArithmeticRigidity, BOT = Bottcher.

## 0. Hardness calibration (applies to every route)

| Fact | Anchor | Consequence |
|---|---|---|
| `κ = κ(K_ζ) = #` distinct right-half zeros, even; a two-prime lattice carries it; RH ⇔ `κ = 0` ⇔ `κ ≤ 1` | HKT, AKLT [M] | every index route ends in one even integer |
| `κ < ∞` ⇔ finite off-line support ⇔ bounded heat counts ⇔ bounded cumulative collision charge ⇒ Lindelöf + zero-free half-plane | HKT, CDG [M]; `exists_nonrealZeroCount_le_iff_exists_collisionCharge_le` [L] | every finite-index waypoint is **≥qRH** |
| Bounded Weil kernel ⇔ RH: `‖K_ζ(u)‖ ≤ Re K_ζ(1)` ∀u ∈ ℚ₊ | RIT `riemannHypothesis_iff_castelnuovoSeveri` [L] | every boundedness target is RH |
| Coupling ≡ kernel: for any two pairs of distinct primes, bounded coupling `K(uv) − K(u) − K(v) + K(1)` on `⟨p,q⟩ × ⟨r,s⟩` ⇔ RH; one lattice `⟨p⟩ × ⟨q⟩` (`a, b ∈ ℤ`) decides; coupling growth rate `e^{σh}` ⇔ zero width `≤ σ`; local Hyers–Ulam constant `3`, no Diophantine input | ACPL `riemannHypothesis_iff_exists_bound_coupling`, `…_zpow`, `zetaZeroWidth_le_iff_coupling_rate`, `norm_sub_linear_le_three_mul` [L] | the coupling is not a softer invariant than the kernel |
| Cone: bounded coupling on `a, b ∈ ℕ` ⇒ RH or the zero width is not attained | ACPL `riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling` [L] | integer scales decide RH up to attainment |
| Glued state: `κ(φ_c) = κ + 1` at `∞` and at every prime | AKG `negIndex_weilArchState_eq_add_one` [L], `TheGluingFormulaAtEveryPlace` [M] | RH ⇔ `κ(φ_c) < 3` |
| No softening: Künneth/Hadamard powers RH-equivalent and all-or-nothing; `n₋(G⊗G) = 2n₊(G)n₋(G)` at every horizon | RIT [M]; EHT `NoSofteningAtResolution` [L] | tensor amplification never helps |
| Edge: RH ⇔ the complete Weil family of an admissible profile has no edge; without RH the edge is `≤ 2(log N)^β` infinitely often (`β > ¼`); a finite first edge is PSD with a zero mode; no edge ⇔ bounded coupling | EHT `TheEdgeOfTheCompleteWeilFamily`, `TheEdgeIsACrossing` [L]; ACPL `eventually_hyperplaneEdge_eq_top_iff_bounded_coupling` [L] | RH ⇔ the overlap flow never acquires a zero mode on `v₁^⊥` [D] |
| Universal regime: tilted spline PD on all vectors for `1 ≤ c ≤ (log N)^α`, every `α < 1/19`, floor `κ/(2c⁷)`, reserve `W ≥ (b/c²³)D_N` | CACT `eventually_tiltedUnitSpline_completeWeilMatrix_posDef_below_residual_ceiling` [L] | under ¬RH the tilted edge lies in `[(log N)^{1/19}, 2(log N)^{¼+}]` infinitely often [D] (Lean edge files use `α < 1/59`) |
| RH regime: tilted full space `α > ¼`, `v₁^⊥` `α > ½`; smooth nonnegative profiles (unitBump) on `v₁^⊥` at every `α > 0`; every `C²` profile at `β > ¼`; sinc at `≍ L(log L)²` | RAPT, RIT `riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log` [L]; EHT [L]; TM [M] | universal and smooth RH regimes use different profiles; no profile transfer |
| Ceilings of the universal method: residual `c⁵/log N` against floor² `c⁻¹⁴` gives `19`; separate shell payment is sharp at `c²/ε`, i.e. `c⁹` at `ε ∝ c⁻⁷`, giving confinement `exp(Cc¹⁶)` and exponent `16`; synthesis gives `4` | CACT, SSH `TheShellsAloneCostTheSquareOfTheOverlap` [L] | three exponents `1/19 < 1/16 < 1/4` organize the Σ problem |
| Packet identity: on atoms `F(n)/√n` the complete form is `J_N + ½A_N + Σ F²/n (s_c + e_N + δ_N − R) − Σ d_n F² +` (center − far cross + pole error + near overlap); at strict separation `log N − γ` cancels the prime diagonal exactly (`Λ ∗ 1 = log`) | ACPL `TheMertensPolarization`, `TheCompleteFormOnTheCoherentSector`, `completeWeilEnergy_packetVector_at_every_overlap` [L] | the prime side is squares minus an exact diagonal; the shell degree `d_n` is the only overlap-growing term |
| Localization: every nonpositive unit vector lies within `η` of a finite conductor sector; at growing overlap the sector has `log P ≍ c¹⁶/η` | ACPL `nonpos_localizes_uniformly_at_growing_overlap` [L] | localization is the confinement; useful only for `c ≤ (log N)^{1/16}` [D] |
| Aperture visibility: an isolated off-line pair of depth `δ` at height `ξ` in an RVM background is seen at aperture `a` iff `S_δ(a) = sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)` | ACS `ArchimedeanDominationIsBlindAtEveryDepth` [L] | edge dictionary at fixed aperture exists; transfer to atomic families missing |
| Collisions: `H(γ) ≤ C(1 + log|γ|/L) − Re Π_{F_L} + 4E_γ(L)`; at log scale the prime polynomial carries `O(1/log T)` of the Hecke defect; counts + linear explicit formula cannot bound `E`; fixed scale ⇔ log corridor (≥qRH); one constant at all dyadic scales ⇔ RH | CDG `HeckeDefectHorizontalMultiplicity`, `PrimePolynomialSelfAbsorption`, `FiniteStratumAndCorridorClassification`, `DyadicPoleNodalRHEquivalence` [L] | WD needs an input beyond counts and the linear explicit formula |
| Selection: every nontrivial prime-set flip is separated (ordinary or two-adic atomic Hodge margin); the diagonal coupling recovers any flip set; ζ and a `p`-flip never both have finite coupling index; Frobenius at infinity (`σ(ρ) = 1 − ρ̄` trivial) ⇔ RH | RIT `TheTwoAdicProbeSeparatesEveryPrimePattern`, ACPL `FlipTwinsCarryTheirIndexIntoTheCouplingForm`, EHT `FrobeniusAtInfinity` [L] | selection of ζ among prime flips is closed; selection is a margin statement, not a positivity producer |
| Paths: crossing-free path `A → I` ⇔ `A` PD; regularized version at every spline horizon ⇔ RH; axial→coupled homotopy has coupling form `t·L_aL_bK` (full index for `t > 0`, zero at `t = 0`) | EHT `IntegersAlongPaths`, `TheIndexComputedByDeformation`; ACPL `TheCouplingHomotopyIsCrossingFree` [L] | deformation needs noncrossing proved from the source |
| Falsification certificates: second upper periodic point of the Xi Donoghue map; repeated real root of a reversed Xi Jensen section; nonnegative Ritz velocity | BOT `XiDonoghueDynamics`, APT `Jensen/XiStrictRoots`, HM `RitzVelocity` [L] | finite tests for ¬RH; no converse mechanism |

## 1. Shared obstacle blocks

### S1. Complete Weil matrix at growing overlap
Routes: HF, SRT, AIP, ACS-atomic, ACT, CHMD-index; RW, EWU, OWU through the ground minimum; SC
through the common hyperplane.

Established:
- universal regime to `(log N)^{1/19}` with floor, literal `weilQuad ≥ 0` and pole-defect reserve
  [L]; fixed-overlap positivity for every `C²` profile on `[0, 1]` without real Fourier zeros [L];
- single Ramanujan modes `(log N)^A ≤ m ≤ N^θ`, `θ < ½`, `α < ¼`, `A > 8α`, every `C²` profile:
  energy `≥ ((1 − 2θ)/4) log m`; the exceptional set is empty there; nonpositive single modes below
  `N^θ` lie below `(log N)^A` [L];
- conductor averages at RH-complete overlap (`θ < ½`, `c²/log N → 0`): nonpositive fraction and
  dimension `o(N^θ)` [M]; polynomial-conductor complement coercivity for `α < 1/16` [M];
- exact packet identities at strict separation and at every overlap; affine incidence energy as an
  exact CRT sum of squares `Σ b_p² v_p + (Σ b_p μ_p)²` on complete periods [L];
- prime-incidence calculus: `√(p−1)/p` times a prime mode is `1_{p|n} − 1/p`; jumps are
  incidence events; sharp prime–pole cost `S_Q = log Q + O(1)`; sharp literal residual scale
  `(log Q)² L_Q`; successor + dyadic rigidity with sharp constant `3/4`, kernel = constant packet
  [M, CSAR files read L];
- shells: separate payment sharp at `c²/ε`; joint top-band shell–pole coefficient
  `O_φ(G(c + log N))` uniformly `1 ≤ c ≤ N/4` [L];
- localization in a finite conductor sector at fixed `c` and, with sector size `exp(c¹⁶/η)`, at
  growing `c` [L];
- growing-packet prime–pole cancellation for packets up to `exp(√log Y/23040000)` with remainder
  `exp(−√log Y/7680000)` [M]; mechanism files for prefix/terminal reserves, variable cutoffs and
  weighted conductor cross bounds [L];
- edge, threshold curve, crossing theorem, aperture visibility law (§0) [L].

| | Obstacle |
|---|---|
| A1 | Explicit horizon `N₀` for the `1/19` theorem (the theorem is eventual) |
| A2 | Propagate the `1/19` exponent into the EHT edge window and crossing theorem (Lean uses `powerLogPositivityExponent = 1/59`) |
| A3 | Edge dictionary: compose the aperture visibility law `S_δ(a) > L` with the synthesis receivers (tilted, sinc, Steklov) to locate the overlap at which one off-line pair of depth `δ` at height `ξ` becomes visible; decide whether the edge of a fixed zero sits at exponent exactly `¼` |
| A4 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` |
| A5 | Size of the shell degree `d_n = Σ_m v_{nm}` at overlap `c` (no Lean bound exists); compare with the affine energy `½A_N` and the pole term |
| A6 | Compare CSAR rigidity and relative residual energies with the complete energy on fixed and slowly growing packets, through the every-overlap packet identity |
| A7 | Run the universal-regime proof for other profiles without real Fourier zeros (constants of floor, reserve, residual) |
| B1 | Positivity on `v₁^⊥` across the detection edge: tilted spline at its RH-complete rate, or any `C^∞` profile at any `α > 0` — **RH** (Σ1, Σ14) |
| B2 | Signed (quadratic-form) estimate on the low conductor band that beats the residual-versus-floor exponent `19` — **sub** (Σ13) |
| B3 | Joint shell–pole payment inside the all-vector reserve, removing the confinement exponent `16` that separate payment forces — **sub** below the synthesis threshold, **RH** at RH-complete overlap (Σ1c, Σ21) |
| B4 | Low-conductor spans below `(log N)^A`: sublinear nonpositive dimension does not bound the index — **sub** (Σ1g) |
| B5 | Conductors `N^{½} < m ≤ N`: frames or residual averages (Elliott–Halberstam type) — **sub** (Σ1h) |
| B6 | Sign-preserving profile transfer between the tilted spline and `C^∞` receivers — **sub** (Σ1d) |
| B7 | Polylogarithmic localization: nonpositive directions within `o(1)` of a sector of dimension `π((log N)^A)` at overlaps beyond `(log N)^{1/16}` — **sub** (Σ1c) |
| B8 | Joint payment of the non-arithmetic Gamma graph, signed diagonal, roots and poles on growing packets — **sub** (Σ1b) |

### S2. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD-index, SC, RIT-Künneth.

Established [L unless marked]: bounded finite-index kernels on countable free abelian groups,
including the Hecke lattice, are PD minus exactly `κ` positive multiples of distinct unitary
characters, `κ` minimal; index `≤ 1` on any abelian group ⇔ a positive character-mass
hyperplane; at index one, unitary-or-hyperbolic dichotomy, and cyclic subexponential ⇔ unitary
positive hyperplane ⇔ cyclic quadratic growth; finite index `≤ r` plus cyclic subexponential
growth ⇒ cyclic polynomial degree `≤ 2r` on any group (unitary second-difference filter);
index = right-zero count, collision mass `2(κ + excess)`, converse Krein–Langer for orbit kernels,
fixed-test horizon defect monotone with supremum the seen zeros, loop-Eisenstein band poles counted
by the Hodge defect [M].

| | Obstacle |
|---|---|
| A8 | Explicit capture stage for complete-cell indices (AID; pipeline card in progress) |
| B9 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ ⊠ K_ζ` (Σ5) |
| B10 | Classification of unbounded finite-index kernels of higher index (structure of the nonunitary part beyond index one) — **sub** |
| B11 | Emptiness of the loop-Eisenstein band poles by a noncancellation theorem for the constant term — **RH** |

### S3. Heat flow, collision charge, Hecke defect
Routes: WD, LA, TH, TT, HCF, SC-heat; census; HEF receivers.

Established [L unless marked]: heat state `κ(φ_c^{(t)}) = N(t)/2 + 1`, antitone, `1` for
`t ≥ 1/8` [M]; `N(t) = 2N↑(t)`, unheated window count `= 2·offLineOrder ≤ 2O(T)`; moving-barrier
`N(t) ≤ 2O(R(0))`; bounded `N` ⇔ bounded `O`; minimal-fibre falsification of every
`N(t) ≤ O(f(t))` law; integer theta collision readings as Fredholm indices, root-free stopping
certificate sound and eventually complete [M]; unit-window increments `n_off ≤ ΔO ≤ 2n n_off`,
`ΔO ≪ log²T` [M]; master inequality for `H(γ)` and `ΔO ≤ 2·max H·n_off`; at log scale the prime
polynomial is self-absorbed; counts + linear explicit formula cannot bound the Hecke defect (cluster
configuration with RVM and all critical zeros); fixed-`c` bounds are a 5-way TFAE independent of
`c` and imply the corridor `|Re ρ − ½| ≤ A/log|Im ρ|`, Lindelöf and a half-plane bound; finite
off-line stratum gives `E ≪ T^{−n}` at every fixed `c`; RH ⇔ one constant at every dyadic scale
`2^k c₀ log T`.

| | Obstacle |
|---|---|
| A9 | Stronger subconvexity exponent to lower the heat floor `2/3 = 4μ(½)` |
| A10 | Certified de Bruijn–Newman upper bound (Polymath15 in corpus normalization) as an index-one time for the heat state |
| A11 | One Lean statement: `ΔO(T) = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf (pieces exist) |
| A12 | Computable stopping prefix: certified interval bounds replacing compact minima |
| B12 | Subcritical heat count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub** |
| B13 | Pointwise heat horizon constant `< ½` — **≥qRH** |
| B14 | Source-side collision charge `< 2` on every window; no heat-index jump on `(0, 1/8]`; every `Λ_X = 0` — **RH** (Σ8, Σ16) |
| B15 | Cumulative charge `O(T) = o(N(T))` — **sub** (density one) |
| B16 | Uniform increment bound `ΔO ≤ M` or `o(log T)` — **LH** |
| B17 | Detection scale independent of zero gaps — **sub** (Π13) |
| B18 | Hecke defect at doubly-logarithmic scale `E_γ(¼ log log|γ|) = o(log|γ|)`, hence zero multiplicity `o(log|γ|)` — **sub** |
| B19 | `E_γ(c log T) = O(1)` on unit windows at one fixed `c` — **≥qRH** (corridor) |
| B20 | One constant for `E_γ` at every dyadic scale — **RH** (Γ4, Π15) |
| B21 | An arithmetic input beyond counts and the linear explicit formula that controls the non-holomorphic (conjugate-diagonal) functional `E_γ` — method obstacle, strength of its first output **sub** (Π15) |

### S4. Counts and producers
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity.

Established [M; ASRP/AKLT/CAF]: one-sided count ⇔ RH; prime-error budget `≥ 2 + γ − log 4π`;
linear theta RR, no quadratic Riemann inequality; quadratic RR on the scaling surface ⇔
renormalized Hodge index; every individual integer producer has slope `> 1`; ceilings `2 log 2`,
`1 + 1/((P+1)(P+2))`, `31/30`, `exp(−0.87n)`; growing-alphabet alternating producers give
`ψ, θ ≤ (1+ε)x + C_ε log²x`; every positive-power frequency band `K = ⌈N^δ⌉` of the Chebyshev
cyclotomic remainder retains the full infimal exponent `2Θ` [L].

| | Obstacle |
|---|---|
| A13 | Same-order mixed-jet recovery for `≥ 3` primes |
| A14 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer |
| B22 | `ε`-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3) |
| B23 | Any unconditional source input at square-root precision — **RH** (Π2) |
| B24 | Characteristic-0 quadratic effectivity: an unconditional Serre-dual `h⁰` — **RH** (Π11) |
| B25 | Near-band cyclotomic energy `O(N^{3/2+ε})` (3/4 strip) on any positive-power band — **≥qRH** (Π16) |

### S5. Carriers, gluing, coupling and selection
Routes: SC, ACS, HF; Γ-candidates.

Established [L unless marked]: coupling calculus (Künneth splitting, separability ⇔ zero
coupling, characters, polarization `C_K(u, v) = B(T_{u⁻¹}f − f, T_v f − f)`, antidiagonal
`C(u, u⁻¹) = 2(K(1) − Re K(u))`, coupling Laplacian); mixed differences see every seen zero,
`κ(L_aL_bK_ζ) = κ(K_ζ)`; bounded-coupling and rate theorems; cone theorem; single-lattice finite
stratum; curve coupling bounded ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius span, golden datum
unbounded on every pair of towers; coupling form selective (golden datum infinite index, flips
recovered); two primes outside `p` carry the full affine state inside `ℤ[1/pqr]` at every
principal-unit depth; principal `S`-unit logarithms dense iff `|S ∖ T| ≥ 2`; carrier classification
for additive `H ≤ ℚ` (finite index with continuous dilation iff `H ∈ {{0}, ℚ}`) [M]; coupled
assembly with `|S| ≥ 2` carries `κ + 1`, primes `≤ e^{2L+8}` exact on log-height `≤ L` [M];
separable assemblies blind or overcounting [M]; global pole = extremal weight, dense for two primes
[M].

| | Obstacle |
|---|---|
| A15 | `𝔽_q(X)` calibration: local walls at higher-degree places, global Hecke product formula, archimedean Weil state of a curve |
| B26 | Exact sum-of-squares identity for Weil's dilation form on the boost hyperplane (or on one two-prime lattice) — **RH** (Σ21, Γ) |
| B27 | Bounded coupling on one two-prime lattice — **RH** (Σ20) |
| B28 | Cone attainment: bounded coupling on `⟨p⟩₊ × ⟨q⟩₊` excludes the unattained-width alternative — **sub** (a pure implication) |
| B29 | Zero-independent selection at the trivial gauge point — **RH** (Γ1) |
| B30 | Frobenius at infinity: a correspondence acting as conjugation on the divisor — **RH** (Γ4) |
| B31 | Selection among unimodular (torus) gauges with `S_N/H_N → 1` and among functional-equation twins without Euler product — **sub** (Γ12, Γ15) |

## 2. Live routes

### WL — prime lag / Weil–Li energy
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔
RH + simple; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; arithmetic Bézout; Landau-window
cost `(2 log 2 − ε)mn`; Adams threshold `2^{qr}`; producers to the main term [M].
- A: A13, A14.
- B: one-sided prime-error bound (**RH**, Π1); B22; joint Möbius-moment / Mertens / sawtooth payment
  at square-root precision (**RH**, Π5).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0` ∀A ⇔ RH; floors `≥ mass/5000` to `181/500`, `≥ mass/8000` up to
`A₊ ∈ (181/500, ½)`; sinc multiple `K` gives positivity on tests in `[−R, R]` with
`288e⌈1 + e^{2(R+1)}⌉ < K/(4K_τ)` [M]; fixed-test horizon index ties apertures to the edge [L].
- A: certified positivity past the two-prime aperture `r ≥ ½ log 3`; A3 (aperture visibility law is
  the RW-native edge dictionary).
- B: all-aperture sign (**RH**, Σ1); subexponential floor for `μ₀` (**≥qRH**); depth-weighted branch
  needs an all-window mass bound (any bound `W` forces squared depth `≤ W`) (**≥qRH**).

### FU — Fourier/Abel prime scheduling
Established: completed Abel moment bounded above ⇒ RH; narrow-window negative prime channel [M].
- A: none identified.
- B: joint bound of seed, drift, prior, cross-block and endpoint terms (**RH**, Σ).

### CFC — first-clock sine coefficient
Established: RH ⇔ coefficient `≥ −C` on the aperture tail; unbounded below under ¬RH;
phase-natural transport is the identity [M].
- A: none.
- B: source lower bound retaining prime, archimedean and endpoint terms (**RH**, Σ).

### RP — normalized prime history
Established: RH ⇔ history `≥ −B(K+2)` eventually; unconditionally below `−δ(K+2)` cofinally;
finite prime-clock density cancellation [M].
- A: none.
- B: high-LCM pairs, moving core and singular transport at linear scale (**RH**, Σ/Π).

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts [M].
- A: explicit shift threshold per order.
- B: all-order / all-shift positivity (**RH**, Σ4).

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`, RH ⇔ trivial point typical;
cyclotomic remainder `≥ 0`; far modes `≤ 288N√(N+1)`; every positive-power band retains the
infimal exponent `2Θ` [L]; Dirichlet inputs uniform for `q ≤ (log x)^A`; rough-packet large sieve;
finite prime-clock cancellation; producers at the main term [M].
- A: none beyond the Siegel–Walfisz range.
- B: moving-scale half-power cancellation (**RH**, Π2); B25 (**≥qRH**); head/leaf signed
  cancellation of finite prime clocks (Σ); trivial-point typicality (**RH**, Γ1).

### TT — theta seam / Wold
Established: seam, tail, Wold receivers; `t < ½` threshold; truncated theta transform
`= −seed·B_N(ρ)` at zeros; two-horizon windowed aperture modes [M].
- A: none.
- B: all-test directed covariance or complete odd positivity (**RH**, Σ3).

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every Xi Jensen polynomial
splits; RH ⇒ reversed Xi Jensen sections have only simple real roots, so a repeated root refutes RH
[L]; RH ⇒ Ritz branches of the Xi heat-moment form move strictly left [L]; `λ_t log t → 0` ⇔ every
fixed-depth strip contains all high zeros; right-half squared-depth moment `o(V)` [M].
- A: explicit horizon per fixed degree; A9.
- B: all-degree / all-height signs (**RH**, Σ4); uniform tail narrowing (**≥qRH**); shrinking-scale and
  exceptional-height control (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; finite-matrix index laws along
paths; regularized deformation of every fixed-width spline horizon ⇔ RH [L].
- A: none.
- B: matrix-complete decomposition with integer trace `< 1` on every disc (**RH**, Σ8); a
  source-driven noncrossing path (Σ19).

### HF — Hodge/Hecke/complete cells
Established: S1 in full; Haar/prime-edge Gamma reserve; full Weil index `≤ R + A` for `R` coarse
cells; collided-form receivers; heat Hodge defect `= N(t)/2`; quadratic RR ⇔ Hodge index;
loop-Eisenstein band poles = Hodge defect [M]; packet identities [L]; Frobenius at infinity ⇔ RH [L].
- A: A1–A7; A8.
- B: B1–B8; Hecke invariance of the collided form (**RH**, Γ4); RR branch: unconditional Serre-dual
  `h⁰` (**RH**); B11.

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; prime wave `O(e^{|u|/2})`; every Haar piece except the
first-prime coarse layer has uniform finite index; Gamma graph pays the prime-two block; growing
Euler head alone unbounded; full prime window cancels the head pole on fixed packets and on growing
packets up to `exp(√log Y/23040000)` [M].
- A: fixed-cell first-prime / coarse / polar bookkeeping.
- B: uniform coarse-size control (finite index, **≥qRH**); odd-sector sign (**RH**, Σ3); B8.

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; `I₇(a) ≥ 0` on `0 < a < ½`; heated orthant signs all ranks;
all-rank signed-center positivity ⇔ RH; Ritz velocity identity [L/M].
- A: rank-8 strictness; ranks 9, 10.
- B: all-rank sign (**RH**, Σ4); rank-uniform signed flux payment (Σ4).

### RN — renewal
Established: compact cone-positive renewal operator with exact regularized determinant [M].
- A: none.
- B: directed mixed prime + Gamma `≥` pole (Σ); real spectrum from cone positivity fails; native
  unregularized synthesis is a no-go (Σ6).

### WD — Ward / collision / heat
Established: S3 in full; integer theta collision readings and Fredholm index; low-window
sectoriality; transition law; seam-smooth prefixes; root-free stopping rule; unit-window increments;
master inequality; log-scale classification of the Hecke defect (self-absorption, corridor TFAE,
dyadic RH equivalence, explicit-formula no-go) [L/M]. `[P]` a mollified-corridor / finite-theta card
is in `2-fully-proven` without Lean.
- A: A9, A10, A11, A12; formalization of the `[P]` card.
- B: B12–B21; vanishing global depth energy as `t ↓ 0` (**RH**); tower branch arithmetic index ceiling
  (**≥qRH**).

### LI — guarded history zeros
Established: `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order [M].
- A: none.
- B: pay the outside budget at every guarded zero (Σ).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packet light-Gram identity; negative
finite-cutoff pairings of the Abel clock [M]; Xi Donoghue map fixes `i` with multiplier in
`(77/85, 1)`, RH makes `i` its only upper periodic point [L].
- A: none.
- B: uniform lower bound after complete source assembly (Σ); no converse to the Donoghue
  falsification criterion.

### PM — physical / complete-energy realization
Established: complete-energy and gauge-mass receivers; half-damping admission; escape alternative
[M]; regularized Gauss–Mayer operator nuclear of order 0, Fredholm determinant, first fixed-point
trace `= ζ(w) +` corrections continued to `Re w > −1` [L]; algebraic scattering transport real on
both the critical parabola and `(¼, ∞)` only for horizontal lines [L].
- A: higher-iterate traces of the regularized Gauss–Mayer operator.
- B: cofinal complete-energy bound as `ε ↓ 0` (**RH**); exterior tightness and exclusion of
  infinite-height escape (Γ/Π); faithful ζ/scattering determinant identity and off-line resonance
  exclusion (**RH**); half-parameter cusp selection (**RH**).

### JAS — joint ancestry
Established: positivity at growing logarithmic prime budget [M].
- A: none.
- B: square-root power budget (**RH**, Π).

### CTF — completion transfer
Established: Euler completion error `≤ 1/(n+1)`; equal limits of full and finite-source energies
[M].
- A: none.
- B: full-source energy decay by signed covariance cancellation (Π); `B X^ε` receiver in the inner
  cutoff (Π).

### HCF — two-grid Hankel
Established: both `log 2`/`log 3` grids with polar cancellation ⇔ RH; one grid aliases [M].
- A: fixed-degree checks.
- B: both grid signs at every degree and height (**RH**, Σ4).

### XN — Newton dynamics
Established: RH ⇔ ξ-Newton source margin on discs; nonnegative Laplacian of the margin [M];
Donoghue-map falsification criterion [L].
- A: none.
- B: cover every zero with nonnegative margin (**RH**, Γ).

### BAG — Bagchi recurrence
Established: RH ⇔ disc recurrence on every closed disc of the strip; Voronin universality [M].
- A: none.
- B: returns near every right-strip point including potential zeros (**RH**, Γ1).

### EWU — Euler weights
Established: RH ⇔ at every aperture some real weights make the full Weil functional nonnegative;
obstruction dual is a blind test [M].
- A: shares RW's fixed-aperture computations.
- B: nonnegative actual minimum at every aperture (**RH**, Σ1).

### GTA — transverse charge
Established: transverse-charge decay criterion; transverse energy pays each negative square [M].
- A: none.
- B: rank-uniform arithmetic transverse-energy decay (Σ4).

### OWU — odd Weil selectivity
Established: every `r > 27/50` has a smooth odd test on `[−r, r]` with `W_ζ > mass/25` and
`W_Liouville < −3 mass/10`; companion forcing and conductor horizon incompatible [M].
- A: positivity on all odd tests slightly beyond `27/50` (shared with RW).
- B: all-test / all-aperture odd sign (**RH**, Σ1).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH [M].
- A: none.
- B: coefficient cancellation (**RH**, Π).

### RB — Robin / Nicolas
Established: large counterexamples need growing prime cores; colossally abundant reduction [M].
- A: none.
- B: square-root remainder on primorials (**RH**, Π).

### SRT — square-root threshold / zero visibility
Established: S1 in full; depth-gap visibility; local count ⇒ bounded critical multiplicity, true for
density-one heights; deep zeros `o(V)`; Steklov full index for `β > 2`; unit-window collision
increments [M]; aperture visibility law [L].
- A: A1–A7; explicit horizons.
- B: B1–B8; tower branch arithmetic index ceiling (**≥qRH**); unattained-depth detection (Σ5).

### ACT — collar transport
Established: explicit collar threshold pays every modulus outside nine atom-dominated moduli [M].
- A: the nine remaining moduli.
- B: one fixed shift paying every profile including exterior primes (Σ1).

### AIP — arithmetic incidence positivity
Established: S1 in full; complete form = prime jump energy + nonnegative affine incidence energy +
signed shell/boundary terms [L]; all-aperture allocation receiver; full Weil index `≤ R + A` [M].
- A: A1, A5, A6; mixed Schur debit on fixed blocks.
- B: all-aperture allocation (**RH**); B2–B8.

### ACS — arithmetic Castelnuovo–Severi
Established: RH ⇔ effectivity ⇔ Hodge index ⇔ section count ⇔ Castelnuovo–Severi at rational scales
[L/M]; renormalized Hodge sign ⇔ scaling-surface Hodge ⇔ real Serre-dual quadratic RR package [M];
loop-Eisenstein band poles = Hodge defect [M]; isolated off-line pairs blind to archimedean
domination at every depth, visible iff `S_δ(a) > L` [L]; curve coupling bounded ⇔ unitary [L];
`𝔽₃` elliptic adelic chain to global spectral integral `ζ_E(u)/ζ_E(u/3)` and Weyl-series convergence
[M].
- A: measure-compatible Bruhat unfolding and constant-term evaluation on the `𝔽₃` loop group; S1
  A-items; A15.
- B: B24 (**RH**); a conformal correspondence over ℤ with factor `≠ 1` (**RH**, Γ10); census
  displacement (Π8); B1–B8; B11.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) < 3` → `κ = 0` → RH.
Established [L unless marked]: `κ(φ_c) = κ + 1` at every place and for primitive Dirichlet
L-functions; translation reading `1`, readings add; on `ℓ = 0` the form is Weil's dilation form plus
shell squares; stable gluing; pole pair invisible to the boost index [M]; carrier classification
[M]; heat-deformed state [M]; Künneth branch all-or-nothing [M]; coupled assemblies exact, separable
assemblies blind [M]; coupling ≡ kernel, one lattice decides, coupling rate = zero width, cone ⇒
RH or unattained width, finite stratum ⇒ RH from single-lattice coupling; axial→coupled homotopy
degenerate at `t = 0`; principal-unit and three-prime cores carry `κ + 1`.
Reading [D]: `K_ζ(u)` is, through the explicit formula, the normalized smoothed prime error in a
multiplicative window of fixed length at `u`; the coupling combines the window errors at `uv, u, v,
1`; boundedness of the coupling is window PNT at square-root precision (Π14).
- A: A15; A10 (heat calibration).
- B: independent `κ(φ_c) < 3`, i.e. positivity on `v₁^⊥` (**RH**, Σ1); B26 (**RH**); B27 (**RH**);
  B28 (**sub**); B14 on the heat branch (**RH**); B12 on the heat branch (**sub**); B9 for the
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
| PW-B (retired) | zero-independent source family at every nonreal strip point; optical flux `−16(Re s − ½)Im s·M₊M₋`, vanishing iff critical [M] | — | killed as a selector (fails at `3/4 + i`); survivor: half-parameter cusp `Λ(s) = 0` receiver, needs zero-selecting scattering rigidity (**RH**) |

## 4. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ (critical sign) | RW, FU, CFC, RP, PA, TT, LA, TG, HF, CHMD, TH, RN, WD (charge `< 2`), LI, SZ, EWU, GTA, OWU, SRT, ACT, AIP, HCF, SC (glued index); FEL, MSC, EGC, PTR, W1C |
| Π (precision) | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, SC (coupling = window PNT), WD (Hecke defect = conjugate diagonal); IRK |
| Γ (selection) | BAG, XN, PM, MC (typicality), ACS (conformal correspondence), HF (Frobenius at infinity); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF; PW-B (retired) |

Within Σ the routes meet the sign problem at one of five faces: the detection edge of the complete
Weil family (HF, SRT, AIP, ACS-atomic, ACT, SC, RW, EWU, OWU), the heat/collision integer (WD, LA,
SC-heat, TG), rank/degree uniformity (TH, HCF, PA, GTA, LA-Jensen), scheduled prime sums (FU, CFC,
RP, SZ, LI, FEL, EGC), and realization (RN, PTR, W1C). In the complete Weil cluster the edge is
organized by three exponents of the overlap `c = (log N)^α`: `1/19` (residual versus floor, where the
universal method stops), `1/16` (confinement, intrinsic to separate shell payment), `¼` (synthesis,
where positivity becomes RH). SC and WD each carry a second, Π-type target: SC the window prime
error read through the coupling, WD the conjugate-diagonal Hecke defect.
