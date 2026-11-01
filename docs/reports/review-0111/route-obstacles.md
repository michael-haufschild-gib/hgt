# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates and the retired PW-B branch of the frontier map,
checked against the Lean corpus at `6e0189d741` and the working tree. For every route the report
gives what is established, the obstacles that are **(A) just work** and the obstacles that are
**(B) open mathematics** (no known solution). Just work means known mathematics, finite computation,
effectivization, or composition of proved statements.

Evidence:
- `[L]` Lean statement or module docstring read.
- `[U]` Lean file unfinished or not yet integrated.
- `[M]` frontier-map or killed-routes entry, Lean not re-read.
- `[D]` derived here from `[L]` statements, not formalized.

Strength of a B-item: **RH** equivalent to RH; **≥qRH** implies Lindelöf and a zero-free half-plane;
**LH** implies Lindelöf; **sub** strictly weaker or of unknown strength.

Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme codes follow the frontier-map source
locator. Further codes: ACPL = ArithmeticCouplingTheory, EHT = EdgeHodgeTheory,
HWV = HodgeTheoryWithoutVarieties, RIT = RenormalizedIntersectionTheory,
CSAR = CriticalScaleArithmeticRigidity, BOT = Bottcher.

## 0. Hardness calibration (applies to every route)

| Fact | Anchor | Consequence |
|---|---|---|
| `κ = κ(K_ζ) = #` distinct right-half zeros, even; a two-prime lattice carries it; RH ⇔ `κ = 0` ⇔ `κ ≤ 1` | HKT, AKLT [M] | every index route ends in one even integer |
| `κ < ∞` ⇔ finite off-line support ⇔ bounded heat counts ⇔ bounded cumulative collision charge ⇒ Lindelöf + zero-free half-plane | HKT, CDG [M] | every finite-index waypoint is **≥qRH** |
| `κ ≤ r` ⇔ translation-stable positive constraints of dimension `≤ r`; `κ ≤ r + 1` admits a character hyperplane of index `≤ r` (any abelian group, no growth assumption) | HKT `Index/TranslationStablePositiveConstraints`, `FiniteIndexCharacterHyperplane` [L] | finite index has a constraint classification; boundedness is extra |
| Bounded Weil kernel ⇔ RH | RIT `riemannHypothesis_iff_castelnuovoSeveri` [L] | every boundedness target is RH |
| Coupling ≡ kernel: one lattice `⟨p⟩×⟨q⟩` decides; rate = width; cone `a, b ≥ 0` ⇒ RH or unattained width | ACPL `riemannHypothesis_iff_exists_bound_coupling`, `riemannHypothesis_or_no_deepest_zero_of_bounded_coneCoupling` [L] | the coupling is not softer than the kernel |
| Glued state: `κ(φ_c) = κ + 1` at `∞` and at every prime | AKG `negIndex_weilArchState_eq_add_one` [L] | RH ⇔ `κ(φ_c) < 3` |
| No softening: Künneth/Hadamard powers RH-equivalent and all-or-nothing; `n₋(G⊗G) = 2n₊n₋` | RIT [M]; EHT `NoSofteningAtResolution` [L] | tensor amplification never helps |
| Kähler package: HR ∧ HL ⇔ strict HR; HR transports wherever HL holds on the HR locus; losing HR forces a primitive zero mode; RH ⇔ HL on the PSD locus along `1 ≤ c ≤ 2(log N)^β`, `β > ½`; Liouville = HL | HWV `TheKahlerPackage` [L]; `TheLiouvilleProperty` [U] | deformation costs nothing; all content is nondegeneracy |
| Edge: RH ⇔ no edge; a finite first edge is PSD with a zero mode; no edge ⇔ bounded coupling; under ¬RH tilted crossings i.o. in `[(log N)^α, 2(log N)^{¼+}]` | EHT `TheEdgeIsACrossing`, `TheEdgeOfTheCompleteWeilFamily` [L] (Lean `α < 1/59`) | RH ⇔ the overlap flow never acquires a zero mode on `v₁^⊥` |
| Critical overlap: for Denjoy–Carleman profiles `c*_N ≍ L(log L)²`, where tail energy = margin = synthesis error = `1/log N`; RH ⇔ positivity at every `K·c*_N`; `K` sees radius `½ log K + O(1)`; receivers stop at the quasi-analytic boundary `(loglog N)^{1+ε}` | TM `ReceiverRate/TheCriticalOverlapIsLogLogTimesLogSquared`, `ABoundedOverlapRateSeesASemilocalWindow`; HKT `TheReceiversEndAtTheQuasiAnalyticBoundary` [L] | the overlap axis is the aperture axis |
| Visibility law: an isolated off-line pair (depth `δ`, height `ξ`, RVM background) is seen at aperture `a` iff `S_δ(a) = sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)` | ACS `ArchimedeanDominationIsBlindAtEveryDepth` [L] | positivity at aperture `a` is a zero-free box below `2π exp(2π S_δ(a))` [D] |
| Rough regime, tilted spline: all vectors `1 ≤ c ≤ (log N)^α`, `α < 1/16`, floor `κ/(2c⁷)`; complement coercive `α < 1/9`; confinement `log R' ≤ Cc¹¹ + log Q₁`; packets `α < 1/8` | CACT `CompleteWeilPositivityBelowOneSixteenth`, `AsymmetricTwoRegionConductorReserve` [L]; `BilinearConductorResidualsAndOneEighthPackets` [U] | under ¬RH the tilted edge lies in `[(log N)^{1/16}, 2(log N)^{¼+}]` i.o. [D] |
| Receivers: tilted full space `α > ¼`, hyperplane `α > ½` (synthesis of order 2); smooth profiles on `v₁^⊥` at every `α > 0`; sinc/DC at `K·c*_N` | SSHA `TheSecondOrderSynthesis`, `TheOverlapLawAtEveryRoot`; RIT `riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log` [L] | the receiver threshold is a synthesis-accuracy threshold |
| Packet identity: complete form on atoms `F(n)/√n` = `J_N + ½A_N` + bounded diagonal − `Σ d_n F²` + boundary terms; `log N − γ` cancels the prime diagonal through `Λ ∗ 1 = log` | ACPL [M] | the shell degree `d_n` is the only overlap-growing non-square term |
| Stars: star of `d` = family at `(c⌊N/d⌋/N, ⌊N/d⌋)`, isometric for every weight; positivity descends; deep stars positive; counterterm flux `log d`; self-similar flux only for generalized von Mangoldt weights | HWV `StarsAreLowerHorizons`, `StarsOfTheCompleteWeilFamily`, `TheDivisorIdentitySelects` [L] | renormalization structure exists; ascent is open |
| Möbius renormalization: `W_{c,N} = −Σ_{d≥2} μ(d)·(star form of d) + W^{cop}`, unique exact star decomposition; `W^{cop}` = archimedean + poles + row-one primes + successor shells on coprime atoms | Möbius inversion on `gcd` + star isometry [D] | local-to-global positivity is a Möbius-cancellation statement |
| Hecke defect: prime polynomial carries `O(1/log T)` of it; counts + linear explicit formula cannot bound it; means `O_c(log U)` (`c < 22/51`); `o(log U)` ⇔ 100% critical-scale clustering; fixed scale ⇔ corridor (≥qRH); one constant over dyadic scales ⇔ RH | CDG `LogScaleHeckeDefect/*` [L] | WD needs an input beyond counts and the linear explicit formula |
| Selection: every nontrivial prime-set flip separated; diagonal coupling recovers flips; Frobenius at infinity ⇔ RH; partner saturation of resonant states ⇔ critical | RIT, ACPL [M]; EHT `FrobeniusAtInfinity`, RHTower `EisensteinResonantPartnerAngle` [L] | selection among prime flips closed; selection is a margin |
| Paths: crossing-free path `A → I` ⇔ `A` PD; axial→coupled homotopy degenerate at `t = 0` | EHT, ACPL [M] | deformation needs noncrossing proved from the source |
| Falsification certificates: second upper periodic point of the Xi Donoghue map; repeated real root of a reversed Xi Jensen section; nonnegative Ritz velocity | BOT, APT, HM [M] | finite tests for ¬RH; no converse mechanism |

## 1. Shared obstacle blocks

### S1. Complete Weil family across the critical overlap
Routes: HF, SRT, AIP, ACS-atomic, ACT, CHMD-index. Through the aperture axis also RW, EWU, OWU. SC
joins through the common hyperplane and the expected critical-scale identification.

Established:
- Rough regime of the tilted spline:
  - all vectors for every `α < 1/16`, with floor and pole-defect reserve [L];
  - polynomial-conductor complement coercive for `α < 1/9`, global negative index `≤ N^θ` [L];
  - confinement exponent `11` [L];
  - packets to `1/8` [U].
- Single Ramanujan modes `(log N)^A ≤ m ≤ N^θ` coercive for every `C²` profile [L].
- Conductor averages at `θ < ½` [M].
- Every `C²` profile without real Fourier zeros is positive on bounded overlap and has edge `→ ∞`;
  one `C^∞` profile carries both edge regimes [L].
- Receivers at `α > ¼` (tilted), every `α > 0` (smooth, hyperplane), every `K·c*_N` (sinc, DC);
  `K ↔ ½ log K` [L].
- Exact packet identities; prime-incidence calculus; sharp prime–pole cost `log Q`; sharp residual
  scale `(log Q)²/log N`; successor + dyadic rigidity with kernel the constant packet [M].
- Shells: separate payment sharp at `c²/ε`; joint top-band `O_φ(G(c + log N))` [L].
- Visibility law [L]; Weil floors through radius `181/500` and at `A₊` [M/L].

| | Obstacle |
|---|---|
| A1 | Fourth-order synthesis for the tilted spline. Its third derivative has bounded variation, so the Euler–Maclaurin synthesis of the smooth case (`TheEulerMaclaurinSynthesis`) applies with the Stieltjes remainder to order `4`. Expected receiver: RH ⇔ eventual positivity at `K(log N)^{1/8}` for every `K` (`α > 1/8`), plus the hyperplane analogue [D]. |
| A2 | Finish the bilinear conductor-residual theorem: positivity on fixed finite conductor packets and coercivity on polylogarithmic conductor subspaces for `α < 1/8` [U]. |
| A3 | Run the rough-regime proof for a Denjoy–Carleman or sinc profile up to `ε·c*_N`. At `ε·c*_N` the floor is `(log N)^{−O(ε)}` while every residual is polynomial in `c ≍ loglog N` [D]. |
| A4 | Edge dictionary for one off-line pair: compose the visibility law with the `K ↔ ½ log K` transfer. In the RVM model this gives edge `≲ C e^{2a(ρ)}·c*_N`, with `a(ρ)` the visibility aperture of `ρ` [D]. |
| A5 | Propagate the `1/16` exponent into the EHT edge-window and crossing theorems (Lean uses `powerLogPositivityExponent = 1/59`). |
| A6 | Explicit horizon `N₀` for the `1/16` theorem (the theorem is eventual). |
| A7 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²`. |
| A8 | Size of the shell degree `d_n = Σ_m v_{nm}` at overlap `c`; comparison with `½A_N` and the pole term (no Lean bound exists). |
| A9 | Compare CSAR rigidity and relative residuals with the complete energy through the every-overlap packet identity, on fixed and slowly growing packets. |
| A10 | Rate for the smooth no-real-zero tilt profile at power-of-log overlap (the both-regimes profile has no rate). |
| A11 | Critical-scale identification: smooth-bump packets of the complete family at `K·c*_φ` reproduce Weil-correlation Grams of a test of radius `½ log K`. This links SC's ratCorr Grams to the complete matrix [D]. |
| A12 | Certified Weil positivity past the two-prime aperture `½ log 3`. Aperture positivity can be pushed to the range where every visible pair is excluded by verified zeros and explicit zero-free regions [D]. |
| B1 | Positivity at every multiple `K·c*_φ` (all-aperture Weil positivity) — **RH** (Σ1). |
| B2 | Joint shell–pole payment on all vectors, bringing the confinement exponent to `≤ 8` (the spline's critical overlap) — **sub** (Σ1c). |
| B3 | Low-conductor spans below `(log N)^A` — **sub** (Σ1d). |
| B4 | Conductors `N^{½} < m ≤ N` (Elliott–Halberstam type) — **sub** (Σ1e). |
| B5 | Joint payment of the non-arithmetic Gamma graph, signed diagonal, roots and poles on growing packets — **sub** (Σ1g). |
| B6 | Critical-scale residual sign: signed cancellation of the overlap residual at `K·c*_φ` — **RH** over all `K` (Π15). |
| B7 | Exact sum-of-squares identity for Weil's dilation form on one two-prime lattice — **RH** (Σ18). |

### S2. Kähler package, edge and stars
Routes: HF, ACS, SRT, AIP, TG, SC.

Established [L unless marked]:
- formal Kähler package, strictness, transport, crossing lemma;
- Liouville = HL, and RH ⇔ HL on the PSD locus [U];
- edge = crossing; Frobenius at infinity and its Hecke-similitude form;
- star isometry for every weight; positivity descent; deep-star positivity;
- divisor-identity selection.

| | Obstacle |
|---|---|
| A13 | Quantitative star range: explicit `M₀` and `α*` in `exists_star_positive_tiltedUnitSpline`, and the list of stars not yet in the universal regime at a given `(c, N)`. |
| B8 | HL on the positive locus of the overlap flow (a source-defined noncrossing mechanism) — **RH** (Σ2). |
| B9 | Star ascent: on primitive zero modes the coprime coupling dominates the Möbius-signed star sum — **RH** at all overlaps; **sub** inside the rough regime (Σ3). |
| B10 | Emptiness of the loop-Eisenstein band poles by a noncancellation theorem — **RH** (Σ19). |

### S3. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD-index, SC, RIT-Künneth.

Established:
- bounded finite-index kernels on free abelian groups are PD minus `κ` unitary characters [L];
- index-one dichotomy [L];
- `κ ≤ r` ⇔ translation-stable positive constraints [L];
- index = right-zero count; collision mass `2(κ + excess)` [M];
- converse Krein–Langer for orbit kernels [M];
- explicit quadratic capture stage for complete-cell indices [L].

| | Obstacle |
|---|---|
| B11 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ⊠K_ζ` (Σ4). |

### S4. Heat flow, collision charge, Hecke defect
Routes: WD, LA, TH, TT, HCF, SC-heat; census; HEF receivers.

Established:
- heat state `N(t)/2 + 1` [M]; bounded `N` ⇔ bounded `O` [M];
- moving barrier `N(t) ≤ 2O(R(0))` [M];
- Fredholm collision index; root-free stopping certificate [M];
- unit-window increments `n_off ≤ ΔO ≤ 2n·n_off`, `ΔO ≪ log²T` [M];
- master inequality for `H(γ)` [M];
- Hecke-defect hierarchy [L]:
  - self-absorption; counts-only no-go;
  - fixed-scale 5-way TFAE ⇒ corridor; finite stratum `E ≪ T^{−n}`;
  - dyadic RH equivalence, also zero-coordinate-free through finite integer-theta readings;
  - anti-nodal growth of the bare prime polynomial;
  - means `O_c(log U)` for `c < 22/51`, `O(U^η)` for `c < 2/3`;
  - almost-all `(6/5)loglog T/log T` corridor;
  - `o(log U)` ⇔ critical-scale clustering.

| | Obstacle |
|---|---|
| A14 | Integrate `μ(½) ≤ 33/200` [U] and transfer it to the heat floor `4μ(½) = 33/50` (size-only repair model is sharp at `2θ`). |
| A15 | Certified de Bruijn–Newman upper bound in corpus normalization as an index-one heat time. |
| A16 | One Lean statement: `ΔO(T) = o(log T)` ⇒ off-line sparsity ⇒ Lindelöf (pieces exist). |
| A17 | Computable stopping prefix: certified interval bounds replacing compact minima. |
| B12 | Subcritical heat count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub**. |
| B13 | Pointwise heat horizon constant `< ½` — **≥qRH**. |
| B14 | Source-side collision charge `< 2` on every window; no heat-index jump on `(0, 1/8]` — **RH** (Σ5). |
| B15 | Cumulative charge `O(T) = o(N(T))` — **sub**. |
| B16 | Uniform increment bound `ΔO = o(log T)` — **LH**. |
| B17 | Detection scale independent of zero gaps — **sub** (Π13). |
| B18 | Hecke defect at doubly-logarithmic scale `o(log|γ|)`, hence multiplicity `o(log|γ|)` — **sub**. |
| B19 | Dyadic mean `o(log U)` at one `c < 22/51`, equivalently 100% of zeros within `κ/log T` for every `κ > 0` — **sub** (Π5). |
| B20 | `E_γ(c log T) = O(1)` on unit windows at one fixed `c` — **≥qRH**. |
| B21 | One constant for `E_γ` at every dyadic scale; equivalently uniform finite-theta aperture readings — **RH** (Γ4, Π5). |
| B22 | An arithmetic input beyond counts and the linear explicit formula that controls the conjugate diagonal — method obstacle; first output **sub**. |

### S5. Counts and producers
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity; census.

Established:
- one-sided count ⇔ RH [M]; prime-error budget `≥ 2 + γ − log 4π` [M];
- linear theta RR; quadratic RR ⇔ renormalized Hodge index [M];
- individual producers have slope `> 1`; growing-alphabet producers reach the main term [M];
- every positive-power Chebyshev band retains `2Θ` [L];
- census: simple critical `≥ 0.67250071` by cosine-kernel pinching [L]; 70% dichotomy [M].

| | Obstacle |
|---|---|
| A18 | Same-order mixed-jet recovery for `≥ 3` primes. |
| A19 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer. |
| A20 | Census: the cosine prime Gram certificate on the same window as the pinching credit [U]; stabilizer calibration at `β = 2`. |
| B23 | `ε`-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3). |
| B24 | Any unconditional source input at square-root precision — **RH** (Π2). |
| B25 | Characteristic-0 quadratic effectivity: an unconditional Serre-dual `h⁰` — **RH** (Π11). |
| B26 | Near-band cyclotomic energy `O(N^{3/2+ε})` on a positive-power band — **≥qRH** (Π10). |
| B27 | Signed prime surplus `S ≤ (1/18 + o(1))N` at bandwidth `4/3`, or `E(1/9) ≤ 4` — **sub** (Π7). |

### S6. Carriers, gluing, coupling and selection
Routes: SC, ACS, HF; Γ-candidates.

Established:
- coupling calculus; mixed differences see every seen zero [M];
- bounded-coupling, rate and cone theorems [L];
- curve coupling bounded ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius span [M];
- carrier classification; unique proper-subgroup split [L];
- coupled assemblies exact, separable assemblies blind [M];
- global pole = extremal weight [M];
- prime-set flips separated; flip-twin Wirsing constants positive [L];
- self-similar counterterm selects `Λ` [L].

| | Obstacle |
|---|---|
| A21 | `𝔽_q(X)` calibration: local walls at higher-degree places, global Hecke product formula, archimedean Weil state of a curve. |
| A22 | `𝔽₃` loop chain: measure-compatible unfolding, Eisenstein convergence, constant term. |
| B28 | Bounded coupling on one two-prime lattice — **RH** (Σ17). |
| B29 | Cone attainment: bounded coupling on `⟨p⟩₊ × ⟨q⟩₊` excludes the unattained-width alternative — **sub**. |
| B30 | Zero-independent selection at the trivial gauge point — **RH** (Γ1). |
| B31 | Frobenius at infinity as an operator: a conformal correspondence of factor `≠ 1`, or a Hecke similitude of the collided form — **RH** (Γ4). |
| B32 | Unimodular gauges with `S_N/H_N → 1`; functional-equation twins without Euler product; zero-density flip twins at `κ = 0` — **sub** (Γ12, Γ15). |

### S7. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established:
- regularized Gauss–Mayer operator: cutoff renormalization; nuclear of order 0; global Fredholm
  determinant entire in `λ` [L];
- source holomorphy; word traces for `Re w > 1`; first trace continued to `Re w > −1` [L];
- `D = A + ζ(w)B`, residue `B(1,λ)`; negative-unit cancellation `B(w,−1) = 0`; raw determinants
  converge while raw norms diverge [L];
- resonant Eisenstein states: truncated-norm exponent `1 − Re ρ`, partner-angle law [L];
- algebraic recentering of the critical parabola impossible [L];
- lossless realization needs infinitely many resonances; Vitali [M].

| | Obstacle |
|---|---|
| A23 | General-`λ` complementary finite-part limit for the Mayer determinant; primitive-geodesic coding and the Mayer–Selberg identity `Z(s) = D(2s,1)·D(2s,−1)` up to the regularization (known mathematics, formalization heavy). |
| B33 | Off-line resonance exclusion (zero-selecting scattering rigidity) — **RH** (Γ4, Σ8). |
| B34 | A zero-free region for ζ near `Re s = 1` from the Mayer operator and the Maass–Selberg relations alone, without the Euler product — **sub**. |
| B35 | Source-faithful realization: prime-faithful lossless port (PTR), centred Ising limit (W1C), directed renewal sign (RN) — **RH** (Σ8). |

### Route-specific items
| | Obstacle | Routes |
|---|---|---|
| A24 | Theta Hankel rank-8 strictness; ranks 9 and 10 | TH |
| A25 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF |
| A26 | The nine atom-dominated moduli of the collar shift | ACT |
| A27 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD |
| A28 | Toeplitz minors of the Xi centre sequence beyond PF₃₇ | LA; 2.4 of the summary |
| B36 | Odd-sector bound `R ≤ ½` — **RH** (Σ7) | CHMD, TT |
| B37 | All-rank / all-degree theta, heat, Jensen, PF and two-grid signs — **RH** (Σ6) | TH, LA, HCF, PA, GTA |
| B38 | Lower bounds for scheduled prime energies — **RH** (Σ20) | FU, CFC, RP, SZ, LI, FEL, EGC |

## 2. Live routes

### WL — prime lag / Weil–Li energy
Established [M]:
- critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔ RH + simple;
- `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split;
- Landau-window cost `(2 log 2 − ε)mn`; Adams threshold `2^{qr}`;
- `{2,3}` stencil `ψ ≤ 23x/20`; growing-alphabet producers give `ψ, θ ≤ (1+ε)x + C_ε log²x`.
- A: A18, A19.
- B: B24 (one-sided count, Π1); B23; joint Möbius-moment / Mertens / sawtooth payment at
  square-root precision (**RH**).

### RW — restricted Weil ground minimum
Established:
- `μ(A) ≥ 0` ∀A ⇔ RH; floors `≥ mass/5000` to `181/500` [M];
- explicit `A₊ > 181/500` with floor `≥ mass/8000`, via the one-prime dilation modulus [L/M];
- a multiple `K` of the critical overlap sees radius `½ log K + O(1)` [L]; visibility law [L].
- RW is the aperture axis of C1: positivity at aperture `A` is a zero-free box below
  `2π exp(2π S_δ(A))` [D].
- A: A12; A4.
- B: B1 (all-aperture sign, **RH**); subexponential floor for `μ₀` (**≥qRH**); the depth-weighted
  branch needs an all-window mass bound (**≥qRH**).

### FU — Fourier/Abel prime scheduling
Established: completed Abel moment bounded above ⇒ RH; narrow-window negative prime channel [M].
- A: none identified.
- B: B38 (joint seed, drift, prior, cross-block and endpoint terms).

### CFC — first-clock sine coefficient
Established: RH ⇔ coefficient `≥ −C` on the aperture tail; unbounded below under ¬RH;
phase-natural transport is the identity [M].
- A: none.
- B: B38 (source lower bound retaining prime, archimedean and endpoint terms).

### RP — normalized prime history
Established: RH ⇔ history `≥ −B(K+2)` eventually; unconditionally below `−δ(K+2)` cofinally; finite
prime-clock density cancellation [M].
- A: none.
- B: B38 with high-LCM pairs, moving core and singular transport at linear scale.

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts [M].
- A: A25 (explicit shift threshold per order).
- B: B37 (all-order / all-shift positivity).

### MC — Möbius cancellation
Established:
- half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [M];
- cyclotomic remainder `≥ 0`; far modes `≤ 288N√(N+1)` [M];
- every band `K = ⌈N^δ⌉` retains `2Θ`; far energy `≤ N^{2Θ+ε}/K` [L];
- Dirichlet inputs uniform for `q ≤ (log x)^A`; producers at the main term [M].
- Seam [D]: the unique exact star decomposition of the complete Weil form has weights `−μ(d)`, so
  local-to-global positivity on the Hodge side is a Möbius-cancellation statement on star energies.
- A: none beyond the Siegel–Walfisz range.
- B: moving-scale half-power cancellation (B24, **RH**); B26 (**≥qRH**); head/leaf signed
  cancellation of finite prime clocks (Σ); B30 (**RH**).

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; `t < ½` threshold; truncated theta transform
`= −seed·B_N(ρ)` at zeros; two-horizon windowed aperture modes [M].
- A: none.
- B: B36 (all-test directed covariance or complete odd positivity).

### LA — Laguerre/Jensen and local heat
Established:
- every fixed Jensen degree eventually real-rooted; RH ⇔ every Xi Jensen polynomial splits; a
  repeated root of a reversed section refutes RH [M];
- Ritz branches move strictly left under RH [M];
- `λ_t log t → 0` ⇔ every fixed-depth strip contains all high zeros; right-half depth moment
  `o(V)` [M];
- `ζ(5/6+it) ≪ t^{2/53} log t` [L]; `μ(½) ≤ 33/200` [U].
- A: A25; A14; A28.
- B: B37 (all degrees / all heights); uniform tail narrowing (**≥qRH**); shrinking-scale and
  exceptional-height control (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; finite-matrix index laws along paths;
regularized deformation of every fixed-width spline horizon ⇔ RH [M]; Kähler transport free [L].
- A: none.
- B: B14 (integer trace `< 1` on every disc); B8 (a source-driven noncrossing path).

### HF — Hodge / Hecke / complete cells
Established:
- S1 and S2 in full; Haar/prime-edge Gamma reserve; full Weil index `≤ R + A` for `R` coarse
  cells [M];
- heat Hodge defect `= N(t)/2`; quadratic RR ⇔ Hodge index; loop-Eisenstein band poles = Hodge
  defect [M];
- packet identities [M]; Frobenius at infinity ⇔ RH [L];
- Kähler package, stars, divisor identity [L]; Liouville = HL [U].
- A: A1–A13; A27.
- B: B1–B10; Hecke invariance of the collided form (B31, **RH**); RR branch B25 (**RH**).

### CHMD — causal hyperbolic–modular duality
Established:
- RH ⇔ `R ≤ ½` on the odd sector; prime wave `O(e^{|u|/2})` [M];
- every Haar piece except the first-prime coarse layer has uniform finite index [M];
- Gamma graph pays the prime-two block; growing Euler head alone unbounded [M];
- full prime window cancels the head pole on fixed and growing packets [M].
- A: A27.
- B: uniform coarse-size control (B11, **≥qRH**); B36 (**RH**); B5.

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; `I₇(a) ≥ 0` on `0 < a < ½`; heated orthant signs at all
ranks; all-rank signed-center positivity ⇔ RH; Ritz velocity identity [M].
- A: A24.
- B: B37; rank-uniform signed flux payment.

### RN — renewal
Established: compact cone-positive renewal operator with exact regularized determinant [M].
- A: none.
- B: directed mixed prime + Gamma `≥` pole; real spectrum does not follow from cone positivity;
  native unregularized synthesis is a no-go (B35).

### WD — Ward / collision / heat
Established: S4 in full [L/M]; integer theta collision readings and Fredholm index; low-window
sectoriality; seam-smooth prefixes; root-free stopping rule; unit-window increments; master
inequality; the full Hecke-defect hierarchy including means, clustering equivalence and the
zero-coordinate-free finite-theta RH equivalence [L].
- A: A14, A15, A16, A17.
- B: B12–B22; vanishing global depth energy as `t ↓ 0` (**RH**); tower-branch index ceiling (B11).

### LI — guarded history zeros
Established: `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order [M].
- A: none.
- B: B38 (pay the outside budget at every guarded zero).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packet light-Gram identity; negative
finite-cutoff pairings of the Abel clock [M]. The Xi Donoghue map fixes `i`, and under RH `i` is its
only upper periodic point [M].
- A: none.
- B: B38 (uniform lower bound after complete source assembly); no converse to the Donoghue
  falsification criterion.

### PM — physical / complete-energy realization
Established:
- Gauss–Mayer operator [L]:
  - renormalized cutoffs; nuclear of order 0; global Fredholm determinant;
  - holomorphy in the source parameter; positive-power word traces; first trace continued to
    `Re w > −1`;
  - `D = A + ζ(w)B` with residue `B(1,λ)`; removability iff `B(1,λ) = 0`; simple pole for small
    `λ ≠ 0`;
  - negative-unit cancellation `B(w,−1) = 0`; raw finite-branch determinants converge;
  - complementary-determinant identity.
- Resonant Eisenstein states [L]:
  - truncated norm `|Λ(ρ−1)|² Y^{1−Re ρ}/(1 − Re ρ)`;
  - partner angle `cos² = 4Reρ(1 − Reρ)`, saturated iff critical;
  - resonant state = Cauchy wave packet of the continuum.
- Complete-energy and gauge-mass receivers, half-damping admission, escape alternative [M].
- Rational and algebraic recentering of the critical parabola are impossible [L].
- Reading [D]: with Mayer's identity, ζ zeros in `½ < Re w < 1` are eigenvalue-±1 events of the
  regular part `R(w)`. PM's selection wall is Frobenius at infinity in the form of partner
  saturation.
- A: A23.
- B: B33 (**RH**); B34 (**sub**); cofinal complete-energy bound as `ε ↓ 0` (**RH**); exterior
  tightness and exclusion of infinite-height escape (Γ/Π); half-parameter cusp selection (**RH**).

### JAS — joint ancestry
Established: positivity at growing logarithmic prime budget [M].
- A: none.
- B: square-root power budget (B24).

### CTF — completion transfer
Established: Euler completion error `≤ 1/(n+1)`; equal limits of full and finite-source energies [M].
- A: none.
- B: full-source energy decay by signed covariance cancellation (Π); `B X^ε` receiver in the inner
  cutoff (Π).

### HCF — two-grid Hankel
Established: both `log 2`/`log 3` grids with polar cancellation ⇔ RH; one grid aliases [M].
- A: A25 (fixed-degree checks).
- B: B37 (both grid signs at every degree and height).

### XN — Newton dynamics
Established: RH ⇔ ξ-Newton source margin on discs; nonnegative Laplacian of the margin [M].
- A: none.
- B: cover every zero with nonnegative margin (**RH**, Γ).

### BAG — Bagchi recurrence
Established: RH ⇔ disc recurrence on every closed disc of the strip; Voronin universality [M].
- A: none.
- B: B30 (returns near every right-strip point including potential zeros).

### EWU — Euler weights
Established: RH ⇔ at every aperture some real weights make the full Weil functional nonnegative;
the obstruction dual is a blind test [M].
- A: A12 (shared with RW).
- B: B1 (nonnegative actual minimum at every aperture).

### GTA — transverse charge
Established: transverse-charge decay criterion; transverse energy pays each negative square [M].
- A: none.
- B: B37 (rank-uniform arithmetic transverse-energy decay).

### OWU — odd Weil selectivity
Established: every `r > 27/50` has a smooth odd test on `[−r, r]` with `W_ζ > mass/25` and
`W_Liouville < −3 mass/10` [M]; companion forcing and conductor horizon incompatible [M].
- A: A12 (odd tests slightly beyond `27/50`).
- B: B1 (all-test / all-aperture odd sign).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH [M].
- A: none.
- B: coefficient cancellation (B24).

### RB — Robin / Nicolas
Established: large counterexamples need growing prime cores; colossally abundant reduction [M].
- A: none.
- B: square-root remainder on primorials (B24).

### SRT — square-root threshold / zero visibility
Established: S1 in full; depth-gap visibility; local count ⇒ bounded critical multiplicity
(density-one heights); deep zeros `o(V)`; Steklov full index for `β > 2`; unit-window increments
[M]; visibility law [L].
- A: A1–A12.
- B: B1–B7; tower-branch index ceiling (B11, **≥qRH**); unattained-depth detection (Σ4).

### ACT — collar transport
Established: explicit collar threshold pays every modulus outside nine atom-dominated moduli [M].
- A: A26.
- B: one fixed shift paying every profile including exterior primes (B1).

### AIP — arithmetic incidence positivity
Established: S1 in full; complete form = prime jump energy + nonnegative affine incidence energy +
signed shell/boundary terms [M]; all-aperture allocation receiver; full Weil index `≤ R + A` [M].
- A: A1, A2, A8, A9, A27.
- B: all-aperture allocation (B1, **RH**); B2–B6.

### ACS — arithmetic Castelnuovo–Severi
Established:
- RH ⇔ effectivity ⇔ Hodge index ⇔ section count ⇔ Castelnuovo–Severi at rational scales [L/M];
- renormalized Hodge sign ⇔ Serre-dual quadratic RR package [M];
- loop-Eisenstein band poles = Hodge defect [M];
- isolated pairs blind to archimedean domination, visible iff `S_δ(a) > L` [L];
- finite-index constraint classification [L]; curve coupling bounded ⇔ unitary [M];
- quantitative complete-cell source transfer at rate `N^{−1/2}` [L];
- `𝔽₃` elliptic adelic chain to `ζ_E(u)/ζ_E(u/3)` and Weyl-series convergence [M].
- A: A21, A22; S1 A-items.
- B: B25 (**RH**); a conformal correspondence over ℤ with factor `≠ 1` (B31, **RH**); census
  displacement (B27); B1–B7; B10.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) < 3` → `κ = 0` → RH.

Established:
- `κ(φ_c) = κ + 1` at every place and for primitive Dirichlet L-functions [L/M];
- translation reading `1`; readings add; dilation form + shell squares on boost mass zero [M];
- stable gluing; pole pair invisible to the boost index [M];
- carrier classification and unique proper-subgroup split [L];
- heat-deformed state [M]; Künneth branch all-or-nothing [M];
- coupled assemblies exact, separable assemblies blind [M];
- coupling ≡ kernel; one lattice decides; cone; finite stratum ⇒ RH from single-lattice
  coupling [L];
- principal-unit and three-prime cores carry `κ + 1` [M].

Reading [D]: `K_ζ(u)` is the normalized smoothed prime error in a fixed-length multiplicative
window at `u`. Boundedness of the coupling is window PNT at square-root precision (Π4). At the
critical overlap, smooth-bump packets of the complete family realize ratCorr Grams (A11).
- A: A21; A15 (heat calibration); A11.
- B: independent `κ(φ_c) < 3`, i.e. B1 on the ratCorr Grams (**RH**); B7 (**RH**); B28 (**RH**);
  B29 (**sub**); B14 on the heat branch (**RH**); B12 on the heat branch (**sub**); B11 for the
  Künneth square (**RH**); B8 (**RH**).

## 3. Candidates and retired branch

| Candidate | Established | A (just work) | B (open) |
|---|---|---|---|
| APF | Fredholm index, cycle-trace reconstruction | — | zero-independent divisor exhaustion (Γ5) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (Γ5) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (Γ/Σ) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (Γ) |
| EGC | pole-safe contour | — | outer expanding-contour sign; raw decay cannot beat the Gamma floor (Σ/Π) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (Γ5) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (Σ) |
| HJ | Hurwitz residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (Γ5) |
| IRK | rotation-algebra trace / winding | — | arithmetic Poisson / projective lift with integral count (Γ/Π) |
| MSC | Möbius–Sonin | — | bridge to nonnegative Sonin energy (Σ) |
| PCS | singular co-shift | — | source-natural wall annihilation; shift ≠ dilation (Γ) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port; lossless realization needs infinitely many resonances (B35) |
| RFHM | support grade; reversible sewing inverse-covariant | — | symmetry-breaking law (Γ) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (Γ5) |
| W1C | finite Lee–Yang + Ising receiver; Vitali obstruction | — | couplings converging to Riemann's measure (B35) |
| WBF | genealogy Gram | — | any arithmetic coupling (Γ5) |
| PW-B (retired) | zero-independent source family at every nonreal strip point; optical flux `−16(Re s − ½)Im s·M₊M₋`, vanishing iff critical [M] | — | killed as a selector (fails at `3/4 + i`). Survivor: half-parameter cusp `Λ(s) = 0` receiver, which needs zero-selecting scattering rigidity (B33, **RH**) |

## 4. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ, aperture axis (positivity at every `K·c*`) | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC (glued index), CHMD, TT; MSC, FEL |
| Σ, Hodge–Lefschetz / stars (HL on the positive locus) | HF, ACS-Hodge, TG |
| Σ, heat / collision integer | WD (charge `< 2`), LA (heat), TG, SC-heat |
| Σ, rank / degree | TH, HCF, PA, GTA, LA (Jensen) |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization | RN, PTR, W1C, PM (Mayer resonances) |
| Π, one-point precision | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, SC (coupling = window PNT); IRK |
| Π, conjugate diagonal | WD (Hecke defect), census |
| Γ, selection / Frobenius at infinity | BAG, XN, PM (partner saturation), MC (typicality), ACS (conformal correspondence), HF (Hecke similitude); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF; PW-B (retired) |

Inside Σ the complete-family routes share one axis. Below the critical overlap of their profile
(rough regime) every positivity theorem is consistent with off-line zeros. The tilted-spline
exponents `1/16` (all vectors), `1/11` (confinement), `1/9` (complement), `1/8` (packets; expected
critical overlap) and `¼` (proved receiver) belong to this regime and to the profile, not to ζ. At
`K·c*` the family is Weil's form at radius `½ log K`, and positivity there is a zero-free box. SC and
WD each carry a second, Π-type target: SC the window prime error read through the coupling, WD the
conjugate-diagonal Hecke defect. PM's open core is the same involution as HF's Hecke similitude and
WD's dyadic constant: Frobenius at infinity.
