# Route obstacles — status quo

Scope: the 32 live routes and 19 candidates of the programme and the programmes that feed them, read
against the Lean corpus at `1e8010c5b4` plus the working tree. For every route: path, what is established,
the open estimate, the mechanism class, the obstacles that are **(A) just work** and the obstacles that are
**(B) open mathematics** (no known solution).

Evidence: `[L]` committed Lean; `[W]` Lean in the working tree; `[P]` paper proof on a pipeline card, not
formalized; `[D]` derived here from Lean statements; `[N]` numerical. Strength: **RH**; **≥qRH** (zero-free
half-plane or Lindelöf); **sub** (strictly below quasi-RH); **identity**; **method**. An A item is known
mathematics, finite computation, effectivization or assembly of proved pieces; `(difficulty unverified)`
marks A items whose difficulty is not established.

Notation. Windows `[−a, a]` (half-width `a`) or half-windows `[−c, 0]`; `W` is Weil's form,
`w_n = Λ(n)n^{−1/2}`, `H` the archimedean–polar form (all prime weights `0`), `𝒥` the Lévy energy. For `f`
left of `m` and its mirror `f∘R`, `R(v) = 2m − v`, the **coupling** is
`𝒞_m(f) = 𝓗_m(f) − Σ_n w_n(f⋆f)(2m − log n)` (collar Hankel form `𝓗_m`); the **band** is
`|𝒞_m(f)| ≤ W(f)`. `a*(Z)` is the onset aperture (supremum of positive half-widths); `a*(ζ)` that of the
zeros of ζ. `L_T = ½log(T/2π)`; camera aperture `λL_T`. `ρ³ = ρ + 1`, `log ρ ≈ 0.2812`.
`a₁ = successorWeilFloorAperture`, `0.362 < enlargedWeilFloorAperture < a₁ < 0.3621`; `a_∞ = lim_k
weilFloorApertureTower k`, the limit of the strictly increasing tower of floor apertures starting at `a₁` (floors
`(1/20000)/2^k`; steps shrinking like `e^{−C·2^k}`).

## 0. Mechanism classes

| Class | Mechanism | Status | Anchor |
|---|---|---|---|
| P1 | **Signed criticality.** Weil's form on a window as a frustrated signed Dirichlet form with pole charges; primes pay the archimedean–polar deficit by the sign of their sliver reflections; pole variance retained | live; format exact in both sectors (neutral signed theta gauge, shifted ground state); RH ⇔ the two certificates on every window; the gauge freedom acts only in the pole direction (on the pole-neutral hyperplane every neutral gauge reads `archForm − primeSum`); frustration survives every sign gauge (even past `log ρ`, odd past `½log 2`); size-only payment dies before half-width `21/40` | SWC, FADF, ACT, WTZ, GWZ, CSTW, WVL [L] |
| P2 | **Prime-blind positivity / calibration.** Archimedean + pole part on signed blind combinations; equivalently the finite-level Weil cones `𝒜(c)` | live; `𝒜(c)` convex, a cylinder beyond `e^{2c}`, every entering weight bounded, stage fibre a compact interval; `⋂𝒜(c) = {Λ}` under RH | RHTower PBAP, FADF [L] |
| P3 | **Reflection positivity of PM.** Krein positivity of the completed resonant space | reduced: both expressions of the defect carry `(b^{2σ−½} − b^{−(2σ−½)})²`; any nonnegative representation ⇔ RH | RIT [L] |
| P4 | **Square-root cancellation** of one smoothed short-window prime count: the band in prime form | live; classical; parity barrier; every one-sided count receiver identified with the band | SWC, GWZ, CSTW, AOG [L] |
| P5 | **Reality by continuation / stability.** Real-rootedness (heat path, Jensen, finite free stability) closed, lost only through collision | live as a receiver; size reaches heat time `½/log X` and no lower; Gaussian finite free capacity `o(d⁻²)`; Euler side Hermite–Biehler stable, ζ/Gamma/pole sides unstable | ZCG, FFP, RHTower DeBruijn, LA, TH [L] |
| — | Identification (camera) | complete: configurations fixed up to clusters of diameter `e^{−c log³T}`; squared gaps of isolated polynomially small clusters read from three prime-side images | ZCG [L] |
| — | Counts / Hodge index / degeneration | closed as an RH mechanism [D] | S3 |
| — | Size-only layers (subcritical regime, one critical multiple, twisted sectors, receiving charges, terminal windows, aperture-independent floor) | true and blind [D] | S1 |

Closed mechanism families (anchors in `rh-killed-routes.md` where they exist):
- **Positivity-preserving certificates:** bare and folded Markov supersolutions, calibrated folded-Markov
  conductance, Beurling–Deny comparison of the even band past `log ρ` at every pole strength `s ≥ 1` and
  all weights, robust Perron margins beyond the pole-saturation gap [L]; **balanced switching**: every sign
  gauge leaves a negative conductance next to each node (logarithmic diagonal), the even sector is frustrated
  in every gauge past `log ρ`, the odd sector from `½log 2` [L: FADF].
- **Size-only payment of the primes:** edge-law certificates die at constant one; for ζ the unique crossing is
  `c* ∈ (½log 5, ½log 6]`; the archimedean–polar form `H` is negative on a window of half-width
  `≤ 21/40` (`w₂ ≤ 0` inadmissible), so size payment dies there; beyond a finite window one test makes the
  prime part strictly negative for the whole calibration space [L: FADF, SWC].
- **Cost-only and sign-blind fold payment:** `#frozen-gamma-cubic`, `#retained-gamma-lower-form`,
  `#first-fold-linear-chord`, `#prime-three-sliver-potential`; uncoupled stage loans (`stageForm 1 H < 0 < W(H)`
  on the positive window `21/20`) [L: AHD].
- **Ground states without the pole variance; window-independent theta gauges:** `#variance-dropped-theta-gauge`,
  `#theta-gauge-cosh-defect`; a single nonsingular even theta gauge has positive outside cosh deficit on every
  window [L: SWC].
- **Gauge optimization off the pole direction:** on the pole-neutral hyperplane every neutral signed even
  gauge represents the even sector by `archForm − primeSum`, independently of its pocket position; receding pockets
  conserve the ground-state outside deficit `½ − ∫_{(−c,c)}Φcosh` through the exterior jumps [L: SWC].
- **Point readings:** Weil's form reads no point values (spikes of arbitrarily small `L²`, `L¹` and Lévy
  energy); certificates see only `Ω`-weighted edge masses [L: FADF].
- **Twisted repair of untwisted negativity:** orthogonal conductor-`p` twists couple at `O(1/K)`; a negative
  untwisted mode stays negative above an explicit critical multiple [L: AHD]. Non-orthogonal Dirichlet-shift
  companions couple at `O(1)` and annihilate every tail mode, leaving the head window of length `log d`
  [L: AHD].
- **Fixed and quartic theta compensations:** fixed load fails at scales 6 and 8 (capacities exact); untruncated
  quartic at 32; truncated quartic at scale 6 [L: TCS].
- **Finite structures, slack, counts, height-local decisions, universal density thresholds, domination as a
  selector, size-only heat repair, PM line selectors:** as in `rh-killed-routes.md`.
- **Finite free factorizations:** Szegő on the source-faithful split (theta piece never real-rooted),
  factorwise/phase shortcuts, positive Dirichlet pieces (never real-rooted), every translation of ζ-side, Gamma
  and pole pieces (unstable); the degree-three semicircle-free test (every real-rooted cubic passes) [L: FFP].

## 1. The picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ `a*(ζ) = ⊤`; positive half-widths form `[0, a*(Z)]`; off RH `a*(ζ)` = contact, attained; `a*(ζ) ≥ a_∞` | WVL, AIP [L] | every window route measures one number |
| `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)`; single-prime stage transport for all `A` ⇔ RH; Dirichlet-shift stabilization for every divisor `d` ⇔ `R₁(log d) = ⊤` ∀d ⇔ RH | WVL, AHD [L] | HF's threshold is the onset aperture; long windows reduce to head windows |
| Floor apertures form an infinite strictly increasing tower from `a₁` with floors `(1/20000)/2^k`, on windows and on reflection pairs | AIP, SWC [L] | `a*(ζ) ≥ a_∞` |
| Positivity at level `a` ⇒ `|β − ½| < 10⁶exp(−a/(480000 log(|γ|+3)))` for `|γ| ≥ 102`; `N(t, t+1] ≤ 240 log(|t|+3)` | SquareRootThreshold [L] | effective excluded-depth corridor |
| Below `log 5`: window positivity ⇔ the `{2,3,4}` sliver band (only `n = 2` in the half-window diagonal; the three kicks use `< 0.991` of the Lévy energy) ⇔ the joint neutral-gauge/shifted-ground-state certificate | SWC [L] | the first stages are an exact three-power problem |
| `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; `W(f) − |𝒞_m(f)| = ½min(W(G₊), W(G₋))`; the coupling truncates to `2 ≤ n ≤ e^{2c}`; floor `‖f‖²/8000` for `c ≤ enlarged` | SWC [L] | the minimal object is a reflection pair |
| Arithmetic part is an optimal Hardy term for `H` iff RH; scaling optimality (only multiple `1`) and criticality (no Hardy weight on odd tests) unconditional; `⋂_cℋ(c) = {1}` ⇔ RH | FADF [L] | Weil positivity is a critical Hardy inequality with a unique admissible multiple |
| Before contact each window carries a complete Weil Hilbert space, a de Branges space with explicit Hermite–Biehler function, unitary zero-moving and antiunitary conjugation; inclusions isometric; at finite contact a fixed evaluation kernel diverges monotonically | CSTW [L] | the window tower is a de Branges chain; RH ⇔ the chain has no finite contact |
| The archimedean symbol `1 + ½log(1 + ξ²)` factors through a logarithmic Poisson factor: holomorphic on the slit plane, one simple negative zero, half-line support preserved, reciprocal = Stieltjes transform of a positive measure, causal kernel a positive probability density, renewal mass normalized | CSTW [L] | a Wiener–Hopf (renewal) factorization of the archimedean part [D] |
| The Weil symbol is `1 + ½log(1 + ξ²)` minus a bounded convolution; evaluation vectors solve the literal operator equation with bounded forcing | CSTW [L] | Riesz vectors are physical (bounded) |
| Correlation-form positivity on a window ⇔ positivity of every finite rational Hecke graph of smaller log-spread; finite templates control spreads with finite Hecke orbits; at spread 6 the ×2/÷3 orbit is infinite | WTZ [L] | finite-matrix reduction ends before `log 6` |
| Even kernel `ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)`: Markov iff `c ≤ log ρ`; odd kernel positive light cone, each acting prime power a frustrated anti-diagonal | SWC, FADF [L] | certificates past `log ρ` are signed and unswitchable |
| Trivial-zero squares are mirror mass minus reflected (even) / antireflected (odd) energy, paid by centre killing | FADF [L] | frustration = pole square (odd) + prime reflections (both) |
| Entry law: outer `|λ(n₀)| ≤ √n₀(log(1/δ) + B)`, inner radius `√n₀η(½log(1/δ) − ¼)` | FADF [L] | soft entry is sharp; beyond the sliver only sign |
| Visibility: `k·pairEnergy(δ,a) ≤ L` in lattice backgrounds; unshielded clusters excluded to doubly-exponential height; tapered crystals hide depth `1/a` above `e^{ca}` | WVL [L] | windows read depth and coherence |
| Camera: `λ > 1` fixes RvM configurations up to near-collisions; `λ > ½` reads isolated zeros of ζ with multiplicity; inside isolated clusters of radius `r ≤ T^{−(M'+κ_λ+1)}` the moments are read to `N r^{j+1}T^{M'+κ_λ} + e^{−K'log³T}`; squared gap from `𝓗 = 4(W₁² − W₀W₂)/W₀²`; FE pair `𝓗 ≈ −4δ²`, on-line pair `𝓗 ≈ Δ²` | ZCG [L] | identification is complete; reality is the sign of an explicit prime-side ratio |
| FE-pair squared gaps `≥ 0` at every zero ⇔ Weil positivity ⇔ `Λ_X = 0` ∀X ⇔ no heat collision ⇔ RH; `Λ_X ≤ (6600/9991 + ε)/log X`; saddle at `½/log(X/2π)`; pair models collide below every scale | ZCG [L] | P5's residual is the sign of `w²` below the saddle |
| Möbius-mollified Jensen stability at infinitely many degrees ⇔ RH ⇔ bounded imaginary parts of Jensen roots along infinitely many degrees (otherwise linear growth `κd`); zero-free `Re s > σ` ⇔ Jensen polynomials of `ξ(σ + i·)` stable (unconditional for `σ ≥ 1`); `R_d(Ξ)` has unboundedly many real roots; normalized Euler factors HB-stable with forced drift `θ_S/2`; ζ/Gamma/pole pieces unstable; `e^{(t/d²)D²}J_d` not real-rooted | FFP [L] | finite free probability reproduces de Bruijn–Newman criticality and every zero-free half-plane |
| PM defect `−D_s(ψ_s) = ∫_0^∞K_σ(x+1)|ψ_s(x) − (x+1)^{−2s}ψ_s(x/(x+1))|²dx`, `K_{1/4} ≡ 0`; infinitely many critical resonances | RIT [L] | the second expression has the same sign |
| Inner-cap flux = `Σ_{off-line ρ}m_ρe^{(ρ−½)t}` + bounded − `L²` | CDG [L] | WD's estimate is a zero-free statement verbatim |
| Cayley ladder of ζ = Toeplitz ladder of paired Li coefficients; RH ⇔ NSD on primitive vectors ⇔ entrywise `≥ 0`; over `𝔽_q` the ladder entries are the sharp Weil lower bound | ALG [W] | Hodge index = Metzler sign = Li positivity |

## 2. Shared obstacle blocks

### S0. The band, the Hardy interval and reflection pairs
Routes: every route of C1, C4, C7, C14, C15, C19, C26.

Established [L]: RH ⇔ two-site PD ⇔ band on every reflection pair ⇔ `1 ∈ ℋ(c)` ∀c ⇔ every growth step
`ℓ → ℓ + ε` a translation contraction (FADF Q7) ⇔ positivity on the two-parameter family
`κ_γ(t + v/2) ± κ_γ(t − v/2)` (SRT); collective sliver identity and the `1/8000` floor through `enlarged`;
`𝒞_m(φ) = c_φ(2m)` for even bumps; scaling optimality and criticality of the Hardy form unconditional.

| | Obstacle | Strength |
|---|---|---|
| B1 | The band at every step and every test (`a*(ζ) = ⊤` ≡ `1 ∈ ℋ(c)` ∀c ≡ every growth step a contraction) | RH |
| B10 | No zero mode at any length | RH |

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACT (index), ACS-atomic, SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF, BVI.

Established [L]:
- Subcritical PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8`; whole-space PD at one critical multiple; a uniform
  aperture-independent critical multiple across all prime entries.
- `R₁(A) = ⊤` for `A ≤ 2·weilFloorApertureTower k`, every `k`; every critical pencil positive on those windows; one window
  `A ∈ (2·enlarged, 1)` with all critical pencils positive.
- Stage transport: composite stages carry no fold; prime-power stages ⇔ `stageForm + w·foldEnergy ≥ w·end mass`;
  unconditional transport across `p = 2` at `A₀ = 2·enlarged − log 2`; first-fold stage-loan obstruction;
  conductor-grading obstruction; single-prime transport for all `A` ⇔ RH.
- Non-orthogonal Dirichlet-shift companions `1_{d|n}g₀(log(n/N) + log d)/√n`: conductor-1 plus conductor-`d` parts,
  `O(1)` cross term, tail modes annihilated at `O(1)`; stabilization of every direction on `[−(A + log d), 0]`
  forces `R₁(log d) = ⊤` and follows from `R₁(log d + ε) = ⊤`; unconditional for `d = 2`; for every `d` ⇔ RH.
- Character windows graded by parity; equal parities coupled through `L(s, ψ̄₁ψ₂)`; joint periodic windows keep the
  residue-averaged mass Gram.
- Critical-curve second order, twisted sectors, frequency pole, bulk, terminal windows (polar source,
  nontrivial kernel, long-index cancellation on near rows and annuli), conductor packets.
- Receiving charges: capacity `log log N + O(1)`; simultaneous receiving vectors on fixed and growing mode sets
  with vanishing physical energy read at `1/80`; literal three-range split, affine short rows, Mangoldt kernel Grams,
  same-source prime towers, harmonic tails, centering; complete physical energy does not control charge.

Status: every layer below the sign is size-only and classified; HF's sign content is `a*(ζ) = ⊤`; twisted
directions cannot pay untwisted negativity. The far-complement estimate loses `O(c)` against its
`O(log N/c⁷)` reserve.

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons (`K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, conductor range `M(N) = o(c_N)`) | — |
| A2 | General profiles past `θ = 1/1080` | — |
| A4 | Certified ratio interval at its size-only optimum; receiving complement inside it (difficulty unverified) | — |
| A9 | Literal channel norms critically small with growing periods, offsets and prime bands (difficulty unverified) | — |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH all |
| B8 | General profiles past `log log N` on the full space | sub |
| B9 | Exact SOS on one two-prime lattice | RH |
| B16 | Window negativity exponent `< ½` (≡ zero width `< ½`) | ≥qRH |
| B55 | Head-window thresholds `R₁(log d) = ⊤` for every `d` (the residue of Dirichlet-shift stabilization) | RH |
| B33 | HF-native arithmetic sign: a window beyond the base certified by the complete family itself (the literal statement `R₁(A) = ⊤` for some `A > 2·enlarged` is supplied by the AIP dilation at `A = 2a₁`, a margin of `≈ 10⁻⁶`; since `R₁(A) = ⊤ ⇔ A/2 ≤ a*`, the qualifier has no content) | sub; finite window |

### S2. The window tower, its canonical system and signed criticality
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF.

Established [L]:
- Window datum, stage criterion, kick = collar Rosati pairing, frozen form; lattice canonical system;
  continuum jet Hankel limit; sectors ⇔ Hamburger / shifted Hamburger; window ⇔ Stieltjes.
- **De Branges chain before contact:** complete Weil Hilbert spaces, entire Fourier coordinates, explicit
  Hermite–Biehler function with Christoffel–Darboux identity, unitary zero-moving, antiunitary conjugation,
  isometric inclusions; kernel blow-up at finite contact with the contact window still positive.
- Weil symbol = logarithmic multiplier + bounded convolution; Riesz vectors bounded, in the operator domain,
  solving a logarithmic Dirichlet equation with bounded forcing; positive-level truncations admissible.
- Calibration spaces `𝒜(c)`: convex, cylinders, each entering coordinate bounded, stage fibre a compact
  interval; sharp entry law; real tests decide.
- Below `log 4`: two-weight convex membership ⇔ Markov–Hankel pair ⇔ retained-variance certificates ⇔ Hodge
  index ⇔ Künneth effectivity; neutral signed even theta gauge and shifted ground state represent both sectors
  exactly on every window; below `log 5` the window is the `{2,3,4}` sliver band (three kicks `< 0.991` of the Lévy
  energy) and the joint certificate. The gauge freedom acts only in the pole direction; receding pockets conserve
  the outside deficit.
- Floor tower: floors `(1/20000)/2^k` on a strictly increasing sequence of apertures from `a₁` (limit `a_∞`), on
  windows and on reflection pairs; multi-prime dilation modulus on every `[−R, R]`.
- Wiener–Hopf factorization of the archimedean symbol: logarithmic Poisson factor, positive Stieltjes measure of
  its reciprocal, positive causal (renewal) kernel.
- Perron sign law; frustration localization; robust Perron costs height; switching never balances.
- Trivial zeros paid by centre killing; regional–edge decomposition `𝒥 = 𝒥_reg + 𝒦`; no point traces.
- Finite rational Hecke graphs decide correlation-form windows; exact Tate horizons through `log(81/16)`;
  positive Tate dimensions a closed interval `[0, κ(A)]`, `κ(A) → 0`; signed ≠ absolute edge cost at the
  ratio-four triangle.

Status: the certificate format is exact on every window in both sectors; what is open is the inequality the
format states. No certificate exists for any `c ∈ (a_∞, log 2)`. These windows carry no zero information
(S11).

| | Obstacle | Strength |
|---|---|---|
| A5 | Rigorous computer-assisted certificate of `(w₂, w₃) ∈ belowLogFourBandWeights c` for `c ∈ (0.3621, log 2)`; margins `1.5×10⁻⁵` (odd), `5.6×10⁻⁸` (even) at `c = ½log 3`, `≈ 2×10⁻⁴` on the odd unit window [N] | — |
| A6 | Exact Tate horizons of the remaining stages below spread `6` (finite templates exist there) | — |
| A7 | Closed form of the first-stage complement `Φ_ε` | — |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` (sharp Schur row bound) | — |
| A33 | Lévy sector margins at `c = ½log 3` in both sectors, feeding soft entry [N] | — |
| A41 | Canonical-system Hamiltonian of the precontact de Branges chain (de Branges ordering theorem applied to the CSTW chain), with contact as its first singular length | — |
| B2 | Kick admission at every stage | RH as induction; each stage sub |
| B3 | Frustration domination: the neutral signed theta-gauge inequality `2V ≤ J_{M⁺}` (even) and the shifted-ground-state inequality (odd) on every window | RH; fixed length sub |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub |
| B5 | Structural certificate below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub; finite window, no door |
| B56 | The `{2,3,4}` sliver band below `log 5` (`a*(ζ) ≥ ½log 5`) | sub |
| B49 | Signed ground-state structure past `log ρ` compatible with unswitchable frustration (nodes cost negative light-cone conductance) | method |
| B51 | Regularity of the Weil Hamiltonian at every finite length (no contact) | RH (identity form of B1) |

### S3. Dimension zero, counts and the Hodge index
Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD, LST, KPA.

Established [L]: Tate jets and signed counts; bare domination ⇔ `Q ≥ 0`; Künneth `h¹ = ½Q`; bidegree,
fixed-rank, definite and Siegel counts excluded; positive Tate dimensions shrink to `0`; below `log 4` window
positivity ⇔ Künneth effectivity ⇔ Hodge index; over `𝔽_q` the Cayley ladder entries are the sharp Weil lower
bound and reflection positivity of every ladder is RH for the curve [W].

Status: closed as an RH mechanism [D].

| | Obstacle | Strength |
|---|---|---|
| A25 | Künneth primitive `h¹` at small degree; mixed jets | — |
| B24 | Genus upper law | indep. |
| B25 | Logarithmic Serre duality, primitive part | sub |

### S4. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, TG, SC, RW; MC through the gluing determinant.

Established [L]: HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; stars, depth law, gcd strata; squarefree
prime complex homotopy equivalent to a wedge of spheres indexed by odd squarefree `N/2 < m ≤ N` (reduced
Euler characteristic `−M(N)`); Redheffer `det = M(N)`; zero modes = radical.

| | Obstacle | Strength |
|---|---|---|
| A23 | Depth law, star horizons, gcd-strata tables | — |
| B10 | No zero mode at any length | RH |
| B11 | Top coprime stratum | RH |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH |
| B45 | Cross-tower gap through the archimedean channel | method |

### S5. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT, CHMD, SC, RIT, CWS.

Established [L]: finite index ⇒ Lindelöf; RH ⇔ index zero; window index left-continuous, counts critical
lengths strictly below, locally finite, critical length `n` finite ⇔ more than `n` right zeros; inward dilation
preserves finite negative families; `{0, ∞}` laws; index `≤ R + A`; growing Euler heads unbounded.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub |

### S6. Window energy, inner caps, near-line density
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established [L]: inner-cap flux on Burnol windows = off-line generating function `Σm_ρe^{(ρ−½)t}` + bounded
+ `L²`; Laplace integrability at exponent `x` ⇔ that of the off-line source; all exponents ⇔ no off-line zero in
the window; fixed degree ⇔ inverse-polynomial corridor; all stages ⇔ RH; VK caps prefix-invariant; eight
near-line density forms; `D_win` ⇔ thin Planck shadows; right-half squared-depth moment `o(V)`.

Status: WD's open estimates are zero-free statements verbatim; WD supplies no producer [D].

| | Obstacle | Strength |
|---|---|---|
| B19 | Inner caps at every polynomial stage (≡ off-line generating function `L²(e^{−xt})` at every stage) | RH; fixed degree ≥qRH |
| B20 | `100%` critical-scale clustering | sub |
| B21 | `D_win` (≡ thin Planck shadows); `D_zero` | sub |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH |
| B23 | Distributional input beyond counts and moments | method |

### S7. Counts, producers, precision and the gauge torus
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census.

Established [L]: one-sided count ⇔ RH; the reflection-pair prime-count band ⇔ Weil-lag bound ⇔ JAS ⇔ CTF ⇔
PBM ⇔ eventual Robin; multivariate parity producers reach `(1+ε)x + C_ε log²x`; individual producers slope
`> 1`; gauge exponents range over `[Θ, 1]`; simple-critical proportion `≥ 0.67250071`.

| | Obstacle | Strength |
|---|---|---|
| A21 | Logarithmic two-point Chowla | — |
| A24 | Census items; Voronoi; Zwegers | — |
| B26 | `ε`-uniform producer; square-root source input | sub; RH |
| B57 | Self-improvement of a strip: `Θ < 1 ⇒ Θ = ½` (no mechanism) | sub |
| B27 | First cyclotomic mode at square-root precision | RH |
| B28 | Signed pair information beyond bandwidth one | sub |
| B29 | First Epstein real zero on the boost line | sub |
| B32 | Half-power law at the trivial gauge point | RH |

### S8. Carriers, coupling, selection and the calibration cone
Routes: SC, ACS, HF; candidates; PBAP.

Established [L]: Gaussian-damped coupling = arithmetic heat average of the compact-test Weil functional
(prime, archimedean, pole retained); damped cone ⇔ RH; Weil cone `{Λ}`; calibration spaces convex with bounded
entering coordinates; total anti-diagonal kernel positive everywhere exactly for `n ∈ {2,3,4,5,7,8,9,11,13}`
(elsewhere the pole pays the whole negative conductance at the midpoint); Selberg-class rigidity; Legendre
`J(ρ)` real ⇔ RH.

| | Obstacle | Strength |
|---|---|---|
| A11 | Function-field calibration of the remaining receivers | — |
| A13 | Widths of the finite-level cones `𝒜(c)`; computed to `c = 0.66` (summary 1.15) [N] | — |
| A31 | Selberg-class degree-one classification | — |
| B30 | Bounded damped cone coupling; unattained width | RH |
| B31 | Finite-sieve Hodge positivity → global | RH |
| B34 | Rosati positivity of the window reflection | RH |
| B36 | Selection at the trivial gauge point | RH |
| B37 | FE twins inside the full class with off-line zeros | sub |
| B42 | Prime-blind positivity on signed blind combinations | RH |
| B58 | Effective uniqueness of the Weil cone: explicit `ε(n, c) → 0` with `|λ(n) − Λ(n)| ≤ ε(n, c)` on `𝒜(c)` | sub |
| B59 | Margin law: decay of `max_λ λ_min(W_λ|[−c,c])` and of the band widths | sub |

### S9. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: Mayer operator; resonance ⇔ `ζ(2s) = 0`; `Q = 2Re[𝓦H, 𝓦H]`; Krein–Lax–Phillips space;
`1 + p^{1−2s} ≠ 0` at every resonance; `−D_s(ψ_s)` equals a `K_σ`-weighted norm of `T_{p,s}ψ_s` (every prime)
and of the three-term shift difference, `K_σ ∝ (b^{2σ−½} − b^{−(2σ−½)})²`, `K_{1/4} ≡ 0`; infinitely many
critical resonances, where `D = 0` but norms, cusp energy and `core_s(2)` are positive; off-line: `D < 0` on both
partners, `T₂` channel reverses sign, reflected cusp pair `−2`; any nonnegative representation of `D_s` ⇔ RH.

Status: P3's sign is `σ = ¼` in two coordinate systems; no positive multiple of norms equals `D` [D].

| | Obstacle | Strength |
|---|---|---|
| A14 | Classical identifications; mixed-parameter completion; full Mayer transfer compatibility; analytic completion of the corrected boundary carrier; rational Weyl identification | — |
| A15 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | — |
| B38 | An expression of `D_s(ψ_s)` at resonances with sign `≥ 0` that does not carry the factor `(b^{2σ−½} − b^{−(2σ−½)})²` | RH |
| B39 | Statistic of resonant states selecting the decay rate | method |
| B40 | Source-faithful realization of unbounded rank | RH |
| B46 | PM-native zero-free region for `ζ(2s)`, `β < 1 − c/log|γ|`, from the carrier alone (route test; reproves a classical region) | sub |

### S10. Zero-configuration geometry, camera and continuation
Routes: ZCG (candidate), LA, TH, HCF, XN, SRT; programmes ZCG, RHTower DeBruijn, SquareRootThreshold.

Established [L]:
- Camera: blindness `πD`; Paley–Wiener; one-depth configurations resolved at the Ingham scale `π/(2a)`,
  mixed depths hide beyond it (any-depth threshold `π/a`); fakes caught above `½log n₀`; sharp local density of
  ζ zeros; local camera constant quasi-polynomial.
- Inversion: `λ > 1` RvM configurations; `λ > ½` subset carriers and every isolated zero of ζ with
  multiplicity; `λ ≤ 1` half-shifted mimics; cancelling clusters of ζ-mimics are near-coincidences within
  `exp(−κlog X/(1 + loglog X))`.
- **Polynomial-scale second order:** isolating windows vary slowly relative to the target image; moments of
  isolated clusters of radius `r ≤ T^{−(M'+κ_λ+1)}` read to `N r^{j+1}T^{M'+κ_λ} + e^{−K'log³(T/2π)}`;
  centres to `O(r²)`, squared gaps to `O(r³)`; dipoles collapse to `2e^{−K'log³T}`; squared gap of a two-point
  cluster `= 𝓗` from three images; discriminant of a `k`-point cluster from `2k − 1` images; points located by
  bordered Hankel determinants.
- Second-moment explicit formula: prime term = height curvature, `(log n)²`-weighted; real and FE pairs enter
  with opposite signs; bounded apertures cannot see Euler columns at primes `p > e^{2r}`.
- Heat: source-profile repulsion law; `6600/9991` horizon (sharp for its profile); saddle at `½/log(X/2π)`;
  `pairModel` order-2 collision below every scale; FE-pair squared gaps `≥ 0` ⇔ RH.
- Euler stages and every finite real carrier real above `2πe^{W_a}`; twins tilted at every height.
- Periodic patterns: a nonzero period-`N` lag symbol cannot vanish at all `|m| ≤ N − 1`; period-`N` mimics never hide
  above `(N − 1)π/(Ng)`; the period-6 mixed-depth mimics hide exactly to `5π/(6g)`.

Status: identification is complete at its scale; the RH content is the sign of the squared gap at
near-coincidences (B44): the squared gap, read at windows built from the cluster [L/D].

| | Obstacle | Strength |
|---|---|---|
| A38 | Sub-Weyl strip profile from the best known exponent pairs (horizon toward `½`; decides nothing about zeros) | — |
| A40 | Camera with real (non-integer) weights and Beurling–Selberg transfer of local counts to mimics (not needed for A39) | — |
| A42 | Effective `T₀` in the camera theorems | — |
| B14 | Collision exclusion along a source-faithful path below `½/log X` (≡ `Λ_X = 0` ∀X) | RH |
| B44 | Reality at near-coincidences: `𝓗 ≥ 0` (up to readout error) on every isolated cluster of ζ, `𝓗 = 4(W₁² − W₀W₂)/W₀²` from images at windows built from the cluster | RH |
| B54 | Distinct zeros of ζ at height `T` separated by `≥ T^{−C}`: open under RH, no implication for real parts, no route depends on it | indep. |

### S11. Window visibility
Routes: every window route; WD, LA, ZCG through depth and density. Programme: WVL, SquareRootThreshold, DCI.

Established [L]: closed-interval law; master law `k·pairEnergy(δ,a) ≤ L` (also for distinct clusters near one
ordinate); deep and cubic brackets; `e^{2(δ−σ)a}/δ` unshielded-cluster law; tapered-crystal barrier;
doubly-exponential non-locality; split-column certification `πD_on + (π/2)D_off`, mixed `(g − ½)ℓ` sharp;
ridge `2Le^{δL}Σ|ε_k| ≤ 1`; contact law at `c log T`; synthesis module; explicit detector: `N(t, t+1] ≤ 240
log(|t|+3)`, every off-line zero of depth `≥ δ` detected at aperture `480000 log(|γ|+3) log(10⁶/δ)`, positivity
at level `a` confines `|β − ½| < 10⁶exp(−a/(480000 log(|γ|+3)))`.

Status: classified in models; for ζ the laws require window positivity, known only at `a ≤ a_∞ ≈ 0.362`,
where they are vacuous.

| | Obstacle | Strength |
|---|---|---|
| A35 | Sharpen the explicit constants (`2²⁶·960`; detector `480000`, `10⁶`) toward the model constant `4δL/k` | — |
| A36 | Remaining onset-law items (general RvM shallow depth-mass bound under positivity; tapered crystal to `a ≍ log T`; two-bump interferometer) | — |
| A39 | Sharp zero location: compose the negative test on the form (`exists_window_re_W_neg`, `not_hodgeIndex_below_nyquist_horizon`) with the camera's isolating windows at `a = λL_T`, `λ > 1`; no on-line mimic needed; a receiver | — |

### S12. Finite free stability
Routes: LA, TH; candidate FFP.

Established [L]: Jensen dictionary `R_d(fg) = R_d(f) ⊞_d R_d(g)`; Walsh half-plane theorem; Szegő composition;
heat = `⊞_d` with Hermite; `e^{(t/d²)D²}J_d` not real-rooted ∀t > 0 (unboundedly many non-real roots, leaving
every strip; Bernoulli shifts cannot repair); shift regime asymptotically semicircular; capacity table; source
split `J^{d,n} = Γ_{n,d} ⊠_d Θ_{n,d}` with Γ Laguerre (negative roots) and Θ never real-rooted; positive
Dirichlet pieces never real-rooted; normalized Euler factors HB-stable at every degree, drift `θ_S/2` forced and
sharp, no bounded translation stabilizes all products; symmetric Euler carrier real ⇔ `c ≥ θ_S/2`; curved phase
degree horizon `≈ δ²/(4a)`; ζ-side, Gamma-side and pole pieces unstable for every phase; RH ⇔ infinitely many
`J_d` real-rooted ⇔ Möbius-mollified Jensen polynomials stable at infinitely many degrees ⇔ imaginary parts of
Jensen roots bounded along infinitely many degrees (else linear growth); zero-free `Re s > σ` ⇔ stable Jensen
polynomials of `ξ(σ + i·)` (unconditional, strict, for `σ ≥ 1`); `R_d(Ξ)` has unboundedly many real roots
(finite free Hardy theorem); genus-one products with nonnegative drift have stable Jensen polynomials (finite free
Pólya–Levin class); `R_d(Ξ)` is a limit of finite free products of rank-one zero pieces, all real-rooted iff RH; `ξ` has no
stability margin on any line, phase `c = 0` exactly critical, genus-one class classified by its drift [W].

| | Obstacle | Strength |
|---|---|---|
| B52 | Stability of `R_d(Ξ·M_S)` at infinitely many degrees | RH |
| B53 | A source-faithful real-rooted (or HB-stable) finite free factorization of `J^{d,n}` other than the Γ ⊠ Θ split | method |

### Route-specific items
| | Obstacle | Routes | Strength |
|---|---|---|---|
| A17 | Theta fifth even section on the compact interval `π ≤ q < 7` with an entry-preserving compensation other than the quartic (truncated quartic positive from `q ≥ 7` and failing at scale 6; fixed load failing at scales 6 and 8; untruncated quartic at 32; first-atom tails PD from scale 3), then rank 9 (difficulty unverified) | TH | — |
| A18 | Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | — |
| A19 | Certificates on the nine anti-diagonals `n ∈ {2,3,4,5,7,8,9,11,13}` where the pole pays nowhere | ACT | — |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | — |
| B15 | Scheduled prime energies bounded below (FU, CFC, RP, EGC, FEL); for SZ and LI identified with B1 | FU, CFC, RP, EGC, FEL | RH |
| B41 | Pre-divisor forcing | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | RH |

## 3. Live routes

Each entry: path; established; open; class; A; B.

### WL — Weil lag
- Path: prime error → square-root bound or subexponential critical energy → RH.
- Established: exact prime-error/energy criteria; first cyclotomic band abscissa `2Θ`; gauge-torus exponents
  `[Θ, 1]`; the reflection-pair prime-count band ⇔ Weil-lag lower bound [L].
- Open: signed square-root precision of one band; a gauge attaining exponent `½` at the arithmetic point.
- Class P4. A: A25. B: B1, B26, B27, B32.

### RW — restricted Weil ground energy
- Path: `μ(a) ≥ 0` at every radius (≡ `a*(ζ) = ⊤`) → RH.
- Established: floors through the tower up to `a_∞` (`‖f‖²/20000` at `a₁`); positive apertures `[0, a*]`; de Branges chain before contact
  with explicit HB function and kernel blow-up at contact; Riesz vectors bounded and solving the logarithmic
  Dirichlet equation; two-site decision; below `log 4` two-weight band; Hardy interval; calibration spaces [L].
- Open: exclude finite contact (regularity of the chain at every length); all-aperture signed coupling payment;
  arithmetic-point membership below `log 4`.
- Class P1. A: A5, A7, A33, A35, A39, A41. B: B1, B2, B3, B4, B5, B49, B51.

### FU — signed prime scheduling
- Path: signed prime/Möbius history → one-sided sampled Abel bound → RH.
- Established: for each fixed `m`, one-sided boundedness of `A(j^m)/j^m` ⇔ RH; one controlled sample per
  backward window of length `N^{1−δ}` suffices [L].
- Open: produce those samples from the complete signed history.
- Class P4. B: B15.

### CFC — first-clock lower bound
- Path: first-clock sine coefficient bounded below on an aperture tail → RH.
- Established: exact tail criterion; unbounded below under ¬RH; phase-natural transport is the identity [L].
- Open: a lower bound retaining prime, archimedean and endpoint terms.
- Class P4. B: B15.

### RP — history floor
- Path: matched-quantile prime history → eventual linear defect floor → RH.
- Established: linear-floor criterion; low-LCM and copied-diagonal payment; sublinear floor impossible [L].
- Open: high-LCM pairs, moving core and singular-domain terms in one floor.
- Class P4. B: B15.

### PA — prime–archimedean passivity
- Path: prime − archimedean trace → current sign or subexponential mismatch → RH.
- Established: exact receivers; each fixed Hausdorff order positive at large shifts [L].
- Open: all-order/all-shift sign.
- Class P5 (order limit). A: A18. B: B14.

### MC — Möbius cancellation
- Path: Möbius/Liouville cancellation at half power → RH.
- Established: half-power and Redheffer criteria; squarefree prime complex ≃ wedge of spheres (Euler
  characteristic `−M(N)`); bounded pronic energy; Möbius exponent Haar-a.e. `½`, Baire-generic `1`; explicit
  exponent-`½` gauge; flip points `max(θ, Θ)` [L].
- Open: half-power cancellation at the trivial gauge; uniform signed long-modulus energy.
- Class P4. A: A21. B: B26, B27, B32, B36.

### TT — theta tail / Wold
- Path: theta source → directed covariance/Wold decay or odd Weil sign → RH.
- Established: exact receivers; Φ-Doob identities; odd sector = band at the centre ⇔ shifted Hamburger ⇔
  antireflected trivial-zero form `4S² ≤ (M − ΣK) + ΣD + P`; shifted ground state represents the odd sector on
  every window [L].
- Open: the odd-sector inequality on every window (frustrated by every acting prime power).
- Class P1 (odd sector). B: B1, B3, B4, B5, B49.

### LA — Laguerre/Jensen and local heat
- Path: theta source → collision-free heat descent / Jensen or finite free stability → RH.
- Established: every fixed Jensen degree eventually real-rooted; RH ⇔ infinitely many `J_d` real-rooted ⇔
  Möbius-mollified stability at infinitely many degrees; finite free de Bruijn–Newman law; `Λ_X ≤
  (6600/9991+ε)/log X`; off-line depth `d` forces `Λ_X ≥ c d²/log X`; collision criterion; saddle `½/log(X/2π)`
  [L].
- Open: arithmetic exclusion of collisions in `(0, ½/log X]`; or uniform Jensen/stability. Pair models collide
  inside that band [L].
- Class P5. A: A18, A38. B: B14, B52.

### TG — topological sub-unit gate
- Path: Euler/Gaussian source → nonnegative residual + integer trace `< 1` → RH.
- Established: winding/index and cubic-transgression identities; central-gap receivers [L].
- Open: a matrix-complete positive residual with sub-unit integer trace on every disc.
- Class P4 (inner caps). B: B10, B19.

### HF — Hodge / Hecke / complete cells
- Path: complete arithmetic form `≥ 0` → Hodge index → RH.
- Established: S1 in full; single-prime stage transport ⇔ RH; unconditional transport across `p = 2` at `A₀`;
  stage-loan and conductor-grading obstructions; Dirichlet-shift companions reduce every long window to its head
  `R₁(log d)` (unconditional for `d = 2`); `R₁ = ⊤` through `2a_∞` [L].
- Open: `a*(ζ) = ⊤`; signed complement at every ratio; the far-complement loss `O(c)` against `O(log N/c⁷)`.
- Class: sign content P1; count face closed; floor layer size-only.
  A: A1–A4, A9, A11, A23. B: B1, B2, B6, B7, B8, B9, B10, B11, B12, B16, B33, B34, B35, B40, B55.

### CHMD — causal hyperbolic–modular duality
- Path: one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- Established: wave/Doob receivers; Haar transport; all-detail prime–pole cancellation
  `O(exp(−√log Y/92160000))` [L].
- Open: one-sided boundedness of the unnormalized prime wave, or the complete odd sign.
- Class P1 (odd sector). A: A20. B: B3, B12.

### TH — theta Hankel ranks
- Path: signed centre-mixed theta jets → all-rank Hankel positivity → RH.
- Established: rank 8 PD for `0 < a < ½`; native fifth even section strict from `q ≥ 5` (floor `49/4000`);
  four retained atoms with error `≤ 1/20000` from `q ≥ 3`; truncated quartic flux preserves every mixed entry and
  is positive at every aperture from `q ≥ 7` (exact rational Schur certificate); fixed load fails at scale 8,
  untruncated quartic at scale 32 (capacities exact); every finite native shifted Hankel matrix PD on a cofinal
  ray; truncated quartic fails at scale 6 (exact capacity); first-atom tails PD from scale 3 [L].
- Open: the compact interval `π ≤ q < 7` with a compensation other than the quartic; then `I₈(a) > 0`; all ranks.
- Class P5 (rank limit; one-centre moment problem). A: A17. B: B14.

### RN — renewal
- Path: theta renewal → divisor-faithful winding/boundary-work sign → RH.
- Established: Green/BV realization; compact cone-positive renewal operator with exact determinant [L].
- Open: directed mixed prime + Gamma `≥` pole including cusp/seam terms.
- Class P3-type. B: B40.

### WD — Ward / collision / window energy
- Path: source current/window energy → collision charge `< 2` or all-resolution sectoriality → RH.
- Established: S6 [L]: inner-cap flux = off-line generating function + bounded + `L²`; every stage receiver is
  an exact zero-free statement.
- Open: inner-cap cancellation through all polynomial stages; density branch `D_win` with vanishing cluster
  tail.
- Class P4 (inner caps; the open estimate is a zero-free statement); density branch sub.
  B: B19, B20, B21, B22, B23.

### LI — paired Li and Cayley ladders
- Path: prime − Gamma history floor / Cayley ladder positivity → RH.
- Established: guarded history-zero set finite, RH ⇔ empty; ¬RH ⇒ the actual-clock primitive escapes to `−∞`
  with exact normalized limit; RH ⇔ the primitive is eventually bounded below [L/W]; Cayley ladder = Toeplitz
  ladder of `2λ_n`; RH ⇔ every ladder NSD on primitive vectors ⇔ entrywise `≥ 0`; paired Li coefficients never
  tend to `0` [W].
- Open: Li positivity at every order (B1 in Li coordinates).
- Class P4 (Li form of Σ1). B: B1.

### SZ — Suzuki screw
- Path: complete rectangular Ward defect bounded below at one width → RH.
- Established: Suzuki first variation of every Lipschitz compact source equals its complete Weil energy; RH ⇔
  nonnegative first variation on factorial-tent patterns ⇔ eventually on grid-tent patterns; unconditional
  uniform finite-shift deficits on `[−3/10, 3/10]`, odd tests on `[−181/500, 181/500]` (prime 2 active), dyadic
  blocks, polynomial windows and lacunary unions [L].
- Open: the first variation on every pattern (B1 in Suzuki coordinates).
- Class P1 (Krein–Schur face of the window form). B: B1.

### PM — Gauss–Mayer physical realization
- Path: faithful scattering source → Krein/Lewis positivity or pole exclusion → RH.
- Established: S9 [L].
- Open: a nonnegative expression of the defect at resonances without the factor
  `(b^{2σ−½} − b^{−(2σ−½)})²`; mixed-parameter completion, full Mayer transfer, rational Weyl identification.
- Class P3. A: A14, A15. B: B38, B39, B40, B46.

### JAS, CTF, PBM, RB — one-sided counts
- All four are identified with the reflection-pair prime-count band and with each other [L: SWC].
- JAS: square-shell Riesz bounds on infinitely many `m` ⇔ RH; open: uniform arithmetic control. B: B26.
- CTF: bounded real rows reach every tolerance ⇔ RH; open: construct the rows. B: B26.
- PBM: regularized prime-zeta convergence right of `½` ⇔ RH; open: coefficient cancellation. B: B26.
- RB: eventual Robin ⇔ RH; open: square-root remainder on extremizers. B: B26.
- Class P4.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: heat explicit formula, two-grid criterion, arbitrary-zero detector [L]; open: signs at every
  degree/height. Class P5. A: A18. B: B14.
- XN: coverage/self-map criterion; nonnegative Laplacian of the interior margin [L]; open: an actual covering.
  Class P5. B: B14.
- BAG: recurrence receivers [L]; open: arithmetic construction of returns. B: B36.
- EWU: even sign ⇔ Hamburger moments ⇔ reflected trivial-zero form `P ≤ (M − ΣK) + ΣN + 4C²`; neutral signed
  even theta gauge represents the even sector on every window; Markov exactly to `log ρ`, frustrated in every
  sign gauge beyond; signed theta gauges reverse the outside deficit [L]; open: `2V ≤ J_{M⁺}` on every window.
  Class P1 (even sector). A: A5, A33. B: B1, B3, B5, B49.
- GTA: decay criterion; positive charge [L]; open: rank-uniform arithmetic energy decay. Class P5. B: B14.
- OWU: odd ⇔ shifted Hamburger ⇔ antireflected form; odd unit window ⇔ `w₂ ∈ unitBandWeights`; odd sector
  frustrated in every sign gauge from `½log 2` [L]; open: the odd inequality on every window. Class P1 (odd
  sector). A: A5, A33. B: B1, B3, B4, B5, B49.

### SRT, ACT, AIP — complete atomic matrix
- SRT: full-family/index receivers; two real parameters decide the line (`κ_γ(t+v/2) ± κ_γ(t−v/2)`);
  split-column receiver; closed-contact receiver; distinct-cluster threshold [L]. Open: complementary-window
  sign, high-zero tail and source-kernel payment at every ratio. A: A1, A35, A40. B: B6, B7, B12.
- ACT: single-shift receiver `Ẑ(m_au) = 2S_a − D_a + 8V_c + 8τ_cA₂`; shifted ground states exact on every
  window; anti-diagonal classification (nine moduli where the pole pays nowhere) [L]. Open: one shift, uniform
  in profile, paying `D_a` with retained variance. Class P1. A: A19. B: B1, B3, B5.
- AIP: allocation receiver; floors `(1/20000)/2^k` along the tower to `a_∞`; capacity `log log N + O(1)`; literal receiving-charge
  bounds [L]. Open: full-space allocation at every `K`. A: A1, A4, A9, A20. B: B6, B7, B8.

### SC — Stokes/Witt–Krein
- Path: glued affine index `≤ 1` / bounded Gaussian-damped two-prime coupling → RH.
- Established: glued index `κ_ζ + 1`; damped cone ⇔ RH; the damped coupling is an arithmetic heat average of the
  complete compact-test Weil functional [L].
- Open: an arithmetic bound for the damped coupling, sublinear tensor loss, or glued index `≤ 1`.
- Class P4. A: A11. B: B1, B9, B10, B12, B30, B31.

## 4. Candidates

| Candidate | Established | Promotion gap | Strength |
|---|---|---|---|
| ACS | RH ⇔ effectivity ⇔ Hodge index ⇔ section count; primitive `h¹ = Q/2`; Cayley ladder over `𝔽_q` = sharp Weil bound; Legendre `J(ρ)` real ⇔ RH [L] | a non-count source of all-aperture primitive effectivity | B34; count face closed |
| ADO | collide or repel for every monic integer polynomial; impurity quantized; finitely many power sums certify integral purity; integral impure polynomials exist in every degree [L/W] | an integral structure on ζ's zeros (absent); discreteness amplifies a certificate and produces none | closed as a producer |
| APF | Fredholm index; cycle-trace reconstruction | zero-independent divisor exhaustion | B41 |
| BSH | framed curvature | pre-divisor section and mate identity | B41 |
| CDC | calibrated confluence iff `Re s = ½` | source-defined potential forcing confluence | B41 |
| EGC | pole-safe contour; copy correction | outer expanding-contour sign | B15 |
| EWJ | Euler/Wold jets | zero-independent source admission | B41 |
| FEL | theta likelihood; BSY = off-line zero sum | predeclared source balance | B15 |
| FFP | Jensen dictionary, Walsh, Szegő; finite free de Bruijn–Newman law; Euler-factor HB stability with forced drift; mollified Jensen criterion ⇔ RH [L] | a source-faithful stable factorization of `J^{d,n}` or of `Ξ·M_S` at infinitely many degrees | B52, B53 |
| HJ | Hurwitz residual = SEC charge | pre-divisor forcing | B41 |
| IRK | rotation-algebra trace / winding | arithmetic projective lift with integral count (count face closed) | closed |
| MSC | Möbius–Sonin; divisor preservation | bridge to nonnegative Sonin energy | B1 |
| PCS | singular co-shift | source-natural wall annihilation | B41 |
| PTR | lossless stacks, unit port gap | prime-faithful port | B40 |
| RFHM | support grade | symmetry-breaking law | B41 |
| SEC | essential norm = seam jump | pre-divisor compactness at zeros | B41 |
| W1C | Lee–Yang receiver; PM's Krein space and generator; side law | positive arithmetic Hilbert realization | B38, B40 |
| WBF | genealogy Gram | any arithmetic coupling | B41 |
| ZCG | S10 in full | a source-side reality law at near-coincidences (`𝓗 ≥ 0`) with a proved global RH implication | B14, B44 |

### ZCG — zero-configuration geometry (candidate)
- Path: prime explicit-formula image → configuration identification → reality at near-coincidences or
  collision-free deformation → RH.
- Established: S10 [L]. At the square-root aperture the explicit formula fixes ζ's zeros up to clusters of
  diameter `e^{−c log³T}`; inside isolated polynomially small clusters it reads centres, squared gaps,
  discriminants and point locations from finitely many prime-side images; FE-pair squared gaps `≥ 0` at every
  zero ⇔ RH.
- Why a candidate: identification decides nothing alone; no source-side condition with a proved RH implication
  fixes the sign of `𝓗`. The proved repulsion mechanisms (integrality over `𝔽_q` given the disc bound, phase speed above the carrier
  horizon, size-only heat bounds above `½/log X`) do not reach ζ's scale.
- Obstacles. A: A38, A39, A42. B: B14, B44.

### FFP — finite free stability (candidate)
- Path: Ξ (or `Ξ·M_S`) → real-rooted / Hermite–Biehler-stable Jensen polynomials at infinitely many degrees,
  certified by finite free convolution of stable source pieces → RH.
- Established: S12 [L].
- Why a candidate: every source-faithful piece except the Möbius Euler side is unstable (ζ side, Gamma side,
  pole pieces for every phase; theta piece never real-rooted; Dirichlet pieces never real-rooted); the Gaussian
  component is `o(d⁻²)`; the mollified criterion is a receiver whose converse does not use the mollifier.
- Obstacles. B: B52, B53.

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| P1 — signed criticality, `a*(ζ) = ⊤` (≡ `1 ∈ ℋ(c)` ∀c ≡ regular Weil chain); first instances `a*(ζ) ≥ ½` (odd), `≥ log 2` (two weights) | RW, EWU, OWU, ACT, CHMD, TT, SZ, MSC, HF (sign content), ACS (sign content); CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, WVL |
| P1 at large ratios — untwisted windows (`R₁ ≡ ⊤`) | HF, SRT, AIP, SC; CACT, AHD, CSAR, ACPL |
| P4 — one-point square-root precision (the band in prime form; Li form) | WL, MC, PBM, RB, JAS, CTF, LI, SC (coupling), FU, CFC, RP, EGC, FEL |
| P4 — inner caps (off-line generating function) | WD, TG |
| P5 — rank / degree / collision / stability below `½/log X` | TH, HCF, PA, GTA, LA, XN; ZCG, FFP (candidates) |
| P2 — prime-blind positivity / calibration | PBAP |
| P3 — reflection positivity (zero side) | PM, W1C, RN, PTR |
| Γ — trivial gauge point / pre-divisor forcing | BAG, MC; APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| closed — counts / Hodge index | ACS (count face), HF-RR, IRK |
