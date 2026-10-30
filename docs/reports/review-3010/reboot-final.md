# Reboot-final: what the Lean corpus says when it is read as code

Status: 30 October 2026. **RH is open.** Sources are Lean statements and proofs in `formal/GaloisForLFunctions`, the
corpus search tool, and the four review-3010 files named in the task. There were no web searches, no builds and no axiom
audits. The checked facts behind every claim are in the companion log [`reboot-final-facts.md`](reboot-final-facts.md)
(G1–G18). Two short numerical checks are archived in
[`computations/2026-10-30-reboot-final-checks`](../../../computations/2026-10-30-reboot-final-checks/README.md).

| Label | Meaning |
|---|---|
| **[L]** | Lean statement, and usually its proof, read for this report (fact-log entry given) |
| **[X]** | Statement the corpus imports from the pinned external package `Zeta23` (its source lies outside `formal/GaloisForLFunctions` and was not read) |
| **(inference)** | Interpretation by this report; the derivation is given |

---

## 0. The answer in brief

1. **Three kinds of theorems, one of which matters for RH.** The corpus has about 498,000 declarations. Among them are
   1,718 `riemannHypothesis_iff…` and 1,150 `riemannHypothesis_of…` declarations (G8). Its unconditional theorems are
   of two different kinds:
   - **RH-blind theorems** stay true whatever the zeros do: bounded-parameter positivity, uniqueness and rigidity, and
     no-go results.
   - **Zero-constraining theorems** form a small classical core. It proves the Vinogradov–Korobov zero-free region,
     Guth–Maynard large values with the `30/13` density bound, and `≥ 67.25%` simple critical zeros. It also proves at
     least `4/5` of ordinates critical, at least `88.8%` of zero copies simple or critical, and an off-line first moment
     `≤ 0.066 V` (G2, G12).

   Only this core says anything about where the zeros are. Neither review report mentions it. It sits in `RHTower`
   (29,311 files) and the pinned `Zeta23` package, which no README describes.

2. **Why the positivity programmes cannot see zeros at the scales they reach.** The corpus proves the mechanism twice:
   - *Archimedean domination.* For every test of bounded aperture, `ζ`'s localized Weil form is coercive at large height:
     the Gamma density `log|ξ|` beats every prime term (G10).
   - *Growth.* An off-line pair grows like `e^{2δ·scale}` along the Hecke orbit while positive parts stay bounded. A zero
     of depth `δ` at height `γ` becomes visible only at aperture about `(1/2δ)·log log γ` (DCP, APol, HKT; G10).

   So every theorem of the form "positive at fixed overlap, aperture, rank or node set" holds whether or not RH holds.
   The fixed-overlap positivity of the complete Weil matrix is one of them: its margin is the synthesis tail
   `E(c) = (2/M)Σ_k k^{−1}∫_{kc}^∞|φ̂|²`. The corpus defines the critical overlap `c*_N ≍ log log N·(log log log N)²` as
   the point where "the tail energy, which is both the margin of the complete Weil form and its synthesis error, equals
   the Weil weight `1/log N`" (G9).

3. **The surviving counterexample has a definite shape.** The census dichotomy is unconditional. In every large dyadic
   window, either at least `3/4` of the zeros are critical, or at least `17%` are *simple off-line zeros within `A/log T`
   of the line*; the first moment `Σ(β − ½) ≤ 0.066 V` says the same on average (G2). The obstruction is therefore
   **microscopic near-line pairs**, not deep zeros. Every engine in the corpus is blind to them in a precise way:
   - the explicit-formula Gram census cannot tell such a pair from a double critical zero (*coalescence blind spot*, G14);
   - Weil positivity sees them only at aperture `≈ log T·log log T` (G10);
   - heat flow heals them in time `≈ δ²` (`Λ ≤ Θ²/2`, G7).

   Electrostatics is the one exception. Such a pair carries a partner field `1/(2δ) ≈ log T/(2a)`, far above the
   `√(2c log γ)` threshold whose violation the corpus shows is equivalent to an off-line zero (G15).

4. **The scarce resource is information beyond bandwidth one.** The explicit-formula census stops at `λ = 1`, where
   Montgomery–Vaughan kills every off-diagonal prime pair. Past it, the only new term is the *signed correlation of close
   prime pairs* `|log(n/m)| ≲ 1/T`; the corpus has reduced this to one open input, the "centred stabilizer discrepancy"
   (G3). The complete-Weil route needs the same scale. Its quasimode error is a fixed `O(1)` boundary layer at the
   horizon `n ≈ N`, of relative size `(log N)^{−1/2}` (proof read, number computed: G9, G13). The RH schedule needs every
   multiple `K·c*_N`, where the margin is `(log N)^{−K'}`.

5. **Both reports read the corpus through its positivity READMEs and inherited its frame.**
   - Opus turns the Weil-cone uniqueness theorem into "rigidity, not estimation". But the engine of that theorem builds a
     `Ξ`-divisible blind family that exists whether or not RH holds (G1). The corpus's only zero-constraining theorems are
     estimates. Opus's own "unconditional global theorems" table includes a theorem whose proof uses Mertens' theorem and
     a spectral floor (G9, G19). Its first-priority target `WindowPositive` is a short-window inequality for nonnegative tests,
     which no corpus theorem connects to RH (G5).
   - Astra's meta-lesson ("keep the signed interaction") is sound. But each of its four directions starts from an RH-blind
     theorem, and it calls fixed-overlap positivity "real progress" without asking what that positivity can see.

6. **Where to look (inference).** At the scale below the mean zero spacing, near the critical line, with information
   beyond the Nyquist bandwidth. The corpus names three concrete carriers of that information:
   1. signed close prime pairs, i.e. the coalescent band of TTPC;
   2. an exact boundary-layer analysis of the complete Weil matrix at the critical overlap;
   3. an arithmetic upper bound of size `o(log γ)` on the transverse field at zeros.

   §6 turns these into work packages. None is a reformulation of RH. Each has a first theorem that would be new and
   would constrain zeros.

---

## 1. How the corpus was read

- **Census of the code.** The corpus has 53,234 Lean files and about 2.37 M lines. `RHTower` (29,311 files) and
  `HTGeometry` (18,918) hold 91% of the files and have no README. The two reports worked mainly from the READMEs of
  about 53 programmes, which hold the remaining 9%.
- **Proofs read** (not just statements):
  - Weil cone uniqueness and its family-rigidity step.
  - ArithmeticResonanceTheory: the realization theorems (all 12 modules; four read in full).
  - The fixed-overlap positivity assembly: reserve, capture lemma, quasimode residual, residual budget, decomposition.
  - The HKT index law, the pair-growth argument and the Lindelöf law; AKLT fine towers.
  - The DCP domination and visibility theorems; the APol odd-sector detector.
  - The rank–trace slack (`RankTraceSpectralSlack`); the de Bruijn–Newman strict bound; the Hölder-realization strip;
    the even and virtual realization no-gos.
  - The `WindowPositive` reduction; the TMWP rate and critical-overlap modules.
- **Statements and docstrings read**: Zeta23 census modules; TTPC; ACS blind spot; AES electrostatics; SquareRootThreshold
  "one zero width"; CCM Bombieri–Yoshida; Deninger capstones; `RHTower/Sieve` (VK, Guth–Maynard); InfiniteSymmetry;
  ThetaCusp and HTGeometry surveys; flip-threshold and selectivity modules.
- **Numerics** (G13): the census constants, the GUE ceiling of the rank–trace method, and the size and location of the
  horizon boundary budget. One further computation (the bottom eigenvalue of `log N·I − P_N`) was not run, because its
  outcome follows from the corpus identities; the prediction is recorded in the computations note.

---

## 2. Audit of `opus-reboot.md`

| Claim | What the code says | Verdict |
|---|---|---|
| "The corpus has stopped being an estimation problem… Positivity proofs with margin cannot exist; this is a theorem, not a pattern. Estimates are the wrong instrument." | The cone theorem fixes the **weights** at `Λ` given ζ's Gamma factor and pole. It says nothing against a proof of `W_Λ ≥ 0` that uses `Λ` exactly. The corpus has positivity **with** margin wherever the test class is restricted: eigenvalue floor `e > 0` at every fixed overlap (G9). It has RH-equivalents with explicit slack: window energy `< 2`, transverse field `< √(2c log γ)` (G15). And the **only** unconditional theorems that constrain zeros are estimates (G2, G12). | False as stated |
| The Weil cone uniqueness theorem "uses neither primes, nor estimates"; it is "the only global, unconditional theorem about the Weil cone". | Correct description of the theorem (G1). Its engine (twisted-arc minimum principle, Prokhorov, Hahn–Banach) produces a family with `F̂ = Ξ·Q_j` that vanishes at **every** zero of `Ξ` wherever it lies. The proof localizes the spectral measure of any positive candidate onto critical zeros. The construction is identical whether or not RH holds; it is a uniqueness theorem. | True; it decides nothing about zero location |
| "RH has a prime-free form… The only arithmetic left is the node set `{log n}`." | `primeBlindPositiveOn_iff_weilPositiveFull_vonMangoldt_and_support`: positivity on a node set `S` ⇔ `W_Λ ≥ 0` and `S ⊇` prime powers (G1). The node set **is** the primes; only the weights vanish. Prime-blind positivity is the Farkas dual of Weil positivity. | Weight-free, not prime-free |
| "The primes are an output… `Λ` is the shadow price." | `nodeValue_eq_vonMangoldtPairing` holds **under RH**; without RH every fibre is unbounded below. This is LP duality restated. | Conditional restatement |
| D1.2: "A modular-potential proof of `WindowPositive` on all of `(0, log 2)`." | `WindowPositive` concerns bounded **nonnegative** `h` vanishing off `(0, log 2)`. Such tests have autocorrelation that never reaches a node `log n`. It implies prime-blind positivity only on the nonnegative single-test cone, and no corpus theorem links that cone to RH (G5). It is a Yoshida-type short-window statement. | Not an RH-strength target |
| D1: "Attack the open half with the same instrument (potential theory on `SL₂(ℤ)\ℍ`)." | The minimum principle's dual output is an annihilating measure, i.e. a null object. The dual of prime-blind positivity is Weil positivity itself, so there is no second half for the same tool to win. `InfiniteSymmetry/TheChamberIsSilentOnTheStrip`: a-priori automorphic information certifies exactly `{Re ρ ≥ 1}`. Entirety of cuspidal loop Eisenstein series certifies nothing about zeros of `Ξ` (G6). | No mechanism; the corpus's own modular modules reach only the PNT line |
| "Over `𝔽_q` … the Weil-positive weights form the large convex set… The 𝔽_q problem has room." | The set is large, but the **actual** curve sits on its boundary: its trace kernel is a finite sum of `2g` unitary characters, of finite Toeplitz rank (HKT `negIndex_expSum`). Weil's proof is no cone argument. In corpus terms the decisive `𝔽_q` feature is a finite-rank odd part (finite virtual realization, Kronecker rank 1). Over ℤ the archimedean place forbids it: the trivial zeros on a real progression kill any finite odd determinant (G11). | Wrong explanation of the 𝔽_q/ℤ difference |
| §2.4 table: the mechanisms listed, including `eventually_noRealZero_completeWeilMatrix_posDef`, "spend no margin and use no estimate of a prime sum". | That proof uses an eigenvalue floor `e/2`, Mertens' theorem (`tendsto_mertensSum_sub_log` in `TheUpwardPrimeRowsRealizeTheCompletedShellCorrection`), the quantitative Mertens deviation (`exists_global_mertensDeviation_exp_sqrt_log_bound`), and prime-window asymptotics (G9, G19). | False |
| §3.3: at growing overlap "the modular null vectors of §3.1 become visible and the margin `E_1(c) ≍ c^{−7}` tends to zero". | The margin is the completed shell energy, the Fourier tail `∫_{kc}^∞|φ̂|²` of the profile (G9). It vanishes because the atomic family synthesizes finer tests, and `c*_N` is defined by margin = synthesis error = `1/log N`. No modular object appears in these proofs. | Unsupported |
| §5.4: `SL₂(ℤ)` "is generated by the two selective structures". | The twisted-arc proof uses the half fundamental domain and its corner at `ρ = e^{iπ/3}` (the `√3` in `∂_y∂_xψ(ρ) = √3(G′(½) − 2G(½))`). No theorem relates selectivity to `SL₂(ℤ)` as a group. | Numerology |
| "Rank ∞ also helps. Two primes carry the whole index." | The two-prime and consecutive-tower laws use only that the log-scales of the subgroup are dense, or tend to `0`. Any dense subgroup of ℝ would do (G10, G18). The Hecke lattice enters as a topology, not as arithmetic. | Correct statement, misread as arithmetic |

**What Opus missed.** The classical engine (G12), the Zeta23 census and its dichotomy (G2), the bandwidth barrier (G3), the
coalescence blind spot (G14), the critical overlap and boundary layer (G9), the domination–growth mechanism (G10), and the
corpus's own unification of the walls into one number `Θ` (G16).

**What Opus got right and this report keeps.** Cone uniqueness is unconditional, so `W_lam ≥ 0` for **any** weight
already forces RH. The corpus's selective structures are the pole, the Gamma factor and additive (successor/Bézout)
structure. Over ℤ the 𝔽_q tools that place a curve inside the cone (Riemann–Roch effectivity, Frobenius, the twist tower,
flat Stepanov coefficients) are proved absent.

---

## 3. Audit of `what-the-corpus-is-telling-us.md` (Astra)

| Claim | What the code says | Verdict |
|---|---|---|
| Meta-lesson: arithmetic information survives in signed comparisons, output norms and mixed terms that positive objects discard. | Supported by the cited theorems (cofactor graph, scale separation, Sonin radical, prime comb). Every one of them is RH-blind: a theorem about a representation, not about zero location. | Sound but insufficient |
| §7: "The mature Weil route has real progress"; fixed-overlap positivity "crosses the separated-atom and entrywise-sign boundaries". | True as positivity. The fixed-overlap atomic Gram has index `0` while the index along the Denjoy–Carleman schedule tends to `κ(K_ζ)` = number of right zeros (`dcProfile_atomicGram_reaches_index`). At fixed overlap ζ is positive whatever its off-line zeros, while the tempered isolated pair fails (G4). The margin is synthesis coarseness (G9). Large-prime flips are invisible below `c ≍ p^{1/8}` (G18). | Progress in positivity, none in zero location |
| §7: the polynomial reserve `W ≥ ac^{−7}D − Cc⁹‖x‖²`; "sixteen is the exponent of this estimate, not a proved optimum". | Correct. The code shows two further bottlenecks Astra does not name. The capture lemma needs prime thresholds `P > exp(2C(K+1)/η)`, a doubly exponential conductor range. The quasimode residual decays only like `(c⁵/log N)^{1/2}`, from a fixed horizon boundary layer (G9, G13). | Correct, incomplete |
| §8A: nonlinear source readings (CDG) and heat dynamics as "the most substantial alternative". | Per Astra's own fact F17 (`polynomialThetaSource_uniform_test_aperture_moments`), CDG recovers the divisor from prescribed theta prefixes by regularized curvature and Green testing. This is generic complex analysis on approximants of `ξ` that finds zeros wherever they are. The heat inequality balances local energy against an outer flux with no source-side bound. Astra notes both caveats but does not draw the conclusion: neither is a source of zero-location information without a comparison inequality the corpus does not have. | Overrated |
| §8B: complete quadratic comparisons (Hermite congruence for theta, Weil prefix Schur). | The Hermite comparison needs `q(x) ≥ 16(N+2)²`, a bounded-rank regime; the prefix theorem pays a prefix uniformly. Both live where domination holds. | Bounded-parameter |
| §8C: source selection at counting precision (gauge stabilizer of the count). | Exact classification for variable sources; at `Λ` the count is RH. It tells which perturbations a proof may ignore, not how to prove the count. | Correct, not a route |
| §6: several purported universal obstructions are narrower than claimed. | Correct and valuable (quantifier audit of holomorphic carriers, the signed Gram table, the tent rigidity). | Kept |

**What Astra missed.** The same classical core as Opus, plus TTPC and the coalescence blind spot, which are the corpus's own
location of the square-root wall in the zero census.

---

## 4. What the code says

### 4.1 The census: what in the corpus constrains zeros at all

| Theorem (unconditional) | Content | Mechanism |
|---|---|---|
| `riemannZeta_ne_zero_vinogradovKorobov` [L G12] | no zeros for `β > 1 − (log γ)^{−2/3}(log log γ)^{−5/3}/10⁸` | growth blocks for ζ near `Re s = 1` and a log-derivative step (`VinogradovZetaGrowthBlocks`, `VinogradovKorobovLogDeriv`, G19) |
| `guthMaynardLargeValuesBound_holds` + `30/13` density [L G12] | `#{ρ : β ≥ σ, γ ≤ T} ≪ T^{(30/13+ε)(1−σ)}` | large values of Dirichlet polynomials |
| `simple_critical_proportion_ge_67250071` [L/X G2] | `≥ 67.25%` simple critical zeros | explicit formula sampled at zero ordinates, rank–trace inequality, Montgomery–Taylor window; IGP non-lattice slack |
| `four_fifths_critical_ordinates`, `simple_or_critical_optimal` [L G2] | `≥ 4/5` of ordinates critical; `≥ 88.76%` of copies simple or critical | same certificate, recounted |
| `eventually_offLineMoment_le_montgomeryTaylor` [L G2] | `Σ m(β − ½) ≤ 0.066 V` | Selberg mollifier + census density |
| Zeta23 near-line dichotomy [L G2] | `≥ 3/4` critical, or `≥ 17%` simple off-line zeros within `A/log T` of the line | census + first moment |
| `newmanConstant_lt_eighth`, `newmanConstant_nonneg` [L G7] | `0 ≤ Λ < 1/8` (`Λ < ½` in standard normalization) | heat-flow barrier dynamics; Dirichlet-series model at negative time |

Every row is a mean-value, mollifier, exponential-sum or heat-flow argument. No row comes from a positivity, rigidity,
gauge, Hodge, Krein–Langer, realization or carrier programme. **(inference)** These programmes have produced many
correct theorems, none of which constrains where the zeros are.

### 4.2 The domination–growth law

The corpus proves both halves of one law.

- **Domination at bounded scale.** For a test `f` supported in `[−a, a]`,
  `Re W_ζ(S_ξ f) ≥ (log(1 + π|ξ|/4) − horizonExponent(e^{2a}) − 2·pairEnergy)∫|f|² − B²/(8(1+π|ξ|))`, so `ζ`'s
  localized form is `L²`-coercive above an explicit height (`exists_height_horizon_zetaZeroConfig_re_W_ge_norm_sq`, G10).
  The archimedean density `log|ξ|` grows; bounded-aperture prime terms do not.
- **Growth at unbounded scale.** On the family `u^d, u^{N+d}`, an off-line pair contributes
  `−2|ω||w|^N|a|²` with `|w| > 1`, while a positive-definite part is at most `p(1)(Σ|c|)²`. "A positive part never pays a
  pair" (`negIndex_add_sum_pairKernel_eq`, G10).
- **The crossover scale.**
  - A diluted off-line crystal of depth `d` on a background of density `L/2π` is invisible below aperture
    `(1/2d) log(L/ℓ)` and visible above it (`exists_diluted_pattern_visibility_constants`).
  - A single off-line zero of depth `δ` at height `γ` is detected by the twisted sinh detector once `e^{2δa}` beats
    `log γ` up to polynomial factors (`odd_sector_nonneg_forces_offLine_companion`).
  - CCM's ground energy decays like `−e^{2ΘB}/B³` when the top depth is attained (G16).

**Consequence (inference).** Fix any parameter that bounds the scale: aperture, overlap, rank, number of nodes, or tower
range. A positivity statement at that parameter is then either false for ζ or true independently of RH. The corpus's many
"positive up to X" theorems are of the second kind:
- Yoshida-type windows (`WindowPositive` up to `12/25`);
- CCM positivity at aperture `√2` with right continuity;
- atomic-resolution stability (AES, SSHA);
- fixed and bounded overlap (CACT, TMWP);
- finite-node blind slack (`BlindSymbolSlack(−γ(0) − 2)`).

Every RH-equivalent statement in the corpus puts the parameter at infinity.

### 4.3 The complete-Weil route at its critical overlap

The architecture of fixed-overlap positivity (G9) is:

```
reserve  a‖x‖² + β·D_N(x) ≤ W_N(x)                    (Gamma reserve + prime defect)
capture  D_N(x) ≤ K  ⇒  x ≈ span{ Ramanujan profiles r_m : m | box(P, L) },  P > exp(2C(K+1)/η)
quasimode ‖W_N r̂_m − E_m(c) r̂_m‖² ≤ K_m (c⁵/log N + c¹⁰(log N/N)²)
floor    E_m(c) ≥ E_1(c) = (2/M) Σ_k k^{−1} ∫_{kc}^∞ |φ̂(2πt)|²
```

Four facts follow from the code.

1. **The margin is the synthesis tail.** `E_1(c)` decreases to `0`. The corpus's critical overlap `c*_N` (least `c` with
   `μ_B(c)² log N ≤ 1`) is where this margin equals the Weil weight `1/log N`.
   `riemannHypothesis_iff_forall_critical_multiple`: RH ⇔ eventual positivity at **every** bounded multiple `K·c*_N`.
2. **The quasimode error is a boundary layer, not a prime error.**
   - The pure prime residual on `r_m` is bounded uniformly in `N` (`exists_uniform_ramanujanPrimeResidual_family_bound`).
   - Its source is the Mertens remainder `R(y) = A(⌊y⌋) − log y + γ` at `y = N/n`.
   - Numerically, the pole-vector budget is `0.0832` at every `N` from `10⁴` to `2·10⁶`, and `96.5%` of it comes from rows
     `n > N/16` (G13).
   - The normalization `‖r_m‖² ≍ log N` alone produces the relative `(log N)^{−1/2}`.
   - The profile `R(y)` does not depend on `N`.
3. **The capture is doubly exponential.** The defect bound `K ≈ |a|/β` enters through `P > exp(2C(K+1)/η)`, and the
   conductor set is the divisors of a `P`-smooth box. The true low spectrum, by `eventually_fullPrime_spectral_count_eq`,
   needs only conductors with `E_m ≤ T`, i.e. `m ≲ e^T`. The lemma is crude by one exponential.
4. **Bounded overlap separates the pole, not the zeros.** Pole-free twins (Liouville, every cofinite flip) fail above the
   Robin–Euler ratio. A flip at a prime `p` is invisible below `c ≍ (√p/log p)^{1/8}`. Off-line zeros are invisible at
   every fixed `c` (G4, G18).

**Inference: what the RH schedule asks of this architecture.**
- For a Denjoy–Carleman profile, `log(1/μ_B(c)) ≍ c/(log c)²`. The margin at `K·c*_N` is therefore about
  `(log N)^{−K·const}`.
- The quasimode error is `(log N)^{−1/2}`. Even with the capture made effective, the assembly can therefore reach only
  about `c*_N/2`.
- RH needs every `K`. Two things are missing:
  - control of the horizon boundary layer to relative precision `(log N)^{−A}` for every `A`;
  - a proof that its correction to the low conductor modes `m ≲ c/c*_N` is nonnegative.

  Both concern a fixed, `N`-independent half-line operator in the variable `u = log(N/n)`. Its profile is `R(e^u)`
  together with the archimedean boundary terms. The corpus already has a model of this kind for a different prime kernel
  (`PoissonPrimeKernelCalkinModel`: a Mertens clock turns a prime kernel into a Wiener–Hopf operator on the half-line,
  up to a Hilbert–Schmidt error).
- This is the sharpest form of the complete-Weil problem the corpus supports. It is still RH: under RH the full matrix is
  PSD at every overlap, so the boundary correction at the critical scale must have the right sign.

### 4.4 The census engine and its walls

The mechanism (G2, `RankTraceSpectralSlack`):
- Sample the explicit formula at zero ordinates. This gives the hat-unit Gram matrix `Â = P + Q`: `P ⪰ 0` from critical
  zeros, `Q` from off-line pairs.
- The prime side computes `tr Â` and `‖Â‖_F²`.
- `c·tr P − (c²/4) rank P ≤ ‖P‖_F²` turns these into a lower bound for the rank, i.e. a count of simple critical zeros.

Four walls, all in the code:

1. **Bandwidth.** The window validity `λ ≤ 1` is used only on the prime side; the zero-side inputs hold for every `λ`
   (`Zeta23FamilyBandwidth`). At `λ ≤ 1`, `κ = 1/λ + λ/3 ≥ 4/3`.
2. **Coalescence blind spot.** A double critical zero and a coalesced off-line pair give the same `Â`. No functional of
   `(Â, N)` beats `(2 − κ)N` there. An isolated off-line pair at displacement `a = (β − ½)log T` contributes eigenvalues
   `m(g+1)`, `−m(g−1)` with `g − 1 → 0` as `a → 0` (G14).
3. **Higher moments.** The cubic moment adds nothing at the blind spot. The quartic moment needs `λ < 1/2`, and
   `kλ ≤ 1` caps the `k`-th moment (`higherMoment_rudnick_sarnak_cap`, G3, G14).
4. **Ceiling.** With the GUE form factor at every bandwidth, `2 − κ = 1 − 1/(3λ²)`, which tends to `1` and never
   reaches it (G13). Even full pair-correlation knowledge cannot make this engine prove RH. It can, however, shrink the
   surviving counterexample class.

TTPC has made the first step past wall 1 exact:
- At `λ = 4/3` the certificate is `N₀* ≥ (29/36 − ε)N − coalescentSurplus`.
- The surplus reduces to odd primes at even shifts.
- That sum equals a parity-locked Ramanujan stabilizer model, which transfers to the negative Ward–Mertens repulsion,
  plus a **centred stabilizer discrepancy**. That discrepancy is the single open input (G3).
- Budget ladder: `β < 5/36` beats `2/3`; `β ≤ 577/4500` beats `HD(1)`; `β ≤ 1/18` gives `3/4`; the Hardy–Littlewood value
  `−1/144` gives `13/16`.
- The corpus's only prime-pair inputs are upper-bound sieves (G3). Its short-interval engine (Matomäki–Teräväinen
  Type I/II, Guth–Maynard) has not been connected to this sum.

### 4.5 One number

`TheWallsMeasureOneZeroWidth` proves that the deficit primitive, mean-square bands, Suzuki formation energy, Möbius–divisor
Abel exponents, the lag family, the CCM ground energy, the heat time, the Balazard–Saias–Yor integral and node criticality
all read `Θ = sup|Re ρ − ½|` (G16). BSU's README states the matching discipline: "Every receiver reads one number…
A reformulation in another unit is not progress."

**(inference)** By the corpus's own `Θ` theorem and BSU's criterion, an RH equivalence adds information only if it brings
a mechanism that bounds `Θ`. This review did not classify all 2,868 reductions. A text scan finds 186 equivalences whose
right-hand side names the zero set or off-line zeros explicitly (G19), which makes them relabelings. ThetaCusp holds sixty
equivalences in "Hawking/Parikh–Wilczek/Teukolsky" vocabulary; the one inspected
(`…CompleteEvaporationQuadraticEnergy_zero`) quantifies over the zero set.

The graded statement `Θ < ½` (any zero-free strip) is open, and the corpus has no mechanism for it. Its candidate inputs
are:
- a Hölder realization, which would give a strip (G11);
- power saving in balanced short windows, which is equivalent to it (G12).

### 4.6 Realizations and carriers

- **No finite realization.** A finite graph zeta has no zeros. A finite virtual realization `det(1−M⁻)/det(1−M⁺)` is
  impossible because the trivial zeros put zeros of an exponential polynomial on a real progression (G11).
  **(inference)** The same should hold for `ξ`, which has no trivial zeros. An exponential polynomial with real
  frequencies has `O(T)` zeros up to height `T` (standard counting, not checked in the corpus), while `ξ` has
  `≍ T log T`. Both obstructions are archimedean.
- **Additive realizations are commutative.** Two first-return words concatenate to length `log p + log q = log pq`.
- **Hölder realizations are squeezed by integrality.**
  - Along `u^n v`, the prime lengths satisfy `p(n+1) = a·p(n)·e^{δ_n}`, `|δ_n| ≤ 2Cθ^{nL}/(1−θ)`.
  - Super-conformal distortion forces composites.
  - Conformal expansion (the geodesic-flow regime) forces an affine recurrence, which primes never obey.
  - Only "rougher than conformal" roofs remain (`θ·e^{φ(a^∞)} ≥ 1`), and any such realization would already give a
    zero-free strip (G11).
- **Deninger carriers.** The corpus built carriers indexed by the zeros and proved they carry "no information beyond RH
  unless … built independently of the zeros". Conformal positivity "does not constrain the location of the spectrum". The
  one carrier type left unexcluded is "a geometric carrier with structural positivity (a category with ζ as one member
  among many)" (G17).

### 4.7 Uniqueness and rigidity

These theorems are RH-blind in the strict sense:
- Weil cone uniqueness (G1);
- theta rigidity and completed positive systems (opus-reboot-facts F10);
- the Krein–Langer index law, whose two-prime and consecutive-tower forms use only density of log-scales (G10, G18);
- Stepanov compressions: a PD compressor must vanish at one character of every off-line pair, which requires knowing the
  pairs (G10).

Their content is that the class of objects is a point or that the index is a zero count. They make RH well posed and do
not advance it. The corpus also contains the reason: MPG's interior invisibility and InfiniteSymmetry's closed chamber
show that positivity, integrality and automorphy certify the boundary line `Re s = 1` and nothing inside (G6).

### 4.8 Statistical versus individual

AES formulates the distinction itself: "Averages, proportions and almost-every statements place most zeros near the line
and exclude none: excluding an individual zero needs control below the zero spacing." Quantized forms give slack:
- RH ⇔ every unit window has transverse energy `< 2`;
- RH ⇔ every right zero feels field `< √(2c log(|γ|+4))`.

Each off-line zero carries at least one quantum, and every off-line zero has a terminal whose field is at least
`1/(2δ) + cδ log γ` (G15).

**(inference)** For a near-line pair (`δ = a/log γ`) the partner term alone is `log γ/(2a)`. An arithmetic upper bound on
the transverse field at zeros of size `o(log γ)` would therefore exclude every near-line pair with `a` bounded, which is
exactly the class the census cannot exclude. The two engines have complementary blind spots:

| | census | electrostatics |
|---|---|---|
| blind to | near-line pairs | deep zeros |
| loud on | deep zeros | near-line pairs |

The missing piece is the field upper bound. The corpus has only the external law for `Re s > 1` and large-value counts of
prime polynomials at zero ordinates.

### 4.9 The convergence point

| Engine | How it treats a simple off-line pair at displacement `a/log T` | Corpus anchor |
|---|---|---|
| Explicit-formula census, `λ ≤ 1` | indistinguishable from a double critical zero as `a → 0` | G14 |
| Weil positivity (aperture `A`) | visible only for `A ≳ (log T/2a)·log log T` | G10 |
| Complete Weil matrix, fixed overlap | invisible; positivity holds regardless | G4, G9 |
| Krein–Langer index on `ℚ_{>0}` | one negative square, visible only along unbounded orbits | G10 |
| Heat flow | healed in time `≈ δ²`; `Λ ≤ Θ²/2` | G7, G16 |
| Electrostatics | partner field `≈ log T/(2a)`, far above threshold | G15 |
| Density / VK | not excluded; only deep zeros are rare | G12 |

**(inference)** The table is the corpus's answer to "where must the solution live". It must exclude, individually,
simple pairs at microscopic horizontal displacement, at every height. The deep zeros are already statistically marginal.
Everything the corpus has proved about positivity happens at scales where such pairs cannot be seen.

---

## 5. What the corpus hints at

1. **Measure progress by visibility, not by equivalence.** Every new theorem should answer two questions: does it
   constrain zero locations unconditionally, and at which scale does it see a pair at displacement `a/log T`? Corpus
   instruments to apply: BSU's criteria, the `Θ` theorem, the AES principle, the ACS blind spot.
2. **The obstacle is microscopic and near-line.** The unconditional census already confines any counterexample, on
   average, to `O(1/log T)` from the line. Deep-zero exclusions (zero-free strips) are a separate, also open, problem
   (`Θ < ½`) that RH-oriented work does not need to solve first.
3. **The archimedean place does two jobs.** Its density `log T` makes every bounded-scale positivity statement true, and
   by the same token blind. It also forbids finite odd parts (ART), which is why the 𝔽_q template cannot transfer.
   Opus's "the archimedean place is the source of rigidity" is right about uniqueness. As a source of positivity it is the
   reason positivity has been easy and uninformative.
4. **Information beyond the Nyquist bandwidth is the resource.** The corpus has identified exactly where it would enter
   in three dialects:
   - signed close prime pairs, at shift range `X/T`;
   - the horizon boundary layer of the complete Weil matrix at relative precision `(log N)^{−A}`;
   - an upper bound for the transverse field at zeros.
5. **Families are not excluded.** Opus's "ζ is isolated; arguments over a family have no family" refers to positive
   deformations at pole order one. The corpus leaves two other kinds of family open:
   - the Deninger analysis leaves exactly "a category with ζ as one member among many";
   - `Zeta23FamilyBandwidth` prepares the zero-side inputs for family bandwidth above `1`.

---

## 6. Research programme

Each work package names its corpus entry points, a first theorem, what counts as success, and what would retire it.
Packages A and B are RH-sensitive partial results; C is an RH-equivalent target in its sharpest available form; D is a
graded target; E is hygiene.

### WP-A. The census past bandwidth one

- **Entry points:** `TransThresholdPairCorrelation` (`zeta_coalescent_certificate_four_thirds`,
  `oddEvenShiftPrimeCoalSum_eq_stabilizerModel_add_discrepancy`, `coalescent_budget_thresholds_for_two_thirds_HD_one_and_three_quarters`);
  `RHTower/Sieve` (Matomäki–Teräväinen Type I/II, `guthMaynardLargeValuesBound_holds`, short-window prime theorem at
  `17/30`); ACS `CoalescentSurplusAndTransThresholdProportionLaws`.
- **A1 (first theorem).** An unconditional bound for the centred stabilizer discrepancy, averaged over shifts
  `h ≤ X^{1/4}` with TTPC's smooth window kernel at `λ = 4/3`. It must be strong enough to give
  `PrimeCoalescentSurplusAtMost β` with `β ≤ 577/4500`, measured in TTPC's normalization `(aL)²Tℓ₁/2π`. That alone gives
  a simple-critical proportion above `HD(1) = 0.6725`. Budget `1/18` gives `3/4` and the off-line moment `57/1000`.
- **A2.** Decide whether the short-interval machinery already in `RHTower/Sieve` evaluates the signed sum. The required
  shape is a weighted shifted convolution `Σ_h w(h)Σ_n Λ(n)Λ(n+h)` with oscillating weights over a short range. Either
  prove the needed Type I/II estimates or record the exact range where they stop.
- **A3.** Family version: run the rank–trace certificate on a family of Dirichlet `L`-functions with the prime side
  measured against the family conductor (`Zeta23FamilyBandwidth` supplies the zero side). Success means a family
  proportion above `HD(1)`. This tests the mechanism; it does not transfer to ζ.
- **Retire when:** the discrepancy is shown to require Hardy–Littlewood-strength input at fixed shifts. Record the
  surviving averaged statement.

### WP-B. Microscopic pairs, individually

- **Entry points:** AES (`TheFieldLawHasAThreshold`, `TheExternalFieldIsAPrimeSum`, `LargeValuesAtZeroOrdinates`,
  `HigherMomentsAtZeroOrdinates`); ACS blind spot (`onSlack`, `negPart_credit_pos_iff_not_posSemidef`); Zeta23
  near-line dichotomy; heat (`le_newmanConstant_of_offLine_zero`, `newmanConstant_le_half_sq_zetaZeroWidth`).
- **B1 (dictionary).** For a simple off-line pair at displacement `a/log T`, compute the exact response of each corpus
  observable as a function of `a` and the scale parameter: census slack `g(a) − 1`, the hyperbolic eigenvalue of the
  sampled Weil matrix, transverse field, window energy, heat time, atomic negative index. Put them in one table with the
  corpus theorem behind each entry. This is mostly assembly; it fixes the target for B2.
- **B2 (first theorem).** An unconditional upper bound on the transverse field at zeros that is `o(log γ)` on a set of
  zeros of positive proportion. Equivalently, a positive proportion of zeros with no off-line partner within
  `ε/log γ` horizontally. Compare `HorizontallyIsolatedSimpleZeros` (`≥ HD(1)` isolated at `5/(2 log T)`, but only among
  critical zeros). Success means the near-line branch of the Zeta23 dichotomy shrinks below `17%`.
- **B3.** An arithmetic observable of the split `(P, Q)` that `Â` discards, for example the Levinson detector or Speiser
  zeros of `ξ′`. `SpeiserDeficitTwoThirds` already ties right zeros of `ξ′` to off-line multiplicity. Success means a
  functional that separates `doubleZeroBlockData` from `coalescedPairBlockData` and is computable from the prime side at
  `λ ≤ 1`.
- **Retire when:** B1 shows every observable has the same `a → 0` degeneracy order. That would be a new no-go, to be
  recorded with its exact exponent.

### WP-C. The complete Weil matrix at the critical overlap

- **Entry points:** CACT `MacroscopicOverlapSpectralAssembly`, `CompleteConductorResidualsRetainTheirHorizonDecay`,
  `TheCompleteWeilGroundStateIsThePole`; RAPT `BoundedPrimeDefectHasFiniteRamanujanApproximation`,
  `eventually_fullPrime_spectral_count_eq`; TMWP `TheCriticalOverlapIsLogLogTimesLogSquared`,
  `ABoundedOverlapRateSeesASemilocalWindow`, `TheSincProductProfile`; `RHTower/PoissonPrimeKernelCalkinModel`
  (half-line model).
- **C1 (first theorem).** Effective fixed-overlap positivity for one tilted Denjoy–Carleman profile without real Fourier
  zeros, with an explicit horizon `N₀(c)`. Replace the capture set by the spectral sublevel (conductors with
  `E_m(c) ≤ T`).
  - Success: `log log N₀(c) = O(c/(log c)²)`, i.e. positivity at a fixed multiple of `c*_N`.
  - By `nonneg_of_critical_multiple` this gives semilocal Weil positivity on `[−R, R]` once the multiple exceeds
    `32e·24e·B⌈1 + e^{2(R+1)}⌉`. That would be a new unconditional theorem for each `R` beyond the Yoshida window, and
    still RH-blind beyond its window.
- **C2 (the boundary operator).** Derive the `N`-independent limit of the complete Weil matrix near the horizon in
  `u = log(N/n)`: Mertens profile `R(e^u)`, center collar, non-ratio successor star. Compute its first-order effect on
  the conductor modes `m ≲ c/c*_N`.
  - Success: a sign theorem for the `1/log N` correction at the critical overlap.
  - Falsifier: a negative correction with nothing in the archimedean terms to compensate it. Under RH that cannot happen,
    so it would point to an error in the decomposition.
- **C3 (computation, only if C2 cannot be settled on paper).** On the runpod, the bottom eigenvalues of the literal
  complete Weil matrix against `c ∈ [1, c*_N]` and `N ≤ 10⁵`, against `E_1(c)`, to measure the boundary correction. The
  pure prime part need not be computed; its behaviour (`γ − κ/log N`, from below) follows from the identities (see the
  computations note).
- **Retire when:** C2 shows the boundary correction depends on zeros at height `≈ N/c` at leading order. Then the
  critical-overlap problem is the zero problem again, and the route closes as "reformulation".

### WP-D. The graded target `Θ < ½`

- **Entry points:** `SquareRootThreshold/TheWallsMeasureOneZeroWidth`; `ReflectiveDirichletPolynomialS2`
  (`moebius_and_prime_powerWindowSaving_iff_quasiRH`); ART `riemannZeta_ne_zero_of_holderRealization`,
  `one_le_exp_mul_of_isPrimeLength`; `RHTower/Sieve` large values.
- **D1.** Determine whether the Guth–Maynard large-values engine gives any power saving for the Möbius row in
  balanced short windows `Q^α`, `Q ≍ P`. The corpus proves that saving is equivalent to quasi-RH, so a partial result
  must be stated with its exact range of `α`.
- **D2.** Quantify the Ruelle–Pollicott strip width `ε` of `exists_holomorphic_reciprocal` as a function of the Hölder
  modulus `θ`. Combine it with the integrality lower bound `θ·e^{φ(a^∞)} ≥ 1`. Either a prime-length Hölder system is
  forced to have `ε → 0`, which is a new no-go, or a window for it remains.

### WP-E. Corpus hygiene

- Every new RH equivalence states its visibility scale for a microscopic pair and its `Θ`-reading. Equivalences whose
  right-hand side quantifies over zeros, or whose objects are defined from the zero set, are labelled as relabelings.
- Carriers or kernels indexed by the zeros are not built (the Deninger result).
- Bounded-parameter positivity is reported with its margin and the scale at which that margin equals the synthesis error.
  Without that scale it is not evidence for RH.
- Programme READMEs list the corpus's zero-constraining theorems (§4.1) as the baseline any new mechanism must beat or
  use.

---

## 7. What would change this assessment

- A theorem from a positivity, rigidity, gauge, Hodge or realization programme that constrains zero locations
  unconditionally, for example a positive-proportion statement or a zero-free region not obtainable from §4.1. That would
  refute §4.1–§4.2.
- A fixed-parameter positivity theorem whose proof fails for a ζ-like configuration with a near-line pair at bounded
  height while the dense background is kept. That would refute the domination half of §4.2.
- A proof that the horizon boundary layer of §4.3 is not universal (that it depends on zeros at leading order). That would
  close WP-C as a reformulation.
- A functional of the explicit-formula Gram data at `λ ≤ 1` that separates double zeros from coalesced pairs. That would
  refute the blind spot as stated in G14 and immediately raise the census.
