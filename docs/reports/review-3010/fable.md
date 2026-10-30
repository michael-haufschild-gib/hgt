# Fable review: the walls, what stands behind them, and where to go

Status: 30 October 2026, corpus `2ca741ffb3` plus working tree. **RH open.** A consolidated reading of the frontier map, the killed-routes ledger, the unification ledger, the route-obstacles report and the walls ledger, checked against the Lean corpus through the search tool. No builds, no axiom audits, no verification of other agents' work.

Labels: **[Lean]** a declaration or module docstring read in the corpus; **[map]** taken from the five ledgers; **(outside)** a statement from outside the corpus, not checked here and carrying no argument; **(inference)** this review's conclusion.

Companions: [frontier map](../rh-current-frontier-map.md) · [killed routes](../rh-killed-routes.md) · [unification](route-unification-ledger.md) · [obstacles](route-obstacles.md) · [walls](walls-ledger.md). Working log: `logs/fable-review-3010.md`.

---

## 0. Answers in brief

1. **Circumventing or breaking a wall.** None can be walked around: Σ, Π, Γ are three readings of one fact, that the zeros are *resonances* and every positive object the corpus owns sees only *spectra*. Three faces are thinner than the ledgers present them. (a) Σ1 in Denjoy–Carleman coordinates: the Steklov receiver sits at `L (log L)² log log L`, `L = log log N`; whether the margin of the complete Weil matrix dies at `L (log L)²` is a Fourier-tail heuristic that the corpus can decide with existing definitions, and the SSIC square-root law fixes the units in which the question must be posed: only a rate certifies depth. (b) Σ2 forbids only *monotone continuation in aperture*; schedule-wise proofs on non-nested families are untouched by it. (c) Γ at bounded resolution is solved and the pole is the selector; selection at growing resolution should be run through the pole conductor.
2. **Wildly different approaches.** Every formulation that is different in its objects lands on the same wall, because RH is about where the *poles of a continuation* sit. The only mechanism in mathematics that controls resonances without positivity is oscillatory cancellation in transfer operators, which yields *strips*; the corpus proves that `ζ` is not the Ruelle zeta of any nuclear expanding analytic Markov system of entropy `≤ 1` [Lean], so such a realization is excluded, and only suspension flows over the infinite prime alphabet remain, outside the finite-type machinery the corpus has formalized.
3. **Quasi-RH with other values.** Any strip `Re s > Θ` is equivalent to a power saving in a Möbius or Liouville sum and, on the Σ side, to a *rate* of failure of positivity: a floor `μ(A) ≥ −C e^{2σA}` is a strip of width `σ` [Lean]. The corpus has reduced the `5/6` and `3/4` strips to one-sided bounds on explicit Möbius dilation tails on power meshes. The external `7/8` is a density-plus-detector argument whose components are largely formalized; the open steps are Proposition 4.6's frequency absorption, Proposition 5.1 and conductor uniformity. In the detector model `5/6` is feasible and `3/4` is not with the present allowance [Lean].
4. **75 % on the line.** Unconditional census: `0.67250071` simple critical, `4/5` of ordinates critical, `3/4` of copies within `4/log T`. The `3/4` threshold is exactly `∫₁^{4/3}(4/3 − α)F(α)dα ≤ 1/9`, twice the Hardy–Littlewood value; the corpus proves no unsigned upper-bound sieve can supply it (`Υ ≤ 8/9` would be required) and that the input must be a *signed*, Hardy–Littlewood-shaped bound with loss at most two [Lean].
5. **Three open questions.** (Q-A) The endpoint receiver in SSIC units. (Q-B) The corpus's own same-point question: a prime-side bound for the Hecke defect at `L ≍ log T`, or an `N`-normalized bound on the horizontal collision charge with constant `< 1/4`. (Q-C) The signed coalescent surplus at `λ = 4/3` with loss factor `≤ 2`.
6. **The new field.** Most of what a new field would need already exists as programmes; §7 says which, and isolates the two missing items: a non-envelope amplifier and an oscillation mechanism with a realization that escapes the Ruelle no-go.

---

## 1. The picture

### 1.1 Resonances, not spectra

Every route in the corpus ends at the same identity (unification §2): the Weil form, the Hodge defect of the scaling surface, the Krein index of the Hecke kernel, the Hecke invariance of the collided polarization, the Báez-Duarte distance, the Hankel cones, the heat constant — each is RH at its endpoint, and each is computed from the primes by the **explicit formula**, which is the argument principle applied to a holomorphic weight [Lean: HEF `TheExplicitImageIsTheWeilForm`]. The zeros enter all of them as *poles of a meromorphic continuation*, that is as resonances. Positive objects (Haar measure, Laplacians, Dirichlet forms, Gram matrices, KMS states) have *spectra*, and a resonance is never an eigenvalue of a positive operator unless the operator was indexed by the zeros to begin with (wall Σ6, `XiZeroCopy`).

The corpus has sharpened this into a rigidity theorem: a holomorphic weight agreeing with `|F|²` on the critical line equals `F·F#` everywhere, so **no choice of test function makes an explicit formula compute a same-point sum** `Σ m_ρ |F(z_ρ)|²`; the gap is the line-reflection defect `½ Σ m_ρ |F(z_ρ) − F(z̄_ρ)|²` [Lean]. The three walls are the three places where this one gap is paid:

| Wall | What the explicit formula gives | What RH needs | The gap |
|---|---|---|---|
| Σ | an equivariant form `W` of unknown sign, a positive form `D` of unknown equivariance [Lean: APol] | one form with both | zero margin: `E(c) → 0`, `μ(A) → 0`, odd form never subcritical |
| Π | Chebyshev precision from integrality, PNT-strength from producers [Lean: ASRP, AHA, EAHT] | one-sided count at `√x` | every producer law is inherited by `Λ + ε n^{−η}` |
| Γ | selection at bounded resolution through the pole, Gamma and Ramanujan packets [Lean: SB, RAPT, CACT] | selection at growing resolution | pole-keeping flips need overlap `≍ p^{1/7}`; gauge-invariant data stop at `3/4` |

(inference) At the endpoint the three are one statement; over `𝔽_q` one object supplies all three (unification §4). Over `ℤ` the corpus has every piece of the analogue, including the λ-ring of Adams operations and Hecke correspondences on the scaling surface and the arithmetic Lefschetz–adjunction identity [Lean: ACS], except a correspondence whose self-intersection is bounded by an invariant independent of the zeros; and it proves that any Hecke-stable effectivity cone satisfying Riemann–Roch already forces the zero-defect floor [Lean], so adjunction reproduces the sign rather than producing it.

### 1.2 The numbers that define the frontier

| Quantity | Value | Evidence |
|---|---|---|
| Complete Weil matrix, fixed overlap `c` | positive definite for every `C²` profile on `[0,1]` without real Fourier zeros; bottom `E(c) = (2/M) Σ_k k^{−1} ∫_{kc}^∞ |φ̂(2πt)|² dt`, attained at the pole conductor | [Lean] |
| Plateau profiles (real Fourier zeros) | positive definite for `0 < c ≤ c*`, `c* > 1 + 10^{−16}` | [Lean] |
| Conductor floor (tilted spline) | `E_m(c) ≳ c^{−7}` for `m ≤ c`, constant above | [Lean] |
| Fixed conductor packets positive | along `(log N)^α`, `α < 1/40`; uniformly on `c ≤ (log N)^A`, `A < 1/48` | [Lean] |
| Gamma reserve survives | while `c⁸ = o(log N)` | [Lean] |
| RH receiver (tilted spline) | `c_N = 2 (log N)^α`, `α > 1/4`; general law `c_N⁴/log N → ∞`, `c_N = o(N)` | [Lean] |
| RH receiver (Steklov profile) | `c_N = L (log L)² log log L`, `L = log log N` | [Lean, K] |
| Krein index of the Weil kernel | `κ(K_ζ) = #{ρ : Re ρ > ½}`, on any two-prime lattice; finite index ⇒ Lindelöf | [Lean] |
| Index zero | ⇔ `ψ(x) − x ≤ C √x log² x` eventually | [Lean] |
| Graded Σ | floor `μ(A) ≥ −C e^{2σA}` ⇔ zero width `≤ σ`; Hecke defect `≤ (2cosh(2dL) − 2)·D` for depth bound `d` | [Lean] |
| Möbius gauge exponent | `≤ 1/2` a.e., `≥ 3/4` on a residual set; gauge-invariant bounds `≥ 3/4` at `0` | [Lean] |
| Producer cost | Adams jets `2^{qr}`; factorial ratios `(2 log 2 − ε) m n` | [Lean] |
| Hecke state on `Aff(ℚ)` | positive definite iff `s ≥ 1/2`; Bost–Connes temperature `β` forces Hecke exponent `β/2` | [Lean] |
| Theta Hankel | rank 7 strict, rank 8 PSD for all `0 < a < 1/2` | [Lean] |
| Census | `≥ 0.67250071 − ε` simple critical; `≥ 4/5 − ε` critical ordinates; `3/4` of copies within `4/log T`; either `N₀ ≥ 3N/4` or `≥ (1/6 − ε)N` simple off-line | [Lean, on the pinned `Zeta23` package] |
| Off-line depth moment | `Σ m_ρ (Re ρ − ½)⁺ ≤ 0.067 T` per dyadic window; Littlewood's lemma formalized | [Lean] |
| Pair correlation | `F(T^α, T) ∼ (T/2π) α log T` for `0 < α < 1`, all zeros with multiplicity, no RH; form `Σ x^{ρ_j+ρ̄_k−1} w` | [Lean] |
| `75 %` threshold | `∫₁^{4/3} (4/3 − α) F(α) dα ≤ 1/9`, twice the Hardy–Littlewood value `1/18`; Fejér majorant `8/27`; five-model calibration | [Lean] |
| Quasi-RH reductions | `Θ ≤ 5/6` ⇐ one-sided `O(j⁸)` on `mobiusDivisorDilationTail (j⁶)(j⁵)`; `Θ ≤ 3/4` ⇐ `O(j⁵)` on `(j⁴)(j³)`; head `≤ (3/5)√M` | [Lean] |
| Density layer | Guth–Maynard `30/13`; density hypothesis on `σ ≥ 5/6`; Vinogradov–Korobov | [Lean] |
| Heat constant | `Λ₊ := inf{t ≥ 0 : H_t real-rooted}`; `Λ₊ < 1/8`, i.e. `Λ < 1/2` standard (Ki–Kim–Lee). `Λ₊ ≥ 0` holds by definition; `Λ ≥ 0` (Rodgers–Tao) is not formalized | [Lean] |
| Baker | logarithms of distinct primes linearly independent over the algebraic numbers (`bakerLinearIndependence_holds`) | [Lean] |
| Lee–Yang | the Lee–Yang theorem for ferromagnetic graphs by Asano contraction; two-prime Lee–Yang Dirichlet polynomials | [Lean] |
| Dynamical zetas | nuclear Ruelle zetas of analytic expanding Markov maps are zero-free on `Re s > σ₀ − 1`; `ζ` is not one of entropy `≤ 1`; Pollicott continuation for Hölder suspensions of finite-type subshifts | [Lean] |

---

## 2. Question 1: a mechanism that circumvents or destroys a wall

### 2.1 Σ1: the receiver–curve question, in the corpus's units

The complete Weil matrix `W(φ, c, N)` has three quantities that are "one Fourier tail separated by the weight `log N`" [map]: the margin `E(c)`, the Gamma reserve, and the synthesis error. For the tilted spline `|φ̂(t)|² ≍ t^{−8}`, `E(c) ≍ c^{−7}` [Lean], the critical curve `E(c_N) log N ≍ 1` is `c_N ≍ (log N)^{1/7}` and the receiver is `(log N)^{1/4}` [map, inference].

(inference, heuristic) For a Gevrey-`s` profile the Fourier tail beyond `c` is `≈ exp(−c^{1/s})`, so the curve would be `(log log N)^s` against the receiver `(log log N)^α`, `α > s` [Lean]; for the Steklov profile (derivative bounds `q! (log q)^{2q}`) the tail is `≈ exp(−c/(log c)²)`, the curve `L (log L)²`, the receiver `L (log L)² log log L` [Lean, K]. The corpus has `completedShellEnergy` and `hasSum_completedShellEnergy` for arbitrary profiles and the explicit `dcProfile`, `steklovDCProfile`; `E(c)` for these profiles is not computed. That computation is the first step, and the heuristic may fail.

Three facts shape the question.

- **Units.** SSIC's square-root precision law [Lean: `depthResolution_le_sqrt`, `theDeficitBudgetLaw`]: a Weil floor at level `η` on scale `L` excludes only depths `δ > √(η/L³)`; the deficit of an off-line lattice grows like `e^{2δa}`, so depth is half the growth rate of the deficit, and a uniform deficit bound is not strength, only a rate is. A receiver on the critical curve, where margin and error are both `≍ 1/log N`, is a question about a *rate*, not about a constant. Q-A (§6) is phrased accordingly.
- **Obstacle.** The all-overlap positivity theorem needs the profile to have no real Fourier zeros because each of its three inputs uses `integral_sq_pos_of_noRealZero` [Lean]. Profiles with real Fourier zeros are not excluded from positivity: the plateau is positive definite for `c ≤ c* > 1 + 10^{−16}` [Lean: TM]. The open point is positivity at *growing* `c` for a Denjoy–Carleman profile, which has real Fourier zeros; whether the quasimode reduction (`eventually_noRealZero_completeWeilMatrix_posDef_of_quasimodes`) survives real zeros is the concrete obstacle.
- **Work already listed.** Extending fixed packets from `(log N)^{1/48}` to the reserve exponent `1/8` is an "A" item [map].

### 2.2 Σ2 is a direction law, not a wall

`extension_forces_positivity` is three lines: a nondecreasing minorant of the nonincreasing `λ(L)`, nonnegative once, is nonnegative everywhere [Lean]. It concerns **nested** families only. The complete Weil matrices along a schedule `(N, c_N)` are not nested; each is a finite statement, and the receiver theorems make the sequence RH-equivalent. The lesson of Σ2 is that the only admissible argument proves the sign on the RH-complete schedule directly, by identities whose errors are compared to the floor at that overlap. Every such identity (ratio-prime, shell repayment, Schur reduction, Gamma reserve) is in the corpus; what is missing is their assembly at growing `c` with growing conductors `m ≤ c`.

### 2.3 Σ3 and Σ6: the collided form is computed; its bound is not

The Allegretto–Piepenbrink mechanism [Lean: ACT] converts zero-margin positivity into existence of a positive supersolution; no positive *profile* works for the folded generator [Lean]. The collided form `D` is positive and transforms by `D(T_L f) = Σ m_ρ e^{2(Re ρ − ½)L}|f̂(ρ)|²` [Lean: APol]; its symmetric second difference is the Hecke defect, a depth moment [Lean: CDG]. `D` and the Hecke defect *are* computed from arithmetic data in the limit, by theta-prefix source currents [Lean: CDG `tendsto_sourceCurrentReading_heckeDefect`]; what is missing is a prime-side *upper bound* for the Hecke defect at `L ≍ log T` (CDG question 2). (inference) A ground-state transform by `D` rather than by a profile is the natural candidate for the positive solution ACT asks for; its remainder is exactly the Hecke defect, so this is CDG question 2 in ACT's language.

### 2.4 Π: amplifiers with a finite seed

The unification ledger asks for "an amplifier with a finite seed". The corpus's Landau mechanism [Lean: `ZetaMultipleLandauZeroFree`] has the shape: a bounded `a` with `a * 1 ≥ 0`, sparse at `1`, and partial sums `O(x^θ)` gives `ζ ≠ 0` on `Re s > θ`. Every nonnegative Dirichlet series built from `ζ` alone keeps its pole, and the pole is the ground state of the complete Weil spectrum while `ℝ^×·ζ` is the simple-pole class [Lean: RAPT, SB]. The producer theory (Adams jets `2^{qr}`, factorial ratios, Bézout, approximate vanishing is divisibility) stands at Chebyshev precision [Lean]; tensor amplification at fixed total support is killed [map]. The family amplifier over Dirichlet characters, with orthogonality as pole-killer and an individual detector rather than an envelope, is the Chen–Gupta–Li argument; its formalization frontier is in §4.2. An envelope alone admits singleton counts [Lean: `DensityEnvelopeNoGo`]; the detector is where the amplification must happen.

### 2.5 Γ: run selection through the pole

Selection at bounded overlap is a theorem: one bounded overlap rejects every pole-free `±1` gauge with bounded harmonic sums and every cofinite flip; pole-budget-one, degree-one completed positive systems are `ℝ^×·ζ` [Lean]. Pole-keeping flips need overlap `≍ p^{1/7}` [map]. Twins with poles are signed divisors and fail every Hilbertian identity [Lean: HEF]. The atomic pole index is sharp (`ζ` pole index `0`, Liouville pole index `1`, at `log N − γ − 2log2 + ε ≤ D < log N − γ − ε`) [Lean: HKT]. (inference) Selection at growing resolution should be organized around the pole conductor `m = 1` and its energy `E₁(c)`, not around prime flips; the open item is the map's "transfer selective pole sign to the complete form at growing overlap".

### 2.6 Across walls: the quantum

The HEF collision charge `O = Σ m_ρ(H_ρ − m_ρ)` is even, `O = 0` on critical configurations, `O ≥ 2` otherwise, `N − N₀ ≤ O` [Lean]. The RHTower horizontal-collision programme has the endpoint for `ζ`: `xiHorizontalCollisionCharge T`, `2·#(right zeros below T) ≤ O(T)`, the exact split into forced reflection self-intersection and accidental excess, the two-prime Cesàro carrier, and the Gauss–Hodge prime current that is summable iff the charge vanishes [Lean]. The corpus's Montgomery form is `Σ_{j,k} x^{ρ_j + ρ̄_k − 1} w(ρ_j + ρ̄_k − 1)`, the conjugate pairing with depth in the diagonal; `MontgomeryBlockSplit` isolates blocks [Lean]. The exact open estimate is CDG question 2 (prime-side bound on the Hecke defect at `L ≍ log T`), HEF topics 3–4 (a source-realizable unimodular clock whose mean square reads the charge with finite loss) and the census form `O(T) ≤ cN(T)`, `c < 1/4`. Landau–Gonek zero moments are Rosati pairings `Q(ρ)conj Q(ρ*)`, and their positivity is a Hodge index of the same type as Weil's, not an input [Lean: AIT].

---

## 3. Question 2: approaches different from the existing routes

Each entry names the source, what the corpus has, and the wall it meets.

**A. Oscillation instead of positivity.** The one family of mechanisms that controls resonances without positivity is oscillatory cancellation in transfer operators, which yields resonance-free *strips* for dynamical zeta functions (outside: Dolgopyat, Pollicott–Sharp, Naud). The corpus has the Pollicott continuation for Hölder suspensions over mixing finite-type subshifts, with a zero-free strip `Re s > 1 − ε` [Lean: `SymbolicRuellePollicott`], and proves that nuclear Ruelle zetas of analytic expanding Markov maps are zero-free on `Re s > σ₀ − 1`, so that **`ζ` is not such a Ruelle zeta of entropy `≤ 1`** [Lean: `not_riemannZeta_eq_ruelleZeta`]: a realization of this type would prove too much. (inference) What is left is a suspension flow over the *infinite* prime alphabet with roof `log p`, formally the Bost–Connes classical system, where both the finite-type hypotheses of the continuation and the expanding-map no-go fail. The arithmetic shadow of oscillation is Vinogradov–Korobov [Lean], a region, not a strip. A strip from this direction needs a realization that is neither a finite-type suspension nor an expanding map, which is wall Σ6 restated.

**B. Unipotent dynamics: closed horocycles.** The corpus has the Eisenstein constant term with its scattering vector on finite decks, `horoAverage(eisVec s) = y^s⟨v,w⟩ + y^{1−s}⟨v, scatVec s w⟩`, the vanishing of horocycle averages of cusp vectors, horocycle mass of theta powers, and a horocycle-cutoff rigidity [Lean]; the ThetaCusp Hawking–BM programme carries a Rankin–Selberg–Zagier Eisenstein route with an RH chain and a scalar-landing no-go [Lean]. Absent is the statement that an equidistribution *rate* `y^{3/4−ε}` of the closed horocycle is RH (outside: Zagier, Sarnak). (inference) It would be a clean reformulation in which Γ is free and Σ is the whole problem; `SelbergLedgerCeiling` shows the trace-formula side reaches only de la Vallée Poussin width [Lean].

**C. Lax–Phillips scattering.** Not in the corpus (outside). Its content, one negative square from the constant function, is the corpus's Krein–Langer formulation and "the pole is the only removable hyperbolic direction" [Lean: HKT]. Nothing new.

**D. The Gauss map and real quadratic forms.** The corpus uses the Mayer transfer operator at `s = ½` as a rigidity tool: Fourier-blind compact cores satisfy a twisted Mayer equation and vanish below support ratio `1 + 1/√2` [Lean]. No prime-geodesic or class-number statement is present. (inference) The scattering zeros `ρ/2` sit in the strip reached only by continuation; this is the same resonance problem in a chart where the prime side becomes class numbers.

**E. Crystalline measures and Lee–Yang.** The corpus has the full Lee–Yang theorem by Asano contraction, two-prime Lee–Yang Dirichlet polynomials whose zero set is a Kronecker line on a torus curve, the DCP pincer (diluted crystals become visible at logarithmic aperture; the archimedean part of `ζ`'s form dominates diluted visibility; crystal gaps are incompatible with the prime torus by Kronecker and Baker) and SRT's non-monotonicity of visibility (adding off-line zeros can hide a configuration) [Lean]. (inference) A classification of multiplicative zero sets that are quasicrystals modulo a smooth density would be a Γ-type result; its finite cases are already here.

**F. Statistical rigidity by contradiction.** Rodgers–Tao's `Λ ≥ 0` is not formalized; the corpus's version of this logic is the visibility theory of SRT and SSIC (refutation is finite, confirmation is not; depth is a rate) [Lean]. At bandwidth `≤ 1` a coalesced pair and a double critical zero share their statistics [Lean: ACS], so the logic needs a trans-threshold or depth-sensitive statistic (§5).

**G. Positive solutions of the Weil generator.** No Martin-boundary or random-walk realization is in the corpus. The Weil form is a Dirichlet form minus a prime form; the Markov sign fails inside the separated regime and the odd ledger is frustrated exactly by primes [Lean: SSHA, SAEI]. Same wall as §2.3.

(inference) The routes that differ in their objects do not differ in their obstruction. The one direction that changes the *type* of conclusion is A, and the corpus has fenced it with a no-go.

---

## 4. Question 3: Quasi-RH with values other than `1/8 < Re ρ < 7/8`

### 4.1 What a strip is, on both sides

Every zero-free strip `Re s > Θ` is equivalent to a power saving: escaped-Möbius, Hecke-defect and theta rate dictionaries [Lean: BVI], terminal ceiling and one-scale bound [Lean: RBG], the Landau multiple [Lean]. On the Σ side the strip is a *rate*: a floor `μ(A) ≥ −C e^{2σA}` on the restricted Weil ground energy gives zero width `≤ σ` [Lean: `zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`, `compensatedWidthFloor_iff_groundEnergy_ge_neg_exp`]; the Hecke defect is bounded by `(2cosh(2dL) − 2)·D` iff all depths are `≤ d` [Lean]; SSIC: depth is half the growth rate of the deficit. *Exact* positivity is critical and proves the line or nothing (Σ2); a strip needs a rate from either side, and none is proved. The sharp reductions:

- `Θ ≤ 5/6` ⇐ a one-sided `O(j⁸)` bound on the `(j−1)`-quotient sum `mobiusDivisorDilationTail (j⁶)(j⁵)`; `Θ ≤ 3/4` ⇐ `O(j⁵)` on `(j⁴)(j³)`; the dilation head is unconditionally `≤ (3/5)√M` [Lean: QuasiRH II, III];
- `5/6`, `3/4` strips ⇔ cyclotomic remainder `O(N^{5/3+ε})`, `O(N^{3/2+ε})` [Lean: BVI].

### 4.2 The external `7/8` claim: formalization frontier

The frontier map carries the Quasi-RH manuscript as unvalidated [E]. The local formalization covers: Lemma 6.2 contour shifts in all regimes, the detector residue at a certified zero, the principal pole residue and its high-ordinate bound, rectangle integrals of the nonprincipal detector integrand, the principal zero census `O(log² X)` by Jensen, the Section-12 primitive-conductor transport, the Lemma 4.5 cubic trace expansion with its `X^{−100}` zero-frequency certificate, and a closed fixed-modulus positive-window zero-density envelope whose constant may depend on the modulus [Lean]. Open [Lean docstrings]: Proposition 4.6 (replace the centered cubic trace by the Lemma 4.5 frequency expansion and absorb the zero-frequency remainder), Proposition 5.1 beyond `S₁`, conductor-uniform `7/3`, and the assembled zero alternative; no module states a strip. Three local facts frame the audit: a density envelope alone admits singleton counts [Lean]; the `7/8` is a sharp detector-budget minimum, with `5/6` feasible iff `ν ≤ 1/15 ∧ κ + 4ν ≤ 4/3` and `3/4` excluded with that allowance [Lean: `QuasiRHDetectorGramTradeoff`, `QuasiRHDetectorScaleBudget`]; the standard packet cannot carry the horizontal collision charge, and the Proposition 4.6 envelope has a source-range floor `288` against the quantum `2` [Lean]. (inference) The audit should target Proposition 4.6's absorption step and the zero alternative, not the contour shifts.

### 4.3 Other values

(inference) No mechanism in the corpus yields a strip at any `Θ < 1`. Within the detector model `5/6` is feasible under the stated parameter constraints and awaits actual Gram lower bounds; `3/4` needs a different allowance or source [Lean]. The reductions of §4.1 make `5/6` and `3/4` concrete one-sided Möbius statements inside the Π4 horizon; on the Σ side the same strips are floor rates on `μ(A)`.

---

## 5. Question 4: at least `75 %` of the zeros on the line

### 5.1 Status

- `≥ (0.67250071 − ε) N(T)` simple critical zeros: the `c = 2` rank–trace certificate of the pinned `Zeta23` package (its README: a complete, sorry-free formalization of Theorems A–E of the 2026 Anthropic paper "More than two thirds of the zeros of the Riemann zeta function lie on the critical line", standard axioms only; corpus docstrings call the certificate Alpöge–Furman's) plus `10^{−8}` from incommensurable Gabor pinching [Lean: IGP]. Dirichlet analogues exist [Lean].
- `≥ (4/5 − ε)` critical ordinates; `3/4` of copies within `4/log T`; off-line depth moment `≤ 0.067 T` per dyadic window via Littlewood's lemma [Lean].
- In every large dyadic window, either `N₀ ≥ 3N/4` or at least `(1/6 − ε)N` of the copies are simple off-line zeros [Lean]. **The `75 %` problem is a bound on simple off-line zeros alone.**

### 5.2 The two routes and their exact prices

**Route II, prime side.** At `λ = 4/3`: unconditional constant `43/36 = 5/4 − 1/18`, prime–pole cross term `O(T^{5/6} log² T)`, proportion `≥ 3/4` iff `κ ≤ 5/4` [Lean]. In form-factor terms `∫₁^{4/3}(4/3 − α)F(α)dα ≤ 1/9`, twice the Hardy–Littlewood value `1/18` [Lean]; the premise is `PrimeSurplusFourThirds`: `primeSurplus ≤ (1/18 + ε)(aL)²·Tℓ₁/2π` eventually [Lean]. The Fejér majorant from sub-threshold data gives `8/27` [Lean].

**Route I, zero side.** The joint `(c = 2, c = 3)` functional at `κ = 4/3` is exactly `(3/4)N`; it certifies `75 %` iff the zero-side spectral slack is `≥ (3/4 − H(λ))N`, which an abstract non-coalesced configuration violates (`179/243 < 3/4`) [Lean]. The displacement credit `E_proj ≥ 0` is exact, retains all cross-pair cancellation, and may vanish [Lean].

**Route III, same-point.** `N − N₀ ≤ O`, so `O(T) ≤ N(T)/4` gives `75 %` [Lean: HEF, HC].

### 5.3 Assessment

The prime route is calibrated exactly [Lean: `calibration_five_models_four_thirds`]. With `F(α) = β + γ(α − 1)` for `α ≥ 1`:

| Model | `(β, γ)` | surplus ratio at `4/3` | against budget `1/18` |
|---|---|---|---|
| Hardy–Littlewood / GUE | `(1, 0)` | `−1/144` | passes, slack `1/16` |
| diagonal only | `(1, 1)` | `0` | passes |
| naive Poisson, no repulsion | `(2, 1)` | `+1/16` | fails by `1/144` |
| spectral sieve, HL shape kept | `(Υ, 0)` | `(9Υ − 10)/144` | passes iff `Υ ≤ 2` |
| unsigned additive sieve | `(1 + Υ, 1)` | `Υ/16` | passes iff `Υ ≤ 8/9`: impossible for any upper-bound sieve |

So the input is a **signed** close-pair estimate that keeps the Hardy–Littlewood repulsion and loses at most a factor two; no upper-bound sieve and no size-only Hilbert inequality controls it [Lean: TTPC README]. The trans-threshold Poisson main term integrates to zero against the dyadic kernel only with the exact Hardy–Littlewood term, and its logarithmic deficit contributes `−(λ − 1)³/(3λ²) < 0` [Lean: Frullani cancellation]. The statement to prove is `CoalescentSurplusAtMost β` with `β ≤ 2` on the signed close-pair sum: a two-sided estimate at the Hardy–Littlewood scale over shifts `h ≤ bn` inside the strip `1/b < n ≤ X`.

The zero-side route needs a census-scale lower bound for `E_proj` or for the second depth moment; HEF's resolvent defect gives the latter without projection [Lean]. The same-point route needs `O(T) ≤ cN(T)`, `c < 1/4`, from a source-realizable carrier [Lean: HC, HEF].

---

## 6. Question 5: the three questions to focus on

**Q-A. The endpoint receiver, in SSIC units.**
*Statement.* For an admissible profile `φ` with Fourier tail `τ_φ`, let `c*_N` solve `τ_φ(c*_N) log N = 1`. Determine the rate `r(N)` such that eventual nonnegativity of the complete Weil energy at overlap `c*_N · r(N)` is RH-equivalent, and whether `r` can be bounded. For the Steklov profile the present receiver has `r = log log L` [Lean, K].
*Why.* It is the one face of Σ1 where the gap is an iterated logarithm; SSIC's law says only a rate can certify depth, so the question is well-posed exactly as a rate and cannot be answered by a constant-factor comparison. A negative answer closes the overlap lane as a lane.
*First steps.* Compute `completedShellEnergy` for `dcProfile` and `steklovDCProfile` [Lean, definitions exist]; test the quasimode reduction for a profile with real Fourier zeros; sharpen the second-order overlap law toward its endpoint.

**Q-B. The same-point question.** (CDG Q2, HEF topics 3–4, HC endpoint.)
*Statement.* A prime-side upper bound for the Hecke defect `D(T_L f) + D(T_{−L} f) − 2D(f)` at `L ≍ log T`, or equivalently a source-realizable carrier whose Cesàro excess reads the horizontal collision charge with finite loss, giving `O(T) ≤ cN(T)` with `c < 1/4`.
*Why.* It is the unique statement with two outputs of different strength: the `N`-normalized bound gives `75 %`; the absolute bound `O < 2` is RH with margin `2`, the only margin not subject to Σ2. The corpus has the carriers (two-prime Cesàro, Gauss–Hodge current, resolvent defect) and the no-gos (holomorphic clocks carry no quantum; standard packets cannot carry the charge).
*First steps.* `tendsto_sourceCurrentReading_heckeDefect`, `heckeDefect_sq_le_two_scale`, `xiHorizontalCollisionCharge_eq_reflection_add_accidental`, `ProjectedDisplacementPaysNegativePartCredit` [Lean].

**Q-C. The signed coalescent surplus at `λ = 4/3`.**
*Statement.* `CoalescentSurplusAtMost β` with `β ≤ 2`: a two-sided, Hardy–Littlewood-shaped bound for the signed close-pair sum `Σ_{m,h} Λ(m)Λ(m+h) m^{−1} K(Th/m)` over `0 ≤ h ≤ cm/T` in the strip, with the Frullani-cancelled main term and loss at most a factor two.
*Why.* It is the exact `75 %` input [Lean: `zeta_three_quarters_of_prime_surplus`], it is the two-point form of the Rosati sign beyond the square-root threshold [Lean: AIT], and the corpus has proved what cannot supply it (unsigned sieves, size-only Hilbert inequalities), which fixes the shape of what can.
*First steps.* `coalescent_sum_linearization_bound`, `hl_coalescent_deficit_integral`, `narrowStrip_beats_two_thirds_iff`, `sieved_closePrimePair_strip_bound` [Lean].

(inference) Q-A is Σ at its thinnest face, Q-B is the only margin-free attack, Q-C is Π at the point where the corpus has excluded the wrong tools.

---

## 7. Question 6: the field that would supply the missing tools

### 7.1 What already exists as programmes

The objects and principles such a field needs are existing programmes:

| Component | Programme [Lean READMEs] |
|---|---|
| criticality, ground states, positive supersolutions | ACT |
| visibility, aperture, depth as a rate, square-root precision law | SRT, SSIC, AOG |
| conjugate diagonal, Hecke defect, source currents | CDG |
| same-point sums, quantum, calibration rigidity | HEF |
| electrostatics of the zero divisor, virial laws | AES |
| crystals, dilution, hiding | DCP |
| trans-threshold pair correlation, coalescent surplus | TTPC |
| Krein index, towers, twins | HKT, AKLT |
| scaling surface, λ-ring, Hecke correspondences, adjunction | ACS |

The principles "identities first, sign last", "calibrate over `𝔽_q`", "fail on the battery", "a reformulation is not a contribution" are HEF §6–11; "computed is not bounded", "positive is not equivariant" are CDG's traps; "only a rate is strength" is SSIC.

### 7.2 What is absent

Two items are not owned by any programme.

1. **A non-envelope amplifier.** A mechanism that turns a crude bound uniform in a family parameter into the sharp one at an *individual* zero, with its own pole-killing. Envelopes cannot do it [Lean: `DensityEnvelopeNoGo`]; CGL is the one attempt and its frontier is §4.2. The field-level question: which arithmetic structure plays the role that big monodromy plays over `𝔽_q`, where tensor powers lose their invariants.
2. **Oscillation for resonance gaps, with a realization that escapes the Ruelle no-go.** The corpus has Pollicott continuation for finite-type suspensions and proves `ζ` is not an expanding-map Ruelle zeta [Lean]. The missing object is a hyperbolic realization over the infinite prime alphabet on which oscillatory (non-positive) cancellation can be run. Its payoff would be a strip, which no critical method gives.

### 7.3 Point of view

RH is a statement about resonances; every positive object sees spectra; the only bridge is holomorphic and rigid. A field built around this has as objects reflection configurations with the two forms `W`, `S` and their defect, Hecke–Krein spaces, quantized charges, depth moments, windows and schedules with a height-renormalized genus, and trans-horizon correlations; as principles: resonances are not spectra; criticality; margin from integrality; selection by symmetry (the pole); same-point information only through a non-holomorphic operation; calibration; graded versus critical kept apart. The corpus already works this way across its programmes; the field is not to be founded but joined, and its two open items (§7.2) are the only places where a genuinely new tool is required.

---

## Appendix: corpus entry points consulted

Walls and frontier: `ExtensionProgrammeNoGo`, `TheExponentIsNotGaugeInvariant`, `TheDecidingInputTheorem`, `TheBottomOfTheCompleteWeilSpectrumIsTheCompletedShellEnergy`, `LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis`, `EveryProfileWithoutRealFourierZerosIsPositiveAtEveryOverlap`, `TransMetzlerPositivity`, `ConductorScaleControlsTheCompletedEnergy`, `FixedConductorPacketsStayPositiveAtGrowingOverlap`, `OddSupersolutionCriterion`, `SuperGevreyCriticalGrowth`, `TheFixedProfileReachesAnIteratedLogEndpoint`, `TheDenjoyCarlemanProfiles`, `TheReceiversEndAtTheQuasiAnalyticBoundary`, `TheSquareRootPrecisionLaw`, `TheScalingSurface`, `TheLambdaRingOfTheScalingSurface`, `LambdaRingEffectivityAndHeckeLefschetzRigidity`, `HeckeIncidenceCartesianLaw`, `HeckeInvarianceOfTheCollidedPolarizationIsRH`, `TheFiniteIndexStratumOfZetaIsLindelofDeep`, `TheGlobalLawIsTheOneSidedSquareRootCount`, `TheSimplePoleClassIsZeta`, `TheBostConnesTemperatureIsTheHeckeExponent`, `CompensatedWidthFloorAndGroundEnergyRate`, `TheWallsMeasureOneZeroWidth`, `FrustrationIsPaidAlongCanonicalPaths`, `CCMNonnegativeGroundStateRH`, `SelbergLedgerCeiling`, `BacklundLindelofConverse`, `DeBruijnNewmanConstant`, `DeBruijnNewmanStrictBound`.

Same-point and census: `HilbertianExplicitFormulas/README`, `ConjugateDiagonalGeometry/README`, `ArithmeticElectrostatics/README`, `TheResolventHilbertianExplicitFormula`, `TheExplicitImageIsTheWeilForm`, `ZetaDepthDistribution`, `TwoScaleDepthRigidity`, `XiHorizontalCollisionChargeEndpoint`, `XiReflectionSelfIntersectionCharge`, `MontgomeryFormLogScaleMeanSquare`, `MontgomerySpacedZeroDetection`, `MontgomeryBlockSplit`, `MontgomeryPairCorrelationLeadingOrder`, `ZeroMomentsAreRosatiPairings`, `KernelCountsAreBlindToComplexQuartets`, `Zeta23*` (and the package README), `ZetaLineLogMeanLittlewoodBudget`, `IncommensurableGaborPinching/CriticalLineZeroProportion`, `TransThresholdPairCorrelation/README`, `FormFactorThresholdAndShiftInequality`, `NarrowStripClosePairEnergyAndExchangeRate`, `CoalescentSieveAnatomyAndModelCalibration`, `BreakingTheCoalescenceBlindSpotAndThreeQuarters`, `ZetaThreeQuartersOfPrimeSurplus`, `PrimePairAverageSharp`, `WhichArithmeticDataForceTheSign`.

Quasi-RH: `QuasiRH*` (17), `ChenGuptaLi*` (280; frontier modules `PositiveWindowZeroDensity`, `ZeroDensityExponents`, `Proposition46`, `Proposition51`, `NonprincipalAnalytic`, `PrincipalZeroCount`, `PrincipalResidue`, `Lemma45*`, `Lemma62*`), `DirichletLZeroDensityDetectorBridge`, `ZetaMultipleLandauZeroFree`, `TheTerminalCeilingAndTheOneScaleBoundAreZeroFreeStrips`.

Different sources: `RuelleZetaNuclearZeroFree`, `SymbolicRuellePollicott`, `SymbolicRuellePollicottBounds`, `ZetaZerosLeeYangQuasicrystal`, `LeeYangAsanoContraction`, `DilutionCrystallizationPincer/README`, `CrystallizationHidesOffLineZeros`, `BlindCoreMayerTransferHalf`, `InversionSymmetricFourierBlind*`, `DeckIncompleteEisensteinMellin`, `DeckCuspidalOrthogonalEisenstein`, `ThetaPowerHorocycleMass`, `MaassFiniteDeckHorocycleCutoffRigidity`, `ThetaCuspHawkingBMEisenstein*`, `Deninger/DeningerCompleteCarrierSpectrumBounded`, `Deninger/DeningerResolventCoreIsRiemannHypothesis`, `BakerProof/BakerIteration`.
