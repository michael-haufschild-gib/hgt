# Source contraction: two-Volterra domination, uniformly in rank

- **ID:** `source-contraction-two-volterra-domination`
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE PROGRAMME / PRODUCER SEARCH
- **RH status:** the target is RH-equivalent by the Lean receiver; every cycle below attacks a
  producer, never restates the receiver.
- **Receiver [CORPUS]:** `riemannHypothesis_iff_posSemidef_thetaTailFirstMomentBezoutian`
  (`RHTower/ThetaTailFirstMomentDoubleLaplace.lean`) with
  `thetaTailKreinDifferenceEntry_eq_thetaTailFirstMomentBezoutian` and the literal channels
  `thetaTailKreinPlusTransform c w s = ∫ (x+s+c)·Φ(x+s)·e^{wx} dx`,
  `thetaTailKreinMinusTransform c w s = ∫ (x+s−c)·Φ(x+s)·e^{wx} dx`
  (`RHTower/ThetaTailFirstMomentKreinTransform.lean`), Φ = `thetaCuspFullSource`.

## Exact problem (frozen)

Let Φ be the literal theta density. For a finite packet `G(x) = Σ_j c_j e^{w_j x}` with
`Re w_j > 1/2`, define the value and moment channels

```
(V G)(s) = ∫_ℝ Φ(y)   G(y − s) dy ,      (W G)(s) = ∫_ℝ y Φ(y) G(y − s) dy ,
Q(G) := 2 Re ⟨ W G , V G ⟩_{L²(0,∞)} .
```

Then `Σ c̄_j c_k B(w_j, w̄_k) = Q(G)` (polarization of the Krein difference; the gauge `c > 0` is
immaterial), and **RH ⟺ Q(G) ≥ 0 for every packet ⟺ the map `(W+cV)G ↦ (W−cV)G` extends to a
contraction**. The task of this card: produce `Q ≥ 0` from the source structure of Φ, uniformly in
rank, without divisor input.

Elementary exact structure (derived, to be Lean-recorded when used):

1. **Full-line vanishing.** `Re ⟨WG, VG⟩_{L²(ℝ)} = 0` for every packet: Φ is even, `yΦ(y)` is odd,
   so the multipliers `Φ̂` (real even) and `i Φ̂′` (imaginary odd) give a purely imaginary
   full-line pairing. All positivity lives in the half-line truncation: `Q` is a boundary/Hankel
   object, and `Q(G) = Q(G∘(−·))` by parity.
2. **Impedance form.** Formally `Q ≥ 0 ⟺ Z := W∘V^{−1}` is positive-real on the half-line; the
   full-line symbol of `Z` is `i(log Φ̂)′ = i Ξ′/Ξ`, Herglotz ⟺ RH. Receiver again — the wall is
   producing half-line dissipativity from the kernel side.
3. **Orbit/Dirichlet split [CORPUS-backed].** `invSqrt_mul_logTranslate_thetaCuspLogSeed`:
   `Φ = Σ_{n≥1} n^{−1/2} g(· + log n)` with one fixed profile `g` (the archimedean seed). Hence
   with the causal positive shift operators `Z := Σ n^{−1/2} S_{log n}`, `Z′ := Σ n^{−1/2} log n·S_{log n}`:
   `V = Z V_g`, `W = Z W_g − Z′ V_g`, and
   `Q(G) = 2 Re ⟨ Z W_g G, Z V_g G ⟩ − 2 Re ⟨ Z′ V_g G, Z V_g G ⟩` — the arithmetic sits in two
   causal positive-coefficient Dirichlet shift operators, the transcendental part in the one-atom
   channels `(V_g, W_g)`. Commutation law: conjugating the impedance by `S_a` subtracts `a`
   (`W_{g(·+a)} = S_a W_g − a S_a V_g`).
4. **Evenness is the global miracle.** Each finite orbit truncation `Σ_{n≤N}` breaks the evenness
   of Φ; the completed source has a second, anti-causal orbit representation
   `Φ = Σ n^{−1/2} g(−· + log n)`. Any producer must consume this two-sided structure: cf. C1/C3.

## Frontier audit

- **[CORPUS]** Receiver and channels as above; Guinand–Weil explicit formula on the resolvent test
  algebra (`XiGuinandWeilExplicitFormula`); single-atom Riccati contraction layer
  (`ThetaCuspSingleAtomReflectedRiccatiContraction`); no reflection-positivity/transfer-operator
  machinery; terminal classifications: positive/scalar/determinant/completion producers, TP order
  ≥ 5 mechanisms (see `2-fully-proven/computations/2026-08-28-c5-bezoutian-tp-li-precert/`),
  prime-tail truncation escape (frontier map).
- **[LITERATURE]** Archimedean-place Weil positivity: Connes–Consani, Selecta Math 2021
  (arXiv:2006.13771), via Sonin space + prolate operators. Semilocal control: Connes–Consani–
  Moscovici, Ann. Funct. Anal. 2024 (arXiv:2310.18423 line). Finite-truncation critical-line
  results: Connes–van Suijlekom 2025. de Bruijn `t ≥ 1/2` real-rootedness; Rodgers–Tao `Λ ≥ 0`.
  Global positivity open; no reflection-positivity producer literature located (searched 2026-08).
- **Residue:** the finite-to-uniform assembly: local/semilocal positivity known, source-side global
  producer absent everywhere.

## Conjecture ledger

- **C1 [CONJECTURE → to kill]** (naive structural sufficiency): for every even, positive,
  log-concave kernel φ with double-exponential decay, `Q_φ(G) ≥ 0` for all Euler-half-plane
  packets. Expected `FALSE` (positivity cannot be a smoothness/convexity-class property; complex
  zeros of φ̂ are compatible with these hypotheses). Kill = explicit φ and packet with `Q_φ < 0`.
  Lesson sought: the exact structural gap between such φ and Φ.
- **C2 [CONJECTURE]** (one-atom domination, exact frame): for the archimedean seed `g` alone,
  `Q_g(G) := 2Re⟨W_g G, V_g G⟩_{L²(0,∞)} ≥ 0` for all packets; equivalently the one-atom
  contraction exists. Mechanism: one-atom impedance = digamma combination + center pole, Herglotz.
  Risk: `REDISCOVERED` relative to CC 2021 archimedean positivity — different operator frame, must
  audit; even so it is the base layer of C3 and Lean-valuable.
- **C3 [CONJECTURE, primary]** (two-sided orbit positivity): the half-line form `Q` of the
  completed source is positive because the causal orbit representation and its reflected
  anti-causal representation of the *same* Φ pair positively: there exists a source-built
  positive structure (transfer/Markov-type kernel on the orbit) whose reflection pairing across
  the modular center *is* `Q`. Producer content = a positivity-improving factorization of the
  Dirichlet-shift channel against the Gamma channel, not a receiver restatement. To be frozen
  exactly after C1/C2 sharpen the constraints.
- **C4 [FALSIFIED — recorded at creation]** (atom induction): positivity of finite orbit
  truncations increasing in N. False: the two-atom source `g + 2^{−1/2}g(·+log 2)` has transform
  `ξ_g(w)·(1 + 2^{−1/2−w-structure})` with a vertical line of off-center zeros
  (`|2^{−1/2−w}| = 1` forces `Re w = −1/2` off the center), so the truncated `Q` is indefinite.
  Matches the corpus prime-tail escape no-go. Lesson: the producer must never pass through
  source-side truncation of the orbit; evenness/FE is not truncation-stable.

## Loop log

- 2026-08-28: card opened; Gate-1 audits complete; C1 kill-test and C2 verification queued.

### Cycle 1 (2026-08-28) — three falsifications, one reframing

- **C1 [FALSIFIED, witness]**: φ₁(x) = e^{−x²/2}(1+0.2cos x) is even, positive, strictly
  log-concave ((log φ₁)″ ≤ −0.75 verified), transform zero at w₀ ≈ π + 2.7989i, and the rank-3
  packet at nodes ≈ (2.824+2.728i, 2.754+3.053i, 2.376+3.711i) gives relative min eigenvalue
  ≈ −0.747. Positivity is not a shape-class property (consistent with the TP₅ break).
- **C2′ [FALSIFIED]**: the FE-symmetrized single atom F_even = (F_g(w)+F_g(−w))/2, with
  F_g(w) = π^{−1/4}π^{−w/2}Γ(w/2+5/4)(w−1/2) (so F_Φ = ζ(w+1/2)F_g exactly), has ONE off-axis
  zero pair (argument-principle count 1.0 per quadrant box Re∈(0.05,8), |Im|∈(0.2,50)) and
  packets with rel min eig ≈ −5e10. Insight: the archimedean place alone, even-completed, fails
  positivity near the center — the low-height Riemann–Siegel phase deficit; the Dirichlet factor
  repairs it. The atom's zero at w = 1/2 is the ζ-pole shadow.
- **E3/E3b [FALSIFIED family]**: causal truncations ζ_N(w+1/2)F_g AND even-symmetrized
  truncations (ζ_N(w+1/2)F_g(w)+ζ_N(1/2−w)F_g(−w))/2 are indefinite for all tested N ≤ 10, with
  large negative witnesses. No source-side truncation ladder exists in either orientation;
  triple-confirms the prime-tail-escape no-go.
- **Reframing [delta]**: full-line pairing Re⟨WG,VG⟩_{L²(ℝ)} ≡ 0 and the ± channels have equal
  symbol modulus pointwise (|iΦ̂′ ± cΦ̂|² difference vanishes; Φ̂ real). Hence Q is a pure
  half-line cross-Hankel form with analytic rapidly-decaying symbols. Corpus fusion: the
  Gauss–Hodge–Weil layer already holds the Krein frame (`xiWeilPolarization_parityFlip_re_nonneg`
  unconditional J-majorant; `riemannHypothesis_iff_polarization_parityFlip_invariant`;
  `riemannHypothesis_iff_xiWeilSquareRealization`; obstruction = `gaussHodgeMassCurrent`).
- **C5′ [CONJECTURE, next]** (essential contraction / trace-class Weil form): on the correct
  carrier the form Q is dominated in absolute value by a source-built trace-class form —
  equivalently K₋∘K₊^{−1} is a contraction modulo trace class, unconditionally. RH-content then
  = sign of one explicit trace-class operator (tr|𝒬| = tr 𝒬). Gate-3 checks pending: carrier
  (LAND gate!), rediscovery vs Connes/CC compactness statements, corpus priors (CCM warning: the
  corrected prime-pole energy is weak-S₁ but NOT trace class — the cross form must be audited
  honestly).
- **C5(κ) ladder [CONJECTURE, design]** (Hodge-index / finite-negative-index): a source-proved
  bound "every finite Bezoutian section has ≤ κ negative eigenvalues" ⟺ at most κ off-line zero
  pairs — weaker than RH, beyond all literature for any finite κ; index tools (Pontryagin,
  winding = the corpus's APF source winding −1) apply where positivity tools fail.

### Cycle 2 (2026-08-28) — frame collapse: Bezoutian = Pick congruence; wall = strip poles

- **C5′ re-typed then subsumed.** As first stated (trace-class domination on the packet class)
  C5′ is ill-posed: Euler-half-plane exponentials are not vectors of any translation-invariant
  L² carrier (the LAND gate, exactly as the frontier map predicts). Re-typing on the K₊-metric
  exposed the collapse below, which supersedes it.
- **Frame-diagonal collapse [delta, exact].** By `thetaTailKreinPlusTransform_eq`,
  `K±G = Σ_j c_j·(F′±cF)(w_j)·e^{−w_j s}` with `F = 2ξc`: both channels are the SAME Laplace
  packet reweighted. Hence with `λ_c := (F′−cF)/(F′+cF)` and `D = diag((F′+cF)(w_j))`:
  `2c·[B(w_j,w̄_k)] = D* [ (1−λ_c(w_j)conj(λ_c(w_k)))/(w_j+w̄_k) ] D` — the theta-tail Bezoutian
  is an exact congruence of the half-plane **Pick matrix** of `λ_c` (numerator identity
  `(F′+cF)(w)(F̄′+cF̄)(v) − (F′−cF)(w)(F̄′−cF̄)(v) = 2c[F′(w)F̄(v)+F(w)F̄′(v)]`).
  Consequences: rank-uniform domination ⟺ `λ_c` Schur on `Re>0` ⟺ `Re(ξc′/ξc) ≥ 0` on `Re>0`
  ⟺ RH. Unconditional boundary control: `|λ_c| ≤ 1` on `Re w ≥ 1/2` (zero-free line σ=1,
  PNT-strength, corpus-owned) and `|λ_c| ≡ 1` on `Re w = 0` (FE + reality: ξc real, ξc′
  imaginary on the line — the system is lossless on the critical boundary).
- **[REDISCOVERED] flags:** the criterion content = Lagarias positivity (Re ξ′/ξ > 0 right of
  the line ⟺ RH, Lagarias 1999) and, through the tilt family `(e^{cw}ξc)′` strip-zero-free ∀c>0,
  Speiser/Levinson–Montgomery derivative-zero calculus. The congruence itself and the theta-tail
  channel realization are corpus-new candidates [BRIDGE]; SV2's "finite negative Pick
  certificates" is the same frame reached from the Euler side — cross-route unification.
- **Wall relocation [delta].** RH ⟺ no poles of `λ_c` in the open strip `0 < Re w < 1/2`
  (zeros of `ξc′ + cξc`), while both strip boundaries are unconditionally controlled and the
  boundary reflection is lossless. Every soft/structural producer must fail because it cannot
  see poles: unified explanation of C1, truncation kills, TP cap. Producer must be an arithmetic
  strip-pole-exclusion = trapped-mode exclusion in a lossless layer → positive-commutator /
  limiting-absorption (Mourre) technology is the untried mechanism class [next cycle].
- **Phase/causality lead:** boundary phase monotonicity of `λ_c` on the critical line reduces to
  the pointwise **Laguerre inequality** `Ξ′(τ)² − Ξ(τ)Ξ″(τ) ≥ 0` — audit corpus/literature
  status next; if owned unconditionally, the lossless boundary data is causal for every c.

### Cycle 3 (2026-08-28) — corpus-audit correction; tilt-collapse layer Lean-proved; wall stable

- Corpus audit (triggered by the standing instruction that the corpus outruns external SOTA)
  found the Carathéodory-kernel receiver already fully built (`XiEulerSafeCauchyLoss`,
  `XiEulerSafeObservability`, `ThetaCuspTiltFluxObservabilityWeld`). Cycle-2's criterion content
  re-labeled `[LOCAL-RESEARCH]`; the residual new layer was proved in Lean unconditionally in
  `ThetaTailKreinXiCentTiltCollapse` (channel collapse, all-plane division-free tilt algebra,
  lossless critical boundary, conj-equivariance; axioms standard). See
  `theta-krein-pick-congruence.md` for exact statements.
- New exact facts extracted: poles of `λ_c` cannot sit on the critical line unless `ξc` has a
  double zero there (both tilts vanish simultaneously ⟺ `ξc = ξc′ = 0`); `c`-trajectories of
  tilted-derivative zeros interpolate `ξc′`-zeros (`c→0`) to `ξc`-zeros (`c→∞`) and are barred
  from both strip walls (left: losslessness+simple zeros; right: unconditional C(i)).
- Cycle-4 unpacking of the Mourre/flow idea collapsed into the Levinson–Montgomery counting
  machinery (argument principle on the tilt family = LM with a `c`-gauge): no producer without a
  new Lyapunov invariant; the one new candidate input surfaced — unconditional Laguerre `L ≥ 0`
  — is known to be strictly weaker than RH, so it cannot break the wall alone. Representation
  verdict per Gate 6: the packet/kernel/half-plane representation is exhausted for producer
  purposes; next cycle must change carrier — the corpus's own frontier verdict points at the
  singular-completion merger chain (JAS/RFHM `C(PrimeTorus)`-sewing, L's coherent-Frobenius
  closure) with the new lossless-boundary layer as the reflection-odd datum.

### Cycle 4 opened (2026-08-28) — carrier change: sewing extension of the lossless wall relation

- **Fusion finding.** The Lean-proved lossless identity `tilt₋ = −conj(tilt₊)` on `Re w = 0` says:
  on the wall, the two literal Krein channels are related by the anti-unitary `J(f) = −conj f`,
  GLOBALLY and divisor-free — exactly the shape of the corpus's superselection sewing objects,
  where per-divisor `primePoisson_reflection_nonzeroClosedSourceLinearSewing_iff` proves a
  nonzero closed reflected sewing exists exactly at `σ = 1/2`, and
  `everyXiDivisorSyndromeIsInternalOnly_iff_riemannHypothesis` closes the chain to RH.
- **C6 [CONJECTURE, next primary].** The global wall relation `K₋|_{Re w=0} = (−conj)∘K₊|_{Re w=0}`
  extends to a closed, densely defined, contractive, source-linear correspondence on the
  two-Volterra carrier, constructed pre-divisor. Downstream is fully Lean-closed: such an
  extension forces every divisor's reflected sectors to sew ⟹ internal-only ∀ ⟹ RH. Producer
  content = the construction; the natural mechanism is boundary-to-interior transport by the
  source Poisson/heat semigroup — staging ground: the corpus's Euler-safe Poisson boundary
  programme (`mem: euler-safe-poisson-boundary-programme`, two named mathlib gaps + two
  integrability traps). Gate-3 caution recorded: existence-of-extension in full generality is
  the receiver; only an explicit semigroup construction with source-provable contractivity
  counts as progress.
- Do-not-revisit list extended: Mourre-as-such, flow/counting (collapse to Levinson–Montgomery),
  unconditional-Laguerre-as-producer (weaker than RH).

### Cycle 5 (2026-08-28) — the C6 transport probe resolves into the Jensen web; producer verdict TERMINAL

- **Exact resolution of the probe.** From the Lean A2-identity,
  `1 − |λ_c(w)|² = 4c·Re(ξc′(w)·conj ξc(w))/|tilt₊(w)|²` and `Re(ξc′ξ̄c) = ½·∂_σ|ξc|²` with
  `|ξc(σ+iτ)|² = |Ξ(τ−iσ)|²`. Hence: contractive transport onto EVERY slice ⟺ horizontal
  monotonicity of `|ξc|` ⟺ Jensen's disc criterion ⟺ Sondow–Dumitrescu — `[REDISCOVERED]`
  (SD 2010, arXiv:1005.1104) and `[LOCAL-RESEARCH]` (corpus already owns SD in Lean:
  `strictMonoOn_norm_XiC_horizontal_of_halfPlaneBound`, and the generic
  `monotoneOn_normSq_horizontal_of_re_nonneg`). **C6's semigroup-transport is terminal as a
  producer**: transport reparametrizes the receiver; it cannot manufacture strip-pole-freeness.
- **Positive salvage [delta, verified numerically to ε⁴]:** the wall-normal contraction jets are
  the classical Laguerre hierarchy:
  `Re(ξc′ξ̄c)(ε+iτ) = ε·L₁(τ) + ε³·L₂(τ)/6 + O(ε⁵)`, `L₁ = Ξ′²−ΞΞ″`, `L₂ = ΞΞ⁗−4Ξ′Ξ‴+3Ξ″²`
  (σ²- and σ⁴-coefficients of `|ξc(σ+iτ)|²` are `L₁` and `L₂/12`). Bridge target for Lean: weld
  the tilt-channel module to the corpus `XiLaguerrePolya`/`LaguerreInequality` layer via these
  finite-jet identities (unconditional; planar-partials machinery exists).
- **Numerics** (`computations/2026-08-28-two-volterra-domination-loop/`): L₁, L₂ violation-free
  on τ ∈ [0.2, 120] at dps 60 (normalized minima 0.044 and 0.082; dps-30 L₂ "violations" were
  stencil artifacts); slice contraction held everywhere sampled; **no Lehmer dip** in
  pointwise-normalized L₁ at τ ≈ 7005.1 (0.365 vs 0.378 baseline).
- **Representation lesson (Gate 6).** The RH-failure mode (close/complex pairs) is invisible to
  pointwise wall jets at every order tested — wall-jet producers are structurally insensitive to
  the actual danger; this closes the transport/jet family of producer candidates entirely.
  Remaining untried carriers stand as at cycle 4: the singular-completion sewing build arc
  (Poisson-boundary mathlib gaps) and the partial-exclusion budget lane (zero-density/HCF).

### Correction to Cycle 5 (2026-08-28, after cross-agent review)

The cycle-5 "representation lesson" overclaimed. Corrected statement:

- Lehmer pairs are on-line and RH-compatible; they are the *near-degeneracy margin* configuration
  (de Bruijn–Newman/backward-flow relevance), not an RH failure mode. Actual failure = an
  off-critical (nonreal-Ξ) zero quartet.
- "Invisible at every order" is false for the complete hierarchy: the full pointwise Laguerre
  family `L_n(t) ≥ 0 ∀n,t` characterizes the Laguerre–Pólya class (Csordas–Vishnyakova), hence
  sees nonreal zeros — it is an RH-strength receiver, not blind. The corpus formalizes all-order
  rigidity (`entire_eq_of_iteratedDeriv_eq`, `seamJet_zero_set_eq`,
  `completedFluxTaylorCoeff_line_pair_all_eq_iff`,
  `exists_completedFluxTaylorCoeff_line_pair_ne_of_re_ne_half`) against narrow finite-prefix
  blindness (`finiteCorrectionDepth_divisorBlind`, `ccm_criticalClock_divisor_blindness`).
- What the numerics support: low-order normalized wall observables (L₁, L₂) show no useful local
  signature at the tested Lehmer window, and no fixed finite jet prefix determines the divisor.
  The strategic verdict stands in corrected form: wall-jet approaches offer no producer because
  finite prefixes are provably blind and the complete hierarchy is receiver-equivalent — the
  finite-to-uniform wall again — not because jets "cannot see" nonreal zeros.

### Formalization batch (2026-08-28) — no-gos and survivors landed in Lean

Three new modules, all umbrella-wired, built, axioms standard (propext/Classical.choice/
Quot.sound) on every theorem:

1. `RHTower/ThetaTailKreinTiltDiagonalLaw.lean` — the rank-one survivor layer:
   `normSq_xiCentTiltPlus_sub_normSq_xiCentTiltMinus` (the pointwise A2 law
   `‖tilt₊‖² − ‖tilt₋‖² = 4c·Re(ξc′·conj ξc)`), line parity (`conj_xiCent_I_mul_ofReal`,
   `conj_deriv_xiCent_I_mul_ofReal`), and the wall vanishing
   `re_deriv_xiCent_mul_conj_xiCent_I_mul` (∂_σ|ξc|² = 0 on the line) with the squared-modulus
   losslessness corollary.
2. `RHTower/XiCentEulerAtomFactorization.lean` — the orbit-split survivor and the truncation
   no-go, now exact: `xiCent_eq_riemannZeta_mul_eulerAtomFactor` (Euler-orbit factorization on
   `Re w > −1/2`), `xiCentEulerAtomFactor_half` (the ζ-pole shadow zero of the single atom), and
   `xiCentTwoAtomTruncation_witness_zero` — the two-atom causal truncation has the explicit
   off-axis zero at `w = −1/2 + (π/log 2)·i` where the atom factor is nonzero, by exact
   arithmetic (`2^{−iπ/log 2} = −1`); no numerics.
3. `RHTower/ThetaTailKernelGeometricDeficitSplit.lean` — the CP/deficit foundation (see the new
   card `theta-kernel-cp-deficit-domination`): orbit-shift parametrization, exact AM–GM split
   `k = 2M + D`, manifest PSD of `M` on finite nonnegative node systems, and the deficit's
   zero-diagonal/nonnegativity/symmetry.

Not formalized, with reasons recorded: the C1 shape-class kill (needs six transcendental
enclosures at complex rational points — queued, corpus-standard but laborious); the
even-symmetrized truncation kills (no closed-form witness; numeric-only, flagged as such);
the TP₅ break (sign certification of 5×5 theta determinants at 1e−12 margins — not worth the
interval-arithmetic cost now); the single-atom integral identity
`thetaBilateralLaplace-of-atom = xiCentEulerAtomFactor` (Mellin–Gamma computation, queued —
would upgrade the factorization to the literal coefficient-faithful atom transform).

### Cycle 7 (2026-08-28) — index/parity exploration: the near-miss programme opened

Full exploration of the Class-C middle recorded on the new card
`index-parity-near-miss-rigidity.md`. Deltas: the exact index dictionary κ_T = N_off(T) with the
proportion/almost-all/finite/zero ladder and its owners; **C8 [CONJECTURE]: κ ∈ {0, ∞} — RH
cannot fail finitely often** — four equivalent forms (generalized-Nevanlinna membership,
polynomial×LP factorization, theta-density ODE-relation onto the LP cone), strictly weaker than
RH, absent from refereed literature; the explicit κ = 1 analytic counterfeit
`Ξ·(τ²−ρ²)(τ²−ρ̄²)/((τ²−γ₁²)(τ²−γ₂²))` proving any C8 proof must be arithmetic; the
consequence-mining resource (finite κ ⟹ Lindelöf-grade upgrades + the anomaly is an exact
κ-frequency Bohr polynomial). Two live attack surfaces: (A) Bohr recurrence/syndetic torus
densities against positive-density one-sided source bounds — lands exactly on T2's "subhalf"
frontier (κ=1 bad-set density = 1/2) with RBH's separated-sign machinery as the classifier;
(B) C9, the function-field Perron–Frobenius template: SC's one-negative-square Krein fibres
(Lorentz slot) + the manifestly cone-preserving `Z = Σ n^{−1/2}S_{log n}` (Frobenius slot) with
the missing weld as open core, first test on the two-atom truncation against the Lean witness.
Killed: shift-orbit amplification (window term), abstract Toeplitz/Smirnov dichotomy (S_κ
exists), Pontryagin symmetry-compression (symmetry group too small), det-sign mod 2 (counting).
