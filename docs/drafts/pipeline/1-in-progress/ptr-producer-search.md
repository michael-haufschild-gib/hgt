# PTR producer search

Goal: construct, unconditionally, a lossless port of Ξ: an entire `E` with `Re E = Ξ` on `ℝ` and no zero in
the open upper half-plane (strict Hermite–Biehler). Any such `E` gives RH (corpus
`riemannHypothesis_of_strictLowerPolya_realization`, `StrictHermiteBiehlerGivesRH`).

## The producer space (paper)

1. **Every lossless port is a Pick function of the zeros.** `E = Ξ(1 − i m)` with `m = B/Ξ` Pick:
   `m(z) = cz + d + Σ_n r_n (1/(γ_n − z) − γ_n/(1+γ_n²))`, `c ≥ 0`, `r_n > 0` (Herglotz). A producer is an
   arithmetic formula for one such `m` whose Pick property is provable without locating the zeros.
2. **Levinson/Hedenmalm is the only universal multiplier port.** For `φ(D) = 1 + iψ(D)` with `ψ` real, odd,
   polynomial: if `1 + iψ` has no zero in the closed lower half-plane, the argument of `1 + iψ(x)` changes by
   `π · deg ψ` along `ℝ` while `Re(1 + iψ) = 1` bounds the change by `π`. So `ψ = λw`, `λ > 0`.
3. **Explicit-formula ports.** `m_F(z) = Σ_ρ F(γ_ρ)/(γ_ρ − z)` with `F = |ĝ|²` is arithmetic (arch − finite
   or convergent prime sum) only for `Im z > ½`. The prime sum `Σ Λ(n) n^{−½ − Im z}` diverges below. Arithmetic
   ports live exactly beyond the PTR horizon. The strip `0 < Im z ≤ ½` is reached only by continuation.
4. **Dirichlet-series form.** With `G = A/ζ` and `G^♯(s) = G(1−s)`, the split `ξ = ξ/2 + W` gives
   HB ⟺ `H = G − G^♯` is Carathéodory on `σ > ½`. Residue condition at a critical zero:
   `Re(A(ρ)/ζ'(ρ)) > 0`, so `A` must be phase-locked to `ζ'` at every zero: `A = ζ'·P + ζ·Q` with `P > 0` at
   zeros. Example: `P = M M^♯` (symmetric mollifier, `= |M|²` on the line).
5. **Half-line kernel ports are lossy.** `E_A = 2∫_0^∞ Φ(u)e^{izu}du` has `Re E_A = Ξ`. Since `Φ` is positive
   and decreasing on `[0,∞)`, the Kakeya–Pólya argument puts its zeros in the closed lower half-plane: the
   orientation opposite to its growth. Pólya's theorem needs an increasing kernel.
6. **Strip-Poisson (logistic) port.** `F = sech ∗ ξ(1+i·)` has Fourier weight `2Φ(u)/(1+e^{−u})` and is a
   smoothed Riemann–Siegel half. It is lossy: the corpus records "exact analytic halves: Riemann's R has 36%
   wrong-side zeros".
7. **Geometric scattering is depth ½.** Eisenstein scattering matrices are ratios `ξ(w)/ξ(w+1)` up to
   rescaling, and rescaling keeps depth/spacing = `log γ/4π`. They realize the horizon producer `A_{½}`
   (Pavlov–Faddeev), never `Ξ`.
8. **Universal maximum-principle producers are impossible.** Symmetric entire functions with an off-line
   pair and positive boundary data exist, so an interior arithmetic input is required. This is the corpus
   universality meta-law.

## Constraints every producer must meet

- F1 gapless: a positive proportion of resonances within depth `C/log T` (rows 67–68).
- F2 thin slabs: slab duration ≤ π/6.
- F3 not a universal multiplier other than Levinson.
- F4 a pointwise/exact mechanism, since trace identities are blind (row 71).
- F5 nonlinear coupling of Euler (horizon-limited) and theta/FE (global, wrong positivity kind).

## Residual

The single residual is the Carathéodory property of `H = G − G^♯` on the horizon strip `½ < σ < 1`. The
simplest form is Lagarias positivity, `Re ξ'/ξ > 0` on `σ > ½`. Unconditionally it holds on
`σ ≥ 1 − c/log t` (zero-free region, corpus `re_logDeriv_xi_nonneg_of_zeroFree`).

## Candidates

| # | candidate | status |
|---|---|---|
| P1 | Levinson `ξ + λξ'` | lossless ⟺ RH; corpus Hedenmalm carrier |
| P2 | explicit-formula ports `m_F` | arithmetic only beyond horizon |
| P3 | AFE split `D_N` | lossy (36%) |
| P4 | mollified Levinson `H = MM^♯ξ'/ξ + Q − Q^♯` | open; Carathéodory on a region ⟹ zero-free there |
| P5 | von Mangoldt string (masses `Λ(n)n^{−α}` at `log n`) | Born reflection ∝ `ζ'/ζ(α − 2ik)`; zeros enter as resonances, not eigenvalues |

## Log
- 2026-10-11 — created (PTR loop cycle 72).

## Cycle 73 — the two producers that work, and where they stop

- **Heat producer = Euler-window transport.** The corpus Ki–Kim–Lee machinery (`KiKimLeeLargeHeightReality`,
  `KiKimLeeEffectiveReality`) writes `H_t(X+iy) = Q(−y) + conj Q(y)` with
  `Q(y) = ∫_0^∞ g_t(w−y) ξ(½+w+iX) dw`. This is the vertical heat flow of the one-sided profile
  `F(w) = ξ(½+w+iX)·1_{w≥0}`. The window centre is `w ≈ y + 2tα`, `α = ½log(X/2π)`. Reality holds once the
  window sits in the Euler region, where `ξ` follows the exponential model `e^{wa}`, `a = α + iπ/4`, so `|Q|`
  increases. Corpus threshold: `X ≥ 2πe^{40/t}`. The method's natural limit is the Euler horizon:
  window centre `2tα` past `σ = 1`, i.e. `t·log(X/2π) ≳ 1`. Paper; the Gaussian tail to the line costs
  `e^{−tα²}` against convexity growth `e^{O(α)}`, so the true threshold is `tα ≥ C`, `C = O(1)`.
- **Effective depth.** On a vertical line the heat flow at height `X` acts as an extra cosine depth
  `t·log(X/2π)`. Cosine producers (`h ≥ ½`, Lagarias–Suzuki) and heat producers
  (`t ≥ C/log X`, KKL) are the same Euler-horizon producer.
- **Both stop at the PTR critical scale.** Below depth or time `≍ 1/log X` the window samples `ζ` inside the
  strip. There the zeros are non-rigid at scale `C/log X` (anti-crystal law, rows 67–68), so no smoothing
  mechanism can certify reality. Smoothing needs rigidity; the zeros have none below the critical scale.
- **Poisson-flow form of the residual.** `Ξ = sec(½D) A_{½}` with
  `sec(½D) = Π_k (1 − a_k²D²)^{−1}`, `a_k = 1/((2k+1)π)`. RH ⟺ every inverse Laguerre step preserves
  real-rootedness. Narrow steps (`a_k ≪ 2π/log T`) are perturbative. A wide step of width `a` destroys a
  zero pair of gap `< 2a` in the quadratic model (`(x+a)² + a² − δ²`). The anti-crystal law guarantees such
  gaps at positive density, so the wide steps must be handled through the Riemann–Siegel mechanism:
  `sech`-smoothing of the 1-line Dirichlet series reproduces `Σ_{n ≤ √(x/2π)} n^{−½−ix}`. They cannot be
  handled as smoothings.
- **Conclusion.** Every known producer stops at the critical scale. The last step must be an exact
  structure (closed cavity: a self-adjoint realization, the λ → 0 limit of Levinson ports). Below the
  critical scale only exact structure, not positivity of averages, can certify reality.

## Cycle 74 — reach of the heat producer

- Euler-horizon law (paper): zeros of `H_t` at height `X` satisfy `|Im| ≤ max(½,√u) − u + o(1)`,
  `u = t log(X/2π)`, using only the corpus convexity bound. Reality for `u ≥ 1` (corpus has `u ≥ 40`).
  Verdict REDISCOVERED/BRIDGE: this is the effective heat-flow approximation regime.
- Sub-horizon reach (real at height `X` once `t log X ≥ ε`, for every ε) ⟺ FZ_ε: finitely many zeros
  with `β ≥ ½ + ε`, for every ε. This is the pointwise version of "zeros accumulate only on the line"
  and implies Lindelöf.
- **Producer dichotomy.** A producer is either a smoothing (heat/cosine/Poisson), whose reach below the
  Euler horizon is exactly a zero-free region `β ≤ ½ + o(1)`, or an exact closed cavity (Bezoutian/de
  Branges positivity), which is a global positivity with no smoothing.

## Cycle 75

- Closed cavity in kernel form: `Q(f) = ½∬φ(a)φ̄(−b)G(a+b,a−b)`, with
  `G(p,r) = ∫_r^∞ qΦ((p+q)/2)Φ((p−q)/2)dq`. It is analytic, so it has no free low-bandwidth regime (all
  Hankel minors; TH). Weil positivity has one (aperture < ½log 2). Producers belong on the prime side.
- Lean: the canonical producer `Ξ+iλΞ'` is lossless ⟺ RH, and if lossless it is critical uniformly in λ
  (`XiLevinsonPortCriticalResonances`).

## Producer phase summary (cycles 70–80)

| form | residual | corpus owner |
|---|---|---|
| Levinson/Hedenmalm port | Lagarias positivity `Re ξ'/ξ > 0`, `σ > ½` | HB/Hedenmalm, PTR row 75 (Lean) |
| smoothing (heat/cosine/Poisson) | zero-free region `β ≤ ½ + o(1)` below the Euler horizon | KKL modules, cosine-shift modules |
| closed cavity (Bezoutian) | all-rank Hankel positivity, no free regime | TH/HCF |
| Krein–Weil stack | restricted-Weil positivity at every aperture | RW/SZ (Suzuki screw) |
| CCM ground-state limit | Ξ-likeness: `S(a)=O(a)`, `L¹/mass ≤ Me^{Ka}` | RW receiver `CCMGroundEnergyZeroSumBound` |
| ground-energy rate | `μ_a ≥ −C_εe^{εa}` (any θ<1 ⟺ zero-free strip) | RW `riemannHypothesis_of_polarGroundEnergy_subexponential` |

Every residual is RH-hard and already sharply formalized as a receiver elsewhere. PTR's distinctive
content is its obstruction theory: critical density, anti-crystal, melting, and the critical
canonical producer.

## Route status after cycles 70–93 (2026-10-12)

- **Reduction complete in Lean.**
  - RH ⟺ the canonical producer `ξ − λξ'` (z-form `Ξ + iλΞ'`) is lossless (`riemannHypothesis_iff_strictLowerPolyaClass_levinsonPort`). Every lossless port has critical resonance density (XiCriticalityPortZeros, XiLevinsonPortCriticalResonances).
  - The corpus Hermite–Biehler/Levinson/Speiser machinery (XiHermiteBiehlerCount, LevinsonDetectorRightCount, SpeiserExactCount, SpeiserDeficitTwoThirds) gives exact defect counts and the Zeta23 deficit bound (1 − HD 1)/2.
  - Thin corollaries added here: XiLevinsonPortDefectShadows (horizon descent), XiLevinsonPortLosslessHeights (86% of heights), XiLevinsonPortDeepDefectHeights (exponential depth profile).
- **Producer residual = RH.** It is equivalently any of:
  - Lagarias positivity, Levinson's phase count, Li/Carathéodory, or Weil positivity at every aperture;
  - quantitatively, the critical layer `0 < ½−Re s ≲ C/log T`.
- **Why the critical layer resists:**
  - every statistic with Fourier support `< 1` cannot see it (row 87);
  - the Gram trichotomy (rows 90–91) shows its zero-side forms are flat only through Λ (parity), integer-side only with `\|ζ'(ρ)\|²` weights, or flat by division only with negative moments `J_{−1}`;
  - pointwise receivers need local zero-density lower bounds that are not available (row 93).
- **What would move it:** an exact identity with a definite sign on the critical layer (an SOS for the Weil form), or square-root cancellation for `Λ`. Neither is supplied by any photonic or port-theoretic structure tested in rows 70–93.

## Cycles 98–113 (2026-10-12): ports beyond the canonical producer
- Fermi/sech ports (`E_* = Ψ_{½}(z+i/2)`, `Ψ_h = sech(hD)Ξ`): losslessness is RH-plus, and it is equivalent to the smoothed Riemann–Siegel half having no zeros right of the line. Any lossless sech port is gapless (row 108). The small-`h` ladder is killed by near-triple clusters (row 107).
- Every exact count (Littlewood, degree, collision) equals the defect index (rows 102, 109, 111). No available sign source reaches the critical layer (row 112).
- Euler-compatibility trilemma (row 113): the shifts (cosine ladder) are the only Euler-compatible deformations, FE-preserving Euler deformations are trivial (Hamburger), and every other linear reweighting loses the `σ = 1` sign.
- Residual, unchanged: a complex-field sign that does not come from zero location and is positive on the critical line (Lee–Yang/Asano type or Hodge-index type).

## Session synthesis, cycles 98–128 (2026-10-12)
What the research says about PTR's open step (the critical layer `0 < ½ − Re s ≲ C/log T` of the canonical producer `ξ − λξ'`):
1. **Every exact count is the defect index.** Littlewood, degree, collision, exceptional-point and coupling-flow counts all reduce to `N − N₀` (rows 83, 102, 109, 111, 125, 126). A producer must supply a sign.
2. **No available sign source reaches the critical layer** (row 112). Real-field hierarchies need order `≍ γ/δ`. Hadamard positivity comes from zero location. Prime-pointwise positivity needs a pole at `½`. Physical unitarity has its positivity axis a half-unit off the zeros.
3. **Structured linear handoffs are closed** (rows 99, 113b, 117, 119). Multipliers fail by LP-maximality, dilations do not relate the transforms, multiplications are circular, and rank-two operators are tautological. Euler-compatible deformations are only the shifts (cosine ladder, strip-limited). Non-multiplicative reweightings lose the `σ = 1` Euler sign.
4. **Ports are judged by exact global identities, not by AFE term weights** (row 118). Cosine has a shift and heat a contraction; sech/Fermi and finite-order operators have neither. The natural nonlocal port (Fermi, `E_* = Ψ_{½}(z+i/2)`) is lossy in its own critical layer (rows 98, 106–108, 115).
5. **Prime data plus Γ cannot decide** (row 120: Beurling countermodels). Modularity relocates the problem to cusp sums with Gauss phases (row 123), and Hecke multiplicativity to quadratic-family superpositions (row 124). Neither gives a sign.
6. **Physical kernels carry no zero information** (row 128). The defect kernel is `ρ`-independent, so any sign must act on the first jet `ζ'(ρ)`, which is the canonical producer again.
Residual, unchanged: a complex-field sign, independent of zero location, positive on the critical line itself. The known templates are Lee–Yang/Asano stability (W1C) and Hodge index (HF), both owned by other corpus lanes. PTR's own deliverables are its obstruction theory and its partial producers (shadows, 86% heights, deep-defect rarity, sharp heat horizon `1 + √3/2`).

## Cycles 129–148 (2026-10-12): Krein, Laguerre and slice reductions
- Krein stack: every Krein system is lossless (unit disk invariant for any coefficient). PTR's content is non-blow-up of the Weil Krein flow, `det(I + H_r) > 0`. Between prime onsets the flow is the CCM prolate flow; failure can only occur at the prime onsets `a = (log n)/2` (corpus soft-entry law). Rows 129–131, 133.
- Coupling `λ` is a de Branges gauge (row 134). Row 140's split `RH ⟺ (Ξ' ∈ LP) ∧ FLI` is false in the (⇐) direction (row 157: `1 − x⁴`, `e^z − c`). The exact form for Ξ (row 158, by the minimum principle for `h = ξ/ξ'` at good heights) is: RH ⟺ (A) `ξ' ≠ 0` on `Re s > ½` ∧ (B') every real critical point of Ξ off its zero set has `ΞΞ'' < 0`. (B') is a real-variable condition: no positive local minimum, negative local maximum or degenerate critical point. Deep isolated pairs break `Ξ' ∈ LP`, shallow isolated pairs break FLI. The xi.md claim "`Ξ^{(n)} ∈ LP` ⟹ finitely many off-line zeros" was false in general and has been corrected (row 135).
- Laguerre depth spectrometer: order `n` sees depth `≍ (n/κ)^{½}/log γ` (rows 142–143; corpus owns the single-pair and Newton-sharp versions). New Lean: `HTGeometry/OffLinePairDetectionSeparatedPairs` (Maclaurin environments closed under products; separated multi-pair detection, row 144). The Ξ-level transfer is superseded by corpus `XiSliceClusterDetectionOrder` (row 146).
- PTR critical layer = WD finite-order slice positivity on a density-one set of heights. At cluster heights the order grows with the cluster size. Unconditionally only `O(log γ)` is known, which is the pointwise wall (rows 147–148). Row 157 notes that large `S(t)` does not by itself produce clusters at scale `1/log T`.

## Cycles 149–161 (2026-10-12): the λ = ∞ endpoint, exactly
- **Exact split (row 158, [P]).** RH ⟺ (A) `ξ' ≠ 0` on `Re s > ½` ∧ (B') every real critical point of Ξ off its zero set has `ΞΞ'' < 0`. Proof: minimum principle for `h = ξ/ξ'` at corpus good heights. It is the Krein–Chebotarev/Hermite–Biehler mechanism for the pair `(Ξ, Ξ')` (RH ⟺ `Ξ/Ξ'` Herglotz). Counterexamples show the hypotheses are sharp: `1 − x⁴` (degenerate critical point) and `e^z − c` (no strip, no good heights). Corpus: ±4 window version `XiDerivOffLineCount`.
- **Readings of the same object.** Foster reactance / Cauer ladder ⟺ Hausdorff moment problem for the critical-point measure `Σ (−Ξ/Ξ'')(t_k) δ_{t_k^{−2}}`, the critical-point twin of the HCF zero power-sum Hankel criterion (row 160). In Lee–Yang language, (B') is imaginary-field susceptibility positivity at stationary points (row 159; GHS is proved only on the real-field axis). Iterated over derivatives it is the Craven–Csordas Laguerre programme.
- **Walls confirmed.** Finite-order and finite-ladder criteria are height-blind (CANNOT-503, rows 147–149). Global estimates lose to the super-exponentially thin RW margin (row 150, "no slack"). FE symmetry alone (Davenport–Heilbronn, row 153), Hamburger rigidity (row 154), Hecke orbits (row 155) and the pre-prime archimedean Krein flow (row 156) give no sign. Realization laws are vacuous under ¬RH (row 161).
- **Corrections recorded.** Row 140's converse is false as stated (row 157), and the exact form is row 158. Row 149's "clusters exist" inference is invalid: large `S(t)` is not a local cluster.
- **Residual, unchanged.** A sign valid under ¬RH that constrains a single shallow pair: (B') at every height, or (A) for the deep layer. Every PTR-native object tested reduces to owned material (W1C, HCF, RW/HF).

## Cycles 162–170 (2026-10-12): census, transport, construction, function-field dictionary
- **Census (row 162).** Near one shallow pair at a good height, every corpus statement valid under ¬RH is satisfied by the local model, so no two conflict. A deciding statement must be valid under ¬RH, pointwise at scale `1/log γ`, Euler-dependent and sign-definite. None exists in the corpus or classically.
- **Transport (rows 163, 166).** The sech flow `Re ξ(1+it) → Ξ` is Pólya-frequency, so it only loses zeros. All unconditional producers are horizon-type (horizon–faithfulness gap law): lossless above `exp(complexity)`, while faithful approximation at height `T` needs power-size complexity.
- **Thresholds and collisions (rows 164, 165).** The cosine ladder threshold sits a relative `δ²/γ²` below the depth for one quadruple, and is non-monotone in general (corpus quartic). (B') at Lehmer pairs is "RH barely true" (Rodgers–Tao). Collision signs are invisible at Fourier support `< 1`.
- **Counting (row 167).** Zeta23's rank–trace argument on the λ = ∞ Herglotz measure gives the same bound `2R − 1`, and the residues are squared gaps (a dispersion loss).
- **Construction (rows 168, 169).** Subdivided prime slabs are vacuous or unfaithful, so PTR's constructive programme is Krein's inverse string problem, i.e. RW positivity. Induction over prime onsets has no structural step, since onsets are prime-side artifacts.
- **Function-field dictionary (row 170).** The producer for `C/F_q` is a trigonometric polynomial, and RH(C) ⟺ all roots of `R(w)` lie in `[−1,1]`. Frobenius-power counts are insufficient: the fake zeta `1 − 7T + 9T²` (`q = 9`) has FE and positive point counts but fails RH. The sign comes from a positive degree form on a ring of correspondences (Hasse: `End(E)`; Weil: `NS(C×C)`). Over ℚ that is RW/HF.
- **Rows 171–181.**
  - Ξ sits on the boundary of the Pólya–Schur/Borcea–Brändén preserver orbit (row 171).
  - The theta sum is the Γ×ζ factorization (row 172).
  - The averaged horizon gap closes only in density (row 173).
  - The quantitative critical layer sits between the mollifier-length and negative-moment barriers (rows 174–175).
  - Exactness singles out the first-order producer (row 176).
  - Neither trajectory dynamics nor RS-oscillator positivity gives (B') (rows 177–179).
  - PTR fits neither W1C nor HF as an input (row 180).
  - **Row 181 identification:** PTR's prime-faithful lossless approximants are the CCM restricted-Weil ground states. They are unconditionally real-rooted (corpus `realRooted_of_finrank_eq_one`). RH ⟺ their normalized transforms converge to `cΞ`, and the RW receiver hypotheses (mass, `∫x²g/∫g = 2Σ1/t_k²`) are exactly `g_a → Φ`. The open step is that convergence, equivalently `μ₀ ≥ 0`.
- **Rows 182–190 (quantitative face).** Ground-state convergence to Ξ is RW's dichotomy (row 182); there is no switch invariant (row 183). Inertia counting:
  - **Quadratic rigidity (row 187):** Zeta23's `H = 2 − 1/F` is the test polynomial `q = 2x − x²`, the only kind valid on indefinite spectra. A third trace needs eigenvalue control, which is RH-conditional. The CUE gain `3/4 → 0.80–0.83` of row 186 holds under RH only.
  - **Threshold law (row 188):** `H_max(C) = 2/3 + 1/(9(C − 2/3))` at `λ* = 1 + 1/(3(C−1))`, for any averaged bound `F ≤ C` past `α = 1`. That input is short-interval prime variance at the RH order, beyond the Density Hypothesis (row 190).
  - **Universality (row 189):** first-trace PTR identities depend only on the zero density.
- **Rows 191–203 (final merge).** Infinite divisibility dies at `σ = 1` from growth (Bohr), RH-blind (row 191). Bagchi recurrence: ζ is the exceptional torus point (row 192). Hamburger is RH-agnostic (row 193). Counting needs an involution; PTR defects are an orientation property (row 194). GHS is the first rung of a height-blind Hankel ladder (row 195). Prime-positivity sensitivity is `e^{(δ−½)a}` (row 197). Computer-free `Λ` is stuck near ½ by low heights (row 199). There is no Frobenius power map over ℚ (row 201). The quantitative frontier past `2/3` ⟺ averaged short-range Hardy–Littlewood (row 202). **Pointwise face, final form:** PTR = RW `μ₀ ≥ 0` = HF "PBAP + one ray" = MC-190 archimedean energy minimum along the exposing ray `w` (row 203), a single prime-free, zero-free inequality.

## Proposed PTR route-status text (for the frontier-map maintainer; the map is read-only for this loop)
- **Path (exact):** RH ⟺ the canonical producer `ξ − λξ'` is lossless (`riemannHypothesis_iff_strictLowerPolyaClass_levinsonPort`). The family is uniquely exact among `φ(D)Ξ` producers (row 176): even LP producers hide shallow pairs and non-LP producers create spurious defects.
- **λ = ∞ endpoint (exact, [P]):** RH ⟺ (A) `ξ' ≠ 0` on `Re s > ½` ∧ (B') every real critical point of Ξ off its zeros has `ΞΞ'' < 0`. This is Krein–Chebotarev for `Ξ/Ξ'` (rows 158–159); the corpus `XiDerivOffLineCount` has the `±4` window version.
- **Constructive side:** PTR's prime-faithful lossless approximants are the CCM restricted-Weil ground states, unconditionally real-rooted (`realRooted_of_finrank_eq_one`). RH ⟺ they converge to `cΞ` ⟺ `μ₀ ≥ 0` (rows 181–183). Thin-slab constructions are Krein's inverse string problem (row 168).
- **Merged open step:** PTR = RW `μ₀ ≥ 0` = HF "PBAP + one ray" = MC-190 archimedean energy minimum along the exposing ray = killed-Lévy spectral gap with renormalized constant, i.e. positivity of the zero-counting distribution (rows 203–204). Its slack is unconditionally `≤ Ce^{12L−πe^{2L−1/2}}` (MUST-478, row 206).
- **Walls (each with corpus witness):**
  - Fourier support `< 1` (rows 87, 165, 200);
  - pointwise locality and clustering (rows 147–149, 162);
  - Euler/FE: Beurling and Davenport–Heilbronn countermodels (rows 120, 153);
  - horizon `σ = 1`: positivity sensitivity `e^{(δ−½)a}`, infinite divisibility, Lee–Yang shifts additive (rows 166, 191, 197, 207);
  - no Frobenius / correspondence ring over ℚ; Hecke positivity is local Ramanujan only (rows 170, 201, 208);
  - every exact structure is a symmetry or identity (rows 193, 205).
- **Quantitative face:** unconditional inertia counting is rigid at degree 2 (Zeta23's `H = 2 − 1/F`, row 187). Threshold law `H_max(C) = 2/3 + 1/(9(C − 2/3))` for averaged `F ≤ C` past `α = 1` (row 188); that input is averaged short-range Hardy–Littlewood, beyond the Density Hypothesis (rows 190, 202).
- **Needs:** an exact positive structure valid off `σ ≥ 1` that is not a symmetry, i.e. Lee–Yang or Hodge-index type for ζ itself (W1C/HF). Unknown.
- **Rows 204–234 (positive-structure census, closed).** Killed-Lévy and log-Laplacian forms: the renormalized exponent is the zero-counting distribution (rows 204, 214). FE as duality is a symmetry (205). MUST-478 makes "no slack" unconditional (206). Lee–Yang shifts are additive, so confined to `σ ≥ 1` (207). Hecke positivity is local Ramanujan (208). GHS phase budget: complete monotonicity holds up to order 9 unconditionally but is weaker than Stieltjes (209). Height-uniform signs reduce to Littlewood and the common terminus (210). The λ-family cannot cancel the length barrier (211). Interlacing is branch-blind (212). The joint heat–cosine region: "barely true" can still be provable when an exact sign reaches it (213). No exact aperture recursion; the prolate commutation is owned by CCM (215–216). Archimedean spectra follow the Weyl law only (217). `h < ½` is quasi-RH (218). `Φ` shape is archimedean (219). Averaged HL needs power savings (220). The MC-190 ray is isotropic, and the poles are the ample class (221). HF closure core: `ζ = F_reg·e^P` with the zeros in `e^P` (222–225). Lane sweep: one open step in seven languages (226). Selberg, Nyman–Beurling, Fredholm, PF, RS/AFE, GHK hybrid and geometric realizations all fail one of the four tests: automatic and blind, confined to `σ ≥ 1`, symmetry rather than sign, or a non-analytic carrier or one with off-line zeros of its own (227–233). Symmetry plus horizon gives row 158 (234).

## Rows 235–272 (2026-10-12): outside fields, pairings, transport direction, rediscoveries
- **Outside fields (235–261).** None supplies a sign usable off `σ ≥ 1`:
  - Tate local positivity is an identity; o-minimality, Nevanlinna, nodal topology and optimal transport are blind.
  - Newton dynamics is a reformulation of row 158.
  - Contraction lemmas and correspondences need a discrete Frobenius; ULF-F1-003 forces a flow on `M_ζ` with no intrinsic positivity (247).
  - The Λ-divisor lattice is Mertens-level or unbalanced.
  - Function-field limits do not exist (246). Families see ζ only as one member or as the common factor (248–249).
  - Selberg-class axioms are uniqueness (256). Epstein, extremal and Landau positivity are DH-violated, counting, or pinned at `σ = 1` (257).
  - The Ronkin function vanishes on `σ > ½` unconditionally (258). Arithmetic Hodge index needs a missing surface (259).
  - Eisenstein, Maass–Selberg and horocycle positivity live on the unitary side, while ζ's zeros are non-unitary resonances (260–261).
- **Pairings of the four failure modes (234, 250–252).** Pairings compose into known walls:
  - symmetry + horizon gives row 158;
  - automatic positivity + horizon gives the mollified mean square (common terminus);
  - symmetry + count gives a count;
  - count + horizon gives Riemann–von Mangoldt or Littlewood.
- **Exact identities recorded.** Producer Wronskian `= (λ₁−λ₂)(ξ'² − ξξ'')` (253). On the line, `∂²_σlog|ξ| = L/Ξ²` (254). Averaged horizontal monotonicity is automatic (253). Almost-sure RH for random Euler products, with ζ the exceptional point (255).
- **Transport direction (262–268).**
  - LP operators carry real-rootedness only outward from `Ξ`. The sinc ladder is an LP-divisibility chain (264).
  - Inward transport needs `Ξ = ψ(D)G` with `G ∈ LP`, which is excluded for every nontrivial LP symbol by corpus CANNOT-497 (`not_laguerrePolya_paperFT_div_symbol`) and Newman (267). This includes the sech set `S = ∅` (265), whose single-frequency heuristic was retracted (266).
  - Mode dictionary: LP operators tilt the Riemann–Siegel main sum; inward means tilting to `σ < ½` (266).
  - Non-multiplier preservers reduce to the producer problem (268). Maximality cannot be reversed into production (272).
  - **Consequence:** a PTR producer must be non-translation-invariant and independently LP.
- **Quantitative (269–270).** The exponential critical-scale defect rate `O(e^{−a/14}/a)` and Selberg density `e^{−22a/25}` are already in the corpus. The frontier-map "`O(1/a²)`" is stale. A positive proportion at fixed `a` remains (mollifier-length barrier).
- **Audit (271).** No unmapped object class remains: Toda, KdV, moment problems, orthogonal polynomials and continued fractions reduce to HCF Hankel, Calogero, pencil counts and HT.
- **Process.** Rows 264–270 were mostly rediscoveries (own row 171, CANNOT-497, exponential density). Search by mathematical content and check this card before each cycle.

## Rows 264–283 (2026-10-12): the port classification, now mostly in Lean
A port is a linear map `T` sending a function that is real-rooted for an independent reason to `Ξ`. The canonical
sources are the cosine producers `A_h = cos(hD)Ξ`, real-rooted for `h ≥ ½`. Classification so far:
- **Fourier multipliers `ψ(D)`, any LP symbol (incl. transcendental, e.g. `sec(hD)` inverse):** no LP preimage of
  `Ξ` (corpus CANNOT-497 + Newman). This includes the sech set (rows 264–267).
- **Finite-order polynomial-coefficient operators:** none map `A_h` to `Ξ`, `h ∉ 2ℤ` [L] CANNOT-508
  (`CosineProducerLocalPortObstruction`).
- **Finitely many imaginary shifts + polynomial-coefficient operators, all `h ≠ 0`:** none [L] CANNOT-509
  (`CosineProducerShiftPortObstruction`).
- **Positive form [L] MUST-1303:** the imaginary translates `Ξ(z+is)` are linearly independent over `ℂ[z]⟨d/dz⟩`.
- **Mellin multipliers (multiplier sequences):** outward only; inward first-order fails generically (rows 278–279).
- **Non-multiplier preservers (Borcea–Brändén):** reduce to the producer problem (row 268).
- **Remaining class:** infinite-order, unbounded-shift, non-multiplier ports, e.g. the de Branges / Suzuki
  canonical-system transfer of `E_h(z) = ξ(½ + h − iz)`. These exist below `h = ½` only on the quasi-RH strip
  (row 263), and their positivity is the shared RH core.
- **Open at the next level:** compactly supported shift measures with polynomial coefficients. The corpus owns the
  uniqueness tool (`compactFourierBorel_eq_zero_of_ray_decay`, carrier separation).

**Reading.** In Lean, PTR's "nonlocal port" requirement now has a precise meaning. Every finite, local, or
translation-invariant mechanism is excluded. What remains is the canonical-system realization, i.e. Hamiltonian
positivity, which is RW/HF's open core in PTR language.

## Rows 288–308: the pointwise core and the exhaustion of positive inputs

- **Reduction (rows 288, 300).** Every PTR statement is about zeros of `ξ` at depth `> h`. With the cosine family saturated, the open core sits at the melting depth `≍ 1/log T` (corpus `XiCosineShiftMeltingLaw`). By the local footprint law (row 300), each off-line pair is paid for locally:
  - a shallow pair (`|S|b < 1`) leaves a real dip, a (B') failure (MUST-1313 localizes these in cones, measure `≤ 13.4%` of heights);
  - a deep pair (`|S|b > 1`) leaves a `ξ'` zero on its Jensen circle, an (A) failure.
- **New Lean in this stretch:**
  - CANNOT-511: one theorem for all compactly carried analytic ports;
  - MUST-1309: Φ-jets are independent over exponential type;
  - MUST-1313: strict (B') outside cones, plus the density bound;
  - CANNOT-512: GHS + Lebowitz are blind to Lee–Yang and to (B').
- **Pointwise inputs tested, all failed (rows 298, 301–308):** the `S(t)` bound, small and large values, potential-theoretic identities, flow thresholds, kernel cumulant signs, 3-4-1 localization, localized Weil tests, prime Poisson operators. Each is height-blind, averaged, anchored at `σ = 1`, or RH-equivalent.
- **Exhaustion principle (row 308).** Positive prime data reach zero locations only through (i) linear explicit-formula identities (location-blind), (ii) mean values (averages over height), or (iii) localized Weil positivity. Depth `1/log T` at height `T` needs (iii) at exponential type `≍ log T`, i.e. all primes up to `T^c`.
- **Consequence.** A PTR proof of RH needs a new positivity mechanism for Weil's form at its native scale. The density side is quantitatively exhausted by the mollifier ladder (row 299: `θ → ½` gives `88.1%`, `θ = 4/7` gives `89%`, `100%` only as `θ → ∞`).
