# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-25, corpus `e4965f55a` with the working tree of that day. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](hard-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2510-update/working-log.md`. Nothing was compiled. `[S]`, `[P]`, `[R]` as in the complete report.

## 0. The frontier in nine statements

1. **Single-channel quadratic positivity can only certify blindness.** Every sharp-stable positive convolution ideal of the Meyer source lies in the maximal blind ideal, the sources whose Mellin transform vanishes at every off-line zero (`isGreatest_meyerSharpPositiveIdeal`). Every scale-shift-invariant Weil-nonnegative test space is blind. The blind ideal is closed in the natural topology; for any topology built from critical data, closedness is RH.
2. **Multiplicative positivity is exhausted below RH strength.** On the boundary line the theory is complete: four invariants force `D = δ₀`, each necessary, and a pole of order `k` carries at most `⌊k/2⌋` boundary zeros, every placement realized. In the interior a positive certificate buys exactly the width `(√B − √A)²/G` paid by the growth input `G`; every finite certificate is capped by `(3 − 2√2)/(2L)`; coupled channels split into rational fibres. In completed positive systems, coupling heights gives the same boundary capacity and a `1/log T` collar with at most `κ²` exceptions [S]. Multiplicative positivity contains no quantized inequality at the critical line.
3. **No route has a rung between Vinogradov–Korobov and quasi-RH.** Every graded cancellation receiver, every power improvement in the Vaughan picture, admission at a fixed damping, and multiplicative forcing have a fixed zero-free strip as their first gain.
4. **The invariants determine ζ, and the simple pole is the exact rigidity threshold.** A nonnegative measure on `[1, ∞)` with Riemann's degree-one theta law is integer counting measure. Positive relative deformations of ξ with the functional equation are trivial at pole order one [S] and admit every off-line type at pole order two (a real pair, or a complex quartet bought with one critical refund).
5. **Pole order pays only for inserted zeros.** For finite deformations of ζ, `(Weil-index increment) = (pole-order increment) + R_crit − I_crit` exactly. The absolute inequality `ind₋ ≤ ord₁F − 1` is false. Applied to ζ, every deformation gives only lower bounds on its index. ζ's own off-line zeros, if any, are not budgeted by any pole count; they are paid, or not, by oscillation, which is a rate (statement 3).
6. **Positivity sits on one side of the explicit formula.** The prime measure is positive unconditionally; the zero measure is positive iff RH. The prime-free gap lies on the same side as the known positivity, so Poisson-gap rigidity yields only density statements on the Weil pair.
7. **Positivity is proved on average beyond the square-root threshold, not at points.** Averaged Weil positivity holds at aperture `κ₀ log Γ` on `[Γ, 2Γ]`, with subpower coercivity up to prime support `Γ^{4/3}`. The main term is the local critical-zero weight. The open step is selection.
8. **Cofactor escape has one explicit model and a zero-driven reading.** At every subcritical damping some actual limit has `K_pp ≥ p^{2ε−2} > 0`; kernel families are singletons or continua; white noise passes every proved constraint. On the spectral reading [R], escape states are horizon Grams of translated zeros `ρ − ε`, so excluding escape at a fixed `ε` is a fixed strip.
9. **Every mechanism tested is depth-homogeneous [R].** Harmonic twists, Følner coupling, family averages and tensor powers over `ℤ` gain on a zero's depth exactly as fast as they pay in arithmetic length. A rate needs a term that does not scale: a fixed base loss or a Riemann–Roch count.

## 1. Just work

Known mathematics suffices for each item. None crosses a wall.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test every candidate mechanism against the complete battery. Invariant models: pole-order-2 real stray, pole-order-2 refunded quartet, pole-order-3 quartet, strip-pole quartet, over-regular Beurling systems, twisted boundary systems at `κ = 2r + 1`, double-pole and periodic-pole boundary systems. Curve and signed models: golden curve, `Γ_ℝ^d` solutions, signed self-dual combinations. Escape models: white noise, reset-origin mixtures, translated-zero power-character kernels. Calibrations a mechanism must reproduce: `κ = 1` rigidity, boundary capacity `⌊k/2⌋`, dlVP optimality, Weil for curves. | Each candidate records which model defeats it, or that none does. |
| **W2** | Finite identities and certificates | Gram, Hausdorff, Hankel and Jensen blocks; finite heat transforms; finite schedules, histories and ledgers; finite Robin and Li checks; finite JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W3** | Premise checks for specified sources | Regularity, support, decay, cutoff and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources). | The hypotheses of an existing transfer are discharged. |
| **W4** | Transport of proved inputs | Width functor, RW↔SZ↔CHMD, HF→AIP, Weil margin→heat window, graded Sobolev floors, with every quantifier kept. | Each conclusion stated at its true strength. |
| **W5** | Certified finite extensions and constants | Push the pointwise windows beyond `3/10`, `181/500` and `(log 2+1/50)/2`; make `κ₀, c₀, C₀, Γ₀` and `R₀, T(λ)` explicit. | Certified finite-aperture theorems. |
| **W6** | Corollary assembly | (i) An averaged bounded-energy statement for WL from the high-zero tail and the filtered deficit. (ii) One rate dictionary for RW, SRT and ACS through `groundRate = polarRate`. (iii) The explicit LA/WD residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. (iv) ACS effectivity as exhaustion: Bézout on the full cone ⇔ maximal blind ideal = ⊤ ⇔ RH. (v) The bare-functional-equation form of positive-measure rigidity: derive the strip-decay premise from finite order and absolute convergence by Phragmén–Lindelöf. (vi) Replace the imported `c/(log|t|)^9` collar in the harmonic module by the MPG dlVP calibration. (vii) Extend the index–pole conservation identity from finite to infinite reflection-antisymmetric corrections, refunds included. (viii) Specialize the `κ²` collar sparsity to ζ and compare its constant with dlVP and Landau–Page. (ix) State boundary capacity `⌊k/2⌋`, the completed-system threshold `κ < 2Σm` and the gauge budget `2Σm ≤ κ` as one capacity law. | Each statement proved from existing theorems. |
| **W7** | Cofactor spectral identity | Prove that the actual cofactor Gram is the truncated translation Gram of `b(u) = e^{−u/2}A_ε(⌊e^u⌋)` with `b̂(τ) = G(1/2+iτ)`, `G(s) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s`, and its Plancherel form; add the power-character kernels `Σ B_{ρρ'} j^{−(ρ−ε)} k^{−(ρ̄'−ε)}` to the ADR battery. | The identity and the kernels in Lean; first step of Q3. |
| **W8** | Depth homogeneity per class | Prove the no-go for each amplification class: harmonic twists `n^{−ikt}` keep the zeros' real parts while the growth input rises with the degree; Følner coupling gains only through `1 − β`; family averages over `χ mod q` and absolute tensor powers give `Θ − 1/2 ≲ 1/S` independent of the degree. | One theorem per class, each with its positive survivor. |
| **W9** | Range-limited growth inputs | State the corpus VK step as a `δ`-range instance of `exclusion_iff_restricted`, giving the VK region with its optimal constant and its barrier. | The VK region as an instance of the growth-to-forcing law. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses its receiver.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy, a one-sided lag or Abel moment, the history floor, the regularized abscissa `1/2`, the JAS half-power budget, Mertens at square root, the late-lag sign. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Cofinal admission as `ε ↓ 0`; a Báez–Duarte residual → 0; signed interior Vaughan energy; exclusion of fixed-origin cofactor escape at every damping. | PM, CTF, BVI, PW-B |
| **B1.3** | **Complete Weil positivity at every aperture.** Low and mixed sectors with Gamma, both polar terms and one shared budget. Equivalent forms: the nodal inequality, positive Suzuki first variation, odd capacity, the one-shift reflected collar, global allocation, the `O(L)` ceiling, Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS |
| **B1.4** | **Selection.** From averaged or almost-all-height statements to every height, in particular zero ordinates. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Coefficient positivity on the bounded-height × small-heat region (de Bruijn–Newman `Λ ≤ 0`); all-rank Hankel positivity at one time; both literal heat grids; rank-uniform Schur decay; the Newton interior margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaustion of the maximal blind ideal by an input outside the exhausted classes (single-channel quadratic, finite or coupled multiplicative, linear in the coefficient measure, pole order). Faces: Ward cap vanishing; the integer sub-unit trace residual; renewal boundary orientation; source effectivity; a section count on the scaling surface that registers oscillatory payment; a stabilization weld; pre-divisor compactness; a descending potential; a centered Ising limit; a lossless nonlocal port; a certificate stream. | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** Cofinal contrast equality (BSY); the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; the global index `D < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** A faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; exhaustion of the bounded-orbit carrier. | ACS/Meyer faithful branch |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | First rung of every graded cancellation receiver (WL, PBM, JAS, MC/BVI bands and short windows, all Vaughan power improvements, RW/ACS graded floors, DR), of admission at a fixed damping and of multiplicative forcing. |
| **B2.2** | Finite off-line index. | HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations (B1.8). |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity beyond `α = 2/3`; the filtered deficit; short-window selection (Q1). |
| **B2.5** | At least `3/4` of the zeros on the critical line. | TTPC: signed coalescent surplus `β ≤ 1/18`. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ` (Chowla/Elliott with rates). | MC anti-alignment; SSA constants; BVI rows. |
| **B2.7** | Hardy–Littlewood prime-pair correlations uniform near the square-root band. | TTPC surplus; short-window selection. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | The KKL horizon (LA/WD residual size); the growth input `G`, the only source of interior gain for multiplicative positivity (statement 2 of §0). |
| **B2.9** | Better de Bruijn–Newman upper bounds. | Shrinks the B1.5 region; corpus has `Λ < 1/8`. |

### 2.3 Tier B3: open problems isolated by this research

No solution is known; none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | Physical-`L²` rate equality `polarRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2`; form-norm rates equal `Δ`; bounded local off-line depth suffices. |
| **B3.2** | **Escape-state classification.** Are the escape states of actual cofactor limits exactly the horizon Grams of translated zeros `ρ − ε`, so that the module hull of an actual escape module contains the translated top zeros? | Record-minimum floor; singleton-or-continuum; contraction calculus; eigencharacter moduli `p^{−s}`, `s ≥ 1/2`; finite hulls in the half-plane closure; visible-pole index; white noise survives. Spectral reading [R]; identity not yet in Lean (W7). |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction in the receiver norm. | Only algebraic injectivity; cofactor-graph closedness ⇔ a uniform estimate; in the golden model payment is nonclosed and only total evaluation is continuous. |
| **B3.4** | **Spectral synthesis in the blind ideal.** Is the span of critical-jet sources dense in the maximal blind ideal for its natural Fréchet topology? | The ideal is naturally closed and matches every finite critical-jet reading; for critical-data topologies closedness is RH. |
| **B3.5** | Surface section law: couple the base theta `h⁰` to test components. | Base `h⁰` RR and Mellin; Boolean counts and finite readings cannot pay; no theorem of the square for the Hecke graphs of `ℤ`. |
| **B3.6** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound `e^{−a}[ψ(e^{2c}) − ψ(e^{2a})]·mass`; frozen finite families fail. |
| **B3.7** | **Short-window averaged positivity:** the least `H(Γ)` for which averaged Weil positivity holds on `[Γ, Γ+H]`. | `H = Γ` proved; the mechanism is zero-density driven. |
| **B3.8** | A nonlocal shared-budget calculus; quantitative cofinal two-tower saving. | Frustration and descent laws exact; fixed-box gaps proved. |
| **B3.9** | Arithmetic input on the residual heat region; source-selective cofactor repair. | Model geometry complete; no universal positive multiplier. |
| **B3.10** | Compatible oriented families; quantitative global-index bounds. | Common-endpoint classification; spline-orbit index ≤ 1 ⇔ RH. |
| **B3.11** | Sub-half-damping signed control of the size-cutoff forward interior. | Exterior paid; `ε = 1/2` endpoint bounded for every squarefree support; integer local exponents below half. |
| **B3.12** | Order-uniform PA thresholds; decoupling rank from time (TH, HCF). | Fixed-order thresholds; coupled windows from Weil margins. |
| **B3.13** | Sharp successor constants: the complex floor in `[−1/2, −1/3]`; zero-defect signs beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`, both exact. |
| **B3.16** | Is the paid ideal of `μ_ε` nonzero on escape? | Paid ideal = ⊤ ⇔ admission; escape gives paid ideal ⊆ annihilator; visible poles bound the paid quotient from below. A positive answer excludes white noise and every faithful module; on the spectral reading [R] it does not exclude the translated-zero states, so it does not decide escape. |
| **B3.17** | **Scale-side coupled positivity.** An unconditional positivity theorem for the Weil or Meyer form on a carrier that is not a single sharp-stable convolution ideal (two dilated channels, `ζ(s)ζ(s+iτ)`, Rankin–Selberg sources `Λ ⋆ Λ`, cones that are not `♯`-stable) and is not off-line blind; or a maximality theorem for all such carriers. | Single-channel class exhausted. Height-side coupling is answered: certificates split into rational fibres (APD), and in completed systems Følner coupling gives boundary capacity and a `1/log T` collar only [S]. No scale-side coupled carrier has been studied. |
| **B3.18** | Equality case of collective boundary capacity: does a completed positive system with even `κ` carry boundary zeros of total multiplicity `κ/2`? | Odd `κ = 2r + 1` is sharp (twisted ζ). Boundary data reach `2Σm = k` only through double-pole quotients without a ζ factor, which have no Riemann-FE completion. |
| **B3.19** | **A base for coefficient systems over `Spec ℤ`.** A base `B` with a simple pole and no zeros; a self-dual system `F` whose even tensor powers have nonnegative log-coefficients; a computable pole part of `L(B, F^{⊗2k})`; ζ's zeros among those of `L(B, F)`. Then `Re ρ ≤ 1/2 + O(1/k)` for every `k` [R]. | Over `𝔽_q` this is Deligne's argument, with a fixed base loss that disappears under `2k`-th roots. Over `ℤ`, `Spec ℤ` is its own base, the class at pole order one is `{ζ}`, and data definable from multiplicative structure alone are expected to admit over-regular Beurling countermodels [R]. |
| **B3.20** | **Signed near-coincidence cancellation at one height** beyond aperture `½ log Γ`: kernel-weighted prime-pair sums with signs, at a single height, beyond the square-root threshold. | Single-height phase-selective law; syndetic phase recurrence; absolute-averaged Hardy–Littlewood versions are expected to start at a fixed strip [R]. Selection beyond `½ log Γ` reduces to this [R]. |
| **B3.21** | **Prescribed successor coordinates.** A positive functional on the affine group of `ℚ` whose successor part is fixed by the arithmetic source (a Hecke or Bost–Connes state), and the positivity it forces on the dilations. | Affine positivity is induced from the dilations with free successor part; RH ⇔ some affine positive-definite function restricts to the spline correlation. |

### 2.4 Settled questions

- **Absolute pole-order budget** (B1.9): false. The index–pole conservation identity is exact; the refunded quartet violates `ind₋ ≤ ord₁F − 1`; for ζ every deformation gives only lower bounds.
- **Interior multiplicative forcing by finite or multi-channel certificates** (B3.14): excluded beyond growth input.
- **Completeness of ζ's invariants** (B3.15): settled by positive-measure rigidity and the relaxation models.
- **Closedness of the blind ideal:** closed naturally; closed for critical data iff RH.
- **Quantized inequality from multiplicative positivity at the critical line:** none (`fejer_quantumBudget_half`).
- **Augmentation as the escape picture:** excluded as unique state.

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier. A positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three walls, each in its own currency.

### Q1. Selection: how short can the averaging window be?

> *What is the shortest window `[Γ, Γ + H(Γ)]` on which unconditional averaged positivity of the complete Weil form at logarithmic aperture holds? In particular, does it hold for `H = Γ^θ` with some `θ < 1`?*

- **Why.** Positivity at every height is RH; positivity averaged over `[Γ, 2Γ]` is proved, with the local critical-zero weight as main term and off-line contributions controlled by zero-density shells. Shrinking the window is a question about zero density in short windows, a classical theme with existing tools. Each intermediate `H` is a new kind of partial result, positivity at almost all heights in short windows, which is not a zero-free strip and is not depth-homogeneous in the way amplifications are: it trades window length, not arithmetic length.
- **Tools.** Short-interval zero weights; the 30/13, Ingham–Huxley and Guth–Maynard density bounds; the all-length Heath–Brown estimate; the phase-selective single-height law; the bad-frequency volume bound.
- **Outcomes.** A threshold `θ₀` with positivity for `θ > θ₀` is the first quantitative selection step for RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF, ACS, SRT and WL together. A proof that no `θ < 1` follows from density inputs alone identifies the missing input as signed short-window prime-pair correlation (B2.7, B3.20).

### Q2. Coupled positivity on the scale side: does any positive carrier escape blindness?

> *Is there an unconditional positivity theorem for the complete Weil or Meyer form on a carrier coupling several scale channels (two dilated channels, `ζ(s)ζ(s+iτ)`, Rankin–Selberg sources `Λ ⋆ Λ`, convolution cones that are not `♯`-stable) whose carrier is not contained in the maximal blind ideal? Or does maximality extend to every such carrier?*

- **Why.** Five forcing classes are mapped below RH strength: single-channel quadratic positivity (maximality), finite multiplicative positivity (growth caps), coupled height positivity (fibre splitting; boundary capacity in completed systems), linear rigidity (identifies ζ, not its zeros) and pole order (pays only inserted zeros). Linear forcing in the logarithmic measure cannot isolate a line, since an analytic kernel vanishing on `Re s = 1/2` and positive off it is zero, so forcing must be at least quadratic. Coupled quadratic positivity on the scale side is the only quadratic class the corpus has not mapped. The maximality proof needs sharp stability and convolution closure: it turns an off-line value into the negative-trace packet `u − u♯` inside the carrier. A carrier lacking either property avoids that proof.
- **Selectivity test.** Any candidate must fail on the relaxation models (pole-order-2 real stray and refunded quartet, strip-pole quartet), reproduce `κ = 1` rigidity, and state how its gain scales with arithmetic length (depth homogeneity, W8).
- **Outcomes.** A non-blind positive coupled carrier is the first positivity theorem in the corpus that is not a blindness certificate, and a candidate forcing input for B1.6. A coupled maximality theorem closes quadratic positivity entirely and leaves only mechanisms with a base (B3.19) or a section count (B1.6).
- **Tools.** The maximality proof and its negative-trace packets; the harmonic coupling formula; the strip Bochner–Weil form and its polar-surface shadow (Hodge index ⇔ `L(x,x) ≤ 2κ ℓ_H(x)ℓ_V(x)`); the scale-stable family law; the Rankin–Selberg structure of `Λ ⋆ Λ`; the two-prime Bochner receiver on `T²`.

### Q3. Escape: are actual escape states exactly the translated zeros?

> *At a subcritical damping `ε`, is every escape state of the actual cofactor limits a horizon Gram of the translated zeros `ρ − ε` with `Re ρ > 1/2 + ε`, and does the hull of every actual escape module contain those translated zeros?*

- **Why.** Cancellation routes have no graded rung below quasi-RH; their only other handle is the escape alternative. The paid-ideal question (B3.16) does not decide it: on the spectral reading the translated-zero states are annihilated by the paid ideal automatically. The decisive question is what the escape states are.
- **Route.** First W7: the cofactor Gram as the truncated translation Gram of one profile whose Fourier transform is `G(1/2+iτ)`, `G(s) = ζ(s)(1/ζ(s+ε) − 1/ζ(1+ε))/s`. Then the classification, using the visible-pole index, the eigencharacter moduli and the record-minimum limits.
- **Outcomes.**
  - *Yes.* Escape at `ε` is exactly the presence of uncancelled zeros right of `1/2 + ε`. PM, CTF, BVI and MC lose the escape alternative as a separate handle: it becomes the fixed-strip rung B2.1, and U1 reduces completely to rates.
  - *No.* Actual escape modules carry states not driven by zeros. Those states are arithmetic objects that a source estimate can target directly, and they give U1 its first handle that is not a strip.
- **Tools.** The paid-graph identification; visible-pole constraints `ord k(ρ−ε) ≥ (ord ζ(ρ) − ord ζ(ρ−ε))₊`; the Fermi Mellin divisor; unit transport; the contraction calculus; record minima; the singleton-or-continuum law.

The three questions are the forcing problem in each wall's currency: selection by height (Q1, Wall 3), positivity outside the blind class (Q2, Wall 14), the structure of escape (Q3, Wall 1).

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. The corpus has a complete map of the known forcing mechanisms, each with a sharp limit.

- **Single-channel quadratic positivity certifies blindness.** Weil, Hodge and trace positivity on a single sharp-stable channel cannot leave the blind carrier.
- **Multiplicative positivity forces the boundary and its capacity, nothing more without growth.** On `Re s = 1` the boundary divisor is positive definite; four invariants force it to vanish off the origin; a pole of order `k` pays for `⌊k/2⌋` boundary zeros. In completed systems the same capacity holds with a `1/log T` collar. In the interior the width is `(√B − √A)²/G`, and no certificate beats the universal cap.
- **Linear rigidity determines ζ but does not see zeros.** Positivity, the functional equation and the simple pole fix the coefficient measure through linear constraints. Zero location is a nonlinear function of that measure.
- **Pole order pays only inserted zeros.** The index–pole conservation identity is exact, the absolute inequality is false, and the simple pole is the exact rigidity threshold. Pole order is a complete invariant for relative deformations and silent about ζ's own zeros.
- **Every amplification over `ℤ` tested is depth-homogeneous [R].** Gains on a zero's depth scale with their arithmetic cost, so they produce no rate.
- **Linear forcing in the logarithmic measure cannot isolate the line.** This is reasoning, not a corpus theorem. A linear functional of the prime measure acts on zeros through an analytic transform; an analytic kernel that vanishes on the whole line `Re s = 1/2` and is positive off it does not exist. In the Hamburger squeeze the target set was discrete (the integers) and `sinc²` vanishes on it exactly. For zeros the target set is a line, so forcing must be at least quadratic.
- **Weil's proof for curves does not transfer.** It forces through a family with a base: sections and ampleness on `C × C`, a ring of correspondences with a theorem of the square, uniformity over all curves, and Riemann–Roch. Over `Spec ℤ` the scaling and Meyer surfaces have Hodge index equivalent to RH, the Hecke graphs satisfy no theorem of the square, and the obvious class graded by pole order degenerates: at pole order one it is `{ζ}`, at pole order two it already admits every off-line type. A class theorem whose base case is RH therefore needs a base that is not ζ itself.

The missing ingredient is a **forcing law of a new kind**. It must be at least quadratic, coupled across scale channels, sensitive to more than pole order, quantitative across limits, independent of the conclusion, and it must contain a term that does not scale with its amplification. No existing toolkit over number fields supplies one.

### 4.2 The field exists: Arithmetic Positive Duality, and what it lacks

The field this assessment points to is already founded in the corpus as **Arithmetic Positive Duality** ([APD README](../../../formal/GaloisForLFunctions/ArithmeticPositiveDuality/README.md)), with [MultiplicativePositivityGeometry](../../../formal/GaloisForLFunctions/MultiplicativePositivityGeometry/README.md) as its rank-one height side and [StripBochnerWeilForcing](../../../formal/GaloisForLFunctions/StripBochnerWeilForcing/README.md) as its strip component. APD's question is the one stated above: the complete rigidity theory of positive arithmetic distributions under Poisson self-duality and integer quantization, and what it can force on the zero side. It already has:

- the **objects**: positive Poisson pairs, positive-definite functions on groups of finite rank and their torus measures, gaps, sign characters, quantum budgets, the affine group of `ℚ`, the critical-jet topology;
- the **mechanism**: the spectral gap identity, an exact sum of nonnegative terms equal to a computable constant, followed by quantization;
- the **two proved instances**: boundary forcing (MPG) and theta forcing (positive-measure rigidity), with the third instance in the strip named as its open core;
- the **contribution standard**: name the positive side, the spectral side, the gap and the integer; state an identity, classification, sharp barrier or rigidity law; run the battery (curves must reproduce Weil with budget `2g`, the golden datum must fail, Beurling countermodels); record every positive survivor;
- the **open agenda**: the third forcing instance; prescribed successor coordinates; rank-`r` realization; positive crystalline measures beyond degree one; integer budgets in the strip on carriers outside multiplicative positivity; spectral synthesis in the blind ideal; signed additive prime correlations.

The B-tier obstacles do not call for a second field. They call for five extensions of APD's scope, each forced by a capacity or exhaustion result; APD's founding document states them as its open topics (oscillatory capacity, coupled scale positivity, a base over `Spec ℤ`, depth homogeneity, spectral readings of the limits):

1. **Inserted versus intrinsic zeros.** The index–pole conservation identity and pole-order-one rigidity show that pole order budgets only zeros created by deformation. APD's quantum budget is the multiplicative scalar model of the pole. The third forcing instance must bound ζ's own zeros, which are paid by oscillation of the zero sum: APD needs an **oscillatory capacity**, not a further pole budget. Its open topic 5, an integer invariant bounded below its first nonzero value on a carrier outside multiplicative positivity, is the right shape; the integer cannot be pole charge.
2. **Depth homogeneity as the organizing obstruction [R].** APD's exhaustion table lists classes one at a time. The common cause, that every amplification over `ℤ` gains on depth as fast as it pays, belongs in its principles, together with the requirement that a forcing step contain a term that does not scale.
3. **A base for coefficient systems.** APD calibrates over `𝔽_q` through positive definiteness of the trace sequence on `ℤ`. Weil's and Deligne's proofs also use a base: tensor powers of a self-dual system with nonnegative traces, a pole part computed by invariants, and a fixed loss removed by roots. APD has no counterpart over `Spec ℤ` (B3.19).
4. **Coupled positivity on the scale side.** APD records that rank helps on the zero side and reads the two-prime orbit as a Bochner problem on `T²`, a receiver. It has no positive coupled scale carrier (two dilated channels, `ζ(s)ζ(s+iτ)`, Rankin–Selberg sources) and no coupled maximality theorem (B3.17, Q2).
5. **Limits and flows.** Selection from averages to points (Q1), escape classification (Q3) and the aperture, damping and heat flows live in other programmes (ACS, ADR, ACCE). Their positive-side and spectral-side readings are APD questions: averaged positivity is a statement about the spectral measure on height windows, and escape states are spectral profiles of the cofactor Gram.

- **Phenomenon to explain.** Arithmetic sources sit on the boundary between dominance (provable) and cancellation (unproved). On the boundary line the capacity is computed: `⌊k/2⌋` zero pairs per pole of order `k`. For inserted interior zeros it is computed: one net unit per pole unit. For ζ's own interior zeros it is unknown. The extended theory should explain why ζ, and not its relaxations, has interior capacity zero as a controlling parameter crosses the boundary: rate `σ → 0`, aperture `A → ∞`, heat `λ → 0`, damping `ε → 0`, window `H → 0`, or a carrier growing to the whole source.

### 4.3 Criteria the extended theory must meet

APD's contribution standard applies unchanged. The rows below add what the B-tier obstacles require beyond it.

| Criterion | Test against the corpus |
|---|---|
| **Selectivity** | Distinguishes ζ from the whole battery (W1): the pole-order-2 real stray and refunded quartet, the pole-order-3 and strip-pole quartets, over-regular Beurling systems, twisted boundary systems, the golden curve, `Γ_ℝ^d` solutions, signed self-dual combinations. Survives every single-node perturbation `Λ + δ·δ_m`. |
| **Joint use of invariants** | Uses coefficient positivity, the functional equation, the simple pole and strip holomorphy together; each proper subset has countermodels. |
| **Sees more than pole order** | Pole order budgets only inserted zeros; a mechanism that reaches ζ's own zeros must read oscillation, not just the divisor at `s = 1`. |
| **Leaves the exhausted classes** | Not single-channel sharp-stable positivity; not a finite or height-coupled multiplicative certificate; not linear in the coefficient or prime measure; not a pole count. |
| **Not depth-homogeneous** | Contains a term that does not scale with its amplification: a fixed base loss or a Riemann–Roch count. |
| **Non-circularity** | No interface field or premise contains the conclusion; the object is constructed before its sign; zero-free-region transfers are not forcing. |
| **Uniformity across limits** | Tails paid in a graph topology; the blind ideal stays closed and every jet visible; closure-based completions lose payment (golden payment domain, origin-`L²`). Aperture, height, rank, damping and window controlled together. |
| **Positivity–faithfulness separation** | RH from trace-bounded data; simplicity a separate output. |
| **Calibration** | Reproduces the boundary forcing law and capacity `⌊k/2⌋`, the exact Fejér barrier, dlVP optimality for its input, the `κ²` collar sparsity, `κ = 1` rigidity, positive-measure rigidity, the conservation identity, and Weil's theorem for curves with budget `2g`. |
| **New partial results** | Results that are not zero-free strips: short-window averaged positivity (Q1), non-blind coupled positivity (Q2), escape classification (Q3), an interior capacity bound for some infinite class of systems not built by deformation. |

### 4.4 Questions it must answer

Questions 2, 5 and 8 are on APD's agenda (its third forcing instance, integer budgets in the strip, spectral synthesis). Questions 1, 3 and 4 are the extensions of §4.2. Questions 6, 7, 9 and 10 belong to the programmes that own the limits and the geometry.

1. **What pays ζ's own zeros?** Pole order pays inserted zeros. What positive structure measures the oscillatory payment of ζ's own zeros, and does it carry a capacity?
2. **What positive structure on the strip extends the boundary divisor?** On `Re s = 1` the divisor is positive definite with capacity `⌊k/2⌋`. Which interior object has that role, and is it a capacity for oscillation rather than for pole charge?
3. **Which coupled scale carriers are positive and not blind?** Is there a maximality theorem for multi-channel carriers, or a carrier that escapes it?
4. **What is the base?** Which coefficient systems over `Spec ℤ` have nonnegative even tensor powers and a computable pole part, and does ζ sit inside one?
5. **How can the invariants be used nonlinearly?** What quadratic or logarithmic inequality uses positivity, the functional equation, the pole and strip holomorphy at once?
6. **How does an average become a point?** What selection principle passes from height averages to zero ordinates despite syndetic phase recurrence?
7. **How does blindness propagate under the flows?** What is the sign of the arithmetic beta function, and what keeps the ground energy positive along the prime-threshold ladder?
8. **What is the right completion?** The natural Fréchet topology closes the blind ideal; is the span of critical jets dense there, and which graph topology controls actual tails?
9. **What replaces the ample class and the ring of correspondences of `C × C`?**
10. **How are shared resources paid?** What nonlocal calculus pays frustrated prime incidences from one budget?

### 4.5 Tools it would develop

APD has built the Fejér-tent pairing, Hamburger rigidity for measures, lattice Herglotz–Bochner and Kronecker push-forward, induction from subgroups, sign-character classification, Bohr projection onto fibres, the quantum-budget calculus and the critical-jet topology. The tools below are not yet in it.

- **Capacity calculus.** Positive-definite and Herglotz inequalities bounding zero charge by pole charge, generalizing `boundary_zero_order_le`, the capacity classification, `collective_half_pole_interior_forcing` and the conservation identity, together with an oscillatory capacity for zeros not created by deformation.
- **Coupled positivity.** Positivity theorems for multi-channel Weil and Meyer forms and the maximality theorems that delimit them.
- **Base constructions.** Tensor-power positivity for coefficient systems over a base, with pole parts computed by invariants, in the shape of Deligne's argument.
- **Nonlinear rigidity.** Stability theory for the theta law beyond sublinear-defect Hamburger stability, measuring how far a positive measure with an approximate law lies from integer counting in norms that see the logarithm of the transform.
- **Growth-to-forcing renormalization.** The scalar law `√A + √(Gη) < √B` with its caps, lifted to an operator statement in which growth and positivity interact beyond a single comparison.
- **Arithmetic beta functions.** Signed flux formulas for the aperture, damping and heat flows.
- **Graph-topology completions and spectral synthesis** for the blind ideal and for cofactor modules.
- **Short-window selection lemmas** from density information to individual heights.
- **Escape-state classification** for cyclic critical-Wiener modules through their spectral profiles.
- **An arithmetic Stepanov method**: auxiliary sections over `ℤ` whose forced vanishing bounds spectral counts (a characteristic-zero shifted-subgroup Stepanov lemma exists in `HTGeometry`).
- **A nonlocal budget calculus** for frustrated signed incidence.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | Arithmetic Poisson pairs (prime and zero measures with Gamma and pole completion); completed positive systems graded by pole order and degree; boundary divisors and their capacities; relative deformations with inserted, removed and refunded zeros; coefficient systems over a base and their tensor powers; receivers; carriers, the maximal blind ideal and its sub-carriers; coupled scale channels and tensor sources; flows and beta functions; shells and collars; cofactor modules with paid ideals, hulls, spectral profiles and escape states; Meyer cohomology with jets and positive degrees; scaling surfaces with sections and `h⁰`; orbits, families and indices. |
| **Language** | It must distinguish: equality, receiver equivalence and directional transfer; source and receiver; signed energy and absolute majorants; linear, quadratic and logarithmic dependence on the source; single-channel and coupled positivity; height channels and scale channels; blind and faithful; inserted and intrinsic zeros; dominated and oscillatory payment; boundary and interior capacity; relative and absolute budgets; finite, countable and uniform limits; graph topology and closure; distinct zeros, multiplicity and multiplicity squared; algebraic and bounded inverses; forced, imported and transferred regions; depth-homogeneous and base-anchored gains. |
| **Mechanisms to discover** | A **capacity law for oscillation**: a positive structure bounding the interior zero charge of ζ itself. A **coupled forcing law**: positivity on several scale channels places the source in the closure of the blind ideal. A **base law**: a fixed loss over a base that vanishes under tensor roots. A **selection law**: averages become points. A **quantization law**: an interior integer charge with a sub-unit bound is zero. A **payment law**: one nonlocal budget pays every frustrated cost. |
| **First milestones** | (1) Averaged positivity on windows `H = Γ^θ`, `θ < 1` (Q1). (2) A coupled scale-side positivity theorem or a coupled maximality theorem (Q2). (3) The escape classification through the cofactor spectral identity (Q3). (4) The depth-homogeneity law as a theorem for each tested class (W8), with its positive survivors. (5) The capacity laws in one statement and the conservation identity for infinite corrections (W6(vii), (ix)). (6) The bare-FE form of positive-measure rigidity, then a quantitative stability theorem for the theta law in a logarithmic norm. (7) A candidate base: one coefficient system over `Spec ℤ` with nonnegative even tensor powers, tested against the over-regular Beurling countermodels. |

Each milestone is a theorem of a type the corpus does not yet contain: a capacity, coupled-positivity, selection, escape or base statement rather than a blindness statement. Under APD's standard each must name its positive side, spectral side, gap and integer. If several succeed, APD's third forcing instance has its first pieces. If they fail, each failure is a sharp no-go that narrows where a forcing law could be.
