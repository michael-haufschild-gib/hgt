# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-25, corpus `eb175d946` plus the working tree of that day. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](hard-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2510-refresh/`. Nothing was compiled.

## 0. The frontier in seven statements

1. **Single-channel quadratic positivity can only certify blindness.** Every sharp-stable positive convolution ideal of the Meyer source lies in the maximal blind ideal, the sources whose Mellin transform vanishes at every off-line zero (`isGreatest_meyerSharpPositiveIdeal`). Every scale-shift-invariant Weil-nonnegative test space is blind. Every other unconditional positivity theorem in the corpus is likewise positivity on a blind carrier.
2. **Multiplicative positivity is exhausted below RH strength.** On the boundary line the theory is complete. The boundary divisor of a positive Euler product is positive definite, and four invariants force `D = δ₀`, each one necessary (`boundary_forcing_law`). In the interior, positivity buys exactly the width `(√B − √A)²/G` paid by the growth input `G` (`exclusion_iff`). Every finite positive certificate, with any number of frequencies, primes or harmonics, is capped by `(3 − 2√2)/(2L)` (`multiFrequency_width_cap`), and a multi-channel certificate decomposes into one-channel problems on its rational fibres.
3. **No route has a rung between Vinogradov–Korobov and quasi-RH.** Every graded cancellation receiver, including every power improvement in the Vaughan picture, has a fixed zero-free strip as its first gain. So does multiplicative forcing.
4. **The invariants determine ζ, and each relaxation breaks the characterization.** A nonnegative measure on `[1, ∞)` with Riemann's degree-one theta law is a multiple of integer counting measure (`measure_eq_of_measureTheta_relation`). Systems with `Λ ≥ 0` and the exact functional equation can have off-line zeros at pole order 2 (a real pair), at pole order 3 (a complex quartet), or with poles of the completion inside the strip. For finite corrections the pole order is a zero budget: `ord₁F − 1` equals the inserted multiplicity, and a complex off-line quartet costs two units.
5. **Positivity is proved on average beyond the square-root threshold, not at points.** Averaged Weil positivity holds at aperture `κ₀ log Γ` on `[Γ, 2Γ]`, with subpower coercivity up to prime support `Γ^{4/3}`. The main term is the local critical-zero weight. The open step is selection: passing to individual heights.
6. **Faithfulness costs simplicity only through operator-norm carriers.** The maximal trace-bounded carrier keeps every critical jet and reaches RH alone; the faithful-degree, Hilbert–Schmidt and bounded-orbit carriers need RH plus simple zeros.
7. **Cofactor escape has one surviving explicit model.** At every subcritical damping some actual limit has `K_pp ≥ p^{2ε−2} > 0`. The kernel family is a singleton or a continuum, and augmentation cannot be the only escape state. White noise satisfies every proved constraint; whether it survives depends on whether the paid ideal is nonzero on escape.

## 1. Just work

Known mathematics suffices for each item. None crosses a wall.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Status-record synchronization | Keep the frontier map and catalogue aligned with the source as modules land, including the scope of each premise and the [S] labels. | Every status sentence matches a Lean statement. |
| **W2** | Certificate replacement | Replace `native_decide` in `RHTower/PrimeArchThetaFirstAtomHighOrderMomentBounds.lean` (PA order-24 quadrature) and `HTGeometry/MilnorKTwoSteinbergSurjective.lean` with kernel-checked arithmetic. | No trusted-computation tactic remains in the project packages. |
| **W3** | Selectivity battery | Test every candidate mechanism against the complete battery. Boundary and invariant models: pole-order-2 real stray, pole-order-3 quartet, strip-pole quartet, over-regular Beurling, double-pole and periodic-pole boundary systems. Curve and signed models: golden curve, `Γ_ℝ^d` solutions, signed self-dual combinations. Escape model: white noise. | Each candidate records which model defeats it, or that none does. |
| **W4** | Finite identities and certificates | Gram, Hausdorff, Hankel and Jensen blocks; finite heat transforms; finite schedules, histories and ledgers; finite Robin and Li checks; finite JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W5** | Premise checks for specified sources | Regularity, support, decay, cutoff and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources). | The hypotheses of an existing transfer are discharged. |
| **W6** | Transport of proved inputs | Width functor, RW↔SZ↔CHMD, HF→AIP, Weil margin→heat window, graded Sobolev floors, with every quantifier kept. | Each conclusion stated at its true strength. |
| **W7** | Certified finite extensions and constants | Push the pointwise windows beyond `3/10`, `181/500` and `(log 2+1/50)/2`; make `κ₀, c₀, C₀, Γ₀` and `R₀, T(λ)` explicit. | Certified finite-aperture theorems. |
| **W8** | Corollary assembly | (i) An averaged bounded-energy statement for WL from the high-zero tail and the filtered deficit. (ii) One rate dictionary for RW, SRT and ACS through `groundRate = polarRate`. (iii) The explicit LA/WD residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. (iv) ACS effectivity as exhaustion: Bézout on the full cone ⇔ maximal blind ideal = ⊤ ⇔ RH. (v) The bare-functional-equation form of positive-measure rigidity: derive the strip-decay premise from finite order and absolute convergence by Phragmén–Lindelöf. (vi) Replace the imported `c/(log|t|)^9` collar in the harmonic module by the MPG dlVP calibration. (vii) Extend the pole-order budget from finite to general reflection-antisymmetric corrections. | Each statement proved from existing theorems. |
| **W9** | Integration and audit | Integrate the modules the frontier map marks [S] (Vaughan endpoint and rate leaves, discrete Beurling rigidity, the beyond-linear-window prime channel). Then run an authorized axiom audit of route receivers and capstones. | Labels match the source; audit clean or findings recorded. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses its receiver.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy, a one-sided lag or Abel moment, the history floor, the regularized abscissa `1/2`, the JAS half-power budget, Mertens at square root, the late-lag sign. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Cofinal admission as `ε ↓ 0`; a Báez–Duarte residual → 0; signed interior Vaughan energy; exclusion of fixed-origin cofactor escape. | PM, CTF, BVI, PW-B |
| **B1.3** | **Complete Weil positivity at every aperture.** Low and mixed sectors with Gamma, both polar terms and one shared budget. Equivalent forms: the nodal inequality, positive Suzuki first variation, odd capacity, the one-shift reflected collar, global allocation, the `O(L)` ceiling, Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS |
| **B1.4** | **Selection.** From averaged or almost-all-height statements to every height, in particular zero ordinates. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Coefficient positivity on the bounded-height × small-heat region (de Bruijn–Newman `Λ ≤ 0`); all-rank Hankel positivity at one time; both literal heat grids; rank-uniform Schur decay; the Newton interior margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaustion of the maximal blind ideal by an input outside single-channel sharp-stable positivity. Faces: Ward cap vanishing; the integer sub-unit trace residual; renewal boundary orientation; source effectivity; a stabilization weld; pre-divisor compactness; a descending potential; a centered Ising limit; a lossless nonlocal port; a certificate stream. | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** Cofinal contrast equality (BSY); the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; the global index `D < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** A faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; exhaustion of the bounded-orbit carrier. | ACS/Meyer faithful branch |
| **B1.9** | **Absolute pole-order budget.** For positive degree-one systems with Riemann's functional equation and entire completion, the off-line zero multiplicity (counted by frequency pairs) is at most `ord₁F − 1`. At pole order one this is RH, since rigidity (under its growth premises) makes the system ζ. Proved for finite corrections of ζ, with sharp models at orders 2 and 3. | ACS, HF, APD, all candidates |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | First rung of every graded cancellation receiver (WL, PBM, JAS, MC/BVI bands and short windows, all Vaughan power improvements, RW/ACS graded floors, DR) and of multiplicative forcing. |
| **B2.2** | Finite off-line index. | HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations (B1.8). |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity beyond `α = 2/3`; the filtered deficit; short-window selection (Q1). |
| **B2.5** | At least `3/4` of the zeros on the critical line. | TTPC: signed coalescent surplus `β ≤ 1/18`. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ` (Chowla/Elliott with rates). | MC anti-alignment; SSA constants; BVI rows. |
| **B2.7** | Hardy–Littlewood prime-pair correlations uniform near the square-root band. | TTPC surplus; short-window selection. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | The KKL horizon (LA/WD residual size); the growth input of multiplicative forcing, the only source of interior gain (statement 2 of §0). |
| **B2.9** | Better de Bruijn–Newman upper bounds. | Shrinks the B1.5 region; corpus has `Λ < 1/8`. |

### 2.3 Tier B3: open problems isolated by this research

No solution is known; none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | Physical-`L²` rate equality `polarRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2`; form-norm rates equal `Δ`; bounded local off-line depth suffices. |
| **B3.2** | Escape-state classification of actual cofactor limits. | Record-minimum floor `K_pp ≥ p^{2ε−2}`; singleton-or-continuum; contraction calculus; rank-one sign law; augmentation cannot be the only state; white noise survives. Decisive sub-question: B3.16. |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction in the receiver norm. | Only algebraic injectivity; cofactor-graph closedness ⇔ a uniform estimate; in the golden model payment is nonclosed and only total evaluation is continuous. |
| **B3.4** | A limit topology for the maximal blind ideal. | The ideal is algebraic and complete as a carrier; the origin-`L²` completion is excluded; the payment-domain model shows closure loses payment, so the topology must be a graph topology. |
| **B3.5** | Surface section law: couple the base theta `h⁰` to test components. | Base `h⁰` RR and Mellin; Boolean counts and finite readings cannot pay; no theorem of the square for the Hecke graphs of `ℤ`. |
| **B3.6** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound `e^{−a}[ψ(e^{2c}) − ψ(e^{2a})]·mass`; frozen finite families fail. |
| **B3.7** | Short-window averaged positivity: the least `H(Γ)` for which averaged Weil positivity holds on `[Γ, Γ+H]`. | `H = Γ` proved; the mechanism is zero-density driven. |
| **B3.8** | A nonlocal shared-budget calculus; quantitative cofinal two-tower saving. | Frustration and descent laws exact; fixed-box gaps proved. |
| **B3.9** | Arithmetic input on the residual heat region; source-selective cofactor repair. | Model geometry complete; no universal positive multiplier. |
| **B3.10** | Compatible oriented families; quantitative global-index bounds. | Common-endpoint classification; spline-orbit index ≤ 1 ⇔ RH. |
| **B3.11** | Sub-half-damping signed control of the size-cutoff forward interior. | Exterior paid; `ε = 1/2` endpoint bounded for every squarefree support; integer local exponents below half. |
| **B3.12** | Order-uniform PA thresholds; decoupling rank from time (TH, HCF). | Fixed-order thresholds; coupled windows from Weil margins. |
| **B3.13** | Sharp successor constants: the complex floor in `[−1/2, −1/3]`; zero-defect signs beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`, both exact. |
| B3.14 | *Closed.* Interior multiplicative forcing beyond growth input by multi-channel finite certificates. | Excluded: `multiFrequency_width_cap`. |
| B3.15 | *Closed.* Completeness of ζ's invariants. | Settled: positive-measure rigidity plus the relaxation models. |
| **B3.16** | **Is the paid ideal of `μ_ε` nonzero on escape?** | Paid ideal = ⊤ ⇔ admission. Escape gives paid ideal ⊆ annihilator. No nonzero paid kernel is known unconditionally. The direct construction `k = n^{−ε} ∗ h` with `h` finitely supported (so that `k ∗ μ_ε = h` is trivially paid) never gives a critical-Wiener kernel; this follows from an elementary divisor-density argument and is not a corpus theorem. A positive answer excludes every faithful escape module, white noise and reset-origin mixtures included. |
| **B3.17** | **Coupled positivity outside the maximality class.** An unconditional positivity theorem on a carrier that is not a sharp-stable convolution ideal (a cone that is not `♯`-stable, a coupled two-channel form such as `ζ(s)ζ(s+iτ)`, a tensor source), whose carrier is not off-line blind. Alternatively, a maximality theorem for all such carriers. | Single-channel class exhausted; finite multiplicative class capped; no coupled quadratic carrier has been studied. |

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier. A positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three families, each in its own currency.

**Settled questions.**

- Do ζ's invariants characterize it? Yes, and the characterization is sharp.
- Can finite positive multiplicative certificates force more than growth input pays? No.
- Can augmentation be the escape picture? Not as the unique state.

### Q1. Selection: how short can the averaging window be?

> *What is the shortest window `[Γ, Γ + H(Γ)]` on which unconditional averaged positivity of the complete Weil form at logarithmic aperture holds? In particular, does it hold for `H = Γ^θ` with some `θ < 1`?*

- **Why.** Positivity at every height is RH; positivity averaged over `[Γ, 2Γ]` is proved. Its main term is the local critical-zero weight, and off-line contributions are controlled by zero-density shell bounds. Shrinking the window is therefore a question about zero density in short windows, a classical theme with existing tools. Each intermediate `H` is a new kind of partial result: positivity at almost all heights in short windows, which is not a zero-free strip.
- **Tools.** Short-interval zero weights and the 30/13, Ingham–Huxley and Guth–Maynard density bounds in the corpus; the all-length Heath–Brown estimate; the phase-selective single-height law; the bad-frequency volume bound.
- **Outcomes.** A threshold `θ₀` with positivity for `θ > θ₀` supplies the first quantitative selection step for RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF, ACS, SRT and WL together. A proof that no `θ < 1` follows from density inputs alone identifies the missing input as short-window prime-pair correlation (B2.7).

### Q2. Coupled positivity: does any positive carrier escape blindness?

> *Is there an unconditional positivity theorem for the complete Weil (or Meyer trace) form on a carrier outside the single-channel sharp-stable class whose carrier is not contained in the maximal blind ideal? Candidates: convolution cones that are not `♯`-stable; the coupled form of two dilated channels `ζ(s)ζ(s+iτ)`; tensor or Rankin–Selberg-type sources. Or does the maximality theorem extend to all such carriers?*

- **Why.** Three positivity mechanisms are now exhausted below RH strength:
  - single-channel quadratic positivity, by the maximality theorem;
  - finite multiplicative positivity, by the growth caps;
  - linear rigidity, which determines ζ but is linear in the coefficient measure, while zero location is not.

  Coupled quadratic positivity is the only positivity class the corpus has not mapped. The maximality proof needs both sharp stability and convolution closure: it turns an off-line value into the negative-trace packet `u − u♯` inside the carrier. A carrier lacking either property avoids that proof. The multiplicative analogue is a warning: coupled positive certificates split into one-channel problems on rational fibres, so coupling bought nothing there. A coupled quadratic carrier is interesting only if it does not split in the same way.
- **Selectivity test.** Any candidate must fail on the pole-order-2 real-stray model, the pole-order-3 quartet model and the strip-pole model, which keep `Λ ≥ 0` and the exact functional equation (W3). A mechanism that does not see pole order cannot be selective.
- **Outcomes.** A non-blind positive coupled carrier would be the first positivity theorem in the corpus that is not a blindness certificate, and a candidate forcing input for B1.6. A maximality theorem for coupled carriers would extend the exhaustion picture to all quadratic positivity of this type and leave only pole-order-sensitive or non-quadratic mechanisms.
- **Tools.** The maximality proof and its negative-trace packets; the harmonic coupling formula (`ζ(s+ikt)` channels, coupled off-line ceiling); MPG boundary positive definiteness; the scale-stable family law; Rankin–Selberg structure of `Λ * Λ`.

### Q3. Escape: is the paid ideal nonzero on escape?

> *At a subcritical damping `ε` at which the receiver escapes, does the paid ideal of `μ_ε` contain a nonzero critical-Wiener kernel? More generally, which cyclic critical-Wiener modules satisfy every proved constraint on actual cofactor limits?*

- **Why.** Cancellation routes have no graded rung below quasi-RH; their only other handle is the escape alternative. White noise passes every proved test: PSD, sharp dilation, antipodality, horizon order and the record floor `1/p ≥ p^{2ε−2}`. It is faithful, and on escape the paid ideal annihilates the module. White noise survives exactly when the paid ideal can be zero.
- **Outcomes.**
  - *Nonzero paid ideal.* Every faithful module is excluded as a fixed-origin escape state: white noise, reset-origin mixtures, every admission-like module. Admission at `ε` becomes equivalent to the faithfulness of one actual limit, and record-minimum limits, with all diagonals positive, are the natural candidates.
  - *Zero paid ideal for some escaping `ε`.* The paid-ideal constraint is empty there. White noise is then a genuine abstract escape state, and escape exclusion needs new arithmetic input (coercivity, moving-boundary cost). B3.2 and B3.3 become concrete.

  A full positive answer to the general classification at every `ε` would be RH. The realistic targets are B3.16 and an explicit description of what an escape module must look like.
- **Tools.** The paid-graph identification; visible-pole constraints `ord k(ρ−ε) ≥ (ord ζ(ρ) − ord ζ(ρ−ε))₊`; unit transport; the contraction calculus; the record-minimum construction; the singleton-or-continuum law.

The three questions are the forcing problem in each family's currency: selection by height (Q1), positivity outside the blind class (Q2), escape exclusion (Q3).

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. What has changed is that the known mechanisms are now mapped with sharp limits.

- **Single-channel quadratic positivity certifies blindness.** Weil, Hodge and trace positivity on a single sharp-stable channel cannot leave the blind carrier (maximality).
- **Multiplicative positivity forces the boundary and nothing more without growth.** The boundary divisor is positive definite and four invariants force it to vanish off the origin. In the interior the certified width is `(√B − √A)²/G`, and no finite certificate beats the universal cap.
- **Linear rigidity determines ζ but does not see zeros.** Positivity, the functional equation and the simple pole fix the coefficient measure through linear constraints (the Fejér-tent squeeze). Zero location is a nonlinear (logarithmic) function of that measure. Each relaxation of the invariant set breaks the characterization, three of them with explicit off-line zeros, so a proof must use all invariants together and quantitatively.
- **Linear forcing in the logarithmic measure cannot isolate the line.** This is reasoning, not a corpus theorem. A linear functional of the prime measure `P` acts on zeros through an analytic transform. An analytic kernel that vanishes on the whole line `Re s = 1/2` and is positive off it does not exist: it would vanish identically. In the Hamburger squeeze the target set was discrete (the integers) and a nonnegative kernel (`sinc²`) could vanish on it exactly. For zeros the target set is a line, so forcing must be at least quadratic. Single-channel quadratic forcing is exhausted.
- **Pole order is the decisive invariant everywhere it has been tested.**
  - On the boundary, positive definiteness gives zero order ≤ pole order, and a zero at `u` forces a pole at `2u`.
  - In the interior, the finite-correction budget gives `ord₁F − 1` = inserted off-line multiplicity, with a complex quartet costing two units.
  - Pole-order rigidity: critical zeros force `κ = d` and `T = ζ^d`.

  RH is the statement that ζ, with budget zero, spends nothing.
- **Weil's proof for curves does not transfer.** It forces through the geometry of `C × C` (sections, ampleness, a ring of correspondences with a theorem of the square) and holds uniformly over a large family of curves. Over `Spec ℤ` the scaling and Meyer surfaces have Hodge index equivalent to RH, their Hecke graphs satisfy no theorem of the square, and in degree one the complete invariant set has a single member. A class-level theorem needs a family. Two candidates exist: the positive functional-equation class graded by pole order, where B1.9 would be the class theorem with RH as its base case, and higher degree, where pole-order rigidity ties `κ` to `d`.

The missing ingredient is a **forcing law of a new kind**. It must be quadratic or higher, coupled across channels, sensitive to pole order, quantitative across limits, and independent of the conclusion. No existing toolkit over number fields supplies one. If it exists, it will probably form a new field: a theory in which positive definiteness on the boundary line (the multiplicative shadow), Hodge positivity on the scaling surface (the quadratic shadow) and the pole budget are aspects of one structure on the critical strip.

### 4.2 Working name and subject

**Arithmetic forcing theory** (alternatively: *zero–pole budget geometry*). Subject: how the multiplicative structure of an arithmetic source budgets its off-line zeros against its pole, across scale, limit and completion. The multiplicative structure here means coefficient positivity, the functional equation, the simple pole and holomorphy of the completion.

- **Phenomenon to explain.** Arithmetic sources sit on the boundary between dominance (provable) and cancellation (unproved). The theory should explain why ζ, and not its relaxations, stays blind as a controlling parameter crosses that boundary: rate `σ → 0`, aperture `A → ∞`, heat `λ → 0`, damping `ε → 0`, window `H → 0`, or a carrier growing to the whole source.
- **Character.** It would combine four components.
  - A **budget calculus on the critical strip**: a positive-definite or Herglotz structure that extends the boundary divisor's positive definiteness into the strip. Zeros and poles act as charges, and positivity bounds zero charge by pole charge absolutely, not only for finite corrections.
  - **Coupled quadratic positivity**: Weil and Hodge forms on several channels at once (dilated channels, tensor and Rankin–Selberg sources), outside the single-channel class of the maximality theorem.
  - A **renormalization theory of positivity**: flows in aperture, damping, heat and window, with arithmetic beta functions (the prime-shell flux is the first computed), fixed points (blind carriers) and relevant directions (off-line zeros).
  - **Intersection theory with a ring of correspondences**: what replaces `ℤ[F]` and the theorem of the square over `Spec ℤ`.

### 4.3 Criteria it must meet

| Criterion | Test against the corpus |
|---|---|
| **Selectivity** | Distinguishes ζ from the whole battery (W3). It must fail on the pole-order-2 real stray, the pole-order-3 quartet and the strip-pole quartet, which keep `Λ ≥ 0` and the exact functional equation. It must also fail on over-regular Beurling systems, the double-pole and periodic-pole boundary systems, the golden curve, `Γ_ℝ^d` solutions and signed self-dual combinations. It must survive every single-node perturbation `Λ + δ·δ_m`. |
| **Joint use of invariants** | Uses coefficient positivity, the functional equation, the simple pole and strip holomorphy together; each alone or in proper subsets has countermodels. |
| **Leaves the exhausted classes** | Not single-channel sharp-stable positivity (maximality); not a finite positive multiplicative certificate (MPG cap); not linear in the coefficient or prime measure. |
| **Non-circularity** | No interface field or premise contains the conclusion; the object is constructed before its sign; zero-free-region transfers are not forcing. |
| **Uniformity across limits** | Tails paid in a graph topology that keeps the maximal blind ideal closed and every jet visible; closure-based completions lose payment (golden payment domain, origin-`L²`). Aperture, height, rank, damping and window controlled together. |
| **Positivity–faithfulness separation** | RH from trace-bounded data; simplicity a separate output. |
| **Calibration** | Reproduces the boundary forcing law with its necessity models, the exact Fejér barrier, dlVP optimality for its input, positive-measure rigidity, the finite pole budget and Weil's proof for curves (genus one: Hasse = degree positivity of `ℤ[F]`). |
| **New partial results** | Results that are not zero-free strips: short-window averaged positivity (Q1), non-blind coupled positivity (Q2), escape classification (Q3), an absolute budget inequality for some infinite class of corrections. |

### 4.4 Questions it must answer

1. **What positive structure on the strip extends the boundary divisor?** On `Re s = 1` the divisor is a positive-definite function. What object plays that role inside the strip, and does it carry an absolute zero–pole budget?
2. **How can the invariants be used nonlinearly?** Rigidity uses positivity, the functional equation and the pole linearly in the coefficient measure. What quadratic or logarithmic inequality uses all of them at once?
3. **Which coupled carriers are positive and not blind?** Is there a maximality theorem for two-channel carriers, or a coupled carrier that escapes it?
4. **What replaces growth input in the interior?** Finite certificates buy only what growth pays. Is there an infinite or coupled certificate that buys more, or is growth input (subconvexity, large values) the only possible source?
5. **How does blindness propagate under the flows?** What is the sign of the arithmetic beta function, and what keeps the ground energy above zero along the prime-threshold ladder?
6. **What is the right completion?** Which graph topology keeps the maximal blind ideal closed, makes the trace lower semicontinuous and controls actual tails?
7. **How does an average become a point?** What selection principle passes from height averages to zero ordinates despite syndetic phase recurrence?
8. **What replaces the ample class and the ring of correspondences of `C × C`?**
9. **How are shared resources paid?** What nonlocal calculus pays frustrated prime incidences from one budget?

### 4.5 Tools it would develop

- **Strip budget calculus.** Positive-definite or Herglotz inequalities on the strip bounding off-line zero charge by pole charge; generalizations of `boundary_zero_order_le`, `poleOrderBudget` and `pole_order_rigidity` to infinite corrections and to the absolute case.
- **Coupled positivity.** Positivity theorems for multi-channel Weil and Meyer forms, together with maximality theorems that delimit them.
- **Nonlinear rigidity.** Stability theory for the theta law beyond the sublinear-defect Hamburger stability, measuring how far a positive measure with an approximate law lies from integer counting, in norms that see the logarithm of the transform.
- **Growth-to-forcing renormalization.** The scalar law `√A + √(Gη) < √B` with its caps, lifted to an operator statement in which growth and positivity interact beyond a single comparison.
- **Arithmetic beta functions.** Signed flux formulas for the aperture, damping and heat flows.
- **Graph-topology completions** for the maximal blind ideal and for cofactor modules.
- **Short-window selection lemmas** from density information to individual heights.
- **Escape-state classification** for cyclic critical-Wiener modules under paid-ideal constraints.
- **An arithmetic Stepanov method**: auxiliary sections over `ℤ` whose forced vanishing bounds spectral counts (a characteristic-zero shifted-subgroup Stepanov lemma exists in `HTGeometry`).
- **A nonlocal budget calculus** for frustrated signed incidence.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | Arithmetic sources (coefficient and log measures with Gamma and pole completion); positive degree-one systems graded by pole order; boundary divisors and their strip extensions; receivers; carriers, the maximal blind ideal and its sub-carriers; coupled channels and tensor sources; flows and beta functions; shells and collars; cofactor modules with paid ideals, hulls and escape states; Meyer cohomology with jets and positive degrees; scaling surfaces with sections and `h⁰`; orbits, families and indices. |
| **Language** | It must distinguish: equality, receiver equivalence and directional transfer; source and receiver; signed energy and absolute majorants; linear, quadratic and logarithmic dependence on the source; single-channel and coupled positivity; blind and faithful; finite, countable and uniform limits; graph topology and closure; distinct zeros, multiplicity and multiplicity squared; algebraic and bounded inverses; forced, imported and transferred regions; dominance and critical regimes; relative and absolute budgets. |
| **Mechanisms to discover** | A **budget law**: pole order bounds off-line zero charge absolutely. A **coupled forcing law**: positivity on several channels places the source in the closure of the blind ideal. A **selection law**: averages become points. A **quantization law**: an interior integer charge with a sub-unit bound is zero. A **payment law**: one nonlocal budget pays every frustrated cost. |
| **First milestones** | (1) Averaged positivity on windows `H = Γ^θ`, `θ < 1` (Q1). (2) A coupled positivity theorem or a coupled maximality theorem (Q2). (3) A decision on the paid ideal at escape (Q3). (4) The pole-order budget for an infinite class of corrections, with its sharp models. (5) The bare-FE form of positive-measure rigidity (W8(v)), then a quantitative stability theorem for the theta law in a logarithmic norm. (6) The sign of the shell flux on one ladder step beyond `3/10` from a structural argument. |

Each milestone is a theorem of a type the corpus does not yet contain: a budget, coupled-positivity, selection or escape statement rather than a blindness statement. If several succeed, the field exists. If they fail, each failure is a sharp no-go that narrows where a forcing law could be.
