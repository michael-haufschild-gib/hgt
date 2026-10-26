# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-26, corpus `19b8caad1` with the working tree of that day. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](hard-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2610/working-log-v3.md`. Nothing was compiled. `[L]`, `[S]`, `[P]`, `[R]` as in the complete report.

## 0. The frontier in fourteen statements

1. **`ζ` has a positive form and an equivariant form, and RH says they are one form.** Weil's form `W` is Hecke equivariant for every zero configuration; its positivity is RH. The collided form `D(f) = Σ_ρ m_ρ|f̂(ρ)|²` is positive unconditionally; its Hecke equivariance is RH [S]. `Re W = D − Δ`, where the off-line defect `Δ` charges every off-line pair whatever its depth [L]. Over `𝔽_q` one form, the Rosati trace of a polarization, has both properties.
2. **Every unconditional positivity found is collided, isotropic, non-localizing, averaged, dominated, or below a horizon.** Kernel counts, coupled counts, escape Cauchy forms and `D` pair `ρ` with its conjugate `ρ̄`; Rosati positivity pairs `ρ` with its reflection `1 − ρ̄`, and only `W` computes that pairing. The explicit formula computes holomorphic sums `Σ H(ρ)`; `D` is not one.
3. **Multiplicative symmetry is hyperbolic exactly at off-line pairs, and elliptic localization inside correspondence-closed carriers is resonance.** A symmetric dilation acts elliptically at an off-line point only at scales `a` with `γ log a ∈ πℤ`: at most one prime, at the unknown height. The only reflection-compatible affine localizer of a pair is `σ_γ(s) = 1 + 2iγ − s`, the functional equation conjugated by the archimedean flow. Its even sector is positive at every pair and cannot exclude; its odd sector is negative at every pair and can.
4. **Elliptic localization has a price, and a gap remains [R].** Every off-axis twist is gauge charged. Twisted positivity of `ζ`'s form is a theorem only below the conductor horizon `e^a ≲ log γ/4`. The forcing half turns positivity on one odd-sector test at one ordinate into an off-line companion, but needs `e^a ≳ (log γ)^{1/(2δ)}`; for every depth `δ < 1/2` the two ranges are disjoint.
5. **Counting is the sign.** Over `ℤ` each of the following is RH: a section count with Riemann–Roch and Bézout; an effectivity function with the Riemann inequality and subquadratic growth in degree zero; a naive height for every integral Rosati form; a one-sided count `ψ(x) − x ≤ C√x log²x`; a fixed tensor loss; horizon torsion `ψ(N) = N + O(√N log²N)`. The effectivity function, the absence of abundant classes, naive heights, the fixed tensor loss and horizon torsion are proved to be one statement [S]. The base theta `h⁰` does not extend to the surface; the theta surface carries a polarization from counting, but it is the same on every fibre and selects nothing; lattice counts on the square collapse to boundary or determinant positivity.
6. **Hodge index splits into a local part that holds and a Lefschetz part that is RH.** At one prime, short windows are Weil positive; RH is positivity on `g − T_{p^m} g`, equivalently a one-sided inequality at one prime or at one shift.
7. **Multiplicative data see orbits, not the point; the first gauge charge is a twist and the second is not archimedean.** Finite multiplicative lattice forms are unitarily equivalent at the Euler and Liouville vacua [S]. The successor connection reads the prime phases from `2 → 3 → 4` [S]. On windows reading only the prime `2`, the Liouville twin is `ζ` at height `π/log 2` plus Gamma and pole corrections, and it is positive on every test with edge mass at most `1/1961`. No height flips the atoms at `2` and `3`; a twist approximating the Liouville vacuum on `{2, 3}` to within `ε` needs `|γ| ≥ log(1/(50ε))` [S].
8. **Every amplification over `ℤ` tested loses linearly, and twists are rate neutral.**
9. **No graded receiver has a rung between Vinogradov–Korobov and a fixed strip.** Escape is located exactly: the damped Möbius receiver escapes at `ε` iff zeros lie right of `1/2 + ε`, up to countably many dampings, and RH is admission at every damping.
10. **One-variable positivity is exhausted.** The κ = 1 completed class is `ℝ^× · ζ`. Real off-line pairs contract for free. A complex quartet contracts only against a real anchor, and a system carrying an anchored quartet has `κ ≥ 3`. No harmonic lift empties the deepest line (Fejér barrier); coupled completions vanish to even order on the real axis; the global conjugate collision has no analytic carrier.
11. **The coupled class is not rigid, and positivity is chiral [S].** At every critical-zero ordinate `γ`, a Bochner-positive splitting of the central double zero deforms `ζ(s)²ζ(s+iγ)ζ(s−iγ)` inside its class; collapsing a critical pair inward is never positive. What survives is a one-sided ceiling on the central vanishing order, which implies RH; its converse is open.
12. **Positivity holds on average and at almost every zero ordinate.** To exclude an individual zero the exceptional sets must lie below the zero spacing; a correspondence of length `L` resolves heights only at scale `1/L`.
13. **Escape classifies and never excludes.** Escape states of dominant configurations are phase kernels whose rank counts the dominant zeros; their forms are collided Cauchy forms, positive automatically; with an Abel weight the finite-height part of an escape state is read from the poles of the symbol on its abscissa line [S]. RH is positive gauge mass of every escape state.
14. **The archimedean–finite coupling never reaches the zeros as a positivity.** The successor is unipotent on polar fibres; Weil's extensions to `Aff(ℚ)` are a box over the critical zeros; the successor defect grows only like `|t|^{1−σ+η}` in the strip.

## 1. Just work

Known mathematics suffices for each item, and none crosses a wall. An item's outcome may be unknown; what is known is the method.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test every mechanism against:<br>• pole-order-2 and pole-order-3 relaxations, strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems;<br>• the golden datum (with its Beurling base axioms) and the complex fake;<br>• the Liouville twin, the `{2,3}`-flipped twin, sign-flipped and dominated twins, Haar-typical twists, Kronecker twists near the Liouville vacuum;<br>• height-coupled lifts, `W_β`-split members of `HeightCoupledSystem 2 1 1 γ`, Fejér-coupled systems;<br>• theta-surface fibres at characteristics `a ≠ 0`;<br>• white noise, reset-origin mixtures, translated-zero eigenstates, Abel atoms.<br><br>Calibrations to reproduce: κ = 1 collapse; `⌊k/2⌋` capacity; dlVP optimality and Fejér barrier; `2 : 1` real-anchor law and `κ ≥ 3` anchored floor; Weil for curves with budget `2g`; exterior-count purity; `ℙ¹ × ℙ¹` effectivity. | Each mechanism records which model defeats it, its local type at off-line pairs, whether its positivity is collided or Rosati, and whether its counting polarization is fibre-selective. |
| **W2** | Finite identities and certificates | Gram, Hausdorff, Hankel, Jensen blocks; finite heat transforms; schedules and histories; finite Robin, Li, JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W3** | Premise checks | Regularity, support, decay and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources, twisted detectors). | Hypotheses of existing transfers discharged. |
| **W4** | Transport of proved inputs | Width functor; RW↔SZ↔CHMD; HF→AIP; Weil margin → heat window. Restate in RW, SZ, CHMD, EWU, OWU, ACT, AIP, HF coordinates: the short-window averaged theorem, the off-line-field theorem, the zero-ordinate theorem, the short-cycle split, the conductor horizon and the forcing half. Restate the effectivity currencies in HF and ACS coordinates. | Each conclusion stated at its true strength. |
| **W5** | Certified extensions and constants | Push the pointwise windows beyond `3/10`, `181/500`, `(log 2 + 1/50)/2`. Make explicit `κ₀, C₀, Γ₀`, `sharpCollarConst κ`, `R₀`, `T(λ)` and the constant `C` of the conductor horizon. | Certified finite-aperture theorems. |
| **W6** | Short windows to the classical range | Replace `Γ^{99/100}` by `Γ^{1/2+ε}` in the averaged, off-line-field, zero-ordinate and positive-measure theorems and in WL's filtered deficit, using Selberg's near-line density on windows `T^{1/2+ε}` [R]. | The four theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W7** | Corollary assembly | (i) An averaged bounded-energy statement for WL.<br>(ii) One rate dictionary for RW, SRT, ACS through `groundRate = polarRate`.<br>(iii) The explicit LA/WD residual region.<br>(v) Replace the imported `c/(log\|t\|)^9` collar of the harmonic module by the MPG or SBWF calibration.<br>(vi) Conservation for infinite reflection-antisymmetric corrections.<br>(vii) One capacity law: boundary, collar, gauge, family.<br>(viii) The upper direction of the energy-rate law `limsup log E_ε(T)/log T = max(0, 2(Θ − ε) − 1)`, from `1/ζ(s) = O(\|t\|^η)` in a zero-free half-plane; the lower direction is `not_energy_le_rpow_of_uncancelled_zero`.<br>(x) **The forcing-gap theorem**: for every `δ < 1/2` no aperture satisfies both the conductor-horizon hypothesis and the companion-forcing inequality `hbig`, with explicit thresholds.<br>(xi) **The ceiling at zero-free ordinates**: if `ξ(1/2 ± iγ) ≠ 0`, `CentralVanishingCeiling γ` ⇔ every member of `HeightCoupledSystem 2 1 1 γ` has `Λ(1/2) ≠ 0`; and two-sided rigidity can hold at `γ` only if `γ` is not a critical-zero ordinate.<br>(xii) **One collided-positivity theorem**: kernel counts, coupled counts, escape Cauchy forms and `D` as instances of one conjugate-pairing form, with its Hecke transformation law. | Each statement proved from existing theorems. |
| **W8** | The first gauge-charged window, edge problem | Compute `inf W_flip(F)/∫F²` over odd real `C²` tests on `[−181/500, 181/500]` with edge mass `> ∫F²/1961` in `E = {log 2 − A ≤ \|x\| ≤ A}`, `flip` = `Λ` with `Λ(2) ↦ −log 2`; by `liouville_window_eq_zeta_twisted` this is `ζ`'s twisted form at `γ₂ = π/log 2` plus explicit corrections. Close by a negative witness or a kernel-checked certificate. | A theorem: the odd window separates `ζ` from the twin, or it does not. |
| **W9** | Depth homogeneity, remaining classes | The loss law for `k`-level forms and Følner coupling (harmonic twists are done: rate neutral). | One theorem per class. |
| **W10** | Range-limited growth inputs | State the VK step as a `δ`-range instance of `exclusion_iff`. | VK as an instance of the growth-to-forcing law. |
| **W11** | Contraction calculus, last items | (i) Whether a complex quartet at depth `1/4 < a < 1/2` contracts at `Δκ = 1` with the boundary pole as anchor, or needs `Δκ = 2`.<br>(ii) A minimum-tax theorem for arbitrary finite rational multipliers, not only zero-planting ones. | Each statement in Lean as a calibration. |
| **W12** | Integration of working sources | BGG (six modules, umbrella), `HeckeInvarianceOfTheCollidedPolarizationIsRH`, `TheBaseAxioms` (five currencies), `TheAbelEscapeStateIsTheBoundaryMeasureOfTheSymbol`, the wide-window prime channel. | Each statement at its stated strength in an umbrella. |
| **W13** | The first non-archimedean twin | Find the least aperture at which the `{2,3}`-flipped weight (`Λ(2), Λ(3)` negated, prime powers by `λ`) fails Weil positivity, by an explicit negative test; compare with certified positivity of `ζ` there (W5). | The aperture `A₂₃` with a witness, and the status of `ζ` at `A₂₃`. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses it.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy; a one-sided lag or Abel moment; the history floor; the regularized abscissa `1/2`; the JAS half-power budget; Mertens at square root; the late-lag sign; the one-sided count `ψ(x) − x ≤ C√x log²x`; typicality of the gauge point `0` (for `Λ`, after subtracting the pole). | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Admission at every damping; subpower receiver energy; positive gauge mass of every escape state; signed control of the long-modulus quadrature; a Báez–Duarte residual → 0. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Positivity of the equivariant form.** `W ≥ 0` at all apertures with Gamma and polar terms. Equivalent forms: the one-sided Weil inequality for `T_{p^m}` on short cycles at one prime; one shift; sufficiency of the free budget; Rosati positivity; the nodal inequality; positive Suzuki first variation; odd capacity; global allocation; Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection.** From short-window averages and almost every zero ordinate, for nonnegative tests of bounded shape, to every height, every signed test, every aperture. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Residual heat region; all-rank Hankel positivity at one time; both heat grids; rank-uniform Schur decay; the Newton margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaust the maximal blind ideal with an input outside the exhausted classes (invariant, non-localizing, nonnegative-test, multiplicative, one-variable, collided, twisted-below-horizon, counting-equivalent). The input must localize by a non-multiplicative operation, carry elliptic local type or a polarization, use sign-changing data, and be computed rather than posited. | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** BSY contrast equality; the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; `D < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** Faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve. | ACS/Meyer faithful branch |
| **B1.9** | **Counting forms of the sign.** An arithmetic effectivity function on the scaling surface; the absence of abundant classes; a naive height for every integral Rosati form; a fixed tensor loss for the spline orbit correlation; a section count with RR and Bézout; horizon torsion at `√N` precision. All but the section count are proved to be one statement [S]; the section count is separately RH [L]. | HF, ACS, AOG, SRT, WL |
| **B1.11** | **Equivariance of the positive form [S].** Hecke invariance of the collided form `D` on every compact real `C²` test; equivalently `Δ ≡ 0`; equivalently `W = D`. | HF, ACS, PM |
| **B1.12** | **The central vanishing ceiling [S].** `ord_{1/2}Λ ≤ ord_{1/2}Λ_γ` for every member of `HeightCoupledSystem 2 1 1 γ`, every `γ ≠ 0`. It implies RH; whether RH implies it is open. | ACS, SBWF |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | Every graded receiver; admission at fixed damping; energy growth; one-sided Lefschetz bounds; multiplicative forcing. |
| **B2.2** | Finite off-line index. | HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations (B1.8). |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity at larger aperture; the filtered deficit; the Hecke defect of `D` (B3.33); exceptional sets of the forcing gap (B3.32). |
| **B2.5** | At least `3/4` of the zeros on the line. | TTPC: surplus `β ≤ 1/18` at the gauge point. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ`. | MC anti-alignment; SSA constants. |
| **B2.7** | Uniform Hardy–Littlewood prime-pair correlations near the square-root band. | TTPC; near-incidence beyond the threshold; successor-charged positivity (B3.26). |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | KKL horizon; growth input of multiplicative positivity. |
| **B2.9** | Better de Bruijn–Newman bounds. | Shrinks the B1.5 region. |
| **B2.10** | Near-line density on windows shorter than `T^{1/2}`. | Averaged positivity on windows `Γ^θ`, `θ < 1/2` (B3.7). |

### 2.3 Tier B3: open problems isolated by this research

No solution is known, and none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | Physical-`L²` rate equality `polarRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2`; bounded local off-line depth suffices. |
| **B3.2** | **Escape completeness for `ζ`.** (b) Summability of the residues of the translated-zero configuration; (c) the escape states when the real parts of the zeros accumulate at an unattained supremum. | Phase-kernel classification for every summable dominant configuration [L]; the dominant-split criterion [L]; the escape alternative [L]; with Abel weights the finite-height part is determined by the poles on the abscissa line without growth bounds between zeros, the rest of the mass escapes to infinite height [S]. Completeness classifies; it does not exclude. |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction. | Algebraic injectivity; kernel `ℝ q_ε`; closedness ⇔ a uniform estimate. |
| **B3.6** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound. |
| **B3.7** | Averaged positivity on windows `Γ^θ` below the classical range. | `θ = 99/100` proved; `θ > 1/2` is W6. |
| **B3.8** | A nonlocal shared-budget calculus. | Frustration and descent laws exact; the AIP diagonal reserve cancels on the polar-neutral hyperplane [S]; log-cell remainders bounded by a biarithmetic Sobolev energy [S]. |
| **B3.9** | Arithmetic input on the residual heat region. | Model geometry complete. |
| **B3.10** | Compatible oriented families. | Spline-orbit index ≤ 1 ⇔ RH. |
| **B3.11** | Sub-half-damping signed control of the forward interior. | Exterior paid; `ε = 1/2` bounded. |
| **B3.12** | Order-uniform PA thresholds; decoupling rank from time. | Fixed-order thresholds. |
| **B3.13** | Sharp successor constants beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`. |
| **B3.16** | Is the paid ideal nonzero on escape? | Would exclude white noise, not translated-zero states. |
| **B3.18** | Equality case of collar capacity at even `κ`. | Odd `κ` sharp. |
| **B3.20** | Signed near-coincidence cancellation at one height beyond aperture `½ log Γ`. | Single-height phase-selective law. |
| **B3.24** | An unconditional nontrivial estimate for a gauge-charged statistic of `μ` or `Λ` at the point `0` beyond the square-root threshold. | Haar-typical twists meet every budget; the Möbius boundary separates the twin at PNT strength. |
| **B3.26** | **The non-archimedean gauge charge.** Does unconditional positivity of `ζ` separate it from gauge twins that are not height twists (first: the `{2,3}` flip), with a margin that survives aperture growth against the `e^A` cost of the off-line field? | First charge is a twist; edge reduction (W8); second charge not archimedean; Catalan repulsion [S]; the successor connection reconstructs `ω(2), ω(3)` on `2 → 3 → 4` [S]; finite multiplicative lattice forms are blind [S]. |
| **B3.28** | **The Rankin–Selberg field** for the actual source `Λ ⋆ Λ`. | Finite polar sources: `Re E_j > 0` at the deepest off-line point. |
| **B3.29** | Lower bounds or arithmetic use of the successor defect `D_Λ` on vertical lines. | `\|D_Λ(s)\| ≤ C_{σ,η}(\|s\|+1)^{1−σ+η}`; real-axis lower bound sharp up to `2^{1+σ}`. |
| **B3.30** | **Stepanov auxiliaries outside the one-prime Hecke algebra.** Auxiliary sections over `ℤ` whose forced vanishing bounds a count. | The natural output (a one-sided count) is RH; Hecke auxiliaries kill only critical symbols; univariate integer polynomials on `[0,1]` give Nair and stop below PNT [R]. |
| **B3.32** | **The elliptic forcing gap.** Is `ζ`'s form nonnegative on the `σ_{γ₀}`-odd twisted detector at the ordinate of a hypothetical off-line zero, at apertures between the conductor horizon `e^a ≈ log γ₀/4` and the forcing threshold `e^a ≈ (log γ₀)^{1/(2δ)}`, at least outside a sparse set of ordinates? | Forcing half [L]; conductor horizon [L]; gap [R]; all-test eventual positivity fails beyond the horizon at Kronecker-aligned heights [L]; positivity at almost every zero ordinate for nonnegative tests [L]. |
| **B3.33** | **The collided form.** An arithmetic identity or inequality computing `D` or its Hecke defect `Σ m(2cosh(2δL) − 2)\|f̂(ρ)\|²` from prime-side data. | `D ≥ 0` [L]; `D` Hecke invariant ⇔ RH [S]; not a holomorphic sum; the global collision has no analytic carrier [L]; escape forms are collided [L]. |
| **B3.34** | **Central nonvanishing of the coupled class.** At ordinates with `ξ(1/2 ± iγ) ≠ 0`, does every member of `HeightCoupledSystem 2 1 1 γ` satisfy `Λ(1/2) ≠ 0`? Is there a subclass with Euler-product or Dirichlet-lattice constraints that admits a zero-cost quartet contraction? | Equivalent to the ceiling at such `γ` [R]; `W_β` splitting and quartet contraction both leave the Dirichlet-lattice decay class [S]; two-sided rigidity fails at critical-zero ordinates [S]. |
| **B3.35** | **A selective counting polarization.** A family of counts on a two-variable arithmetic object, of rank growing with the class, whose Tate limit is a positive quadratic form that depends on the fibre and equals the Rosati form at the fibre of `ζ`. | Theta surface: counting polarization, soft [L]; lattice counts on the square: boundary or determinant positivity [L]; base `h⁰` does not extend [L]; `ℙ¹ × ℙ¹` calibration [L]. |

### 2.4 Settled questions

- **Section counts, effectivity, naive heights, one-sided counts.** Each is the sign; none is a weaker input.
- **Elliptic localization in correspondence-closed carriers.** Resonance only; `σ_γ` is the unique reflection-compatible affine localizer; its even sector cannot force; Hecke + `σ_γ` stability is blindness.
- **Two-sided rigidity of the coupled class.** False at every critical-zero ordinate [S]. Positivity is chiral: outward splitting positive, inward collapse not.
- **The contraction and collision calculus.** Minimum anchored cost `κ ≥ 3`; planting cost `Δκ ≥ 2`; boundary-twist absorption; Fejér coupling at central cost `9(K+1)/(2K)`; Fejér barrier; even real orders; global collision non-analytic.
- **The first gauge charge.** A height twist; separation needs edge-concentrated tests; the second charge is not archimedean.
- **Escape.** Located (alternative), classified (phase kernels, summable configurations), read as collided Cauchy forms; RH is positive gauge mass.
- **The successor defect.** Polynomially small in the strip, holomorphic, no principal parts.
- **Also settled:** theorem of the square and budget free; positivity beyond isotropy only without localization; kernel counts blind to quartets; base at receiver level; successor coupling empty; the κ = 1 class; Lefschetz receivers at one prime; linear loss of family averages and moments; twists rate neutral; blind-ideal synthesis; averaged positivity at `Γ^{99/100}`; absolute pole-order budget false.

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three walls, each in its own currency.
4. The question does not reduce to a mapped class: its output is not a zero-free strip, a collided positivity, a counting reformulation of the sign, a gauge-orbit statement or a one-variable positive system.
5. The question addresses the polarization problem in its current form: a positive form that is equivariant, or an equivariant form that is positive, produced by a structure that computes it.

**Why these three.** The previous round's questions are answered. Elliptic localization exists only through `σ_γ`, at a price; the open part is the forcing gap. Counting is the sign in every currency; the open part is a form that is computed. The first gauge charge is archimedean; the open part is the second.

### Q1. The elliptic forcing gap: can a single odd-sector sign be proved beyond the conductor horizon?

> *At the ordinate `γ₀` of a hypothetical off-line zero of depth `δ`, is Weil's form of `ζ` nonnegative on the `σ_{γ₀}`-odd detector (the twisted sinh test) at apertures between the conductor horizon `e^a ≈ log γ₀/4` and the forcing threshold `e^a ≈ (log γ₀)^{1/(2δ)}` — for all such ordinates, or for all outside a set sparse enough that zero-density estimates exclude it?*

- **Why.**
  - The odd sector of the elliptic localizer is the only localizing sector whose positivity excludes, and the forcing half needs it on one test at one height [L].
  - Below the conductor horizon twisted positivity is a theorem, and it is source-blind [L]; above the forcing threshold one sign forces an off-line companion within ordinate distance `R ≈ e^a` [L]. For `δ < 1/2` the ranges are disjoint [R].
  - The known obstruction beyond the horizon (no eventual positivity for all tests) comes from Kronecker-aligned heights; the question asks for one test at the ordinates of zeros.
  - On the prime side the twisted detector is a Dirichlet polynomial of length `e^{2a}` evaluated at `γ₀`; the question is whether its large values can occur at the ordinates of off-line zeros.
- **Route.**
  1. W7(x): the gap as a theorem with explicit thresholds.
  2. The exact inequality: the twisted detector's prime polynomial against the shifted digamma term `≈ log γ₀`, the shifted poles and the tails.
  3. An exceptional-set version: positivity for all `γ₀ ≤ T` outside a set `E_T`, by moments of the prime polynomial over zero ordinates (the method of the zero-ordinate theorem), compared with `N(1/2 + δ, T)` and with the local count `A₀ log T` of companions.
- **Weaker-than-RH content.** Proved at threshold `θ` (apertures up to `e^a ≈ (log γ)^θ`), the forcing half gives a non-isolation law: an off-line zero of depth `δ > 1/(2θ)` has an off-line companion within ordinate distance `(log γ)^θ`. That is a structural statement about off-line zeros, not a zero-free strip, so it escapes the first-rung law.
- **Outcomes.**
  - *Yes:* the first localizing positivity of elliptic type that forces something; with density bounds on clusters, possibly a theorem excluding isolated deep off-line zeros.
  - *No:* a theorem that the odd-sector sign at apertures beyond the horizon is equivalent to the absence of nearby off-line zeros, closing elliptic localization as a forcing mechanism; forcing must then come from a computed polarization (Q2).

### Q2. The collided form: what computes the positive form, and what bounds its Hecke defect?

> *Is there an arithmetic identity or inequality — an explicit formula on the conjugate diagonal — that computes the collided form `D(f) = Σ_ρ m_ρ|f̂(ρ)|²`, or bounds its Hecke defect `D(T_L f) + D(T_{−L} f) − 2D(f) = Σ_ρ m_ρ(2cosh(2δ_ρ L) − 2)|f̂(ρ)|²` by prime-side data?*

- **Why.**
  - `ζ` already has a positive form, `D`, unconditionally; its Hecke equivariance is RH [S]. `W` is equivariant and computed; its positivity is RH. A proof by polarization needs either half from a structure that computes it.
  - Every counting reformulation of the missing positivity has been shown to be the sign; a computation of `D` is not a reformulation.
  - `D` pairs `ρ` with `ρ̄`; the explicit formula computes only holomorphic sums and pairs `ρ` with `1 − ρ`. A one-variable meromorphic carrier of the conjugate collision does not exist [L]. Any computation of `D` is therefore two-variable or non-holomorphic.
  - Reading [R]: `D(f)` is the squared norm of `f̂` restricted to the zeros in `ℓ²(zeros, m)`, and its Hecke invariance is the unitarity of the archimedean flow there. This is the Hilbert–Pólya structure, stated as a quadratic form. Over `𝔽_q`, `D` is the Hermitian trace `Tr(P(F)P(F)*)` on `H¹ ⊗ ℂ` and `W` is the Rosati trace `Tr(P(F)P(F)′)`; purity is `* = ′`.
- **Weaker-than-RH content.**
  - With `f̂` localized at height `T` and `L ≍ log T`, the Hecke defect is a weighted count of off-line zeros with weight `≍ T^{2c(β−1/2)}`, a zero-density functional [R]. Any arithmetic upper bound for it is a density-type theorem; a bound beyond the density exponents would be new; vanishing is RH.
  - An identity computing `D` on a restricted test class (e.g., twisted tests at one ordinate, where `σ_γ` acts) is a construction, not a sign.
- **Candidates to test.**
  - The continuous spectrum of the modular surface: Rankin–Selberg unfolding and the Maass–Selberg relation give unconditionally positive truncated Eisenstein norms in which the scattering coefficient `ξ(2s−1)/ξ(2s)` appears, and the height-coupled lift of `ζ` is a Rankin–Selberg square of an Eisenstein series [R].
  - Mean values of Dirichlet polynomials over zero ordinates (the zero-ordinate theorem's method).
  - The theta surface, where a counting polarization exists but is fibre-independent (B3.35).
- **Outcomes.**
  - *Yes:* the conjugation side becomes computable; the polarization problem reduces to the equivariance of a computed positive form, and the Hecke defect bound is a new density-type theorem.
  - *No:* a theorem that `D` is not a limit of explicit-formula or mean-value functionals beyond density strength; the polarization must then be constructed (B3.35), not read off.

### Q3. The first non-archimedean gauge charge

> *Does any unconditional Weil-positivity statement for `ζ` fail for the twin that flips the atoms at `2` and `3` — the first gauge twin that is provably not a height twist — and can the separating margin be carried by the successor holonomy on `2 → 3 → 4` rather than by certified numerics?*

- **Why.**
  - A `ζ`-specific sign must use sign-changing, gauge-charged data. Every unconditional positivity of the corpus is gauge blind; the first prime window is gauge charged only through a height twist of `ζ` itself [L].
  - From the second prime on, gauge charge is not archimedean [L]; the Liouville point stays at distance `≥ e^{−|γ|}/50` from the Kronecker line [S].
  - Finite multiplicative lattice forms cannot see the vacuum; the successor connection can, and it reconstructs `(ω(2), ω(3))` from the links `2 → 3 → 4` [S]. The `+1` structure is the gauge-charged datum.
- **Route.**
  1. W8: the edge eigenproblem for the single flip at `2`.
  2. W13: the failure aperture `A₂₃` of the `{2,3}`-twin, with a witness; certified positivity of `ζ` at `A₂₃` (W5).
  3. The margin as a function of aperture, against the `4(A+1)²e^A N²Φ` cost of the off-line field (B3.26).
  4. Whether the margin is a function of the successor links: a mixed (affine) correlation prescribed by the actual source, not a free extension, which APD shows adds nothing.
- **Outcomes.**
  - *Separation with a surviving margin:* the first unconditional positivity that reads non-archimedean arithmetic; an input for B1.6's gauge-charge condition.
  - *Separation with a collapsing margin:* a measured threshold where positivity starts to see arithmetic, and a sharp no-go beyond it.
  - *No separation up to the certified aperture:* positivity is gauge blind on every window where the twin is not a twist, as far as certification reaches.

The three questions are the forcing problem in each wall's currency:
- Q1: what a localized sign at one height can force (Wall 3, faces 3.18–3.19; Wall 1, face 1.3).
- Q2: what computes the positive form, and its equivariance defect (Wall 14, faces 14.18 and 14.21; Wall 1, face 1.16).
- Q3: whether positivity carries non-archimedean gauge charge (Wall 1, face 1.18).

**Considered and not chosen.**
- **The central vanishing ceiling (B1.12) and central nonvanishing of the coupled class (B3.34).** RH-sufficient and not refuted, but a proof of two-sided rigidity at zero-free ordinates must use the zero-freeness, and the ceiling at such ordinates is a central-nonvanishing statement for a class of degree-four objects with no known classification.
- **A selective counting polarization (B3.35).** The constructive form of Q2's negative outcome; it has no candidate object yet beyond the soft theta surface.
- **Escape at infinite height (B3.2).** Classification only.
- **Stepanov auxiliaries (B3.30).** Their natural output is RH; univariate integer polynomials are classically insufficient.
- **The Rankin–Selberg field (B3.28).** An ingredient of Q2.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. The corpus maps every forcing mechanism it has found, each with a sharp limit:

- **Invariant positivity is isotropic.** Multiplicative correspondences are boosts at off-line pairs; positivity invariant under a boost is isotropy; non-localizing positivity holds for every prime weight.
- **Elliptic localization is resonance or `σ_γ`.** Within correspondence-closed carriers only resonant scales act elliptically; `σ_γ` localizes at the price of gauge charge and conductor, and its unconditional positivity stops at the conductor horizon.
- **One-variable positivity is Landau–Fejér positivity.** Real anchors of twice the weight; anchored quartets force `κ ≥ 3`; harmonic couplings anchor and never count; the global collision has no analytic carrier; the coupled class is not rigid.
- **Counting is the sign.** Section counts, effectivity functions, naive heights, one-sided counts, tensor bases and horizon torsion are RH.
- **Collided positivity is free and blind.** Determinants, coupled counts, escape forms and `D` are positive automatically and see no sign; their equivariance is the content.
- **Multiplicative data see orbits; the archimedean place supplies only the first gauge charge.**
- **Amplification loses linearly; averages select windows, not zeros; escape classifies, it does not exclude.**

What is missing has a precise shape: a **structure that computes a form which is both positive and Hecke equivariant** — equivalently, that makes complex conjugation on the zeros (the Frobenius at the infinite place) agree with the functional-equation reflection by an algebraic mechanism. Over `𝔽_q` this structure is a polarization of `C × C`: the Rosati involution is the transpose of correspondences, the trace is positive by Riemann–Roch on the surface, and `H¹` carries a Hermitian structure in which Frobenius is a similitude. Over `ℤ` no existing theory supplies it:

- arithmetic intersection theory has a Hodge index theorem on arithmetic surfaces fibred over `Spec ℤ`, not on a square of `Spec ℤ`;
- the adele class space and the scaling site realize the zeros spectrally, with Weil's pairing as the trace, and their positivity is RH;
- the Hilbert–Pólya picture posits the Hilbert norm (`D`) and asks for unitarity (its equivariance) without computing either;
- the theta surface computes a counting polarization that is the same on every fibre;
- one-variable positive systems are exhausted at classical strength.

A new field is therefore likely required [R].

### 4.2 The field: arithmetic polarization, the geometry of the conjugate diagonal

**Thesis [R].** RH is the coincidence on the zero divisor of two involutions: the functional-equation reflection `s ↦ 1 − s`, holomorphic and computed by the explicit formula, and complex conjugation `s ↦ s̄`, antiholomorphic and computed by nothing. Their composite is the Rosati reflection `s ↦ 1 − s̄`. The field studies structures on which both involutions act and a positive trace can be computed: its aim is to make the infinite place's Frobenius an algebraic correspondence on a two-variable arithmetic object, so that positivity becomes a count and equivariance becomes a symmetry.

**What it would be like.**
- Like Hodge theory: a Hermitian structure (giving `D`) and an intersection pairing (giving `W`), related by a polarization.
- Like Arakelov theory: the archimedean place is a geometric fibre with a metric, and positivity comes from sections of metrized bundles.
- Like Tate's theory of heights: positivity from a naive height at bounded distance from a quadratic form.
- Like gauge theory: the prime gauge torus acts, multiplicative data are gauge invariant, and the arithmetic point is fixed by additive (successor) structure that carries holonomy.

**Parts already in the corpus.**
- **Positive duality** (APD, MPG, SBWF): rigidity and capacity of positive Poisson pairs; the exhausted one-variable shadow.
- **Correlation geometry** (ACG) and **biarithmetic gauge geometry** (BGG): the gauge torus, charged and invariant statistics, successor holonomy, Catalan repulsion, torsion characteristics.
- **Correspondence positivity** (ACP) and **arithmetic polarization** (PL): the layer map of Weil's argument, local types, elliptic localizers, the two forms and their capacity identity, collision and contraction calculus, escape as collided forms.
- **Arithmetic effectivity** (AE): the five currencies of the sign, the theta surface, horizon torsion.

What none has is the object on which the two forms are one.

### 4.3 Criteria the field must meet

| Criterion | Test against the corpus |
|---|---|
| **Computability** | The positive form, or the positivity of the equivariant form, is produced by an identity (an explicit formula, a trace formula, a count), not posited. Counting reformulations of the sign (B1.9) do not count. |
| **Conjugate-diagonal reach** | It computes sums `Σ G(ρ, ρ̄)` for a class of two-variable `G` large enough to contain `\|f̂(ρ)\|²`; one-variable meromorphic carriers are excluded by the collision law. |
| **Selectivity** | Distinguishes `ζ` from the battery W1: relaxations, coupled-class deformations, the golden datum and complex fake, dominated, flipped and Liouville twins, theta-surface fibres at `a ≠ 0`. |
| **Fibre selectivity of counts** | Its counting polarization depends on the fibre and is the Rosati form at the fibre of `ζ`; the theta surface's is fibre-independent. |
| **Rank growth** | Its section spaces have rank growing with the class; rank-one and Künneth lattice counts collapse. |
| **Gauge charge** | Uses sign-changing atoms, the pole, or the successor connection; sees non-archimedean charge beyond the first prime. |
| **Local type** | Localizes by a non-multiplicative operation; elliptic at off-line pairs (through `σ_γ` or otherwise) or carries a polarization. |
| **Chirality** | Reproduces that positive deformations split critical double zeros and never collapse critical pairs. |
| **Joint use of invariants** | Uses coefficient positivity, the FE, the simple pole and strip holomorphy together. |
| **Non-circularity** | No premise contains the conclusion; objects are constructed before their sign. |
| **Uniformity** | Aperture, height, rank, damping and window controlled together; exceptional sets below the zero spacing. |
| **Calibration** | Reproduces Weil for curves (`2g`, Hermitian `H¹`, Rosati transpose), exterior-count purity, `ℙ¹ × ℙ¹` effectivity, the κ = 1 collapse, the `2 : 1` anchor law and `κ ≥ 3`, the conductor horizon, the capacity identity `W = D − Δ`. |
| **New partial results** | Outputs that are not zero-free strips: a non-isolation law (Q1), a density-type bound from the polarization (Q2), a non-archimedean gauge-charged positivity (Q3), central nonvanishing for a coupled class (B3.34). |

### 4.4 Questions it must answer

1. **What is the Frobenius at infinity as a correspondence?** Which algebraic involution on a two-variable arithmetic object acts on the zero spectrum as complex conjugation?
2. **What computes the positive form?** Which identity evaluates `D`, or its Hecke defect, from arithmetic data (Q2)?
3. **What selects the fibre of `ζ`?** Which count has a quadratic term that depends on the characteristic and is the Rosati form at `a = 0` (B3.35)?
4. **What has rank growing with the class?** Which section spaces on the square of `Spec ℤ` escape the diagonal collapse?
5. **How does `σ_γ` localize beyond the conductor horizon?** What controls the odd-sector sign at the ordinate of a zero (Q1)?
6. **What is the non-archimedean gauge charge?** How does positivity read the successor holonomy beyond the first prime (Q3)?
7. **What pays `ζ`'s own zeros?** The capacity `Δ` is depth uniform; which structure bounds it by `D`?
8. **Is the coupled class bounded at the centre?** Does any member of `HeightCoupledSystem 2 1 1 γ` exceed `ζ_γ`'s central order (B1.12, B3.34)?
9. **What are the escape states of `ζ`?** Where does Abel mass go when the abscissa is not attained (B3.2)?
10. **How does an average become a point?** Which selection principle reaches below the zero spacing?
11. **What is the base?** Which structure has a tensor loss independent of the power?

### 4.5 Tools

**Built:** the capacity identity `W = D − Δ` and the Hecke law of `D`; the polarization law; local forms, boosts, resonance and the elliptic localizers `σ_γ`; twisted explicit formulas and the conductor horizon; the forcing half; the effectivity calculus, Tate's limit law, the theta surface, horizon torsion, section-count and Stepanov criteria; the gauge torus, finite lattice intertwiners, successor connection and holonomy, Catalan repulsion, Ramanujan torsion; the contraction and collision calculus with minimum anchor costs, Fejér barriers and parity of couplings; chiral deformations; phase kernels, Bohr uniqueness, the escape alternative and criterion, Abel boundary measures; normalized graphs, determinant and Rosati degrees, exterior counts.

**Not yet built:**
- **Conjugate-diagonal explicit formulas:** identities for `Σ G(ρ, ρ̄)`.
- **Hermitian structures on correspondence spaces:** a Hilbert norm on zero transforms produced arithmetically, with the archimedean flow acting by computed similitudes.
- **Selective counting polarizations:** fibre-dependent counts with rank growing with the class.
- **Elliptic localization beyond the horizon:** odd-sector sign laws at zero ordinates, with exceptional-set control.
- **Non-archimedean gauge-charged positivity:** certificates whose margins are successor-holonomy data.
- **Rigidity and ceilings for coupled classes:** central-order bounds for degree-four positive systems with shifted poles.
- **Oscillatory capacity bounds:** `Δ ≤ D` from structure.
- **Selection lemmas** at the zero-spacing scale.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | • The correspondence surface of `Spec ℤ`: Hecke ring, normalized graphs, archimedean flow, successor and affine maps, the reflection `s ↦ 1 − s`, conjugation `s ↦ s̄`, the Rosati reflection and the localizers `σ_γ`.<br>• The two forms: the equivariant form `W`, the positive form `D`, the capacity `Δ`, the Hecke defect of `D`.<br>• The biarithmetic semigroup `⟨+1, ×p⟩`: the gauge torus, gauge points and twins, the successor connection and its holonomy, torsion characteristics.<br>• Counting objects: polar surfaces with Euler characteristics, effectivity functions, naive heights, the theta surface with its characteristic, horizon tori `ℤ/lcm(1,…,N)ℤ`.<br>• Positive systems: completed, height-coupled and Fejér-coupled classes, their deformations, anchors, ceilings.<br>• Escape objects: cofactor profiles, symbols `G`, phase kernels, Abel boundary measures, gauge mass.<br>• Candidate two-variable carrier [R]: the continuous spectrum of the modular surface, whose Eisenstein family has Rankin–Selberg squares equal to the height-coupled lifts of `ζ`, and whose Maass–Selberg relation is an unconditional positive norm. |
| **Language** | It must distinguish: positive and equivariant; collided (conjugate) and Rosati (reflection) pairing; computed and posited; hyperbolic, elliptic and unipotent; resonant and localizing; even and odd sector; below and beyond the conductor horizon; gauge invariant and gauge charged; archimedean and non-archimedean charge; orbit and point; count and sign; soft and selective polarization; one-variable and two-variable; inserted and intrinsic zeros; anchor, pole tax and collision; two-sided rigidity and one-sided ceiling; outward and inward deformation; classification and exclusion; average and individual zero. |
| **Mechanisms to discover** | • A **polarization law over `ℤ`**: positivity and equivariance of one computed form.<br>• A **conjugation law**: an algebraic correspondence acting as complex conjugation on the zeros.<br>• A **selective count**: a fibre-dependent counting polarization.<br>• An **elliptic forcing law**: odd-sector positivity at zero ordinates beyond the conductor horizon.<br>• A **non-archimedean charge law**: positivity reading successor holonomy.<br>• A **capacity law**: `Δ ≤ D` uniformly in the depth.<br>• A **ceiling law**: central-order bounds for coupled classes.<br>• A **base law**: a fixed tensor loss. |
| **First milestones** | (1) W7(x): the forcing gap as a theorem; then Q1's exceptional-set version.<br>(2) W8 and W13: the first two gauge-charged windows; then Q3's margin law.<br>(3) Q2: the Hecke defect of `D` as a density functional, and a test of the modular-surface carrier.<br>(4) W7(xi): the ceiling at zero-free ordinates as central nonvanishing; a probe of B3.34.<br>(5) W7(xii): one theorem for all collided positivity.<br>(6) W11: the last contraction calibrations. |

Each milestone is a theorem of a kind the corpus does not yet contain: a forcing law of elliptic type, a gauge-charged positivity beyond the archimedean line, a computation on the conjugate diagonal, or a ceiling for a coupled class, rather than a receiver, a blindness theorem or a counting reformulation of the sign. Each programme standard adds its own requirements:
- **APD:** name the positive side, the spectral side, the gap and the integer.
- **ACG / BGG:** name the gauge charge and its holonomy.
- **ACP / PL:** name the layer of Weil's argument, the local type, whether the carrier localizes, and whether the positivity is collided or Rosati.
- **AE:** name the currency, and show the count is not one of the five forms of the sign.
