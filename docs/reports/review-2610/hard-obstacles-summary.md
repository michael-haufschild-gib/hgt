# Research frontier summary: work, open mathematics, next questions, and a possible new field

Status: 2026-10-26, corpus `8b9038260` with the working tree of that day. This summary covers the 31 routes, 17 candidates, PW-B and the supporting programmes of the [complete report](hard-obstacles.md). Companions: [walls ledger](walls-ledger.md), [route unification](route-unification-ledger.md). Evidence: corpus search and Lean statement reading, recorded in `logs/review-2610/working-log-v2.md`. Nothing was compiled. `[L]`, `[S]`, `[P]`, `[R]` as in the complete report.

## 0. The frontier in twelve statements

1. **Multiplicative symmetry is hyperbolic exactly at the off-line zeros.** At a reflection pair `{ρ, 1 − ρ̄}` the Rosati local form has signature `(1, 1)`; Hecke operators, the archimedean flow and every gauge twist act on it by boosts iff `Re ρ ≠ 1/2`, by rotations on the line; the successor acts unipotently; the functional equation acts by the reflection swap. Positivity of a carrier invariant under a boost forces isotropy. This is the common origin of every blindness, half-blindness and isotropy theorem in the corpus.
2. **Weil's argument transfers to `ℤ` up to its sign.** Identities (L1), the theorem of the square for normalized graphs (L2) and the budget (L3) hold over `ℤ` for free, and hold on the golden datum. Kernel counts (L4) are blind to complex quartets, hence to every strip zero of `ζ`. What is missing is Rosati positivity (L5), equivalently the sufficiency of the free budget, and a base with fixed tensor loss (L6); each is RH.
3. **Hodge index splits into a local part that holds and a Lefschetz part that is RH.** At one prime, every test in `[−η, η]` is Weil positive for `η ≤ 3/10`; RH is the nonnegativity of Weil's form on the differences `g − T_{p^m} g`, equivalently a one-sided Weil inequality at one prime, equivalently at one fixed shift.
4. **Positivity on a carrier certifies blindness, half-blindness or isotropy, never forcing.** The only positivity beyond isotropy in the corpus lives on non-localizing carriers (aperture `≤ 3/10`) and holds for every prime weight.
5. **Multiplicative data and nonnegative tests cannot see the actual source.** Multiplicative observation is projection onto gauge orbits; the Möbius half-power law holds at Haar-almost every gauge point and at `0` is RH; the prime source is typical except for its pole. On nonnegative tests `ζ` is the worst member of its sign orbit: positivity there transfers to every dominated twin.
6. **Every amplification over `ℤ` tested loses linearly.** Gauge moments, family averages [S], tensor products and relative powers gain on depth exactly as fast as they pay; zero loss is flatness, which on a curve is unitarity. A rate needs a fixed tensor loss, and that is RH.
7. **No route has a rung between Vinogradov–Korobov and quasi-RH.** Graded receivers, Vaughan power improvements, admission at fixed damping, power growth of the damped receiver energy [S], one-sided Lefschetz bounds and multiplicative forcing all have a fixed strip as first gain.
8. **The invariants determine `ζ`; the simple pole is the rigidity threshold.** The pole-budget-one completed positive class is exactly `ℝ^× · ζ`. Real off-line pairs contract to the line at no pole cost; complex quartets cost pole budget in every known contraction, and a cost-free contraction would prove RH.
9. **Pole order pays only for inserted zeros, and a budget pays a hyperbolic pair only on a finite segment.** `ζ`'s own zeros are paid, if at all, by oscillation of the zero sum, which no aperture-uniform capacity controls except the one RH asserts.
10. **Positivity holds on average over short windows and at almost every zero ordinate.** Exclusion of an individual zero needs exceptional sets below the zero spacing; a correspondence of length `L` resolves heights only at scale `1/L`.
11. **Escape is made of translated zeros on every finite window and at every finite rank.** The cofactor Gram is a translation Gram of one profile whose Laplace transform is `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s` [S]; completeness is an energy split of that profile.
12. **The archimedean–finite coupling never reaches the zeros.** Positivity on `ℚ_{>0}` splits into archimedean and Kronecker-null parts; the successor sees continuous archimedean spectra but never atoms; the extensions of Weil's correlation to `Aff(ℚ)` are a box of parameters over the critical zeros and add no constraint.

## 1. Just work

Known mathematics suffices for each item. None crosses a wall. An item may have an unknown outcome; what is known is the method.

| ID | Task | Concrete content | Completion criterion |
|---|---|---|---|
| **W1** | Selectivity battery | Test every mechanism against: pole-order-2 real pairs and refunded quartets as `CompletedPositiveSystem 2 1`; pole-order-3 and strip-pole quartets; over-regular Beurling systems; twisted boundary systems at `κ = 2r + 1`; the Siegel family `ζ(s)/ζ(s+1−β)`; double-pole, periodic-pole and half-zero boundary data; the Liouville twin, sign-flipped and dominated twins, Haar-typical twists; Hecke and Bost–Connes states; the golden datum and the complex fake (`q = 16`, roots `±8i, ±2i`); `Γ_ℝ^d` solutions; signed self-dual combinations; white noise, reset-origin mixtures and translated-zero eigenstates. Calibrations to reproduce: `κ = 1` collapse to `ℝ^× · ζ`, `⌊k/2⌋` capacity, dlVP optimality, Weil for curves with budget `2g`, exterior-count purity over `𝔽_q`. | Each mechanism records which model defeats it, or that none does, and the local type of its correspondences at off-line pairs. |
| **W2** | Finite identities and certificates | Gram, Hausdorff, Hankel and Jensen blocks; finite heat transforms; schedules, histories and ledgers; finite Robin and Li checks; finite JAS and Vaughan budgets. | Every finite term certified; no cofinal claim. |
| **W3** | Premise checks | Regularity, support, decay, cutoff and domain membership for named tests and families (SZ limits, CHMD domains, candidate sources). | The hypotheses of an existing transfer are discharged. |
| **W4** | Transport of proved inputs | Width functor; RW↔SZ↔CHMD; HF→AIP; Weil margin → heat window; graded Sobolev floors; the short-window averaged, off-line-field and zero-ordinate theorems, and the short-cycle local–global split, restated in RW, SZ, CHMD, EWU, OWU, ACT, AIP and HF coordinates. | Each conclusion stated at its true strength. |
| **W5** | Certified extensions and constants | Push the pointwise windows beyond `3/10`, `181/500`, `(log 2 + 1/50)/2`; make `κ₀, C₀, Γ₀`, `sharpCollarConst κ`, `R₀`, `T(λ)` explicit; compare the κ = 1 collar with dlVP. | Certified finite-aperture theorems. |
| **W6** | Short windows to the classical range | Selberg's near-line density holds on windows `T^{1/2+ε}` [R]; replace `Γ^{99/100}` by `Γ^{1/2+ε}` in the averaged, off-line-field, zero-ordinate and positive-measure theorems and in WL's filtered deficit. | The four theorems on `Γ^{1/2+ε} ≤ H ≤ Γ/8`. |
| **W7** | Corollary assembly | (i) An averaged bounded-energy statement for WL from the high-zero tail and the filtered deficit. (ii) One rate dictionary for RW, SRT and ACS through `groundRate = polarRate`. (iii) The explicit LA/WD residual region `{|t| ≤ T(λ), λ ≤ λ₀}`. (iv) ACS effectivity as exhaustion: Bézout on the full cone ⇔ blind ideal = ⊤ ⇔ RH. (v) Replace the imported `c/(log|t|)^9` collar in the harmonic module by the MPG dlVP calibration or the SBWF κ = 1 collar. (vi) The conservation identity for infinite reflection-antisymmetric corrections, refunds included. (vii) One capacity law: boundary `2Σm ≤ k`, collar `2Σ ord ≤ κ`, gauge `2Σm ≤ κ`, family `Σm ≤ k`. (viii) The energy-rate law of the damped receiver: `limsup log E_ε(T)/log T = max(0, 2(Θ − ε) − 1)` for all but countably many `ε`, from the energy–holomorphy theorem behind `riemannZeta_sub_eq_zero_of_energy_growth` (a pole of the Mellin pairing at `ρ − ε` survives unless `ζ(ρ − ε) = 0`) in one direction and the classical bound `1/ζ(s) = O(|t|^δ)` in a zero-free half-plane in the other. (ix) State the escape-completeness criterion as one theorem linking the translation-Gram, Laplace-form and gauge-torus spectral readings. | Each statement proved from existing theorems. |
| **W8** | The first gauge-charged window | Compute `inf W_{flip}(F)/∫F²` over odd real `C²` tests `F` supported in `[−181/500, 181/500]`, where `flip` is `Λ` with `Λ(2)` replaced by `−log 2` (the Liouville twist on this window). The certificate `re_weilFullFunctional_liouvilleTwist_odd_window` decides every test with `Re(k_F(log 2) + k_F(−log 2)) ≥ 0`; the rest is a finite-aperture eigenvalue problem, to be closed by an explicit negative witness or by a kernel-checked certificate (as for PA order 24). Then the minimal failure aperture of the twin from full-cone selection. | A theorem: either the odd window separates `ζ` from its twin, or it does not, with the least separating aperture. |
| **W9** | Depth homogeneity, remaining classes | The loss law for harmonic twists `n^{−ikt}`, for `k`-level forms and for Følner coupling, each with its positive survivor. Gauge moments, products and finite family averages [S] are proved; for family averages the slope is the logarithm of the family mean, forced when that mean exceeds `1`. | One theorem per class. |
| **W10** | Range-limited growth inputs | State the corpus VK step (`vk_dlvp_contradiction`) as a `δ`-range instance of `exclusion_iff`. | The VK region as an instance of the growth-to-forcing law, with its barrier. |
| **W11** | Cost of complex contraction | Prove that no multiplier with nonnegative Laplace density contracts a complex off-line quartet at `Δκ = 0` (the quartet multiplier has density `2e^{t/2}cos(γt)(e^{at/2} − e^{−at/2})²`, sign-changing and growing; critical refunds add bounded cosine terms) and determine the least cost for `1/4 < a < 1/2` (`1` or `2`). Expected outcome: a no-go. A cost-free contraction would prove RH through the κ = 1 collapse. | The optimal pole cost of complex contraction. |
| **W12** | Integration of working sources | `TheCofactorGramIsATranslationGram`, `TheLaplaceFormOfTheCofactorProfile`, `MomentAmplificationOfAnyFamilyLosesLinearly`, `SubpowerReceiverEnergyTranslatesZeros`, the long-modulus decomposition modules, the closed-cycle recovery modules, the wide-window prime channel, the finite-window incidence modules; formalization of the paper-proved gauge-mass criterion (RH iff every actual common cofactor limit at every `0 < ε < 1/2` has positive gauge mass). | Each statement at its stated strength in an umbrella; the gauge-mass criterion in Lean. |

## 2. Open mathematical obstacles

### 2.1 Tier B1: RH-strength closing statements

Each is equivalent to RH or stronger. Solving one closes every route that uses its receiver.

| ID | Statement | Routes |
|---|---|---|
| **B1.1** | **Critical signed cancellation at every positive slack.** Bounded critical deficit energy, a one-sided lag or Abel moment, the history floor, the regularized abscissa `1/2`, the JAS half-power budget, Mertens at square root, the late-lag sign. Gauge forms: typicality of the gauge point `0` for `μ`; for `Λ`, square-root cancellation at `0` after subtraction of the pole. | WL, MC, FU, RP, PBM, JAS, SRT, DR |
| **B1.2** | **Signed small-damping energy.** Cofinal admission as `ε ↓ 0`; subpower receiver energy at every damping; signed control of the long-modulus quadrature; a Báez–Duarte residual → 0; exclusion of fixed-origin cofactor escape at every damping. | PM, CTF, BVI, MC, PW-B |
| **B1.3** | **Complete Weil positivity; the Lefschetz part.** All apertures with Gamma, both polar terms and one shared budget. Equivalent forms: the one-sided Weil inequality for `T_{p^m}` on short cycles at one prime; `Re W(T_v g, g) ≤ W(g, g)` at one shift; sufficiency of the free budget (both normalized graphs of `1 ± T` effective); Rosati positivity (L5); the nodal inequality; positive Suzuki first variation; odd capacity; the one-shift reflected collar; global allocation; the `O(L)` ceiling; Bézout on the exact source cone. | RW, SZ, CHMD, EWU, OWU, ACT, AIP, TT, HF, ACS, SRT |
| **B1.4** | **Selection.** From short-window averages and almost every zero ordinate, for nonnegative tests of bounded shape, to every height, every signed test and every aperture. At `A ≍ log Γ` an exceptional set must be below the zero spacing, and a localizing correspondence must have length `≳ log Γ`. | WL, SRT, ACS, APT |
| **B1.5** | **Critical-endpoint heat and moment sign.** Coefficient positivity on the residual heat region; all-rank Hankel positivity at one time; both literal heat grids; rank-uniform Schur decay; the Newton interior margin; order-uniform passivity. | LA, WD, TH, HCF, GTA, XN, PA |
| **B1.6** | **Forcing and exhaustion for a realization.** Exhaustion of the maximal blind ideal by an input outside the exhausted classes: invariant (hence hyperbolic) quadratic positivity, non-localizing positivity, positivity on nonnegative tests, finite or coupled multiplicative certificates, linear rigidity in the coefficient measure, pole order, gauge-invariant data, kernel counts. The input must localize at off-line pairs, have a non-hyperbolic local symmetry or an independent polarization there, and use sign-changing (gauge-charged) data. Faces: Ward cap vanishing; the sub-unit trace residual; renewal boundary orientation; source effectivity; a section count; a stabilization weld; pre-divisor compactness; a descending potential; a centred Ising limit; a lossless nonlocal port; a certificate stream. | TG, RN, WD, ACS, all candidates, PW-B |
| **B1.7** | **Single-currency endpoints.** Cofinal contrast equality (BSY); the subexponential Li floor; the eventual Robin tail; recurrence near possible zeros; the global index `D < 2`. | FEL, LI, RB, BAG, HF |
| **B1.8** | **RH with simple zeros.** A faithful positive Meyer degree; RR for the Hilbert–Schmidt reserve; exhaustion of the bounded-orbit carrier. | ACS/Meyer faithful branch |
| **B1.9** | **Fixed tensor loss (the base).** One exponent `L` with `|c(t)|^k ≤ C_k e^{Lt}` for every `k`, for the spline orbit correlation; equivalently a sublinear loss law for a zero-forced family; for the one-prime Lefschetz sequence, `|c_m| ≤ c_0`. It cannot come from multiplicative data, family averages, moments or products. | HF, SRT, ACS, AOG |

### 2.2 Tier B2: classical open problems weaker than RH

| ID | Problem | Where it is the next rung |
|---|---|---|
| **B2.1** | Quasi-RH: a fixed zero-free strip. | First rung of every graded cancellation receiver, of admission at fixed damping, of power growth of the receiver energy, of one-sided Lefschetz bounds and of multiplicative forcing. |
| **B2.2** | Finite off-line index. | HF/AOG index exit; WD collision masses. |
| **B2.3** | Simplicity of the zeros. | Operator-norm faithful realizations (B1.8). |
| **B2.4** | Density hypothesis; large values beyond Guth–Maynard. | Averaged positivity at larger aperture; the filtered deficit. |
| **B2.5** | At least `3/4` of the zeros on the critical line. | TTPC: signed coalescent surplus `β ≤ 1/18` at the gauge point `0`. |
| **B2.6** | Power-saving sign correlations of `μ`, `λ` (Chowla/Elliott with rates). | MC anti-alignment; SSA constants; BVI rows. |
| **B2.7** | Hardy–Littlewood prime-pair correlations uniform near the square-root band. | TTPC surplus; near-incidence beyond the threshold. |
| **B2.8** | Subconvexity and growth near `Re s = 1`. | KKL horizon; the growth input `G`, the only source of interior gain for multiplicative positivity. |
| **B2.9** | Better de Bruijn–Newman upper bounds. | Shrinks the B1.5 region; corpus has `Λ < 1/8`. |
| **B2.10** | Near-line zero density on windows shorter than `T^{1/2}`. | Averaged positivity on windows `Γ^θ`, `θ < 1/2` (B3.7). |

### 2.3 Tier B3: open problems isolated by this research

No solution is known; none is proved RH-equivalent.

| ID | Question | Present boundary |
|---|---|---|
| **B3.1** | Physical-`L²` rate equality `polarRate = Δ`. | `Δ ≤ polarRate = groundRate ≤ 1/2`; form-norm rates equal `Δ`; bounded local off-line depth suffices. |
| **B3.2** | **Escape completeness as an energy split.** Does the cofactor log profile, after removal of the residue exponentials of `G(s) = ζ(s)(1/ζ(s+ε) − Re(1/ζ(1+ε)))/s` at the translated zeros, have pronic energy negligible against the row's? | Finite-window eigenstates = translated zeros with multiplicity; rank-one escape rows ⇔ translated zeros; nonresonant finite-rank decomposition; translation-Gram and Laplace forms [S]; prime-torus spectral reading; gauge mass; white noise survives every proved kernel constraint. |
| **B3.3** | Quantitative coercivity of residual/trace reconstruction in the receiver norm. | Algebraic injectivity; kernel `ℝ q_ε`; cofactor-graph closedness ⇔ a uniform estimate. |
| **B3.5** | **A section count on the correspondence surface.** An `h⁰` on normalized graphs of the scaling surface — nonnegative, growing, with Riemann–Roch proved without the sign — extending the base theta `h⁰`. | Base `h⁰` with RR and Mellin; normalized graphs with degree `δ/2` and the theorem of the square; Boolean counts and finite readings cannot pay; positive majorants give Bézout without RR. |
| **B3.6** | Signed shell flux along the moving prime-threshold ladder. | Birth jumps vanish; collar bound; frozen finite families fail. |
| **B3.7** | Averaged positivity on windows `H = Γ^θ` below the classical range. | Proved at `θ = 99/100`; `θ > 1/2` is W6; below needs B2.10. |
| **B3.8** | A nonlocal shared-budget calculus; quantitative cofinal two-tower saving. | Frustration and descent laws exact; the Rosati trace form is one budget, frustration its negative index. |
| **B3.9** | Arithmetic input on the residual heat region; source-selective cofactor repair. | Model geometry complete; no universal positive multiplier. |
| **B3.10** | Compatible oriented families; quantitative global-index bounds. | Common-endpoint classification; spline-orbit index ≤ 1 ⇔ RH. |
| **B3.11** | Sub-half-damping signed control of the size-cutoff forward interior. | Exterior paid; `ε = 1/2` bounded for every squarefree support. |
| **B3.12** | Order-uniform PA thresholds; decoupling rank from time (TH, HCF). | Fixed-order thresholds; coupled windows. |
| **B3.13** | Sharp successor constants: complex floor in `[−1/2, −1/3]`; zero-defect signs beyond conductor 3. | Odd shifts `1/3`, lag 2 `1/4`, exact; zero-defect signs have `f(2) = −1`. |
| **B3.16** | Is the paid ideal of `μ_ε` nonzero on escape? | A positive answer excludes white noise, not the translated-zero states. |
| **B3.18** | Equality case of collar capacity: a completed positive system with even `κ` and collar zeros of total multiplicity `κ/2`. | Odd `κ = 2r + 1` sharp. |
| **B3.20** | Signed near-coincidence cancellation at one height beyond aperture `½ log Γ`. | Single-height phase-selective law; near-incidence is gauge charge. |
| **B3.24** | **The gauge point beyond the threshold.** An unconditional estimate for a gauge-charged statistic of `μ` or `Λ` at the point `0` beyond the square-root threshold, better than the trivial bound. | Haar-typical twists meet every budget; the Möbius boundary separates the Liouville twin at PNT strength; the prime source is atypical only by its pole. |
| **B3.25** | **Elliptic localization.** A localizing arithmetic carrier — one that isolates an off-line reflection pair — whose positivity is unconditional and whose local symmetry there is not hyperbolic; or a theorem that every localizing positive arithmetic carrier is isotropic at off-line pairs. | Multiplicative correspondences are boosts off the line; separating isometries are boosts; non-localizing positivity is source-blind; coupled point-stable carriers are isotropic; the successor is unipotent. |
| **B3.26** | **The gauge-charged window ladder.** Beyond W8: do Weil-positivity certificates through the first `k` primes separate `ζ` from its sign twins with margins that survive as the aperture grows against the `e^A` cost of the off-line field? | Prime-free windows (`< log 2`) are weight-blind; the odd `181/500` window reads only the atom `2`; full-cone selection makes every single-atom perturbation fail at some aperture. |
| **B3.27** | **An arithmetic exterior count.** A count on the pair-sum spectrum of `ζ` — the `ℤ`-analogue of kernel counts on `Λ^k H¹`, which collide complex quartets into real off-line points — whose nonnegativity is proved by counting. | Over `𝔽_q` exterior counts force unitarity in every genus; determinant counts are blind to complex quartets; vertical symmetric squares preserve positive definiteness and do not force purity. |
| **B3.28** | **The Rankin–Selberg field.** Identify the polar data of the actual source `Λ ⋆ Λ`, with Gamma and polar terms and infinitely many zeros, with the field `E_j = Σ_{k≠j} m_k/(z_j − z_k)`; does a positivity of that source constrain `Re E_j` at the deepest off-line zero? | Finite polar sources: `Re E_j = 0` on critical configurations, `> 0` at the deepest off-line point with its reflection. |
| **B3.29** | **The regular part of the successor.** Quantify the successor defect `D_Λ` in the strip: the near-incidence information that the unipotent successor carries. | `D_Λ` holomorphic on `Re s > 0`; principal parts of `−ζ'/ζ` unchanged. |
| **B3.30** | **An arithmetic Stepanov method.** Auxiliary sections over `ℤ` whose forced vanishing bounds a spectral count. | Sparse Hecke annihilators need a lattice and never kill an off-line symbol; a characteristic-zero shifted-subgroup Stepanov lemma exists in `HTGeometry`. |

### 2.4 Settled questions

- **The theorem of the square over `ℤ`.** Normalized graphs of the correspondence ring obey it, unique modulo fibres, with degree half the defect; it holds on the golden datum and carries no budget. The Hecke scale map obeys none; scale addition is not ring addition.
- **The budget over `ℤ`.** Free, by the similitude law; its sufficiency at every scale is RH.
- **Positivity beyond isotropy.** Exists on non-localizing carriers, for every prime weight; on localizing multiplicative carriers it is impossible, by hyperbolicity; the successor forces nothing. What remains open is B3.25.
- **The base at receiver level.** Fixed tensor loss ⇔ RH; linear loss ⇔ the strip.
- **Successor coupling.** No successor prescription couples to Weil's correlation; the extensions of Weil's correlation are a box over the critical zeros; arithmetic successors and archimedean dilations live in different regularity classes; the successor reads exactly the continuous part of an archimedean dilation spectrum and never its atoms; whether singular continuous spectra are seen remains a side question.
- **The κ = 1 class.** `CompletedPositiveSystem 1 d` is `ℝ^× · ζ`.
- **Lefschetz receivers.** One prime suffices for one-sided bounds; short cycles suffice; one shift suffices; the local part on short cycles holds.
- **Amplification by family averages and moments.** Linear loss; zero loss iff flatness.
- **The cofactor Gram as a translation Gram of one profile** with Laplace form `G(s)`; rank-one escape rows are translated zeros.
- **Spectral synthesis in the blind ideal; coupled scale positivity on point-stable carriers; short-window selection at `Γ^{99/100}`; translated zeros as escape eigenstates on finite windows; depth homogeneity for moments, products and family averages; bare-FE and stable theta rigidity; collar sparsity `⌊κ/2⌋`; the absolute pole-order budget (false); interior multiplicative forcing beyond growth input (excluded); completeness of `ζ`'s invariants.**

## 3. The three questions to answer next

**Selection criteria.**

1. The question is weaker than RH, so it can be answered.
2. Either answer changes the frontier: a positive answer adds a mechanism; a negative answer is a sharp no-go naming the missing input.
3. Together the questions cover the three walls, each in its own currency.
4. The question respects the exhaustion map: it does not reduce to a mapped class.
5. The question addresses one of the three conditions a `ζ`-specific positivity must meet — localization, a local symmetry that is not hyperbolic or an independent polarization, sign-changing data — or the missing layer L5 of Weil's argument.

**Calibration that orders the questions.** Over `𝔽_q`, Frobenius polynomials localize at an impure eigenvalue pair and act there hyperbolically, exactly as Hecke polynomials do over `ℤ`. Weil still wins, because Rosati positivity holds on the whole correspondence ring for an independent reason, a polarization from Riemann–Roch on `C × C`; hyperbolic localization then turns that positivity into the vanishing of the off-line pair. Over `ℤ` every unconditional positivity found is a consequence of invariance and therefore isotropic. A forcing law needs a positive structure that is not a consequence of invariance. Two sources are conceivable: a localizer whose local symmetry is not hyperbolic (Q1), or a polarization from counting (Q3). Q2 asks whether any unconditional positivity of `ζ` can carry gauge charge at all.

### Q1. Elliptic localization: can an arithmetic carrier isolate an off-line pair without acting on it hyperbolically?

> *Is there an arithmetic operation that isolates one off-line reflection pair `{ρ, 1 − ρ̄}`, on a carrier where Weil's form is unconditionally positive, while its local symmetry at that pair is elliptic (a rotation or the reflection swap) rather than a boost — or is every localizing positive arithmetic carrier generated by correspondences that are hyperbolic at off-line pairs, hence isotropic there?*

- **Why.** Positivity constrains a fibre only where the carrier localizes. In the corpus, localization comes from polynomials in Hecke operators (Lagrange interpolation on separating symbols), and Hecke operators are boosts exactly at off-line pairs; positivity on such carriers is isotropy. Non-localizing positivity (aperture `≤ 3/10`) has full fibres and holds for every prime weight. Elliptic isometries cannot separate the two points of a pair (separation is hyperbolic), so an elliptic localizer must be non-isometric: an arithmetic operation that changes the local form while respecting the reflection.
- **Ingredients to test.** The functional equation (the reflection swap) combined with a non-isometric arithmetic operation; Poisson and Sonin self-dualities of the archimedean place; the Rankin–Selberg source, whose polar data at a zero are the field of the other zeros (B3.28); the regular part `D_Λ` of the successor (B3.29); affine correspondences, which have genus zero and act unipotently.
- **Selectivity test.** Fail on the `CompletedPositiveSystem 2 1` models, the complex fake and the Liouville twin; reproduce coupled isotropy for multiplicative carriers; state the length of the localizing operation (a separation at distance `δ` costs `≳ 1/(Lδ)`).
- **Outcomes.** *Yes:* the first unconditional positivity that is neither invariant-induced isotropy nor non-localizing, and a forcing input for B1.6 (B3.25). *No:* a universal hyperbolicity theorem: quadratic positivity is closed as a forcing mechanism over `ℤ`, and a proof must come from counting (Q3) or from rates (U1).

### Q2. Where does unconditional Weil positivity first become gauge charged?

> *For which aperture and which tests does an unconditional Weil-positivity theorem for `ζ` fail for a gauge twin of `ζ` (a sign flip of prime-power atoms, the Liouville twist)? First instance: does the odd window `[−181/500, 181/500]`, which reads only the atom at `2`, separate `ζ` from the twist with `Λ(2)` replaced by `−log 2`? Then: do window certificates through the first `k` primes keep a gauge-charged margin as the aperture grows?*

- **Why.** Every unconditional positivity theorem of the corpus is gauge blind: prime-free windows hold for every weight; positivity on nonnegative tests holds for every dominated twin; carrier positivity is isotropic; averaged positivity is shared by Haar-typical twists. A `ζ`-specific sign must live on sign-changing atoms. Below `log 3` the Weil functional reads only the atom at `2`, the certificate holds for every weight with `w(2) = log 2`, and for the Liouville twist it is undecided exactly on odd tests with negative correlation at `log 2`. Full-cone selection makes every perturbation of `Λ` at a prime-power atom fail Weil positivity at some finite aperture, so each twin has a finite failure aperture; the question is whether certified positivity of `ζ` reaches it.
- **Route.** W8 (a finite-aperture eigenvalue problem with a certified answer); then the minimal failure aperture of each twin, compared with W5's certified windows for `ζ`; then the scaling of the gauge-charged margin against the `4(A+1)²e^A N² Φ` cost of the off-line field (B3.26).
- **Outcomes.** *Separation at `181/500`:* the first unconditional positivity theorem true for `ζ` and false for a gauge twin, and a calibration point for criterion (iii) of §1.1 of the complete report. *No separation there:* the sign of the first prime is invisible at that aperture; the least separating aperture and the number of primes it reads become the measured threshold at which positivity starts to see arithmetic. *Margins that survive growth:* a gauge-charged positivity ladder, the first route into B1.3 that is not gauge blind. *Margins that collapse like `e^{−A}`:* a sharp no-go locating gauge charge beyond bounded apertures.

### Q3. A section count on the correspondence surface

> *Is there a section count `h⁰` on the normalized graphs of the scaling surface of `ℤ` — nonnegative, growing with the class, extending the base theta `h⁰` — that satisfies Riemann–Roch with a proof that does not use the sign of Weil's form?*

- **Why.** Over `𝔽_q`, Rosati positivity (L5) comes from counting: Riemann–Roch on `C × C` makes a class with positive self-intersection and positive degree effective, and the Hodge index follows. Over `ℤ` layers L1–L3 are free, so L5 is the whole difficulty, and the corpus has the pieces of the counting argument except the count: exact source RR as an identity, normalized graphs with degree `δ/2` and the theorem of the square, a base theta `h⁰` with RR and Mellin transform to `ξ`. What fails is the dimension: Boolean section counts (`h⁰ ≤ 1`) cannot pay unbounded fibre intersection, finite readings cannot supply Bézout, positive majorants give Bézout without RR.
- **Weaker-than-RH content.** Nonnegativity of `h⁰`, the RR inequality, and vanishing on classes of negative degree are three separate statements; only their conjunction gives the Hodge index. Each alone is a theorem about a construction, not about the zeros.
- **Calibration.** Reproduce Weil for curves with budget `2g`; on the golden datum and the complex fake the count must exist and RR must hold while the vanishing statement fails; reproduce the base theta RR.
- **Outcomes.** *Yes:* L5 reduces to a vanishing statement on the correspondence surface, an ampleness question with a counting meaning, and the arithmetic exterior count (B3.27) becomes the count on its exterior powers. *No:* a theorem that every section count on normalized graphs with RR is RH-equivalent, closing Weil's counting route over `ℤ` in this form.

The three questions are the forcing problem in each wall's currency: what positivity can see after localization (Q1, Wall 3 face 3.18 and Wall 14 face 14.17); whether positivity can carry the arithmetic sign at the gauge point (Q2, Wall 1 faces 1.3 and 1.18); and whether the missing layer of Weil's argument has a counting construction (Q3, Wall 14 faces 14.4 and 14.18).

**Considered and not chosen.**
- Escape completeness (B3.2): reduced to an energy split of one profile; either answer leaves U1 a rate problem or adds escape objects as targets, and neither supplies a forcing mechanism.
- Cost of complex contraction (W11): expected to be a no-go by a short density argument; a cost-free contraction would be RH.
- The arithmetic exterior count (B3.27): over `𝔽_q` exterior counts are counts on the Jacobian; over `ℤ` it presupposes the polarization of Q3.
- The Rankin–Selberg field (B3.28): an ingredient for Q1.
- Selection below the zero spacing (B1.4) is RH-strength; the gauge point beyond the threshold (B3.24) is Chowla-strength.

## 4. Would the B-tier obstacles require a new field of mathematics?

### 4.1 Assessment

No theorem shows that a new field is necessary. The corpus has a complete map of the known forcing mechanisms, each with a sharp limit, and it now knows which layer of Weil's argument is missing over `ℤ`:

- **Invariant quadratic positivity certifies blindness, half-blindness or isotropy,** because every multiplicative correspondence is hyperbolic at an off-line pair. Non-localizing positivity has full fibres and is source-blind.
- **Multiplicative positivity forces the boundary and its capacity, nothing more without growth.** In completed systems: the same capacity on collars of width `1/log T`; at `κ = 1` the class is `ℝ^× · ζ`.
- **Linear rigidity determines `ζ` but does not see zeros.** Zero location is nonlinear in the coefficient measure.
- **Pole order pays only inserted zeros.** Real pairs contract for free; complex quartets cost pole budget.
- **Multiplicative data see only gauge orbits; nonnegative tests see only the size of the source.**
- **Amplification over `ℤ` loses linearly** — moments, family averages, tensor products, relative powers.
- **Averaging over heights selects windows, not zeros;** a correspondence resolves heights only at the inverse of its length.
- **The successor never reaches the zeros:** it is unipotent on their polar fibres and sees only continuous archimedean spectra.
- **Weil's argument transfers except for its sign.** Identities, the theorem of the square and the budget are free over `ℤ`; kernel counts are blind to complex quartets; Rosati positivity, the sufficiency of the budget and a fixed tensor loss are each RH.

The missing ingredient is a **polarization of the correspondence surface of `Spec ℤ`**: a positive structure on the Hecke–archimedean correspondences whose positivity is a theorem about the structure (counting, or a non-hyperbolic localizing symmetry), not a consequence of invariance, and which sees the sign of prime-power atoms. Over `𝔽_q` this is supplied by Riemann–Roch and an ample class on `C × C`. Over number fields no existing theory supplies it: arithmetic intersection theory works on arithmetic surfaces fibred over `Spec ℤ`, not on a square of `Spec ℤ`, and the scaling-site geometry has a Riemann–Roch on its base while its Hodge index on the square is equivalent to RH. A new field is therefore likely required [R].

### 4.2 The field: arithmetic polarization

The corpus holds three parts of it. **Arithmetic Positive Duality** is the rigidity and capacity theory of positive Poisson pairs, with MPG as its boundary side and SBWF as its strip side. **Arithmetic Correlation Geometry** supplies the symmetry: the gauge torus, its charged and invariant statistics, the loss law. **Arithmetic Correspondence Positivity** supplies the correspondences: normalized graphs, the budget, determinant and Rosati degrees, local types at reflection pairs, the layer map of Weil's argument. What none has is the object that makes Weil's positivity a theorem: a polarization, with sections to count. The field the B-tier points to is their extension by that object, here called **arithmetic polarization** [R].

- **Phenomenon to explain.** Why the positivity of the explicit formula pairs a zero with its reflection `1 − ρ̄` (Rosati, elliptic, the functional equation) rather than with its conjugate (determinants) or its dilates (hyperbolic); why `ζ`, and not its gauge twins, its dominated twins or its pole-order-two relaxations, carries no off-line charge; why every positivity built from multiplicative invariance is isotropic.
- **Scope.** Positive structures on the correspondence surface of `Spec ℤ` — dilations (gauge invariant, hyperbolic off the line), affine maps and the successor (gauge charged, unipotent), the archimedean flow (hyperbolic), the reflection (elliptic) — with their sections, degrees, polarizations and localizing operations; the capacity of such a structure for intrinsic charge; its selectivity against twins and relaxations.

### 4.3 Criteria the field must meet

| Criterion | Test against the corpus |
|---|---|
| **Selectivity** | Distinguishes `ζ` from the whole battery W1: `CompletedPositiveSystem 2 1` pairs and quartets, pole-order-3 and strip-pole quartets, over-regular Beurling systems, the Siegel family, twisted boundary systems, the golden datum, the complex fake, `Γ_ℝ^d` solutions, signed self-dual combinations, dominated and flipped twins; survives every single-node perturbation `Λ + δ·δ_m`. |
| **Gauge charge** | Separates the gauge point `0` from its twins; uses sign-changing atoms, the archimedean pole or additive structure; fails on the Liouville twin. |
| **Localization** | Isolates a reflection pair; states the length of its localizing operation. |
| **Local type** | Its positivity is not a consequence of invariance under a symmetry that is hyperbolic at off-line pairs: either its localizer is elliptic, or its positivity comes from counting. |
| **Reflection pairing** | Pairs `ρ` with `1 − ρ̄` (Rosati traces), not `ρ` with `ρ̄` (determinants); sees complex quartets. |
| **Counting origin** | Positivity is a dimension or a cardinality, with a Riemann–Roch identity proved without the sign. |
| **Sublinear loss** | Contains a term that does not scale with its amplification; loses nothing to gauge or family Jensen. |
| **Joint use of invariants** | Uses coefficient positivity, the FE, the simple pole and strip holomorphy together; each proper subset has countermodels. |
| **Sees more than pole order** | Reaches intrinsic charge; reproduces the conservation identity as its relative case and the free contraction of real pairs. |
| **Non-circularity** | No interface field or premise contains the conclusion; objects constructed before their sign; zero-free-region transfers are not forcing. |
| **Uniformity** | Tails paid in a graph topology; aperture, height, rank, damping and window controlled together; exceptional sets below the zero spacing where individual zeros are concerned. |
| **Calibration** | Reproduces Weil for curves with budget `2g` and an ample class; exterior-count purity; the theorem of the square in genus one; boundary forcing and `⌊k/2⌋` capacity; dlVP optimality; the κ = 1 collapse and `5d < 9κ`; positive-measure rigidity; the Kronecker split. |
| **New partial results** | Results that are not zero-free strips: an elliptic localizer or a universal hyperbolicity theorem (Q1), a gauge-charged positivity (Q2), a section count with Riemann–Roch (Q3), escape completeness (B3.2), a capacity bound for an infinite class of systems not built by deformation. |

### 4.4 Questions it must answer

1. **What is the polarization?** Which class on the correspondence surface of `Spec ℤ` plays the ample divisor, so that the Rosati trace `τ(ξ ξ')` is positive for a reason other than RH?
2. **What counts sections?** Which `h⁰` on normalized graphs is a genuine dimension with Riemann–Roch (Q3)?
3. **Which localizer is not hyperbolic?** Which non-isometric arithmetic operation isolates a reflection pair with an elliptic local symmetry (Q1)?
4. **Where is the gauge charge?** At which aperture and on which atoms does positivity first separate `ζ` from its twins (Q2)?
5. **What is the exterior square of the spectrum?** The pair-sum spectrum `ρ_i + ρ_j` as an arithmetic object with counts (B3.27).
6. **What pays `ζ`'s own zeros?** A budget pays a hyperbolic pair only on a finite segment; which positive structure measures oscillatory payment and carries a capacity?
7. **How does the archimedean place enter?** The prime source is atypical only by its pole; how does a polarization see the pole and the Gamma factor?
8. **What are escape states?** The energy split of one profile (B3.2).
9. **How does an average become a point?** Which selection principle reaches below the zero spacing with a correspondence of length `≳ log T`?
10. **What is the base?** Which structure has a tensor loss independent of the power?

### 4.5 Tools it would develop

Built: the Fejér-tent pairing, Hamburger rigidity and its stability, lattice and `ℚ_{>0}` Bochner, Kronecker decomposition, induction from subgroups, sign characters, the quantum budget, the critical-jet topology and synthesis, the coupling matrix, gauge Jensen and family Jensen, ratio energy and the near-incidence form, normalized graphs and the similitude law, determinant and Rosati degrees, exterior counts over `𝔽_q`, the local form with its boost and isometry laws, the resolution law, the zero-contraction calculus, the translation-Gram and Laplace forms of the cofactor. Not yet built:

- **Section theory on the correspondence surface.** `h⁰` of normalized graphs; Riemann–Roch; vanishing in negative degree; the extension of the base theta `h⁰`.
- **Polarizations.** Ample-type classes for the Hecke–archimedean correspondence ring; Rosati positivity from ampleness.
- **Elliptic localization.** Non-isometric, reflection-compatible operations that isolate a reflection pair; their positivity laws.
- **Gauge-charged positivity certificates.** Weil-positivity certificates that read sign-changing atoms, with margins as a function of aperture.
- **Arithmetic exterior powers.** Pair-sum spectra with counts.
- **Oscillatory capacity.** A positive structure whose integer counts intrinsic charge, keeping dominated and oscillatory payment apart.
- **Escape-state analysis** of one profile through its Laplace form.
- **Selection lemmas** at the zero-spacing scale.
- **An arithmetic Stepanov method**: auxiliary sections whose forced vanishing bounds spectral counts.

### 4.6 Objects, language and mechanisms

| Layer | Content |
|---|---|
| **Objects** | The correspondence surface of `Spec ℤ`: scaling surface, Hecke ring with Rosati involution, normalized graphs, the archimedean flow, affine maps and the successor, the functional-equation reflection; reflection pairs with their local forms; polarizations and section counts; arithmetic Poisson pairs; completed positive systems graded by pole order and degree; boundary divisors and capacities; the gauge torus, gauge orbits and the gauge point `0`; dominated and sign-flipped twins; Lefschetz sequences and short cycles; carriers: blind, half-blind, left-blind, isotropic, non-localizing; cofactor profiles with their Laplace forms and escape states; coefficient systems over a base. |
| **Language** | It must distinguish: equality, receiver equivalence and directional transfer; source and receiver; gauge-invariant and gauge-charged; the orbit and the point; hyperbolic, elliptic and unipotent; localizing and non-localizing; determinant and Rosati trace; budget and sufficiency; local part and Lefschetz part; blind, half-blind and isotropic; inserted and intrinsic zeros; dominated and oscillatory payment; boundary and collar capacity; linear and sublinear loss; nonnegative and sign-changing atoms; averages, almost-every statements and individual zeros. |
| **Mechanisms to discover** | A **polarization law**: positivity of the Rosati trace from a section count. An **elliptic localization law**: positivity on a carrier that isolates a reflection pair with a non-hyperbolic symmetry. A **charged positivity law**: Weil positivity that reads the sign of prime-power atoms with a margin that survives aperture growth. A **capacity law for oscillation**: a bound on `ζ`'s own interior zero charge. A **completeness law** for escape. A **base law**: a fixed loss over a base removed by tensor roots. |
| **First milestones** | (1) W8: the first gauge-charged window, then its ladder (Q2). (2) An elliptic localizer or a universal hyperbolicity theorem (Q1). (3) A section count on normalized graphs with Riemann–Roch, or a no-go (Q3). (4) W11: the optimal cost of complex contraction. (5) W9: the loss law for the remaining amplification classes. (6) The energy split of the cofactor profile (B3.2). |

Each milestone is a theorem of a type the corpus does not contain: a polarization, an elliptic localizer, a charged positivity, a completeness law, rather than a blindness or receiver statement. Under APD's standard each must name its positive side, spectral side, gap and integer; under ACG's standard its gauge charge; under ACP's standard its layer of Weil's argument, the local type of its correspondences at off-line pairs and whether its carrier localizes.
