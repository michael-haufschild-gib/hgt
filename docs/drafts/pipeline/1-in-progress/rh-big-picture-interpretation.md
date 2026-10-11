# RH: the big picture of what the corpus has proven, and what it implies

- **ID:** rh-big-picture-interpretation
- **Stage:** 1-in-progress (living synthesis; read at the start of every RH cycle)
- **Sources:** STATUS.md (474 MUST / 221 CANNOT), rh-current-frontier-map.md (16 routes, 23 candidates),
  rh-killed-routes.md (27 retired routes, 101 class kills, 477 scoped mechanisms),
  cross-route-producer-synthesis.md (positivity sources P1–P10), krein-producer-loops.md (L1–L405),
  terminal-classification-two-doors (ULF-TERM-001), f1-object-forced-shape (ULF-F1-003),
  rh-goal-loop-opus-2026-09-29.md (483 cycles).

## 1. What is proven, by kind
1. **Equivalences (receivers).** Every route ends at the same statement. Examples:
   - RH ⟺ restricted Weil positivity `μ₀(a) ≥ 0` at every aperture (Bombieri–Yoshida) [L];
   - ⟺ `Λ ∈` Weil cone, which splits into existence (PBAP) and uniqueness (U);
   - ⟺ Krein–Langer index of the pole-free form `= 1` at every aperture (L366);
   - ⟺ finite-order slice signs; ⟺ Báez-Duarte `d_N → 0`; ⟺ `newmanConstant = 0`; and many more.
   - HF's Hodge index, RW's aperture positivity and TG's integrality index are **one integer**:
     `index(H_W|_B) = 1 + N_off(B)`, the number of off-line pairs resolved at aperture `B` (L366).
2. **Unconditional zero information** (all near `σ = 1`, or on average):
   - VK zero-free region `riemannZeta_ne_zero_vinogradovKorobov` [L];
   - 67.25% simple critical zeros and 83.62% distinct (Zeta23);
   - off-line moment `≤ 0.067V`; horizontal isolation; local zero counts;
   - Hardy's theorem; zero-free window `|t| ≤ 10.26`; Newman constant `< 1/8`.
3. **Unconditional positivity, small or soft only:**
   - `μ₀(½log 2) ≥ 1/10`, and `≥ 1/20` past the prime 2 [L];
   - PBAP on the nonnegative cone (L349, paper);
   - Weil-cone rigidity: Λ extreme and exposed, every regular perturbation fails (exact-primes gate) [L].
4. **The approximation side, complete** (MUST-787–793) [L]. At every aperture:
   - real-rooted ground states exist;
   - the ground level is `{P·G_a : deg P < d}` over one real-rooted generator, with multiplicity
     `1 +` (number of form-domain derivatives), and `d ≥ 2` only at parity crossings;
   - `W_a − μ_a` dominates a positive quadrature at the zeros of `G_a`.

## 2. The no-go structure (proved obstructions)
- **Gates** (frontier map): sharp endpoints · exact primes · rigidity not estimate · orientation (two-torsion,
  reflection-odd) · individual zeros · exponent not constant · cofinal source law · Mellin-diagonal blind ·
  holomorphic readers unquantized.
- **Walls** (core catalogue): √X-precision one-sided prime sums (wall 1, the terminus of every lane),
  |ζ|²-vs-log|ζ|, clustering, axis outside the zero set, no F₁ Frobenius, probability-cone, statistical, infinitesimal
  admixture, temperedness, oscillation–transport.
- **Terminal classification** (ULF-TERM-001): every producer shape is one of four theorem-closed kinds.
  These are fixed functionals; convergence in the strip; symmetries `s ↔ σ(s)`; two-factor presentations of ξ.

## 3. Interpretation
1. **RH is the vanishing of one integer, cofinally.** `N_off(B) = 0` for every `B` (L366). All analytic receivers are
   readings of this integer at some smoothing scale.
2. **There is no slack anywhere.**
   - `μ_a ≤ exp(−e^{2a})` (MUST-478) and `λ₂(Q₀) ≤ exp(−ce^{2a})` (L62);
   - `σ_prod ≥ ½` with equality only at Λ (L346–L347);
   - de Bruijn–Newman `Λ ≥ 0`.
   - RH sits exactly on the boundary of every deformation family. A proof must be an exact or extremal mechanism,
     never an estimate with margin.
3. **The only certificate is the zero set itself.**
   - The producer is Λ, unique among regular deviations, and its positive spectral measure is the zero measure.
   - Local zero-free certificates exist at every finite scale but cannot glue: a global producer must be singular
     at the zeros of an Euler product (L386).
   - Hence every unconditional producer route needs near-RH input (L398).
4. **Partial results do not interpolate.**
   - Zero-free regions improve the floor exponent by `o(1)` only (row 480); only a strip moves it.
   - Densities and averages are blind to individual zeros.
   - The RH step is a jump of `½` in an exponent, with no intermediate statements in the Weil/lag lanes.
5. **Consequence:** statistical or averaged tools cannot prove RH: pair correlation (Montgomery), moments, large
   sieve, Szegő asymptotics, mollifiers below θ>1, Bakry–Émery integrated curvature. They read the integer only
   through averages. The approximation side (CCM) is closed in Lean and moves RH only through the sign of `μ_a`.

## 4. What a proof must therefore be
- An exact, global, orientation-sensitive mechanism forcing the integer `N_off(B)` to vanish at every `B`, with input
  beyond Markov positivity and the PNT main term (Beurling systems share those and have off-line zeros: row 475).
- Known templates for "an integer forced to vanish by structure", each with its corpus status:
  - (a) Hodge index from geometry. HF, door 1: the missing surface. The arithmetic "easy half" is not free (row 468).
  - (b) Spectral realization by a self-adjoint operator. Its faithfulness is RH verbatim (CANNOT-462,
    `DeningerResolventCoreIsRiemannHypothesis`).
  - (c) An exact trace equal to the index, with an a-priori sub-unit bound. This is TG and door 2, and MUST-127
    requires it. The bound `B_base < 1` is explicit, but the source-side identity must hold at √X precision
    (CANNOT-461).
  - (d) Rigidity: existence plus uniqueness of producers (PBAP + U). The two decisive tests are computational.
- The forced shape of the missing object (ULF-F1-003):
  - infinite rank, with the scaling flow as Frobenius;
  - integrality on the Dirichlet-ring coefficients, never on eigenvalues;
  - no finite integral lattice carrying three Frobenii [L];
  - the single open datum is a geometrically produced Hodge positivity.

## 5. Working rule
- Choose each target from §4. Name which template (a)–(d) it advances, which forced-shape constraint it respects,
  and which gate it passes. Do not start from a borrowed tool.

## Log
- 2026-10-06 — created at user direction ("always start with the big picture, and interpretation of all we know and
  have proven in our lean corpus").
- 2026-10-06 (loop 484–486, first computations under the lifted ban).
  - U, the uniqueness of the producer, has a dual certificate, C-PIN: a prime-blind `ν = Ξ²ĥ` with `ĥ > 0`. By Gordan duality, C-PIN is infeasible exactly when a positive-off-Z crystalline separator exists. Separators are Dirichlet series with spectrum in `log ℕ_{≥2}`, holomorphic on `σ > ½`, with `Re ≥ 0` on the line off Z; the U-violators are among them.
  - Finite-level C-PIN is feasible with healthy margins once `ĥ` resolves the zero spacing (M ≤ 240). The corpus "Kronecker wall" was a resolution artifact, so the dual route to U is open.
  - The prime-blind LP has no universal extremal (cross-gaps 2.5e-6 to 1e-2), so there is no closed-form route to PBAP.
  - Atomic-on-Z producers are already closed in the corpus (`WeilConeCriticalZeroCarriedRigidity`).
- 2026-10-06 (row 488, MUST-794): external audit against the 2026 CCM literature (Connes arXiv 2602.04022; Connes–van Suijlekom CMP 2026; Silva Zenodo 2026). Their structural hypothesis, even-simplicity, is now discharged in Lean: even-sector generators are cross-rooted, and Ξ ≠ 0 on iℝ. The approximation template's single open step is the convergence (localization) of explicit even generators to Ξ.
- 2026-10-06 (row 496, MUST-796): the CCM receiver of MUST-795 was vacuous for polar ground states.
  - Cross-rooted zeros add positively to `Σz⁻⁴`, and the forced polar zeros `±i/2` exceed Ξ's budget by a factor of about 4·10⁵.
  - The corrected open input is `G_a/(z²+¼) → cΞ` on the strip (Lean receiver). Numerics at a ≤ 0.8 show it holds, with z²-deficit ≈ e^{−2a}/(4π²): the zero-density gap above `T* = 2πe^{2a}`, i.e. the same Nyquist law as μ_a.
  - Picture unchanged: approximation side closed except one convergence statement, which is RH-strength.
  - Methodological lesson: positivity of power sums on the cross detects vacuous receivers.
- 2026-10-06 (row 497, MUST-797): Connes's QW_λ has a real-rooted ground state at every λ, and a simple one is real-rooted, of either parity, with no hypothesis. The approximation template is now closed in Lean for both the polar and the unconstrained form, except the single convergence statement.
- 2026-10-06 (rows 496–508): the CCM approximation template has ONE analytic open core, the boundary (edge) mass of the restricted-Weil ground state at `x = ±a`.
  - Arithmetic-blind (proved): real roots [L], quadrature, multiplicity, monotone zero flow.
  - Equivalent faces of the edge decay: convergence, localization, zero domination, gap non-penetration, parity-simplicity (Connes's step 1 is RH-sensitive: planted off-line zeros force even/odd crossings with half-period π/(2t₀)).
  - Exact parity transfer: `Q(sign·f) = Q(f) ∓ 4H(f₊)`, H the Hankel form of the Weil kernel. The archimedean Hankel part is a negative Laplace kernel (favors even), the pole part is rank-2 positive and measures edge mass (favors odd).
- 2026-10-06 (rows 524–534): template (d), uniqueness U, after this segment.
  - Rigid in Lean (every Weil-positive system of the class is Λ):
    - finite type `Λ⋆a + μ⋆f + v` (WeilFiniteTypeUniqueness);
    - dilation series absolutely convergent left of the line (MUST-801);
    - deviations of absolute abscissa `< 1` (WeilAbscissaRigidity);
    - lacunary, dyadic and common-ratio supports;
    - integer-atomic spectra;
    - nonnegative notch-small systems with `T = 0`.
  - Remaining room for a second producer:
    - deviations at full PNT scale on both signs that are not multiplicative;
    - dilation series singular at `Re s = ½`, where counting would need Kac–Rice in place of Jensen;
    - infinite Möbius parts, where the realness defect sits at Riemann's `b = 2` capacity and needs ζ′ moments with uniform `n`-dependence.
  - The reverse harmonic sign `T ≥ 0`, i.e. `Φ_lam(1) ≤ ξ'/ξ(1)`, is the one-number form of U for nonnegative producers.
  - Existence (PBAP) is RH-strength, and every rigid class is excluded under ¬RH. So template (d) reduces RH to existence in a class not yet known to be rigid.
- 2026-10-06 (geometric/topological loop G1–G42, card `rh-geometric-topological-loop-2026-10-06.md`; MUST-802 [L]).
  - Four laws govern every geometric or topological mechanism:
    - balance: topological counts pair off-line zeros against saddles, folds, U-turns;
    - signature: every reality mechanism is a definiteness, a uniqueness, IVT plus a margin, or self-adjointness;
    - deformation dichotomy: isotopies carry no arithmetic; configuration-changing families put `ξ` on the RH boundary;
    - Euler rigidity: coupled multivariable Euler products have natural boundaries.
  - Uniqueness via hyperbolic contraction is now formal (Newton–Schwarz–Pick, MUST-802). It also needs a margin, which vanishes at near-collisions.
  - Consequence: the only mechanism class compatible with no slack and no analytic positivity is an EXACT geometric signature (template (a)), on an object whose incidence is multiplicative.
  - Exclusion list for that object (loop G42–G55): Arakelov `ℙ¹_ℤ`/`𝔾_m` (additive incidence); Hecke/Shimura surfaces (`ζ` only in Eisenstein/boundary cohomology, while Hodge index controls cuspidal parts; MUST-803 formalizes the CM-corner Hessian); hyperbolic geodesic kernels (no radial PD extension); convex-body mixed areas (Sylvester circularity); restricted Grassmannian/KdV (spectral); adelic solenoid (rank-one cohomology, Lefschetz `1−q`); scaling-site square (open in the F₁ lane). What remains: `Λ(n)` as a fixed-point count on a class-space quotient, with a non-spectral Hodge index.
- 2026-10-07 (row 536, MUST-804 [L]): the "dilation series singular at `Re s = ½`" room is closed for `A` absolutely convergent on `Re s ≥ ½` with a log moment. The mechanism uses no zero counting: the archimedean phase velocity `θ' ~ ½ log t` dominates, in mean, the `O(T log log T)` fluctuation of `log|ζ|`, so `Re A ≤ 1` on the line, and Phragmén–Lindelöf plus `A(1) = 1` give `A ≡ 1`. Remaining U-room: Möbius parts at `δ = 0` (they need discrete negative moments `Σ 1/|ζ'(ρ)|`), and non-multiplicative full-scale deviations. Existence stays RH-strength.
- 2026-10-07 (rows 530 and 537, MUST-801/806): U (uniqueness of producers) now holds for `Λ⋆a + μ⋆f + v` with `a` absolutely convergent past ½, `f` finitely supported, and `v` regular with bounded line values. A parallel session added the boundary class for pure dilations. Two mechanisms:
  - realness plus strip almost-periodic zero density;
  - the `|ζ|²`-weighted boundary inequality. The weight annihilates every zero; the leading functional is the Kakutani product of Poisson kernels on the Bohr torus, and the Weil normalization `A(1)=1` is its barycenter.
  - Reading: the `|ζ|²` notch annihilates `μ_Λ` identically, so it can certify uniqueness but never existence. Every U-proof is RH-blind by construction. Existence (PBAP), the RH core, needs weights that do not vanish at the zeros.
- 2026-10-07 (row 537, conjecture C538 "frozen real part"). For every integer-supported full-cone Weil-positive `λ`, the Weil boundary measure `μ_λ` has no absolutely continuous part; equivalently `Re D_λ(½+it) = θ'(t)` a.e.
  - It holds for Λ (under RH) and in every AP-structured class (MUST-800/801/804). Real supports violate it (the MUST-523 system has a.c. density `≥ 1/100`), so integrality must enter.
  - If true, `D_w = D_λ − D_Λ` has `Re D_w = 0` a.e. on the line. Reflection, plus pure-point control of the singular part, gives `D_w(s) = −D_w(1−s)`, and the MUST-524 Hamburger mechanism gives `w = 0`, i.e. U.
  - Heuristic (variance law): an integer `λ` with mean 1 has `Σ_{n≤t} λ(n)²/n ≥ log t` (Cauchy–Schwarz). Random-phase fluctuations of `Re D_λ` then exceed `½ log t` on a set of measure `≍ T^{1−1/(8κ²)}` with `κ ≥ 1`, which matches MUST-523's `κ = 1 > 1/8`. Only FE-frozen systems survive.
  - Consequence for strategy: template (d) can only reformulate RH. U is C538 plus Hamburger, and existence is Λ's own positivity (PBAP).
- 2026-10-07 (row 539, MUST-807 [L]): infinite Möbius parts are excluded from the Weil cone. If `Λ⋆a + μ⋆f` is Weil-positive with `a` and `f` absolutely convergent past ½, then `a = δ₁` and `f = 0`, under a log moment on `f`.
  - The mechanism is first-moment sign rigidity of `F` against `ζ` with `K!`-Möbius weights, which remove the diagonal `F(1)`.
  - Reading: the natural ¬RH repairs of `Λ`, Möbius parts whose `F/ζ` cancels off-line poles, can never be Weil-positive.
  - U-room left: regular `v` combined with infinite `f`, and non-multiplicative full-scale deviations. Existence (PBAP) remains the RH core.
- 2026-10-07 (row 540, MUST-808 [L]): U holds for the whole absolutely convergent finite-type class `Λ⋆a + μ⋆f + v`.
  - Structural law (Lean): Möbius mollification by `Π_{p≤K}(1−p^{−s})` de-tilts the `|ζ|²` Kakutani–Poisson functional to `(1−1/p)·Haar` at the primes `≤ K`. This is the exact mechanism by which mollifiers isolate Dirichlet coefficients at the `T log T` level.
  - With MUST-801/804/806/807, the `|ζ|²` method has exhausted its natural classes. What remains of U is crystalline (atomic producers / twins, L405) or non-absolutely-convergent. These are no longer gaps that boundary-average methods can reach.
- 2026-10-07 (row 545, MUST-810 [L]): U holds in the boundary class with a Möbius part. If `Λ⋆a + μ⋆f + v` is Weil-positive, with log moments on `a, f` at `½` and `Σ|v|n^{−½} < ∞`, then it equals `Λ`; `A, F, V` may have a natural boundary on the line. Past-½ analyticity entered the `|ζ|²` chain only through Cauchy estimates. U is now closed in every absolutely convergent class with log moments; what remains is non-absolutely-convergent or crystalline.
- 2026-10-07 (row 546, external audit). Template (d) is being developed externally: Johns (Oct 2026, preprint) studies positive solutions of the explicit formula with ζ's archimedean data and arbitrary positive prime measures. Its results:
  - LP duality: existence ⟺ a zero-free, prime-free positivity;
  - Conjecture U;
  - "criticality ⟺ purely atomic zero measures", which is C538 in their setting;
  - uniqueness near ζ's support via the Bondarenko–Radchenko–Seip (BRS) Fourier interpolation basis;
  - computer-certified near-criticality `κ* ≤ 1.15·10⁻⁹⁰⁶` through zero-killing certificates `Ξ²·(polynomial)`, i.e. numerical C-PIN.

  Reading: the shared open core is non-atomic zero mass (C538), and nobody has a proof of existence. The corpus already goes beyond them in the integer-node case (atomic producers via Hamburger, MUST-524). BRS gives the corpus an exact coordinate system: a producer is determined by its off-Z zero mass `μ^{off}`. The coordinates are `w(n) = π√n ∫U_{n²}dμ^{off}`, evaporation `½∫V_γ dμ^{off}`, and the constraints `∫U_m dμ^{off} = 0` for non-square `m`.
- 2026-10-07 (row 547, MUST-812 [L]). Prime-blindness has a sharp analytic threshold, the Carlson / Blaschke boundary of the node set `log ℕ`: no measure with `∫|w|e^{(π/2)|t|} < ∞` is prime-blind (even at the primes alone). `Ξ²` decays exactly at `e^{−π|t|/2}`, the archimedean factor matched to the pole of ζ at 1, so every C-PIN or magic-function certificate lives exactly on the threshold. Only the polynomial prefactor `|t|^{7/2}|ζ(½+it)|²` keeps it alive. This is the structural reason for "no slack anywhere" (§3.2) on the certificate side. It also separates degree one, which is exactly critical, from higher degree, where tempered prime-blind multipliers do not exist.
- 2026-10-07 (row 553, MUST-818 [L]; correction of rows 548–549). The polynomial "room" thresholds (`a < 2κ`, "ζ's pole factor gives room 9/2", "bounded C-PIN admissible") were artifacts of a max-modulus Jensen bound and are withdrawn.
  - True law: blindness at a divergent node set (primes) fails under every polynomial room. Blindness at log-dense nodes (all integers) fails under room `e^{K√|t|}` (Carlson). Counterexamples exist at `e^{Ct/log t}` [P]; conjectured boundary `∫ρ/t² < ∞`.
  - Reading: the certificate side keeps "exact criticality at rate `π/2`", but C-PIN certificates must be non-tempered. The "no slack" law on the certificate side is stronger than recorded: no certificate is a tempered multiple of `Ξ²`.
- 2026-10-07 (rows 550–552, MUST-815–817 [L]). The resonance method now applies to the whole Weil cone.
  - `Re ζ(½+it) > log t + K` infinitely often, unconditionally.
  - ζ-pole carriers `β·1 + v` and the pencil `βΛ + γ·1 + v` meet `W` at most in `Λ`.
  - Every `λ ∈ W`, with no regularity class, obeys the budget `Σ_{C⊆P}λ(∏C)(∏C)^{−σ₀}2^{−|C|} ≤ K₁ + K₂ log∏P`, so `liminf_{squarefree} λ ≤ 0`.
  - Reading: these are necessary conditions that `Λ` meets with a large margin. Resonance reads `λ` only on squarefree frequencies and is RH-blind. Template (d) adds no RH content beyond Λ's own positivity.
  - Audit: the budget, and MUST-815(ii), were already contained in the corpus `weil_multiplicativeToeplitz_bound` (sharp `log N` at `σ = ½`). New are the formal Ω₊ for `Re ζ` and the Hardy-zero half of the pencil.
- 2026-10-07 (row 555, MUST-821 [L]). The ζ-multiplicative pole carriers `βΛ + (1⋆m) + v`, with `m, v ∈ ℓ¹(n^{−½})`, meet `W` only in `Λ`. The residue share `M(1)` is forced to `0`: a positive share fails by Toeplitz resonance at a hybrid Euler point, a negative share fails at Hardy zeros. With MUST-801–810 this classifies regular pole carriers. The U lane is now exhausted in every regular class; what remains is non-regular (natural boundaries at the line, non-multiplicative full-scale deviations) or the existence core PBAP.
- 2026-10-08 (rows 557–558, MUST-823/824 [L]). Lee–Yang zero-gap law.
  - Any Lee–Yang datum affine in a field of frequency `λ` has a real zero in every window of radius `π/λ`, on any graph and with any couplings.
  - So a stability producer of Ξ can use only slow fields, `|log q| < π/γ₁ ≈ 0.222`. Integer or prime fields are excluded outright, and the integer-anchored Γ-chain (ALY) dies at its first site.
  - Reading: this is the Lee–Yang instance of the F₁ forced-shape law (ULF-F1-003). Integrality must sit on couplings or coefficients, never on fields or eigenvalues.
  - It matches the Weil-cone lane, where integer support (a coefficient constraint) is what U needs, and the frequencies (zeros) stay free. Across lanes, arithmetic enters as an interaction constraint, never as a spectral parameter.
- 2026-10-09 (rows 556–559, MUST-822/823 [L]): the approximation template (CCM) is now formally a single inequality.
  - If real-rooted full ground states `u_a` along `a_j → ∞` satisfy `∫|u_a|e^{(½+η)|t|} ≤ C|∫u_a|`, then RH (`riemannHypothesis_of_localizedFullGrounds`). No identification of the limit with `Ξ`, no convergence statement and no eigenvalue control is needed. Only positive frequencies (one-sided translates) enter, and the limiting eigenvalue is forced to 0.
  - New tool: one-sided Laplace atom rigidity. An `L¹` line function cannot mimic discrete spectral atoms lying above it. It turns any limiting Weil Euler–Lagrange identity into "the limit vanishes on the Xi divisor".
  - Reading: real-rootedness (flip extremality) and the eigen-equation are both free. Localization, i.e. strip analyticity of the transforms at rate `½+η`, is the whole RH content. It cannot come from exact symmetries of the compressed form (row 559).
  - Correction (row 562): for real-rooted Cartwright functions the strip growth is a functional of the modulus on ℝ (no Blaschke factors): `log|F(x+iy)| = a y + P_y⋆log|F|(x)`. So localization is a real-line statement: the minimizer's modulus follows the Γ-decay profile of Ξ up to the Nyquist height `e^{2a}`, whose Poisson mean exactly cancels the type term `a y`. The aperture–height law `log T* = 2a` is the archimedean rate `π/4` read through the Poisson kernel.
  - Weakest Lean form (rows 564–565, MUST-833): for even real-rooted ground states, localization can be replaced by a bounded inverse-square zero sum `Σ_ρ 1/|ρ|² = ∫t²u/∫u`, together with a mass ratio `∫|u| ≤ Me^{a}|∫u|`. Gaussian growth `e^{A(Re z)²}` along the strip is enough, because smearing the exact eigen-equation over shifts produces Gaussian tests whose tails are killed by the Paley–Wiener growth. So the CCM core is a statement about the low-frequency zeros: they must not drift to 0. Under ¬RH some hypothesis must fail along every aperture sequence. MUST-805 exhibits one mechanism: past parity crossings the ground state is odd, so its mass is zero.
  - Quantitative form (row 572, MUST-838): at a single aperture the zero sum controls the ground energy, `|μ_a| ≤ μ_max` once `a ≳ S`. So linear zero sums `S_a ≤ a/(200(K+2))` already force RH, with no limit argument. Read geometrically: RH follows if even real-rooted ground states have effective width `√(∫t²u/∫u) ≲ √a` instead of the trivial `a`. Under ¬RH the resonance has width `≍ a`, so a square-root saving in ground-state width decides RH. The method's floor is `S ≲ a`, where the Paley–Wiener growth `e^{a/2}` meets the Gaussian tail.
- 2026-10-09 (row 564, MUST-829 [L]). The certificate side of U has an exact second-order constant.
  - Integer blindness with room `e^{K|t|/log|t|}` forces vanishing iff `K < π/2` (Lean for `K < π/2`; extremal family for `K > π/2`).
  - Corpus conjecture C553 (`∫ρ/t² < ∞`) is refuted.
  - Reading: "no slack" holds at two orders. Rate `π/2` is Γ's decay matched to the pole of ζ. The constant `π/2` at scale `t/log t` is the half-plane angle seen through the narrowing that the density of `log ℕ` permits (`Σ1/(n log n) = ∞`).
  - C-PIN multipliers must grow like `e^{(π/2−ε)|t|/log|t|}`, and signed blind measures exist just above that. Growth considerations are now exhausted for U; only positivity (C556) can decide whether a certificate exists.
- 2026-10-09 (rows 568–571, MUST-830 [L]). Template (d), uniqueness half:
  - Selective exact-null tests reduce to blind ones below `e^{(π/2)|t|/log|t|}` (Lean). The explicit-PD-multiplier construction of C-PIN is excluded for every sub-threshold multiplier.
  - In BRS interpolation coordinates, a regular C-PIN would be the basis function `V_1` itself (row 569). Positivity needs second-order vanishing on `Z`, which `V_1` plausibly lacks (row 571, heuristic).
  - Reading: explicit uniqueness certificates are confined to non-regular limits. Template (d) now has neither a regular route to U nor a non-RH-strength route to existence (row 543).
  - Existence (PBAP) splits into tests blind by support geometry, which carry exponential slack (row 570, heuristic), and tests blind by cancellation, which carry all of RH.
  - Remaining templates: (a) a geometric Hodge index (the missing surface), (b) spectral faithfulness, (c) an exact trace with an a-priori sub-unit bound.
- 2026-10-09 (route-candidates loop, cycles 557–572; MUST-825–832, 837, 840 [L]). The Nyman–Beurling/chronological (CTF) family is now fully classified.
  - Kernels `e^{−t^a}`: integer dilates of the defect are dense iff `a ≤ 1`, the Carlson rate `π/2` (MUST-840). For `a > 1`, RH ⟺ membership of `e^{−t^a}` (MUST-837, explicit sinc separator built from an off-line zero). For `a ≤ 1`, RH ⟺ unit-bounded coefficients (MUST-831).
  - Budget dichotomy: the coefficient price is bounded or `≥ exp(ε^{−2})`. Integral `{0,μ(k)}` rows suffice (MUST-832). Möbius sign constraints are invisible (cycle 572, paper).
  - Reading: in this family the whole RH content is the `ℓ^∞` size of the approximating coefficients. Support, signs, integrality and Euler-product structure carry none of it; the Γ weight decides only where the content sits. The family's producer is "1/ζ is boundedly summable on the line", i.e. the near-line behaviour of the zero set. No input from inside the family can reach it, so the family is a receiver and lies outside templates (a)–(d).
- 2026-10-09 (loop row 578, MUST-842 [L]): the CCM ground-state receivers reduce to one scalar, the low-frequency share `|I_{a/40}(F)|/‖f‖₁` of the ground transform. Parity, real roots and zero sums are not needed: Paley–Wiener growth plus the zero-free window `|Re γ| > 9` controls the zero side at Gaussian width `≍ a`. Under ¬RH the very negative ground states must oscillate at the zero ordinates. So the CCM obstruction is spectral localization of the ground transform away from frequency `0`, and edge growth is secondary.
- 2026-10-09 (loop rows 579–581, MUST-843/844 [L]):
  - The low-frequency share has a continuous rate law: a share decaying like `e^{−ηB}` gives `|Re ρ − ½| ≤ max(0, η + ½ − 165c/2)/2` through the sharp Bombieri–Yoshida cap.
  - Shape receiver: nonnegative symmetric-decreasing ground states (the shape of `Φ`) force RH, while positivity alone misses by `e^{a}`.
  - Every positivity mechanism for the ground state (Perron–Frobenius, Markov/Lévy reading) runs into the rank-two pole block. That block carries the PNT main term, so the shape question is the prime fluctuation again (rows 377–378, 475–477).
- 2026-10-09 (route-candidates loop, cycles 578–603; MUST-846 [L]). The CTF family realizes template (d) internally, with the uniqueness half proved.
  - U (unconditional, MUST-846): bounded producers are unique. Rows bounded by `C` with heat residual → 0 have `a_n → μ(n)` pointwise. Mechanism: the large-`t` end of `L²(0,∞)` reads the Lambert residues of `1 − ζA` one at a time. So support, signs and initial segments are forced.
  - Existence is RH (MUST-831): μ must be boundedly summable on the line, equivalently the sharp Möbius errors stay bounded along a subsequence (MUST-827).
  - Reading: this parallels the Weil-cone picture (U proved in every regular class, existence = Λ's own positivity). In both families the arithmetic object is forced by rigidity and RH is its existence as a bounded or positive producer. A uniqueness theorem cannot carry RH content in either family. Every remaining lever is an existence mechanism: a positivity or a summation method for μ at √ precision.
- 2026-10-09 (rows 586–588c, MUST-845 [L]). The uniqueness certificate (C556) is ζ-free.
  - A test `ĝ = Ξ²R` is blind at every `log n`, `n ≥ 2`, iff `Ψ_R = 𝓜^{−1}[G²R]` (`G = s(s−1)Γ_ℝ/2`) vanishes on `ℕ_{≥2}`: `ζ²` enters as `Σd(m)m^{−s}` and leaves through `μ⋆μ` (`logNode_blind_iff_certKernel_vanishes`). The certificate growth law then holds without the `|ζ|²` weight of MUST-830.
  - Reading (rows 588–588c, paper): exact-null tests of order `k` (`Ξ^k Q`) are fixed points of ζ^k's Voronoi involution vanishing on `ℕ_{≥2}`, with nodes `n^{1/k}` in the chart.
    - Order 1 is subcritical: many signed certificates, none positive.
    - Order 2 is critical, RV-type at `√n` but for the hyperbolic `K₀/Y₀` transform of `d(n)`, so at most an interpolation family. Positivity is decided against the degree-3 twin rosettes.
    - Order ≥ 3 is overdetermined.
  - So U's dual certificate lives exactly in degree 2, the last rigid degree (`V₂ = ℂζ²`). An RV-type interpolation theorem for the `d(n)`-Voronoi transform (not in the literature) would reduce C556 to the sign of one function.
- 2026-10-09 (cycles 611–613; MUST-848, MUST-850 [L]). Every criterion family proved so far splits into a free half and an RH half:
  - Weil cone: summation free (compact tests), positivity is RH. U (uniqueness of producers) holds in every regular class.
  - CTF (Γ-weighted Nyman–Beurling): positivity free (triangle inequality, MUST-848), Möbius summation is RH. Uniqueness is free for bounded producers (MUST-846). Existence (a bounded producer) is RH.
  - Classical Báez-Duarte: uniqueness is free with NO budget (MUST-850). Every approximant obeys `|ĉ_n+μ(n)| ≤ (Σ_{d∣n}(2d+1))·dist` via the exact step form `uR(u) = 1 − Σ_k c_k{m/k}` on `[m,m+1)`. Existence (distance → 0) is RH.
  - CCM: real-rootedness and the eigen-equation are free; localization is RH.
  - No `ℓ^p` formulation (`p < ∞`) of the summation-type families exists, since Möbius rigidity gives infinite `ℓ^p` mass (C611). The summation families (`ℓ¹–ℓ^∞`) and the positivity families (`ℓ²`) are therefore distinct types with no interpolating formulation.
  - Reading: RH is always the existence of a nice object whose uniqueness is already free. No existence mechanism that does not presuppose the object (compactness, randomness, fixed points, Tauberian transfer, self-improvement) survives (C606/C607). The missing input is an existence theorem from positivity or geometry, in agreement with §4 template (a).
- 2026-10-09 (rows 585, 597–598; MUST-851 [L]). The CCM split, made exact:
  - Free half: the truncated Riemann kernel is a near-null vector, `|Q_b(v, Φχ_{b−w,w})| ≤ C(1+b)Φ(b−2w)‖v‖₁` for every form-domain `v`. Inputs: the radical of `Φ″` with two integrations by parts, and the edge layer (pole lag, sparse prime sum, archimedean `O(b)`).
  - RH half: the ground state's overlap with `Φχ`. Positivity plus `‖x‖₂ ≤ e^{b}‖x‖₁/6` gives overlap `≥ Φ(b−2w)‖x‖₁/2`, hence `|μ_b| ≤ C(1+b)` and RH. Without signs the overlap receiver is nearly a reformulation: expanding the near-null vector in eigenvectors, the overlap is small exactly when `μ` is very negative. Under ¬RH the resonance ground state is orthogonal to `Φ`, because its transform sits at the off-line zero where `Ξ` vanishes.
  - Reading: in CCM, positivity (Perron–Frobenius) is the only mechanism that forces overlap without spectral input. Its obstruction is still the rank-two pole block carrying the PNT main term.
- 2026-10-09 (loop rows 614–629; MUST-852, MUST-853 [L]).
  - CTF is now sharp on both sides. Bounded rows with error ε are Möbius exactly on a prefix of length Θ(log 1/ε), the height window the Γ weight resolves (MUST-846 lower bound, MUST-853 upper bound). Beyond the window, high-pass (dilation-difference) directions are free. CTF existence is therefore a low-pass window problem, and its RH content sits in strip-singular dual functionals (row 621: Möbius inversion over multiples fails exactly by off-line residues).
  - Real-rooted producers form one class. Lee–Yang chains with complex fugacities (MUST-852: real-rootedness needs no ferromagnetic positivity), CMV/OPUC, canonical systems, quantum graphs and divisibility trees are all unitary/HB producers, universal in the LP closure. Each is constrained by six laws:
    - slow (harmonic) fields for height covariance;
    - transparency or a turning point: uniformly small fugacities freeze the phase (MUST-820/823's frozen phase), while a potential growing like `e^{u/2}` in log-scale creates a WKB turning point `k* ≍ z²` with a moving pivot (row 637: the Riemann–Siegel chain at `c_k = κ(k+2)^{−½}` is a lattice Pólya `K_{iz}` model);
    - no mean-field component, since by `Λ ≥ 0` every Curie–Weiss/Gaussian-average step is a heat flow;
    - no unitary Euler factors of modulus `p^{−½}` (row 625);
    - quenched, not annealed (row 628);
    - harmonic free spins degenerate on the divisor lattice with zero zeta `π^{−s}ζ(s)²`, whose principal part matches Ξ's (row 616).
  - The single open core of this class is an arithmetic coupling law that resolves the divisor lattice (`ζ²`) into Ξ's zeros (`ζ′/ζ`) without passing through a heat flow.
- 2026-10-09 (rows 631–640; MUST-854/856/857 [L]).
  - The free/RH split recurs inside the unitary producer class.
    - Free: real-rootedness (MUST-852/857). Archimedean phases are exact Whittaker connection coefficients of continuum Dirac systems with exponential mass (row 640). Field density is pinned to harmonic (row 639, with the parallel field-density budget).
    - RH: the arithmetic, i.e. whether integer discreteness (Poisson resonances) produces ζ and not merely a lattice regularisation of the Γ-phase.
  - Where ζ sits: on the divisibility tree, Euler products are root susceptibilities (coupling variable, row 632), where no reality theorem exists (row 633). Lee–Yang controls only field variables. Unitary producers cannot carry Euler factors of modulus `p^{−½}` (MUST-854).
  - Both Nyman–Beurling criteria now have formal two-sided uncertainty laws (MUST-846/853 CTF `Θ(log 1/ε)`, MUST-850/856 BD polynomial). Uniqueness is a window statement, and existence is approximation on that window.
- 2026-10-09 (rows 641–645): the Lee–Yang class reduces to a trilemma.
  - The field-density budget forbids parallelism (row 645), so producers are one-dimensional in log scale.
  - For a one-dimensional chain with fields `n^{−β}` and fugacities `n^{α−1}`, the turning point is `x* = (z/2κ)^{1/(α+β−1)}` (WKB).
  - Harmonic density (`β = 1`), critical-line weights (`α = ½`) and the Riemann–Siegel balance (`x* ∝ z`) are pairwise compatible but never all three (row 644).
  - Matching `S(T)` needs log-discrepancy of the site Schur phases (row 641), and only the turning-point regime meets that rigidity budget a priori (row 642).
  - Reading: the Lee–Yang route realises either the critical line or the AFE balance, never both. Its last escape routes are non-WKB lattice resummation or non-power profiles.
- 2026-10-09 (Opus loop rows 606–613b; MUST-824 addendum, MUST-860 [L]).
  - The Lee–Yang field-density law is formal: every producer of Ξ in the class has field density at most the `Γ(s/2)` density, `log(T/2π) − 1 + C/√T`.
  - Complex-fugacity chains with constant fields are exactly Szegő (OPUC) recursions, with `Z` the paraorthogonal polynomial (algebraic check). With site-dependent fields they are discrete Krein systems. A chain producer of Ξ is therefore a Krein/de Branges inverse problem.
  - At first order the doubled-harmonic chain is the Eisenstein constant-term shape, with an explicit `κ²H²e^{|κ|H}` tail [L].
  - The pole is the detector. Fejér/box tests decide RH by Landau (row 608), but polar profile-monotone tests are blind (row 612). Polarizing at the far edge is forbidden by convex order. Polarizing centrally costs the prime-free Weil energy per unit of pole mass, which swamps every zero contribution.
  - So monotone-cone detection needs the exact `e^{U/2}` cancellation between the pole and the PNT main term: wall 1 again, now as a convexity statement.
- 2026-10-09 (rows 646–665; MUST-858/860, CANNOT-497).
  - **Unitary producers read ζ as a phase modulation, never as a zero carrier.**
    - Chains are self-dual Lee–Yang data (MUST-858) and unimodular chains are free spins (MUST-860).
    - At first order the doubled-harmonic chain is the Lagarias–Suzuki shape `2cos(xℓ)+2κRe[y^{ix}ζ(1+2ix)]`.
    - The count condition (`c·ρ = n²` at the turning point) and the critical-line Born condition (`c·ρ = n^{½}`) are incompatible for every profile.
    - No Born window at `Re s = ½`: the expansion parameter `κ√log M` cannot be both small and large.
  - **LP-maximality (CANNOT-497, paper; Lean brick `FirstOrderFilterVanishingIntervalBound`).**
    - Ξ ∉ φ(D)·LP for every LP symbol φ with a (non-exceptional) real zero. With Newman (Gaussian), every non-translation LP operator is excluded. The statement is unconditional, since under ¬RH it is trivial.
    - Mechanism: invert one first-order factor, an RC low-pass filter. A real-rooted pre-image must vanish in every Ξ-gap, but filtered Hardy `Z` has macroscopic mean square, while `∫ℓ²Z² = o(T)` (gap moments plus Hardy–Littlewood/Ingham).
    - Reading: RH, if true, is barely true in every LP direction. No producer is a regularisation of a real-rooted object.
  - **Mean-square versus pointwise (rows 663, 665).** Flat-spectrum and gap-moment tools see densities only. Every unconditional pointwise-exact tool (Rouché, Landau, Carlson–Pólya, 3-4-1 positivity, Maass–Selberg) is anchored at the 1-line (the pole at `s = 1`, Euler convergence). Every exact `½`-anchor is RH-strength or known false (one-sided Mertens/Pólya bias). This is Lesson L from the operator side.
- 2026-10-09 (rows 666–682; CANNOT-497 extended; seven Lean modules for its deterministic half).
  - **LP-maximality covers every LP symbol with a real zero.** The degree-one RC-filter argument works for any such symbol. With Newman, Ξ is maximal in the LP-operator order, and Pólya's `ξ*` is no LP operator away from Ξ.
  - **Window laws everywhere.** Every finite-order positivity sees zeros only below a height that grows with its order:
    - Schoenberg `PF_k` of the real-axis kernel `FT[1/ξ(½+τ)]` (row 681);
    - Weil positivity on `[−a,a]`;
    - CTF at error `ε` (`Θ(log 1/ε)`);
    - inertia with bounded Fourier support (Zeta23).
    RH is the passage to the limit, so a proof needs a mechanism that is uniform in height.
  - **Free versus RH positivity in one kernel.** `Λ = FT[1/ξ(½+τ)]` is Bochner-positive definite unconditionally, while Schoenberg total positivity is RH. This is the corpus's free/RH split once more.
  - **Near-line core = band coupling.** Missed crossings would need the self-dual balance-point band of the Riemann–Siegel sum to override the main band locally. An independence model predicts that at a positive proportion of zeros (contradicting Zeta23), so the bands are coupled. The coupling is multiplicative and statistical, not an exact AFE identity (rows 670–671).
  - **Candidate audit.** PBM, HJ, SEC and EGC reduce to von Koch counting, the seam `|n^ρ|` vs `|n^{1−ρ̄}|`, or zero-free contour bounds. MSC's transport must mix Dirichlet coefficients across `n`: power riggings are excluded by the corpus and LP multipliers by CANNOT-497, which leaves the NB/mollifier family.
- 2026-10-09 (rows 693–695; LP-maximality closed for all real-rooted polynomial symbols [L]).
  - **Zero slack in every LP direction is a theorem.** In Lean: Newman (Gaussian), every real-rooted polynomial symbol, and Ki–Kim–Lee effective reality. For a curve over `F_q` the analogue has slack, because the minimum zero gap is positive. So RH for ζ is a rigidity statement, and a proof must be exact and uniform in height.
  - **The Gaussian ceiling is `1/√3`** (heuristic; the AFE-half optimum uses length-`t` halves, beyond the mean-value range, and inside that range the yield is `½`). Two counts of real zeros meet at the same constant:
    - the Kac–Rice share for a Gaussian function with Z's flat spectrum;
    - the best Hermite–Biehler count from a smooth AFE half `ζ = A + χA*`, which equals `1/√3` in the random model, attained by the linear log-taper `½ − (√3/2)y` (row 695).
  - Second-moment, Gaussian-level information therefore caps at `1/√3`. Zeta23's `0.6725` comes from arithmetic: prime pair correlation via the explicit formula at bandwidth `λ ≤ 1`. Its `H(λ) = 2 − 1/λ − λ/3` peaks at `λ = √3` with value `2 − 2/√3 ≈ 0.845`, and the `⅓` is the same flat-spectrum second moment.
  - Reading: all the way to 100%, the content of RH lies in correlations beyond pairs, i.e. in the unitary (eigenvalue) structure that the CUE model has by construction. Any route must manufacture that structure; neither second moments nor finite-bandwidth explicit formulas contain it.
- 2026-10-09 (rows 700–705; MUST-871, cosine family [L]). **Zero slack measures gap irregularity, not exactness.** This refines the 693–695 entry.
  - **Finite-order slack.** `cos(hD)Ξ` acquires finite-order LP slack for every `h > 0`; its spectrum is top-heavy (`cosh` weights), so its zeros become Gram-regular.
    - `Ξ` has none: its flat low-frequency theta mass is the signature of irregular, GUE-like spacing.
    - Any LP function whose zeros are dense (density → ∞) and irregular at the scale of the mean gap should be LP-maximal by the same Poincaré argument.
  - **Heat slack.** Gaussian (heat) zero slack holds along the whole family (row 705), as Rodgers–Tao's pair-correlation reading predicts.
  - Corrected reading: zero slack does not show that RH must come from an exotic exact mechanism. It shows that `Ξ`, if LP, is a typical dense-and-irregular LP function sitting on the LP boundary, so every perturbative proof (`Ξ` near something LP) is dead.
  - The positive requirement is unchanged: a structural, height-uniform, divisor-faithful mechanism. That is the corpus's global positivity/unitarity shape, with no margin to spend.
- 2026-10-09 (correction to the previous entry; `cosineShift_heat_threshold` [L]).
  - **Heat slack carries no information about zero statistics.** For every `h ≥ ½`, `Λ_{dBN}(cos(hD)Ξ) = 0` exactly and unconditionally, yet those functions have Gram-regular zeros: `Re ξ(½+h+it)` with `\|ζ\| ≍ 1`.
  - The corpus Newman mechanism (`DeBruijnNewmanNonnegative`) is a Bohr phenomenon: at height `T` the damped function is modelled by the Gaussian-weighted Dirichlet series `F_τ`, and its zeros reappear at `Re s ≈ τ log T`. Any Dirichlet-modulated theta transform has `Λ ≥ 0`.
  - So the claim "heat slack, as Rodgers–Tao's pair-correlation reading predicts" is withdrawn.
  - Finite-order slack still separates regular zero sets (`h > 0`, slack) from irregular ones (`h = 0`, rigid).
  - Net reading: `Λ = 0` together with LP is achievable unconditionally by natural ζ-built functions. RH asks for it at the single member `h = 0`, where finite-order rigidity also holds.
- 2026-10-09 (Opus loop rows 637–644; MUST-872, 874–877, 879 [L]). **Exact receivers split into RH plus a multiplicity law.**
  - Báez-Duarte: `liminf d_N² log N ≥ Σ_ρ 2m_ρ²/|ρ|²` over all critical zeros. Multiplicity sits in the constant, through the Legendre endpoint extremal `∫₀¹p_m² = 1/m²`. The rate at the simple-zero constant implies RH ∧ simplicity (MUST-876).
  - Möbius Hilbert form: `E_N = Ω((log N)^{2m−1})`. Multiplicity sits in the log exponent.
  - Liouville: `J ≥ −C√t log^k(1/t)` implies RH ∧ critical orders `≤ k+1`.
  - Reading: the free/RH split has a third summand. Power-lossy (ε) forms are RH-equivalent. Log-lossy or constant-sharp forms are RH ⊕ (a multiplicity bound), and the simple-zero forms are RH ⊕ SZC. A producer aimed at a sharp rate must see multiplicities, so sharp-rate targets are strictly harder than RH. Target the ε-lossy forms.
  - Which receivers read multiplicity. The grading occurs exactly in `1/ζ`-type receivers: Báez-Duarte (approximating `1` by `ζ·P`), the Möbius Hilbert form (`Γ/ζ`) and Liouville (`ζ(2s)/ζ(s)`). There a zero of order `m` is a pole of order `m`, which costs `log^{m−1}` growth. `ζ′/ζ`-type receivers are multiplicity-blind, since a zero of order `m` is a simple pole with residue `m`. These are Weil positivity, the lag function `Φ`, Li coefficients and the CCM form. Strategy reading: exact laws are RH-equivalent only on the `ζ′/ζ` side; on the `1/ζ` side they overshoot to RH ∧ SZC unless ε-lossy.
- 2026-10-10 (Opus loop rows 676–685; CANNOT-500/501, MUST-882–884 [L]). **Abscissae carry the zeros only for signed, pole-free sources.**
  - Nonnegative Dirichlet series (`Λ`, `Λ/log`, `1_P`) converge exactly where they converge absolutely, so their abscissa is 1 unconditionally. The DR claim ("`Σ Λ(n)n^{−s}/log n` converges on `½ < Re s < 1` iff RH") and the PBM claim (the same for `Σ_p p^{−s}`) were false.
  - The positive survivors are the pole-regularized series `Σ ((Λ(n)−1)/log n) n^{−s}` (`log ζ` minus `Σ n^{−s}/log n`), `Σ (1_P(n) − 1/log n) n^{−s}` and `Σ (Λ(n)−1) n^{−s}`. Each has abscissa of convergence `½ + α` exactly when ξ is zero-free on `Re s > ½ + α`. This is consistent with the corpus `zetaZeroAbscissa` exponent laws.
  - Reading: the pole at `s = 1` is the whole monodromy. Once it is subtracted, prime, `log ζ` and `ζ′/ζ` sources carry the same exponent, so none is an independent producer. Every Landau-type positivity mechanism is pinned at `σ = 1` by that pole (Lesson L again).
  - **Strict multiplicity grading (MUST-884).** `M(x) = o(√x(1+log x)^a)` gives RH and every critical order `< a + 1`. So convergence of `Σ μ(n)n^{−½}(1+log n)^{−a}` at the single point `s = ½` is a receiver for RH ∧ simple zeros when `a ≤ 1`, and `Σ μ(n)/√n` diverges unconditionally. One-sided ε-lossy Liouville bounds equal RH exactly (MUST-882); only log-scale forms see multiplicity.
  - **Markov horizon.** The restricted Weil form is Markovian on aperture `a` iff `2a ≤ log ρ` (`ρ` the plastic number). The corpus no-go was aperture-free and vacuous at small apertures; the sharp form is now Lean (`satisfiesBeurlingDenyOn_screwEvenForm_iff`). Beyond the horizon, Perron–Frobenius positivity of ground states must be spectral (HF L364–L366, C365), not local.
- 2026-10-10 (Opus loop rows 691–707; MUST-888–896 [L]). **Dilated denominators give contractions, not producers; Li coefficients follow the window law.**
  - **Dilation cascade.** For an integral Euler-product receiver `∏ζ(ks)^{b_k}` with some `b_k < 0`, `k ≥ 2`, a power bound only forces the implication `ζ(ρ) = 0 ⇒ ζ(ρ/k) = 0`. A pole at `ρ/k` can be cancelled by the numerator. With reflection this gives the contraction `z ↦ 1 − z/k`, whose orbit converges to the real fixed point `k/(k+1)`, where `ζ ≠ 0`. Branching IFS versions work the same way (`riemannZeta_ne_zero_of_branching`). The exponent law is therefore exact only up to the cascade attractor: squarefree `Θ ≤ 2/3`.
  - **Smoothing is necessary and sufficient for faithfulness.** Sharp counts overshoot RH by a lattice-point problem (squarefree `x^{¼}`). A weight with zero-free Mellin transform (Γ) removes it, giving RH ⟺ `Σμ²(n)e^{−nt} = (6/π²)/t + O(t^{−¼−ε})` and the quasi-RH ladder: zero-free on `Re s > 1 − 1/k` ⟺ a `1/k²` saving in the smoothed `k`-free count.
  - **No rung is cheap (row 706).** The saving on rung `k` is the smoothed Mertens bound at scale `t^{−1/k}`, reweighted by `h(x^k)`: the Littlewood equivalence after a change of variables.
  - **Li growth law (row 707).** The negative Li coefficients grow exactly at the rate `max_ρ max(|w_ρ|, |w_ρ|⁻¹)`. Since that excess is `≍ |1 − 2β|/|ρ|²`, a Li bound at a fixed exponential rate `1 + δ` is RH below height `≍ δ^{−1/2}`. Li positivity is therefore another window law, with horizon `√n`. The sign condition at all `n` is the height limit, not a global positivity, which is consistent with the `ζ′/ζ`-side multiplicity blindness: the Li receiver is a radius.
  - Reading: every receiver in this segment is a change of variables on the same zero set: dilations, smoothing, Cayley transform. None manufactures a constraint the divisor does not already carry. The producer gap is unchanged.
- 2026-10-10 (Opus loop rows 708–717; MUST-896–898 [L]). **Every receiver is a cost-weighted reader of the zero hull; only dilation changes height.**
  - **Horizon taxonomy.** A receiver at scale `L` reads the zero set through a height cost `c(γ)`. A zero `β + iγ` is visible when `(β − ½)L ≳ c(γ)`:
    - sharp sums (Perron): `c ≍ log γ`;
    - Γ-smoothing: `c = π\|γ\|/2`, so the error exponent is the Legendre-type transform `u(L) = inf_ρ((1−β)L + π\|γ\|/2)`, the support function of the lower convex hull of `{(\|γ\|, 1−β)}` (row 717);
    - Li (row 708): excess `≍ δ/γ²`, horizon `√(n/δ)`. Conformal maps of the half-plane force this `γ^{−2}` compression, so absolutely convergent power-sum receivers cannot have a uniform horizon.
  - **Partial discharges follow the parametrization.** Horizon-parametrized receivers (Li rate `r`) are partially discharged by verified bands: the corpus `γ² ≥ 431/2` gives the unconditional Li rate `432/431`. Width-parametrized receivers (exponents) are discharged only up to the zero-free region at height `≍ L`. Rows 715–716 prove near-power savings `exp(−cL/(log L)^{2/3+})` for the Abel-smoothed Möbius sum and every `k`-free rung, which tend to exponent 0.
  - **Height changes only through `n ↦ nᵏ`.** Argument dilation (`ζ(ks)`) is the only height-changing operation in any receiver. Contracting collisions (`ρ ↦ 1 − ρ/k`) close by a minimum-height principle (row 713). Expanding collisions (HB's `5ρ/2 − 1`) leave geometric towers that no density tool sees (row 712). All collision residuals are rational ordinate relations, so they are excluded by the linear-independence hypothesis for ordinates. Squarefree (`κ = 2`) is the minimal dilation at which an RH-level dilated receiver closes (row 717).
  - **Minimal counterexample = wall 1** (row 714). "Every off-line zero has a lower one" is RH. The only height-lowering law is a `k`-free count with square-root cancellation, which is wall 1 seen from the integers.
  - Reading: the receiver side is now classified by (cost function, dilation). Producers must supply either square-root cancellation for a dilated count (wall 1) or individual-zero information beyond linear-independence-type coincidences. Neither appears in any unconditional tool. The frontier is unchanged.
  - **JAS (dressed lag aggregate), 2026-10-10.** RH ⟺ `JasDressedPSD 1 ∧ ¬JasOffLineChain` [L, R:JointAncestryRouteCapstone]. Existence (PSD at σ=1) is Weil positivity on completely multiplicative test vectors, i.e. wall 1 [L arithmetic form]. The chain residual ("every off-line zero has a farther one") mirrors the minimal-counterexample law: a farthest zero is excluded [L], and a chain survives only through phase-opposing near-alignment of zeros on the Kronecker torus (near-ties: wall 3; far zeros: t-aspect prime sums beyond Vinogradov–Korobov, i.e. linear-independence-type ordinate information). The dressing gives an exact jump (σ* ∈ {0} ∪ (1,∞)) but no a-priori bound, so it is a detector, not a producer. Gaussian localization removes the chain but collapses to Φ̂ ≥ 0.
- 2026-10-10 (Opus loop rows 722–724; MUST-899 [L]). **Receivers are measures on the Martin boundary of the half-plane.** In the spectral coordinate `a = γ − i(β−½)`, every receiver reads off-line zeros through a positive harmonic function vanishing on the critical line. Finite Martin points (`δ/((γ−x₀)²+δ²)`) are window receivers (Li, the LI clock response, Cayley families). The point at infinity (`δ`) gives the exponent receivers (Mertens, `k`-free, Abel-smoothed), each with a height cost set by its smoothing. Families over all finite points are the local-at-every-height receivers (WD, LA). Positive averages of finite points are δ-blind, so the point at infinity is reached only by windows at heights tending to infinity. A producer must therefore be either a global exponent bound (wall 1) or a height-uniform local sign (WD/LA's open core). Route LI's clock receiver now needs only a subexponential bound, with the rate `1/431` unconditional (MUST-899). Correction: a single rung `k ≥ 3` closes at a fixed `ε`; only `k = 2` needs every `ε`.
- 2026-10-10 (Opus loop rows 727–761; MUST-901, MUST-902 [L]). **Every unconditional mechanism lives where a series converges or a positivity holds, and a single off-line zero is visible only past that boundary.**
  - **Li ranges are powers of the verified band.** Termwise Li positivity holds for `n ≲ γ_off` (`re_xiLiPaired_nonneg_of_le_68`, band `γ² ≥ 431/2`), aggregate positivity for `n ≲ γ_off²` (rows 727–729). Every Li-type partial discharge is a band statement.
  - **Finite off-line sets are a finite wave** (row 755, MUST-902 [L]): `ψ(x) = x − Re Σ_{q∈S}x^q/q + O(√x log²x)` when every off-line copy lies in the finite set `S`. The single-quartet step (ITQ, strictly weaker than RH and open) needs one arithmetic inequality incompatible with a wave of relative size `x^{β₀−1}`.
  - **Inventory against ITQ** (rows 734–760): sieve positivity has relative precision `≍ 1` (parity); Halász/MR/Tao have `o(1)`; BV, towers and large sieve are family averages with weight `→ 0` on a fixed zero; Vinogradov minor arcs, Weil–Kloosterman and subconvexity give power savings only off the principal major arc, as upper bounds, or on the 1-line. The ITQ wave sits at the one place none reaches: the principal major arc of the unweighted prime sum. A relative power saving there is wall 1.
  - **The 1-line transport law** (rows 749–750, 761): every unconditional Eisenstein/Hermite–Biehler line law (Lagarias–Suzuki, Weng, Ki–Komori–Suzuki, Bianchi) is `ζ ≠ 0` on `Re = 1` plus Maass–Selberg unitarity, moved to the family's critical line by an argument dilation (`×2` on `ℍ²`) or a shift (`+½` on `ℍ³`). The `ζ`-zeros are displaced strictly left. Dynamically, an essential spectral gap `ε` for the modular surface ⟺ a zero-free strip `β ≤ 1 − 2ε` up to finitely many zeros. Spectral-gap technology (Dolgopyat, FUP) works only where the transfer operator converges.
  - **Positive kernels forbid Newton-polygon real-rootedness** (row 753): `b_m² ≤ b_{m−1}b_{m+1}` (Cauchy–Schwarz on `Φ ≥ 0`) forces the Hutchinson ratio `≤ 2.5 < 4` for every `m ≥ 2`, so Sheats' characteristic-`p` mechanism has no archimedean analogue for `Ξ`.
  - Reading: the missing input is a **lower-bound mechanism inside the strip** (row 757). All upper-bound technology (exponential sums, decoupling, subconvexity, mean values) bounds `|ζ|` or counts zeros, and none excludes one. The only lower bound in the corpus is the Euler product's at `σ > 1`. A producer must either continue a lower bound past the 1-line, or supply relative power cancellation at the principal major arc. These are the same requirement, read through Perron's formula.
- 2026-10-10 (Opus loop rows 783–795). **Three more positivity sources are excluded; the resolution scale is the common wall.**
  - **Interlacing families (Marcus–Spielman–Srivastava).** A nonnegative combination of real-rooted functions with a common interlacer is real-rooted, which is new to the corpus. Ξ is never a nontrivial nonnegative combination of LP-symbol images of itself: on the kernel side `Σc_kφ_k(iu) ≡ 1`, while LP symbols satisfy `φ(iu) ≥ φ(0)`. In any common-interlacer decomposition every piece must carry the full `n = 1` theta tail; the `n ≥ 2` theta terms have `≈ (T/π)log n` fewer zeros and turning points at `t ≈ 2πn²`.
  - **Siegel's exact decomposition** `ξ = GR + (GR)^#` gives RH from "`R` zero-free right of the line". The Jessen–Bohr mean of `log\|R\|` has a kink at `σ = ½` of width `≍ 1/log t`, so `R` should carry zeros right of the line at the critical scale (heuristic). The canonical Hermite–Biehler split is not HB.
  - **Hodge index at level `a`.** The exact identity `Q(f) = ∫\|f̂\|²(W − P_a)` (support `[−a,a]`) cannot be closed by any symbol or height-split operator bound. At Nyquist heights `t ≈ e^{2a}`, `W ≈ a/π` while `P_a` has Gaussian fluctuations of the same size, so `W − P_a < 0` on a positive proportion of heights even under RH. Positivity there is cancellation inside the quadratic form.
  - Reading: local receivers (first Laguerre inequality, cosine LP, HB decompositions, slice signs) are blind at depth `≲ 1/log γ`. There an off-line pair is indistinguishable from a double critical zero for every prime range `x < e^{1/δ}`. Exponent receivers need wall 1. No new positivity source was found; the corpus already holds the defect-disk, Herglotz and natural-boundary laws that were re-derived.
- 2026-10-10 (HCF loop rows 42–78, MUST-904/912). **Route HCF is a coordinate system on the Weil form, not a producer.**
  - In heat coordinates `w = z²` the strip is the parabola `Re w > (Im w)² − ¼`; Euler factors are heat traces on its boundary, the pole is its vertex [L].
  - Receivers [L]: index = #off-line quadruples (Gram, Hankel, arch−prime); Hankel determinants; sign = parity; no Toda blow-up; complete monotonicity.
  - The real-time layer is Route U's polynomial-square trace, whose linear wedge is the unconditional window. HCF bandwidth equals Weil aperture, so the window sits under the Nyquist wall. Complex time reduces R1 to the ψ-error exponent.
  - Template check: (a) needs the missing surface (HCF's Gram form is the intersection form on scaling-flow graphs); (b) circular; (c) wall 1; (d) HCF test functions are never prime-blind (MUST-812). No HCF-internal producer exists.

- 2026-10-10 (Opus FOZ/Li session; rows 782–815 of the first numbering and 900–901; MUST-906–910, 913). **Receivers are now exact and classified; the producer gap is sharpened.**
  - **Finite exceptions cost nothing on the receiver side.** FOZ ⟺ `ψ − x + Re W_S = O(√x log²x)` ⟺ `Φ − Re Σ_S w e^{u p}` bounded on one side (MUST-906/907). The new tools are Landau's theorem for any one-sided bounded real function and a tilted-ray pole argument. FOZ therefore needs exactly the precision of RH (wall 1).
  - **Detection–knowledge duality (row 801).** An arithmetic identity has a known power-precision error iff its Dirichlet series vanishes at the zeros it would detect, so identities annihilate exactly the waves they should see. Producers must be inequalities, and every inequality class known (`Λ ≥ 0`, squares, trigonometric positivity, sieves, Turán power sums) ends at the 1-line, averaging, or parity.
  - **Soft countermodels.** Davenport–Heilbronn for deep off-line zeros and the backward heat flow `H_λ` (`λ < 0`) for near-line pairs. Any producer must fail on both, i.e. must use the Euler product.
  - **Li's criterion is pinned two-sidedly and thins exactly along intersective sequences.** RH ⟺ `0 ≤ λ_n ≤ n²λ₁`, the chord bound / CND / unitary-orbit picture (MUST-910). The lower side fails at the identity phase and the upper side at the half-turn. Thinning along `P(x)` works iff `P` has a root modulo every integer (MUST-913, Furstenberg–Sárközy–Kamae–Mendès France class), and Ramanujan sums are the countermodel otherwise. Primes are not a thinning sequence; `p − 1` should be [P].
  - **Reading.** The receiver side now has exact equivalences, exception tolerance, sparse forms and a recurrence-theoretic classification. Every gain lands in receivers. The producer must be a pointwise inequality for a signed arithmetic object that uses the Euler product inside the strip, and none is known. Positivity is available only where a Dirichlet series or Euler product converges (the 1-line law), and that region excludes every point where an off-line zero could sit.
- 2026-10-11 (HCF loop rows 79–100): twenty-five more producer analogies in heat dress (Gutzwiller/Berry–Keating, de Branges, Lee–Yang, Lorentzian, Bost–Connes, Selberg heat trace, Nyman–Beurling, DVP, family positivity, sampling, modularity, Arakelov) each map onto an existing wall. Row 100 of `hcf-exact-layer-loop-2026-10-09.md` holds the map. HCF adds no producer input; a new HCF cycle must name an input outside that map.

## 2026-10-11 synthesis (Opus loop rows 914–932)

- **Receivers are classifiable exactly.**
  - Li's criterion thinned to an index set holds for all abstract configurations exactly along sets of Bohr recurrence (MUST-929 [L]). For ξ, the zero-free band widens this to every progression of modulus below 90 except even moduli at the half residue (MUST-926 [L]).
  - Weil-lag thinning is governed by the gap scale `√n`: every syndetic set works (MUST-927 [L]). Along `{b^m}` exactly the resonant non-attained chains evade (MUST-933 [L]).
- **Ordering of zeros decides residues.** Receivers dominated by real parts (lag, JAS, CCM) carry a "non-attained supremum" residue. Receivers dominated by Cayley modulus (Li) always have a finite attained top layer and no such residue.
- **Connes' parity step is a Cauchy-matrix spectral problem at leading order.** Its spectrum is `spec(diag((M/2)e^{±iθ})·[1/(p_i+p_l)])`. Graded asymptotics and nonvanishing Cauchy minors make the extremes never balance (MUST-932 [P]). Its residue is thin (MUST-934 [P]).
- **None of this produces positivity.** Every result above is a receiver classification. The producer side is unchanged (`producer-needs-saturation-2026-10-11`).
- 2026-10-11 (HCF loop rows 189–245, CANNOT-503 [L]). **Positivity duality, rank dichotomy, and where HCF's open core sits.**
  - **Positivity duality (row 193):** the explicit formula exchanges pointwise positivity and positive-definiteness. Λ ≥ 0 (and every Brownian, adelic, Bochner, Pólya-frequency or prime-heat-trace reading of it) is positive-definiteness of the subtracted prime part, never zero-side positivity (rows 190–198, 218, 222, 243).
  - **Rank dichotomy [L]:** at bounded rank the real zeros (Hardy) dominate every off-line zero above a height H(N) (`exists_height_heatMomentDet_pos`, CANNOT-503). At unbounded rank every off-line quadruple gives a negative direction (index law). So R2 must be rank-uniform, and no density or positive-proportion input helps (rows 228–238).
  - **Open core in HCF coordinates:** deep off-line zeros need √X prime precision (wall 1). Near-line pairs (δ ≍ 1/log γ) sit exactly at the masking threshold of the derivative channel, so deciding them is CANNOT-471 (row 239). Kernels, test spaces, orientation channels, thinning and integrable or Jacobi structure add nothing (rows 201–216, 230–244).
- 2026-10-11 (HCF loop rows 246–268, MUST-939 [L]). Two-sided large-time law in Lean: bounded rank detects exactly the off-line zeros with fewer heat frequencies below them, and is blind above H(N). The HCF signature has the separator shape of CANNOT-471's Lesson G (row 249) but costs primes to e^{C/δ} to evaluate locally (row 250). The corpus-wide saturation map (`producer-needs-saturation-2026-10-11.md`) independently finds the same single resolution limit. HCF is twin-blind (row 266), so it cannot feed the HF twin door.
- 2026-10-11 (HCF loop rows 269–288). **The producer profile, derived from countermodels.**
  - Every HCF input alone has an off-line countermodel (CANNOT-64, CANNOT-477, Davenport–Heilbronn).
  - Seven standard Euler × FE couplings fail; only mollification acts inside the strip, and only on average.
  - Voronin universality makes every local inside-strip law vacuous, so the producer is global.
  - FE-side global criteria lack margin (Λ ≥ 0), and the Euler side is the explicit-formula duality.
  - The remaining profile (global, non-linear, Euler × FE, zero margin) is Weil's function-field mechanism, so HCF's open core is the arithmetic Hodge index (template (a)), reached here from the countermodel side.

## 2026-10-11 addendum (Opus loop rows 933–938; MUST-935–941 [L])

- **Thinning is governed by the native regularity of each receiver.**
  - *Lag* (additive, Lipschitz scale `√n` two-sided, chord scale `n^{3/4}`). The exact chord balance plus Brun–Titchmarsh makes the lag criterion symmetric on every quadratic mesh: RH ⟺ mesh lags bounded below ⟺ bounded above (MUST-940). The mesh scale `n^{3/4}` is where both the `x log x` curvature and the prime chord charge become `O(g²/n)`. Unconditionally it can be pushed only by `exp(c(log n)^{1/3})` (Huxley); under RH it would reach `n/log²n`.
  - *Li* (Cayley phases). The lower half thins exactly along Bohr-recurrent sets (MUST-929). Its failure set for ξ contains a Bohr neighbourhood of 0 (MUST-935). The upper half needs Bohr density: squares fail abstractly, via `v = 2i` (MUST-941). Li's two-sided pin is asymmetric: lower = recurrence to phase 0, upper = visits to the negative cone of the dominant cosine polynomial.
- **Connes' parity at leading order is a ± pair problem for `diag(c)·Cauchy`, now in Lean (MUST-936).** The wedge compound detects `±μ` pairs. At imaginary aperture its leading block-triangular part has principal Cauchy minors on the diagonal, and analytic continuation carries this to arbitrarily large real apertures. The half-turn geometry (`π𝟙 ∈ H`) needed for the sign is the same geometry as the upper Li failures (`nθ ≈ π`).
- **Reading.** Every new result is a receiver law. Each receiver's tolerance for sparse data equals its native modulus of continuity, and no thinning ever touches the producer gap (wall 1 / near-double / Nyquist).
- 2026-10-11 (HCF loop rows 300–500). **HCF structural summary.**
  - HCF's unconditional Lean content is two NON-OVERLAPPING regimes: the small-time window (all ranks ≤ κ/a positive, `heatHankel_re_pos_of_window`) and bounded-rank large-time behaviour (blind above H(N), CANNOT-503; detects every off-line zero with fewer than N − 2 frequencies below it, MUST-939).
  - RH is exactly their rank-uniform bridge (row 499), and every bridging mechanism tested (≈ 300 cycles: positivity sources, couplings, operator, probabilistic, algebraic, dynamical, logical) maps onto templates (a)/(b), wall 1, or the strip wall.
  - The sharpest form of the missing object is an additive (FE/Poisson) × multiplicative (Euler) coupling inside the strip at √-strength. Its only exact instance, Kuznetsov, has its √ in the q-aspect.
- 2026-10-11 (HCF loop rows 513–520). **HCF fully reduced.** Its two receivers (vertical boundedness R1; Hankel PSD R2) exhaust the support/positivity characterisations of the zero measure. Direct attacks place each of its three targets exactly at a classical open wall with zero slack: R1 ↔ √-scale ψ-error (wall 1), R2 ↔ all-aperture Weil positivity (Nyquist/PBAP), Δ∞ = 0 ↔ zero-free regions shrinking to σ = ½ (strip wall).

## 2026-10-11 addendum (rows 942–944; MUST-946, 947, 1218)
- The CCM parity lane is closed for finite off-line sets, except for one residue.
  - Connes' step 1 (an even ground state at all large apertures) excludes every finite off-line configuration whose top layer has one positive leading-order point. That includes every top layer with even-sum ordinate relations, in particular ℚ-independent ordinates.
  - Everything is in Lean. The chain is MUST-936 (no ±μ pair), MUST-946/947 (sign via Kronecker with relations) and MUST-1218 (model to operator).
- Structural lesson. For an interval source `u`, the top-layer zero-sum term is exactly a Laplace pairing of the reflected source `u(a − ·)` with `e^{−(δ−it)s}`. The off-line zeros act on an edge layer of width `O(1/δ)` at the aperture ends. Their energy is `e^{2δa}` times a Cauchy-matrix form with phases `−2ta`, and no asymptotics enter at this step. Errors come only from the parity halving and from the reflected copy (`O(e^{−δa})`).
- What it does not give.
  - Infinite off-line sets (chains). A uniform floor for infinitely many lower off-line zeros would need a Carleson-type density bound, which is not natural for hypothetical zeros.
  - Top layers with an odd-sum relation and `F ≤ 0` on the whole aperture line.
  - Step 1 is RH-loaded only for finite configurations. It is not a producer.

## 2026-10-11 addendum (rows 945–953; MUST-1219–1226, 1229)
- **The CCM parity receiver is complete for finite top layers, up to near-coincident ordinates.**
  - Exact laws [L]:
    - ground energy `μ₀ = −(e^{2δa}/2)(Λ* + o(1))`;
    - near-ground shape = edge profiles;
    - pointwise parity law `sign F(θ(a))`;
    - alternation under even relations;
    - the quantitative half-turn criterion.
  - Deep limit [L]: for fixed ordinate shape and `δ → 0`, `F(θ(a₀)) > 0` with no relation hypothesis. The balance becomes `M*[λ_max(Γ^c_a) − λ_max(Γ^s_a)]`, the difference of the cosine and sine Grams of the top ordinates on `[0, a]`.
  - What is left is near-coincident top ordinates (spacing `≲ δ`) with an odd-sum relation.
- **Physical reading.** Off-line zeros are edge states of the Toeplitz form on `[−a, a]`, with energies `−e^{2δa}`. Their parity is a spectral asymmetry of a finite-rank Hankel operator, decided at first order by the sum Gram `1/(2δ − i(t_j + t_k))`. The leading (difference-Gram) problem is exactly parity-symmetric. `F(0) > 0` is false [P] (common-phase sinusoid law). Excluding edge states is the same as a short-interval prime bound at `√x` precision near `e^{2a}` (wall 1), so the receiver adds no producer.
- **Infrastructure.** `HTGeometry/DanskinPerturbationBound`: the upper half of Danskin's theorem with uniformly perturbed coefficients. It is reusable for any first-order eigenvalue limit.

## 2026-10-11 addendum (rows 954–961; MUST-1230–1236, 1240, CANNOT-504)
- **The Lee–Yang / Griffiths–Simon lane is now fully shaped in Lean.**
  - Tools:
    - Lee–Yang for every ferromagnetic graph (MUST-1231);
    - the first-zero budget `Z ≥ ∏cos·Z₀·(1 − S)` (MUST-1233);
    - Ising graphs as corpus Lee–Yang data (MUST-1235);
    - GKS certificates via Griffiths I (MUST-1236).
  - The capstone is that a convergent producer sequence gives RH (MUST-1240, phase-normalized form in CANNOT-504).
  - Forced shape:
    - the normalizer must be the centered magnetization characteristic function, with total field `Λ_n → ∞` and `β_n = Λ_n/2 + O(1)` (CANNOT-504);
    - unscaled site masses `≥ log 2` are impossible, and growing graphs need the scale to tend to 0 (MUST-1236);
    - frequencies bounded below are impossible (corpus MUST-806 family).
  - The shape is exactly row 608's Griffiths–Simon class.
- **Lesson (CANNOT-504).** A capstone's hypotheses can be unsatisfiable. MUST-1240 (constant normalization) and the prime-tree `E`-capstone are vacuous for nonnegative bonds. Spin-flip symmetry pins `Λ_n − 2β_n`, nonnegative coefficients give exponential type, and `E·Ξ` is never of exponential type (Zeta23 simple-critical census). Every "producer ⇒ RH" capstone should be audited for satisfiability with this exponential-type test.
- **Reading.** Any GS limit is an LP-class characteristic function. So `Ψ = e^{−bz²}Ξ/Ξ(0)` (Gaussian-smoothed `Φ`) is the only possible target shape, and success is RH itself. The necessary GS inequalities (Lebowitz, GHS, Gaussian domination) all hold under RH, so none of them can kill the lane unconditionally. The open core is constructive: a centered ferromagnet with collapsing masses whose limit law is `Φ` (or `Φ * N(0, 2b)`).
