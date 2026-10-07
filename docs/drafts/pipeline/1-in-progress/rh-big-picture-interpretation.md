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
