# Renormalized Biarithmetic Geometry (RBG)

Namespace `GaloisForLFunctions.RenormalizedBiarithmeticGeometry`; umbrella `RenormalizedBiarithmeticGeometry.lean`; 23 modules.
Everything is unconditional. `riemannHypothesis_iff_*` and `zeroFreeStrip_iff_*` are equivalences, not proofs of RH.

## 1. Motivation

Weil's pairing over 𝔽_q is at once positive, Frobenius-equivariant, pinned to the arithmetic point and finite on the
diagonal. Over ℤ these properties live on different objects and separate exactly at divergent self-energies. RBG asks
which renormalization keeps positivity through the scale limit (survival cones), which coupling of +1 and ×p pins the
arithmetic point (gauge charge, log-cells), which non-scaling invariant makes amplification lossless (collided mass),
and which local geometry of ξ'/ξ replaces Weil's global extremum (critical discs, terminals). Each answer is either a
soft law (true for every configuration, blind to ζ) or a selective one, and RBG records which.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Quadratic form, survival cone | `quad`, `survivalCone` | x ↦ Σ x_iA_{ij}x_j; null cone of counterterm B |
| Lattice germ | `latticeGerm`, `latticeGermLimit` | G_r(z) = Σ r^k/(k+z); renormalized limit −ψ(z) − γ |
| Lattice Hankel family | `latticeHankel`, `latticeCounterterm` | G_r(x_i + x_j); counterterm 𝟙𝟙ᵀ |
| Torsion germ | `torsionGerm`, `torsionLimit`, `torsionLimitForm` | AET Abel torsion energy; limit −P(m,n), diagonal −I(n,n)/φ(n) |
| Harmonic-number kernel | `harmonicFn` | H(x) = ψ(1+x) + γ; kernel H(x) + H(y) − H(x+y) |
| Periodic germ, Cesàro Gram | `periodicGerm`, `cesaroGram`, `twistedGerm`, `periodMean` | Σ r^k a_α(k)a_β(k)/(k+1+x_α+x_β); counterterm mean(a_αa_β) |
| Ramanujan modes | `ramanujanMode`, `shiftedMode`, `twinPeriod` | Re c_n(k); c_n(k+1) |
| Hecke defect, mass | `heckeDefect` (CDG), `mass`, `amplify` | E(L) = Σ w_ρ(2cosh(2δ_ρL) − 2); D = Σ w_ρ; a_D(e) = 4e + e²/D |
| Depth moments, Hankel forms | `depthMoment`, `hankelForm`, `seenLevels` | m_j(L) = Σ w_ρk_ρ^j, k_ρ = 2cosh(2δ_ρL) − 2 |
| Integer theta reading | `reading` | finite-prefix computation of m_j(L) (CDG) |
| Gauges | `flipGauge`, `sourceKernel`, `sourceForm` | −1 at one prime; kernels built from a source F |
| Dilations | `latticeDilate`, `cellDilate`, `succShift` | δ_a ↦ δ_{ma}; q ↦ q(⌊n/m⌋); q ↦ q(n−1) |
| Cell holonomy defect | `hsDefect`, `chargedCells`, `liouvilleAgreements` | Hilbert–Schmidt failure of covariance of M_2 on [1,X] |
| Critical disc, terminal, lens | `InCriticalDisc`, `IsTerminal`, `InTerminalLens`, `lensWidth`, `rayRadius` | disc radius |b| about ½ + iγ; zero outside all discs; zero-free sector |
| Positive deformation | `PositiveDeformation` | Λ₀'/Λ₀ − Λ'/Λ = Laplace transform of a measure on (0,∞) |
| Configuration defect | `configMass`, `configDefect` | Hecke defect of any finite (w_i, δ_i) |

## 3. Language

- *Regularized family* Q_r − s_rB → A; *counterterm* B; *survival cone* ker B. Scalar counterterm = nothing survives.
- *Mode relations*: Σ C_αa_α ≡ 0. *Per-order relations*: coefficients sum to zero over each torsion order.
- *Pole node*: node x = 0 / order-one orbit, self-energy −log(1−r).
- *Blind* coupling (n; a,b): nab a square; *charged* otherwise. *Charged cell* a: σ(a)σ(2a+1) ≠ σ(2).
- *Soft* law: holds on every positive configuration. *Selective*: separates ζ (Euler gauge) from twins (Liouville).
- *Packet*: a_0 + Σ a_j cos(ω_jt) ≥ 0; a_0 *pole share*, a_j *purchases*; *height* of an ordinate over independent generators.

## 4. Mechanisms

**A. Survival of positivity through a scale limit**
1. PSD Q_r ⇒ A ≥ 0 on ker B; B ⪰ 0 when s_r → ∞; counterterms of one family are proportional, so the cone is scheme independent. Finsler–Debreu converse; scalar counterterm realizes every form.
2. Periodic Abel germ: each level is a Cauchy form (PSD); mean-zero parts converge (Dirichlet + Abel); counterterm = Cesàro Gram; survival cone = module of mode relations. Every limit entry = finite sum of digamma values at rational shifts.
3. Archimedean germ (all modes 1): cone = polar hyperplane Σc = 0, where −ψ(x_i + x_j) is a positive Hankel form; off it nothing survives (−1 at x = 1). Torsion germ: identity counterterm, cone {0}, limit indefinite on {1, q} for every prime power q.
4. Pole node spends the hyperplane constraint: H(x) + H(y) − H(x+y) PSD on the whole space.
5. Ramanujan orthogonality Σ_{k<q}c_m(k)c_n(k) = qφ(n)δ_{mn} ⇒ twins survive exactly on per-order relations; one node per order ⇒ {0}. Shifted twins: pole-node block = torsion energy, entry −I(m,n); at orders m, mt it is −φ(m)Λ(t) = digamma sum at rationals.

**B. Lossless amplification**
6. Two-scale rigidity E(L)² ≤ D(E(2L) − 4E(L)) gives E(2L) ≥ a_D(E(L)); a_D doubles the angle of D(2coshθ − 2). Hence E(2^kL) ≥ D(2cosh(2^kθ) − 2) with fixed loss D, and an upper bound at one large dyadic scale transfers losslessly down.
7. Moments m_j(L) form a Stieltjes sequence: Hankel PSD, null vectors = annihilating polynomials of seen levels (shell rigidity), log-convexity. Integer theta prefixes compute all moments for j|L| ≤ 2log(n+1).
8. Soft: rigidity and amplification hold for every finite nonnegative (w_i, δ_i) configuration.

**C. Gauge charge and cells**
9. Real-gauge blindness of (n; a,b) ⇔ nab square (prime-flip gauges, (−1)^{v_p}). Diagonal, ratio, product couplings blind; successor a(a+1) charged. Square-class criteria hold for Λ iff for λΛ.
10. Lattice and cell dilations both satisfy M_mS = S^mM_m; M_m = Σ_{r<m}S^rD_m. Lattice dilation covariant at every gauge; dyadic cell dilation only at Euler (9 = 3² forces c = 1; halving induction), on [1,X] exactly for primes ≤ 2X + 1.
11. Covariance defect ≥ 2·#charged cells; Liouville charged cells = sign changes λ(2a) ≠ λ(2a+1); a = 2u(u+1) charged when λ(u) ≠ λ(u+1); squares vs twice-squares give ≥ J charged cells below 8J⁴.

**D. Terminal geometry of ξ'/ξ**
12. Reflected pair contributes 2x(x² + (y−γ)² − b²)/(…) to 2Re ξ'/ξ: negative only inside its critical disc. Outside all discs Re ξ'/ξ ≥ 0 (Carathéodory region); terminals = zeros outside all discs.
13. Terminal lens (two radius-½ circles through p) is outside all discs, zero-free except p, Re ξ'/ξ ≥ 0; Harnack spreads ACP's outward floor (÷3) to discs of radius ρh/2 about p + h.
14. Zero of depth > a ascends to a right terminal of depth > a; one-scale defect bound with angle ϑ fails against any seen zero of depth > ϑ.

**E. Order and amortization**
15. Positive deformations compose; mutual ones are trivial (two nonnegative Laplace transforms summing to 0).
16. Kronecker dilution Σ|a_j| ≤ a_0 on ℚ-independent ordinates; Fejér packet on γ,…,Mγ buys M·a_0; height law via torus diagonal + (M+1)-node quadrature; weighted heights m_i = t^i give a finite purchase constant for every lattice cloud; difference packets buy (N−1)·a_0.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Survival law; scheme independence of the cone | `quad_nonneg_of_regularized`, `survivalCone_eq_of_regularized`, `quad_nonneg_on_survivalCone_iff` | proved |
| Counterterm rank dichotomy (torsion {0}, lattice hyperplane) | `counterterm_rank_dichotomy` | proved |
| Pole node completes the archimedean germ | `harmonicKernel_nonneg` | proved |
| Periodic germ survival = relations | `periodicGerm_survival`, `periodicGerm_survivalCone_eq` | proved |
| Ramanujan twin law; twins carry the primes | `ramanujanTwin_survivalCone_eq`, `ramanujanTwin_carries_primes` | proved |
| Primes as digamma sums | `orbitIntersection_eq_digamma_sum`, `totient_mul_vonMangoldt_eq_digamma_sum` | proved |
| Dyadic amplification; RH ⇔ dyadic subexponential growth | `heckeDefect_dyadic_ge`, `riemannHypothesis_iff_dyadic_subexp` | proved |
| Hecke moment problem; shell rigidity | `hankelForm_eq_tsum`, `ncard_seenLevels_lt_of_hankel_null`, `depthMoment_sq_le` | proved |
| Lossless transfer from integer prefixes | `heckeDefect_le_of_readings`, `reading_ge_of_heckeDefect_ge` | proved |
| One-scale bound / terminal ceiling ⇔ zero-free strip | `zeroFreeStrip_iff_heckeDefect_bound`, `zeroFreeStrip_iff_terminal_ceiling`, `riemannHypothesis_iff_no_right_terminal` | proved |
| Gauge blindness = square class | `realSignBlind_iff_isSquare`, `sourceForm_nonneg_twist_iff`, `successor_coupling_charged` | proved |
| Cells fix the gauge (reach 2X + 1) | `cellDilate_two_covariant_iff`, `cellDilate_two_covariant_on_horizon_iff` | proved |
| Liouville cell defect ≥ 2J on [1, 8J⁴] | `hsDefect_liouville_sandwich`, `hsDefect_liouville_ge` | proved |
| Terminal lens zero-free; floor spreads | `xi_ne_zero_of_mem_terminalLens`, `exists_terminal_floor_spreads` | proved |
| Positivity is irreversible | `not_positiveDeformation_of_ne` | proved |
| Dilution, height law, finite purchase | `sum_abs_le_of_packet_nonneg`, `sum_le_height_mul_of_generated_packet`, `exists_purchase_bound` | proved |
| Capstone (23 laws) | `renormalized_biarithmetic_geometry_laws` | proved |

## 6. Tools

**Developed**
- Survival-cone calculus for regularized quadratic families (finite-dimensional, Mathlib only).
- Digamma closed forms for every renormalized periodic Abel germ.
- Amplification map a_D and its angle-doubling conjugacy; Stieltjes/Hankel moment calculus for depth levels.
- Prime-flip gauges and the square-class criterion; Baumslag–Solitar cell/lattice dilation calculus; HS covariance defect.
- Critical-disc sign of reflected pairs; terminal lens; Harnack on the Carathéodory region.
- Kronecker + diagonal quadrature for packets; weighted heights; difference packets.

**To build**
- Explicit twin coefficients on per-order relations whose survival inequality bounds short-cycle differences of Weil's prime form.
- An arithmetic one-scale bound for integer-prefix readings at L ≍ log n (equivalent to a zero-free strip).
- Positive lower density of Liouville sign changes λ(2a) ≠ λ(2a+1) (linear cell holonomy).
- Exact purchase constant of a general cloud (LP between difference-set and height bounds).

## 7. Open questions

1. Can a matched torsion–continuum twin, built on per-order relations, control Weil's prime form rather than only re-express it?
2. Is there any source-side input for the one-scale Hecke bound weaker than a zero-free strip? (Proved: no.) Which strip width is reachable?
3. Linear growth of the Liouville cell defect (two-point correlation of λ along (+1, ×2)).
4. Exact purchase constant between (largest difference set − 1) and minimal weighted height; does it obstruct clustered companion clouds?
5. Can terminal lenses be chained to a global ceiling at some depth a < ½?

## 8. Traps

| Trap | Fact |
|---|---|
| Positivity of the torsion energy for r < 1 bounds the prime form | Identity counterterm: every symmetric form is such a limit |
| A better regularization scheme keeps torsion positivity | Survival cone is scheme independent: {0} |
| Any continuum twin cancels the torsion divergence | Only shared modes (same Ramanujan order) create relations |
| The archimedean germ is positive | Only on the polar hyperplane; the pole node is needed for full positivity |
| A cleverer multiplicative weight separates ζ from Liouville | Square-class couplings accept Λ iff λΛ |
| Point masses at log n lose nothing | Lattice dilation is gauge blind; only cells fix the gauge |
| Dyadic amplification is selective | Soft: holds for every positive configuration; it only transfers a bound |
| Something weaker than a strip bounds the one-scale defect | The uniform bound is the strip |
| Collective packets amortize the pole cost | Purchase ≤ (weighted height) × pole share |
| Terminal information is one-dimensional (a ray) | Harnack spreads it to discs; lens is a sector |
| A positive deformation can be inverted | Only trivially |

## 9. Context

| Uses | Modules |
|---|---|
| ArithmeticCorrespondencePositivity | 4 (terminals, ray floor, real tests, terminal pair ray) |
| ConjugateDiagonalGeometry | 3 (collided form, two-scale rigidity, theta readings) |
| BiarithmeticGaugeGeometry | 3 (gauge torus, Liouville/Euler gauges, Landau–Wronskian) |
| ArithmeticEffectivityTheory | 3 (torsion energy, orbit intersections, Ramanujan sums) |
| HTGeometry, RHTower, MultiplicativePositivityGeometry | 1–3 each (digamma Gauss series, Harnack, Kronecker, Laplace mass, Fejér) |

| Used by | Modules |
|---|---|
| BezoutValuationIncidence | 3 (dyadic amplification, theta readings, critical discs) |
| TransThresholdPairCorrelation | 3 (periodic germs, twins, pole node) |
| RenormalizedArithmeticPotentialTheory | 2 (rank dichotomy, twin law) |
| ArithmeticIntersectionTheory, ArithmeticCorrelationGeometry, HTGeometry | 1 each |

| Neighbour | Relation |
|---|---|
| RenormalizedArithmeticPotentialTheory | applies the survival law to Weil's horizon regulator; computes finite parts |
| ConjugateDiagonalGeometry | supplies D, E(L), two-scale rigidity; RBG adds amplification and the moment problem |
| BiarithmeticGaugeGeometry | supplies gauges and successor connection; RBG classifies blindness and fixes the gauge by cells |
| ArithmeticCorrespondencePositivity | supplies terminals and outward floor; RBG adds critical discs, lens, Harnack |
| ArithmeticEffectivityTheory / ArithmeticIntersectionTheory | torsion energies and orbit intersections renormalized here |

## 10. Big picture

RBG explains why positivity is so hard to carry from finite objects to the limit over ℤ: the prime place keeps no
positivity through its divergence at all, the archimedean place keeps it only on one hyperplane, and only coupling to
the arithmetic point (the pole) restores it. Matching the prime place requires a twin carrying the same Ramanujan
modes, and when one is built the primes reappear as digamma values — the inequality is re-expressed, not yet proved.

It also sorts tools into soft and selective. Amplification, rigidity and moment positivity hold for every positive
configuration, so they can only transport a bound that must come from elsewhere; every such target is exactly a
zero-free strip. Multiplicative (square-class) criteria cannot tell ζ from its Liouville twin; only the successor,
seen through log-cells, pins the Euler point. A proof of RH must therefore inject a selective, additive–multiplicative
input at one scale; everything else in the machinery is transfer.
