# Stage-3 ledger: 11-rh-zero-divisor-geometry

Goal (2026-10-05): every card here formalized unconditionally in Lean, then moved to `3-formalized`.

| Card | Lean status | Next brick |
|-|-|-|
| weil-cone-explicit-real-producer | DONE, moved to stage 3 (`RHTower/LebesgueAtomWeilPositivity`) | — |
| weil-cone-common-ratio-unions-bohr-nonvanishing | DONE, moved to stage 3: Thm A `VerticalAP.le_liminf_nonvanishingCount`; Thm B `WeilCommonRatio.eq_vonMangoldt_of_weilPositiveFull_of_commonRatio` | — |
| weil-cone-rational-mass-atomic-producers | DONE, moved to stage 3: (a) iff `WeilZetaPower.weilPositiveFull_counting_iff_zetaPowerDatum`; (b) `HalfIntegerMassRigidity.vonMangoldt_and_riemannHypothesis_of_half_integer_counting` | — |
| weil-cone-finite-type-uniqueness | algebraic core only (`FiniteTypeDiscreteMomentAlgebra`) | boundary residue law; Gonek lemma; Jutila + Ingham density |
| verified-height-one-zero-turing-extension | consumer theorems only | BLOCKED by rules: headline is a certified numerical fact at height 3·10¹²; needs kernel Riemann–Siegel/Turing evaluation of ≈1.2·10¹³ zeros ("no computations", no `ofReduceBool`). User decision required |

## Reusable corpus facts found this goal
- Theorem B needs no Theorem A: `WeilAbscissa.eq_vonMangoldt_of_weilPositiveFull_of_sparse_rpow`.
- Step 3 of finite type ≈ `WeilRegular.eq_zero_of_weilPositive_add` (linear growth only; card allows polynomial).
- Explicit formula for ζ is proved: `WeilEF.EF_lit_zetaZeroConfig`.
- Corpus Ingham–Huxley has a `T^ε` loss (`exists_zeroHeightBox_ncard_le_ingham_huxley`); corpus Selberg
  near-line density decays only like `1/a` (`exists_selberg_nearLine_zeroDensity`). Neither suffices for Lemma C′.

## Rational-mass card: brick plan
(b) k = 2, G = ζ² (level-one Maass converse at λ = ¼):
- R1 K₀ = `modifiedBesselKOrder · 0`: Mellin `∫K₀(r)r^{s−1}dr = 2^{s−2}Γ(s/2)²`, ODE, holomorphic extension in the argument, decay.
- R2 `u_g(x+iy) = 4√y Σ g_n K₀(2πny)cos 2πnx + √y(b + a log y)`: C^∞, `Δu = u/4`, even, 1-periodic.
- R3 theta relation `u(i/y) = u(iy)` from `Λ(s) = Γ_ℝ(s)²G(s)` even with double poles (a, b = Laurent data at 1).
- R4 PDE uniqueness: `v = u − u∘S` with `v = ∂ₓv = 0` on iℝ₊ ⇒ `v ≡ 0` (x-analyticity + derivative recursion).
- R5 Wronskian: Green (`SelbergModularCurrentGreen`) ⇒ constant terms of `u_G`, `u_{ζ²}` proportional.
- R6 Roelcke: level-one cusp eigenfunction with `λ < 3π²/2` vanishes (`SelbergModularPotentialGreen`, `SelbergModularStripComparison`, Wirtinger).
- R7 assemble: `G = ζ²` ⇒ `F = ζ` ⇒ `lam = Λ`, RH.
Done (2026-10-05, axiom-clean, unwired leaf modules in `RHTower/`):
- R1 `BesselKZeroMoments` (K_j moments, Bessel ODE, `hasMellin_kZero`).
- R2 `MaassBesselSeries`, `MaassBesselFunction` (smooth λ=¼ eigenfunction, even, periodic).
- R4 `MaassAxisUniqueContinuation`, `MaassBesselHolomorphicLines`, `MaassConverseAutomorphy`.
- R3 `MaassThetaMellin`, `MaassGammaCorrections`, `MaassThetaRelation` (`kTheta_relation`).
- `MaassConverseLevelOne.maassFun_invS`: FE ⇒ `u(−1/z) = u(z)`.
- R5 `ModularInversionGreen` (S/T-invariant Green, radial anti-invariance, gradient-density invariance),
  `MaassConstantTermWronskian.constTerm_wronskian_eq_zero`.
- R6 `MaassLevelOneCuspVanishing.coeff_eq_zero_of_invS` (no even level-one cusp form at λ = ¼; Roelcke via
  corpus strip comparison + Wirtinger + explicit Bessel decay; corpus `SelbergMaassStripGap` only covers λ < ¼).
- R7 `MaassZetaSquaredConverse.coeff_eq_divisorCount_of_functional_equation` (converse theorem for ζ²),
  `WeilHalfIntegerMassRigidity.vonMangoldt_and_riemannHypothesis_of_half_integer_counting` (+ atomic form
  `half_integer_mass_rigidity`). All wired into `RHTower.lean`; standard axioms only.
- R10 (open): the card allows atoms anywhere. Small atoms (|t|<1, finitely many) give a polynomial factor `P`
  (|P| still increases in σ ≥ ½). An atom at `t = 0` of odd multiplicity flips the FE sign; then `u∘S = −u`,
  `u∘T = u` and `(ST)³ = 1` force `u = 0`. Needs a sign-ε version of `MaassThetaRelation` + automorphy.
(a) R8 datum-k exponentiation (generalize `IntegerMassRigidity` to masses in (1/k)ℕ, atoms t_j ≥ 0);
    R9 converse: explicit formula for degree-k `G` (Hadamard + contour) ⇒ producer.

## Rational-mass card (a): plan (2026-10-05)
R10 done: `WeilRationalMassAtomicProduct.bigG_pow_eq_of_fractional_counting` (any k, atoms anywhere): `G^k = K·P·Q`,
`P(1−s) = (−1)^{Σn}P(s)`. Odd sign for k = 2 killed by `(ST)³ = 1` (`coeff_eq_zero_of_odd_functional_equation`).
(a) forward: Ĝ := K·P·Q entire, zeros on the line, sign `(−1)^{kμ{0}}`, finite order (corpus
`weierstrassE1_norm_le_exp_two_norm_sq` ⇒ order ≤ 2), `Ĝ(1) ≠ 0` (pole of exact order k), `−G'/G = k·Σ lam n^{−s}`.
(a) converse (G with ζ^k FE, finite order, zeros on the line ⇒ (1/k)Λ_G Weil-positive):
- A1 generic prime-side line integral (Zeta23 `prime_side_line` is Λ-specific; generalize).
- A2 two-line residue lemma: `(1/2π)∫(H(c+it)+H(1−c−it))·g_{z₀}(c+it)dt = H(z₀)+H(1−z₀)`, `g_{z₀} = 1/(s−z₀)+1/(s−1+z₀)`,
  `1−c < Re z₀ < c`. Covers the pole terms (z₀ = 0) and every atom (z₀ = ½+it).
- A3 `W_lam(k) = (1/2π)∫(H+H̃)Φ_lam` on `Re s = c` (A1 + Zeta23 `gamma_line_shift` + A2 at z₀ = 0).
- A4 atomic explicit formula: Φ_lam atomic with c_j ≥ 0 ⇒ `W_lam(f⋆f̃) = Σ c_j(|f̂(t_j)|²+|f̂(−t_j)|²) ≥ 0`.
- A6 Hadamard: corpus `OrderOneHadamard.eq_const_mul_hadamardProduct_of_even` on `Ĝ(½+z)/z^{m₀}` ⇒ Φ_lam atomic.
- A7 finite order ⇒ order-one envelope (Phragmén–Lindelöf in the strip + Stirling on the edges).

(a) DONE 2026-10-05: A1–A3 `WeilFunctionalLineIntegral`, A4 `WeilAtomicExplicitFormula`, measure identity
`WeilAtomicBoundaryMeasure`, A6 `CompletionLogDerivZeroPairs` (no even/odd split: subtract the Hadamard
expansions at s and 1−s), A7 `CompletionOrderOneEnvelope`, assembly `WeilZetaPowerConverse`, `WeilZetaPowerForward`.
Lean correction: FE sign is (−1)^{kμ{0}}, not +1 in general.

## Common-ratio Theorem A: brick plan (2026-10-05)
Source checked: Li–Radziwiłł arXiv 1208.2684. Thm 3: discrete mollified 2nd moment = continuous + O(T/(log T)^{1−ε}),
for EVERY α > 0 (no Diophantine condition; Thm 2 without mollifier does depend on e^{2πℓ/α} ∈ ℚ). Continuous
side: BCHB `∫|ζM_θ|²φ(t/T) = φ̂(0)T(1+1/θ+o(1))`, θ < ½. Proof = |ζ|² AFE (Lemma 3) + Poisson in ℓ + Farey
uniqueness (Lemma 4) + large-b tail (Lemma 5) + mollifier-kills-resonance (Lemma 1, Euler products + zero-free
region) + first moment (Prop 3).
Corpus assets: exact product AFE `riemannZeta_mul_eq_productAFE`, critical pair `ZetaNotch.zetaSq_eq_afe`,
dual-weight bounds `ZetaNotchDualWeightBounds`, windowed twisted moment + diagonal law (`ZetaNotchTwistedDiagonal`,
off-diagonal only crude: θ < 1/4), BCHB per-(h,k) main term pieces (`Sieve/TwistedDiagonalAdapted`,
`BchbDensityIntegral`, `TwistedMainTermMerge`), Graham upper half, `pow_mul_norm_fourier_le_of_iteratedDeriv`,
`exists_pow_mul_norm_fourierIntegral_le`, orbit-closure Haar (`HTGeometry.CompletedObserverTimeTorus`,
`PhaseOrbitClosureSubtorus`), zero-free regions (VK lane).
Bricks:
- B1 smooth weights V (= corpus `smoothAFECutoff`) decay/derivatives; B2 |ζ|² AFE with Stirling error O(t^{-1/2+ε})
  (dual weight `W_t(Y) ≈ V(Y(2π/t)²)`);
- B3 uniform Fourier decay of `φ(x/T)V(c/(αx+β))` in c (Faà di Bruno); B4 Poisson in ℓ;
- B5 continuous BCHB: diagonal + (no off-diagonal for θ<½ by rapid decay) + Conrey main-term evaluation
  `Σ b_hb_k (h,k)/(hk)(log(T(h,k)²/hk)+2γ) → 1+1/θ`;
- B6 discrete−continuous: Lemmas 4,5,1; B7 twisted first moment (Prop 3 with Q^{it});
- B8 torus: Haar of orbit closure, Fourier of smooth W on T^K, inner approximation of 1_U; B9 assembly.

## Common-ratio Theorem A: formal route (fixed 2026-10-05, after reading LR §3–6)
LR's Thm 3 is used only as an UPPER bound `limsup T⁻¹Σψ(ℓ/T)|ζM(s_ℓ)|² ≤ (∫ψ)(1+1/ϑ)`; Prop 3 as
`T⁻¹Σφ(ℓ/T)e(ℓγ)ζM(s_ℓ) → [γ∈ℤ]∫φ`. W is approximated by trigonometric polynomials, so only
characters of the orbit closure H are needed (`∫_H e_m dμ_H = [⟨m,θ⟩∈ℤ]`), no Weyl equidistribution.
Bricks (done ✓):
- TA1 ✓ `ZetaSquareStirlingAFE.exists_norm_zetaSq_sub_symmetricAFE_le` (|ζ|² AFE, error ≪ log t/√t).
- TA2 ✓ `ZetaSquareDiagonalHarmonic.exists_norm_diagHarm_sub_le`: 𝓗(x)=Σs⁻¹V(s²/x)=½log x+γ+O(x^{−1/4}).
- TA3 ✓ `Sieve.LinearMollifierGcdForms`: S₀ log N → 1, S₁ → 1.
- TA4 discrete sums: k-fold summation by parts `|Σ_ℓ g(ℓ)e(ℓu)| ≤ (len+k)‖g⁽ᵏ⁾‖∞/(4‖u‖)ᵏ`; Riemann sums.
- TA5 t-dependent cutoff: `Σ_ℓψ(ℓ/T)V(c/t_ℓ)e(ℓu)` via Mellin `V(c/t)=(1/2π)∫(c/t)^{−w}e^{w²}/w` + TA4
  on `ψ(y)(αy+β/T)^w` (Cauchy estimates + Leibniz); trivial bound `CT min(1,(T/c)^σ)`.
- TA6 first moment: corpus `riemannZeta_eq_tsum_smoothAFECutoff_sub_dual_sub_residue_general` with
  x = T^{1+κ} (dual ≪ |t|/x via |ζ(−½+iu)| ≪ 1+|u|); c_N = Σ_{d|N}b(d)V(N/dx) → 0 for fixed N ≥ 2
  (Σ_{d|N}μ(d)log d = −Λ(N)); dyadic block count `#{N∈[X,2X]: ‖u_N‖<1/T} ≤ C(1+X/T)`; needs d(n) ≪ n^ε.
- TA7 divisor bound d(n) ≤ C_ε n^ε, 6^{ω(n)} ≤ C_δ n^δ; Farey spacing/counting.
- TA8 twisted gcd forms c_{a,b}(h,k)=μμ(ha,kb)/(hk) = E_{a,b} ⋆ P (P = corpus principal model, local
  factor (1−X/p)(1−Y/p)/(1−XY/p)); E_{a,b} = E^{(ab)} ⋆ ρ_{a,b}, ρ local (1−Y)(1−XY/p)/(1−Y/p) at p|a,
  mirror at p|b; ‖E_{a,b}‖₁ ≤ C·6^{ω(ab)}; ΣE_{a,b} = 0 for ab>1. Dominated convergence with corpus
  `tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow` + envelope ⇒ D_{a,b}L → 0, |D_{a,b}|L ≤ C(ab)^δ.
  Gcd-log twisted form by peeling primes (log(ha,kb) additive; coprime-restricted c^{(p⊥)} has
  correction local factor 1/P_p) ⇒ D'_{a,b} → 0, |D'_{a,b}| ≤ C(ab)^δ.
- TA9 F(a,b,t)=Σ_{h,k}b_hb_k(ha,kb)/(hk)·𝓗(t(ha,kb)²/(2π·ha·kb)) = (½log(t/2πab)+γ)D + ½D' + E,
  |E| ≤ C(ab)^{1/4+δ}y^{1/2}t^{−1/4}L³ (uses g ≤ (h,k)(a,k)(b,h), Σg/(hk) ≤ C(ab)^δL³).
- TA10 second moment: quadruples (m,n,h,k), u = α log(nk/mh)/2π. diag (F(1,1)) → 1+1/ϑ; non-resonant
  ‖u‖ ≥ T^{−1+η}: TA5 with k large; resonant j=0: forces mn ≥ T^{2−2η−2ϑ}, killed by V decay;
  resonant j≠0, b<K_j=T^{1/2−η}e^{−π|j|/α}: unique fraction (Farey), contributes ≤ CT(ab)^{−1/2}sup|F|,
  dominated convergence over j via (U)/(P) (fraction fixed iff e^{2πj/α} ∈ ℚ, else ab → ∞);
  b ≥ K_j: LR Lemma 5 (Farey count + divisor bound) ≪ T^{1/2+ϑ+ε}.
- TA11 orbit closure H ⊂ 𝕋^K, Haar probability μ_H, characters, inner regularity, mFourier density.
- TA12 assembly: Cauchy–Schwarz, ϑ → ½, φ → 1_{[1,2]}, W → 1_U.

### Theorem A progress (2026-10-05, namespace `RHTower.VerticalAP`, all wired after `ZetaSquareDiagonalHarmonic`, axiom-clean)
- TA4 ✓ `VerticalProgressionLatticeSums`: `norm_latticeSum_le` (k-fold summation by parts), `norm_tsum_sub_integral_le`.
- TA5 ✓ `VerticalProgressionCutoffSums`: trivial/decay/oscillation bounds for `Σψ(ℓ/T)V(c/t_ℓ)e(ℓu)`
  (`exists_norm_latticeSum_cutoff_le`: `≤ C T²/(c T^k δ^k)` uniformly in `c`).
- TA6 ✓ first moment: `VerticalProgressionMollifier` (M_N, long smoothed ζ-series, mollified coefficients),
  `…FirstMomentExpansion`, `…BumpSums`, `…Resonance` (per-j counting, geometric sums), `…FirstMoment`,
  `…ResonantMass` (`tendsto_resonantMass`), `…FirstMomentLimit`:
  `tendsto_firstMoment_div_int` (γ = j ⇒ J/T → ∫φ), `tendsto_firstMoment_div_of_not_int` (γ ∉ ℤ ⇒ J/T → 0),
  for every 0 < θ ≤ ½ with N = ⌊T^θ⌋, X = T^{21/16}.
- Next: TA8/TA9 (twisted gcd forms, F(a,b,t)), TA10 second moment, TA11 torus, TA12 assembly.

### Theorem A progress (2026-10-06): TA8 done (namespace `RHTower.Sieve`, not yet wired)
- `TwistedSelbergCoefficient`, `…Factorization` (c_{a,b} = (F⋆G)⋆P), `…Summability`, `…Forms`
  (generic dilated inner sums `dilatedInner`, `tendsto_sum_mul_dilatedInner`, `abs_sum_mul_dilatedInner_le`;
  Q_{a,b}/L^{q+r+1} → 0 for ab>1, uniform envelope M·d(ab)d(a)d(b)2^{ω(a)+ω(b)}L^{q+r+1}).
- `TwistedSelbergGcdLog`: c_{a,b}·log(ma,nb) = (F'⋆G+F⋆G')⋆P + (F⋆G)⋆P^{log} (Leibniz derivations + local
  series identity at p|a, p|b, p∤ab). `TwistedSelbergGcdLogForms`: G_{a,b}/L^{q+r+2} → 0 for ab>1, envelope
  M(1+log ab)d(ab)d(a)d(b)2^{ω(a)+ω(b)}L^{q+r+2}.
- TA9 ✓ `Sieve/TwistedSelbergRatioForms` (radical reduction, S₀/S₁ twisted forms, cancellation, envelopes,
  `sum_gcd_mul_div_le`: Σ(ha,kb)/(hk) ≤ d(ab)(1+log N)²(1+log Nab)) and `VerticalProgressionRatioForm`
  (`ratioForm_eq` splitting via 𝓗; `ratioForm_one_one_uniform` F(1,1,t) → ½+1/(2θ); `ratioForm_uniform_of_ne`;
  `exists_norm_ratioForm_le` ‖F(a,b,t)‖ ≤ C(ab)^{1/3}; all uniform for t ∈ [c₁T,c₂T], N = ⌊T^θ⌋, θ < ½).
- TA10 sub-bricks (plan): S1 expansion S₂ = 2Σ_q X_q + O(T^{½+θ}log T) (|ζ|² AFE, swap ℓ/q);
  S2 fibers of q ↦ reduced(nk, mh): Σ_{fiber(a,b)} X_q = Σ_ℓ ψ(ab)^{-½}(a/b)^{it_ℓ}F(a,b,t_ℓ) (+ majorant F⁺);
  S3 per-q bounds: ‖u‖ ≥ T^{-1+η} (TA5 oscillation), j = 0 near-resonance ⇒ mn ≥ T^{2-2η-2θ} (V decay);
  S4 Farey: distinct a/b, a'/b' differ by ≥ 1/(bb'); count in window ≤ 1 + 4λB²;
  S5 resonant j ≠ 0: b < K_j unique fraction + dominated convergence over j (TA9 (P),(U));
  b ≥ K_j dyadic Farey sum ≪ T^{½+θ+ε}; S6 assembly S₂/T → (∫ψ)(1+1/θ).
- TA10 progress (2026-10-06, unwired, all compile, no sorry): S1 `VerticalProgressionSecondMomentExpansion`
  (`norm_secondMoment_sub_expansion_le`); S2 `VerticalProgressionRatioFibers` (`quadRatio`, `hasSum_fiberTerm`,
  `fiberTerm_eq` Φ_T(a,b) = Σ_ℓψ(ab)^{-½}e^{it log(a/b)}F(a,b,t)); S3 `VerticalProgressionOffResonance`
  (`hasSum_indicator_fiberTerm`, `sum_offResonant_le`, `pairProd_ge_of_near_diagonal`, `sum_nearDiagonal_le`);
  S4 `VerticalProgressionFarey` (spacing, `card_le_of_window`); S5 `VerticalProgressionResonantBounds`
  (`sum_decay_le`, `pairProd_ge_of_huge`, `norm_ratioForm_le_crude`, `norm_fiberTerm_le`) and
  `VerticalProgressionResonantCount` (`card_window_le` ≤ 2e³δ'W+1, `card_resonantSet_le`, `sum_resonant_rpow_le`
  dyadic Farey sum). Remaining: Ra dominated convergence over j (uniqueness via card_window_le < 2), assembly
  with η = (½−θ)/4, ε₁ = η, s = ½ − η/4.
- TA10 ✓ (2026-10-06, axiom-clean, unwired): `VerticalProgressionSecondMomentLimit.tendsto_secondMoment_div`:
  T⁻¹Σψ(ℓ/T)|ζM_N(½+i(αℓ+β))|² → (∫ψ)(1+1/θ) for every α>0, β, 0<θ<½, N=⌊T^θ⌋ (full asymptotic, not only
  limsup). Modules: …ResonantSmall (dominated convergence over j), …ClassLimits (off-resonant, near-diagonal,
  huge, medium resonant via dyadic Farey), …SecondMomentLimit (partition `indicator_partition`, diagonal
  `tendsto_fiberTerm_one_one_div`, expansion error). Next: TA11 orbit-closure characters, TA12 assembly.
- TA11 ✓ `BohrOrbitClosureHaar` (`orbitHaar`, `integral_mFourier_orbitHaar`, `orbitHaar_pos_of_isOpen`).
  TA12 ✓ `VerticalProgressionBohrMoment.tendsto_bohrMoment_div` (S₁(W)/T → (∫W dμ_H)∫φ, any continuous W),
  `VerticalProgressionBohrNonvanishing.le_liminf_nonvanishingCount` (μ_H(U)²/3, every open U),
  `le_liminf_card_riemannZeta_ne_zero` (1/3). All TA modules wired into `RHTower.lean`; standard axioms.
  Card moved to `3-formalized` (2026-10-06).

## Finite-type card: brick plan (2026-10-06)
See the card's "Lean plan (2026-10-06)": FT1 datum + continuation identification, FT2 boundary-pole lemma,
FT3 residue consequences, FT4 smooth zero sums, FT5 Gonek lemma, FT6 Rules A/B + Landau–Gonek,
FT7 density (Jutila near line, uniform Ingham, corpus Ingham–Huxley far), FT8 Steps 1–2, FT9 Step 3.
- FT1–FT3 ✓ `WeilFiniteTypeContinuation`, `WeilFiniteTypeResidues` (master identity, `A(1)=1`, boundary-pole lemma,
  off-line `Aζ'=F`, multiple critical `F=0`, simple critical residue real ≥ 0, `critical_realness`).
- FT7(a)(i) ✓ `ZetaMollifiedShortWindowMeanSquare.exists_eventually_shortWindow_meanSquare_le`:
  `∫_{y₀}^{y₀+T^{1−η}} |ζM_N(½+it)|² ≤ C T^{1−η}` for `N = ⌊T^θ⌋`, `θ+η < ½`, all `y₀ ∈ [T/2, 2T]`
  (diagonal fibre = TA9 `F(1,1,t)`; off-diagonal by `K`-fold IBP after Mellin, `|λ| ≥ 1/(N√(2mn))`;
  tail `mn > T^{1+ε}` by cutoff decay). Standard axioms.
