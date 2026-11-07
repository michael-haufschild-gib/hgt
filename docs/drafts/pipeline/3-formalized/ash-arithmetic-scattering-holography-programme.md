# Arithmetic scattering holography programme

- **ID:** ash-arithmetic-scattering-holography-programme
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), programme card
- **Source:** `docs/reports/review-0611/obstacles-summary.md` §2.7, §2.10
- **Statement:** Is universal damping on the function-field black hole a law of wave dynamics? No. Fake tree lattices with flux, unitarity, causality and commuting positive Hecke operators have off-line resonances. The survivor is the Krein flux law: a form with exactly the universal rate on every system, a dissipated energy exactly under RH.

## Goal
Folder `formal/GaloisForLFunctions/ArithmeticScatteringHolography/`, umbrella `ArithmeticScatteringHolography.lean`, foundational README in the folder.

## Paper derivations

**The graph.** `Γ\T_∞` for `E/𝔽_q` (Takahashi): rank-2 bundles mod `O(∞)` with fixed determinant. Data: `q`, abelian `G` (cusps), `D` (dead ends). `a = #G[2]`, `h = #G`, `a + h + 2#D = 2(q+1)`, `t = q+1-h`. Vertices and indices in `TheEllipticBlackHole`.

**Regular solution** (`λ = X+Y`, `XY = q`): core `hλ`; dead `(q+1)h`; neck `2λ²-(q+1)(q+1+t)`; pin `λ²-t(q+1)`; cap `(q+1)(λ²-q²-q-t)`; ray 0 `λ(λ²-q²-q-t)`; `ray(k+1) = λ ray k - q ray(k-1)`, `ray(-1) = neck`. Identity `q neck = (q-1) pin + cap` defines the core (balanced) sector.

**Jost.** `(X-Y) e(ray k) = j(Y,X) Y^{k+1} - j(X,Y) X^{k+1}`, `j(X,Y) = (Y²-1)(X³-tX+Y)`. Resonances: `X⁴-tX²+q = 0` or `Y² = 1`.

**Scattering.** Zero-mean `A`: `f(P,k) = A(P)X^k + (Y/X)A(-P)Y^k`, core and dead zero. Radial: `S = -Y j(Y,X)/(X j(X,Y)) = qw + q(q-1)h w²(1+qw)/((1-q²w)(1-tw+qw²))`, `w = X⁻²`.

**Pulse.** With `d_m` = coefficient of `w^m` in `1/((1-q²w)(1-tw+qw²))`, `ds(2m) = d_m`:
core `h(ds(τ-2)-q²ds(τ-6))`; dead `(q+1)h(ds(τ-3)-q ds(τ-5))`; neck `2δ(τ-1)+(q-1)h(ds(τ-3)+q ds(τ-5))`; pin `δ(τ-1)+qh(ds(τ-3)-ds(τ-5))`; cap `(q+1)(δ(τ-1)+q(q-1)h ds(τ-5))`; ray `δ(τ+k)+q^k r(τ-k)`, `r(τ) = qδ(τ-2)+q(q-1)h(ds(τ-4)+q ds(τ-6))`. Only the core equation uses the recurrence.

**Flux.** `(λ-λ̄) mass_{K+1} = Σ_P flux_K`; for outgoing `f`, nonreal `Y`: `(1-q/|Y|²) mass_{K+1} = μ_K Σ|c_P|²|Y|^{2K}`, so `|Y|² > q`.

**Hecke.** `T_Q(P,k+1) = q f(P+Q,k) + f(P-Q,k+2)`, `T_Q(P,0) = gap(P+Q) + f(P-Q,1)`, neck `(q-1)φ + f(P-Q,0) + f(-P-Q,0)`. Commutation is formal in `G`; the key identities are `gap(-R) = gap(R)` and `gap(T_{Q'}f)(R) = q(q-1)φ + q f(R-Q',0) + q f(-R-Q',0)`.

**Degree two.** Odd `G`, `G'`, `#G + #G' = 2(q+1)`, dead ends `±Q`, `Q ∈ G'∖0`. With `S = (Af)(core)`, `dT(Q') = q f(d_{Q'})`, `dT(0) = (q+1)f(pin) - f(cap)`: core `(q²-q+t)f_c + Σf(P,0)`; dead `(q+1)S - dT(Q+w) - dT(Q-w)`; neck `(q-1)S + f(P-Q₀,1) + f(-P-Q₀,1)`; pin `qS - dT(w) + f(-Q₀,1)`; cap `(q+1)f(-Q₀,1) + (q-1)dT(w)`; `(P,0)`: `q(q-1)f_c + q f(-P-Q₀,0) + f(P-Q₀,2)`; `(P,1)`: `q gap(P+Q₀) + f(P-Q₀,3)`; `(P,k+2)`: `q²f(P+Q₀,k) + f(P-Q₀,k+4)`. The core row of `A T = T A` uses `Σ_Q dT(Q) = dT(0) + 2qΣf_d` and `Σ_P gap(P) = 2q Σw f_n - dT(0)`.

**Propagator.** On a ray `u(d+1, k+1) = q u(d,k) + f(k+d+2) - q f(k+d)`. With `W_τ = c_τ + q W_{τ-2}` and `V_τ = c_τ - q V_{τ-2}`: `gap(u_{τ+1})(P) = q(f(P,τ) + f(-P,τ) + (q-1)W_τ)`, `dT(u_{2n+1}) = q(q+1)V_{2n}`, `dT(u_{2n+2}) = q(q+1)V_{2n+1} + 2(-q)^{n+1} dT(f)`. Since `2q S[g] = Σ_Q dT(g,Q) + Σ_P gap(g,P)`, the core obeys `c_{d+1} + q c_{d-1} = κ₁V_{d-1} + κ₂W_{d-1} + a_{d-1} + θ_d s₂`, with `κ₁ = #G'(q+1)/2`, `κ₂ = #G(q-1)/2`. Solution: `R(z) = 1/((1-q²z)(1-tz+qz²))`; coefficients at the core `φ = (1-qz)²(1+qz)R`, `ρ = (1-q²z²)R`, `γ = (1-qz)²R`; in `W`: `ρ, σ = (1+qz)R, η = (1-qz)R`; in `V`: `γ, η, γ' = γ/(1+qz)`. Growth: `r_{n+1} ≥ (q²-q) r_n` for `|t| ≤ q`, `q ≥ 3`.

**Cusp forms.** `Λ_w`: dead `g(Q+w)+g(Q-w)-2g(Q)`, pin `g(w)-g(0)`, cap `-(q-1)(g(w)-g(0))`. `T_{2Q,w} = P₂(T_Q) - qΛ_w`; `T_{Q,m,w} = P_{2m}(T_Q) + (-q)^mΛ_w`. Mass pairing: `⟨Λf,h⟩ = (1/(2(q+1))) Σ_{G'} (Θ_w-2)g_f · g_h`.

**Count law.** `K(φ+ψ) + K(φ-ψ) = 2K(φ) + 2K(ψ)`, `K(1) = 1`, `K(π) = q`, `K(1-π) = q+1-t` force `K = 𝒬`: three second-difference recursions. Fake `h = 3`: `K(2-π) = q-8`, the law needs `8-q`.

**KMS.** `G(z) = F(1+iz)`, `G(z+i) = G(-z)`. Fake: `Φ_b(x) = e^{-x²}(e cosh b + cosh 2x)`, transform `√π e^{w²/4} e (cosh b + cosh w)`, `w = s-½`; zeros `w = ±b + iπ(2k+1)`.

**Throat.** Indices `q+1`, `(a, q+1-a)`, `(b, q+1-b)`, then `(1, q)`. Condition at the end: `(X+Y)f₀ - (q+1)f₁ = Y²(z-q²)(z² - Tz + (b-1)q)/((q+1-a)(q+1-b)X³)`, `T = 1 + (b-1)q - ab`.

**Semigroup.** `R(m+n) = a_n R(m+1) + b_n R(m)`, `Z = [[0,1],[-q,t]]`. `H(x,y) = q|x|² - t Re(x̄y) + |y|²`, `H(y, ty-qx) = q H(x,y)`; on a mode `z`: `H(1,z) = 2 (Im z)²`. Kramers–Kronig: `∮ F(w) w^{n-1} dw = 0`, so `∫ Re F cos nθ = ∫ Im F sin nθ`.

**Height law (Manin).** `h = X³+aX²+bX+c` separable, twist `Y² = X³+aDX²+bD²X+cD³`, `D = h(T)`, `X = x/D`. `δ² (Z₁+Z₂) = 2[(X₁X₂+b)(X₁+X₂)+2aX₁X₂+2c]`, `δ² Z₁Z₂ = (X₁X₂-b)² - 4c(X₁+X₂+a)`, `δ = X₁-X₂`. On the diagonal `B = 4h(x)`, `C = h'(x)² - (8x+4a)h(x)`: a common zero is a double root. Gauss on `(v₁Z-u₁)(v₂Z-u₂)` and on the top coefficients. `X(P₀-P₁) = N/(T^q-T)²`, `N = T^{2q+1} + T^{q+2} + 2aT^{q+1} + bT^q + 2h^{(q+1)/2} + bT + 2c`, monic of degree `2q+1`; at `c`: `χ(h(c)) = 1` no loss, `0` loss one with `N'(c) = h'(c) ≠ 0`, `-1` loss two. So `K(1,1) = 1 + Σ(1+χ(h(c))) = #E(𝔽_q)`.

**Every class.** `S(d+2,Q) = A S(d+1,Q) - q S(d,Q)`, `S₁ = T_Q`, `S₂ = T_{Q,0}`. Off rays `S(d,Q)f = P_d(A)(f∘τ)`, `(f∘τ)(R,j) = f(R-Q,j)`. On rays `S(d+2)(R,k+1) = q S(d+1)(R,k) + f(R-Q,k+d+3) - q f(R-Q,k+d+1)`.

**Long throats.** `Q₀ = 1`, `Q₁ = z + q(1-c₀)`, `Q_{j+2} = (z+q)Q_{j+1} - c_{j+1}b_j z Q_j`. `R = (z+q)Q_{m+1} - (q+1)b_m z Q_m`. `R(0) = q^{m+2}(1-c₀)`, `R(q²) = 0`, so `D(0) = q^m(c₀-1)`; the functional equation at degree `2g` would need `q^g`, and `q^{2g-1}(c₀-1) = q^g` fails for `g ≥ 2`.

**Krein.** `R_{n+2} = tR_{n+1} - qR_n` with `R_n = l_{n+1} + q l_n`. `𝒬(x,y) = y²-txy+qx²`. `𝒬(y, ty-qx) = q𝒬(x,y)`. `𝒬(R_n,R_{n+1}) = q^{n+2}(q+1+t)`. Probe: `𝒬(g₀y+g₁x, g₀z+g₁y) = (qg₀²+tg₀g₁+g₁²)𝒬(x,y)`. Normalized: divided by `q` per double tick. Equals `deg(y-xF)`.

**Over ℤ.** `T_p E_u = (p^u+p^{-u})E_u`, so `T_p𝓕(τ) = 𝓕(τ+log p)+𝓕(τ-log p)`. `𝒬_f(τ) = e^{-τ/2}W_Z(f,f)` by scale isometry.

## Gates
- [x] 0 → 1 in-progress: statements fixed, corpus read
- [x] 1 → 2 fully-proven: derivations above
- [x] 2 → 3 formalized: modules below, each checked with `lake --old env lean` with no messages; wired into `ArithmeticScatteringHolography.lean` and `MainTheorems.lean`

## Lean certificate
| Claim | Module | Theorems |
|---|---|---|
| Graph, measure, Green | `TheEllipticBlackHole` | `Channels.waveOp_one`, `waveOp_nonneg`, `truncSum_greenDensity` |
| Regular solution, resonances | `TheRegularSolution` | `Channels.waveOp_regular`, `regSeq_jost`, `exists_outgoing_iff`, `jost_eq_zero_iff` |
| Exact ringdown | `TheExactRingdown` | `Channels.pulse_isWave`, `reflected_of_lt`, `echo_one`, `echo_sub_ground`, `coreSeq_eq_modes`, `ringSignal_add_two`, `minusBranch_isOutgoing`, `plusBranch_isIncoming`, `scattering_mul_swap`, `dampingRate_add_partner` |
| Flux | `TheFluxLaw` | `flux_law`, `mass_law`, `normSq_lt_of_outgoing`, `core_mass_law`, `gram_law`, `energy_balance` |
| Scattering matrix | `TheScatteringMatrix` | `zeroMeanField_eigen`, `scattering_eq_causal`, `norm_radialScattering_eq_one` |
| Hecke | `HeckeAtASecondPlace` | `heckeOp_comm`, `heckeOp_comm_waveOp`, `IsWave.hecke`, `hecke_energy_balance`, `heckeOp_eq_conj`, `truncSum_heckeGreen`, `heckeOp_balanced`, `IsOutgoing.hecke_eigen`, `chi_hecke_eigen` |
| Rigidity | `TheRigidityOfHeckeOnResonances` | `hecke_rigidity`, `ray_of_ray_ge`, `chebOp`, `chebOp_eigen`, `chebOp_comm_waveOp`, `chebOp_comm_heckeOp`, `chebOp_ray`, `Channels.chebOp_two_deltaCore` |
| Degree two | `HeckeAtAPlaceOfDegreeTwo` | `heckeTwo`, `Channels.heckeTwo_comm_waveOp`, `Channels.heckeTwo_comm_heckeOp`, `Channels.heckeTwo_comm`, `Channels.heckeTwo_one`, `Channels.heckeTwo_nonneg`, `Channels.heckeTwo_resonance`, `oddPairChannels`, `universal_damping_not_forced_with_degree_two` |
| Propagator | `ThePropagatorCoefficients`, `TheWavePropagatorIsPositive` | `propR_growth`, `gap_formula`, `deadTerm_odd`, `deadTerm_even`, `core_even`, `core_odd`, `even_closed`, `odd_closed`, `chebOp_nonneg`, `heckeDeg`, `heckeDeg_comm`, `heckeDeg_resonance`, `heckeDeg_energy_balance`, `universal_damping_not_forced_at_every_degree` |
| Cusp forms | `TheCuspidalSector` | `thetaOp`, `thetaField`, `thetaField_wave`, `heckeTwo_thetaField`, `heckeTwo_separates`, `heckeTwo_eq`, `truncSum_thetaOp_green`, `heckeDeg_symmetric`, `heckeTwo_symmetric` |
| Full family | `TheFullHeckeFamily` | `heckeFull`, `heckeFull_zero`, `heckeFull_comm`, `heckeFull_nonneg`, `heckeFull_thetaField`, `heckeFull_symmetric`, `universal_damping_not_forced_by_the_full_algebra` |
| Count law | `TheCountLawOfTheProbes` | `CountLaw.eq_kreinSquare`, `exists_countLaw_iff`, `Channels.universal_iff_countLaw`, `first_conservation`, `probeCount_law_iff`, `fake_violates_second_probe`, `card_quotient_probeLattice`, `card_quotient_tower`, `elliptic_has_countLaw` |
| KMS strip | `TheKMSStripOfTheHorizon` | `kms_condition`, `kms_midpoint`, `quarter_iff_midpoint`, `kernel_positive`, `xi_kms_positive`, `fake_horizon` |
| Integer probes | `TheIntegerProbesOfTheHorizon` | `posSemidef_of_integer_nonneg`, `riemannHypothesis_iff_integerProbes`, `integerProbe_parallelogram`, `riemannHypothesis_of_count` |
| Semigroup and phase | `TheLaxPhillipsSemigroup` | `lpMatrix`, `recurrence_shift`, `hankel_det_eq_zero`, `kreinHerm_step`, `kreinHerm_nonneg_iff`, `kreinHerm_mode`, `kreinHerm_semigroup`, `kramers_kronig`, `causal_symbol_kramers_kronig` |
| Height law | `TheParallelogramLawOfHeights` | `formA`, `formB`, `formC`, `forms_no_common_zero`, `forms_bezout`, `forms_top`, `pair_bezout`, `pair_top`, `eq_const_mul_of_cross`, `sum_product_of_X_ne`, `double_of_Y_ne`, `crossRelations`, `height_parallelogram` |
| Count law on a true curve | `TheCountLawOfATrueCurve` | `numer_monic_natDegree`, `commonFactor_mul`, `commonFactor_dvd`, `reduced_coprime`, `xCoord_sub`, `height_sub_eq`, `manin_countLaw`, `elliptic_has_countLaw`, `hasse_of_countLaw`, `elliptic_universal_damping_of_countLaw` |
| Every class | `EveryClassOfHecke` | `heckeClass`, `heckeClass_off_ray`, `heckeClass_comm`, `heckeClass_ray`, `heckeClass_one`, `heckeClass_resonance`, `heckeClass_nonneg`, `heckeClass_add_theta_nonneg`, `universal_damping_not_forced_at_every_class` |
| Throat of every length | `TheThroatOfEveryLength` | `chain_green`, `thPoly_monic_natDegree`, `thDen_eval_zero`, `thDen_eval_ground`, `chain_resonance`, `denom_constant_eq`, `top_of_functional_equation`, `chain_no_functional_equation` |
| Throat | `TheThroatOfABlackHole` | `throat_green`, `throat_resonance`, `throat_partner_law`, `throat_functional_equation_iff`, `throat_krein_step` |
| Krein | `TheKreinFluxLaw` | `kreinSquare_step`, `kreinSquare_eq_turan`, `wronskian_step`, `kreinSquare_probe`, `kreinSquare_nonneg_iff`, `normalizedKrein_step`, `flux_nonneg_iff`, `kreinSquare_ringSignal`, `probe_krein_nonneg_iff`, `modes_on_circle_iff`, `damping_domination_iff`, `integer_kreinSquare_nonneg_iff`, `lucasMix_rate_iff`, `ringSignal_rate_iff` |
| Window, edge, fakes | `TheHasseWindow` | `Channels.abs_traceR_le`, `universal_iff_window`, `universal_iff_product`, `Channels.exists_resonance_of_root`, `Channels.norm_resonance_lt`, `oddChannels`, `exists_slow_resonance`, `universal_damping_not_forced_one_cusp`, `universal_damping_not_forced_three_cusps`, `universal_damping_not_forced_many_cusps` |
| Horocycles | `TheHorocycleIsTheWave` | `horosphere_isWave`, `horoSignal_eq`, `horocycle_rate_iff`, `Channels.waveOp_waveOp_deltaCore` |
| Blindness | `ThePhysicalPositivitiesAreBlind` | `schur_bound_iff`, `norm_schurSymbol_le`, `radialScattering_eq_schur`, `Channels.coreMoment_psd`, `spectralDensity_nonneg`, `ramanujan_for_every_black_hole`, `Channels.heckeOp_nonneg` |
| Tower | `TheBaseChangeTower` | `frobPoly_base_change`, `abs_towerTrace_lt`, `towerTrace_overdamped`, `tower_bound_iff` |
| Curve datum | `TheCurveDatumOfABlackHole` | `datumOfRoots`, `bode_integral`, `posLog_eq_rate_deficit`, `bode_eq_zero_iff`, `kreinSquare_eq_endDeg`, `krein_eq_half_defect` |
| Every genus | `TheKreinLawAtEveryGenus` | `toeplitz_shift`, `curveKrein_step`, `normalizedMode_mul_partner`, `toeplitz_nonneg_iff_unitary`, `krein_tfae`, `bode_integral_every_genus` |
| True curves | `TheBlackHoleOfACurve` | `ellipticChannels`, `traceR_ellipticChannels`, `elliptic_trace_sq_le`, `elliptic_universal_damping` |
| One clock | `TheOneClockOfTheModularHorizon` | `heckeOp_normalizedEisenstein`, `heckeOp_wavePacket`, `treeWave_isWave`, `heckeOp_heckeOp_wavePacket`, `minusBranch_constantTerm`, `plusBranch_constantTerm`, `horoMean_heckeOp` |
| Krein over ℤ | `TheKreinLawOfTheModularHorizon` | `modeFactor_mul_partner`, `modeFactor_eq`, `physicalKrein_eq`, `hasDerivAt_physicalKrein`, `kreinFlux_nonneg_iff`, `exists_antiDissipative_of_not_riemannHypothesis`, `kreinFlux_nonneg_of_onLine`, `physicalCorrelator_rate_iff` |
| Log-mean | `TheBulkReadingOfTheLogMean` | `causalSymbol_universalFrequency`, `log_norm_causalSymbol_universal`, `rateDeficit_pos`, `bode_hasSum`, `bode_tendsto_iff_deficit_density` |
| Rank barrier | `TheRankBarrier` | `ringSignal_silenced`, `infinite_excited_modes` |

## No-go closure
- **Exact killing theorem/mechanism:** the route "derive universal damping on the function-field black hole from flux, unitarity and Hecke" fails. For every odd `N ≤ 2q+1` the group `ℤ/N` gives a black hole with local regularity, Green's identity, unitarity, causality and a commuting positive Hecke family; when `(q+1-N)² > 4q` it has a resonance with `|a|² > q` (`exists_slow_resonance`, `universal_damping_not_forced_*`). Hecke cannot help, because the resonances lie in the sector where `T_Q = A` (`IsOutgoing.hecke_eigen`), and over ℤ the corresponding statement is that `T_p` is a time translation (`heckeOp_wavePacket`).
- **Strongest positive survivor:** the Krein flux law. On every black hole, curve datum and tempered configuration, the form `𝒬` decays at exactly the universal rate; its flux is a manifest boundary square exactly under universal damping; it is the degree form over a curve and the Weil form over ℤ.
- **New insight:** RH on the graph says the ringdown is underdamped. The rate `¼` is the Liouville value. The sign is the effectivity of the degree form: `deg` counts points, and a real-quadratic fake has the same algebra with an indefinite form. So physics supplies the form and the rate, and arithmetic must supply the sign.
- **Status:** formalized in the modules above; no hypotheses beyond parameter ranges. Not formalized: characteristic two for the height law, the identification of the graph with `Γ\T_∞` (Takahashi, classical), the Bass–Kulkarni lattice statement (classical).

## Log
- 2026-11-07 — created in 1-in-progress; README first draft; modules formalized; README final; moved to 3-formalized
