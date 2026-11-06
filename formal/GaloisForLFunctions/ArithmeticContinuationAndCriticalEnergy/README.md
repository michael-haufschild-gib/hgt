# Arithmetic Continuation and Critical Energy (ACCE)

Namespace `GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy`; umbrella
`ArithmeticContinuationAndCriticalEnergy.lean`; 85 modules.

## 1. Motivation

A critical energy of an exact arithmetic source is finite at one end of a parameter range (half
damping, a cutoff, a small aperture) and RH says it stays finite as the parameter runs to the
critical end. ACCE studies **transport in the parameter**: the derivative of the energy, what pays
it, and which horizon-uniform bound must be estimated. Every object carries two indices — a
continuous parameter and an observation horizon $T$ — and the only currency is a bound uniform in
$T$. Three faces: damping $\varepsilon$ (main), cutoff, aperture $a$ (restricted Weil ground energy).

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Energy family | `Admits`, `CofinallyAdmits`, `UniformlyAdmitsOn` | $E:\mathbb R\to\mathbb N\to\mathbb R$; $\exists B\,\forall T$ is the content |
| Source | `pmPowerDampedCenteredDivisorPrefix` (RHTower) | $A_\varepsilon(n)=\sum_{d\le n}\mu(d)d^{-\varepsilon}\lfloor n/d\rfloor-n\,m_0(\varepsilon)$, $m_0=1/\zeta(1+\varepsilon)$ |
| Critical energy | `dampedMobiusEnergy` | $E_T(\varepsilon)=\sum_{n\le T}A_\varepsilon(n)^2/(n(n+1))$ (pronic weight) |
| Tangent | `dampedChebyshevError` (BVI) | $E_\varepsilon=\partial_\varepsilon A_\varepsilon$ = centred damped Chebyshev prefix |
| Signed work | `signedDampingWork` | $W_T=\langle A_\varepsilon,E_\varepsilon\rangle_T$; $\partial_\varepsilon E_T=2W_T$ |
| Autocorrelation | `tangentCorrelation` | $K_T(\eta,\varepsilon)=\langle E_\eta,E_\varepsilon\rangle_T$ (Gram kernel) |
| Second tangent | `dampedChebyshevSecond` | $F_\varepsilon=\partial_\varepsilon E_\varepsilon$ (row $\mu\log^2$) |
| Budgets | `LinearContinuation`, `OsgoodContinuation`, `AveragedContinuation`, `DampingContinuation` | horizon-free bounds on loss rate |
| Relative loss | `relativeLoss` | $r_T=-\partial_\varepsilon\log(1+E_T)$ |
| Dilation | `rowDilate`, `prefixDilation` | $v(\lfloor\cdot/j\rfloor)$; $D^fv(n)=\sum_j f(j)v(\lfloor n/j\rfloor)$ |
| Dilation form | `rowDilationForm`, `quotientIncidenceKernel` | $\langle v,D^{\Lambda_\varepsilon}v\rangle$; kernel $\kappa(n,m)=\sum_{\lfloor n/j\rfloor=m}\Lambda(j)j^{-\varepsilon}$ |
| Inversion defect | `inversionDefect` | $\rho_\varepsilon(n)=n-m_0\Phi_\varepsilon(n)\in[0,n]$ = $-m_0\cdot$ majorant prefix |
| Majorant source | `majorantCenteredPrefix`, `majorantEnergy` | row $d^{-\varepsilon}$, signs removed |
| Work accounting | `workCore`, `workDeviation`, `deviationRow`, `dampedPrimePrefix` | core $\sum\psi_\varepsilon(n)/(n(n+1))$ + deviation terms |
| Dirichlet form | `dilationEdgeMass`, `dilationJumpEnergy` | $2Q=M-J$ on the dilation graph |
| Block energy | `dampedBlockEnergy`, `dilationStepObservation` | centred sums over $(\lfloor n/q\rfloor,n]$; $O_qv=v-v(\lfloor\cdot/q\rfloor)$ |
| Long/short split | `pmShortModulusSawtooth`, `pmLongModulusQuadrature` | moduli $\le D$ sawtooth + signed long-modulus quadrature |
| Function field | `fqCenteredPrefix`, `fqEnergy` | $\mathbb F_q[T]$ model, same weight |
| Aperture | `ccmRestrictedWeilGroundEnergy` (RHTower), `CompensatedWidthFloor`, `groundEnergyRate` | $\mu(a)$; floors $\mu\ge-Ce^{2\sigma a}$ |
| Zero pairs | `pairedPlusEnergy`, `pairedMinusEnergy` | $E_\pm=\tfrac14\sum_q|\hat u(-z_q)\pm\hat u(-\bar z_q)|^2$ |
| Shell flow | `shellFlux`, `frozenFamily`, `primeShellCorrelation`, `primeThresholdLadder` | aperture step decomposition |

## 3. Language

- **Admission**: finite named norm, $\exists B\forall T$. **Cofinal**: at parameters accumulating at the critical end.
- **Continuation**: propagation of admission across $[a,c]$ by a horizon-free budget.
- **Pointwise / averaged**: bound on $-E_T'$ vs on $\int_a^c r_T$; averaged is the bottom of the hierarchy.
- **Paid**: bounded uniformly in $T$ unconditionally. **Debt**: a positive term the deviation must cancel.
- **Width** $\Delta=\Theta-\tfrac12$ (`zetaZeroAbscissa`, `zetaZeroWidth`): partial continuation on $(a_0,c]$ ⇔ strip $\Theta\le\tfrac12+a_0$.
- **Selective**: separates the Möbius source from size-blind (majorant) and sign-blind (parity twin) models.

## 4. Mechanisms

**A. Transport calculus (abstract).**
1. Master inequality: $0\le\psi E'+\beta'$ ⇒ $\Psi(E)+\beta$ monotone (`scaledEnergy_add_budget_le`); Grönwall $1+E(a)\le(1+E(c))e^{\beta(c)-\beta(a)}$; Osgood for coercive $\Psi$; superlinear scale $\log(1+\log(1+u))$ tolerates an extra log (`riemannHypothesis_of_superlinear_dampingContinuation`).
2. Horizon-dependent budgets transport nothing: $\mathrm{Esc}_T=e^{2(1/2-\varepsilon)\log(T+1)}-1$ has exact linear identity with coefficient $2\log(T+1)$, admitted only at ½ (`not_linearContinuation_escapeEnergy`).
3. Affine envelopes need contraction $q\le\theta<1$; $q=r=1$ diverges linearly (`not_bddAbove_affineEnvelope_one_one`). Ground floors transport under *relative* decay (`floor_le_of_relative_decay`).
4. Averaged budget ⇔ ratio bound ⇔ admission (`averagedContinuation_iff_ratio_bound`, `averagedContinuation_iff_admits`); pointwise strictly stronger (spike: `exists_averagedContinuation_not_linearContinuation`) and can fail in an admitted state (`exists_admits_everywhere_not_linearContinuation`). Sparse/Cesàro horizons suffice (`Admits.of_dyadic_horizons`, `admits_iff_cesaro`).

**B. Exact derivative and its faces.**
5. $\partial_\varepsilon E_T=2W_T$ = Markov boundary flux − jump energy − density forcing (`two_mul_signedDampingWork_eq_markov`); $\int_a^c2W_T=E_T(c)-E_T(a)$ (`integral_signedDampingWork_eq`); non-admission is always a named deep negative work (`exists_signedDampingWork_lt_of_not_admits`).
6. Scalar first moment of the tangent is paid ($L^1$, `exists_uniform_scalar_damping_work_bound`); subtracting the constant source is neutral (`admits_damped_residual_iff`, `linearContinuation_residual_iff`); the residual cusp forces positive work only at escaping horizons.
7. Signed work is strictly weaker than tangent norm (rotating row: zero work, tangent $|K|$); sector energies cannot be added ($m^2$ vs $m$).
8. Cutoff is free given admission: dyadic shells telescope into $E_T$ with geometric error (`exists_bound_sum_ramanujanPhysicalShellEnergy_of_admits`); stage identity keeps the signed cross term (`ramanujanCutoff_stage_energy_eq`).

**C. Endpoints and shape.**
9. Both ends paid: $E_T(\varepsilon)\to\sum_{n\le T}1/(n(n+1))\le1$ as $\varepsilon\downarrow0$ (`tendsto_dampedMobiusEnergy_nhdsGT_zero`); ½ admitted. ¬RH ⇒ unbounded **interior bump** (`exists_unbounded_interior_bump_of_not_riemannHypothesis`); bump lives at small $\varepsilon$ and large $T$ (`exists_damping_head_energy_le`; core $\ge\log2/(4\varepsilon)$ only beyond $2^{1/\varepsilon}$).
10. Shape criteria (each ⇒ RH): convexity; single sign change of $W$; $-\|E_\varepsilon\|^2\le\langle A_\varepsilon,F_\varepsilon\rangle$ (`riemannHypothesis_of_second_tangent_pairing_ge`, constant-free). No-bump ⇒ damping-uniform admission (`uniformlyAdmitsOn_of_no_interior_bump`). Global $W\ge0$ is false ($W_1\to-\tfrac12$, `not_forall_signedDampingWork_nonneg`).
11. Out-and-back: $\int_a^c\|E_x\|\ge2\sqrt{E(\varepsilon)}-\sqrt{E(a)}-\sqrt{E(c)}$ (`integral_pronicNorm_tangent_ge`).
12. Free anchor: RH ⇔ cofinal bound on $\int_\eta^\varepsilon2W_T$ uniform in $T,\eta$ (`riemannHypothesis_iff_cofinal_work_integral_bound`).

**D. The sign is an angle.**
13. $W_T(\varepsilon)=\langle A_\delta,E_\varepsilon\rangle+\int_\delta^\varepsilon K_T(\eta,\varepsilon)d\eta$; $K\ge0$ ⇒ RH; obstruction = off-diagonal anti-alignment of tangents; relative stability $\|E_\eta-E_\varepsilon\|\le\|E_\varepsilon\|$ ⇒ RH; second-tangent majorant gives it on fine partitions. Hierarchy is strict.
14. At most $1+1/\delta$ dampings pairwise $\delta$-anti-correlated (`card_le_of_pairwise_anticorrelated`).
15. $\iint_{[a,c]^2}K_T=\|A_c-A_a\|_T^2\ge0$ unconditionally; its horizon bound ⇔ admission (`admits_iff_bounded_double_integral_tangentCorrelation`).

**E. Prime-pair / Nyman–Beurling coordinates.**
16. Pronic pairing of prefixes = $\sum a_jb_k/\max(j,k)-(\sum a)(\sum b)/(T+1)$ (`pronicPairing_prefix_eq_maxKernel`) = single level sum (`sum_sum_div_max_eq_level_sum`); $E_T$ and $W_T$ are level sums minus a boundary term.
17. Polar calibration: $P_T-m(\varepsilon)R_T(\eta)-m(\eta)R_T(\varepsilon)+m(\eta)m(\varepsilon)(2T-H_T)$, each piece linear in $T$; admission ⇔ cancellation to **relative precision $1/T$** (`admits_iff_relative_precision_inv_T_primePair`).

**F. Dilation calculus on integer prefixes.**
18. $D^f\circ D^g=D^{f*g}$ exactly (`prefixDilation_comp`); twist $n^{-\varepsilon}$ is a ring homomorphism (`dampedTwist_mul`); inversion law $\sum_jj^{-\varepsilon}A_\varepsilon(\lfloor n/j\rfloor)=n-m_0\Phi_\varepsilon(n)$; tangent $=D^{\Lambda_\varepsilon}A_\varepsilon$ + polar shift (`dampedChebyshevError_eq_dilation`) $=D^{\mu_\varepsilon}$(Möbius-free row) (`dampedChebyshevError_eq_moebiusDilation`); $F_\varepsilon=D^{\Lambda*\Lambda-\Lambda\log}A_\varepsilon$+corr. (log is a derivation, `pmul_log_mul`).
19. Pronic measure is exactly dilation self-similar: fibre mass $1/(j\,m(m+1))$ (`sum_Icc_pronic_dilation_fibre`); contraction exactly $1/\sqrt j$; complete blocks scale pairings by $1/p$ (`pronicPairing_rowDilate_complete_blocks`); incomplete fibre costs $\le CD/p$.
20. Term-by-term route: $\sum_jj^{-(\varepsilon+1/2)}$ converges iff $\varepsilon>\tfrac12$ (`not_summable_dilationSeries_of_le_half`); head $j\le J$ paid, only the tail obstructs.
21. Self-improving identity $E_T=\langle A,\rho\rangle-\langle A,D^{\zeta_\varepsilon,\ge2}A\rangle$, $0\le\rho\le n$; sublinear pairings ⇒ admission at one damping; $\rho=-m_0A^{\rm maj}$, so $\|\rho\|$ unbounded for $\varepsilon\le\tfrac12$ (CS on $\langle A,\rho\rangle$ cannot close).
22. Dirichlet form: $2Q=M-J$ (`two_mul_rowDilationForm_eq`); sign ⇔ Poincaré $J\le M$; creation-potential floor; Beurling–Deny $Q(v)\le Q(|v|)$ (obstruction = sign changes); prime-power steps reduce to single primes.
23. Hardy: $\|v\|^2\le\frac q{(\sqrt q-1)^2}\|O_qv\|^2$, reverse $\le2(1+1/q)$ (`pronicNorm_sq_le_dilationStepEnergy`) ⇒ prefix energy ⇔ block energy (`singleDamping_admission_tfae`); $O_q$ is injective, two-sided stable, selective (majorant unbounded, parity twin $\gtrsim\log T$).
24. Window means: dilation form $=\sum_j\Lambda(j)j^{-\varepsilon}\langle F_jv,v\rangle$, $F_j$ = pronic adjoint = fibre average.

**G. Accounting of the work.**
25. $W=$ core $+$ window functional $+\langle\mathrm{dev},\psi_\varepsilon\rangle+Q(\mathrm{dev})+$ polar (`signedDampingWork_accounting`); $|Q(\mathrm{dev})|\le\Theta_\varepsilon(T)\cdot$ residual energy.
26. Zero anchor: integrated core is a prime count, $\ge c\sum_{p\le T/2}1/p\to\infty$ (`exists_horizon_integral_workCore_ge`): **core is a $\log\log T$ debt** the deviation must cancel. On $[a,c]$, $a>0$: $\int$core $\le\log\zeta(1+a)-\log\zeta(1+c)$ (paid).
27. Five faces of $-2W$ (deviation−core, $J-M$−polar, Markov, window mean, Möbius-factored); on positive intervals admission ⇔ bound on any one (`obstructingTerms_positive_interval_tfae`).

**H. Zeros, width and unconditional range.**
28. One admitted damping $\varepsilon\le\tfrac12$ translates zeros $\rho\mapsto\rho-\varepsilon$ with multiplicity up to the boundary (`analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings`; Mellin of $L^2$ source is $O((\Re s-\tfrac12)^{-1/2})$, less than one power).
29. Admitted for $\varepsilon>\Theta-\tfrac12$; eight continuation forms equivalent (`signedAveragedContinuation_tfae`); threshold infimum $=\Theta-\tfrac12$; boundary attained only with critical shadow; unconditional on VK band and with sub-power saving $T^{1-2a}e^{-\kappa\sigma(T)/270}$.
30. Short/long split: $A_\varepsilon(n)$ = short sawtooth ($d\le D$) + signed long-modulus quadrature (`pmPowerDampedCenteredDivisorPrefix_eq_short_add_quadrature`); at $D=\sqrt n$ short head has bounded pronic energy for $0<\varepsilon<1$ (`sum_pmShortModulusSawtooth_sqrt_pronic_le`).
31. Function field: $A^{\mathbb F_q}_\varepsilon(n)=q^{-\varepsilon}$ constant; energy $\le1$ uniformly; any degree-2 mass breaks it.
32. Complementary sectors: head energy $=(1-\alpha_P)^2\|L_P\|^2+\|R_P\|^2$, $\alpha_P\to1$; cutoff transitions contract; contractive stage recurrence ⇔ admission.

**I. Aperture face.**
33. Weil polarization $Q_a=E_+-E_-$; compensated bound $E_-\le E_++B\|u\|^2$ ⇔ $\mu(a)\ge-B$; uncompensated ⇔ bounded off-line depth mass; at $a\le3/10$, $B=-1/5000$.
34. Shell flux: $\mu(a)-\mu(b)$ = relaxation energy $\ge0$ (`energy_sub_energy_eq_shiftedForm`), family-universal; literal flow strictly decreasing (translation invariance + compact BS kernel + independent translates, `strictAnti_ccmRestrictedWeilGroundEnergy`); ≤ one crossing.
35. Frozen primes at $\lfloor e^{2a}\rfloor$: step = frozen relaxation + arithmetic jump bracketed by shell correlations, which read only the collars; threshold ladder $A_{j+1}=\tfrac12\log(j+2)$ has zero arithmetic jump (`riemannHypothesis_iff_sum_frozen_relaxation_le`); every frozen family collapses $\le-\alpha e^c$ (`not_exists_subtrivial_exp_floor_frozenFamily`).
36. Rates: trivial floor $\sigma=\tfrac12$ unconditional (`compensatedWidthFloor_half`); polar = full rate unconditionally (`groundEnergyRate_eq_polarGroundEnergyRate`); in the CCM form domain, form, polar-form and Birman–Schwinger rates equal the width unconditionally (`formGroundEnergyRate_eq_zetaZeroWidth`, `birmanSchwingerNormRate_eq_zetaZeroWidth`).
37. Aperture transport: fixed positive margins impossible (doubly exponential ceiling, `not_additive_step_transport`); vanishing relative steps with strict positivity ⇒ RH; graded negative-floor steps ⇒ `CompensatedWidthFloor σ` (`zetaZeroWidth_le_of_graded_aperture_step`).

**J. Undamped Hilbert energy.**
38. For all large T, uniformly over every N≤T, the actual signed form
    `H(N)=Σ_{m,n≤N}μ(m)μ(n)/(m+n)` satisfies
    `0≤H(N)≤C T exp(−κ vkScale(T)/27)`
    (`exists_uniform_mobiusHilbert_le_vinogradovKorobov`). Abel–Cauchy bounds
    H by Mertens squares; a split at √T retains the VK saving without assuming
    H is monotone. Subpower growth remains open.

## 5. Pillar theorems

| Theorem | Content |
|---|---|
| `riemannHypothesis_iff_cofinallyAdmits` | RH ⇔ cofinal admission of $E_T$ (reference equivalence) |
| `averagedContinuation_iff_admits` | averaged budget on $[a,c]$ ⇔ admission at $a$ |
| `signedAveragedContinuation_tfae`, `sInf_averagedContinuationThresholds_eq_zetaZeroAbscissa_sub_half` | eight forms; threshold = width |
| `tendsto_dampedMobiusEnergy_nhdsGT_zero`, `exists_unbounded_interior_bump_of_not_riemannHypothesis` | both ends paid; escape is an interior bump |
| `signedDampingWork_eq_pairing_add_integral`, `riemannHypothesis_of_nonneg_tangentCorrelation` | sign = angle of tangents |
| `admits_iff_relative_precision_inv_T_primePair` | prime-pair cancellation to precision $1/T$ |
| `prefixDilation_comp`, `dampedChebyshevError_eq_dilation` | dilation calculus |
| `two_mul_rowDilationForm_eq`, `pronicNorm_sq_le_dilationStepEnergy`, `singleDamping_admission_tfae` | Dirichlet form, Hardy, block energy |
| `not_admits_majorantEnergy`, `admits_majorantEnergy_iff_half_lt` | size-blind source admitted iff $\varepsilon>\tfrac12$ |
| `exists_horizon_integral_workCore_ge`, `obstructingTerms_positive_interval_tfae` | core debt; obstruction faces |
| `analyticOrderAt_le_analyticOrderAt_sub_of_mem_receiverDampings` | zero translation with multiplicity |
| `pmPowerDampedCenteredDivisorPrefix_eq_short_add_quadrature`, `sum_pmShortModulusSawtooth_sqrt_pronic_le` | long-modulus quadrature is the whole obligation |
| `strictAnti_ccmRestrictedWeilGroundEnergy`, `apertureFlow_step_eq_geometric_add_arithmetic`, `relativeFluxLaw_isClassIII` | aperture shell flow |
| `groundEnergyRate_eq_polarGroundEnergyRate`, `formGroundEnergyRate_eq_zetaZeroWidth` | rate equalities |
| `fqCenteredPrefix_eq` | function-field calibration |
| `exists_uniform_mobiusHilbert_le_vinogradovKorobov` | undamped Hilbert energy: VK saving uniformly for N≤T |

## 6. Tools

**Developed.** Transport calculus (master inequality, Grönwall, Osgood, superlinear scale, affine
envelopes, relative-decay floors); horizon sparsification (dyadic, Cesàro); exact work identities
(derivative, integral, Markov, level sum, max-kernel); tangent Gram calculus; dilation calculus
(composition, twist homomorphism, inversion law, Möbius factorization, second-order kernel);
pronic self-similarity (exact fibres, $1/\sqrt j$, complete/incomplete blocks); Dirichlet form and
Hardy inequality on the dilation graph; stable selective observation $O_q$; capped-row and
pronic tail masses; short/long modulus decomposition; zero-translation Mellin estimate; aperture
shell-flux, frozen-family and collar decomposition; polar-parity decomposition; rotated-disk
sampling with log packet ceiling; exponential-tilt stability in the CCM form norm.

**To build.** A horizon-free signed bound on the long-modulus quadrature (or any obstruction face)
at one $\varepsilon<\tfrac12$; a relative-precision-$1/T$ prime-pair estimate; a source-derived
bound on the arithmetic shell jump relative to $\mu$ that reads every prime weight; a contraction
for sector compensation below ½.

## 7. Open questions

1. Continuation on a fixed $[a,\tfrac12]$, $a<\tfrac12$ (zero-free strip), in any of the eight equivalent forms; then cofinally.
2. Pronic energy of the long-modulus quadrature at one $\varepsilon<\tfrac12$.
3. Signed bound on the deviation (any face) on a positive interval, keeping the sign (majorant and parity twin refute sign-blind routes).
4. Accumulated tangent anti-correlation below ½ beyond the double-integral identity.
5. Which prime-pair information gives relative-precision $1/T$ cancellation at fixed damping.
6. Quantitative prime-shell control: bound the arithmetic jump along ground states without presupposing the floor (Class III: must read exact prime weights).
7. Physical-$L^2$ rate = width without a non-clustering input (form-domain version proved).
8. Quantify the number-field defect from the constant function-field prefix.

## 8. Traps

| Trap | Why |
|---|---|
| RH-equivalent restatements as progress | `riemannHypothesis_iff_cofinallyAdmits`, `_cofinal_averagedDampingContinuation`, `_cofinal_work_integral_bound`, `_cofinal_double_integral_tangentCorrelation`, `_iff_pairedMinusEnergy_le_pairedPlusEnergy`, `_iff_birmanSchwingerNormRate_eq_zero`, `vanishing_aperture_transport_tfae` are reformulations |
| Horizon-dependent budget | `escapeEnergy` obeys an exact linear law and is admitted nowhere below ½ |
| Pointwise budget as target | not implied by admission; the averaged form is exact |
| Tangent-norm bounds | strictly stronger than the signed demand |
| Absolute/term-by-term dilation estimates | diverge exactly at ½ |
| Size-blind arguments | majorant $d^{-\varepsilon}$ never admitted for $\varepsilon\le\tfrac12$ |
| Positivity of the dilation kernel | zero diagonal, indefinite; sign only for the literal source |
| Core positivity "helps" | at the zero anchor the core is a $\log\log T$ debt |
| Global $W\ge0$ | false at $T=1$ |
| Leading-order prime asymptotics | polar pieces cancel only to relative precision $1/T$ |
| Ratio smallness / adding sector energies | not a bound; cross terms carry $m^2$ |
| Combined pairing with $\kappa=0$ in `singleDamping_admission_tfae` | is the energy identity itself |
| Fixed positive aperture margin | incompatible with the doubly exponential ceiling |
| Relative flux law with nonnegative factors | equals RH and fails for every one-prime perturbation |
| Frozen-prime operators | no subtrivial floor; the shell must be unfrozen |
| Shell-flux identities decide the sign | family-universal; decide shape only |
| Form-domain rate = $L^2$ rate | physical $L^2$ needs non-clustering |

## 9. Context

| Programme | Relation (verified imports) |
|---|---|
| RHTower | source, receiver dampings, zero abscissa, Möbius floor summatory, CCM restricted Weil operator and pole/Schur infrastructure, packet density (23 imports) |
| BezoutValuationIncidence | tangent form, pronic norm, Markov flux, linear cusp, Littlewood admission, VK band, hyperbola cancellation; BVI imports escape-tail, damping-average and zero-translation modules |
| TransHorizonIncidenceMechanics | first-moment/Chebyshev bridge, parity pair, oscillating power at zeros |
| SquareRootThreshold | contact aperture, width, unsigned depth sampling, Landau exponent rates |
| ArithmeticCriticalityTheory | certified $\mu(3/10)\ge1/5000$ |
| ArithmeticCompensationTheory | ACCE imports origin cost, doubly exponential floor decay, core-debt zeta-log ratio; ACompT imports the critical energy, averaged budget, Möbius dilation, majorant, self-similarity, core debt, aperture transport |
| ArithmeticDefectRigidity | imports pronic self-similarity, capped-row cost, exact/incomplete dilation blocks, Hardy, block energy |
| SignedArithmeticEnergyIncidence | two-way: Hilbert–Schmidt chain in; critical energy, inversion defect, escape tail out |
| ArithmeticOrientationTheory | imports aperture floor transport modules |
| ArithmeticCorrespondencePositivity, BiarithmeticGeometry, ArithmeticGaugeTheory, ArithmeticEffectivityTheory, ArithmeticCorrelationGeometry | single imports (self-similarity, zero-width band, function field, tangent dilation, critical energy) |

## 10. Big picture

ACCE recasts RH as a question of survival rather than sign: finite energy at an easy end must
survive transport to the critical end, uniformly in the horizon. Every exact identity the
programme proves — derivative, angle, dilation, Dirichlet form, prime-pair level sum, shell flux —
shows the same thing from a different side: the easy ends are paid, the cutoff is free, the short
moduli are paid, the scalar moment is paid, and what remains is one signed cancellation in the
long-modulus Möbius tail, at relative precision $1/T$, against a positive prime-harmonic debt. The
transport machinery does not supply that cancellation; it locates it, prices it in the width unit,
and refutes every route that ignores signs (majorant), ignores exact prime weights (Class III,
frozen primes) or estimates terms separately (indefinite kernel, divergent dilation series at ½).
The function-field model shows the mechanism itself is sound — with exact higher-degree Möbius
cancellation there is nothing to transport — so the number-field difficulty is that cancellation
and nothing else. For the RH proof this means: continuation frameworks are complete as
bookkeeping, and the only admissible new input is a sign-reading estimate on the long-modulus
quadrature (equivalently the prime-shell correlation) below half damping.
