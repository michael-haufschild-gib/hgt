# Continuous Hardy Z from the normalized Gamma phase

- **ID:** continuous-hardy-z-gamma-phase
- **Stage:** 3-formalized
- **Type:** THEOREM `[LEAN-PROVED]`; classical Hardy/Riemann--Siegel real-amplitude law;
  honestly `not_new_scientific_knowledge`
- **Source:** Riemann zeta functional equation, Schwarz reflection, and the nonvanishing of
  `Gammaℝ` on `Re s > 0`
- **Formalization:**
  `formal/GaloisForLFunctions/HTGeometry/UnitaryReflectionPhaseHalving.lean`,
  `formal/GaloisForLFunctions/RHTower/HardyCarrier.lean`,
  `formal/GaloisForLFunctions/RHTower/HardyZ.lean`,
  `formal/GaloisForLFunctions/RHTower/HardyZPhaseAsymptotic.lean`,
  `formal/GaloisForLFunctions/RHTower/HardyZThetaTrace.lean`,
  `formal/GaloisForLFunctions/RHTower/HardyZSignChange.lean`

## Exact law

For `s(t)=1/2+it`, set

```text
w(t) = conjugate(Gammaℝ(s(t))) / norm(Gammaℝ(s(t))).
```

Then `w` is differentiable (hence continuous), `conjugate(w)w=1`, and

```text
w(t)^2 = zetaChi(s(t)),
zeta(s(t)) = w(t) * hardyZ(t),
hardyZ(t) in R.
```

The residual phase orientation is now discharged exactly.  Define the global real lift

```text
theta(t) = integral_[0,t] (Re(digamma(1/4+iu/2))/2 - log(pi)/2) du.
```

The central Gamma value is a positive real, hence `w(0)=1`, and the phase differential law
integrates without any branch choice or undetermined constant:

```text
w(t) = exp(-i*theta(t)),
zeta(1/2+it) = exp(-i*theta(t)) * hardyZ(t),
exp(i*theta(t)) * zeta(1/2+it) = hardyZ(t).
```

More generally, every complex value reflected by this Gamma phase equals `exp(-i*theta(t))`
times its canonical real phase-halved amplitude.  This one exponential normal form simultaneously
covers zeta, `gN`, and the symmetrized Euler--Maclaurin carrier, so their critical-line
approximation errors are entirely real after the same exact unwinding.

The same general law is now closed at first-jet level.  For every differentiable reflected path
`z(t)=exp(-i*theta(t))*A(t)` with real canonical amplitude `A`,

```text
exp(i*theta(t)) * z'(t) = A'(t) - i*theta'(t)*A(t).
```

It specializes both to zeta/Hardy Z and to every finite `gN`/`gammaHardyCarrier`.  At a zero the
phase-velocity term vanishes, so complex transversality and real-amplitude transversality are
equivalent.  In particular,

```text
zeta(1/2+it) = 0
  implies
(zeta'(1/2+it) = 0  iff  hardyZ'(t) = 0).
```

This discharges the simple-zero/first-jet Prop interface without assuming that any such zero
exists or is simple.

The lift is differentiable and odd, with exact velocity

```text
theta'(t) = Re(digamma(1/4+it/2))/2 - log(pi)/2.
```

The corpus's vertical digamma asymptotic gives the unconditional first-order law

```text
theta'(t) - (1/2)*log(t/(2*pi)) -> 0  as t -> +infinity.
```

The general asymptotic-integration law extracted alongside it then gives the phase-value form

```text
(theta(t) - ((t/2)*log(t/(2*pi)) - t/2)) / t -> 0.
```

Thus `theta'`, `theta(t)/t`, and `theta(t)` tend to positive infinity.  The phase is strictly
increasing on some terminal ray, and on a possibly enlarged terminal ray it is a bijection onto
the ray beginning at its boundary value.  Every sufficiently large phase level therefore has a
unique positive-tail height, giving an exact Gram-point/Riemann--Siegel Prop interface.
This closes the global branch, orientation, exact first derivative, and first-order derivative and
value asymptotic interfaces; it does not supply the quantitative second derivative or remainder
bounds needed by the smooth approximate functional equation.

This uses the normalized Gamma value rather than a principal-log square root.  It therefore
discharges the global phase-continuity premise that the existing finite Hardy carrier could only
avoid after squaring.

The same phase also supplies a globally oriented finite carrier

```text
gammaHardyCarrier_N(t)
  = Re(conjugate(w(t)) * gN_N(1/2+it)).
```

It is differentiable and even, has exactly the zeros and modulus of `gN`, and gives the exact polar
decomposition `gN = w * gammaHardyCarrier_N`.  The old principal-log phase and `w` square to the
same `zetaChi`, hence differ pointwise by exactly one sign.  Consequently

```text
hardyCarrier_N(t) = gammaHardyCarrier_N(t)
  or hardyCarrier_N(t) = -gammaHardyCarrier_N(t),
hardyCarrier_N(t)^2 = gammaHardyCarrier_N(t)^2.
```

This identifies and removes the old branch-continuity obstruction without changing any squared
finite-carrier moment.

At the completed level, one general archimedean scale law now covers every value carrying this
phase.  Instantiating it gives both the Xi/Hardy-Z identity and

```text
completedGN_N(1/2+it)
  = -(1/4+t^2)/2 * norm(Gammaℝ(1/2+it)) * gammaHardyCarrier_N(t).
```

Thus completed, raw, and continuous-real finite-carrier zeros agree exactly.  Continuity also
closes the finite sign and moment interfaces: a sign bracket, or the generic second/first-moment
gap for `gammaHardyCarrier_N`, produces an actual on-line zero of `gN_N`.

The exact completed-value bridge is

```text
xi(s(t)) = -(1/4+t^2)/2 * norm(Gammaℝ(s(t))) * hardyZ(t).
```

Consequently, with no zeta nonvanishing hypothesis,

```text
zeta(s(t)) = 0  iff  hardyZ(t) = 0  iff  xi(s(t)) = 0,
hardyZ(t)^2 = norm(zeta(s(t)))^2.
```

The coefficient-side positivity of Xi at the real centre also fixes the global sign convention:

```text
hardyZ(0) < 0.
```

This is an unconditional starting sign for later critical-line sign-change arguments.

The already-formalized positive theta-cusp trace now meets this Hardy normalization exactly.  Set

```text
A(t) = (1/4+t^2) * norm(Gammaℝ(s(t))) > 0.
```

Then

```text
A(t) * hardyZ(t)
  = -4 * integral_(0,infinity) thetaCuspFullSource(x) * cos(t*x) dx.
```

Equivalently, if `F+` is the Fourier transform of `xiThetaPositiveSource`,

```text
norm(Gammaℝ(s(t))) * hardyZ(t)
  = Re(F+(t/(4*pi))) - 1/(1/4+t^2).
```

The positivity of `A(t)` discharges all denominator premises and gives the value reflections

```text
hardyZ(t) < 0  iff  the theta-cusp cosine trace is positive,
zeta(s(t)) = 0 iff  the theta-cusp cosine trace is zero,
zeta(s(t)) = 0 iff  Re(F+(t/(4*pi))) = 1/(1/4+t^2).
```

These are exact source-level interfaces, not evidence for a zero or for RH.

Direct conjugation of the Gamma phase, zeta, and every symmetrized carrier closes the missing
height reflection (and the positive Xi scale is compatible with it):

```text
Xi(-t) = Xi(t),
A(-t) = A(t),
hardyZ(-t) = hardyZ(t),
hardySEM_N(-t) = hardySEM_N(t).
```

Thus Hardy Z is globally even without selecting or comparing logarithmic phase branches.  The
Gamma phase, zeta line restriction, every continuously oriented finite carrier, and every
nontrivial symmetrized-EM approximant are in fact globally real differentiable.  Differentiating
the height reflections gives the unconditional first-jet laws

```text
hardyZ'(-t) = -hardyZ'(t),
gammaHardyCarrier_N'(-t) = -gammaHardyCarrier_N'(t),
hardySEM_N'(-t) = -hardySEM_N'(t),
```

and all three derivatives vanish at the reflection centre.  These are regularity and symmetry
interfaces only; they assert no zero away from the centre.

At the Prop boundary, a two-height Hardy-Z bracket or theta-cusp cosine bracket now produces an
actual zeta zero between the heights.  The generic corpus moment-gap theorem is also specialized
all the way through continuity and the zeta-zero interface:

```text
0 < S,
S <= integral_[a,b] hardyZ(t)^2 dt,
abs(hardyZ(t)) <= M on [a,b],
M * abs(integral_[a,b] hardyZ(t) dt) < S
  implies
there exists t in [a,b] with zeta(1/2+it) = 0.
```

Thus the formal interface now ends exactly where the genuinely analytic moment estimates begin.

The real symmetrized Euler--Maclaurin approximation also supplies a finite, exact certificate
interface.  If two values `hardySEM_N(t1)` and `hardySEM_N(t2)` have opposite signs and each
strictly exceeds its named pointwise error budget in absolute value, then the actual Hardy values
have the same respective signs and zeta has a genuine critical-line zero between `t1` and `t2`.
This is a theorem schema only; no numerical witness or computation is used here.

Pointwise convergence makes that certificate complete:

```text
zeta(1/2+it) != 0
  iff
there exists N >= 1 with hardySEMError_N(t) < abs(hardySEM_N(t)),

zeta(1/2+it) = 0
  iff
for every N >= 1, abs(hardySEM_N(t)) <= hardySEMError_N(t).
```

The existential direction follows from convergence; it does not provide or use a computed cutoff.
The universal zero test can be weakened from every level to an eventual tail condition: a nonzero
value forces all sufficiently large levels to clear the shrinking cone strictly.

The squared Hardy amplitude is interval-integrable on every finite window.

The existing symmetrized Euler--Maclaurin carrier now descends through the same continuous phase.
Writing `hardySEM_N` for half of its real amplitude gives the exact error isometry

```text
2 * abs(hardyZ(t) - hardySEM_N(t))
  = norm(2*zeta(s(t)) - semCarrier_N(s(t)))
```

and hence the unconditional pointwise bound

```text
abs(hardyZ(t) - hardySEM_N(t))
  <= 2 * norm(s(t)) * N^(-1/2),    N >= 1.
```

Thus the complex Euler--Maclaurin approximation and its functional equation now expose a continuous
real critical-line approximant without a new analytic hypothesis.

The explicit error also closes the limiting interface:

```text
hardySEM_N(t) -> hardyZ(t) as N -> infinity,
```

pointwise at every height and uniformly on every symmetric compact window `[-R,R]`.

## General law extracted

`UnitaryReflectionPhaseHalving.lean` proves for arbitrary complex values that

```text
conjugate(w) * w = 1
  implies
(w^2 * conjugate(z) = z  iff  Im(conjugate(w) * z) = 0).
```

It also gives the exact real polar normal form, norm law, and zero interface.  The existing finite
carrier `gN` and the actual zeta value now instantiate this one law; the former's norm and zero
proofs were reduced to the shared interface.

For differentiable complex paths `w(t), z(t)`, it also extracts the exact first-jet law

```text
d/dt amplitude(w,z)
  = Re(conjugate(w')*z + conjugate(w)*z').
```

The corresponding general differentiability-transfer theorem applies on every real normed
parameter space and subsumes the separate Hardy-Z, finite-carrier, and symmetrized-EM regularity
proofs.

The fixed-locus classification is now bidirectional and unique:

```text
IsPhaseReflected(w,z)
  iff
there exists a unique r in R with z = w*r.
```

Thus phase halving identifies the whole reflected complex fixed locus with one real line, rather
than only constructing an amplitude after a reflection proof has already been supplied.

For any two values carrying the same unitary phase, the shared law also gives

```text
conjugate(z) * y = amplitude(z) * amplitude(y),
norm(a*z - b*y) = abs(a*amplitude(z) - b*amplitude(y))  for a,b in R.
```

This common-phase correlation/isometry law subsumes the bespoke complex algebra in the
Hardy-Z/symmetrized-EM error identity and exposes the whole common-phase Gram geometry as real.
Concretely, zeta, `gN`, and `semCarrier/2` form an exact real-isometric comparison triangle on the
critical line:

```text
norm(zeta - gN_N) = abs(hardyZ - gammaHardyCarrier_N),
norm(zeta - semCarrier_M/2) = abs(hardyZ - hardySEM_M),
norm(gN_N - semCarrier_M/2) = abs(gammaHardyCarrier_N - hardySEM_M).
```

The first and third identities assert no unproved accuracy for `gN`; they expose precisely where
such an estimate would enter.

The finite sign interface is complete as well: two actual Hardy values have strictly opposite
signs if and only if one common finite level clears both pointwise error cones and its two real
approximants have opposite signs.  Via the positive theta scale, the identical finite certificate
characterizes strict opposite signs of the two theta-cusp cosine traces.

## Formal theorem surface

- `IsUnitaryPhase`, `IsPhaseReflected`, `phaseHalvedAmplitude`
- `phaseHalvedAmplitude_conj`
- `hasDerivAt_phaseHalvedAmplitude`, `differentiable_phaseHalvedAmplitude`
- `isPhaseReflected_iff_rotated_im_eq_zero`
- `IsPhaseReflected.eq_phase_mul_amplitude`
- `IsUnitaryPhase.ne_zero`
- `isPhaseReflected_iff_existsUnique_phase_mul`
- `IsPhaseReflected.conj_mul_eq_amplitude_mul_amplitude`
- `IsPhaseReflected.norm_real_mul_sub_real_mul_eq_abs_amplitude_sub`
- `IsPhaseReflected.norm_eq_abs_amplitude`
- `IsPhaseReflected.eq_zero_iff_amplitude_eq_zero`
- `riemannZeta_conj_of_re_pos`
- `riemannZeta_conj_eq_zero_iff_of_re_pos`
- `gammaHardyPhase_isUnitary`, `gammaHardyPhase_sq`
- `gammaHardyPhaseRate`, `hasDerivAt_gammaHardyPhase`
- `gammaHardyPhase_neg`, `riemannZeta_line_neg`
- `differentiable_Gammaℝ_line`, `differentiable_gammaHardyPhase`
- `continuous_gammaHardyPhase`
- `hardyPhase_eq_or_eq_neg_gammaHardyPhase`
- `gN_line_isGammaPhaseReflected`, `gammaHardyCarrier`
- `gN_line_eq_gammaHardyPhase_mul_gammaHardyCarrier`
- `norm_gN_line_eq_abs_gammaHardyCarrier`
- `gN_line_eq_zero_iff_gammaHardyCarrier`
- `differentiable_gN_line`, `differentiable_gammaHardyCarrier`
- `continuous_gammaHardyCarrier`, `even_gammaHardyCarrier`
- `hardyCarrier_eq_or_eq_neg_gammaHardyCarrier`
- `hardyCarrier_sq_eq_gammaHardyCarrier_sq`
- `archFactor_mul_phaseReflected_eq_realScale`
- `completedGN_line_eq_scale_mul_gammaHardyCarrier`
- `completedGN_line_eq_zero_iff_gammaHardyCarrier`
- `zetaChi_mul_conj_riemannZeta_line`
- `riemannZeta_line_isPhaseReflected`
- `conj_gammaHardyPhase_mul_zeta_eq_hardyZ`
- `riemannZeta_line_eq_gammaHardyPhase_mul_hardyZ`
- `gammaHardyTheta`, `hasDerivAt_gammaHardyTheta`, `odd_gammaHardyTheta`
- `gammaHardyPhase_zero`, `gammaHardyPhase_eq_exp_neg_theta`
- `gammaPhaseReflected_eq_exp_neg_theta_mul_amplitude`
- `exp_theta_mul_gammaPhaseReflected_eq_amplitude`
- `riemannZeta_line_eq_exp_neg_theta_mul_hardyZ`
- `exp_theta_mul_riemannZeta_line_eq_hardyZ`
- `gN_line_eq_exp_neg_theta_mul_gammaHardyCarrier`
- `semCarrier_line_eq_exp_neg_theta_mul_two_hardySEM`
- `deriv_gammaPhaseReflected_eq_exp_neg_theta_mul`
- `exp_theta_mul_deriv_gammaPhaseReflected_eq`
- `re_exp_theta_mul_deriv_gammaPhaseReflected_eq_amplitude_deriv`
- `im_exp_theta_mul_deriv_gammaPhaseReflected_eq_neg_rate_mul_amplitude`
- `deriv_gammaPhaseReflected_eq_zero_iff_amplitude_deriv_of_zero`
- `exp_theta_mul_deriv_gN_line`
- `deriv_gN_line_eq_zero_iff_deriv_gammaHardyCarrier_of_zero`
- `exp_theta_mul_deriv_riemannZeta_line`
- `re_exp_theta_mul_deriv_riemannZeta_line`
- `im_exp_theta_mul_deriv_riemannZeta_line`
- `exp_theta_mul_deriv_riemannZeta_line_eq_deriv_hardyZ_of_zero`
- `deriv_riemannZeta_line`, `deriv_riemannZeta_line_eq_zero_iff_deriv_hardyZ_of_zero`
- `deriv_riemannZeta_eq_zero_iff_deriv_hardyZ_of_zero`
- `gammaHardyPhaseRate_sub_log_conductor_tendsto_zero`
- `tendsto_div_atTop_zero_of_deriv_tendsto_zero`
- `gammaHardyThetaMain`, `hasDerivAt_gammaHardyThetaMain`
- `gammaHardyTheta_sub_main_div_tendsto_zero`
- `gammaHardyTheta_div_sub_log_conductor_tendsto_zero`
- `gammaHardyTheta_div_tendsto_atTop`, `gammaHardyTheta_tendsto_atTop`
- `gammaHardyPhaseRate_tendsto_atTop`, `exists_gammaHardyTheta_strictMonoOn`
- `exists_gammaHardyTheta_terminal_bijOn`
- `xi_line_eq_scale_mul_hardyZ`
- `hardyZ_zero_height_neg`
- `riemannZeta_line_eq_zero_iff_hardyZ`
- `xi_line_eq_zero_iff_hardyZ`
- `hardyZ_sq_eq_norm_riemannZeta_line_sq`
- `deriv_neg_of_even`, `deriv_zero_of_even`
- `differentiable_riemannZeta_line`, `differentiable_hardyZ`
- `deriv_hardyZ_neg`, `deriv_hardyZ_zero`
- `deriv_gammaHardyCarrier_neg`, `deriv_gammaHardyCarrier_zero`
- `continuous_hardyZ`, `intervalIntegrable_hardyZ_sq`
- `zetaChi_mul_conj_semCarrier_line`, `semCarrier_line_isPhaseReflected`
- `hardySEM`, `semCarrier_line_eq_two_mul_gammaHardyPhase_mul_hardySEM`
- `two_mul_abs_hardyZ_sub_hardySEM_eq_norm`
- `norm_riemannZeta_line_sub_gN_eq_abs_hardyZ_sub_gammaHardyCarrier`
- `norm_riemannZeta_line_sub_half_semCarrier_eq_abs_hardyZ_sub_hardySEM`
- `norm_gN_line_sub_half_semCarrier_eq_abs_gammaHardyCarrier_sub_hardySEM`
- `differentiable_semCarrier_line`, `differentiable_hardySEM`
- `deriv_hardySEM_neg`, `deriv_hardySEM_zero`
- `abs_hardyZ_sub_hardySEM_le`, `continuous_hardySEM`
- `hardySEM_tendsto_hardyZ`, `hardySEM_tendstoUniformlyOn_Icc`
- `hardyZArchScale`, `hardyZArchScale_pos`
- `Xi_eq_neg_half_hardyZArchScale_mul_hardyZ`
- `Xi_neg`, `Xi_pos_iff_hardyZ_neg`, `Xi_eq_zero_iff_hardyZ`
- `hardyZ_neg`, `even_hardyZ`
- `semCarrier_line_neg`, `hardySEM_neg`, `even_hardySEM`
- `norm_Gammaℝ_mul_hardyZ_eq_re_fourier_xiThetaPositiveSource_sub_correction`
- `hardyZArchScale_mul_hardyZ_eq_neg_four_mul_thetaCuspCosine`
- `hardyZArchScale_pair_mul_hardyZ_pair_eq_sixteen_mul_thetaCuspCosine_pair`
- `hardyZ_mul_nonpos_iff_thetaCuspCosine_mul_nonpos`
- `hardyZ_neg_iff_thetaCuspCosine_pos`
- `hardyZ_neg_iff_re_fourier_xiThetaPositiveSource_lt_correction`
- `riemannZeta_line_eq_zero_iff_thetaCuspCosine`
- `riemannZeta_line_eq_zero_iff_re_fourier_xiThetaPositiveSource`
- `exists_riemannZeta_line_zero_of_hardyZ_sign_bracket`
- `exists_gN_line_zero_of_gammaHardyCarrier_sign_bracket`
- `exists_gN_line_zero_of_gammaHardyCarrier_moment_gap`
- `exists_riemannZeta_line_zero_of_thetaCuspCosine_sign_bracket`
- `exists_riemannZeta_line_zero_of_hardyZ_moment_gap`
- `hardySEMError`, `hardySEMError_neg`, `hardySEMError_tendsto_zero`
- `hardySEMError_nonneg`
- `eventually_hardySEMError_lt_abs_of_hardyZ_ne_zero`
- `hardyZ_mul_hardySEM_pos_of_error_lt_abs`
- `riemannZeta_line_ne_zero_of_hardySEM_error_lt_abs`
- `riemannZeta_line_ne_zero_iff_exists_hardySEM_certificate`
- `riemannZeta_line_eq_zero_iff_forall_hardySEM_trapped`
- `riemannZeta_line_eq_zero_iff_eventually_hardySEM_trapped`
- `thetaCuspCosine_eq_zero_iff_forall_hardySEM_trapped`
- `thetaCuspCosine_ne_zero_iff_exists_hardySEM_certificate`
- `hardyZ_pair_neg_iff_hardySEM_pair_neg_of_error_margins`
- `hardyZ_mul_neg_iff_thetaCuspCosine_mul_neg`
- `hardyZ_pair_neg_iff_exists_hardySEM_certified_pair`
- `thetaCuspCosine_pair_neg_iff_exists_hardySEM_certified_pair`
- `exists_riemannZeta_line_zero_of_hardySEM_certified_sign_bracket`

## 2026-07-20 first-jet, curvature, and source-value extension

`[LEAN-PROVED] [BRIDGE]` The exact theorem surface now also includes:

- `deriv_digamma_partialSum_tendsto`
- `one_div_sq_le_re_deriv_digamma_of_pos`
- `hasDerivAt_re_digamma_ofReal`, `strictMonoOn_re_digamma_ofReal`
- `deriv_digamma_vertical_im_neg`
- `differentiable_hardyZArchScale`, `hardyZArchScale_firstJet`
- `deriv_hardyZ_eq_zero_iff_thetaCuspFirstSineMoment_of_zero`
- `deriv_Xi_eq_hardyZArchScale_firstJet`
- `deriv_Xi_eq_neg_half_scale_mul_deriv_hardyZ_of_zero`
- `deriv_Xi_eq_zero_iff_deriv_hardyZ_of_zero`
- `deriv_Xi_eq_neg_two_mul_thetaCuspFirstSineMoment`
- `deriv_Xi_eq_zero_iff_thetaCuspFirstSineMoment`
- `deriv_Xi_ne_zero_iff_thetaCuspFirstSineMoment_ne_zero`
- `hasDerivAt_gammaHardyPhaseRate`, `deriv_gammaHardyPhaseRate`
- `strictMonoOn_gammaHardyPhaseRate`, `strictAntiOn_gammaHardyPhaseRate`
- `strictConvexOn_gammaHardyTheta`, `strictConcaveOn_gammaHardyTheta`
- `abs_deriv_gammaHardyPhaseRate_le`, `windingRateDeriv_abs_le_sharp`
- `gammaHardyPhaseRate_sub_log_conductor_bound`
- `existsUnique_pos_gammaHardyPhaseRate_eq_zero`
- `gammaHardyTheta_morseGeometry_of_rate_eq_zero`
- `gammaHardyTheta_eq_minimum_iff_of_rate_eq_zero`
- `gammaHardyTheta_bijOn_Ici_of_rate_eq_zero`
- `factorial_nsmul_iterate_dslope_self_eq_iteratedDeriv`
- `iterate_dslope_self_eq_iteratedDeriv_div_factorial`
- `xiThetaDividedChain_self_eq_iteratedDeriv_div_factorial`
- `iteratedDeriv_XiC_neg`, `xiThetaDividedChain_self_neg`
- `iteratedDeriv_XiC_eq_zero_before_supportMultiplicity`
- `iteratedDeriv_XiC_ne_zero_at_supportMultiplicity`
- `xiSupportMultiplicity_eq_iff_iteratedDeriv`
- `xiSupportMultiplicity_reflect`
- `thetaCuspFourierLaplaceJetIntegrand`
- `integrable_abs_pow_mul_exp_neg_mul_abs`
- `integrable_thetaCuspFourierLaplaceJetIntegrand`
- `hasDerivAt_integral_thetaCuspFourierLaplaceJet`
- `iteratedDeriv_thetaCuspFourierLaplace_eq_integral_jet`
- `iteratedDeriv_thetaCuspFourierLaplace_eq_iteratedDeriv_XiC`
- `iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet`
- `xiC_zero_mem_thetaCuspFourierLaplaceStrip`
- `xiSpectralPointSupport_mem_thetaCuspFourierLaplaceStrip`
- `xiThetaDividedChain_self_eq_integral_thetaCuspFourierLaplaceJet_div_factorial`
- `xiThetaDividedChain_self_eq_integral_thetaCuspFourierLaplaceJet_div_factorial_of_zero`
- `xiSupportMultiplicity_eq_iff_thetaCuspFourierLaplaceJet`
- `thetaCuspBoundaryReflectionDefect`
- `thetaCuspBoundaryReflectionDefect_eq`
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect`
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect_eq_zero_before_supportMultiplicity`
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect_at_supportMultiplicity`
- `iteratedDeriv_thetaCuspBoundaryReflectionDefect_ne_zero_at_supportMultiplicity`
- `xiSupportMultiplicity_eq_iff_thetaCuspBoundaryReflectionDefectJet`
- `integral_thetaCuspFourierLaplaceJet_neg`
- `iteratedDeriv_XiC_conj`
- `integral_thetaCuspFourierLaplaceJet_conj`
- `integral_thetaCuspFourierLaplaceJet_neg_conj`
- `integral_thetaCuspFourierLaplaceJet_ofReal`
- `xiSupportMultiplicity_eq_iff_thetaCuspCosineDerivativeIntegral`
- `xiSpectralPointSupport_eq_ofReal_of_rh`
- `xiSupportMultiplicity_eq_iff_thetaCuspCosineDerivativeIntegral_of_rh`
- `xiThetaEigenFourier_self_eq_I_mul_thetaCuspFourierLaplaceFirstMoment`
- `xiThetaEigenFourier_self_eq_I_mul_thetaCuspFourierLaplaceFirstMoment_of_zero`
- `xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplace_deriv_ne_zero`
- `xiThetaFirstQuotientValueConstraint_iff_thetaCuspFourierLaplaceFirstMoment_ne_zero`
- `continuedPrimeArchUpperCauchy_and_thetaCuspFourierLaplaceFirstMoment_iff_rh_and_simple`
- `continuedPrimeArchUpperCauchy_and_thetaCuspFourierLaplaceFirstMoment_iff_exists_conservative_metric`
- `riemannHypothesis_and_xiZerosSimple_iff_thetaCuspFirstSineMoment`
- `riemannHypothesis_and_xiThetaFirstQuotientValueConstraint_iff_thetaCuspFirstSineMoment`
- `continuedPrimeArchUpperCauchy_and_thetaCuspFirstSineMoment_iff_rh_and_simple`
- `continuedPrimeArchUpperCauchy_and_thetaCuspFirstSineMoment_iff_exists_conservative_metric`

The source-value law is now all-order, not only first-order.  Over every complete
characteristic-zero nontrivially normed field, `k!` times the value after `k` removable divided
slopes of an analytic map into any complete normed space is its `k`-th derivative; the scalar
division form is an immediate corollary.  Applied to centered Xi, this
identifies the complete Hedenmalm multiplicity chain with the normalized Taylor jet.  Uniform
dominated differentiation on the entire theta Fourier--Laplace strip then identifies that jet with
the explicit moment weighted by `(-i x)^k`.  Every centered Xi zero lies in the strip, so the strip
premise disappears on the divisor.  Analytic multiplicity `k` is therefore equivalent to vanishing
of all explicit source moments below `k` and nonvanishing of the order-`k` moment.  At `k = 1`, the
Hedenmalm quotient self-value is exactly `i` times the differentiated source integral, and the
resulting first-moment condition is unconditionally equivalent to the Hedenmalm quotient constraint
and global Xi simplicity.  Under RH it specializes to nonvanishing of the real positive-theta sine
moment at every real Xi zero.  Centered Xi evenness and Schwarz reality now propagate through the
entire jet/source chain: negation contributes `(-1)^k`, conjugation conjugates the value, their
composition does both, and reflected divisor support points have exactly equal analytic
multiplicity.  On the real centered axis the two-sided complex jet integral is exactly the
complexification of the pre-existing positive-half cosine-phase derivative integral; consequently,
at a real divisor support point, the first nonzero member of that real integral hierarchy is the
exact analytic multiplicity.  Under RH the support point is canonically the complexification of
its real part, so this last interface no longer carries an existential multiplicity-copy witness
or a caller-supplied coordinate equality.

The same classification now closes the higher-order seam in the one-sided Hedenmalm boundary
primitive.  For every logarithmic cut, its unnormalized anti-reflection defect is the Xi function
times an explicit nonvanishing exponential gauge.  The full defect jet is the corresponding
triangular Leibniz transform; at a divisor of multiplicity `m`, all orders below `m` vanish and the
order-`m` defect jet is the cut exponential times the explicit order-`m` theta source moment.
Hence every cut reads exactly the same multiplicity, without normalizing away the boundary value.
This covariance supplies no estimate forcing the first moment to be nonzero.

Focused `lake env lean` checks passed for `ReflectedDividedDifference.lean`,
`ThetaCuspFourierLaplace.lean`, `XiHedenmalmMultiplicityChain.lean`,
`HardyZThetaTrace.lean`, and `XiHedenmalmThetaJetSource.lean`.  A `/tmp`
`#print axioms` audit reports only `propext`, `Classical.choice`, and `Quot.sound` for the audited
declarations above.

## Scientific status and open core

The mathematics is classical; the contribution is the dependency-closed Lean bridge, the
continuous phase construction, and the exact identification with the corpus's positive theta
source.  It closes the `HardyZ.lean` substrate item in
`hardy-critical-line-moment-anchor.md` but does **not** prove a critical-line zero.  The exact open
core remains analytic: a symmetric approximate functional equation with height-dependent cutoff,
the required zeta moment estimates, and the Hardy mean/sign-change inequality.  The corpus already
contains the needed first/second derivative-test machinery; the newly discharged differentiability,
first-jet, source-value, and exact global phase interfaces do not supply the missing
height-dependent AFE estimates.  The first-order laws
`theta'(t) = (1/2)log(t/(2*pi)) + o(1)` and
`theta(t) = (t/2)log(t/(2*pi)) - t/2 + o(t)` are closed, as are an explicit rate-error bound, a
coarse unconditional second-jet bound, strict half-line curvature, and the unique positive phase
minimum.  What remains open for the smooth AFE is the sharper complex-uniform asymptotic control
and the source/moment estimates, not the real branch-free phase geometry.  The Hedenmalm/source
equivalences characterize `RH + simplicity`; they prove neither conjunct.  No RH statement is
claimed here.
