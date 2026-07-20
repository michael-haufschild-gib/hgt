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

## Scientific status and open core

The mathematics is classical; the contribution is the dependency-closed Lean bridge, the
continuous phase construction, and the exact identification with the corpus's positive theta
source.  It closes the `HardyZ.lean` substrate item in
`hardy-critical-line-moment-anchor.md` but does **not** prove a critical-line zero.  The exact open
core remains analytic: a symmetric approximate functional equation with height-dependent cutoff,
the required zeta moment estimates, and the Hardy mean/sign-change inequality.  The corpus already
contains the needed first/second derivative-test machinery; the newly discharged differentiability
interfaces do not supply the missing height-dependent AFE estimates.  No RH statement is claimed
here.
