# Coupled Sonin projective quantum-Fisher reduction

- **ID:** sonin-coupled-projective-quantum-fisher
- **Stage:** 1-in-progress
- **Type:** `[BRIDGE] [FORMALIZATION SOURCE] [OPEN CORE]`
- **Physics source:** pure-state Fubini--Study/quantum-Fisher geometry and the
  Anandan--Aharonov uncertainty-speed relation
- **Statement:** The aperture-dependent scalar counterterm in the coupled vacuum-Feshbach source
  interface can be replaced by one gauge-invariant two-vector source Gram determinant.  A
  one-sided comparison of that projective source value with the target Feshbach remainder implies
  RH.

## Goal

Remove the remaining scalar choice from the vacuum-Feshbach source theorem.  The prior weakest
interface chooses, for every zero-constant integer tail `q` and error `epsilon`, both

```text
an aperture a,
a real scalar counterterm c,
```

and compares the nonnegative norm `||V_a(q-c)||^2` with the fixed prime--Gamma Feshbach remainder.
Quantum projective geometry says that the scalar direction is gauge, so the correct invariant
source value is its two-channel Gram determinant rather than an optimized representative.

## Exact physics value relation

For real Gram coordinates

```text
mass      = <psi,psi>,
overlap   = <psi,dpsi>,
speedSq   = <dpsi,dpsi>,
```

define

```text
Dproj = mass*speedSq-overlap^2,
shifted(c) = speedSq-2*c*overlap+c^2*mass.
```

Then

```text
mass*shifted(c) = Dproj + (mass*c-overlap)^2.                 (1)
```

Consequences formalized in
`formal/GaloisForLFunctions/HTGeometry/ProjectiveQuantumFisherValue.lean` are:

```text
Dproj is invariant under dpsi -> dpsi-c*psi,
Dproj/mass <= shifted(c)                         if mass>0,
shifted(overlap/mass) = Dproj/mass,
F_Q = 4*Dproj/mass^2.
```

For arbitrary vectors in a real or complex Hilbert space, the intrinsic value

```text
||psi||^2 ||dpsi||^2 - |<psi,dpsi>|^2
```

is nonnegative by Cauchy--Schwarz.  This is the unnormalised Fubini--Study tangent metric and the
two-vector Gram determinant.

This is a static constraint value.  The parameter language of quantum evolution is not used to
propagate the hypertranscendental object.

## General HTGeometry application

The existing vacuum Robertson determinant is now identified exactly as

```text
momentVacuumRobertsonDeterminant(s,q)
  = projectiveQuantumTangentValue
      (s_0, L_s(q), L_s(q^2)).
```

The existing Feshbach remainder is therefore the corresponding projective variance, and its
normalized pure-state quantum Fisher value is

```text
F_Q(s,q) = 4 * momentVacuumFeshbachRemainder(s,q) / s_0.      (2)
```

Both statements are source-formalized in
`formal/GaloisForLFunctions/HTGeometry/VacuumFeshbachValue.lean`.  They apply to every moment
functional using that module, not only the zeta specialization.

`formal/GaloisForLFunctions/HTGeometry/MomentFiniteCoordinateValue.lean` supplies the reusable
finite-coordinate bridge

```text
L_s(ofFn(c)) = sum_i c_i s_i,
L_s(ofFn(c)^2) = c^T H_s c.
```

This is what lets an explicit operator Gram source enter the general moment/Feshbach API without
an additional coefficient-convolution argument.

## Coupled Sonin application

For an actual positive aperture `a`, set

```text
v_0 = soninAllPrimeCoupledPowerVector a 0,
v_q = soninAllPrimeCoupledPolynomialPowerVector a q,
D_a(q) = ||v_0||^2 ||v_q||^2 - |<v_0,v_q>|^2.
```

`D_a(q)>=0` is structural.  The new counterterm-free source hypothesis asks only that, for every
zero-constant integer tail and positive error, there is a nondegenerate aperture satisfying

```text
normalizedPrimeArchMoment(0) * D_a(q)
  <= (targetFeshbachRemainder(q)+epsilon)
       * Re(S_a(0))^2.                                      (3)
```

If the target remainder were negative, choose `epsilon` smaller than its magnitude.  The left
side is nonnegative, while nondegeneracy makes the right side strictly negative.  Hence every
target remainder is nonnegative and RH follows.

The actual coupled source has its own real moment sequence

```text
S_a(k) = Re(soninAllPrimeCoupledTraceMoment(a,k)).
```

The finite-coordinate value bridge proves the exact identities

```text
||V_a(p)||^2 = L_{S_a}(p^2),
<V_a(1),V_a(p)> = L_{S_a}(p),
D_a(p) = sourceRobertson_a(p)
       = S_a(0) * sourceFeshbach_a(p).                     (4)
```

After cancelling the positive `S_a(0)`, equation `(3)` is exactly the moment-only comparison

```text
normalizedPrimeArchMoment(0) * sourceFeshbach_a(q)
  <= (targetFeshbachRemainder(q)+epsilon) * S_a(0).        (5)
```

This form contains neither an explicit Hilbert vector, a determinant subtraction, nor a scalar
counterterm.

The normalized pure-state quantum Fisher value removes the remaining source mass:

```text
QFI_a(p) = 4 * sourceFeshbach_a(p) / S_a(0),

normalizedPrimeArchMoment(0) * QFI_a(q)
  <= 4 * (targetFeshbachRemainder(q)+epsilon).             (6)
```

Equations `(5)` and `(6)` are exactly equivalent at every nondegenerate aperture.  Thus the
weakest current source obligation can be expressed as one dimensionless quantum-information
value bound, with no explicit source normalization factor on either side.

Normalizing the moment functional itself gives

```text
E_a[p]   = L_{S_a}(p) / S_a(0),
Var_a(p) = E_a[p^2] - E_a[p]^2,
QFI_a(p) = 4 * Var_a(p).
```

The same source hypothesis is therefore exactly the variance comparison

```text
normalizedPrimeArchMoment(0) * Var_a(q)
  <= normalizedPrimeArchMoment(0) * Var_target(q) + epsilon. (7)
```

Equation `(7)` contains no Feshbach remainder, determinant, source mass, vector, counterterm, or
conventional QFI factor.

The source implementation is
`formal/GaloisForLFunctions/RHTower/SoninCoupledProjectiveQuantumFisher.lean`, with declarations

```text
soninAllPrimeCoupledProjectiveTangentEnergy,
SoninCoupledPrimeArchVacuumProjectiveFisherUpperBound,
riemannHypothesis_of_soninCoupledPrimeArchVacuumProjectiveFisherUpperBound.
```

It also supplies a fully quotient-free Robertson form.  That form implies the Feshbach comparison
after rescaling the positive error by the fixed target vacuum mass.

## Direct corpus impact

- **One hypothesis variable removed:** the RH-facing source statement chooses only an aperture;
  the scalar counterterm is replaced by an invariant value.
- **Missing equivalence discharged:**
  `RHTower/SoninCoupledProjectiveFeshbachEquivalence.lean` proves that the projective-Fisher
  condition, the moment-only source-Feshbach condition `(5)`, and the previous weakest
  aperture-plus-counterterm variance condition are exactly equivalent.  The proof works through
  values and therefore needs no separate coefficient-linearity theorem for the polynomial vector.
- **Source mass eliminated:** the same module proves the dimensionless QFI condition `(6)`
  exactly equivalent to `(5)` and gives it a direct RH consumer.  This removes the final explicit
  occurrence of `S_a(0)` from the analytic inequality.
- **Canonical optimizer exposed:** the scalar minimizing representative is explicitly
  `L_{S_a}(p)/S_a(0)`, and the norm of that centered source vector is exactly
  `sourceFeshbach_a(p)`.
- **General normalized-state API:**
  `HTGeometry/NormalizedMomentQuantumVariance.lean` defines normalized expectation and variance
  for every moment functional, proves `Feshbach = mass * variance` and `QFI = 4 * variance`, and
  identifies the centered representative's normalized square with the variance.  Its size-biased
  state API also applies outside the Sonin route: it rewrites the two live theta-cusp ratio gates
  exactly as a lower and an upper thermal-susceptibility bound, with direct linear-Hankel and
  degree-two-tail/RH consumers in `RHTower/PrimeArchThetaThermalSusceptibility.lean`.
- **Final scalar simplification:** equation `(7)` is source-formalized exactly equivalent to the
  QFI, Feshbach, projective, and old counterterm conditions, with a direct RH capstone.
- **Existing moment-ratio route connected:** normalized expectation of `X^n` is exactly
  `S_a(n)/S_a(0)`, the coordinate already used by
  `SoninCoupledPrimeArchMomentRatioCoupling`.  For a monomial tangent the source QFI is now
  source-formalized as
  `4*(S_a(2n)/S_a(0) - (S_a(n)/S_a(0))^2)`.
- **Gauge independence:** estimates may be made on any scalar-phase representative without
  changing the projective determinant.
- **Target identity sharpened:** the prime--Gamma Feshbach remainder is now exactly a quantum
  Fisher value, not merely analogous to a variance.
- **Existing projective machinery connected by theorem:** for unit vectors,
  `projectiveGramTangentEnergy v g = 1-|<v,g>|^2`.  The new
  `RHTower/RayleighProjectiveQuantumFisher.lean` adapter therefore lets the existing spectral-gap
  and phase-aligned-distance theorems consume the invariant value directly.
- **Existing Robertson machinery connected by theorem:**
  `HTGeometry/ProjectiveQuantumFisherConsumers.lean` rewrites the generator determinant on the
  right of `twoChannelRobertsonGram` as `||f||^2 * projectiveGramTangentEnergy g h`.  No new
  positivity axiom is added.
- **Finite/Krylov consumers connected by theorem:** for every complex moment realization,
  `projectiveGramTangentEnergy (v 0) (v 1) = m_0*m_2-m_1^2`.  The same consumer file specializes
  this identity to the first two vectors of `ThermalKrylovDeterminant.lean`, making the first
  nontrivial thermal Hankel determinant exactly a projective quantum-Fisher value.

No umbrella import was edited because those files are concurrently dirty.  The new modules are
standalone and can be wired into the umbrella only after the shared worktree settles.

## Attack and boundary cases

1. **Zero tangent:** `D_a(0)=0`; the target remainder is also zero, so no false strictness is
   introduced.
2. **Pure scalar tangent:** `v_q=c*v_0` gives `D_a(q)=0`; the projective value correctly deletes
   that direction.
3. **Vanishing vacuum:** normalization would be meaningless.  The RH interface quantifies only
   over `SoninCoupledNondegenerateAperture`, which already gives `Re(S_a(0))>0`.
4. **Circularity check:** target projective/Fisher nonnegativity is not assumed.  Only the source
   Hilbert Gram determinant is nonnegative; the one-sided comparison forces the target sign.
5. **Wrapper check:** equation `(3)` is not a renamed old norm inequality.  Its input no longer
   contains `c`, and its left side is invariant under scalar changes of representative.
6. **Multiparameter nuisance audit:** quantum-estimation theory also profiles a block of nuisance
   parameters by a Fisher-matrix Schur complement.  Applying that extension to the polynomial
   channels `span{1,X}` would require positivity and invertibility of the target first nonconstant
   Hankel block.  The live corpus does not discharge that block unconditionally; adding it would
   trade the removed linear counterterm for a new target hypothesis.  No two-nuisance wrapper was
   promoted.  Revisit only after the first target minor is independently available.
7. **Small-aperture collapse audit:** the corpus has quadratic aperture majorants for each
   weighted residual and for the all-prime residual energy, but it has no theorem producing
   nondegenerate coupled apertures cofinally near zero and no operator-polynomial estimate forcing
   `QFI_a(q) -> 0`.  Therefore equation `(6)` cannot currently be dismissed as a disguised target
   sign test, but neither can small-aperture decay be claimed as a source mechanism.  The exact
   missing audit inputs are a nondegenerate aperture schedule and a normalized polynomial-energy
   bound.
8. **Collapse no-go formalized:** if every fixed test admits nondegenerate apertures with
   `Var_a(q) -> 0`, then equation `(7)` is exactly equivalent to target Feshbach positivity and
   therefore exactly equivalent to RH.  Thus a quantum-metrology spectral-width estimate proving
   only variance collapse would retire the small-aperture route as a sign test; it would not prove
   RH.  The declarations are
   `SoninCoupledPrimeArchNormalizedVarianceCollapseToZero` and
   `soninCoupledPrimeArchNormalizedVarianceUpperBound_iff_riemannHypothesis_of_collapse`.
9. **Quantum-instrument nondegeneracy localized:** `[SOURCE-FORMALIZED, UNVERIFIED]` the all-prime
   direct-sum column is nonzero exactly when one prime-power residual channel is nonzero.  This is
   the Kraus/Stinespring outcome-stacking value relation applied to the live Sonin operator: an
   orthogonal direct sum cannot cancel a nonzero transition amplitude.  The global
   `SoninCoupledNondegenerateAperture` premise is therefore constructible from one local residual
   witness.  This strengthens the source interface but does not yet prove such a witness exists at
   the apertures needed for `(7)`.

The exact specialized equivalence between the previous `exists c` polynomial-vector condition and
the new determinant condition is now source-formalized.  It is obtained by identifying every
polynomial-vector norm with the corresponding coupled moment-functional square value and applying
the general Feshbach minimum there; no `natDegree` coefficient-linearity premise is needed.

## Open core

`[OPEN CORE]` Prove the equivalent normalized-variance inequality `(7)` from the explicit coupled
prime-power and Gamma residual formulas.  Its source value can be computed through either the
normalized moment state or the canonical scalar Schur complement

```text
sourceFeshbach_a(q)
  = L_{S_a}(q^2) - L_{S_a}(q)^2 / S_a(0).
```

The aperture may still depend on `q` and `epsilon`, but no scalar optimization or source-mass
comparison remains.  A useful attack must compare source and target variances using common
prime--Gamma structure.  Bounding the source variance solely by the spectral width of the positive
coupled energy can at most establish collapse to zero; the formal no-go above shows that this does
not supply the missing arithmetic comparison.

## Literature provenance

1. J. P. Provost and G. Vallee, *Riemannian structure on manifolds of quantum states*,
   Communications in Mathematical Physics 76 (1980), 289--301,
   DOI [10.1007/BF02193559](https://doi.org/10.1007/BF02193559).
2. J. Anandan and Y. Aharonov, *Geometry of quantum evolution*, Physical Review Letters 65
   (1990), 1697--1700,
   DOI [10.1103/PhysRevLett.65.1697](https://doi.org/10.1103/PhysRevLett.65.1697).
3. S. L. Braunstein and C. M. Caves, *Statistical distance and the geometry of quantum states*,
   Physical Review Letters 72 (1994), 3439--3443,
   DOI [10.1103/PhysRevLett.72.3439](https://doi.org/10.1103/PhysRevLett.72.3439).
4. J. Zhang and J. Suzuki, *Hybrid Cramér--Rao bound for quantum Bayes-point estimation with
   nuisance parameters*, arXiv:2510.16810 (2025),
   [arXiv:2510.16810](https://arxiv.org/abs/2510.16810).  This source motivates the audited
   multiparameter Schur extension; that extension was not promoted for the corpus reason above.
5. D. Petz, *Monotone metrics on matrix spaces*, Linear Algebra and its Applications 244 (1996),
   81--96,
   DOI [10.1016/0024-3795(94)00211-8](https://doi.org/10.1016/0024-3795(94)00211-8), and
   C. Ferrie, *Data-processing inequalities for quantum metrology*, Physical Review A 90 (2014),
   014101,
   DOI [10.1103/PhysRevA.90.014101](https://doi.org/10.1103/PhysRevA.90.014101).  Their
   channel-contraction principle was audited but does not directly apply to the current
   principal-subtracted boundary-residual source, which is not exposed as a state-independent
   trace-preserving quantum channel.
6. S. Pang and T. A. Brun, *Quantum metrology for a general Hamiltonian parameter*, Physical
   Review A 90 (2014), 022117,
   DOI [10.1103/PhysRevA.90.022117](https://doi.org/10.1103/PhysRevA.90.022117).  Generator
   spectral-width bounds were audited as a possible source-variance estimate.  In the present
   route they would be useful primarily to prove the collapse premise of the formal no-go, not the
   target comparison itself.
7. K. Kraus, *General state changes in quantum theory*, Annals of Physics 64 (1971), 311--335,
   DOI [10.1016/0003-4916(71)90108-4](https://doi.org/10.1016/0003-4916(71)90108-4), and
   W. F. Stinespring, *Positive functions on C*-algebras*, Proceedings of the American
   Mathematical Society 6 (1955), 211--216,
   DOI [10.1090/S0002-9939-1955-0069403-4](https://doi.org/10.1090/S0002-9939-1955-0069403-4).
   Their operation/dilation formalism supplies the direct-sum channel interpretation used only
   for the exact local-to-global nondegeneracy bridge; no CPTP monotonicity assumption is made.

The projective metric and quantum Fisher normalization are known physics.  The contribution here
is a `[BRIDGE]`: their exact value identity is applied to remove a concrete variable from the live
coupled-Sonin RH source interface.

## Verification status

Source inspection only.  Under the active user constraint, no Lean invocation, scratch
compilation, lint, axiom inspection, numerical check, targeted build, or full build was run.  The
new declarations remain stage 1 until a narrow validation pass is authorized.

## Log

- 2026-07-15 -- primary quantum-geometry provenance checked; general HTGeometry value identity,
  moment-Feshbach bridge, coupled Sonin counterterm-free source value, and RH consumers written
  source-only.  No computation or build run.
- 2026-07-15 -- finite-coordinate moment bridge and exact coupled source
  `projective = Robertson = mass * Feshbach` identity added source-only.  This proves equivalence
  with the previous weakest aperture-plus-counterterm condition and reduces the open comparison
  to the moment-only equation `(5)`.  Quantum-channel monotonicity was audited but not imported:
  the principal-subtracted Sonin boundary residual is not presented as a state-independent CPTP
  channel.  No computation or build run.
- 2026-07-15 -- source mass cancelled from the normalized pure-state QFI.  The new dimensionless
  condition `(6)` is source-formalized as exactly equivalent to the moment-Feshbach and old
  counterterm interfaces, with a direct RH capstone.  A static small-aperture audit found no
  cofinal nondegenerate schedule or normalized polynomial-energy decay theorem; no collapse or
  circularity claim was promoted.  No computation or build run.
- 2026-07-15 -- normalized moment expectation and variance added as general HTGeometry values;
  the coupled source condition reduced to equation `(7)`.  The conditional small-variance route
  was then closed formally: source variance collapse makes `(7)` equivalent to RH rather than a
  proof mechanism.  Quantum spectral-width bounds remain relevant only to discharging that no-go
  premise unless an independent prime--Gamma variance comparison is found.  No computation or
  build run.
