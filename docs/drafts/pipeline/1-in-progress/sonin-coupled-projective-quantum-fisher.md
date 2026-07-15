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

The exact specialized equivalence between the previous `exists c` polynomial-vector condition and
the new determinant condition still requires a source lemma making coefficient-linearity of
`soninAllPrimeCoupledPolynomialPowerVector` explicit across the `natDegree` representation.  The
general value-level minimization is proved; the RH capstone does not depend on that equivalence.

## Open core

`[OPEN CORE]` Prove `(3)` from the explicit coupled prime-power and Gamma residual formulas.  In
expanded source coordinates the required object is only the `2 x 2` determinant

```text
Re(S_a(0)) * ||V_a(q)||^2 - |<V_a(1),V_a(q)>|^2.
```

The aperture may still depend on `q` and `epsilon`, but no scalar optimization remains.  A useful
next attack is to express both mixed entries by the existing real coupled trace moments and seek a
direct determinant comparison, rather than estimate `||V_a(q-c)||` for a chosen `c`.

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
