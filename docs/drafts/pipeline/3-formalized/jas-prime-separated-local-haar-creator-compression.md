# JAS prime-separated local-Haar creator compression

Status: FORMALIZED IN LEAN 4
Route: JAS
Date: 2026-08-29
Lean module: `GaloisForLFunctions.RHTower.JointAncestryPrimeSeparatedLocalHaarCreatorCompression`

## Result

Fix `0 < sigma`, height `t`, and the literal prime-Poisson product measure `mu`.  For every prime
`p`, replace only its circle-Poisson parameter by zero, obtaining a product measure `nu_p` with a
Haar `p`-coordinate and unchanged remaining coordinates.  The formalization proves:

1. `mu` and `nu_p` are mutually absolutely continuous for every `sigma > 0`, including
   `sigma = 1/2`;
2. a selected unit vector `v_p : L²(mu)` has vector-state measure exactly `nu_p` for every
   continuous multiplier;
3. the full Laurent orbit `M_(z_p^q) v_p`, `q : Z`, is orthonormal;
4. the two-frame `(v_p, M_(z_p) v_p)` compresses `M_(z_p)` to the Boolean creator
   `|1><0|` and `M_(z_p^-1)` to the adjoint annihilator `|0><1|`;
5. placing the `p`-frame in grade `natEquivPrimes.symm p` gives one orthonormal family indexed by
   `Nat.Primes × Fin 2`;
6. this family has an explicit isometric `ell²` synthesis;
7. globally, positive and negative coordinate multipliers have exactly those same-prime Boolean
   blocks, while every cross-prime matrix coefficient is zero.

This realizes simultaneous oriented prime creators inside the literal prime-Poisson measure class
without requiring a global Haar vacuum, which is impossible at and left of the critical wall.

## Corpus origin

Conjecture JAS-PSLHC was frozen before proof from mandatory corpus searches:

- `scripts/formal_tools.py research "JAS reflected source-linearity prime Poisson measure class non-diagonal source cancellation Gamma theta XiPrimePoissonReflectionSewing"`
- `scripts/formal_tools.py research "jointAncestryActualThetaClosedGrade synthesis coordinate prime support synchronized source coefficient"`
- `scripts/formal_tools.py research "JAS Gamma insertion unitary dilation compression corner bilateral shift support cut"`
- `scripts/formal_tools.py research "prime Poisson two dimensional compression multiplication nilpotent creator"`
- `scripts/formal_tools.py research "circlePoissonHalfLikelihood inverse haar vector L2 multiplication Fourier moment"`
- `scripts/formal_tools.py research "one coordinate circlePoisson product measure half likelihood withDensity target"`
- `scripts/formal_tools.py research "l2Single l2Amplification orthonormal grade separated packet inner_single_left"`
- `scripts/formal_tools.py research "def IndexedEllTwo ellTwoCoordinateBasis"`

Corpus constraints determined the construction:

- `not_JASPrimeSupportCoordinateRaisingRepresentation` excludes a direct invertible-coordinate to
  support-cutting Gamma identification;
- partial-landing and toggle-dense-range no-gos exclude direct and unoriented creator landings;
- `not_JASCriticalPrimeThetaFixedGradeSingletonSynthesis` excludes one fixed grade;
- `jointAncestryCriticalPrimeInjectiveGradeSynthesis_exists` identifies collision-free grading as
  the positive Bessel boundary;
- `torusPoissonMeasure_mutuallyAbsolutelyContinuous_iff_summable_normSq` permits a one-coordinate
  parameter replacement even at the global singularity wall;
- `weightedDensityUnitary_continuousL2Mul` transports every multiplier coefficient;
- `primePoisson_hasHilbertHaarVacuumPowerLaw_iff` rules out replacing all coordinates at the
  critical wall and forces the local, grade-separated design.

No prior corpus theorem supplied the oriented local compression or simultaneous prime-separated
synthesis.

## Proof

The source and locally Haarized parameter sequences differ on the singleton `{p}`, so their squared
displacement is summable.  Product-measure Kakutani equivalence gives mutual absolute continuity.
The repaired Radon-Nikodym density yields a multiplication-intertwining unitary from `L²(nu_p)` to
`L²(mu)`; transporting the constant target vacuum produces `v_p` and transfers all continuous
multiplier moments.

Under `nu_p`, the `p` coordinate is Haar, hence its Laurent moment is `1` at exponent zero and `0`
otherwise.  The adjoint formula for multiplication converts this moment identity into orthogonality
of the full Laurent orbit and both two-frame compression laws.  Distinct primes occupy distinct
amplification grades, so their matrix coefficients vanish.  Orthonormal-family synthesis then
gives the bounded source map.

Main declarations:

- `primePoissonMeasure_mutuallyAbsolutelyContinuous_localHaar`
- `exists_unitVector_inner_continuousL2Mul_eq_integral_of_mutuallyAbsolutelyContinuous`
- `exists_jasPrimePoissonLocalHaarVacuum`
- `inner_jasPrimePoissonLocalHaarPowerVector`
- `orthonormal_jasPrimePoissonLocalHaarBooleanVector`
- `jasPrimePoissonLocalHaar_positiveCompression`
- `jasPrimePoissonLocalHaar_negativeCompression`
- `orthonormal_jasPrimeSeparatedLocalHaarBooleanPacket`
- `jasPrimeSeparatedLocalHaarBooleanSynthesis`
- `jasPrimeSeparatedLocalHaarBooleanSynthesis_coordinateBasis`
- `jasPrimeSeparatedLocalHaar_positiveCompression`
- `jasPrimeSeparatedLocalHaar_negativeCompression`

## RH proof chain

1. This theorem supplies a literal prime-Poisson-measure-class, orientation-sensitive compressed
   Boolean source for every prime, with collision-free grade slots and bounded synthesis.
2. Conjugate each creator by the formalized Gamma-theta support gauge and pass through
   `jasActualThetaClosedGradeSynthesisRelation`, inserting literal Gamma gains and actual completed
   theta grade norms.
3. Assemble those corners into a coefficient-faithful, prime-support-synchronized RFHM source
   relation.
4. Derive divisor-independent `XiPrimePoissonReflectionSewing rho`.
5. Apply `xiPrimePoissonReflectionSewing_iff_internalOnly`.
6. Apply `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`.
7. Conclude every nontrivial zeta zero lies on the critical line, hence RH.

Step 1 is now closed.  Exact remaining JAS core is steps 2--3: compatibility of these compressed
source corners with the Gamma-theta gauge and coefficient-faithful synchronized assembly.  This
module does not claim RH.

## Novelty audit

Label:
`[PROVED IN LEAN] [CORPUS-NOVEL ROUTE THEOREM] [TARGETED EXTERNAL NO-MATCH] [GLOBAL NOVELTY UNVERIFIED]`.

Targeted searches covered Kakutani product equivalence, Radon-Nikodym multiplication intertwiners,
unit-circle shift compressions, prime spectral/Hilbert-space RH programs, and semi-local operator
approaches.  Closest sources were:

- Lie--Sullivan, *Quasi-invariance of countable products of Cauchy measures under non-unitary
  dilations*, <https://arxiv.org/abs/1611.10289>, for Kakutani-style product equivalence;
- Hoareau--Le Maitre, *Spatial models for boolean actions in the infinite measure-preserving
  setup*, <https://arxiv.org/abs/2406.02401>, for measure-class `L²` multiplication intertwiners;
- Xue, *On a Hilbert Space Reformulation of Riemann Hypothesis*,
  <https://arxiv.org/abs/1911.04029>, for an unrelated operator-invariance RH criterion;
- Connes--Consani, *The Scaling Hamiltonian*, <https://arxiv.org/abs/1910.14368>, for an unrelated
  semi-local operator framework tied to RH.

Local Radon-Nikodym transport and finite compression ingredients are standard.  No targeted source
matched the exact arithmetic theorem: simultaneous all-prime, locally Haarized creator/annihilator
compression inside the singular critical prime-Poisson measure class with collision-free synthesis
and the stated JAS sewing role.  Exhaustive global novelty is not certified.

## Lean audit

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/JointAncestryPrimeSeparatedLocalHaarCreatorCompression.lean`.
- Exact leaf build passed:
  `lake build GaloisForLFunctions.RHTower.JointAncestryPrimeSeparatedLocalHaarCreatorCompression`
  (`12133/12133`, build completed successfully).
- Printed axioms for eight core/capstone theorems: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Formal lint found no forbidden declaration or reachability failure for this module.  Reported
  unrelated pre-existing umbrella reachability errors and large-file warnings elsewhere.
- Module is imported by `GaloisForLFunctions.RHTower`.

