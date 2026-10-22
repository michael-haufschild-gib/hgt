# SZ: actual physical two-prime phase law

- **ID:** SZ-PHYSICAL-TWO-PRIME-LAW
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** SZ canonical-head joint phase credit; SteinhausDirichletLogCost;
  SuzukiGroundEnergyContinuity; actual Fourier Plancherel carrier.

## Exact attempted transfer

An independent-prime Dirichlet square density is not automatically the
physical spectral measure of the actual Weil ground. Test the strongest
proposed identification already on the literal primes 2 and 3.

For physical f, let d nu_f(t) = |Fourier(f)(t)|^2 dt and
P(t) = (fract(-t log 2), fract(-t log 3)). Let rho_f = P_*nu_f.
The independent phase reference is the product of uniform measures on [0,1].

## Dependency-closed paper argument

Write alpha=log 2, beta=log 3. The measurable countable union

    S = union_(m,n in Z) { (x,y) : beta*x-alpha*y=alpha*n-beta*m }

contains every P(t), by the floor/fractional-part identity. Each vertical
section of each line is a singleton, since alpha>0. Tonelli and countable
subadditivity show that S has zero independent phase measure. Therefore
rho_f is singular with respect to that reference. Plancherel gives
rho_f(S)=rho_f(univ)=norm(f)^2. For the actual normalized ground this is 1,
so rho_f cannot have any density relative to independent phases.

The singularity argument does not require irrationality, a numerical
approximation, RH, a spectral gap, or an unproved ground property.

## Positive survivor and limit of the obstruction

The stronger survivor uses the corpus theorem that log(3)/log(2) is
irrational. Equal fractional phase pairs force the frequency difference
times both logarithms to be integers; irrationality forces that difference
to be zero. Thus P is a Borel injection and has a measurable inverse on
its range. Extend that inverse by zero off the range. For every
nonnegative spectral cost W, its integral against nu_f is exactly the
integral of W composed with this inverse against rho_f. The full shifted
Gamma weight is one such cost. The map on measures is injective: the
joint phase law retains the complete spectral measure, not just selected
prime moments. No Dirichlet degree cost is identified with Gamma energy.

Finite-correlation approximation is not ruled out by singularity. No sign
for the canonical-head Gamma--prime--polar gap follows. This closes only
the attempted exact independent-density transfer, not route SZ.

## Research/audit log

- 2026-10-03: corpus searches1215652 and1215688 inspected. Both partial;
  compiler/source coverage does not certify absence or novelty. Existing
  scalar-symbol pushforward absolute continuity does not imply absolute
  continuity of this two-coordinate law.
- Final leaf audit25304: exit0, no diagnostics. Command:
  `lake --old env lean GaloisForLFunctions/RHTower/CCM/CCMPhysicalTwoPrimePhaseLaw.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCM/CCMPhysicalTwoPrimePhaseLaw.olean`.
- Axiom audit6552: all19 public declarations checked from a /tmp import;
  only `propext`, `Classical.choice`, `Quot.sound`. No added axioms, proof
  placeholders, heartbeat changes, numerical experiments, or umbrella build.
- One RHTower umbrella import. Formal lint7116 exited1 on13 unrelated
  reachability errors; this leaf is not among them. Exact list retained in
  the main SZ working log. Targeted whitespace check passed.

## Exact Lean declarations

Leaf: `formal/GaloisForLFunctions/RHTower/CCM/CCMPhysicalTwoPrimePhaseLaw.lean`.

- `ccmTwoPrimePhysicalPhaseSupport_null`: independent phase mass zero.
- `ccmPhysicalTwoPrimePhaseLaw_support_mass`: physical mass on that set.
- `ccmPhysicalTwoPrimePhaseLaw_mutuallySingular`: singularity for every source.
- `ccmNormalizedGroundTwoPrimePhaseLaw_not_absolutelyContinuous` and
  `ccmNormalizedGroundTwoPrimePhaseLaw_ne_withDensity`: unconditional actual
  ground specialization, with aperture as the only source parameter.
- `ccmTwoPrimePhysicalPhase_measurableEmbedding` and
  `ccmTwoPrimePhysicalPhase_map_injective`: complete spectral faithfulness.
- `ccmTwoPrimePhysicalFrequency_phase`: exact measurable frequency recovery.
- `ccmPhysicalTwoPrimePhaseLaw_recover_spectral_cost` and
  `ccmPhysicalTwoPrimePhaseLaw_recover_Gamma_cost`: complete cost recovery.

These theorems close the stated transfer question, not the hard joint
Gamma--prime--polar sign. RH and its falsification remain unresolved.
