# JAS Hilbert-multiplicity Haar-vacuum superselection

Status: FORMALIZED IN LEAN 4
Route: JAS
Date: 2026-08-29

## Result

Let `H` be any complex Hilbert space containing a unit vector, let `0 < sigma`, and let finite
mixed torus characters act by pointwise scalar multiplication on

`L²(primePoissonMeasure sigma t hsigma; H)`.

There is a unit vector whose complete mixed Laurent matrix coefficients equal the product-Haar
coefficients if and only if

`1 / 2 < sigma`.

The negative direction is uniform in `H`.  Thus finite, countably infinite, nonseparable, and
continuous diagonal Hilbert multiplicity cannot evade the critical prime-Poisson/Haar
superselection wall.  Adding diagonal source channels is retired as a JAS repair.

Labels:

- `[PROVED IN LEAN]`
- `[CORPUS-NOVEL ROUTE THEOREM]`
- `[TARGETED EXTERNAL NO-MATCH]`
- `[GLOBAL NOVELTY UNVERIFIED]`

## Corpus origin

Conjecture was frozen only after these required corpus searches:

- `scripts/formal_tools.py research "L2Amplification inner coordinate sum norm square diagonal multiplication operator matrix coefficient"`
- `scripts/formal_tools.py research "lp fun inner tsum coordinatewise operator inner l2 amplification"`
- `scripts/formal_tools.py research "JAS exact oriented bilateral completion prime Poisson measure class Gamma theta creator open core"`
- `scripts/formal_tools.py research "Hilbert valued Lp scalar multiplication continuous multiplier L2 vector field"`
- `scripts/formal_tools.py research "Lp complex scalar function smul fixed unit vector isometry inner"`

Decisive corpus inputs were `lpBoundedSmulCLM`, `lp_norm_sq_eq_integral_vector`, the corpus's
`l2Amplification` disjointness machinery, and the scalar threshold theorem in
`JointAncestryPrimePoissonHaarVacuumPowerDilationWall`.  Corpus had no theorem treating complete
Haar vacuum moments in `L²(mu; H)` uniformly over arbitrary Hilbert multiplicity.

## Lean theorem

Module:

`GaloisForLFunctions.RHTower.JointAncestryHilbertMultiplicityHaarVacuumSuperselection`

Main declarations:

- `hilbertL2VectorStateDensity`
- `hilbertL2VectorStateMeasure`
- `hilbertL2VectorStateMeasure_univ`
- `continuousHilbertL2Smul`
- `integral_hilbertL2VectorStateMeasure_eq_inner`
- `scalarToUnitVectorIsometry`
- `lpUnitVectorEmbedding`
- `lpUnitVectorEmbedding_continuousL2Mul`
- `HasHilbertHaarVacuumPowerLaw`
- `torusHaar_absolutelyContinuous_of_hasHilbertHaarVacuumPowerLaw`
- `not_hasHilbertHaarVacuumPowerLaw_of_mutuallySingular`
- `not_hasHilbertHaarVacuumPowerLaw_primePoisson_of_le_half`
- `hasHilbertHaarVacuumPowerLaw_of_hasExactHaarVacuumPowerLaw`
- `primePoisson_hasHilbertHaarVacuumPowerLaw_iff`

The capstone is unconditional and closed:

```lean
theorem primePoisson_hasHilbertHaarVacuumPowerLaw_iff
    (e : H) (he : ‖e‖ = 1) (sigma t : ℝ) (hsigma : 0 < sigma) :
    HasHilbertHaarVacuumPowerLaw H (primePoissonMeasure sigma t hsigma) ↔
      1 / 2 < sigma
```

## Proof

For Hilbert-valued `v`, define the scalar vector-state measure

`rho_v = mu.withDensity (x |-> ‖v(x)‖²)`.

Lean proves:

1. `‖v‖ = 1` makes `rho_v` a probability measure;
2. `rho_v ≪ mu` for every `v`;
3. `integral f d rho_v = inner v (M_f v)` for every continuous scalar multiplier;
4. complete mixed Laurent coefficients determine probability measures on the infinite torus;
5. hence a Hilbert-valued Haar vacuum forces `rho_v = torusHaar` and therefore
   `torusHaar ≪ mu`;
6. prime-Poisson is mutually singular with product Haar when `sigma ≤ 1 / 2`, contradiction;
7. when `1 / 2 < sigma`, the scalar repaired Haar vacuum embeds isometrically as `f |-> f • e`
   for any unit vector `e : H`, preserving every multiplier matrix coefficient.

No coordinate basis, separability, dimension bound, or sum over multiplicity is used.

## Positive survivor and route consequence

Multiplicity failure exposes a sharper survivor: a JAS source completion reaching the critical
line must retain the prime-Poisson measure class and change orientation, mix source fibres
non-diagonally, or produce reflected cancellation directly from the Gamma-theta source.  Neither
more copies nor continuous diagonal multiplicity can supply exact unweighted Haar bilateral
powers.

This does not prove RH.  It closes one genuine proof-design ambiguity before the remaining producer
problem.

## Full RH chain

1. construct a prime-Poisson-measure-class oriented bilateral completion surviving the arbitrary
   multiplicity wall;
2. compress it to the literal Gamma-theta creator with Boolean nilpotence and actual theta grade;
3. derive prime-support- and grade-synchronized source coefficients;
4. obtain divisor-independent `XiPrimePoissonReflectionSewing rho`;
5. apply `xiPrimePoissonReflectionSewing_iff_internalOnly`;
6. apply `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`;
7. conclude every nontrivial zeta zero has real part `1 / 2`;
8. conclude RH.

## External literature audit

Targeted primary-source searches covered Hilbert-valued multiplication representations, direct
integrals, vector states, and vector/operator Radon-Nikodym theorems.

- Boiko--Dubovoy--Kheifets, *On special cases of Radon--Nikodym theorem for vector and operator
  valued measures*: https://arxiv.org/abs/1303.0098
- Mikusinski--Ward, *A characterization of the Radon-Nikodym property for vector valued measures*:
  https://arxiv.org/abs/1701.04837
- Raginsky, *Radon-Nikodym derivatives of quantum operations*:
  https://arxiv.org/abs/math-ph/0303056
- Hoareau--Le Maître, *Spatial models for boolean actions in the infinite measure-preserving
  setup*: https://arxiv.org/abs/2406.02401

These sources support general Radon-Nikodym or multiplication-representation background.  No
targeted source states the arbitrary-Hilbert-multiplicity prime-Poisson/product-Haar threshold, its
critical value, or the JAS no-go.  General vector-state measure theory is not claimed as novel.

## Audit

- Direct check:
  `lake env lean GaloisForLFunctions/RHTower/JointAncestryHilbertMultiplicityHaarVacuumSuperselection.lean`
  passed without warnings.
- Exact leaf audit:
  `lake build GaloisForLFunctions.RHTower.JointAncestryHilbertMultiplicityHaarVacuumSuperselection`
  passed: `Built ... (14s)` and `Build completed successfully (12132 jobs)`.
- `#print axioms` on ten structural and capstone declarations reports only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Formal lint introduced no forbidden declaration and reports no reachability problem for this
  module.  Repository lint remains nonzero because of pre-existing unrelated umbrella
  reachability errors and large-file warnings.
- Module is wired into `GaloisForLFunctions.RHTower`.
- No computation was used in theorem discovery or proof.

