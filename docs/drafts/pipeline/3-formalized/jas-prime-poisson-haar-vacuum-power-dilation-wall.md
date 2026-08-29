# JAS prime-Poisson Haar-vacuum power-dilation wall

Status: FORMALIZED IN LEAN 4
Route: JAS
Date: 2026-08-29

## Result

For `0 < sigma`, literal prime-Poisson multiplication `L²` contains a normalized vector whose
complete finite-support mixed Laurent vacuum coefficients equal product-Haar coefficients if and
only if

`1 / 2 < sigma`.

Equivalently, exact Haar bilateral vacuum power law for commuting flat Boolean prime creators is
available in literal source representation only in open right half-plane, never at critical wall.

Formal endpoint:

`primePoisson_hasExactHaarVacuumPowerLaw_iff`

in

`GaloisForLFunctions.RHTower.JointAncestryPrimePoissonHaarVacuumPowerDilationWall`.

Labels: `[PROVED IN LEAN] [CORPUS-NOVEL ROUTE THEOREM] [TARGETED EXTERNAL NO-MATCH] [GLOBAL NOVELTY UNVERIFIED]`.

## Corpus origin

Conjecture was frozen only after required corpus searches:

- `scripts/formal_tools.py research "Lp vector state measure withDensity norm square inner multiplication integral character"`
- `scripts/formal_tools.py research "ProbabilityMeasure withDensity Lp norm square Radon Nikodym vector state probability"`
- `scripts/formal_tools.py research "withDensity_apply univ lintegral norm Lp probability measure constructor"`
- `scripts/formal_tools.py research "probabilityMeasure_ext_of_infiniteTorusFourier_integral_eq"`
- `scripts/formal_tools.py research "primePoissonMeasure_mutuallySingular_torusHaar_of_le_half primePoissonMeasure_mutuallyAbsolutelyContinuous_torusHaar_iff"`
- `scripts/formal_tools.py research "eLpNorm two lintegral enorm sq norm one"`
- `scripts/formal_tools.py research "JASGammaBooleanL2 boolean basis vacuum creator insertion occupied nilpotent"`
- `scripts/formal_tools.py research "infiniteTorusFourier torusCharacter equality"`

Decisive corpus inputs were infinite-torus Fourier uniqueness, sharp prime-Poisson/Haar Kakutani
wall, repaired Radon--Nikodym half-density unitary, continuous multiplication calculus, and actual
JAS Boolean creator laws.  Search found no existing vector-state classification or exact critical
Boolean-dilation obstruction.

## Proof

For `v : L²(mu)`, define vector-state measure

`rho_v = mu.withDensity (x |-> ‖v(x)‖²)`.

Lean proves:

1. `‖v‖ = 1` makes `rho_v` a probability measure.
2. `rho_v ≪ mu`.
3. Integration against `rho_v` equals multiplication-operator matrix coefficient
   `inner v (M_f v)`.
4. If all finite Laurent coefficients equal Haar coefficients, infinite-torus Fourier uniqueness
   forces `rho_v = torusHaar` and hence `torusHaar ≪ mu`.
5. For `sigma ≤ 1 / 2`, prime-Poisson is singular to Haar, contradiction.
6. For `1 / 2 < sigma`, repaired Radon--Nikodym half-density unitary transports constant Haar
   vacuum into prime-Poisson `L²`, preserving every multiplication coefficient.

This proves both directions and exposes exact operator-language power law, not only measure-class
sewing.

## Formal declarations

Generic infrastructure:

- `l2VectorStateDensity`
- `l2VectorStateMeasure`
- `l2VectorStateMeasure_absolutelyContinuous`
- `l2VectorStateMeasure_univ`
- `isProbabilityMeasure_l2VectorStateMeasure`
- `l2VectorStateProbabilityMeasure`
- `integral_l2VectorStateMeasure_eq_inner`
- `torusHaar_absolutelyContinuous_of_hasHaarVacuumVector`
- `not_hasHaarVacuumVector_of_mutuallySingular`
- `torusHaarVacuum`
- `norm_torusHaarVacuum`
- `inner_torusHaarVacuum_continuousL2Mul`
- `hasHaarVacuumVector_of_withDensity_eq`
- `hasHaarVacuumVector_of_mutuallyAbsolutelyContinuous_torusHaar`

Route theorems:

- `not_hasHaarVacuumVector_primePoisson_of_le_half`
- `primePoisson_hasHaarVacuumVector_iff`
- `integral_infiniteTorusFourier_torusHaar_eq_ite`
- `hasExactHaarVacuumPowerLaw_iff_hasHaarVacuumVector`
- `primePoisson_hasExactHaarVacuumPowerLaw_iff`

## Consequence and positive survivor

Killed implementation:

`critical prime-Poisson source -> exact unweighted Haar bilateral power dilation -> flat Boolean creator compression`.

Reason: exact power dilation forces full mixed Laurent Haar vacuum law, while theorem proves no
such source vector exists at wall.

Strongest positive survivor: open-right-half source carries explicit transported Haar vacuum, and
critical JAS must retain prime-Poisson measure class or replace exact power dilation by genuinely
non-Haar orientation.  Countable multiplicity alone cannot change vector-state domination; any
future amplified model must alter spectral measure class, not merely add channels.

## Full RH chain

This theorem is early route gate, not RH proof:

1. prime-Poisson-measure-class oriented bilateral completion surviving this wall;
2. compression to literal Gamma-theta creator, including Boolean nilpotence and actual theta grade;
3. prime-support- and grade-synchronized source coefficients;
4. divisor-independent `XiPrimePoissonReflectionSewing rho`;
5. `xiPrimePoissonReflectionSewing_iff_internalOnly`;
6. `xiDivisorSyndromeIsInternalOnly_iff_re_eq_half`;
7. critical-line theorem for every nontrivial zeta zero;
8. RH.

New burden is narrower: do not pursue unweighted Haar vacuum transport at wall.  Construct
orientation inside prime-Poisson measure class and prove actual Gamma-theta compression, or retire
exact power-dilation JAS.

## Literature audit

Targeted primary-source searches covered commuting/q-commuting Fock dilations, vector spectral
measures, infinite-product Poisson/Haar equivalence, and arithmetic scaling representations.
Closest sources found:

- Bhat--Bhattacharyya--Dey, *Standard noncommuting and commuting dilations of commuting tuples*,
  https://arxiv.org/abs/math/0204107
- Dey, *Standard dilations of q-commuting tuples*, https://arxiv.org/abs/math/0310389
- Connes--Consani, *The Scaling Hamiltonian*, https://arxiv.org/abs/1910.14368

These cover standard tuple/Fock dilation or arithmetic multiplication representations, not sharp
prime-Poisson critical threshold for Haar-vacuum vector states, and not JAS Boolean creator
consequence.  No exact match found.  Global novelty remains unverified; standard vector-state and
Fourier-determinacy ingredients are not claimed novel.

## Audit

- Direct check passed:
  `lake env lean GaloisForLFunctions/RHTower/JointAncestryPrimePoissonHaarVacuumPowerDilationWall.lean`
- Exact leaf build passed:
  `lake build GaloisForLFunctions.RHTower.JointAncestryPrimePoissonHaarVacuumPowerDilationWall`
  with `Build completed successfully (12130 jobs)`.
- `#print axioms` for fourteen core and route declarations reports only
  `propext`, `Classical.choice`, `Quot.sound`.
- Formal lint reports no forbidden declaration in new module.  Repository-wide pre-existing large
  file warnings and unrelated umbrella-reachability errors remain.
- Module imported by `formal/GaloisForLFunctions/RHTower.lean`.
- Frontier map was not edited.
