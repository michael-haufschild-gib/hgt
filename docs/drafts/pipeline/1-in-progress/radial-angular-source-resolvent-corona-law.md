# Finite-observation / asymptotic-completion separation law

- **ID:** RASRC-1
- **Stage:** 1-in-progress
- **Type:** THEOREM / SYNTHESIS
- **Source:** `RadialAngularRecurrenceCompletionLaw`, `QuantumRecurrenceCoronaLaw`,
  `CCMUnitaryPolarSourceAtlas`, and the whole RHTower/HTGeometry audit

## Exact claim

`[PAPER-PROVED] [CORPUS] [NOVELTY UNVERIFIED] [NOT RH]`

Let `I` be any coordinate set, `A` any alphabet, and `~` any equivalence relation on records
`I -> A` which identifies records differing on only finitely many coordinates.  For every finite
set `S` of observed coordinates, every set `Y`, and every map

```text
F : ((I -> A) / ~) -> Y,
```

if `F` can be computed from the coordinates in `S` of a representative record, then `F` is
constant.  In symbols, the implication

```text
(forall u v, u|S=v|S -> F([u])=F([v]))
  -> Function.Constant F                                      (A)
```

holds without topology, linearity, positivity, or boundedness assumptions.  Thus no nonconstant
asymptotic spectral invariant is a finite-horizon observable.

Every finite cylinder therefore surjects onto the whole quotient.  Sequential recurrence modulo
late-time-vanishing differences is one instance, not the definition of the law.

Equip `A` with any topology and the record space with its product topology.  Every quotient fibre
is dense, because it contains all finite modifications of each representative.  The coinduced
quotient topology is therefore indiscrete.  More sharply, if `Y` is `T1`, any reporter whose
pullback to record space is continuous at even one point is constant.  This is the topological
form of `(A)` and requires no countability, metrizability, algebra, or probability.

Two corpus constructions are literal additional instances.  The Hadamard coefficient-tail
algebra identifies finite-support changes, so every finite prime/coefficient prescription occurs
in every reduced-product class.  The Sonin singular-grade relation identifies sections modulo
`o(epsilon)`; every finite depth modification is exactly zero eventually and hence preserves the
grade.  In both cases every finite-coordinate reporter on the completed quotient is constant.

This exact categorical separation has a robust physical form.  In every finite diagonal quantum
system, every finite normalized Heisenberg record and every positive tolerance admit both:

1. an arbitrarily close strict-contraction completion for which every complete Heisenberg history
   vanishes;
2. an arbitrarily close unitary completion of every admissible positive projective temporal rank.

Spectral completion has two independent coordinates which no finite observation horizon can
identify:

1. **radial survival:** from every finite diagonal unitary record, arbitrarily close strict
   contractions reproduce every normalized Heisenberg observable on the prescribed finite horizon
   but make every complete Heisenberg history tend to zero;
2. **angular recurrence:** arbitrarily close unitary completions reproduce the same finite record
   while realizing every admissible positive projective temporal rank.

At complete time, the quotient of a finite-contraction return history by all vanishing histories is
exactly its peripheral spectral carrier and vanishes exactly when peripheral mass vanishes.  Thus
radial survival is selected before angular recurrence dimension; neither is a finite-horizon
observable.

The Riemann first-clock atlas is an arithmetic infinite-divisor realization of this separation.
Finite-aperture creases recover the source births.  Strictly off-critical characters have nonzero
radial exponent and are recovered as poles of fixed-width source continuation.  After subtracting
their reflected polar sector, critical characters have unit modulus and form the unique Bohr
recurrence asymptote, whose coefficients recover multiplicity.  Therefore

```text
birth/current  -> source atoms,
radial/growth  -> off-critical divisor,
angular/corona -> critical divisor.
```

The three readouts are jointly complete, but they are not three strata of the universal theorem.
Creases are the finite-aperture source readout; poles and Bohr frequencies are two necessarily
non-finite boundary readouts of the completed divisor.  Law `(A)` proves that no nonconstant
divisor invariant descending to the recurrence corona can be replaced by any exact finite-time
reporter.  The physical future-fan strengthens this from an abstract splice obstruction to
arbitrarily close genuine finite-dimensional evolutions.

## Dependency-closed proof

### Universal finite-observation separation

Fix a finite coordinate set `S` and two arbitrary quotient classes `q_1,q_2`.  Choose a record
`u` representing `q_1`.  Splice the coordinates `u|S` to any representative of `q_2`.  The
spliced record `w` agrees with `u` on `S` and differs from the chosen representative only on `S`,
hence represents `q_2`.  If `F` is determined by `S`, then

```text
F(q_1)=F([u])=F([w])=F(q_2).
```

As `q_1,q_2` were arbitrary, `F` is constant.  This also proves the sharper geometric statement:
every finite cylinder projects surjectively onto the entire quotient.

### Positive survivor: cofinal observation is necessary and can work

The law does not say completed information is inaccessible.  It says a nonconstant completed
invariant must escape every fixed finite coordinate set.  The corpus supplies an exact positive
model: Sonin packets lose all mass below every band they outrun and retain all mass below every
band that outruns them.  Between one moving slow band and one moving fast band, their Fourier
energy has an eventual uniform positive floor.  Thus cofinal moving observation detects precisely
the tail energy that every fixed band misses.  The Riemann pole chart and Bohr chart are the
analytic-continuation and infinite-mean counterparts of this constructive escape from finite
observation.

### Universal radial branch

Let `U` be unitary in a nontrivial complex C*-algebra and fix horizon `N` and tolerance `eta>0`.
For `0<r<1`, Bernoulli's inequality gives, for `n<=N`,

```text
||(rU)^n-U^n|| = |r^n-1| <= n(1-r).
```

Choose `r` close enough to one that the last expression is below `eta/2` throughout the finite
horizon.  For every `||O||<=1`, the exact telescoping identity

```text
V O V* - U O U* = (V-U) O V* + U O (V*-U*)
```

and contractivity give a factor-two bound, so the normalized Heisenberg records are within `eta`.
But `||(rU)^n||=r^n` tends to zero; hence `(rU)^n O ((rU)^n)*` tends to zero for every `O`.
This proves finite-horizon compatibility with complete extinction.

### Universal angular branch

For a finite diagonal Hamiltonian with `d+1` levels, its projective recurrence dimension is the
rational rank of the `d` gap coordinates.  For every `1<=k<=d`, vectors of exact rational rank `k`
are dense.  Choose such a gap vector within `eta/(2(H+1))` of the reference gaps.  The operator
Lipschitz estimate for the two diagonal Heisenberg evolutions then keeps every normalized probe
within `eta` for `|t|<=H`, while the completed projective temporal rank is exactly `k`.  Combining
this perturbation with the radial branch produces both incompatible futures from one finite record.

### Complete-time selection

For a finite contraction `T`, the spectral decomposition separates eigenvalues of modulus one from
strictly contractive eigenvalues.  The latter contribution to `inner(x,T^n x)` tends to zero.  The
former is the positive weighted character sum over the peripheral spectrum.  Hence their classes
in the quotient by vanishing histories are equal.  The class is zero exactly when the peripheral
spectral mass is zero.  Every finite cylinder in unrestricted history space still surjects onto the
whole recurrence corona, confirming that completion, not a finite prefix, performs the selection.

### Riemann realization

`CCMUnitaryPolarSourceAtlas` proves unconditionally:

- the derivative crease at `L=log k` recovers `Lambda(k)` exactly;
- the fixed-width rectangular continuation has a simple pole at precisely every shifted
  strict-right Xi zero, with normalized residue equal to analytic multiplicity;
- functional-equation reflection supplies the strict-left sector;
- subtracting twice the reflected strict-right rational divisor from the scaled first clock leaves
  exactly the critical rational divisor;
- that residual converges to a unique continuous Bohr-almost-periodic screw series, and its
  nonzero Bohr coefficients recover every critical-line multiplicity.

For the centered character `exp(z(rho-1/2))`, `Re(rho-1/2)` is its radial exponent and
`Im(rho)` its angular frequency.  The preceding atlas is therefore the claimed exact
source--radial--angular realization.  No zero exclusion is used.

## Formal evidence

- `formal/GaloisForLFunctions/HTGeometry/TailQuotientSeparationLaw.lean`
  - `finiteCoordinateCylinder_surjective_quotient`
  - `finiteCoordinate_quotientReporter_constant`
  - `nonconstant_finiteModificationQuotientReporter_not_determinedBy`
  - `finiteModificationQuotient_fiber_dense`
  - `finiteModificationQuotient_coinduced_eq_indiscrete`
  - `continuousAt_pullback_finiteModificationQuotientReporter_constant`
  - `finiteCylinder_surjective_tailQuotient`
  - `finiteHorizon_tailQuotientReporter_constant`
  - `nonconstant_tailQuotientReporter_not_determinedBy`
- `formal/GaloisForLFunctions/HTGeometry/TailHadamardFiniteObservationSeparationLaw.lean`
  - `finiteCoordinateCylinder_surjective_tailHadamardReducedProduct`
  - `finiteCoordinate_tailHadamardReporter_constant`
- `formal/GaloisForLFunctions/HTGeometry/RadialAngularRecurrenceCompletionLaw.lean`
  - `exists_scalarDampedUnitary_heisenberg_finiteHorizon_close_extinct`
  - `exists_finiteQuantumRecurrenceFutureFan`
- `formal/GaloisForLFunctions/RHTower/UniversalPersistentRecurrenceSelectionLaw.lean`
  - `finiteContraction_returnAmplitude_sub_persistentCarrier_tendsto_zero`
  - `finiteContraction_returnAmplitude_tendsto_zero_iff_persistentMass_zero`
- `formal/GaloisForLFunctions/RHTower/QuantumRecurrenceCoronaLaw.lean`
  - `finiteContraction_recurrenceCorona_eq_persistentCarrier`
  - `finiteContraction_recurrenceCorona_eq_zero_iff_persistentMass_zero`
  - `finiteCylinder_surjective_recurrenceCorona`
- `formal/GaloisForLFunctions/RHTower/AsymptoticCompletionSeparationLaw.lean`
  - `recurrenceAsymptoticSetoid_tailSaturated`
  - `finiteHorizon_recurrenceCoronaReporter_constant`
  - `nonconstant_recurrenceCoronaReporter_not_determinedBy`
- `formal/GaloisForLFunctions/RHTower/SingularGradeFiniteObservationSeparationLaw.lean`
  - `singularGradeSetoid_finiteModificationSaturated`
  - `finiteCoordinateCylinder_surjective_singularGradeQuotient`
  - `finiteCoordinate_singularGradeReporter_constant`
- `formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`
  - `exists_pos_eventually_le_fourier_band_gap`
- `formal/GaloisForLFunctions/RHTower/CCMUnitaryPolarSourceAtlas.lean`
  - `ccmFirstClockCreasePolarFrequencyAtlas`
- `formal/GaloisForLFunctions/RHTower/CCMFirstClockAsymptoticBohrTorelli.lean`
  - `ccmFirstClockAsymptoticBohrModel_eq_explicitScrew`
  - `bohrCoefficient_ccmFirstClockAsymptoticBohrModel_eq_multiplicity`
  - `ccmFirstClockAsymptoticBohrModel_recovers_absoluteMultiplicity`

Direct check and axiom audit of the new radial--angular module remain to be repeated in this lane
after other foreground builds stop.  Existing atlas and recurrence modules are already in corpus;
final audit remains pending.

## Hostile novelty and significance boundary

- Radial damping of a unitary and density of prescribed rational ranks are individually elementary.
  They are not novelty claims.
- Peripheral/transient spectral splitting is classical.  The recurrence-corona formulation is a
  bridge, not a priority claim without deeper literature audit.
- The splice proof of `(A)` is elementary once the correct quotient is named.  Its significance is
  explanatory, not technical: it is the representation-independent impossibility theorem behind
  every attempted finite observer of a complete spectral phase.
- Candidate scientific contribution is the combination of the exact categorical law `(A)`, its
  robust physical future-fan, and its literal Riemann source realization: one finite physical
  record admits extinct and arbitrarily ranked recurrent futures, while one arithmetic clock
  resolves source birth and the complete divisor only by singular boundary readouts.
- This theorem explains why finite-time positivity, bounded Hilbert-space completion, or one regular
  scalar observer cannot replace the pole and recurrence charts.  It does not prove their polar
  chart is empty and therefore does not prove RH.
- Paper inclusion is conditional on concise presentation.  If it reads as analogy rather than a
  theorem-driven interpretation of the atlas, omit it rather than create another collage.

## 2026-08-01 strengthening: kernel-pair transversality and orientation before completion

Finite support is only one collision mechanism.  Whole-corpus census now covers 7,223 modules
and 79,162 declarations; the RH obstruction audit exposes 689 clusters.  Their dominant mechanisms
are literal divisor reading, even/positive scalarization, finite-window loss, reflection-phase
folding, and regular analytic or spectral completion.  These suggest one stronger law.

For maps

```text
X --pi--> Q,       X --tau--> T,       X --chi--> C,
```

write `K_f={(x,y):f(x)=f(y)}`.  Then:

1. every downstream observer of `pi` has kernel containing `K_pi`;
2. `chi` is recoverable from `(pi,tau)` exactly when
   `K_pi intersect K_tau` is contained in `K_chi`;
3. if `pi` is invariant under an involution and `chi` is reflection-odd, then `chi` cannot descend
   through `pi` away from its zero locus; every sufficient `tau` must separate each reflected pair;
4. if the `pi`-fibres are dense, every separated continuous downstream reporter is constant;
5. if the collision is all-orders-flat versus finite Rees grade, every exact bounded sewing
   channel has norm beyond every finite inverse order.

This is the candidate **orientation-before-completion law**.  The generic support theorem is its
local-cylinder instance.  Hedenmalm dense radicals and full-product graph closures are dense-kernel
instances.  Reflection-even Weil energies and positive Grams are involutive-kernel instances.
Finite-Rees sewing is the quantitative radical instance.  Wold--Poisson, Sonin--Calkin, and Ward
are downstream consumers of the surviving transverse character.  Julia/Fisher odd jets, source
loop currents, prime-window residues, and the crease--pole--Bohr atlas are positive transverse
channels.  Arithmetic cancellation and sign production remain genuine upstream walls rather than
downstream repairs.

The paper must use this single kernel-pair theorem as architecture.  It must not present the
instances as additional main theorems or claim that category-specific analytic estimates follow
from the set-level identity without their verified hypotheses.
