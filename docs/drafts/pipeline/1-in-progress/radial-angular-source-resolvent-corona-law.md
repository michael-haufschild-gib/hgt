# Radial--angular source--resolvent--corona law

- **ID:** RASRC-1
- **Stage:** 1-in-progress
- **Type:** THEOREM / SYNTHESIS
- **Source:** `RadialAngularRecurrenceCompletionLaw`, `QuantumRecurrenceCoronaLaw`,
  `CCMUnitaryPolarSourceAtlas`, and the whole RHTower/HTGeometry audit

## Exact claim

`[PAPER-PROVED] [CORPUS] [NOVELTY UNVERIFIED] [NOT RH]`

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

The Riemann first-clock atlas is an arithmetic infinite-divisor realization of the same split.
Finite-aperture creases recover the source births.  Strictly off-critical characters have nonzero
radial exponent and are recovered as poles of fixed-width source continuation.  After subtracting
their reflected polar sector, critical characters have unit modulus and form the unique Bohr
recurrence asymptote, whose coefficients recover multiplicity.  Therefore

```text
birth/current  -> source atoms,
radial/growth  -> off-critical divisor,
angular/corona -> critical divisor.
```

The three readouts are jointly complete.  The finite-horizon future-fan theorem proves that the
radial and angular readouts cannot be collapsed into one bounded finite-time observer in general.

## Dependency-closed proof

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
- `formal/GaloisForLFunctions/RHTower/CCMUnitaryPolarSourceAtlas.lean`
  - `ccmFirstClockCreasePolarFrequencyAtlas`

Direct check and axiom audit of the new radial--angular module remain to be repeated in this lane
after other foreground builds stop.  Existing atlas and recurrence modules are already in corpus;
final audit remains pending.

## Hostile novelty and significance boundary

- Radial damping of a unitary and density of prescribed rational ranks are individually elementary.
  They are not novelty claims.
- Peripheral/transient spectral splitting is classical.  The recurrence-corona formulation is a
  bridge, not a priority claim without deeper literature audit.
- Candidate scientific contribution is the exact future-fan theorem plus its literal Riemann
  source realization: one finite record admits extinct and arbitrarily ranked recurrent futures,
  while one arithmetic clock resolves source birth, radial divisor, and angular divisor by three
  singular boundary readouts.
- This theorem explains why finite-time positivity, bounded Hilbert-space completion, or one regular
  scalar observer cannot replace the pole and recurrence charts.  It does not prove their polar
  chart is empty and therefore does not prove RH.
- Paper inclusion is conditional on concise presentation.  If it reads as analogy rather than a
  theorem-driven interpretation of the atlas, omit it rather than create another collage.

