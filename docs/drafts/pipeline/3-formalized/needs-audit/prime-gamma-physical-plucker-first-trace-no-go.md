# Prime--Gamma physical Pluecker fixed-node first-trace no-go

- **ID:** `prime-gamma-physical-plucker-first-trace-no-go`
- **Stage:** 3-formalized / needs audit
- **Type:** `[FALSIFIED DIRECT IDENTIFICATION] [THEOREM] [EXACT POSITIVE SURVIVOR] [P-G99]`
- **Parents:**
  `hedenmalm-theta-route-p-plucker-covariance-operator.md`,
  `prime-gamma-physical-plucker-entire-determinant.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerFirstTraceNoGo.lean`

## Conjecture attacked

P-G98 produces a positive faithful Schatten-one physical Pluecker operator `T`, a stable reflected
`det2(I + uT)`, and a canonical ordinary Fredholm repair

```text
exp(u * sourceTrace) det2(I + uT) = det(I + uT).
```

Conjecture: canonical repair is completed Xi in square coordinate.  Its first derivative would
force the literal nuclear source mass to equal `thetaCuspNormalizedEvenMoment 1 / 2`.

## Exact killing theorem

The covariance diagonal has an exact Bernoulli form.  For every packet `z` and coordinate `i`,

```text
C_z(i,i) = m_z,i (1 - m_z,i),
```

where `m_z,i` is coordinate-selection mean.  Consequently source trace is not hidden spectral
notation:

```text
sourceTrace
  = sum_z blockWeight_z
      sum_i node_z,i * m_z,i * (1 - m_z,i).
```

Critical Stokes arithmetic gives rational, computation-free bounds:

```text
prime-two base node                 < 1/25,
every base node at prime p >= 3    < 3/125,
every four-node adjacent packet sum < 2/25.
```

For every real `m`, not only `m in [0,1]`,

```text
m(1-m) <= 1/4.
```

Hence every local Bernoulli quadratic is strictly below `1/50`.  Positive normalized block
weights have total mass one, so

```text
sourceTrace <= 1/50.
```

The independent prime--archimedean moment theorem gives

```text
1/50 < thetaCuspNormalizedEvenMoment 1 / 2.
```

Therefore canonical ordinary determinant has wrong first jet:

```text
deriv ordinaryPhysicalPlueckerDet 0
  != thetaCuspNormalizedEvenMoment 1 / 2.
```

Direct `det2` was already impossible because its first derivative is zero.  P-G99 now excludes
both canonical determinant conventions before any higher-coefficient comparison.

## No-go closure

- **Exact killing theorem/mechanism:** fixed positive reciprocal-gap nodes have total packet
  capacity `<2/25`; Bernoulli curvature has universal apex `1/4`; normalized positive sewing cannot
  raise first trace past `1/50`, while Xi first coefficient is strictly larger.
- **Strongest positive survivor:** fixed-node obstruction is independent of physical Pluecker
  probabilities.  It holds for every real four-coordinate mean because `m(1-m)<=1/4` globally.
  P-G94--P-G98 positivity, faithfulness, continuous zero spectrum, negative-real determinant zeros,
  and cofinal convergence remain exact reference geometry, but cannot themselves be Xi.
- **New insight:** probability reweighting, local metric tuning, and canonical trace restoration are
  one exhausted equivalence class.  Viable transfer must leave fixed-positive-node Bernoulli
  quadratic geometry: change/amplify spectral nodes from completed source data, add a genuinely
  signed or indefinite boundary channel, or use a non-Bernoulli singular transfer.  P-G97 further
  requires this operation at continuous zero spectrum rather than through bounded inversion.
- **Status:** paper proof dependency-closed; exact survivor and no-go formalized in Lean; external
  novelty audit pending.  This retires direct P-G98 determinant identification, not SP-E reference
  geometry or all source-derived boundary transfers.

## Higher universal principle

Earlier failures appeared as unrelated normalization debts: uniform Boolean curvature was too
small, fourth-depth transport lost `1/64`, `det2` erased first trace, and ordinary repair restored
only physical mass.  P-G99 identifies their common cause.  Incidence descent correctly fixes a
positive compact geometry, but completed arithmetic requires more first-order spectral capacity
than any fixed-node Bernoulli covariance can carry.  Descent and stability solve geometry; they do
not create archimedean completion charge.  That charge must enter through source completion before
or at singular boundary transfer, not through reweighting probabilities after spectralization.

## Conjecture loop audit

1. **Conjecture:** identify reflected physical `det2` directly with Xi.
   **Failed:** regularization forces zero first derivative.
2. **Pivot:** restore ordinary determinant canonically by `exp(u*sourceTrace)`.
   **Proved:** exact finite Fredholm determinants, trace convergence, and literal nuclear mass.
3. **Conjecture:** literal source mass equals Xi first coefficient.
   **Failed:** unconditional rational wall `sourceTrace <= 1/50 < Xi first coefficient`.
4. **Pivot:** vary six-minor incidence probabilities while retaining physical nodes.
   **Failed more strongly:** every real coordinate mean obeys same local ceiling.
5. **Surviving conjecture:** completed Gamma/polar source supplies a node-changing, amplifying, or
   signed/indefinite singular boundary transfer compatible with P-G97 continuous zero spectrum;
   physical Pluecker operator is its stable reference geometry, not its final scalar determinant.

## Formal status

Lean proves without added axioms:

- `fourRatePluckerCovariance_coordinateDelta_self_eq_bernoulliVariance`;
- `gammaSewnCriticalPhysicalPluckerNuclearTraceMass_eq_tsum_bernoulliTrace`;
- `gammaSewnMobiusApertureStokesSquaredReciprocalGapNode_depth_eq`;
- `gammaSewnCriticalPhysicalPlucker_packetNode_sum_lt_two_div_twentyFive`;
- `gammaSewnCriticalPhysicalPlucker_arbitraryBernoulliTrace_lt_one_div_fifty`;
- `gammaSewnCriticalPhysicalPluckerNuclearTraceMass_le_one_div_fifty`;
- `gammaSewnCriticalPhysicalPluckerNuclearTraceMass_lt_thetaFirstCoefficient`;
- `gammaSewnCriticalPhysicalPluckerOrdinary_firstJet_ne_theta`.

Direct `lake env lean` and target-only module build pass.  `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.  RHTower umbrella import is wired; no umbrella build was run.

## Log

- 2026-08-16 — direct ordinary identification falsified; universal fixed-node Bernoulli capacity
  wall and positive survivor formalized as P-G99.
