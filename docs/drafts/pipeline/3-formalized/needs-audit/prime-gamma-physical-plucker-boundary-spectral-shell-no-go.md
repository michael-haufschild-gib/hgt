# Prime--Gamma physical Pluecker boundary spectral-shell no-go

- **ID:** `prime-gamma-physical-plucker-boundary-spectral-shell-no-go`
- **Stage:** 3-formalized / needs audit
- **Type:** `[FALSIFIED CANONICAL INVERSE REBALANCING] [THEOREM] [EXACT POSITIVE SURVIVOR] [P-G102]`
- **Parents:**
  `prime-gamma-physical-plucker-boundary-amplification-no-go.md`,
  `prime-gamma-physical-plucker-first-trace-no-go.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerBoundarySpectralShellNoGo.lean`

## Conjecture attacked

P-G101 excludes amplitude eight in both bounded channels of canonical resolvent partition but
leaves unnormalized inverse `(eps+T)^-1` at `eps<=1/8`.  P-G102 tests whether this channel can
rebalance coefficient-faithful fourth-depth column along actual zero-boundary limit.

Conjecture: for arbitrarily small positive `eps`, existing positive physical Pluecker operator has
nonzero vector satisfying

```text
(eps+T)^-1 v = 8v.
```

## Exact killing theorem

Functional calculus gives exact spectral localization for every real `c!=0`:

```text
(eps+T)^-1 v = cv  =>  Tv = (1/c-eps)v.
```

Literal positive rank-one expansion gives operator budget

```text
||T|| <= nuclearTraceMass <= 1/50.
```

At required `c=8`, inverse eigenvector would force original eigenvalue `1/8-eps`.  Whenever

```text
0 < eps < 21/200 = 1/8 - 1/50,
```

this value is strictly larger than operator norm.  Thus vector must be zero.  No amplitude-eight
inverse eigenvector can persist in any approach to zero boundary.

## No-go closure

- **Exact killing theorem/mechanism:** prescribed inverse gain is rigid positive spectral shell,
  and current source trace bounds full positive spectrum below that shell near zero.
- **Strongest positive survivor:** P-G100 weighted boundary trace and polar cancellation remain
  exact reference geometry, but correction must change operator before inversion.  Lawful target
  is oriented off-diagonal source/co-source shorting whose cross term can pay `63w/64`; no scalar
  function of current positive `T` can do so.
- **New insight:** “singular inverse” and “zero-spectrum source” are not equivalent.  Fixed finite
  inverse gain eight selects shell tending to `1/8`, whereas actual singular norm comes from gains
  diverging like `1/eps` at zero.  SP-E normalization debt is a finite-shell request incompatible
  with P-G99 trace budget.
- **Status:** dependency-closed proof and Lean formalization complete; external novelty audit
  pending.  No Xi or RH identification claimed.

## Higher universal principle

Three resources must be kept separate: cofinal rank capacity, local gain, and spectral support.
Boundary transfer repairs first; normalization debt demands second; scalar resolvent fixes third.
Once positive incidence is spectralized, trace budget bounds all scalar functional-calculus repair.
Completed orientation must therefore enter before positivity, through source/co-source incidence
whose off-diagonal shorting changes operator rather than postprocessing spectrum.

## Conjecture loop audit

1. **Conjecture:** existing orthogonal `4+4` source law supplies scalar amplitude eight.
   **Failed:** it gives total squared norm eight and source norm `sqrt 8`, not vector gain eight;
   pointed radial half is gauge.
2. **Conjecture:** unnormalized inverse gets amplitude eight from continuous zero singularity.
   **Failed:** exact gain eight localizes at `1/8-eps`, tending to positive shell `1/8`.
3. **Conjecture:** physical operator contains required shell near boundary.
   **Failed sharply:** `||T||<=1/50`, excluding shell for `eps<21/200`.
4. **Pivot:** change operator before inversion by oriented off-diagonal source/co-source shorting;
   exact `63w/64` cross-budget and Xi charge remain open.

## Formal status

Lean proves without added axioms:

- `positiveBoundaryInverse_eq_real_smul_imp_operator_eq_smul`;
- `norm_gammaSewnCriticalPhysicalPluckerSpectralOperator_le_nuclearTraceMass`;
- `norm_gammaSewnCriticalPhysicalPluckerSpectralOperator_le_one_div_fifty`;
- `gammaSewnCriticalPhysicalPluckerBoundaryInverse_no_amplitude_eight_near_zero`;
- `gammaSewnCriticalPhysicalPlucker_canonicalBoundaryResolvent_cannot_rebalance_near_zero`.

Direct `lake env lean` checks and exact target builds pass.  `#print axioms` reports only `propext`,
`Classical.choice`, and `Quot.sound`.  RHTower umbrella import is wired; no umbrella build was run.

## Open core

P-G103 now classifies exact operator target: negative polar pivot `-w` with unique nonnegative cross
`(sqrt 63 / 8)w`. Construct this cross term from literal Gamma/co-Poisson/Stokes data, retain P-G100
four-unit relative cancellation, and identify completed Xi divisor.

## Log

- 2026-08-16 — unnormalized inverse survivor killed throughout zero-boundary neighborhood;
  exact `21/200` spectral-shell threshold formalized as P-G102.
