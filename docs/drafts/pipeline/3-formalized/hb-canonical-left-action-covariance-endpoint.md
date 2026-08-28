# HB canonical left-action covariance endpoint

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC22

Separate exact canonical left-coordinate Peierls incidence from two-branch FE--Schwarz covariance.
Prove:

1. canonical left-source covariance at one Xi fibre is equivalent to the critical-line equation;
2. universal unit canonical left-source covariance is equivalent to RH;
3. actual global left-coordinate Peierls incidence holds unconditionally;
4. incidence plus canonical covariance is equivalent to RH, unit canonical left-response
   stationarity, and canonical orbit optical darkness;
5. every tilted fibre retains incidence while covariance fails and optical power is positive.

## Result

HC22 holds. The existing global Peierls propagator realizes exact unit-amplitude BM incidence for
the literal canonical left-coordinate source packets on every Xi fibre. For nonzero amplitude,
reflection exchanges regular and complementary canonical left sources exactly when
`Re(q)=1/2`.

Define `HBXiPeierlsCanonicalLeftActionCovariance n` as the conjunction of actual global incidence
and universal unit left-source covariance. Lean proves, without hypotheses,

`HBXiPeierlsCanonicalLeftActionCovariance n ↔ RiemannHypothesis`.

The same proposition is exactly equivalent to HC21 unit canonical regular-left Ward and HC18
canonical FE--Schwarz orbit optical darkness. At every tilted fibre, the incidence equality remains
true, source covariance is false, and canonical orbit optical power is strictly positive.

## Main Lean declarations

- `HBXiPeierlsCanonicalLeftActionIncidence`
- `HBXiPeierlsCanonicalLeftBranchCovariance`
- `HBXiPeierlsCanonicalLeftActionCovariance`
- `hbXiPeierlsCanonicalLeftSource_reflect_eq_iff`
- `hbXiPeierlsCanonicalUnitLeftSourceCovariance_iff_regularLeftCurrent_zero`
- `hbXiPeierlsCanonicalLeftActionIncidence_holds`
- `hbXiPeierlsCanonicalLeftBranchCovariance_iff_rh`
- `hbXiPeierlsCanonicalLeftActionCovariance_iff_rh`
- `hbXiPeierlsCanonicalLeftActionCovariance_iff_regularUnitLeftWard`
- `hbXiPeierlsCanonicalLeftActionCovariance_iff_opticalWard`
- `hbXiPeierlsCanonicalLeftAction_tilted_incidence_noCovariance_positiveOptical`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalLeftActionCovarianceEndpoint.lean`

## New knowledge

Action incidence and two-branch covariance are independent burdens in the explicit BM model.
Incidence is already solved by a single target-independent global Peierls operator and survives
off wall. Canonical two-branch FE covariance is exactly the critical-line equation fibrewise and
exactly RH globally. Therefore adding canonical incidence to covariance contributes no hidden
analytic premise: the entire remaining package is precisely RH.

The tilted theorem is the sharp positive obstruction. It proves a concrete trichotomy on the same
explicit fibre: exact action incidence, failed two-branch covariance, positive orbit radiation.
This forces any off-wall continuation away from individual two-branch covariance and toward the
already Lean-constructed four-sector FE--Schwarz orbit landing.

## Literature audit through 2026-08-28

Primary literature supports the component technologies: covariant phase space and Peierls
brackets; Kerr QNM bilinear forms, reflection symmetry, and mode projections; Green-function QNM
excitation factors; and beyond-GR excitation calculations. Search found no prior theorem combining
an explicit Xi-indexed BM Peierls action, canonical left-source FE covariance, a fibrewise
critical-wall classification, and a global RH equivalence:

- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*,
  https://arxiv.org/abs/1402.1282
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935
- Berti--Cardoso, *Quasinormal ringing of Kerr black holes: The excitation factors*,
  https://arxiv.org/abs/gr-qc/0605118
- Silva et al., *Quasinormal modes and their excitation beyond general relativity*,
  https://arxiv.org/abs/2404.11110

Novelty claim is the exact incidence/covariance separation and its RH-complete classification, not
generic Peierls or QNM projection theory.

## Verification

- Scratch: `lake env lean /tmp/HC22.lean`
- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalLeftActionCovarianceEndpoint.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalLeftActionCovarianceEndpoint`
- Build result: success, 11916 jobs after dependency replay
- `#print axioms` on nine endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token scan: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated umbrella reachability failures; HC22 is reachable and has no
  lint finding

## Remaining HB burden

Derive canonical two-branch left-source FE covariance from an independent physical or arithmetic
law without assuming an RH-equivalent Ward statement, or exploit the four-sector FE--Schwarz orbit
survivor to obtain a new coercive/nonnegative identity whose vanishing cannot be manufactured by a
covariant response compensator.

