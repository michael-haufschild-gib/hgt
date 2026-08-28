# HB FE--Schwarz orbit Peierls trace

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC16

Sum the exact HC14 global Peierls cubic cuts over the complete multiplicity-exact FE--Schwarz
quartet

`q, reflect q, conj q, reflect (conj q)`,

using the canonical sectorwise unit-carrier source amplitude. The orbit trace is invariant under
both reflection and conjugation without requiring branch equality, and has exact value

`-4 * normSq(mixing(q)) * (8n + 5)`.

Consequently it is strictly negative off the critical wall, vanishes exactly on the wall, and
universal vanishing is equivalent to RH. More generally, every positive reflection-invariant
weighting of the two conjugate reflection pairs has the same zero locus.

## Significance target

Construct the minimal four-sector orbit-level landing forced by HC15. If true, this closes orbit
covariance but proves that positive real-closure symmetrization cannot cancel the BM source
obstruction: it doubles it. A surviving physical action must supply a genuinely signed/complex
FE--Schwarz character, and its Ward law must force the orbit trace to vanish.

## Result

HC16 holds. The single HC14 target-independent global Peierls operator realizes all four
sectorwise unit-carrier cubic cuts. Their complete orbit trace is

`-4 * normSq(mixing(q)) * (8n + 5)`.

It is automatically invariant under both multiplicity-exact functional-equation reflection and
Schwarz conjugation, strictly negative in real part at every tilted Xi copy, zero exactly on the
critical wall, and universally zero exactly under RH.

The stronger weight classification also closes. Give equal real weight `a` to `q, reflect q` and
equal real weight `b` to `conj q, reflect(conj q)`. Then

`weightedTrace = -2 * (a+b) * normSq(mixing(q)) * (8n+5)`

and

`weightedTrace = 0 ↔ a+b=0 ∨ Re(q)=1/2`.

Thus every positive-total-weight physical average preserves the RH detector. Opposite pair weights
cancel unconditionally, but only by erasing all detector information.

## Main Lean theorems

- `hbXiPeierlsUnitCarrierCubicCutAt_eq`
- `hbXiPeierlsFESchwarzOrbitCubicTrace_eq`
- `hbXiPeierlsFESchwarzOrbitCubicTrace_reflect`
- `hbXiPeierlsFESchwarzOrbitCubicTrace_conj`
- `hbXiPeierlsFESchwarzOrbitCubicTrace_re_neg_of_tilt`
- `forall_hbXiPeierlsFESchwarzOrbitCubicTrace_eq_zero_iff_rh`
- `hbXiPeierlsFESchwarzWeightedOrbitCubicTrace_eq_zero_iff`
- `hbXiPeierlsFESchwarzSignedOrbitCubicTrace_eq_zero`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFESchwarzOrbitPeierlsTrace.lean`

## New knowledge

Four-sector real closure solves covariance but not stationarity. The natural positive orbit trace
adds rather than cancels, producing a representation-independent real sign. The weight
classification proves a sharp dichotomy unavailable from either the two-branch no-go or the
existing real-closure cardinality theorem: a reflection-invariant real quartet can vanish off wall
only through zero total conjugate-pair weight, and that signed character is identically blind.

This narrows the HB endpoint to one physical statement: a positive/nonzero-total-weight
Einstein--Teukolsky Ward or boundary conservation law forcing this already-covariant orbit trace to
vanish. Such a law would imply RH directly; orbit symmetrization alone cannot supply it.

## Literature audit through 2026-08-28

Primary literature provides the separate ingredients of covariant Peierls brackets, nonlinear
Teukolsky sources, second-order Kerr evolution, and reflection-derived QNM bilinear currents. The
audit found no Xi-divisor FE--Schwarz quartet Peierls trace, no exact negative orbit formula, and no
reflection-invariant weight zero-locus classification:

- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*,
  https://arxiv.org/abs/1402.1282
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935
- Spiers--Pound--Moxon, *Second-order Teukolsky formalism in Kerr spacetime: formulation and
  nonlinear source*, https://arxiv.org/abs/2305.19332
- Ripley--Loutrel--Giorgi--Pretorius, *Numerical computation of second order vacuum perturbations
  of Kerr black holes*, https://arxiv.org/abs/2010.00162

Novelty claim is the exact four-sector construction, invariance, sign law, and complete weight
classification, not general existence of Peierls brackets, Teukolsky sources, or reflection
currents.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFESchwarzOrbitPeierlsTrace.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFESchwarzOrbitPeierlsTrace`
- Build result: success, 11895 jobs after shared dependency replay
- `#print axioms` on six endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token and diff-whitespace scans: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated umbrella reachability failures; this module is reachable and
  has no lint finding

## Remaining HB burden

Derive, from a literal gauge-fixed Einstein--Teukolsky action or boundary Ward identity, vanishing
of the positive orbit trace. HC16 proves that covariance and real closure are insufficient; the
needed input must be physical stationarity/conservation with nonzero total orbit weight.
