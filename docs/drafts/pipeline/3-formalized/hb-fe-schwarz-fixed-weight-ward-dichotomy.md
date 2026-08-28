# HB FE--Schwarz fixed-weight Ward dichotomy

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC17

For fixed reflection-invariant real orbit weights `a,b`, universal vanishing of the exact HC16
weighted Peierls trace is equivalent to

`a+b=0 ∨ RH`.

Hence every zero-total FE--Schwarz boundary orientation gives an unconditional but RH-blind Ward
identity, while every nonzero-total (in particular positive) Ward identity is itself equivalent to
RH.

## Result

HC17 holds exactly. Define the fixed-weight Ward identity by universal vanishing over all
nontrivial Xi zeros of the HC16 weighted orbit trace. Lean proves

`WardIdentity(n,a,b) ↔ a+b=0 ∨ RiemannHypothesis`.

For `a+b ≠ 0`, the Ward identity is equivalent to RH. In particular, the equal positive weighting
`a=b=1` is equivalent to RH. Conversely, every zero-total weighting `a,-a` satisfies the Ward
identity unconditionally and therefore carries no information about zero location.

## Main Lean theorems

- `hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff`
- `hbXiPeierlsFESchwarzFixedWeightWardIdentity_iff_rh_of_sum_ne_zero`
- `hbXiPeierlsFESchwarzPositiveWeightWardIdentity_iff_rh`
- `hbXiPeierlsFESchwarzZeroTotalWardIdentity`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFESchwarzFixedWeightWardDichotomy.lean`

## New knowledge

Fixed-weight orbit stationarity has a complete classification. It is not an extra symmetry fact:
it is either the algebraically vacuous zero-total character or RH itself. This closes the residual
possibility that FE reflection, Schwarz conjugation, Stokes orientation, or a fixed group character
could produce a useful global Ward law without supplying new physical content.

The positive survivor is exact: any independently derived nonzero-total Einstein--Teukolsky Ward
identity closes the HB route by proving RH. The equal-positive orbit identity is the canonical
minimal endpoint.

## Literature audit through 2026-08-28

Primary literature supplies the separate frameworks of covariant Peierls brackets, reflection
currents for Kerr perturbations, and nonlinear Teukolsky sources. Search found no Xi-divisor
FE--Schwarz fixed-weight Ward identity and no theorem classifying universal stationarity as
`zero-total weights ∨ RH`:

- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*,
  https://arxiv.org/abs/1402.1282
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935
- Spiers--Pound--Moxon, *Second-order Teukolsky formalism in Kerr spacetime: formulation and
  nonlinear source*, https://arxiv.org/abs/2305.19332
- Ripley--Loutrel--Giorgi--Pretorius, *Numerical computation of second order vacuum perturbations
  of Kerr black holes*, https://arxiv.org/abs/2010.00162

Novelty claim is the exact fixed-weight classification and RH equivalence, not general existence
of Ward identities, conserved currents, Peierls brackets, or nonlinear Teukolsky sources.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMFESchwarzFixedWeightWardDichotomy.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFESchwarzFixedWeightWardDichotomy`
- Build result: success, 11897 jobs after shared dependency replay
- `#print axioms` on four endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token and diff-whitespace scans: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated umbrella reachability failures; this module is reachable and
  has no lint finding

## Remaining HB burden

Derive one nonzero-total Ward identity from a literal gauge-fixed Einstein--Teukolsky action,
boundary current, or optical conservation law. HC17 proves that formal symmetry cannot derive it;
any successful derivation is already an RH proof.
