# HB source-independent response dichotomy

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC20

For a divisor-independent scalar response `c`, prove the exact pointwise classification

`correctedCurrent(n,c,q)=0 ↔ c=0 ∨ Re(q)=1/2`

and global classification

`(∀ q, correctedCurrent(n,c,q)=0) ↔ c=0 ∨ RH`.

Equivalently, zero response is exactly the blind branch, while every nonzero fixed scalar response
retains full RH force. At unit response, identify this Ward law with HC18 canonical optical
darkness.

## Result

HC20 holds. Lean proves exact factorization

`sourceIndependentCurrent(n,c,q) = c * unsquaredSourceCurrent(n,q)`.

The local and global zero classifications follow with no auxiliary premise. In particular, the
unit fixed-response Ward identity is equivalent both to RH and to universal vanishing of canonical
Peierls--Darboux optical power. Any nonzero fixed response is nonzero at every tilted Xi copy.

## Main Lean theorems

- `d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_mul`
- `d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff`
- `forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff`
- `forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff_rh_of_ne_zero`
- `forall_d4BMXiSecondHarmonicSourceIndependentUnitResponseCurrent_eq_zero_iff_rh`
- `d4BMXiSecondHarmonicSourceIndependentUnitWard_iff_canonicalOpticalWard`
- `d4BMXiSecondHarmonicSourceIndependentResponseCurrent_ne_zero_of_tilt`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceIndependentResponseDichotomy.lean`

## New knowledge

HC19 and HC20 give an exact response boundary. Division-free source-matched reflected response can
cancel every fibre while optical power stays positive. By contrast, a source-independent scalar
response cannot alter the physical zero locus unless it collapses identically to zero. Thus no
nonzero constant renormalization, phase, excitation factor, or scalar normalization can fake HB
stationarity.

The remaining proof burden is narrowed to one physical noncollapse statement: derive the relevant
divisor-independent response scalar from the literal action/Green/QNM construction and prove it is
nonzero. Once supplied, HC20 converts its universal Ward law directly to RH.

## Literature audit through 2026-08-28

Primary literature distinguishes source-dependent QNM excitation coefficients from universal,
initial-data-independent Green-function excitation factors and constructs conserved Kerr bilinear
currents. Search found no Xi-divisor fixed-response current, no exact blind/nonblind
`c=0 ∨ critical wall` classification, and no `c=0 ∨ RH` or optical-darkness equivalence:

- Berti--Cardoso, *Quasinormal ringing of Kerr black holes: The excitation factors*,
  https://arxiv.org/abs/gr-qc/0605118
- Zhang--Berti--Cardoso, *Quasinormal ringing of Kerr black holes. II. Excitation by particles
  falling radially with arbitrary energy*, https://arxiv.org/abs/1305.4306
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935
- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*,
  https://arxiv.org/abs/1402.1282

Novelty claim is the exact source-independent response classification and its RH/optical Ward
identification, not the classical excitation-factor or Peierls frameworks.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingBMSourceIndependentResponseDichotomy.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceIndependentResponseDichotomy`
- Build result: success, 11914 jobs after shared dependency replay
- `#print axioms` on seven endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token and diff-whitespace scans: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated umbrella reachability failures; this module is reachable and
  has no lint finding

## Remaining HB burden

Construct the literal action-derived or Green/QNM response scalar and prove its noncollapse and
source independence. HC20 then supplies the complete algebraic conversion from its Ward identity
to RH.
