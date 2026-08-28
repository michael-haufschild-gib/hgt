# HB canonical left-response Ward

Status: formalized
Route: HB
Started: 2026-08-28
Completed: 2026-08-28

## Conjecture HC21

Evaluate each canonical BM left connection covector on its own exact horizon-to-AdS connection
column after multiplying that outer column by one global scalar `c`. Although covectors and outer
coefficients depend on Xi divisor `q`, prove that regular and complementary evaluations are
identically `c` on every fibre.

Use these literal left-coordinate evaluations as Peierls response corrections. Prove that both
currents coincide with HC20 fixed scalar response current and satisfy

`(∀ q, canonicalLeftCurrent(n,c,q)=0) ↔ c=0 ∨ RH`.

At unit normalization, identify both branch Ward laws with canonical Peierls--Darboux optical
darkness.

## Result

HC21 holds. Both canonical dual evaluations remove all Xi-dependent connection coefficients
exactly. This is equality to `c`, not merely equality up to a nonzero fibre factor. Their response
functions are extensionally equal to HC20 constant correction, and their Peierls currents agree
pointwise with the source-independent scalar current.

Lean proves local `c=0 ∨ critical wall` and global `c=0 ∨ RH` classifications for both branches.
At `c=1`, either universal left-response Ward identity is exactly equivalent to HC18 canonical
optical darkness.

## Main Lean theorems

- `d4BMXiSecondHarmonicCanonicalRegularLeftResponse_eq`
- `d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse_eq`
- `d4BMXiSecondHarmonicCanonicalRegularLeftResponse_fun_eq`
- `d4BMXiSecondHarmonicCanonicalComplementaryLeftResponse_fun_eq`
- `d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq_zero_iff`
- `d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq_zero_iff`
- `forall_d4BMXiSecondHarmonicCanonicalRegularLeftResponseCurrent_eq_zero_iff`
- `forall_d4BMXiSecondHarmonicCanonicalComplementaryLeftResponseCurrent_eq_zero_iff`
- `d4BMXiSecondHarmonicCanonicalRegularUnitLeftWard_iff_canonicalOpticalWard`
- `d4BMXiSecondHarmonicCanonicalComplementaryUnitLeftWard_iff_canonicalOpticalWard`

Module:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalLeftResponseWard.lean`

## New knowledge

Canonical radial dual normalization turns fibre-dependent exact BM connection data into a genuinely
divisor-independent response scalar. Regular and complementary horizon branches give the same
fixed response and the same RH-complete Ward law. Thus radial normalization choice, connection
coefficient variation, and noncollapse are no longer independent HB burdens.

Subsequent HC22 corpus synthesis corrects the remaining-gap diagnosis recorded at HC21 completion.
`ThetaCuspHawkingBMGlobalLeftCoordinatePeierlsIncidence` already proves exact incidence for these
canonical left source packets under one target-independent global Peierls propagator. The remaining
two-branch gap is FE--Schwarz covariance of the literal canonical left sources, not action
incidence. HC22 proves that covariance is itself exactly equivalent to RH.

## Literature audit through 2026-08-28

Primary literature develops universal Green-function QNM excitation factors, Kerr conserved
bilinear forms and mode projections, and first-principles excitation calculations. Search found no
Xi-indexed BM horizon-to-AdS dual-column normalization, no proof that both radial branches return
one global scalar, and no induced `c=0 ∨ RH` or optical Ward classification:

- Berti--Cardoso, *Quasinormal ringing of Kerr black holes: The excitation factors*,
  https://arxiv.org/abs/gr-qc/0605118
- Green et al., *Conserved currents for Kerr and orthogonality of quasinormal modes*,
  https://arxiv.org/abs/2210.15935
- Silva et al., *Quasinormal modes and their excitation beyond general relativity*,
  https://arxiv.org/abs/2404.11110
- Khavkine, *Covariant phase space, constraints, gauge and the Peierls formula*,
  https://arxiv.org/abs/1402.1282

Novelty claim is the exact dual normalization across Xi fibres and its RH/optical Ward consequence,
not generic QNM projection or excitation-factor theory.

## Verification

- Direct: `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingBMCanonicalLeftResponseWard.lean`
- Target audit: `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalLeftResponseWard`
- Build result: success, 11915 jobs after dependency replay
- `#print axioms` on ten endpoints: `[propext, Classical.choice, Quot.sound]` only
- Forbidden-token and diff-whitespace scans: clean
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build run
- Global lint reports only unrelated umbrella reachability failures; this module is reachable and
  has no lint finding

## Remaining HB burden after HC22 correction

Exact action incidence and canonical left normalization are both closed. Prove canonical
two-branch FE--Schwarz covariance from an independent physical/arithmetic law, or work through the
four-sector orbit survivor; HC22 shows the two-branch covariance statement is already equivalent to
RH and fails at every tilted fibre.
