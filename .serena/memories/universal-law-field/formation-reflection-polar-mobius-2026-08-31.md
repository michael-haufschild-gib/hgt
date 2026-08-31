# ULF-TAFM-22: formation reflection polar mechanics

Closed new route-independent mechanism on 2026-08-31.

Paper:
`docs/drafts/pipeline/2-fully-proven/universal-law-field/topologically-admitted-formation-mechanics/full-formation-reflection-polar-decomposition-boundary-mobius-and-joint-reconstruction-law.md`

Lean:
- `formal/GaloisForLFunctions/HTGeometry/FormationReflectionPolarMechanics.lean`
- `formal/GaloisForLFunctions/HTGeometry/ShiftedEulerFormationReflectionPolarMechanics.lean`
- wired into `formal/GaloisForLFunctions/HTGeometry/UniversalLawField.lean`

Mechanism:
- Weighted free-commutative profile x has total weight T, support weight R, multiplicity defect D=T-R.
- Full packet C_x(ω)=exp(ωT)∏support(1-exp(-2ωℓ)).
- Exact reflection C_x(-ω)=M_x(ω)C_x(ω), with M=(-1)^|support| exp(-2ωD).
- M(-ω)M(ω)=1: lifted reflection is information-neutral.
- For real a, norm M=exp(-2aD); normalized phase=(-1)^|support|.
- With positive occupied weights, norm=1 iff profile is exterior/squarefree.
- Boundary projection times normalized reflection equals formation Möbius. Thus Möbius is derived from reflection polar data, not inserted.
- Prime factorization with weights log p specializes to shiftedEulerCoeff. Squarefree projection of c_-ω equals μ(n)c_ω.
- Joint reconstruction recovers parity from phase and valuation excess from log modulus.

Verification:
- both direct `lake env lean <file>` passes.
- targeted leaf builds pass; no umbrella/full build.
- 11 #print axioms capstones depend only on propext, Classical.choice, Quot.sound.
- no sorry/admit/new axiom/opaque/unsafe.
- formalized mirror and _LEAN-CERTIFICATION updated.

Hostile limitation:
- no Möbius summatory cancellation, Gamma sewing, zero control, or RH.
- general free commutative law cannot distinguish ordinary from generalized primes.
- next load-bearing theorem: completed prime–Gamma recovery must transport this unitary-boundary partial phase and prove global boundary-phase properness/cancellation.
