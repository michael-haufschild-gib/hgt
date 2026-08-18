# Source-horizontal second-Cartier orbit coercivity (2026-08-18)

## Formal result
Added `formal/GaloisForLFunctions/RHTower/SourceHorizontalSecondCartierOrbitCoercivity.lean`, wired into `RHTower.lean`.

For positive energy
`Q(u,(a,b)) = ‖u‖² + ‖a+b‖²`
and polarized ghost orbit
`T_(lam^n)(1,(c,c))`, Lean proves the exact identity
`Q = ‖lam‖^(2n) + 4‖c‖² (‖lam‖⁻¹)^(2n)`.
For nonzero `lam,c`, forward-orbit boundedness iff `‖lam‖=1`.

Actual strict-right Xi specialization uses literal
`sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q p`
and
`sourceHorizontalActualXiSecondCartierKreinScale x u q r N`.
Under nonzero Julia coupling/aperture and positive BV endpoint third jet, energy tends to `+∞` for every `q : XiRightZeroCopy` and prime `p`.
Capstone conjoins divergence with exact support-fibre sum, preserving `xiSupportMultiplicity`.
Universal actual boundedness is proved iff RH.

## Scientific verdict
Existing Hermitian-incidence/Krein shell cannot hide compactness: every off-line retained fibre has explicit reciprocal hyperbolic escape. Indefinite invariants are blind to the positive radial energy. This closes the “derive compactness from current shell” idea negatively.

RH is not closed. Remaining viable producer is precise: an unconditional completed-source, coefficient- and multiplicity-faithful admission into a fixed literal endpoint fibre that uniformly bounds this exact Q along the prime-transfer orbit. Any such theorem would force unit character modulus and hence criticality. Existing incidence, determinant, Krein form, and scalar conormal short do not control Q.

## Verification
- `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalSecondCartierOrbitCoercivity.lean`: pass.
- Exact leaf `lake build GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierOrbitCoercivity`: pass.
- Main theorem axiom audits: only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint still reports unrelated unwired HTGeometry files; new RHTower module is wired.
- No umbrella build run.

Paper/formal card: `docs/drafts/pipeline/3-formalized/source-horizontal-second-cartier-orbit-coercivity.md`.
Frontier map updated.