# Hawking/Teukolsky single-sector frequency-support no-go (2026-08-24)

## New result
For BM frequencies
[
\omega_+=x+i(y-D),\qquad \omega_-=-x+i(-y-D),
]
a real single QNM supplies Fourier generators \(\omega_+\) and \(-\bar\omega_+\). A finite stationary monomial with multiplicities \(r,s\) has frequency
[
\Omega_{r,s}=r\omega_+ + s(-\bar\omega_+).
]
For \(x\ne0\), exact same-sector conversion \(\Omega_{r,s}=\omega_-\) is equivalent to
[
s=r+1,qquad (r+1)y=rD.
]
At any Xi divisor, \(0<y<1/2\), while BM \(D_n=2n+3/2\ge3/2\). If \(r=0\), equation forces \(y=0\); if \(r\ge1\), it forces \(y\ge D/2\ge3/4\). Both contradict strip bounds.

## Consequence
No finite stationary local Einstein--Teukolsky vertex built only from one positive BM QNM and its real-field partner can drive opposite QNM branch in same Xi sector. Existing AIME inverse-Jost expression remains a valid meromorphic pole/residue, but its interpretation as physical single-seed branch conversion lacks Fourier-support incidence. Actual branch return requires at least one of:
- another spectral/angular sector,
- continuum or nonmodal memory,
- explicitly time-dependent background/vertex.

This is physical non-diagonal-support necessity, distinct from corpus tautological principal-sector-moment mixing.

## Formalization
Created:
`formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTeukolskySingleSectorFrequencyNoGo.lean`

Main declarations:
- `d4SingleSectorMonomialFrequency_eq_minus_iff`
- `d4SingleSectorMonomialFrequency_ne_minus_of_strip`
- `d4BMSingleSectorMonomialOutputFrequency_ne_qnmMinus_xi`

Added import to `formal/GaloisForLFunctions/RHTower.lean`.

Verification:
- direct targeted Lean compile passed;
- new declarations' `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`;
- lint task-local reachability fixed; global lint still fails on two unrelated pre-existing unreachable modules:
  `DeningerMeyerHalfDensityFiniteXiJetVerticalDefect`,
  `HTGeometry.SecondOrderConstraintDescent`.

No git used. Scratch files deleted.

## Further candidate
Horizon shear transfer on thermally normalized branch frequencies yields an absorption-asymmetry formula proportional to \(\Im z=1/2-\Re\rho\). Do not formalize until physically deriving branch-dependent half-shift from regular Teukolsky horizon variables; raw BM frequencies instead center equality at strip boundary, so declared de-aliasing is insufficient.