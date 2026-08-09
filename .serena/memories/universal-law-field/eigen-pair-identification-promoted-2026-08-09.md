# ULF-INV-10 promoted: eigen-pair prime identification — 2026-08-09 (Claude)

Card: `2-fully-proven/universal-law-field/eigen-pair-prime-identification-derivation.md`
(moved from stage 1 after D1-D8 closed). [NO LEAN yet — certification is the FIRST priority of
the next Lean-enabled session.]

## The theorem (paper-proved)

For every pair of Xi zeros alpha, beta: the eigen-pair's own absolutely convergent prime+Gamma
expression equals the antidiagonal Hermitian Gram value. Hence the corpus's unconditional
"eigen-span positivity <=> RH + simplicity" holds in genuine PRIME-SUM form: the identification
gate of the Weil-polarization lane (the corpus's recorded "what is left") is closed at paper
level for the decisive class.

## Proof architecture (for the Lean plan)

Rectangle contour of (XiC'/XiC)·F_alpha·(sharp F_beta):
- Residue side COLLAPSES: F_alpha(rho) = -XiC(rho)/(alpha+rho) = 0 off the own fiber; the sum
  IS the single antidiagonal Gram term; multiple zeros degenerate (order-(m-1) vanishing of the
  quotient) exactly matching the simplicity clause.
- Prime side: logDeriv_completed_split + termwise Lambda-series integration (Parseval to
  time-side pair values at ±log n) + arch part; boundaries die by
  exists_norm_xiThetaEigenFourier_horizontal_le.
- Double-pole (matched partner) case = diagonal norm via l'Hopital of the D1 Wronskian
  reduction; coherence appeared three independent times.
- Convergence inputs, all certified: pair decay rate 2-(|Im a|+|Im b|) > 1; theta source has
  ZERO-MEAN seed (computed: 2π[2π·3/(8π²) − 3/(4π)] = 0) => super-exponential decay both ends
  by Poisson; substrip quotient decay (18a-family).

## Pinned conventions (all read in source, no repairs needed)

- Transform: ∫ u(x) e^{−izx} dx (`hedenalmThetaEigenTransform`).
- XiC z = xi(1/2 + zI); XiC_even.
- Quotient: xiThetaEigenFourier = I·dslope XiC alpha; F_alpha(z) = −XiC(z)/(z+alpha).
- Sharp: xiWeilSharp F z = conj(F(conj z)); polarization = Σ'_{XiZeroCopy} F·sharpG
  (multiplicity-exact copies = residue multiplicities).
- Source: thetaCuspSeed = 2π(2πt⁴−3t²)e^{−πt²}, zeroth moment exactly 0; k transform = XiC.

## Verdicts recorded

- ULF-INV-9 wall-grade suspicion: DEAD on the decisive class (frozen conjecture falsified — as
  the loop intends). Survives at most on the broad algebra (optional, lower value).
- The corpus gate-layer note "identifying the continuous limit with an actual prime sum is what
  is left" — discharged for the decisive class.

## Remaining live surface of the inverse theory

1. N8's involution (the group-3 boundary itself — the original problem, fully specified).
2. Lean certification of this card (first Lean session priority).
3. Optional: broad-algebra half of INV-9; bridge-grade two-axis map; calibration deepening.
