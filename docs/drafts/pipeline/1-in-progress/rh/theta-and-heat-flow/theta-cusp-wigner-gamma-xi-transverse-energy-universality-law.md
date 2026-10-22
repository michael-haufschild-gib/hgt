# Theta-cusp Wigner–Gamma–Xi transverse-energy universality law

- **ID:** theta-cusp-wigner-gamma-xi-transverse-energy-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of
  `thetaCuspCenterMixedFourierCurrent_eq_two_mul_re_radialWigner`,
  `thetaCuspShellPairHedenmalmCurrent_eq_gamma`,
  `thetaCuspCenterMixedFourierCurrent_eq_tsum_sourceProductFiber`,
  `hasDerivAt_thetaCuspSourceProductFiberHermitianEnergy`,
  `tsum_thetaCuspSourceProductFiberHermitianEnergy_eq_normSq_XiC`, and
  `hasDerivAt_normSq_XiC_transverse_eq_centerMixedFourierCurrent`
- **Statement:** On the critical aperture, one transverse current has four exact coordinates:
  twice the real radial Wigner current, the cofinal sum of completed-source product-fibre
  currents, the derivatives of the fibre Hermitian energies expressed through reflected
  incomplete-Gamma shell remainders, and the derivative of `‖XiC‖²`. The fibre energies
  themselves sum exactly to `‖XiC‖²`.

## Goal

Close the value/derivative square between the Wigner, incomplete-Gamma, product-fibre, and
completed-Xi coordinates without differentiating an infinite series term by term.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: Lean proof pending
- [ ] 3 → 4 publication-ready: post-proof collision audit pending

## Corpus inputs

- `thetaCuspCenterMixedFourierCurrent_eq_two_mul_re_radialWigner`
- `thetaCuspCenterMixedFourierCurrent_eq_tsum_sourceProductFiber`
- `thetaCuspShellPairHedenmalmCurrent_eq_gamma`
- `hasDerivAt_thetaCuspSourceProductFiberHermitianEnergy`
- `summable_thetaCuspSourceProductFiberHermitianEnergy`
- `tsum_thetaCuspSourceProductFiberHermitianEnergy_eq_normSq_XiC`
- `hasDerivAt_normSq_XiC_transverse_eq_centerMixedFourierCurrent`

## Proof

**[PROVED HERE]** Fix `0 ≤ a < 1/2`, a horizontal coordinate `b`, and
`z = b - ia`. The aperture assumptions imply `|a| < 1`, so every source-shell and product-fibre
identity applies. The Wigner normal-form theorem identifies the actual center-mixed Fourier
current with twice the real radial Wigner integral. The product-fibre reassembly theorem identifies
that same current with the absolutely convergent sum of the completed-source fibre currents.
For each fibre, the Hermitian-energy theorem identifies its current with the transverse derivative
of the finite fibre energy. Each ordered positive shell pair entering that current is, by the
incomplete-Gamma theorem, exactly the reflected Gamma-remainder current. Independently, absolute
summability and cofinal regrouping show that the fibre energies sum to `‖XiC z‖²`; direct
analytic differentiation identifies the derivative of `‖XiC(b-iα)‖²` with the same actual
current. Substituting the Wigner equality gives the direct transverse derivative with Wigner
value. No exchange of an infinite derivative and sum, and no computation, is used. ∎

## Strict gain over corpus endpoints

The Wigner theorem did not identify a completed energy primitive or the incomplete-Gamma
coordinate. The Gamma/fibre theorems did not identify their cofinal current with the radial Wigner
transform. The Xi norm theorem did not expose either microscopic coordinate. This closure gives
one commutative value/derivative law and records explicitly that the infinite derivative is
certified directly, while every finite fibre derivative is certified separately.

## Lean certificate

- Planned module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerGammaXiTransverseEnergyUniversalityLaw`
- Planned main theorem:
  `thetaCusp_completeWignerGammaXiTransverseEnergyUniversality`
- Umbrella:
  wire into `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Deferred until dependency-closed Lean proof.

## Log

- 2026-07-23 — fresh terminal theta scan exposed the Wigner/Gamma/Xi energy square.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
