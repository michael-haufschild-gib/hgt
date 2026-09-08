# Original Maass component currents after scalar curvature flexibility

- **ID:** SELBERG-ORIGINAL-SOURCE-CURRENTS
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [Selberg conjecturing loop](selberg-quarter-conjecturing-loop.md), cycle 40.
- **Goal:** Recover and test differential constraints of the original congruence component vector that are absent from the scalar family. The full all-congruence quarter bound remains the objective.

## Corpus-derived mechanism

Broad OR discovery over holonomy, monodromy, equipartition, zero means, and signed curvature reached 3212 declarations in 574 modules. Source inspection of `MonodromyVoltageLift` found exact finite permutation lifting and fibre holonomy; `HolonomyCorankDichotomy` concerns sequence recurrence/rank and does not furnish the needed Maass energy estimate. These are discovery counts, not complete source coverage.

A separate OR query for Noether, Wronskians, and current conservation reached 1009 declarations in 211 modules. Inspected `HTGeometry.QNMNoetherFlux`: actual currents obey a full continuity equation, whereas a spatial current alone need not be constant. Inspected `RHTower.ThetaCuspHawkingBMLaplaceWronskian`: two original solutions of the same differential equation give an actual conserved Wronskian after the correct integrating factor. The mechanism to transfer is cancellation from the original shared differential equation, with every current component retained. No QNM mode or radial chamber is being substituted for a Maass source.

The existing `SelbergMaassTraceDirection` supplies permutation-equivariant normalized source directions, amplitude-weighted zero means, and actual direction-energy identities. Direct source search found no Selberg Wronskian/Noether-current theorem under those names. The exact common component eigen-equation must be used, rather than merely the scalar norm equation.

## Conjecture → proof attempt

For actual real and imaginary congruence components U_i of the same original Maass eigenform, define J_ij=U_i*grad(U_j)-U_j*grad(U_i), using actual Frechet derivatives. Conjecture: the planar divergence is identically zero on the upper half-plane because the two source eigen-equations have the same parameter. Derive its full modular permutation/Jacobian transport and its relation to the retained radial/angular energy. All statements must be proved from the original source, including at common zeros when no division is used.

Then test whether integrated currents, their periods, or their constraints at all integral cusps add quantitative information to the original core-plus-cusp quarter form. Conservation by itself must not be promoted to a spectral gap. If a proposed global comparison fails, extract and audit the exact surviving source conservation/energy identity and keep arithmetic or nodal costs explicit.

## Status and next action

The precise source APIs are now inspected: `quotientForm N f q` is itself an original Maass cusp eigenform with the same parameter; its fields `.2.2.1.1` and `.2.2.1.2` carry original C² regularity and the actual eigen-equation. `quotientForm_mul` gives the exact right-quotient permutation under integral pullback. The multiplied `SelbergMaassTraceRadial.density_mul_directionalEnergy` identity holds even at common zeros.

The full complex-pair conservation calculation is written in `/tmp/selberg_source_currents40.lean`, but has not yet been run: the serial cycle-39 final audit currently owns the only task Lean worker. Its paper argument is exact: differentiating F*grad G-G*grad F cancels the two first-derivative products; the remaining F*Delta G-G*Delta F vanishes by the common original potential -lambda/y². Realification or conjugate pairing is still needed to retain phase currents inside an individual complex component. No source file for cycle 40 exists yet.

A further broad OR query for Lagrange identities, wedge energy, Gram determinants, and angular momentum reached 194 declarations in 94 modules. Inspected the exact two-coordinate Gram-defect identity in `HTGeometry/RiemannGaussian/SymmetricPickSchur` and the actual differentiated/integrated bracket in `HTGeometry.SturmLagrangeIdentity`. The proposed next quantitative invariant is the full real-component sum of squared pair currents, related to the multiplied original radial residual without division by amplitude. Its finite-family identity and original-source instantiation remain to be proved.

The inspected two-coordinate identity suggests a more economical complex formulation. For each direction v, write D=sum|F_q|², E_v=sum|d_v F_q|², B_v=sum conjugate(F_q)*d_v F_q, and J_qr,v=F_q*d_v F_r-F_r*d_v F_q. Conjecture the exact finite-family identity

`D*E_v-(Re B_v)^2 = (1/2)*sum_(q,r)|J_qr,v|²+(Im B_v)^2`.

Expanding the pair squares gives the complex Gram defect D*E_v-|B_v|²; the additional imaginary square restores the real radial defect. Thus the pair currents and the total phase current together should capture the original angular residual, including single-component phase variation that pair currents alone miss. The common real eigenvalue should also force divergence of the total phase current to vanish. These are precise paper-proof candidates, not yet Lean results; neither conservation nor the nonnegative decomposition is itself the quarter comparison.

## Regulator forcing must survive the pivot

Inspection of the actual `SelbergMaassAugmentedDirection.source` exposes an additional constraint: its `none` coordinate is the positive constant e, while each `some q` is an original Maass component. The added coordinate does not share the Maass eigenvalue. Hence not every augmented current can be divergence-free. With J=e*grad F-F*grad e, the literal bracket calculation gives div J=-(lambda/y²)*e*F. This source forcing must be retained, rather than extending the common-eigenvalue cancellation to the regulator coordinate. The augmented C² family is the existing mechanism that stays smooth through original nodes.

Next: run the completed complex-pair and finite-wedge scratch after the cycle-39 audit; extend to phase currents, exact modular current transport, the energy identity, and the actual regulator forcing. Do not assume a closed current is exact on a quotient, nor that its periods vanish. The cycle-39 scalar family does not settle this source-sensitive candidate.
