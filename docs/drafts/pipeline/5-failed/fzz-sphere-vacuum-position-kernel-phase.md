# FZZ sphere-vacuum position-kernel phase

- **ID:** FZZ-P-SVPP
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Statement:** The first-order Halder--Jafferis genus-zero vacuum position kernel can retain a chiral phase and drive divisor-mode passivity.

## Goal

Test `sphere vacuum/area position-kernel phase -> chiral divisor-mode passivity -> Mellin completeness -> RH`.

## No-go closure

- **Exact killing theorem/mechanism:** `fzzCigarParity_sphereVacuumReplicaKernelPhaseCollapse_noGo`; HJ (3.26), (3.29) is a finite product of absolute-value powers with real exponent motion. Off collisions it is strictly positive, its exact first variation is real, and its antiunitary-odd phase is zero at every depth.
- **Strongest positive survivor:** real sign/magnitude after position integration; phase from meromorphic regularization of a divergent integral; external-BRST branch factors; torus/higher-genus prime-form monodromy; higher replica order.
- **New insight:** neutral coefficient collapse's generic position-kernel survivor is absent in the literal genus-zero vacuum first-order phase channel. Any FZZ-P phase producer must leave that sector.
- **Status:** paper and Lean closed; targeted build `8840/8840` PASS; umbrella wired; axioms `[propext, Classical.choice, Quot.sound]`.

