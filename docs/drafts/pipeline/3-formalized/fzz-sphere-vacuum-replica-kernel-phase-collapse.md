# FZZ sphere-vacuum replica-kernel phase collapse

- **ID:** FZZ-P-SVRP
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Halder--Jafferis arXiv:2402.00932v3 (3.26), (3.29)--(3.33); `FZZCigarParityMarkedOPEChargeIncidenceNoGo.lean`; `FZZCigarParityGradeHermitianization.lean`
- **Statement:** At every finite neutral screening depth and collision-free sphere configuration, the HJ vacuum replica kernel is positive and its first replica variation is real; its chiral phase is identically zero.

## Goal

Kill `sphere vacuum/area position-kernel phase -> chiral divisor-mode passivity -> Mellin completeness -> RH`.

## Gates

- [x] 0 → 1  source-pure: HJ (3.26), (3.29) explicitly use absolute-value powers; corpus resolves the omitted same-charge increment as `0` and opposite increment as `2k/(k-2)`
- [x] 1 → 2  complete paper proof below; no open dependency
- [x] 2 → 3  `fzzCigarParity_sphereVacuumReplicaKernelPhaseCollapse_noGo`; direct Lean, targeted build, standard-axiom audit; umbrella wired
- [ ] 3 → 4  publication-ready

## Proof `[PROVED HERE]`

Write every collision-free positional factor as `q_i=|d_i|²>0`.  HJ's undeformed and deformed vacuum integrands have only real exponent motions `e_i+δv_i`; the corpus gives `v_i=0` on the marked same-winding block and `v_i=2k/(k-2)` on the opposite block.  Hence

`K(δ)=∏ᵢ q_i^(e_i+δv_i)=exp(∑ᵢ(e_i+δv_i)log q_i)>0`,

and

`K'(δ)=K(δ)∑ᵢv_i log q_i∈ℝ`.

Thus `K-star(K)=0` and likewise for its first replica tangent, pointwise at every depth. Ordinary convergent integration against the real sphere measure cannot restore a chiral phase; meromorphic regularization is outside this claim. Since this phase channel is identically zero both at radial twist `0` and at `i`, no predicate of it can select the Abel/Mellin wall.

## No-go closure

- **Exact killing mechanism:** conjugate Wick factors combine into positive absolute-value powers, and real replica exponent motion preserves the real locus.
- **Strongest positive survivor:** real sign/magnitude after position integration; phase from meromorphic regularization of a divergent integral; external-BRST branch factors; genuine torus/higher-genus prime-form monodromy; higher replica order.
- **New insight:** the position-kernel survivor of neutral coefficient collapse does not survive in the HJ genus-zero vacuum phase channel. FZZ-P must leave the sphere-vacuum first-order phase sector.
- **Novelty audit:** corpus search found no all-depth HJ kernel-phase theorem; targeted literature search through August 2026 found discussion of the absolute-value integrand and external branch cuts, but no phase-selector classification.
- **Lean:** `GaloisForLFunctions.RHTower.FZZCigarParitySphereVacuumReplicaKernelPhaseCollapseNoGo`; targeted build PASS (`8840/8840`); axioms `[propext, Classical.choice, Quot.sound]`; umbrella wired.
