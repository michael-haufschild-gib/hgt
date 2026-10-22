# Theta C5 master-reserved center-velocity seam no-go

- **ID:** C5-VP1-master-reserve-seam-no-go
- **Stage:** 3-formalized
- **Type:** FALSIFIED + THEOREM (Lean)
- **Source:** `../1-in-progress/theta-cusp-c5-center-velocity-likelihood-bregman-cone.md`
- **Statement:** Global nonnegativity of the C5 master-reserved center-velocity core is impossible;
  its smooth positive-ray proxy has a strictly negative fourth modular-seam jet.

## Goal

Kill the sufficient chain

`global master-reserved-core nonnegativity → strict center velocity → center C5 → fixed-action
transport → CLG/TTF or Weil positivity → RH`

and classify the exact source-specific defect that any surviving C5-VP1 argument must cancel.

## Gates

- [x] 0 → 1 in-progress: source-pure seam-jet conjecture and hostile falsifier recorded
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: targeted `lake build` green and axiom audit clean
- [ ] 3 → 4 publication-ready: standalone exposition and external review

## Paper proof

Let `r(t) = exp(q(t)) - 1`, where `q` is the center reflected logarithmic action, and write
`G₂,G₃` for second and third source likelihood jets. Define the two-sided smooth proxy

`M(t) = A(t) + 10 r(t)t²(G₃(t)+6G₂(t))`,

where `A` is the literal center action core. Existing positive-ray likelihood decomposition gives
`M(t) = masterReservedCore(t)` for every `t > 0`.

Reflection makes `r,q₂` even and `q₁,q₃,A` odd. The universal C5 seam algebra gives
`A^(j)(0)=0` for `j<4`; oddness gives `A⁽⁴⁾(0)=0`. Also
`r(0)=r'(0)=0` and `r''(0)=k=q₂(0)>0`. Leibniz therefore yields

`M⁽⁴⁾(0) = 120 k (G₃(0)+6G₂(0))`.

Strict theta likelihood cooling says `6G₂(0) < -G₃(0)`, so this fourth jet is negative. Taylor's
mean remainder theorem gives `M(t)<0` throughout some punctured right neighborhood. Positive-ray
equality transfers the sign to the master-reserved core and contradicts universal nonnegativity.

`[PROVED HERE]`

## No-go closure

- **Exact killing theorem/mechanism:**
  `not_forall_thetaCuspCenterFifthRootVelocityMasterReservedCore_nonneg`; uniform replacement of
  the literal third likelihood channel by six curvature units introduces a negative fourth seam
  jet.
- **Strongest positive survivor:**
  `thetaCuspCenterFifthRootVelocityMasterReservedSeamProxy_seamJetClassification`; all jets below
  four vanish and the exact first defect is `120*k*(G₃+6G₂)`.
- **New insight:** Cubic second-channel cancellation is necessary but insufficient. Any surviving
  reserve must preserve the literal third likelihood channel through fourth order or add the exact
  opposite fourth-jet correction. Uniform six-curvature reserve strategies are eliminated.
- **Status:** Paper proof dependency-closed; Lean formalization unconditional and umbrella-wired.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFifthRootCurvatureVelocityMasterReservedSeamNoGo`
- Direct `lake env lean` check: PASS
- Targeted `lake build` check: PASS
- `#print axioms` for route kill, local negativity, and seam classification:
  `[propext, Classical.choice, Quot.sound]`
- Global lint: new module reachable and contains no forbidden declaration; repository lint remains
  red only for unrelated pre-existing unreachable modules.

## Novelty audit

Internal corpus search found no master-reserved center-velocity seam classification. It contained
the prior cubic cancellation, a different fixed-action adaptive-reserve fifth-order no-go, and the
literal eighth-order C5 opening. Primary-literature search through August 2026 found Planat--Solé's
second-level Riemann Xi-kernel concavity theorem, but no fifth-root velocity, likelihood-reserve
substitution, or fourth-order seam-defect result.

## Log

- 2026-08-29 — conjectured from corpus likelihood decomposition and strict cooling law
- 2026-08-29 — paper proof closed, Lean formalized, branch killed
