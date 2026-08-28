# Theta center-mixed rank-four global even closure (2026-08-28)

- Frontier map remained read-only.
- New Lean modules:
  - `formal/GaloisForLFunctions/RHTower/ThetaCuspCenterMixedFourPointEvenGlobal.lean`
  - `formal/GaloisForLFunctions/RHTower/ThetaCuspCenterMixedFourPointFarTail.lean`
  - `formal/GaloisForLFunctions/RHTower/ThetaCuspCenterMixedFourPointOddStationary.lean`
- Core scalar law: for increasing concave equal-step angles `theta1 <= theta2 <= theta3 <= pi/2`, midpoint concavity plus `theta3 <= 3 theta1` implies nonnegativity of the reflection-even four-point cosine wall.
- Applied to each completed theta reflected-source fibre using `concaveOn_thetaCuspReflectedLogCorrelationAngle`, strict source-product antitonicity, and angle subadditivity. Positive matrix-kernel center integration proves `thetaCuspCenterMixedEvenParityWall a t >= 0` for every physical aperture and `t >= 0`.
- Consequence: `thetaCuspCenterMixedGramFourEquispaced_posSemidef_iff_oddParityWall`; global rank-four PSD has only the odd wall left.
- Any failed packet now forces an interior negative stationary odd wall, strict middle-drop dominance `F(t)-F(2t) > F(0)-F(t)`, and dyadic jet constraint `0 <= F'(t)-2F'(2t)`.
- Targeted leaf build passed. Axiom audit: only `propext`, `Classical.choice`, `Quot.sound`. Formal lint's semantic checks passed for these files but repository-wide lint exited on unrelated pre-existing unreachable modules.
- Literature collision search through 2026-08-28 found no exact reflected-source half-angle wall or positive center-mixture rank-four theorem. Closest: Planat–Solé arXiv:2608.19160, a different Laguerre-expression concavity result.
- Next open core: exclude the stationary odd drop/decay certificate using stronger completed-source Riccati/likelihood structure; generic angle concavity is insufficient.