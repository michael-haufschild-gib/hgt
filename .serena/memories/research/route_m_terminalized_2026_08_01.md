# Route M terminalization — 2026-08-01

Route M is **FORMALIZED — TERMINALIZED**, not retired/dead and no longer open at reader construction.

Failed predecessor (`SR-49`): cyclic scalar contraction, proper cyclic-algebra/infinite-Krein escape, and multiplicative edge-reader assembly fail. Failed card remains scoped to that class.

Completed survivor (`SR-41`):
- `C_(K,w)=U_w R_K-R_K U_w`, with FE–Schwarz functional calculus `U_w` of completed Euler clock and exact Gamma–Jacobi tail loss `R_K`.
- `Phi_(m;i,j)(A)=(-m_4/m_3) A_ij`.
- Reader is restriction-compatible, completed-Euler covariant, genuinely noncyclic, source-barycentric, and reflection-odd.
- On prime labels it vanishes on marked orientation iff two seam values agree.
- Exact weighted-barycentric normalization is projectivized additive marked current; positive normalization preserves zeros and real signs.
- For every nonempty actual von Mangoldt aperture and every Jacobi aperture, cofinal anchored reader flatness on every Xi-divisor fibre is equivalent to RH.

Interpretation: Route M object, orientation handoff, and connector are closed. No source theorem proves flatness, so RH remains unproved. Any continuation must target an additive-current/cofinal-flatness source theorem as a new route, not another Route M reader wrapper or fictitious co-Poisson continuation.

Lean:
- `formal/GaloisForLFunctions/HTGeometry/FiniteBarycentricReader.lean`
- `formal/GaloisForLFunctions/RHTower/GammaJacobiBarycentricPointedEulerReader.lean`
- wired into `HTGeometry.lean`, `RHTower.lean`, and `RiemannHypothesisSOTA2026.lean`
- direct elaboration and targeted capstone build pass
- axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- full lint has no Route M error; unrelated concurrent unwired modules keep repository-wide lint nonzero

Paper: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/gamma-jacobi-barycentric-pointed-euler-reader.md`.
