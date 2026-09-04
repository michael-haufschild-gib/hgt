# Constrained (pole-vanishing) Weil form — working log

Route-specific working log for the restricted / pole-vanishing Weil positivity programme
(`CCMRestrictedWeilPolar*` modules, ground energy `μ₀`, degeneracy threshold, numerics in
`2-fully-proven/computations/weil-polar-ground-energy/`).  Moved here on 2026-09-04 from
`universal-law-field/STATUS.md`, which records only what the solution object MUST / CANNOT be.
Labels `Fnnn` / `MUST-nnn` are historical ledger numbers; `MUST-nnn` here are route tasks or
route-level facts, not constraints on the object.

---

## 2026-09-03 (viii–ix) — constrained Weil continuity and ground energy
F403/MUST-141 — Lean: a positive constrained Weil Rayleigh floor persists on a right aperture
neighborhood, including prime entries. The remaining quantitative input is Connes–Consani's
pole-vanishing Sonin inequality at `√2`.
F404/F405 — Lean: nonzero pole-vanishing smooth interior sources exist and are dense; ground energy
`μ₀` is antitone and continuous, and strict positivity is open.
MUST-142 — `WEIL-ENTRY-001` is Lean-closed modulo published numerical certificate
`μ₀(√2)>0` (margin about `0.3%`); qualitative prime-2 crossing is formal, quantitative crossing is
that one external number.
## 2026-09-03 (x) — degeneracy threshold of the pole-vanishing Weil form
F406 — Lean (`RHTower.CCMRestrictedWeilPolarGroundState`): the pole-vanishing ground energy is
attained; either it is positive at every aperture or it vanishes at a unique threshold with an
attained normalized pole-vanishing null vector and nonnegativity on the pole-vanishing subspace.
MUST-143 — Failure of Weil positivity on the pole-vanishing subspace, if it happens, is a
degenerate threshold `a*` with an attained null vector; prime entries cannot cause it
discontinuously; given Connes–Consani, `a* > (log 2)/2`. The remaining links to RH itself
(RH ⇒ no threshold by zero density; no threshold ⇒ RH by the `s(s−1)` multiplier) are paper-level.
## 2026-09-03 (xi) — pole-vanishing multiplier; RH-link status
F407 — Lean (`RHTower.CCMRestrictedWeilPolarMultiplier`): `∫ e^{sx} g'' = s² ∫ e^{sx} g` for smooth
compactly supported `g`; the operator `∂² − 1/4` sends every strict-interior source to a
pole-vanishing one (`isPolarConstrained_polarMultiplier`). The pole-vanishing smooth core is the
image of `∂² − 1/4` (converse on paper via the Green kernel `−e^{−|x|/2}`).
MUST-144 — The link `μ₀ > 0 everywhere ⇒ RH` is Bombieri–Yoshida's pole-vanishing Weil criterion;
the corpus cannot currently formalize it (two-bump localization is not pole-vanishing; the
explicit formula stops at the resolvent algebra). It is a known theorem, so it is recorded, not
pursued. The archimedean form alone is indefinite on the pole-vanishing subspace at large
apertures (Fourier mass near `|ξ| = 1/2` where `θ′ < 0`), so primes are necessary there.
- **Nugget:** the pole-vanishing subspace is the range of `∂² − 1/4`, the operator with Mellin
  symbol `s(s−1)`; Weil's pole terms and the two pole constraints are the same two-dimensional
  space seen from the test side and the zero side.
## 2026-09-03 (xii) — numerical study of the pole-vanishing Weil form
F408 — Computation (RunPod, report in `2-fully-proven/computations/weil-polar-ground-energy/`):
`μ₀(√2) = 0.54704` with second eigenvalue 0.84; `μ₀(a) > 0` at every aperture tested, converged
through `λ ≈ 2.1` and decaying super-exponentially after; archimedean-only positivity on the
pole-vanishing subspace ends at `λ_arch = 1.81451`; each prime power becomes necessary within
0.01–0.02 of aperture after its entry. Upper-bound numerics with convergence control, not
interval-certified.
MUST-145 — Numerically the constrained input of Theorem D holds with an order-one margin, and no
degeneracy threshold exists below `λ ≈ 5`; the analytic wall is unchanged (a Galerkin minimum is
an upper bound, so positivity is evidence, negativity is proof). New quantitative facts: the
archimedean threshold `λ_arch = 1.8145` and the immediate necessity of each entering prime.
F409 — Computation: the pole-vanishing ground state's Fourier zeros converge to the zeta
ordinates (eight zeros to `10⁻³` by `a = 0.9`), like the full ground state of Connes–Consani–
Moscovici; the spectral realization does not depend on the pole terms.

## 2026-09-04 — three deliverables opened (card `weil-polar-bombieri-yoshida-prime-two-entry.md`)
WP-T1 (BY): pole-vanishing ground energy ≥ 0 at all apertures ⇒ RH, via a discrete multiplier
`M(γ) = (e^{iγh}−1)(e^{iγh}−e^{h/2})(e^{iγh}−e^{−h/2})` acting by translates, the twisted ray energy, and a
weighted Widder–Landau engine (plan in the card).
WP-T2 (P2): analytic prime-2 entry — Connes–Consani's computer-checked step (115) to be replaced; explicit range.
WP-T3 (GM): Guth–Maynard-type large-values theorem in Lean.
