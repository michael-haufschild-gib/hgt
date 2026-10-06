# Zero-flip rigidity: simple Weil ground states have real Fourier zeros

- **ID:** RW-CVS-ZERO-FLIP (MUST-787)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); general form of Connes–van Suijlekom Theorem 3.1
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/FourierZeroFlipRealZeros.lean`,
  `formal/GaloisForLFunctions/RHTower/WeilGroundStateRealZeros.lean`

## Statement (unconditional)

Let `f` be continuous, supported in `[-L, L]`, `f̂(z) = ∫ f(u)e^{izu}du`, and `f̂(z₀) = 0`. The flip
`h = f + (z₀ − z̄₀)g`, `g(x) = −ie^{−iz₀x}∫_{−L}^x e^{iz₀y}f(y)dy`, is continuous (and `Cⁿ` if `f` is),
supported in `[-L, L]`, and `ĥ(w) = f̂(w)(w − z̄₀)/(w − z₀)` for `w ≠ z₀`.

1. If every admissible function with the same Fourier modulus on `ℝ` as `f₀ ≠ 0` is a multiple of
   `f₀`, every zero of `f̂₀` outside the constraint set `E` is real.
2. For a real symbol `S`, if `∫S|f̂|²/∫|f̂|²` has the single extremal eigenline `ℂf₀`, `f̂₀` is
   real-rooted outside `E`.
3. Restricted Weil form (weights `lam`, atoms `≤ N`, pole-constrained `C²` tests on `[-a, a]`): a
   simple ground state has all transform zeros real except `±i/2`.

## Proof

Integration by parts with `u = ∫_{−L}^x e^{iz₀y}f`, `v = e^{i(w−z₀)x}/(i(w−z₀))`; the boundary term is
`u(L)v(L) = f̂(z₀)v(L) = 0`. Then `|t − z̄₀| = |t − z₀|` on `ℝ`. Rigidity gives `h = cf₀`, so
`f̂₀(t)((t − z̄₀) − c(t − z₀)) = 0` on `ℝ`; the bracket vanishes at most once unless `c = 1` and
`z₀ = z̄₀`; otherwise `f̂₀ = 0` a.e. on `ℝ` and Fourier inversion gives `f₀ = 0`.

## Audit

Leaf builds exit 0; `lake --old env lean` on both modules exit 0; `#print axioms` for all public
theorems: propext, Classical.choice, Quot.sound. Wired into `HTGeometry.lean` (after the CvS toy
modules) and `RHTower.lean` (after `WeilPositivityPrimeBlindDuality`). Lint: no findings in these files.

## Limits

Simplicity of the ground state is a hypothesis. RH needs, in addition, locally uniform convergence of
the normalized ground-state transforms (divided by `w² + ¼`) to a nonzero multiple of `Ξ` along some
apertures `a_k → ∞`; then Hurwitz gives RH. Under ¬RH the ground states at large aperture have
negative energy and their real zeros need not approach the zeta zeros near an off-line zero.
- 2026-10-06 — Simplicity removed (Opus, MUST-788): `HTGeometry/FourierZeroDivisionGroundStates` proves that ground
  states are closed under division by non-real Fourier zeros (`isGround_flipAux`, splitting
  `|f̂|² = |(t−x₀)ĝ|² + y₀²|ĝ|²`), that multiplicity `≤ d` caps the distinct non-real zeros of every ground state below
  `d` (`card_lt_of_isGround`), and that a nonzero real-rooted ground state exists (`exists_isGround_real_zeros`).
  Weil corollaries `card_lt_of_weil_groundState`, `exists_real_rooted_weil_groundState` in `WeilGroundStateRealZeros`.
  Leaf builds exit 0, both `lake --old env lean` audits exit 0 without diagnostics, axioms standard, wired after
  `FourierZeroFlipRealZeros` in HTGeometry.lean.

## MUST-789 — unconditional at every aperture (2026-10-06)

`RHTower.CCMRealRootedGround.exists_realRooted_polarGround` (module
`RHTower/CCMRestrictedWeilRealRootedGroundState`, built, `lake --old env lean` clean, axioms
`propext, Classical.choice, Quot.sound`). On the full CCM form domain at every aperture `a > 0`:
the polar ground subspace is finite-dimensional (`finiteDimensional_groundSubmodule`), and some
nonzero polar ground state has only real transform zeros off `±i/(4π)`. Ingredients: the
Fourier–Laplace division operator `divLaplace` (HTGeometry `FourierLaplaceDivision`), closure of
the form domain under division (`exists_div`), ground-state splitting (`isPolarGround_div`), and
the closed subspace plus compact antilipschitz embedding argument. The `Cⁿ` attainment caveat is
gone. What remains for RH is the localization criterion RW-LOC-HURWITZ (paper).

## MUST-790 — positive quadrature at ground-state zeros (2026-10-06)

`RHTower.CCMGroundQuadrature` (module `RHTower/CCMRestrictedWeilGroundZeroQuadrature`, built, audit
clean, axioms `propext, Classical.choice, Quot.sound`): Euler–Lagrange `excessForm_eq_zero_of_ground`,
zero-quotient orthogonality `excessForm_zeroQuotient_orthogonal`, quadrature `quadrature_le`, and
`exists_realRooted_quadrature` (real-rooted ground state + positive weights on any finite set of its
zeros with `Σρ|ĝ(x)|² ≤ Q(g) − μ_a‖Jg‖²`). `exists_div` was generalized to arbitrary zeros (real
included) via the bound `|ĝ| ≤ |f̂| + C·1_{[x₀−1,x₀+1]}` in the form measure.

## MUST-794 (2026-10-06): even-sector cross-rooted ground states
- Module `RHTower/CCMRestrictedWeilEvenSectorCrossZeros.lean` (namespace `RHTower.CCMEvenSector`; standard axioms; `lake --old build` green; wired after `CCMRestrictedWeilGroundParityCrossing`).
- Statement: at every aperture the even polar ground energy `μᵉ_a` is attained. The even ground level is finite-dimensional, and some even ground state has transform zeros only on `ℝ ∪ iℝ` (off `w_{±1/2}`).
- Literature comparison:
  - Connes–van Suijlekom (CMP 406 (2026) 312, Thm 6.1) assume a simple, isolated, even minimum.
  - Connes (arXiv 2602.04022, §6.6) lists even-simplicity as the first remaining step.
  - Silva (Zenodo, June 2026) reduces even-simplicity to scalar criteria, open in the arithmetic case.
  - With MUST-787–794 the Hurwitz half of their programme needs no simplicity or parity hypothesis. Only the convergence of the even generators to Ξ remains.

## MUST-795 (2026-10-06): source-locked strip receiver
- Module `RHTower/CCMEvenGroundXiStripConvergenceRH.lean` (namespace `RHTower.CCMXiStrip`; standard axioms; `lake --old build` green; wired after `CCMRestrictedWeilEvenSectorCrossZeros`).
- `riemannHypothesis_of_evenGround_strip_convergence`: even ground states with cross-rooted transforms whose normalized transforms converge to `XiC` on `\|Im z\| < ½` give RH.
- Reusable: `zero_mem_closed_of_tendstoLocallyUniformlyOn` (Hurwitz closed-locus transfer on open sets) and `differentiable_unitaryLaplace`.
