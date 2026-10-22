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
`RHTower/CCM/CCMRestrictedWeilRealRootedGroundState`, built, `lake --old env lean` clean, axioms
`propext, Classical.choice, Quot.sound`). On the full CCM form domain at every aperture `a > 0`:
the polar ground subspace is finite-dimensional (`finiteDimensional_groundSubmodule`), and some
nonzero polar ground state has only real transform zeros off `±i/(4π)`. Ingredients: the
Fourier–Laplace division operator `divLaplace` (HTGeometry `FourierLaplaceDivision`), closure of
the form domain under division (`exists_div`), ground-state splitting (`isPolarGround_div`), and
the closed subspace plus compact antilipschitz embedding argument. The `Cⁿ` attainment caveat is
gone. What remains for RH is the localization criterion RW-LOC-HURWITZ (paper).

## MUST-790 — positive quadrature at ground-state zeros (2026-10-06)

`RHTower.CCMGroundQuadrature` (module `RHTower/CCM/CCMRestrictedWeilGroundZeroQuadrature`, built, audit
clean, axioms `propext, Classical.choice, Quot.sound`): Euler–Lagrange `excessForm_eq_zero_of_ground`,
zero-quotient orthogonality `excessForm_zeroQuotient_orthogonal`, quadrature `quadrature_le`, and
`exists_realRooted_quadrature` (real-rooted ground state + positive weights on any finite set of its
zeros with `Σρ|ĝ(x)|² ≤ Q(g) − μ_a‖Jg‖²`). `exists_div` was generalized to arbitrary zeros (real
included) via the bound `|ĝ| ≤ |f̂| + C·1_{[x₀−1,x₀+1]}` in the form measure.

## MUST-794 (2026-10-06): even-sector cross-rooted ground states
- Module `RHTower/CCM/CCMRestrictedWeilEvenSectorCrossZeros.lean` (namespace `RHTower.CCMEvenSector`; standard axioms; `lake --old build` green; wired after `CCMRestrictedWeilGroundParityCrossing`).
- Statement: at every aperture the even polar ground energy `μᵉ_a` is attained. The even ground level is finite-dimensional, and some even ground state has transform zeros only on `ℝ ∪ iℝ` (off `w_{±1/2}`).
- Literature comparison:
  - Connes–van Suijlekom (CMP 406 (2026) 312, Thm 6.1) assume a simple, isolated, even minimum.
  - Connes (arXiv 2602.04022, §6.6) lists even-simplicity as the first remaining step.
  - Silva (Zenodo, June 2026) reduces even-simplicity to scalar criteria, open in the arithmetic case.
  - With MUST-787–794 the Hurwitz half of their programme needs no simplicity or parity hypothesis. Only the convergence of the even generators to Ξ remains.

## MUST-795 (2026-10-06): source-locked strip receiver
- Module `RHTower/CCM/CCMEvenGroundXiStripConvergenceRH.lean` (namespace `RHTower.CCMXiStrip`; standard axioms; `lake --old build` green; wired after `CCMRestrictedWeilEvenSectorCrossZeros`).
- `riemannHypothesis_of_evenGround_strip_convergence`: even ground states with cross-rooted transforms whose normalized transforms converge to `XiC` on `\|Im z\| < ½` give RH.
- Reusable: `zero_mem_closed_of_tendstoLocallyUniformlyOn` (Hurwitz closed-locus transfer on open sets) and `differentiable_unitaryLaplace`.

## MUST-796 (2026-10-06): the polar obstruction and the corrected receiver
- Module `RHTower/CrossRootedPolarZeroXiStripObstruction.lean`. Namespace `RHTower.CCMPolarObstruction`; standard axioms; `lake --old build` green; wired after `CCMEvenGroundXiStripConvergenceRH`.
- `not_tendstoLocallyUniformlyOn_XiC`: even, order-one, cross-rooted `F_n` with `F_n(i/2) = 0` admit no `c_nF_n → XiC` on the strip.
  - Mechanism: `Λ_F(y) = iF'(iy)/(2yF(iy)) = Σ_q 1/(2(a_q²+y²))`, from Hadamard plus the reflection of zero copies.
  - Every term is real and decreasing; the polar pair forces a drop that is unbounded as `y → ½`.
  - Equivalently, `Σ_q a_q⁻⁴ ≥ 16` against Ξ's `σ₄ ≈ 3.7·10⁻⁵`.
- `not_evenGround_strip_convergence`: MUST-795's `riemannHypothesis_of_evenGround_strip_convergence` has jointly unsatisfiable hypotheses (vacuous).
- Corrected receivers:
  - `riemannHypothesis_of_crossRooted_polarQuotient_strip_convergence` and `..._evenGround_polarQuotient_...`: convergence of `c_nG_n(z)/(z²+¼)` to `XiC` on the strip.
  - `riemannHypothesis_of_strip_convergence_of_cross_zeros`: the general form for functions holomorphic on the strip.
- Numerics (`computations/2026-10-06-polar-ground-xi-shape`, a = 0.5–0.8):
  - polar ground states are `(1+4z²)·(Ξ-shaped)`, with `c₄ = −8 + c₄(Ξ)`;
  - the quotient approaches `Ξ/Ξ(0)` with a z²-coefficient deficit `≈ e^{−2a}/(4π²)`.
- Qualification of the MUST-794 literature comparison above:
  - Connes's `k_λ` and the CvS theorem concern the **unconstrained** Weil form `QW_λ`; MUST-794 is about the **polar-constrained** form.
  - MUST-794 therefore removes even-simplicity for the polar analogue, not for Connes's eigenvectors.
  - The CCM route for corpus objects is now: polar even generators (cross-rooted, MUST-794) with `G/(z²+¼) → cΞ` on the strip ⇒ RH [L].
  - For Connes's own objects, an unconstrained analogue of MUST-794 would be needed.

## MUST-797 (2026-10-06): the unconstrained form (Connes's `QW_λ`)
- Module `RHTower/CCM/CCMRestrictedWeilFullFormRealRootedGround.lean`. Namespace `RHTower.CCMFullRealRootedGround`; standard axioms; `lake --old build` green; wired after `CrossRootedPolarZeroXiStripObstruction`.
- `exists_realRooted_fullGround`: at every aperture, some nonzero ground state of the unconstrained form (bottom `ccmRestrictedWeilGroundEnergy`) has only real transform zeros.
- `realRooted_of_finrank_eq_one`: a simple ground level is real-rooted, of either parity.
- `riemannHypothesis_of_fullGround_strip_convergence`: the receiver for Connes's objects.
- New ingredients:
  - `source_eq_integral_add_pole` (frequency form with pole term `2Re(conj f̂(w₋)f̂(w₊))`);
  - `pair_identity` (the flip splits `conj F(w̄)F(w)` at every `w`);
  - `conj_polarPoint`.
- Literature:
  - this removes the simple + isolated + even hypotheses of Connes–van Suijlekom Thm 6.1 for the Weil form;
  - it settles the first "remaining step" of Connes 2602.04022 §6.6 for the Hurwitz argument;
  - it is the continuous analogue of Delsarte–Genin–Kamp.
