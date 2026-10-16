# CHMD: the spectrum of the arithmetic resolvent above 1/2 is pure point, locally finite, finitely degenerate

- **ID:** chmd-pure-point-above-threshold-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CHMD route; direct continuation of chmd-no-weyl-above-threshold-2026-10-16 (MUST-1548: no weakly null Weyl sequences above `1/2`)
- **Statement:** Let `R` be the bounded arithmetic resolvent on `L²(Θcosh(x/2)dx)`. For `μ > 1/2`: `μ ∈ σ(R)` iff `μ` is an eigenvalue; every unit approximate-eigenvector sequence at `μ` has a subsequence converging weakly to a genuine eigenvector; every eigenspace above `1/2` is finite-dimensional; for every `ε > 0` the set of eigenvalues in `[1/2 + ε, 1]` is finite. Also: Weyl's criterion for symmetric bounded operators on real Hilbert spaces (generic, reusable).
- **Status:** STATUS MUST-1551. One leaf (`CHMDPurePointAboveThreshold`, 11 declarations), axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audit clean; `lake build --old` green; wired into `GaloisForLFunctions/RHTower.lean`; index refreshed; global lint clean of proof debt (remaining errors are other agents' unwired modules).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `exists_approx_eigen_of_mem_spectrum`, `exists_eigenvector_of_approx_eigen_above_half`, `mem_spectrum_iff_hasEigenvalue_above_half`, `finite_eigenvalues_above`, `finiteDimensional_eigenspace_above_half`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
MUST-1548 excluded weakly null Weyl sequences above `1/2`. To turn this into a statement about the
spectrum one needs (a) that spectral points carry approximate eigenvectors at all (Weyl's criterion,
absent from mathlib for bounded selfadjoint operators), and (b) weak compactness to produce an actual
eigenvector. Both are now in Lean, so the CHMD image of off-line zeros is a genuine discrete point
spectrum: bound states of finite degeneracy, finitely many above each `1/2 + ε`, accumulating only at
the essential threshold `1/2` (which is attained by the cusp escape, MUST-1546).

## Paper proof
*Weyl's criterion.* Let `T` be symmetric bounded on a real Hilbert space and `μ ∈ σ(T)`. If no unit
sequence has `‖(T−μ)w_n‖ → 0` then `T − μ` is bounded below by some `m > 0` (otherwise normalize the
witnesses of `‖(T−μ)x‖ < ‖x‖/(n+1)`). A symmetric operator `S` bounded below is injective and has
closed range (antilipschitz on a complete space); if `y ⊥ range S` then `⟪S(Sy), y⟫ = ⟪Sy, Sy⟫ = 0`,
so `Sy = 0`, `y = 0`; the range is dense and closed, hence everything; `S` is bijective, a unit, and
`μ ∉ σ(T)`.

*Eigenvectors.* For unit `w_n` with `‖(R−μ)w_n‖ → 0`, `μ > 1/2`: `L²(μ)` is second countable, so a
subsequence `w_{φ n}` converges weakly to some `x` (corpus `exists_real_weak_subseq`). If `x = 0`,
the subsequence is a weakly null unit Weyl sequence at `μ`, excluded by MUST-1548. For every `k`,
`⟪Rx − μx, k⟫ = lim (⟪Rw_{φn}, k⟫ − μ⟪w_{φn}, k⟫) = lim ⟪(R−μ)w_{φn}, k⟫ = 0` (`R` symmetric), so
`Rx = μx`.

*Local finiteness.* Eigenvalues of `R` lie in `[0,1]` (`‖R‖ ≤ 1`). If infinitely many eigenvalues
`μ_k ≥ 1/2+ε` existed, choose unit eigenvectors `x_k`; distinct eigenvalues of a symmetric operator
have orthogonal eigenspaces, so `(x_k)` is orthonormal; a subsequence `μ_{φk} → μ* ∈ [1/2+ε, 1]`;
`‖(R − μ*)x_{φk}‖ = |μ_{φk} − μ*| → 0` and `(x_{φk})` is weakly null (Bessel), contradicting MUST-1548.

*Finite multiplicity.* The eigenspace `K` is closed, hence a Hilbert space with a Hilbert basis
indexed by `w ⊆ K`. If `w` is infinite it contains an orthonormal `ℕ`-family of eigenvectors,
excluded by MUST-1548; if finite, the span of `w` is finite-dimensional, closed and dense, so `K` is
finite-dimensional.

## Lean module (namespace `RHTower.CHMDPolar`)
`RHTower/CHMDPurePointAboveThreshold.lean` — `isUnit_of_symmetric_of_bounded_below`,
`exists_approx_eigen_of_mem_spectrum` (generic real Hilbert space), `mem_spectrum_of_eigenvector`,
`eigenvalue_le_one`, `exists_eigenvector_of_approx_eigen_above_half`,
`exists_eigenvector_of_mem_spectrum_above_half`, `mem_spectrum_iff_hasEigenvalue_above_half`,
`resolvent_isSymmetric`, `finite_eigenvalues_above`, `isClosed_eigenspace`,
`finiteDimensional_eigenspace_above_half`.

## Big picture
- CHMD spectral picture now complete at the structural level: `σ(R) ⊆ [0,1]`, `σ_ess(R) ⊆ [0,1/2]`
  with `1/2 ∈ σ_ess` (cusp escape), `σ(R) ∩ (1/2,1]` discrete, pure point, finitely degenerate,
  accumulating at most at `1/2`. RH ⟺ (even primitive sector) no spectrum above `1/2`.
- All of this is unconditional and ζ-explicit: harmonic identity + Chebyshev shells (confinement),
  digamma asymptotics (log-Sobolev control), and abstract Hilbert space theory.

## Next conjectures
1. Birman–Schwinger: the eigenvalues of `R` in `(1/2, 1]` with multiplicity correspond to the nonreal
   zero orbits of `Xi` (via the signed divisor pairing / spectral nullspace readouts of the corpus).
2. The even-sector restriction and the exact dictionary "RH ⟺ no eigenvalue of `R|_{even,primitive}`
   above `1/2`" in Lean (the ⇒ direction exists: `weilOperator_isPositive_of_riemannHypothesis`).
3. Quantitative gap: lower bound on the distance from `1/2` of the top eigenvalue in terms of the
   off-line zero's distance from the critical line.
