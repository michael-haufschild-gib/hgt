# MSC complete-minimal singular realization

- **ID:** msc-complete-minimal-singular-realization
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md`, route MSC
- **Statement:** For `1/2 < Re ρ` and `σ > 1`, exact physical MSC source/overlap columns admit an infinite-dimensional complete minimal positive-Hilbert realization; if `Re ρ ≤ 1`, every such realization is non-Bessel.

## Goal

Kill positivity, infinite dimension, completeness, and minimality as possible MSC rigidity inputs. Combined with the formal Bessel wall, this isolates finite analysis stability as exact remaining Hilbert obstruction. Full RH chain: any MSC proof must derive Bessel/frame stability from Hedenmalm's source geometry; complete-minimal positive completion alone is compatible with a hypothetical strict-right zero.

## Gates

- [x] 0 → 1  in-progress: source-pure statement, explicit construction, route consequence
- [x] 1 → 2  fully-proven: dependency-closed paper proof and novelty audit
- [x] 2 → 3  formalized: Lean theorem, targeted build, axioms audit
- [ ] 3 → 4  publication-ready

## Construction and proof

Write
`a_n = infiniteMobiusCriticalComplexDampedSignedWeight σ (mscPhysicalZeroCoordinate ρ σ) n`,
`b_n = infiniteMobiusSignedWeight σ n`, and `P_n = |a_n||b_n|`.
Corpus identity gives
`P_n = squarefreeMobiusMass (Re ρ) n / squarefreeMobiusTotal σ`.
Hence `0 ≤ P_n ≤ 1`, and `P_n → 0` along every cofinal squarefree sequence, because `Re ρ > 0`.

Let `q_k` enumerate odd primes and `r_k = 2q_k`. These are disjoint injective squarefree sequences. Put `A = range q`, `B = range r`. Define a positive mode norm

`t_n = |a_n|⁻¹` on `A`, `t_n = |b_n|` on `B`, `t_n = sqrt (|b_n|/|a_n|)` on other squarefree indices, and `t_n = 1` otherwise.

In `H = ℓ²(Fin 2 ⊕ ℕ)`, let `e₀,e₁` be head coordinates and `f_n` the private tail coordinate. Set

`c_n = a_n t_n / 2`, `d_n = b_n / (2t_n)`,
`s_n = sqrt(1-|c_n|²-|d_n|²)`,
`u_n = c_n e₀ + d_n e₁ + s_n f_n`, and `m_n = t_n u_n`.

On `A`, `|c_n|=1/2` and `|d_n|=P_n/2`; on `B` the roles reverse; elsewhere both equal `sqrt(P_n)/2` or vanish. Thus `s_n² ≥ 1/2`, `‖u_n‖=1`, and `m_n≠0`. With source `2e₀` and overlap `2e₁`, conjugate-linearity in the first variable gives exactly
`⟪u_n,source⟫ = star(a_n)t_n` and `⟪u_n,overlap⟫ = star(b_n)/t_n`.

Minimality: `s_n⁻¹ f_n` is biorthogonal to `u_n`; private tail coordinates give the Kronecker law.

Completeness: if `z ⟂ u_n` for all `n`, restrict the equation to `q_k`. Tail coordinates of an `ℓ²` vector tend to zero along the injective private-tail sequence, while `|c_{q_k}|=1/2` and `|d_{q_k}|=P_{q_k}/2→0`; hence `z(e₀)=0`. Restriction to `r_k` similarly gives `z(e₁)=0`. The original equations then give `s_n z(f_n)=0`; since `s_n>0`, every tail coordinate vanishes. Therefore `z=0`, so the system is complete.

If `Re ρ≤1`, `exists_besselViolation_of_re_le_one` applies to this exact realization, so it violates every finite Bessel bound.

## Novelty audit

- Corpus has the MSC coefficient product invariant, exact Bessel wall, and generic complete/minimal-system theory, but no exact non-Bessel MSC completion.
- Prokofyev, arXiv:2505.15321, uses finite-head plus private-tail systems for defect classification; it does not prescribe the two MSC analysis columns or prove the arithmetic stability wall.
- Olevskii, arXiv:2008.12877, proves completion by small perturbations; it does not preserve prescribed MSC coefficients.
- Hedenmalm, arXiv:2606.17494, supplies the spectral pair motivating MSC but not this completion/classification.

## Lean certificate

- Module: `RHTower/Hedenmalm/HedenmalmGammaSewnSquarefreeFisherCompleteMinimalSingularRealization.lean`
- Main theorem: `strictRightXiZero_mscCompleteMinimalSingularRouteKill`
- Build: targeted module PASS
- Axioms: `propext`, `Classical.choice`, `Quot.sound`
