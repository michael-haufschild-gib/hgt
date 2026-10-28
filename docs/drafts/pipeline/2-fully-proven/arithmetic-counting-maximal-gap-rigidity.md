# The maximal prime gap does not select the untwisted multiplicative source

- **ID:** ACP-MAXIMAL-GAP
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** arithmetic-counting-positivity.md; arithmetic-counting-pole-angle.md
- **Statement:** For every prime `p ≥ 11` the single-prime flip `ω_p(n) = (−1)^{v_p(n)}` has
  hyperplane gap exactly `2 log 2`. The maximal selective margin is attained by infinitely many
  nontrivial completely multiplicative sign twins of `ζ`, none of which is Weil-positive.

## Goal

`isGreatest_signGauge_hyperplaneGap` shows no sign gauge has a hyperplane gap above `2 log 2`,
and `ζ` attains it. The squared-angle bound gives prime flips gaps `(2 log 2)((p−1)/(p+1))²`
only. The open question was whether the **maximal** gap is rigid among multiplicative gauges.
It is not: for `p ≥ 11` the flipped sector of the prime form has first excitation
`log p · (1 + 1/p)`, far above `2 log 2`, and the rotation of the pole inside that sector costs
less than the excess. Consequence for the frontier: the exact discrete margin, even with complete
multiplicativity and the untwisted polar matching, is not the missing continuous selection
mechanism. Any transfer must read more of the source than the hyperplane gap.

## Gates

- [x] 0 → 1: explicit arithmetic source and quantitative question.
- [x] 1 → 2: dependency-closed paper proof (below). `[PROVED HERE]`
- [ ] 2 → 3: Lean theorem `primeFlip_hasHyperplaneGap_two_mul_log_two` in
  `ArithmeticCountingPositivity/LargePrimeFlipsAttainTheMaximalGap.lean`; axiom audit.

## Objects (all in the corpus)

Pole gauge `y_n = √n x_n`; `D_N(x) = Σ_{mt≤N} Λ(t)(x_{mt} − x_m/√t)²`; harmonic mass
`H_N = Σ_{n≤N} 1/n`; signed count `S_N = Σ_{n≤N} ω_p(n)/n`; `c_p = (p−1)/(p+1)`, so
`S_N ≥ c_p H_N` (`primeFlip_harmonicCorrelation_ge`). Two-scale data for a prime cutoff `Q > p`
and a horizon `X`: `Q`-smooth parts `a`, rough fibres `R(Q, N/a)` of harmonic mass `R_a`,
`G = R(Q, N/X) ≤ R_a ≤ F = R(Q, N)` for `a ≤ X`, `F − G ≤ 1 + log X` (thin shells); fibre means
`h_a`; smooth mean `c` of `h` on `a ≤ X` with weights `1/a`; `V = Σ_{a≤X}(1/a)(h_a − c)²`;
`g = zeroExt(h)` on the box `B = smoothBox X Q` (a product of `p`-ladders of full length
`X + 1`), with `Σ_{a∈B}(1/a) g(a) = 0`; `W = Σ_{n≤N}(1/n)(y_n − c)²`; `D_S`, `D_L` the walk
energies of primes `< Q` and `≥ Q`, `D_N = D_S + D_L`.

## Proof

**Reduction.** By `eventually_atomicWeilForm_add_poleDefect_le`, `P_N(ω_p x) ≤ (log N − γ +
ε₁)|x|² − (1 − ε₁) D_N(ω_p x)`, so it suffices to prove the **twisted Poincaré inequality**: for
every `η > 0`, eventually in `N`, every `z` with `Σ_n ω_p(n) z_n/√n = 0` satisfies
`D_N(z) ≥ (2 log 2 − η)|z|²`. (Apply it to `z = ω_p x`; `ω_p² = 1`.)

**Step 1 (twisted Efron–Stein on the box).** `boxVar ≤ boxGlauber = Σ_q Σ_u Var_q(u)`
(`boxVar_le_boxGlauber`) and each ladder pays its variance with constant `log q · W_q(X) ≥ boxGap`
(`boxLadderVar_le`, `boxGap_le_ladder`). Keeping the `p`-ladders separate:
`boxEnergy(g) ≥ boxGap · boxVar(g) + (log p · W_p(X) − boxGap) · V_p(g)`, where
`V_p(g) = Σ_{u∈B, p∤u} Var_p(u)` is the within-`p`-fibre variance and `W_p(X) = Σ_{i≤X} p^{−i}
∈ [1 + 1/p, p/(p−1)]`. Also `V_p(g) ≤ Σ_{a∈B}(1/a) g(a)² = V`.

**Step 2 (the flipped pole lives in the `p`-sector).** Fibre the box over `p`:
`B = ⊔_{u∈B, p∤u} {u p^i : i ≤ X}`, `ω_p(u p^i) = (−1)^i`. Since `Σ_{a∈B}(1/a) g(a) = 0`, for
any constant `κ`: `⟨ω_p, g⟩_B := Σ_{a∈B}(1/a) ω_p(a) g(a) = Σ_u (1/u) Σ_i p^{−i}((−1)^i − κ)
(g(u p^i) − m_u)`, with `m_u` the ladder mean. Two Cauchy–Schwarz inequalities (on each ladder,
then over `u ≤ X`, the only `u` with nonzero ladder variance since `g` vanishes above `X`) give
`⟨ω_p, g⟩_B² ≤ [(1+κ²)W_p − 2κ σ_p] · Z_X · V_p(g)`, `σ_p = Σ_{i≤X}(−1/p)^i`,
`Z_X = Σ_{a≤X smooth} 1/a ≤ 1 + log X`. With `κ = c_p`, the geometric sums give `σ_p ≥ c_p W_p`,
hence `⟨ω_p, g⟩_B² ≤ (1 − c_p²) W_p Z_X V_p(g)`.

**Step 3 (two scales with the extra term).** From Step 1 and `smoothVar ≤ boxVar`,
`smoothVar_mul_le_of_box` applied with the constant `boxGap + Z₀/V` (`Z₀ = (log p·W_p −
boxGap)V_p(g)`, convention `Z₀/0 = 0`) yields, for `X` large, `E_X(h) ≥ g₁ V + Z` with
`g₁ = 2 log 2 − ε/2` and `Z = Z₀/(1 + e₂)`, `e₂ = 16 L_Q/log X`. Then `two_scale_le` with
`g₁' = g₁ + Z/V ≤ 2 log 2 + 2 log p` and `le_of_two_scale` with `T = g₁' + ε/2` (parameters
`τ, Q, X, N` chosen for `T_max = 2 log 2 + 2 log p`) give `(g₁' − ε/2) W ≤ D_N`. Since
`W ≥ Σ_{a≤X}(1/a) R_a (h_a − c)² ≥ G V`, this is
`D_N(z) ≥ (2 log 2 − ε) W + G Z`.

**Step 4 (the mean).** `|z|² = W + H_N m² − H_N(m − c)² ≤ W + H_N m²` with `m` the harmonic mean
of `y`. Fibring the constraint over the smooth parts (`ω_p(ab) = ω_p(a)` for rough `b`):
`c S_N = −A`, `A = Σ_{a≤N}(ω_p(a)/a) R_a (h_a − c) = G⟨ω_p, g⟩_B + A_var + A_halo`, and
`H_N(m − c) = B = B_var + B_halo` (the `G`-part of `B` vanishes by definition of `c`). Bounds:
`A_var², B_var² ≤ (1 + log X)³ V ≤ (1 + log X)³ W/G`;
`A_halo², B_halo² ≤ H_N · (2 D_S + 2 M_Q W)/log X` (Jensen on each fibre above `X`, then
`sum_log_mul_fibre_le`). With `S_N ≥ c_p H_N`:
`H_N m² ≤ (1+κ)² G² ⟨ω_p,g⟩_B²/(c_p² H_N) + C₁[(1+log X)³ W/(G H_N) + (2D_S + 2M_Q W)/log X]`.

**Step 5 (the arithmetic condition).** By Step 2 and `G Z_X ≤ H_N`,
`(2 log 2)(1+κ)² G²⟨ω_p,g⟩_B²/(c_p² H_N) ≤ (2 log 2)(1+κ)²(1 − c_p²) W_p G V_p(g)/c_p²`, while
`(1 − δ) G Z ≥ (1 − δ) G W_p (log p − 2 log 2) V_p(g)/(1 + e₂)` (`boxGap ≤ 2 log 2 ≤ 2 log 2 · W_p`).
So the main term is paid once
`(2 log 2)(1+κ)²(1+e₂)(1 − c_p²) ≤ (1 − δ) c_p² (log p − 2 log 2)`, i.e.
`4p (2 log 2)(1+κ)²(1+e₂) ≤ (1 − δ)(p − 1)²(log p − 2 log 2)`.
For `p ≥ 11`, `log p ≥ log 11 ≥ 3 log 2 + 3/11 > 2.35`, and with `κ = δ = e₂ = 1/20` the
left side is at most `6.44 p` while the right side is at least `0.91 (p − 1)² ≥ 6.44 p`.
The error terms are at most `(η/2) W + δ D_S` once `log X` and then `G` are large.

**Step 6 (assembly).** `(2 log 2 − η)|z|² ≤ (2 log 2 − η/2) W + (1 − δ) G Z + δ D_S ≤
(1 − δ)[(2 log 2 − ε) W + G Z] + δ D_S ≤ (1 − δ) D_N + δ D_N = D_N` with `ε = η/4` and
`δ ≤ η/(8 log 2)`. ∎

## Consequences

- With `isGreatest_signGauge_hyperplaneGap`: `IsGreatest {g | HasHyperplaneGap ω_p g} (2 log 2)`
  for every prime `p ≥ 11`.
- With `finiteFlip_matching` and `primeFlip_not_weilPositiveFull`: a completely multiplicative
  sign gauge with the untwisted polar matching, the maximal hyperplane gap, every Weil coefficient
  of the same size as `Λ`, and a negative complete Weil test. The gap, multiplicativity and polar
  matching do not identify `ζ`; selection must read the signed source beyond the pole hyperplane.
- The primes `p < 11` are not decided by this argument: the crude secular bound
  `c_p² (log p(1+1/p) − 2 log 2) ≥ 2 log 2 (1 − c_p²)` fails there.

## Log
- 2026-10-28 — paper proof completed; Lean formalization started.
