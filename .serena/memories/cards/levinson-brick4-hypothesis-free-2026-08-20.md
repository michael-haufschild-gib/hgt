# Levinson brick 4 is hypothesis-free (2026-08-20)

Card: `docs/drafts/pipeline/1-in-progress/levinson-critical-proportion-programme.md`.

## State

Levinson's counting step is now unconditional Lean with **no** standing hypothesis. The whole
method is reduced to one analytic quantity: `N_{G♯}([½,4]×[T₁,T₂])`, the zero count of
`G♯ = (s−1)²(ζ + λζ′)` in the closed box.

Final capstones (`RHTower/LevinsonAdmissibleWindow.lean`):
- `exists_levinson_admissible_window`
- `exists_levinson_admissible_window_singleton`

```text
∃ c > 0, ∀ λ < 0 with |λ| ≤ 1, ∀ 20 ≤ a₁ < b₁ ≤ a₂ < b₂,
  ∃ T₁ ∈ (a₁,b₁), ∃ T₂ ∈ (a₂,b₂), ∀ n,
    (n+2)π + π + (T₂−T₁)(6/T₁²) + c log T₁ + c log T₂ + 2π·N_{G♯} ≤ θ(T₂) − θ(T₁)
    ⟹ n ≤ xiOddFiberCount T₂  and  H₁(T₂) ≥ (3/2)n − N(T₂)/2.
```

All axiom-clean (`propext, Classical.choice, Quot.sound`).

## The mathematical points that made it work

1. **`G = ζ + λζ′` vanishes on the critical line exactly at the multiple zeros of `ζ`.**
   `Y·Z = 2 Re[e^{iθ}G]` with `Y ≠ 0` forces `ζ(½+iτ) = 0`, then `λ ≠ 0` forces `ζ′(½+iτ) = 0`.
   There `ord G = ord ζ − 1`.

2. **No indented contour is needed.** Factor `G♯ = Q·H` with `Q` the node polynomial of the
   critical-line zeros. Then
   - `Re (Q′/Q)(½+iτ) = 0` (singular part `m/(i(τ−τ_j))` is purely imaginary), so the left-edge
     integrals of `G♯` and `H` coincide;
   - each node contributes exactly `π` to `(right)+(bottom)−(top)` — the three integrals are
     `arctan(q/a)+arctan(p/a)`, `arctan(a/p)`, `−arctan(a/q)` with `a = d−½`, `p = τ_j−T₁`,
     `q = T₂−τ_j`, and `arctan u + arctan u⁻¹ = π/2` collapses them;
   - removing the nodes lowers the box count by exactly `M = Σ m_j`.
   Net: `∫_left Re(G♯′/G♯) = (three edges) − 2π N_closed + π M`, the indented-contour identity with
   no indentation and no limits.

3. **The `π M` surplus pays the counting loss exactly.** On the line
   `Q(½+iτ) = i^M ∏(τ−τ_j)^{m_j}`, so `Z = P·ρ·cos φ` with `P` real. Each sign change of `P` can
   spoil at most one step of the sign chain *provided the chain nodes avoid the `τ_j`*. They can:
   the chain is built from first hitting times of levels `c₀ + iπ` and `φ(g_i) = c₀ + iπ` exactly,
   so a node lands on a prescribed point only for finitely many base levels; one extra half-turn
   buys a good `c₀`. Loss `≤ M`, paid by the `π M` surplus. Net cost: `(n+1)π → (n+2)π`.

4. **The pole factor `(s−1)^{-2}` is handled by the reflected quadratic** `conj(s−1)²` inside the
   polar carrier: `1/w² = conj(w)²/normSq(w)²`, the scalar is real and positive, and the phase
   velocity of the reflected factor is `(¼+τ²)^{-1} > 0`, so the correction only helps. This keeps
   the carrier a product of entire objects (no quotient, no `logDeriv` of a quotient).

## New reusable modules

- `HTGeometry/PhaseSignChainAvoid.lean` — sign chains at an arbitrary base level with `cos c₀ ≠ 0`;
  `exists_avoiding_level`; `exists_sign_chain_avoiding` (nodes off a prescribed finite set).
- `HTGeometry/RectangleBoundaryPole.lean` — `simplePole_three_edge_variation = π`.
- `HTGeometry/RectangleNodeProductVariation.lean` — `logDeriv_nodeProduct`,
  `nodeProduct_three_edge_variation = π·Σ m_j`.
- `HTGeometry/EntireMultiplicityFactor.lean` — `exists_entire_multiplicity_factor` (exact
  prescribed multiplicities at finitely many points, cofactor nonvanishing at every node),
  `analyticAt_multiplicityFactor`, `multiplicityFactor_ne_zero`,
  `analyticOrderAt_eq_of_factor_ne_zero`.
- `RHTower/HardySignSubchainCount.lean` — `le_xiOddFiberCount_of_sign_subchain`,
  `le_xiOddFiberCount_add_card_of_factored_advance`.
- `RHTower/LevinsonLineZeroFactorization.lean`, `RHTower/LevinsonFactoredPolar.lean`,
  `RHTower/LevinsonWindowUnconditional.lean`, `RHTower/LevinsonWindowEdgeUnconditional.lean`,
  `RHTower/LevinsonAdmissibleWindow.lean`.

## Concurrency note

Another Claude session owns the AFE / mollified-second-moment side of this card (brick 5:
`SmoothAFEZetaGeneral*`, `SmoothAFEZetaGeneralEdge`, twisted mean value). Do not touch
`SmoothAFEZeta*` while that lane is live.

## Lean traps hit

- `HasDerivAt.pow` on `ℝ → ℂ` produces a Pi-form with a different `Module ℝ ℂ` instance path
  (`instInnerProductSpaceRealComplex.toModule` vs `NormedAlgebra.toNormedSpace.toModule`) and does
  not unify. Write `f * f` and use `HasDerivAt.mul` instead of `.pow 2`.
- `Complex.continuous_re.comp_continuousOn` yields `re ∘ f`; finish with
  `simpa [Function.comp_def]`. Same for `ContinuousOn.div` which yields `f / g` in Pi form —
  `simpa [Pi.div_def]`.
- `Finset.card_sdiff` in this toolchain has no subset hypothesis and states
  `(s \ t).card = s.card − (t ∩ s).card`; use `card_union_le` on `range n ⊆ good ∪ bad` instead.
