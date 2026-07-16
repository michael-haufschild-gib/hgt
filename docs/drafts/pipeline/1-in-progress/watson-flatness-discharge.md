# Watson flatness for half-argument digamma jets — unconditional discharge

- **ID:** watson-flatness-discharge
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → THEOREM (Lean) target
- **Source:** `formal/GaloisForLFunctions/HTGeometry/QuantitativeHolderInterface.lean:240` (`WatsonFlatness`)
- **Statement:** For every `n`, every `P : MvPolynomial (Fin (n+2)) ℂ`, and every `c > 0`: if
  `σ ↦ halfDigammaJetEval n P σ = O(e^{−cσ})` on the real ray at `+∞`, then the evaluation is
  eventually zero on the ray.

## Goal
`WatsonFlatness` is the single named analytic input separating `QuantitativeHolder` (QH) from
Hölder's theorem; `quantitativeHolder_of_watsonFlatness` is already formalized.  Discharging it
makes QH an unconditional theorem of the tree; the ξ-hypertranscendence chain
(`xi_hypertranscendental_of_quantitativeHolder`) then remains conditional only on
`XiFrequencyCollapse`.

## Gates
- [x] 0 → 1  in-progress: well-posed; complete proof plan below; all classical inputs identified
      as existing mathlib/in-tree lemmas
- [ ] 1 → 2  fully-proven: paper proof written out (the plan below is the proof; write prose)
- [ ] 2 → 3  formalized: Lean theorem `watsonFlatness : WatsonFlatness`, lint green
- [ ] 3 → 4  publication-ready

## Approach — Phragmén–Lindelöf bootstrap (complete plan, verified against tree+mathlib)

Write `F z = halfDigammaJetEval n P z`; it is analytic off the pole lattice `−2ℕ`
(`analyticAt_halfDigammaJetEval`, in-tree).  Set `G₀ ζ := F (1 + ζ)`; then `G₀` is analytic on
the closed sector `Σ_α = {|arg ζ| ≤ α}`, `α := 3π/4` (the shift `1 + ζ` avoids all poles since
`|arg(1+ζ)| ≤ |arg ζ|`).  Fixed constants: `θ₀ := π/8`, `β := 9π/16`, `κ := 9/8 = β/(π/2)`.

**A. Sector growth (module `DigammaSectorBounds`).**
`‖G₀ ζ‖ ≤ C_P (1+‖ζ‖)^{N_P}` on `Σ_α`.  Ingredients, all present:
- arg-free sector: work with `{w | ‖w‖·cos β ≤ w.re}`; key algebraic inequality
  `‖w + t‖² = ‖w‖² + t² + 2t·Re w ≥ cos²(β/2)(‖w‖+t)²` for `Re w ≥ ‖w‖ cos β`, `t ≥ 0`
  (pure `nlinarith` algebra, no `arg`).
- order-0 bound: Gauss series `tsum_gaussDigammaSeriesTerm_eq_digamma_add_euler_of_offPoles`
  (in-tree, everywhere off poles) + termwise `|1/(n+1) − 1/(s+n)| = |s−1|/((n+1)|s+n|)`
  + sector inequality ⟹ `‖ψ(w)‖ ≤ C(δ)(1 + ‖w‖)` on the sector.
- order-`j+1` bound: shift law `HTGeometry.iteratedDeriv_digamma_add_nat` (in-tree) +
  shift-limit `iteratedDeriv_digamma_add_nat_tendsto` (in-tree, all `z`) ⟹
  `ψ^{(j+1)}(w) = (−1)^{j}·j!·(−1)·∑_{n≥0} (w+n)^{−(j+2)}` (tsum via tendsto uniqueness);
  sector inequality ⟹ `‖ψ^{(j+1)}(w)‖ ≤ C_j(δ)` on sector minus small ball.
- assemble over monomials of `P` (`MvPolynomial` induction as in
  `analyticAt_halfDigammaJetEval`).

**B. One PL step per half-sector (mathlib `PhragmenLindelof.horizontal_strip` via `exp` chart —
no cpow here).**  On the strip `{0 < im η < α}` set
`h(η) := G₀(exp η) · exp((c/2)·e^{−iθ₀}·exp η)`.
- boundary `im = 0`: `‖h‖ ≤ C·e^{−c e^x}·e^{(c/2)cosθ₀·e^x} ≤ C'` (uses the O-hypothesis for
  large real argument + compactness bound on the initial segment);
- boundary `im = α`: multiplier modulus `e^{(c/2)e^x cos(α−θ₀)}`, `cos(5π/8) < 0`, kills the
  polynomial growth from A;
- growth: `‖h‖ ≤ A·exp(B·exp(1·|re η|))`, and `1 < π/α = 4/3` — strip lemma applies.
⟹ `‖G₀ ζ‖ ≤ C·exp(−(c/2)(cosθ₀·Re ζ + sinθ₀·Im ζ))` for `arg ζ ∈ [0, α]`.
Mirror strip `{−α < im η < 0}` with multiplier `e^{+iθ₀}` for the lower half.
Since `cos(argζ ∓ θ₀) ≥ cos(β−θ₀) = sin(π/16) > 0` for `|arg ζ| ≤ β`:
**uniform exponential decay** `‖G₀ ζ‖ ≤ C e^{−c₄‖ζ‖}`, `c₄ = (c/2)sin(π/16)`, on `|arg ζ| ≤ β`.

**C. Widening + endgame (mathlib
`PhragmenLindelof.eq_zero_on_right_half_plane_of_superexponential_decay`).**
`W(w) := G₀(w^κ)` (`Complex.cpow`, principal branch) on `{Re w ≥ 0}`: maps into `|arg| ≤ β`,
so `‖W w‖ ≤ C e^{−c₄‖w‖^{9/8}}` — superexponential on `ℝ⁺` (`SuperpolynomialDecay atTop expR`),
bounded on `iℝ`, bounded growth, `DiffContOnCl` (continuity at `0` from `‖w^κ‖ = ‖w‖^κ`).
⟹ `W ≡ 0` on `{Re ≥ 0}` ⟹ `G₀(t) = 0` for all real `t ≥ 0` (via `x ↦ x^{8/9}` surjectivity
and `Complex.ofReal_cpow`) ⟹ `∀ᶠ σ, halfDigammaJetEval n P σ = 0`.  ∎

Then bank `quantitativeHolder : QuantitativeHolder :=
quantitativeHolder_of_watsonFlatness watsonFlatness` and re-express downstream users.

## Status of ingredients
- mathlib: `PhragmenLindelof.horizontal_strip`, `eq_zero_on_right_half_plane_of_superexponential_decay`
  (both verified present in `.lake/packages/mathlib/Mathlib/Analysis/Complex/PhragmenLindelof.lean`),
  `Complex.digamma` + `digamma_apply_add_one`.
- in-tree: `analyticAt_halfDigammaJetEval`, `halfDigamma_jet_annihilator_eq_zero_of_ray`,
  Gauss series off poles, polygamma shift law + shift-limit, all-orders vertical bounds.
- to build: modules `HTGeometry/DigammaSectorBounds.lean` (A) and
  `HTGeometry/WatsonFlatnessDischarge.lean` (B+C).

## Log
- 2026-07-16 — created directly in 1-in-progress with complete verified plan; build started.
