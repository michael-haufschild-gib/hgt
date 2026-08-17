# The (σ_p,∂_s) generators are Fourier-diagonal — combination modes (hence C5) are a moment/ring phenomenon, not a generator one

- **ID:** archimedean-generator-axis-mode
- **Stage:** 0-backlog-lean
- **Type:** THEOREM (paper) — Door-2 grade **BRIDGE** (the lemma is elementary); the **payload is structural** (a positive C5 localization)
- **Priority:** FOUNDATIONAL
- **Source:** extends `erosion-cocycle-reducibility.md` (the axis-mode criterion, proved for the σ_p Euler
  observable) to the **archimedean generator** ∂_s; DeWitt #131 (CC / Source-A/B divide), Professor #132
  (FE-cocycle BRIDGE); the combination-mode criterion of `../../door/door-C5-irreducibility-and-door-2-retest.md`;
  the archimedean-generator program #127/#128 (`completed-connection-category.md`); 00-status #59/#111/#127.

---

## Result

On the Bohr Fourier basis `e_m(x) = ∏_p x_p^{m_p}` (`m ∈ ℤ^{(P)}` finite support), **both** generators of
the completed `(σ_p, ∂_s)`-connection act **diagonally** — they multiply each mode by a scalar and never
mix modes:

> `σ_p · e_m = p^{−m_p} · e_m`   (constant multiplier, the prime dilation)
> `∂_s · e_m = −(m·ℓ) · e_m`,   `ℓ = (log p)_p`, `m·ℓ = Σ_p m_p log p`   (the archimedean generator)

Consequently the archimedean generator `∂_s = −Σ_p (log p) θ_p`, **despite being an infinite sum over all
primes, generates no combination modes**: it is a sum of single-coordinate operators `θ_p = x_p ∂_{x_p}`
(`θ_p e_m = m_p e_m`), each touching one prime. Its only non-axis content is the **archimedean digamma**
`∂_s log Γ_ℝ = −½logπ + ½ψ(s/2)` — a single non-decoupling function, but **Source A alone** (no primes).

**The combination modes (`m = m_pδ_p + m_qδ_q + …`, ≥2 primes) — the entire native zone, per the
combination-mode C5 criterion — arise solely from the ring product** `e_m · e_{m'} = e_{m+m'}`, i.e. from
moments / tensor / Rankin–Selberg constructions, **never from the connection generators.**

## Proof
- `x_p = p^{−s}`, so `σ_p : x_p ↦ p^{−1}x_p` gives `σ_p e_m = ∏_{q≠p} x_q^{m_q} (p^{−1}x_p)^{m_p} =
  p^{−m_p} e_m` — diagonal, multiplier `p^{−m_p}`.
- `∂_s x_p = ∂_s p^{−s} = −(log p) p^{−s} = −(log p) x_p`, so `∂_s = −Σ_p (log p) x_p ∂_{x_p} = −Σ_p (log p)
  θ_p`. Then `θ_p e_m = m_p e_m` ⟹ `∂_s e_m = −(Σ_p m_p log p) e_m = −(m·ℓ) e_m` — diagonal.
- Both are diagonal ⟹ the Lie algebra and group they generate act diagonally (a **pro-torus** action; cf.
  pro-torus inverse problem, support-log §43.2). Diagonal operators preserve Fourier support: applied to an
  axis-mode object they return an axis-mode object. They **cannot manufacture** a combination mode.
- A combination mode `e_{m+m'}` with `m, m'` on distinct prime axes is produced **only** by the algebra
  product `e_m · e_{m'}` — the multiplicative/ring structure, absent from the (additive) generator action.
- On the multiplicative diagonal: `∂_s log ζ = ζ'/ζ = −Σ_p (log p) Σ_{k≥1} p^{−ks}` is additive over primes
  (axis-mode), confirming `∂_s` decouples on the ζ-side; the digamma is the lone Source-A residue. ∎

## Door-2 verdict and the positive payload
**BRIDGE** at the lemma level (Fourier diagonalization of a torus action is elementary harmonic analysis on
`𝕋^∞` — a Door-2 parent). The value is the **structural consequence**:

> **The entire connection/generator level is combination-mode-free.** σ_p (already: `erosion-cocycle-reducibility`),
> ∂_s (here), the completed `(σ,∂)`-connection (#127), `FE = flatness`, the curvature (`[∂_s,σ_p]=0`, flat —
> #132), and the holonomy *generator* are all diagonal/axis-mode/Source-A. None can carry a native C5
> theorem, because none has combination-mode content.

So **C5, if it exists, is forced to the ring/moment level or the global holonomy:**
1. **Moment/product positivity** — the Hankel sections `P_{i+j}` (Wheeler's finite-free carrier,
   `finite-free-convolution-flow.md`), `⊗`, Rankin–Selberg, `n`-level correlations: the only objects with
   genuine combination-mode content. *This is where the combination modes live, so this is where C5 lives.*
2. **Global holonomy** (G5, `weil-positivity-operator.md`): the *generator* is diagonal/BRIDGE, but the
   **global monodromy** of the flat completed connection around the σ-fixed circle (RH = unitary holonomy)
   is not a generator-level object — it survives this lemma.

This **closes the archimedean-generator program (#127/#128) as a C5 *source*** at the generator level
(building `𝓜⁺`/`G_L⁺` + FE=flatness is BRIDGE, as those cards already grade their own construction), and
**confirms positively** that the team's two live apex targets — the finite-free Hankel positivity and the
G5 holonomy — are the *only* places a C5 theorem can be earned. A directional certainty, not another dead
end: it permanently removes a large search space (all generator/connection/curvature/cocycle objects).

## `F_q` shadow (Door-5)
Over `F_q(C)` the diagonal generator is the single Frobenius (`u = q^{−s}`), also Fourier-diagonal; the
pro-torus has rank 1 (`corank = 1`, #121). No archimedean digamma residue (no `Γ`), and combination modes
still only from products. Consistent: the generator level is BRIDGE in every border, as expected.

## Gates
- [x] 0 → 1 in-progress: generators' diagonal action stated; ∂_s = −Σ(log p)θ_p axis-mode confirmed.
- [x] 1 → 2 fully-proven: both generators Fourier-diagonal (elementary, above); combination modes = ring
  product only; C5 localized to moment level / global holonomy; `F_q` shadow; Door-2 = BRIDGE/structural.
- [x] 2 → 3 formalized (2026-08-17) — `RHTower/BohrGeneratorAxisMode.lean`; see the Lean
  formalization section at the end of this card.  Earlier partial-anchor note kept for provenance:
  Lean anchors were present for the finite Bohr-character skeleton:
  `bohrCharacter_scaleCoordinate` proves coordinate scaling acts diagonally (`e_m(...,c x_p,...)=c^{m_p}e_m`),
  `bohrCharacter_add` proves ring products add modes (`e_{m+n}=e_m e_n`), `twoAxisMode_support_eq` and
  `bohrCharacter_twoAxis_product` prove the explicit two-axis combination-mode product
  (`../3-formalized/two-axis-bohr-combination-mode.md`), and the Kronecker-frequency theorems in
  `KroneckerFlow.lean` prove the finite `m·ℓ` no-resonance/frequency side. Remaining work:
  package the actual `∂_s` operator on an analytic function space, the infinite torus/generator language,
  and the C5-localization synthesis.
- [ ] 3 → 4 publication-ready: folds into the "where C5 must live" exposition alongside erosion-cocycle.

## Cross-references
- `erosion-cocycle-reducibility.md` — the companion: σ_p Euler observable axis-mode. **Together** the two
  cards clear the full generator set (σ_p + ∂_s).
- `archimedean-prime-cross-term.md` (#132) — FE-cocycle BRIDGE; curvature flat (`[∂_s,σ_p]=0`).
- `multiplier-dichotomy-theorem.md` (#131, DeWitt) — CC/Source-A-B divide; this is its Fourier-side twin.
- `finite-free-convolution-flow.md`, `weil-positivity-operator.md` — the two surviving C5 loci (moment
  positivity / global holonomy) this card points to. **Coordinate; do not duplicate.**
- `completed-connection-category.md` (#127) — its generator-level construction is BRIDGE by this lemma; its
  native content (if any) is the global holonomy.

## Log
- 2026-06-19 — created in 2-fully-proven (Professor). Proved both `(σ_p, ∂_s)` generators are
  Fourier-diagonal (`σ_p e_m = p^{−m_p}e_m`, `∂_s e_m = −(m·ℓ)e_m`); hence the archimedean generator
  `∂_s = −Σ(log p)θ_p`, though an infinite prime sum, generates no combination modes (only the Source-A
  digamma is non-axis). Combination modes (the native C5 zone) are a **ring/moment** phenomenon
  (`e_m·e_{m'}=e_{m+m'}`) only. **Payload:** the entire connection/generator level is combination-mode-free
  ⟹ C5 is forced to the moment-positivity level (finite-free Hankel) or the global holonomy (G5).
  Extends `erosion-cocycle-reducibility` (σ_p) to ∂_s; closes the "∂_s entangles all primes" escape hatch.
- 2026-06-19 — Leaner: added the partial formalized anchor
  `../3-formalized/two-axis-bohr-combination-mode.md`. Lean theorems `twoAxisMode_support_eq` and
  `bohrCharacter_twoAxis_product` prove that multiplying two distinct nonzero axis Bohr modes gives a
  genuine two-axis combination mode. Parent remains in `2-fully-proven`; the analytic `∂_s` operator,
  infinite torus/generator language, digamma residue, and C5-localization synthesis are still paper-level.

## Lean return note — 2026-06-19 (Leaner)

Returned from `2-fully-proven`: the Lean coverage is only the finite Bohr-character skeleton. The ticket's stated content also includes the analytic `∂_s` operator, infinite-torus/generator language, digamma Source-A residue, and C5-localization synthesis. Those are not formalized as one Lean theorem, so moving the whole card to `3-formalized` would repeat the partial-anchor mismatch.

## Triage note — 2026-06-19 (Professor): returned to 2-fully-proven (user-directed; Leaner over-return)

Per @user ("send tickets that are clearly 'leaner is just lazy' back to fully-proven"): Leaner's return was a
**Lean-library-coverage objection** (no formal model of the imported / categorical / analytic objects), **not** a
paper-proof defect. This is a **paper-proven BRIDGE theorem** whose proof legitimately credits classical imports;
those imports are to be carried as hypotheses/axioms (or formalized separately) at the Lean stage — not a reason to
reject the paper proof. The card's stated theorem is proved at its 1→2 gate; any co-located open conjecture
(C5★ / ω=0 / Schanuel / apex) is explicitly a SEPARATE open core, not part of this theorem. Re-banked for Lean re-attempt.

## Lean anchor update — 2026-06-19 (Leaner)

Added the finite-support integer-mode derivative anchor `deriv_archimedeanPrimeMode` in
`formal/GaloisForLFunctions/RHTower/ArchimedeanAxisMode.lean` and created split certificate
`../3-formalized/archimedean-prime-mode-derivative.md`. This formalizes the prime-side finite-mode formula
`d/ds exp(-s(m·ell)) = -(m·ell) exp(-s(m·ell))`. The parent card remains in `2-fully-proven`: the infinite
torus/generator packaging, Gamma/digamma residue, and C5-localization synthesis are not yet formalized as a
single Lean theorem.

## 2026-06-24 axis positivity versus square tests

`axis-positivity-does-not-imply-hankel-positivity.md` records the positivity analogue of the axis/combination split. The generators and coefficient signs live on axis modes; the repair/index condition lives in Hankel or Schur combination modes. A proof of RH-bearing positivity must therefore supply the source transfer between these levels.

## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/RHTower/BohrGeneratorAxisMode.lean`
(wired into the `GaloisForLFunctions.RHTower` umbrella).

The three items the earlier return note listed as missing — "package the actual `∂_s` operator on an
analytic function space, the infinite torus/generator language, and the C5-localization synthesis" —
are now Lean theorems.

**The model.**  `PrimeMode := Nat.Primes →₀ ℤ` is the finite-support integer mode lattice and
`BohrAlgebra := AddMonoidAlgebra ℂ PrimeMode` is the Bohr Fourier algebra, whose ring product is
exactly `e_m · e_{m'} = e_{m+m'}` (`mode_mul`).  A *diagonal Fourier operator* is
`diagOp c : BohrAlgebra →ₗ[ℂ] BohrAlgebra` acting coefficientwise by a multiplier `c : PrimeMode → ℂ`
(`coeff_diagOp`).  `AddMonoidAlgebra.supported ℂ ℂ S` is the submodule of elements with Fourier
support inside `S`; `axisSet = {m | m.support.card ≤ 1}` and
`IsCombinationMode m ↔ 2 ≤ m.support.card`.

| Card step | Lean name |
|---|---|
| `σ_p e_m = p^{−m_p} e_m` | `sigmaOp_mode` |
| `θ_p e_m = m_p e_m` | `thetaOp_mode` |
| `∂_s e_m = −(m·ℓ) e_m` | `dsOp_mode` (using the earlier `deriv_archimedeanPrimeMode`) |
| `∂_s = −Σ_p (log p) θ_p`, finite on every mode | `dsMult_eq_neg_sum`, `dsOp_mode_eq_neg_sum` |
| flat curvature `[∂_s, σ_p] = 0` (and `[θ_p,θ_q]=0`, `[σ_p,θ_q]=0`) | `diagOp_commute`, `sigmaOp_dsOp_commute`, `thetaOp_commute`, `sigmaOp_thetaOp_commute` |
| diagonal operators preserve Fourier support | `diagOp_mem_supported` |
| the whole generated Lie algebra / group is diagonal (pro-torus action) | `generators`, `generatorAlgebra`, `generatorAlgebra_le_diagonal` |
| **they cannot manufacture a combination mode** | `generatorAlgebra_preserves_axisSupported`, `generatorAlgebra_coeff_combinationMode_eq_zero` |
| combination modes come only from the ring product | `twoAxis_product_not_mem_axisSupported`, `support_twoAxis`, `isCombinationMode_twoAxis` |
| **the analytic function space**: `∂_s` really is `deriv` | `bohrEval`, `differentiable_bohrEval`, `deriv_bohrEval` |
| **the infinite torus / generator language**: `σ_p` is precomposition with the coordinate dilation `x_p ↦ p^{-1}x_p` | `torusEval`, `torusEval_sigmaOp`, `sigmaMult_eq_unit` |
| the archimedean Source-A residue `∂_s log Γ_ℝ = −½logπ + ½ψ(s/2)` | `logDeriv_GammaR` (with `logDeriv_cpow_linear`) |
| ζ-side decoupling: every Euler term `p^{-ks}` is an axis mode | `eulerTerm_axisMode`, `axisSet_single` |
| `F_q` shadow: a rank-one lane set has **no** combination modes at all | `rankOne_no_combination_modes` |
| the whole Result as one statement | `generatorLevel_axisMode_law` |

**What the formal statement says.**  `generatorAlgebra` is the unital `ℂ`-subalgebra of
`Module.End ℂ BohrAlgebra` generated by *all* the prime dilations `σ_p`, *all* the single-lane Euler
operators `θ_p`, and the archimedean generator `∂_s`.  `generatorAlgebra_le_diagonal` proves that
every element of it is a diagonal Fourier operator, and
`generatorAlgebra_coeff_combinationMode_eq_zero` proves that for every such `T`, every axis-mode
input `a` and every combination mode `m`, the coefficient `(T a).coeff m` is zero.  That is exactly
the card's payload: *the entire connection/generator level is combination-mode free*.  By contrast
`twoAxis_product_not_mem_axisSupported` exhibits two axis modes on distinct prime lanes whose ring
product leaves the axis submodule.

**Not formalized, and not an obligation of this card.**

1. The Door-2 *verdict* ("C5, if it exists, is forced to the ring/moment level or the global
   holonomy") is a directional claim about where a future theorem can be earned, i.e. about the
   project's search space — it is not a mathematical proposition and has no Lean statement.  Its
   mathematical content is precisely `generatorAlgebra_coeff_combinationMode_eq_zero`, which is
   proved.
2. The identity `∂_s log ζ = −Σ_p (log p) Σ_{k≥1} p^{−ks}` is not re-proved here; the corpus already
   owns it as `RHTower.XiWardInteriorTraceSplit.logDeriv_riemannZeta_eq_neg_LSeries`.  What this
   card *uses* — that each term of that expansion is an axis mode — is `eulerTerm_axisMode`.
3. The `F_q(C)` Door-5 shadow is formalized only in its structural content (a rank-one lane set has
   no combination modes, `rankOne_no_combination_modes`); the statement that the `F_q(C)` pro-torus
   has corank `1` belongs to the separate corank cards.

Verification: `lake build GaloisForLFunctions.RHTower.BohrGeneratorAxisMode` — PASS; `#print axioms`
on all seventeen named results reports only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-08-17 — Formalized unconditionally in Lean 4 and promoted to stage 3.  The Bohr Fourier
  algebra, the diagonal-operator algebra, both generators, the finite `−Σ(log p)θ_p` expansion, flat
  curvature, the analytic `deriv` realization, the infinite-torus dilation realization, the Gamma
  digamma residue and the axis/combination separation are all unconditional Lean theorems.
