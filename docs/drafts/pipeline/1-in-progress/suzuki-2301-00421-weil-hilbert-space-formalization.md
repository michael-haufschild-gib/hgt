# Suzuki, *On the Hilbert space derived from the Weil distribution* (arXiv:2301.00421v3) — full Lean formalization

- **ID:** suzuki-2301-weil-hilbert
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:2301.00421v3 (2025-11-07; TeX source `screwzse_11.tex`, 2393 lines; incorporates arXiv:2209.04658)
- **Statement:** Formalize unconditionally and closed in Lean every lemma/theorem/proposition of the
  source that is not already owned by mathlib or this corpus.

## Goal

Close the whole source paper in Lean.  RH-conditional source statements keep RH as the source's own
hypothesis (never a new hypothesis added by us); everything else is unconditional.

## Source inventory (TeX labels → paper numbering)

| TeX label | Paper | Statement | RH? | Lean status |
|---|---|---|---|---|
| `thm_1_1` | Thm 1.1 | `K(Θ_ξ) → H_W`, `F ↦ [F⁻¹F]`, is a Hilbert isomorphism with `‖E F‖²_{H(E)} = ‖F‖²_{K(Θ)} = π⟨ψ_F,ψ_F⟩_W` | yes | OPEN |
| `prop_101` | Prop 1.2 | `𝔖_t ∈ L²(ℝ)` for every fixed `t ∈ ℝ` | no | OPEN |
| `prop_102` | Prop 1.3 | `𝒫̂_φ ∈ L²(ℝ)` for `φ ∈ C_c^∞(ℝ)` | no | OPEN |
| `thm_1_2` | Thm 1.4 | RH ⟺ `‖𝒫̂_{Dψ}‖²_{L²} = π⟨ψ,ψ⟩_W` for all `ψ ∈ C_c^∞`; countably many `ψ` suffice | ⟺ | OPEN |
| `cor_1_1` | Cor 1.5 | RH ⟺ `2‖ψ‖²_{L²} = ⟨ψ,ψ⟩_W` for all `ψ ∈ V°(0)` | ⟺ | OPEN |
| `prop_301` | Prop 3.1 | `𝔓_t(z) = P_t(z)` (prime--arch formula equals the Xi-zero series) | no | **IN PROGRESS** — zero-side Laplace transform CLOSED (`integral_suzukiPtZeroSum_laplace`); `𝔓`-side in progress |
| `lem_301` | Lem 3.2 | `‖ψ‖₀ := π^{-1/2}‖𝒫̂_{Dψ}‖_{L²}` is a norm on `C_c^∞(ℝ)` | no | OPEN |
| `prop_401` | Prop 4.1 | `{F_γ}` is an orthonormal basis of `K(Θ)`; `Θ'(γ)/2 = -i/m_γ`; `F_γ(γ)=1/√(m_γ π)`, `F_γ(γ')=0` | yes | OPEN (cited to Su23 Prop 3.2) |
| `thm_4_1` | Thm 4.2 | `t ↦ π^{-1/2}𝔖_t` is a screw line of `g_ξ`: `π⁻¹⟨𝔖_t,𝔖_u⟩ = G_g(t,u)` | yes | OPEN |
| `cor_401` | Cor 4.3 | RH ⟺ `(2π)⁻¹‖𝔖_t‖² = -g(t)` for all `t ≥ t₀`, some `t₀ ≥ 0` | ⟺ | OPEN |
| `thm_4_2` | Thm 4.4 | RH ⟺ `‖𝒫̂_φ‖² = π⟨φ,φ⟩_{G_g}` for all `φ ∈ C_c^∞` with `φ̂(0)=0` | ⟺ | OPEN |
| `thm_4_3` | Thm 4.5 | RH ⟺ `‖ψ‖₀² = ⟨ψ,ψ⟩_W` for all `ψ ∈ C_c^∞` | ⟺ | OPEN |
| `cor_4_2` | Cor 4.6 | RH holds if `‖g_n‖₀² = ⟨g_n,g_n⟩_W` for all Bombieri--Lagarias `g_n` | ⟸ | OPEN |
| `lem_5_1` | Lem 5.1 | `K(Θ) = F(V(0))`, `H(E) = E·F(V(0))`, `V(0) = L²(0,∞) ∩ K L²(0,∞)` | yes | OPEN |
| `rmk_5_2` | Rmk 5.2 | `V(0) = {0}` would falsify RH; `K`-eigenvector reduction | yes | OPEN |
| `lem_5_2` | Lem 5.3 | `V(0) ≅ L²(τ)` by `ψ ↦ (ψ̂(γ))_γ`, `2‖ψ‖² = ‖S_ψ‖²` | yes | OPEN |
| `lem_5_3` | Lem 5.4 | `H_W ≅ L²(τ)` by `[ψ] ↦ S_ψ`, `⟨ψ,ψ⟩_W = ‖S_ψ‖²` | yes | OPEN |
| `thm_5_1` | Thm 5.5 | Refined Thm 1.1: (1) the four-fold norm identity on `V(0)`; (2) the composite map | yes | OPEN |
| `thm_5_2` | Thm 5.6 | `H_0 = H_W`, `K_0 = K(Θ)`; `𝒫̂_D` inverts Thm 5.5(2); `V(0) = closure V°(0)` | yes | OPEN |
| `thm_5_3` | Thm 5.7 | `E·F(V(t))` is a de Branges subspace of `H(E)` for all `t ≥ 0`, isomorphic to `H_W(t)` | yes | OPEN |
| `prop_5_1` | Prop 5.8 | RH ⟺ (1) `‖ψ‖² = ½⟨ψ,ψ⟩_W` on `V(0)` and (2) the peaked-test condition | ⟺ | OPEN |
| §6 | — | `(H_W, A_{W,π/2})` is a Hilbert--Pólya space; eigenvalue multiplicity one | yes | OPEN |
| §7 (unnumbered) | Thm 7.1 | UNCONDITIONAL: `𝔓_t(0) = -g_ξ(t)` and `lim_{y→∞}[y𝔓_t(-iy) - ½ψ(¼+y/2) + ½log π] = -g_ξ'(t)` for `t ≠ log n` | no | **(7.1) CLOSED** `RHTower.tendsto_suzukiFrakP_zero`; (7.2) open |
| `thm_4` | — | inside `\comment{...}` in the source: NOT a paper statement.  Excluded. | — | N/A |

## Corpus dictionary (checked with `scripts/formal_tools.py research`)

- `A(z) = ξ(1/2 - iz) = XiC z` (functional equation `ξ(s)=ξ(1-s)`).  `XiC` is `XiEntireReal.lean`.
- `E_ξ = XiC + I·XiC' = xiHedenmalmDeBrangesE` (`XiHedenmalmDeBrangesSeam.lean`); its
  `E^♯ = xiHedenmalmDeBrangesESharp`.  Verified: `ξ'(1/2-iz) = i·XiC'(z)`.
- `g_ξ` of eq. (4.3) is the corpus's `screwFn screwLinearCoeff screwLerchConst` on `t ≥ 0`, i.e.
  `g_ξ = -suzukiPsi` and `(g_ξ t : ℂ) = -xiScrewDivisor t` unconditionally
  (`SuzukiExplicitScrewZeroSeries.lean`).
- `Γ` with multiplicity is the corpus's `XiZeroCopy` / `xiSpectralPoint`;
  `xiSpectralPoint_inv_sq_summable` gives `∑ m_γ|γ|^{-2} < ∞`.
- Resolvent-class explicit formula: `xiGuinandWeilExplicitFormula` (regularized Cauchy kernels).
- Rectangular explicit formula: `xiWeilPolarization_rectangular_eq_prime_add_arch`.
- Su22 Lemma 2.1 (exponential-type uniqueness on Xi zeros): `SuzukiTitchmarshUniqueness.lean`.
- Lerch blocks: `screwLerchTail`, `screwLerchTail₁`, `screwLerchTail₂`, `lerchExp k = 2k + 1/2`,
  with `screwLerchTail t = ¼ e^{-t/2}Φ(e^{-2t},2,¼)` and
  `screwLerchTail₁ t = -½ e^{-t/2}Φ(e^{-2t},1,¼)`.
- Screw derivative: `hasDerivAt_screwFn_of_affine`, `screwFnDeriv`, `hasDerivAt_screwLerchTail`.

## Layer plan

1. **L1 — objects.**  `suzukiLerchDiff`, `suzukiFrakP` (eq. 1.6), `suzukiFrakS` (eq. 1.5),
   `suzukiPtZeroSum` (eq. 3.2), `suzukiGXi` (eq. 4.3) and the bridge `suzukiGXi = -suzukiPsi`.
2. **L2 — §7 appendix theorem** (unconditional; no explicit formula needed).
3. **L3 — Prop 3.1** (`𝔓_t = P_t`); the genuine explicit-formula content of the paper.
4. **L4 — Prop 1.2/1.3** (`L²` membership + Minkowski).  Needs `ζ'/ζ` strip bound and
   `N(T+1)-N(T) = O(log T)`.
5. **L5 — Lem 3.2** (norm).
6. **L6 — Hardy/model/de Branges layer**: `H²(ℂ₊)`, `K(Θ)`, `H(E)`, the isometric involution `K`,
   `V(t)`.  Mathlib has none of this; build it.
7. **L7 — RH-conditional main theorems** (Prop 4.1, Thm 4.2, Cor 4.3, Thm 4.4/4.5, Cor 4.6,
   Lem 5.1/5.3/5.4, Thm 5.5/5.6/5.7, Prop 5.8, Thm 1.1/1.4/1.5, §6).

## Source defects found

- Eq. (7.2)'s proof prints `(d/dt)(e^{-t/2}Φ(e^{-2t},2,¼)) = -2e^{-t/2}Φ(e^{-2t},2,¼)`.  The correct
  identity is `= -2 e^{-t/2}Φ(e^{-2t},1,¼)` (second Lerch slot drops from `2` to `1`).  With the
  printed version the theorem is false; with the corrected version eq. (7.2) is exactly right.
- Eq. (7.2) writes `𝔅_t` for `𝔓_t` (typographic).

## Landed Lean

| Module | Content |
|---|---|
| `RHTower/SuzukiWeilLerchBlock.lean` | `suzukiLerchDiff` / `suzukiLerchKernel` (the regularized `Φ(e^{-2t},1,w) - Φ(e^{-2t},1,1/4)` of eq. (1.6)), its factorization `= (1/4-w)·kernel`, `suzukiLerchKernel t (1/4) = 4e^{t/2}·screwLerchTail t`, the Gauss bridge `ψ(w)-ψ(1/4) = -suzukiLerchDiff 0 w`, and continuity of the kernel at `1/4`. |
| `RHTower/SuzukiWeilZeroSeries.lean` | `suzukiPtZeroTerm` / `suzukiPtZeroSum` (eq. 3.2), summability, `‖P_t(z)‖ ≪_z e^{|t|/2}`, per-copy Laplace transform, and **`integral_suzukiPtZeroSum_laplace`**.  Also `XiC_neg` (evenness of the centered completed Xi source), which the corpus did not have. |
| `RHTower/SuzukiWeilFrakP.lean` | `suzukiFrakP` (eq. 1.6) and `suzukiFrakPReg`; `suzukiScrewG_eq_screwFn`; `riemannZeta_half_ne_zero`; `logDeriv_riemannZeta_half : ζ'/ζ(1/2) = -screwLinearCoeff/2`; `continuousAt_logDeriv_riemannZeta_half`; **`tendsto_suzukiFrakP_zero`** (eq. 7.1). |

All capstones audited: only `propext, Classical.choice, Quot.sound`.

## Anti-duplication audit (2026-08-22)

Checked with `scripts/formal_tools.py research` before and after writing:

- `g_ξ` of eq. (4.3) **already exists** as `RHTower.suzukiScrewG` (`SuzukiScrewFunctionCriterion.lean`).
  A private `suzukiGXi` was written and then **deleted**; the corpus object is used instead.
- `ζ(1/2) ≠ 0` reuses `riemannZeta_real_strip_ne_zero` (`ZetaRealStrip.lean`) instead of a new proof.
- the shifted `p`-series reuses `summable_one_div_nat_add_one_rpow` (`ZetaRealBound.lean`).
- the explicit affine slope of `screwPrimeSum` on an atom-free window is
  `screwPrimeSum_eq_checkpoint_affine` with `suzukiCheckpointMass` (`SuzukiCheckpointEventDynamics.lean`);
  do not re-derive it.
- `𝔓_t`, `𝔖_t`, `P_t`, and the complex-parameter Lerch difference are genuinely absent from the corpus
  (confirmed by grep for `frakP`/`𝔓` and by the standing parity card).

## Open core of eq. (7.2)

The printed limit is over a function whose *printed formula* has removable poles at
`y ∈ {1/2 + 2m : m ∈ ℕ}` (trivial zeros of `ζ(1/2-y)` and poles of `ψ(1/4-y/2)` and of the Lerch
block).  Away from them the Lean expression is the true value; at them it is Lean junk.  Reflection
(`logDeriv_riemannZeta_add_reflect_off_poles`) plus the Gauss bridge reduces the whole singular part
to the single object

```text
W_t(y) = e^{-yt} (ζ'/ζ)(1/2-y) - (1/2) e^{-t/2} suzukiLerchDiff t (1/4-y/2)   →   -screwLerchTail₁ t,
```

whose two poles cancel exactly (residues `-e^{-y_m t}/(y-y_m)` and `+e^{-y_m t}/(y-y_m)`).  Plan:
state the limit along `atTop ⊓ 𝓟 {y | ∀ m, 1/4 ≤ |y - (1/2+2m)|}` (cofinal, non-vacuous), where the
Lerch block has the uniform majorant `9 e^{-2nt}` and dominated convergence applies, and where
`|ψ(1/4-y/2)| = O(y log y)` gives `e^{-yt}·(ζ'/ζ)(1/2-y) → 0`.  The `-g_ξ'(t)` side is
`hasDerivAt_screwFn_of_affine` fed by `screwPrimeSum_eq_checkpoint_affine`.

## Proof route for Proposition 3.1 (chosen, partly executed)

Suzuki proves (3.1) by applying Weil's explicit formula to the non-smooth, non-compactly-supported
test function `φ_{z,t}`.  The corpus has no explicit formula for that class.  **Instead** we prove
(3.1) by matching *Laplace transforms in `t`*, which reduces everything to the corpus's already-owned
regularized-Cauchy explicit formula `xiRelativeResolventTrace = continuedPrimeArchSourceRelativeTrace`:

```text
∫_0^∞ P_t(z) e^{-σt} dt = (T(-iσ) - T(-z)) / (σ (iσ - z)),           σ > 1/2,     [DONE]
∫_0^∞ 𝔓_t(z) e^{-σt} dt = same,                                                    [IN PROGRESS]
```

The `P`-side proof: termwise Laplace `1/(σ(γ-iσ)(γ-z))`, reindex the divisor by
`xiZeroCopyReflectEquiv` (this is what moves both base points `-iσ`, `-z` into the corpus's
admissible half-plane), then partial fractions.  The `𝔓`-side proof splits eq. (1.6) into five
blocks (`suzukiFrakPPolar/Zeta/Prime/Digamma/Lerch`) whose Laplace transforms are, with
`s_σ = 1/2+σ`, `s_z = 1/2-iz`, `A = logDeriv archFactor`:

```text
polar          →  [1/s_σ + 1/(s_σ-1) - 1/s_z - 1/(s_z-1)] / (σ(σ+iz))
zeta           →  -(ζ'/ζ)(s_z) / (σ(σ+iz))
prime          →  +(ζ'/ζ)(s_σ) / (σ(σ+iz))
digamma+Lerch  →  [ψ(s_σ/2) - ψ(s_z/2)] / (2σ(σ+iz))
```

and their sum is `[ζ'/ζ(s_σ) + A(s_σ) - ζ'/ζ(s_z) - A(s_z)]/(σ(σ+iz))`, which is exactly
`(T(-iσ)-T(-z))/(σ(iσ-z))` because `T(w) = I·(ζ'/ζ + A)(1/2+wI)` and `iσ - z = i(σ+iz)`.
(The digamma+Lerch collapse uses the two partial fractions `1/((n+w)(n+a)) = (a-w)^{-1}[...]`,
`a = 1/4+σ/2`, and the corpus's `digamma_sub_eq_tsum`.)

Endgame: Laplace determinacy.  With `σ = m + N₀` and the substitution `u = e^{-t}` the vanishing of
`∫_0^∞ (𝔓_t - P_t)e^{-σt}dt` becomes vanishing of all polynomial moments of a bounded function
supported in `[0,1]`, so `RHTower.ae_eq_zero_of_moments_eq_zero` (`ExpDecayFourierAnalytic.lean`)
applies.  Continuity of both sides in `t` then upgrades a.e. to pointwise.

## Log
- 2026-08-22 — created; source inventoried statement by statement; corpus dictionary established.
- 2026-08-22 — L3 started: the Xi-zero-series Laplace transform is closed; the five-block split of eq. (1.6) and the polar/zeta/digamma Laplace transforms are closed.
- 2026-08-22 — L1 (Lerch block) and eq. (7.1) closed in Lean; two sign typos in the printed proof of
  (7.1) recorded; anti-duplication audit run and one duplicate (`suzukiGXi`) removed.
