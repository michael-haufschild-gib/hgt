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
| `prop_101` | Prop 1.2 | `𝔖_t ∈ L²(ℝ)` for every fixed `t ∈ ℝ` | no | **CLOSED** `RHTower.memLp_suzukiFrakS` |
| `prop_102` | Prop 1.3 | `𝒫̂_φ ∈ L²(ℝ)` for `φ ∈ C_c^∞(ℝ)` | no | OPEN |
| `thm_1_2` | Thm 1.4 | RH ⟺ `‖𝒫̂_{Dψ}‖²_{L²} = π⟨ψ,ψ⟩_W` for all `ψ ∈ C_c^∞`; countably many `ψ` suffice | ⟺ | OPEN |
| `cor_1_1` | Cor 1.5 | RH ⟺ `2‖ψ‖²_{L²} = ⟨ψ,ψ⟩_W` for all `ψ ∈ V°(0)` | ⟺ | OPEN |
| `prop_301` | Prop 3.1 | `𝔓_t(z) = P_t(z)` (prime--arch formula equals the Xi-zero series) | no | **CLOSED** `RHTower.suzukiFrakP_eq_suzukiPtZeroSum` |
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
| §7 (unnumbered) | Thm 7.1 | UNCONDITIONAL: `𝔓_t(0) = -g_ξ(t)` and `lim_{y→∞}[y𝔓_t(-iy) - ½ψ(¼+y/2) + ½log π] = -g_ξ'(t)` for `t ≠ log n` | no | **CLOSED** `RHTower.tendsto_suzukiFrakP_zero` (7.1) + `RHTower.tendsto_suzukiFrakP_vertical` (7.2) |
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

## Assessment of the two remaining unconditional items

### Eq. (7.2) — EXECUTED (CLOSED)

`E(y) := y𝔓_t(-iy) - ψ(¼+y/2)/2 + ½log π`.  Substituting the reflection formula
(`logDeriv_riemannZeta_add_reflect_of_one_lt_re` at `s = ½+y`) and the *off-poles* Gauss bridge
`ψ(w) = ψ(¼) - suzukiLerchDiff 0 w` regroups `E(y)` into exactly five blocks
(`suzukiVerticalEnergy_eq`), all singular parts cancelling:

```text
  4y(e^{t/2}-1)/(1+2y) + 4y(e^{-t/2}-1)/(1-2y)                          → 2e^{t/2} - 2e^{-t/2}
+ e^{-yt}[log π - ½ψ(¼+y/2) - ζ'/ζ(½+y) - ½ψ(¼)]                       → 0
+ ∑_{n ≤ e^t} Λ(n)n^{-1/2}(e^{-y(t-log n)}-1)                           → -suzukiCheckpointMass ⌊e^t⌋
+ ½ψ(¼) - ½log π + ζ'/ζ(½+y)                                            → screwLinearCoeff/2
+ ½[e^{-yt}·suzukiLerchDiff 0 (¼-y/2) - e^{-t/2}·suzukiLerchDiff t (¼-y/2)]  → -screwLerchTail₁ t
```

and the sum of the five limits is `-g_ξ'(t)` exactly, via `digamma_quarter_sub_logPi`
(`screwLinearCoeff = ψ(¼) - log π`, from reflection at `s = ½`) and `hasDerivAt_screwFn_atomFree`.

Three pieces of genuinely new mathematics were needed.

1. **The Gauss digamma series off the poles** (`SuzukiWeilDigammaOffPoles.lean`).  The corpus's
   `digamma_sub_eq_tsum` and mathlib both stop at `Re w > 0`; the appendix limit needs `ψ(¼-y/2)`
   arbitrarily far to the *left*.  The extension is by a shift law: `suzukiLerchDiff 0 (w+1)
   = suzukiLerchDiff 0 w - w⁻¹` mirrors `ψ(w+1) = ψ(w) + w⁻¹`, so the defect
   `ψ(w) - ψ(¼) + S(w)` is `1`-periodic and vanishes off the poles because it vanishes on the
   half-plane.  A by-product: `summable_suzukiLerchDiffTerm_all` — the series is summable at *every*
   `w`, with no hypothesis at all.
2. **The `y`-uniform dominant** for the fifth block.  Its `n`-th term is
   `(e^{-yt} - e^{-y_n t})·2y/(y_n(y_n-y))`, `y_n = 2n+½`; the apparent pole at `y = y_n` is killed
   by the numerator.  `norm_suzukiVerticalLerchTerm_le` gives the three-regime dominant
   (`y_n ≤ y/2`, `y/2 < y_n < 2y`, `y_n ≥ 2y`), so `tendsto_tsum_of_dominated_convergence` applies.
3. **`ζ'/ζ(σ) → 0` on the real ray** (`tendsto_logDeriv_riemannZeta_ofReal_atTop`), by comparing the
   Dirichlet series of `Λ` at `σ` with its value at `2`.

The limit is taken along `suzukiVerticalFilter = atTop ⊓ 𝓟 {y | ∀ m, ¼ ≤ |y - (2m+½)|}`, because the
*printed* formula (1.6) is Lean junk exactly at `y ∈ {½ + 2m}` (trivial zeros of `ζ(½-y)`, poles of
`ψ(¼-y/2)` and of the Lerch block), where the total is regular but the individual blocks are not.
The filter is proved non-trivial (`suzukiVerticalFilter_neBot`, cofinal sequence `y_k = 2k + 3/2`).

### Prop 1.2 — EXECUTED (CLOSED), by a route that needs no Titchmarsh input

Suzuki's proof uses Titchmarsh 9.6(A) (`ζ'/ζ` = sum over nearby zeros + `O(log T)`) and 9.2 (local
zero count `O(log T)`) to get `𝔖_t(x) ≪_t log|x|/|x|`.  **Neither is needed.**  The whole singular
part is killed by one elementary observation: on the real axis `A = XiC` and `A'` are *real*, so
`E^♯ = A - iA'` has `|E^♯|² = A² + A'²` and therefore

```text
|A/E^♯| ≤ 1     and     |A'/E^♯| ≤ 1      everywhere on ℝ.
```

Feeding the completed split `ζ'/ζ(1/2-ix) = i(A'/A)(x) - (log archFactor)'(1/2-ix)` into the
`ζ'/ζ` block of eq. (1.6) and multiplying by `A/E^♯` turns its pole at every real Xi zero into the
*bounded* quantity `iA'/E^♯` (`suzukiFrakS_ofReal_decomp`):

```text
𝔖_t = i(A/E^♯)·(polar + prime + kernels)
    + i·expSlope·( i(A'/E^♯) - (A/E^♯)·(log archFactor)'(1/2-ix) ).
```

The remaining blocks decay because the Lerch kernel does.  With `A_n = n+1/4`, `B = |x|/2`, weighted
AM–GM gives `|n + 1/4 - ix/2| ≥ A_n^{1/4}B^{3/4}`, hence

```text
‖suzukiLerchKernel t (1/4 - ix/2)‖ ≤ (|x|/2)^{-3/4} · ∑ₙ (n+1/4)^{-5/4}.
```

The exponent `3/4` is what makes the argument work: the naive Cauchy–Schwarz split gives only
`|x|^{-1/2}`, which is *not* square integrable.  The same Gauss bridge turns `ψ(1/4-ix/2)` into
`ψ(1/4) - (ix/2)·kernel`, so the archimedean logarithmic derivative on the critical line is bounded
by `M + (|x|/4)‖kernel‖`, and the `2/|x|` half of the exponential-slope bound absorbs that product
exactly.  The result is the master estimate

```text
‖𝔖_t(x)‖ ≤ C_t · (1 + |x|)^{-3/4}      for x ≠ 0 with XiC(x) ≠ 0,
```

and `(1+|x|)^{-3/2}` is integrable on `ℝ` (`integrable_one_add_norm`, `finrank ℝ ℝ = 1 < 3/2`).

**Measurability** is the one non-obvious extra ingredient.  The printed formula for `𝔖_t` contains
`ζ'/ζ`, whose measurability is not available off the shelf (nor is that of `Γ` or `ψ`).  It is
avoided by `suzukiFrakSModel`: the same decomposition with the digamma traded for the Lerch kernel,
built only from `XiC`, `deriv XiC`, exponentials and one convergent series.  It agrees with `𝔖_t`
off the origin and the countable real Xi zero set (`XiC_zeroSet_countable`), which is null.

## Source defects found

- Eq. (7.2)'s proof prints `(d/dt)(e^{-t/2}Φ(e^{-2t},2,¼)) = -2e^{-t/2}Φ(e^{-2t},2,¼)`.  The correct
  identity is `= -2 e^{-t/2}Φ(e^{-2t},1,¼)` (second Lerch slot drops from `2` to `1`).  With the
  printed version the theorem is false; with the corrected version eq. (7.2) is exactly right.
- Eq. (7.2) writes `𝔅_t` for `𝔓_t` (typographic).

## Landed Lean

| Module | Content |
|---|---|
| `RHTower/SuzukiWeilLerchBlock.lean` | `suzukiLerchDiff` / `suzukiLerchKernel` (the regularized `Φ(e^{-2t},1,w) - Φ(e^{-2t},1,1/4)` of eq. (1.6)), its factorization `= (1/4-w)·kernel`, `suzukiLerchKernel t (1/4) = 4e^{t/2}·screwLerchTail t`, the Gauss bridge `ψ(w)-ψ(1/4) = -suzukiLerchDiff 0 w`, and continuity of the kernel at `1/4`. |
| `RHTower/SuzukiWeilFrakPLaplace.lean` | The five-block split of eq. (1.6) (`suzukiFrakPPolar/Zeta/Prime/Digamma/Lerch`), the prime-ray and Lerch-ray decompositions, all five Laplace transforms with their integrability, and **`integral_suzukiFrakP_laplace`**. |
| `RHTower/SuzukiWeilPropThreeOneCapstone.lean` | Continuity in `t` of both sides on `(0,∞)` (via the `max(t-log n,0)` form of the prime ray and locally uniform Weierstrass bounds), the a.e.-to-pointwise gluing lemma, and **`suzukiFrakP_eq_suzukiPtZeroSum`** = Proposition 3.1. |
| `RHTower/SuzukiWeilPropThreeOneDeterminacy.lean` | Exponential growth bounds for all five blocks and for `𝔓`; measurability in `t`; `ae_eq_zero_of_expFourier_eventuallyEq_zero` and `expFourier_eventuallyEq_zero_of_imaginarySegment` (reusable determinacy tools); **`suzukiFrakP_ae_eq_suzukiPtZeroSum`**. |
| `RHTower/SuzukiWeilPropThreeOne.lean` | `riemannZeta_ne_zero_of_XiC_ne_zero`, the two evaluations of `xiRelativeResolventTrace` in prime--archimedean terms, and **`integral_suzukiFrakP_laplace_eq_zeroSeries`** — the two Laplace transforms agree. |
| `RHTower/SuzukiWeilZeroSeries.lean` | `suzukiPtZeroTerm` / `suzukiPtZeroSum` (eq. 3.2), summability, `‖P_t(z)‖ ≪_z e^{|t|/2}`, per-copy Laplace transform, and **`integral_suzukiPtZeroSum_laplace`**.  Also `XiC_neg` (evenness of the centered completed Xi source), which the corpus did not have. |
| `RHTower/SuzukiWeilFrakP.lean` | `suzukiFrakP` (eq. 1.6) and `suzukiFrakPReg`; `suzukiScrewG_eq_screwFn`; `riemannZeta_half_ne_zero`; `logDeriv_riemannZeta_half : ζ'/ζ(1/2) = -screwLinearCoeff/2`; `continuousAt_logDeriv_riemannZeta_half`; **`tendsto_suzukiFrakP_zero`** (eq. 7.1). |
| `RHTower/SuzukiWeilDigammaOffPoles.lean` | **`digamma_sub_quarter_eq_offPoles`** — Gauss's digamma difference series at *every* `w` off the poles of `Γ`, not just on `Re w > 0` (a mathlib and corpus gap); `summable_suzukiLerchDiffTerm_all` (hypothesis-free summability); `suzukiLerchDiff_zero_add_one` (the shift law `S(w+1) = S(w) - 1/w`); `suzukiLerchDiff_zero_five_quarters`; `norm_suzukiLerchKernel_le_of_one_le_re`. |
| `RHTower/SuzukiWeilVerticalDecay.lean` | The Titchmarsh-free decay toolkit: reality of the centered Xi jet on ℝ, `norm_XiC_div_ESharp_le_one` and `norm_deriv_XiC_div_ESharp_le_one` (both quotients bounded by one), the `ζ'/ζ ↔ A'/A` bridge `logDeriv_riemannZeta_vertical_eq`, the `(|x|/2)^{-3/4}` Lerch-kernel bound, the weight `decayW x = (1+|x|)^{-3/4}` with its comparison lemmas, the exponential-slope bounds `min(|c|, 2/|x|)`, and `exists_norm_logDeriv_archFactor_vertical_le`. |
| `RHTower/SuzukiWeilPropOneTwo.lean` | `suzukiThetaSharp`, **`suzukiFrakS`** (eq. 1.5), `suzukiFrakS_ofReal_decomp` (the pole-free five-block form), the blockwise bounds, **`exists_norm_suzukiFrakS_le`** (`‖𝔖_t(x)‖ ≤ C(1+|x|)^{-3/4}`), the measurable model `suzukiFrakSModel` with `measurable_suzukiFrakSModel`, and **`memLp_suzukiFrakS`** = Proposition 1.2. |
| `RHTower/SuzukiWeilAppendixDerivative.lean` | `hasDerivAt_screwFn_atomFree` (the exact derivative of `g_ξ` off the prime-power atoms); `tendsto_logDeriv_riemannZeta_ofReal_atTop`; `suzukiVerticalLerchTerm` / `suzukiVerticalFilter` / `suzukiVerticalLerchBound` with the three-regime `y`-uniform dominant and `suzukiVerticalFilter_neBot`; `digamma_quarter_sub_logPi` (`screwLinearCoeff = ψ(1/4) - log π`); `suzukiFrakP_vertical_mul`; `suzukiVerticalEnergy_eq` (the five-block decomposition); the five block limits; and **`tendsto_suzukiFrakP_vertical`** = eq. (7.2). |

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

### Endgame for Prop 3.1 — EXECUTED

1. **Growth**: `‖P_t(z)‖ ≤ C_z (e^{|t|/2}+1)` is `norm_suzukiPtZeroSum_le` (done).  For `𝔓` combine the
   five block bounds already proved (`norm_suzukiFrakPPrime_le`, `norm_suzukiLerchDiff_le`, and the
   elementary polar/zeta/digamma blocks) into `‖𝔓_t(z)‖ ≤ C e^{ct}` for `t ≥ 0`.
2. **Determinacy**: set `h t := 𝔓_t(z) - P_t(z)` and `g t := h t · e^{-σ₁ t} · 1_{Ioi 0}(t)` for a
   fixed large `σ₁`.  Then `‖g‖ ≤ K e^{-ε|x|}` and, by the Laplace identity,
   `expFourier g (iτ) = ∫_0^∞ h(t) e^{-(σ₁-τ)t} dt = 0` for all real `τ < σ₁ - σ₀`.
   `expFourier g` is analytic on the strip `|Im w| < ε` (`analyticOnNhd_expFourier`), so vanishing on
   the imaginary segment forces `expFourier g =ᶠ[𝓝 0] 0` by
   `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, and then the tail of
   `RHTower.ae_eq_zero_of_moments_eq_zero` (`ExpDecayFourierAnalytic.lean`: `convex_imStrip`,
   `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`,
   `integrable_ae_eq_zero_of_fourier_eq_zero`) gives `g = 0` a.e., hence `h = 0` a.e. on `(0,∞)`.
   *(The reusable generalization to extract: the same conclusion from `expFourier g =ᶠ[𝓝 0] 0`
   instead of from vanishing moments.)*
3. **Continuity** of both sides in `t` upgrades a.e. to pointwise: `P_t` by `continuous_tsum`-style
   local uniform bounds; `𝔓_t` blockwise, the only nontrivial block being the prime one, which is
   continuous because the entering ray `w_n φ(t - log n)` vanishes at its atom `t = log n`.

Endgame: Laplace determinacy.  With `σ = m + N₀` and the substitution `u = e^{-t}` the vanishing of
`∫_0^∞ (𝔓_t - P_t)e^{-σt}dt` becomes vanishing of all polynomial moments of a bounded function
supported in `[0,1]`, so `RHTower.ae_eq_zero_of_moments_eq_zero` (`ExpDecayFourierAnalytic.lean`)
applies.  Continuity of both sides in `t` then upgrades a.e. to pointwise.

## Log
- 2026-08-22 — **Proposition 1.2 CLOSED in Lean, unconditionally** (`memLp_suzukiFrakS`), by a route that uses *no* Titchmarsh zero-density or `ζ'/ζ` input: the two elementary quotient bounds `|A/E^♯| ≤ 1`, `|A'/E^♯| ≤ 1` on the real axis kill the poles, and a weighted-AM–GM bound gives the Lerch kernel the decay exponent `3/4` (the naive `1/2` would not be square integrable).  Also generalized the corpus's `suzukiFrakP_eq_reg` to `suzukiFrakP_eq_reg_of_re_pos` (hypothesis `‖z‖ < 1/2` weakened to `0 < Re(1/4 - iz/2)`, which the whole real axis satisfies).  All capstones axiom-clean.
- 2026-08-22 — **eq. (7.2) CLOSED in Lean, unconditionally** (`tendsto_suzukiFrakP_vertical`), completing the whole unconditional appendix Theorem 7.1.  Required a new mathlib/corpus gap module: Gauss's digamma difference series off the poles.  Both new capstones axiom-clean.
- 2026-08-22 — created; source inventoried statement by statement; corpus dictionary established.
- 2026-08-22 — **Proposition 3.1 CLOSED in Lean, unconditionally** (`suzukiFrakP_eq_suzukiPtZeroSum`), by the Laplace-matching route: five-block Laplace transform of eq. (1.6), Laplace transform of the Xi-zero series, the corpus explicit formula as the bridge, Laplace determinacy through the exponential Fourier transform, and continuity in `t`.  All capstones axiom-clean.
- 2026-08-22 — L3 started: the Xi-zero-series Laplace transform is closed; the five-block split of eq. (1.6) and the polar/zeta/digamma Laplace transforms are closed.
- 2026-08-22 — L1 (Lerch block) and eq. (7.1) closed in Lean; two sign typos in the printed proof of
  (7.1) recorded; anti-duplication audit run and one duplicate (`suzukiGXi`) removed.
