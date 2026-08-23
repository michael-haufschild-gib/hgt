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
| `thm_1_1` | Thm 1.1 | `K(Θ_ξ) → H_W`, `F ↦ [F⁻¹F]`, is a Hilbert isomorphism with `‖E F‖²_{H(E)} = ‖F‖²_{K(Θ)} = π⟨ψ_F,ψ_F⟩_W` | yes | **CLOSED** `RHTower.suzukiModelWeilEquiv`, `norm_sq_suzukiModelWeilEquiv`, `suzukiWeilTauEquiv_suzukiModelWeilEquiv` |
| `prop_101` | Prop 1.2 | `𝔖_t ∈ L²(ℝ)` for every fixed `t ∈ ℝ` | no | **CLOSED** `RHTower.memLp_suzukiFrakS` |
| `prop_102` | Prop 1.3 | `𝒫̂_φ ∈ L²(ℝ)` for `φ ∈ C_c^∞(ℝ)` | no | **CLOSED** `RHTower.memLp_suzukiPHat_of_compactSupport` |
| `thm_1_2` | Thm 1.4 | RH ⟺ `‖𝒫̂_{Dψ}‖²_{L²} = π⟨ψ,ψ⟩_W` for all `ψ ∈ C_c^∞`; countably many `ψ` suffice | ⟺ | **CLOSED (main clause)** `RHTower.riemannHypothesis_iff_normSq_suzukiPHat_deriv`; the *countably many* clause is Cor 4.6 and needs BoLa99 |
| `cor_1_1` | Cor 1.5 | RH ⟺ `2‖ψ‖²_{L²} = ⟨ψ,ψ⟩_W` for all `ψ ∈ V°(0)` | ⟺ | **CLOSED** `RHTower.riemannHypothesis_iff_normSq_suzukiPHat_suzukiTest` |
| `prop_301` | Prop 3.1 | `𝔓_t(z) = P_t(z)` (prime--arch formula equals the Xi-zero series) | no | **CLOSED** `RHTower.suzukiFrakP_eq_suzukiPtZeroSum` |
| `lem_301` | Lem 3.2 | `‖ψ‖₀ := π^{-1/2}‖𝒫̂_{Dψ}‖_{L²}` is a norm on `C_c^∞(ℝ)` | no | **definiteness CLOSED** `RHTower.eq_zero_of_suzukiPHat_D_ae_zero` |
| `prop_401` | Prop 4.1 | `{F_γ}` is an orthonormal basis of `K(Θ)`; `Θ'(γ)/2 = -i/m_γ`; `F_γ(γ)=1/√(m_γ π)`, `F_γ(γ')=0` | yes | **CLOSED** — `RHTower.suzukiFGammaHilbertBasis` is the orthonormal basis of `K(Θ)`; with `inner_suzukiFGammaLp`, `norm_suzukiFGammaLp`, `suzukiFGammaLp_mem_suzukiModelSpace`, `hasSum_normSq_inner_suzukiFGammaFamily` (Parseval), `hasDerivAt_suzukiHalfInner` (4.1), `suzukiFGammaFun_self` / `suzukiFGammaFun_eq_zero_of_ne` (4.2) |
| `thm_4_1` | Thm 4.2 | `t ↦ π^{-1/2}𝔖_t` is a screw line of `g_ξ`: `π⁻¹⟨𝔖_t,𝔖_u⟩ = G_g(t,u)` | yes | **CLOSED** `RHTower.inner_suzukiFrakSFull_eq_pi_mul_screwKernel` |
| `cor_401` | Cor 4.3 | RH ⟺ `(2π)⁻¹‖𝔖_t‖² = -g(t)` for all `t ≥ t₀`, some `t₀ ≥ 0` | ⟺ | **CLOSED at `t₀ = 0`** `RHTower.riemannHypothesis_iff_norm_sq_suzukiFrakSFull`; the `t₀ > 0` refinement needs Su22 Thm 11.1 |
| `thm_4_2` | Thm 4.4 | RH ⟺ `‖𝒫̂_φ‖² = π⟨φ,φ⟩_{G_g}` for all `φ ∈ C_c^∞` with `φ̂(0)=0` | ⟺ | **CLOSED** `RHTower.riemannHypothesis_iff_normSq_suzukiPHat` |
| `thm_4_3` | Thm 4.5 | RH ⟺ `‖ψ‖₀² = ⟨ψ,ψ⟩_W` for all `ψ ∈ C_c^∞` | ⟺ | **CLOSED** (same theorem as Thm 1.4) |
| `cor_4_2` | Cor 4.6 | RH holds if `‖g_n‖₀² = ⟨g_n,g_n⟩_W` for all Bombieri--Lagarias `g_n` | ⟸ | OPEN — blocked on BoLa99 §4, absent from the corpus |
| `lem_5_1` | Lem 5.1 | `K(Θ) = F(V(0))`, `H(E) = E·F(V(0))`, `V(0) = L²(0,∞) ∩ K L²(0,∞)` | yes | **CLOSED** `RHTower.map_fourier_suzukiV0` + `RHTower.memDeBranges_iff_mem_suzukiModelSpace` |
| `rmk_5_2` | Rmk 5.2 | `V(0) = {0}` would falsify RH; `K`-eigenvector reduction | yes | **CLOSED** `RHTower.exists_suzukiK_eigenvector` (+ `suzukiKFun_mem_suzukiV0`); `V(0) ≠ 0` follows from `suzukiFGammaLp_mem_suzukiModelSpace` |
| `lem_5_2` | Lem 5.3 | `V(0) ≅ L²(τ)` by `ψ ↦ (ψ̂(γ))_γ`, `2‖ψ‖² = ‖S_ψ‖²` | yes | **CLOSED** `RHTower.hasSum_suzukiClarkWeight_normSq_restriction`, `suzukiRestriction_inj`, `exists_suzukiRestriction_eq`, `hasSum_suzukiClarkWeight_normSq_restriction_suzukiV0` |
| `lem_5_3` | Lem 5.4 | `H_W ≅ L²(τ)` by `[ψ] ↦ S_ψ`, `⟨ψ,ψ⟩_W = ‖S_ψ‖²` | yes | **CLOSED** `RHTower.suzukiWeilTauEquiv` (with `denseRange_suzukiSpectralMap`) |
| `thm_5_1` | Thm 5.5 | Refined Thm 1.1: (1) the four-fold norm identity on `V(0)`; (2) the composite map | yes | **CLOSED** `RHTower.norm_sq_suzukiV0_eq_pi_mul_weil`, `suzukiWeilTauEquiv_suzukiV0` |
| `thm_5_2` | Thm 5.6 | `H_0 = H_W`, `K_0 = K(Θ)`; `𝒫̂_D` inverts Thm 5.5(2); `V(0) = closure V°(0)` | yes | **`H_0 = H_W` and `K_0 = K(Θ)` CLOSED** `RHTower.normSq_suzukiPHat_deriv_eq_pi_mul_suzukiWeilInner`, `RHTower.suzukiKZero_eq_suzukiModelSpace`; `V(0) = closure V°(0)` is its image under `𝖥⁻¹` |
| `thm_5_3` | Thm 5.7 | `E·F(V(t))` is a de Branges subspace of `H(E)` for all `t ≥ 0`, isomorphic to `H_W(t)` | yes | **CLOSED** `RHTower.suzuki_deBranges_subspace` (+ `suzukiWeilRay`, `norm_sq_suzukiWeilRay`) |
| `prop_5_1` | Prop 5.8 | RH ⟺ (1) `‖ψ‖² = ½⟨ψ,ψ⟩_W` on `V(0)` and (2) the peaked-test condition | ⟺ | **CLOSED** `RHTower.suzuki_prop_5_1` (unitary normalisation: `π` in place of `½`; `δ = 1/2` in (2)) |
| §6 | — | `(H_W, A_{W,π/2})` is a Hilbert--Pólya space; eigenvalue multiplicity one | yes | **CLOSED in the sequence model** `RHTower.isSelfAdjoint_suzukiTauDiag`, `suzukiTauDiag_basis`, `eq_smul_suzukiTauBasis_of_eigen` — a self-adjoint operator whose eigenvalues are exactly the Xi zeros, each simple, on `L²(τ) ≅ H_W` |
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
   `V(t)`.  Mathlib has none of this.  **But the corpus now does own `H²` of a half-plane and a full
   Paley–Wiener theorem** (`HTGeometry.PaleyWienerHalfPlane.isHalfPlaneHardy_eq_laplaceRay`, twelve
   modules; see the `paley-wiener-half-plane-closed` memory).  Start from there; what is still
   missing is the model space `K(Θ)` for a meromorphic inner `Θ` and the de Branges space `H(E)`.
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
- **The negative-`t` convention is inconsistent (substantive).**  The paper extends `P_t` (3.2) and
  `𝔖_t` (1.5) to `t < 0` by *evenness* (`𝔖_t := 𝔖_{-t}`), but equations (3.6)–(3.8), Theorem 4.2 and
  Theorem 1.4 all use the eq. (3.2) series *without* the absolute value.  With the even extension one
  computes, for `φ = Dψ`,
  `𝒫̂_{Dψ}(z) = -(i/2)(1+Θ(z))∑_γ m_γ c_γ/(γ(z-γ))` with
  `c_γ = γ∫_0^∞ e^{iγt}(ψ(t)-ψ(-t))dt`, which vanishes identically for every **even** `ψ`.  Lemma 3.2
  (that `‖·‖₀` is a norm) and eq. (1.9) would then both be false.  Dropping the absolute value gives
  `c_γ = γψ̂(γ)`, which is what (3.8) asserts.  Formalized object: `RHTower.suzukiFrakSFull`.
- Eq. (3.6) as printed also carries a sign/conjugation slip: `𝔖_t = i(1+Θ^♯)/2·P_t` expands with
  coefficient `(e^{-iγt}-1)/γ` against `F_γ` (not `F_γ^♯`), and with the opposite overall sign from
  the printed formula.  Immaterial for every norm statement downstream.

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
| `RHTower/SuzukiWeilFrakSZeroSeries.lean` | **`suzukiFrakSFull`** — `𝔖_t = i(1+Θ^♯)/2·P_t` for *every* real `t`, the object equations (3.6)–(3.8) actually use; agreement with `suzukiFrakS` for `t > 0` (Prop 3.1); the divisor-reflection identity `P_{-t}(z) = P_t(-z)` (`suzukiPtZeroSum_neg`, through `xiZeroCopyReflectEquiv`); `norm_suzukiFrakSFull_le` for all `t`; joint measurability in `(x,t)`; and `memLp_suzukiFrakSFull`. |
| `RHTower/SuzukiWeilTransformRaySeries.lean` | `suzukiPHatConj`, `suzukiPHat_ofReal_eq_conj`, `suzukiPHatRayTerm`, and **`suzukiPHatConj_eq_tsum`** = the multiplicity-exact form of Suzuki eq. (3.7).  Also `integral_suzukiPtZeroSum_mul` (the Fubini exchange). |
| `RHTower/SuzukiWeilDifferentialPairing.lean` | `suzukiD` (eq. 1.8), `hasDerivAt_expSlopeKernel`, `deriv_eq_zero_of_supp`, `integral_eq_intervalIntegral_of_supp`, **`integral_expSlope_mul_deriv`** (integration by parts) and **`integral_expSlope_mul_conj_D`** = step 2 of the Lemma 3.2 route. |
| `RHTower/SuzukiWeilRaySeriesHolomorphy.lean` | `exists_pos_dist_xiSpectralPoint`, `norm_raySeriesNumerator_le`, and **`differentiableAt_suzukiPHatRaySum`** = step 3a of the Lemma 3.2 route. |
| `RHTower/SuzukiWeilRaySeriesIdentity.lean` | **`suzukiPHatRaySum_eq_zero_off_divisor`** = step 3b(i): the identity theorem carrying real-axis vanishing to the whole divisor complement. |
| `RHTower/SuzukiModelSpace.lean` | **`hardyL2`** (`H² = 𝖥(L²(0,∞))` as a closed subspace of `L²(ℝ)`), `negRayProj`/`halfLineL2` (the kernel presentation that makes `L²(0,∞)` a closed submodule for free), `suzukiThetaSymbol` (the unimodular normalization of `Θ_ξ = E^♯/E` on the line), `thetaMul`/`thetaMulInv` with their two-sided inverse laws, and **`suzukiModelSpace`** `= K(Θ_ξ) = H² ⊖ Θ H²` with `isClosed_suzukiModelSpace`.  Key input: `E^♯(x) = conj(E(x))` on ℝ. |
| `RHTower/SuzukiModelSpaceOrthogonal.lean` | `lowerHalfLineL2`, `halfLineL2_orthogonal` (`L²(0,∞)^⊥ = L²(-∞,0)`), `thetaUnitary` (multiplication by `Θ` is unitary), `hardyL2_orthogonal`, and **`suzukiModelSpace_eq_inf_map`** = Suzuki eq. (2.7), `K(Θ) = H² ∩ Θ(H²)^⊥`. |
| `RHTower/SuzukiInnerDerivative.lean` | **`hasDerivAt_suzukiHalfInner`** = Suzuki eq. (4.1): `A/E = (1+Θ)/2` has a simple zero of slope `-i/m_γ` at every Xi zero.  Stated for `A/E` rather than `Θ`, because at a multiple zero `E` vanishes too and `Θ = E^♯/E` is `0/0` in Lean exactly where the derivative is wanted.  Proof peels the zero and uses `P(γ) = i m h(γ) ≠ 0`. |
| `RHTower/SuzukiScrewLineCoefficients.lean` | `suzukiFrakSFull_zero` (`𝔖_0 = 0`, immediate from the zero series) and **`summable_norm_sq_suzukiScrewCoeff`** — the `L²` convergence step of Theorem 4.2, unconditional because `|Im γ| < 1/2` bounds `|e^{-iγt}-1|` uniformly. |
| `RHTower/SuzukiWeilPropOneThree.lean` | `suzukiFrakSSharp`, **`suzukiPHat`** (eq. 1.7, built on `suzukiFrakSFull`), the pointwise bound `norm_suzukiPHat_ofReal_le`, and **`memLp_suzukiPHat_of_compactSupport`** = Proposition 1.3.  No Minkowski integral inequality is used: the master bound of Prop 1.2 is pointwise and its constant is monotone (`suzukiFrakSConst_mono`), so `‖∫‖ ≤ ∫‖·‖` suffices. |
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

## Route for Lemma 3.2 (`‖·‖₀` is a norm) — step 1 DONE, steps 2–4 next

With the corrected object, on the real axis (all that `‖·‖₀` sees),

```text
𝒫̂_φ(x) = conj( i(1+Θ^♯(x))/2 · ∑_q a_q/(γ_q(x-γ_q)) ),   a_q = ∫(e^{-iγ_q t}-1)·conj(φ(t))dt,
```

the series being **absolutely** convergent (the extra `1/γ_q` is what makes it so; the printed
`∑_γ m_γ ψ̂(γ)/(z-γ)` of (3.8) is not absolutely convergent).

1. **DONE** — `RHTower.suzukiPHatConj_eq_tsum` (module `SuzukiWeilTransformRaySeries`), by
   `integral_tsum_of_summable_integral_norm`; the domination uses `|Im γ| < 1/2`
   (`norm_suzukiPtZeroExp_le`) so that the exponential factor is `≤ e^{T/2}+1` uniformly in `q` on
   the support of `φ`.  Companion: `suzukiPHat_ofReal_eq_conj`.
2. **DONE** — `RHTower.integral_expSlope_mul_conj_D` (module `SuzukiWeilDifferentialPairing`):
   `∫(e^{-iwt}-1)conj((Dψ)(t))dt = w·∫e^{-iwt}conj(ψ(t))dt`, so `a_q = γ_q·(Fourier of conj ψ at
   `-γ_q`) and the ray becomes `F(-γ_q)/(z-γ_q)`.  Engine: `integral_expSlope_mul_deriv`
   (integration by parts on a window containing the support, transported back by
   `setIntegral_eq_integral_of_forall_compl_eq_zero`); `deriv ψ` inherits the support bound
   (`deriv_eq_zero_of_supp`).  Also `suzukiD` (eq. 1.8), `deriv_conj_comp`.
3a. **DONE** — `RHTower.differentiableAt_suzukiPHatRaySum` (module `SuzukiWeilRaySeriesHolomorphy`):
   the ray series is complex differentiable at every `z₀` with `XiC z₀ ≠ 0`.  The dominant is the
   crux: a `1/dist(z₀,Γ)` bound gives only `∑ 1/|γ_q|` (divergent); shrinking to radius `r/2` with
   `r ≤ |z₀-γ_q|` for *every* `q` gives `|w-γ_q| ≥ |z₀-γ_q|/2` uniformly, hence
   `‖ray‖ ≤ 2M‖(γ_q(γ_q-z₀))⁻¹‖` with `summable_xiResolventProduct_norm`.  Companion:
   `exists_pos_dist_xiSpectralPoint`, `norm_raySeriesNumerator_le`.

3b(i). **DONE** — `RHTower.suzukiPHatRaySum_eq_zero_off_divisor` (module
   `SuzukiWeilRaySeriesIdentity`): vanishing at every admissible *real* point upgrades to vanishing
   at every point off the divisor.  Uses `isPreconnected_XiC_ne_zero`, `isOpen_XiC_ne_zero` and
   `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`, with the reals accumulating at
   `0` (where `XiC 0 ≠ 0`).

3b(ii). **Fibre residue — DO NOT BUILD, the corpus already owns it.**  A search on 2026-08-22
   turned up, in `RHTower.XiCauchyTransformCompleteness`:

   - `xiCauchyTransform (u : lp (fun _ : XiZeroCopy => ℂ) 2)` — the Cauchy transform of a
     square-summable divisor vector;
   - `differentiableOn_xiCauchyTransform` — holomorphic off the divisor (this overlaps the
     `SuzukiWeilRaySeriesHolomorphy` module built here: the corpus version assumes an `ℓ²` vector,
     the local one assumes `1/(|γ_q||z-γ_q|)`-summability; keep both, but note the relation);
   - `xiCauchyTransform_eq_zero_of_re_eq_zero_on_ball` — completeness;
   - **`xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball`** — *the multiplicity fibre
     sums vanish*, i.e. exactly this step.

   Also `RHTower.finite_xiSpectralPoint_fiber` already exists (`XiWeilPolarization.lean:242`); a
   duplicate was written here and discarded.

   **Remaining work for 3b(ii)** is therefore only the *bridge*, and its two fiddly points are
   already settled:

   - `xiCauchyTransform u z = ∑'_q conj(u q)·(γ_q - z)⁻¹`, whereas the ray sum is
     `R z = ∑'_q b_q/(z - γ_q) = -∑'_q b_q·(γ_q - z)⁻¹`.  So take **`u q := conj (b_q)`**, giving
     `xiCauchyTransform u = -R`.
   - the corpus theorem only needs **`(xiCauchyTransform u z).re = 0` on one ball** inside the
     regular set — far weaker than the full vanishing already proved by
     `suzukiPHatRaySum_eq_zero_off_divisor`, so any ball inside `{XiC ≠ 0}` will do.

   What is left: `Memℓp (fun q => conj (a_q/γ_q)) 2`, which is immediate from `|b_q| ≤ M/|γ_q|`
   (`norm_raySeriesNumerator_le` plus `xiSpectralPoint_ne_zero`) and
   `xiSpectralPoint_inv_sq_summable`.  Then
   `xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball` gives
   `xiWeilFiberSum u ρ = 0` for every `ρ`, i.e. `m_ρ · conj(F(-γ_ρ)) = 0`, hence `F(γ) = 0` for
   every `γ ∈ Γ` (using that `Γ` is negation-symmetric, `xiSpectralPoint_reflect`).

3b (original sketch, superseded above).  `‖·‖₀ = 0` ⟹ the series vanishes a.e. on `ℝ` (because
   `A(x)/E^♯(x) ≠ 0` off the countable real Xi zero set), and then
   `lim_{z→γ}(z-γ)·T(z) = m_γ a_γ/γ = 0`.  **The corpus already owns the analytic layer this needs**:
   `HTGeometry.HerglotzDiscreteSupportSeries.summableLocallyUniformlyOn_discreteHerglotzCauchy_off_poles`
   and `.differentiableOn_discreteHerglotzCauchySeries_off_poles` (a discrete-support Cauchy series is
   holomorphic off its poles, with normal convergence), plus
   `HTGeometry.AnalyticRootFactor.finite_zeros_closedBall`,
   `RHTower.LocallyFiniteDivisorPresentation.LocallyFiniteDivisor`, and
   `RHTower.XiWeilDivisorHilbert`'s preconnectedness of the divisor complement for the identity
   theorem.  Do **not** rebuild these.
4. `η̂(γ) = 0` for all `γ ∈ Γ` (Γ is negation-symmetric, `xiSpectralPoint_reflect`) ⟹ `η = 0` by
   `RHTower.suzuki_lemma_two_one` (Su22 Lemma 2.1, already in the corpus: entire of exponential type
   + vanishing on `{z : ξ(1/2-iz)=0}` ⟹ identically zero) ⟹ `ψ = 0`.  Note `ξ(1/2-iz) = XiC z`.

## Layer L6/L7 — starting points already in the corpus

- `H²` of a half-plane **and a full Paley–Wiener theorem**:
  `HTGeometry.PaleyWienerHalfPlane.isHalfPlaneHardy_eq_laplaceRay` (twelve modules).  Rotate by
  `z = iw` to reach Suzuki's `H²(ℂ₊) = 𝖥(L²(0,∞))`.
- Hermite–Biehler for the Xi pair: `RHTower.StrictHermiteBiehlerGivesRH.strict_hermiteBiehler_of_rh`,
  `RHTower.SuzukiLagariasMeromorphicInner.suzukiCanonicalHermiteBiehler_of_halfPlaneBound`,
  `analyticOrderAt_xiHedenmalmDeBrangesE_eq_pred_of_XiC_zero`.
- **Genuinely missing**: the model space `K(Θ) = H² ⊖ ΘH²` for a meromorphic inner `Θ`, the de
  Branges space `H(E)`, the Makarov–Poltoratski restriction isometry `K(Θ) → L²(μ_Θ)` (eq. 2.8),
  and Prop 4.1 (`{F_γ}` an ONB of `K(Θ)`, cited to Su23 Prop 3.2).

## Route for Theorem 4.2 (screw line) — EXECUTED (CLOSED)

Target: `(1/π)⟪𝔖_t, 𝔖_u⟫_{L²(ℝ)} = G_g(t,u)`.

**Reduction (checked on paper).**  On `ℝ`, `E^♯(x) = conj(E(x))`, so `A/E^♯ = conj(A/E) = conj h`
and `𝔖_t(x) = i · conj(h(x)) · P_t(x)`.  Hence

```text
conj(𝔖_t(x)) · 𝔖_u(x) = |h(x)|² conj(P_t(x)) P_u(x) = conj(h P_t)(x) · (h P_u)(x),
```

so `⟪𝔖_t, 𝔖_u⟫ = ⟪h P_t, h P_u⟫`.  Writing the divisor sum over the *support* `ρ` (multiplicity
`m_ρ`) and using `h(x)/(x-γ_ρ) = -i √(π/m_ρ) F_ρ(x)`,

```text
h P_t = -i √π · ∑_ρ b_ρ(t) F_ρ,        b_ρ(t) := √(m_ρ) (e^{-iγ_ρ t} - 1)/γ_ρ.
```

Orthonormality of `{F_ρ}` (now proved) then gives
`⟪h P_t, h P_u⟫ = π ∑_ρ m_ρ conj(c_ρ(t)) c_ρ(u) = π ∑'_q conj(c_q(t)) c_q(u) = π G_g(t,u)` by
`suzukiScrewKernel_eq_tsum` (Su22 (1.9), proved).

**The one analytic step, and how to do it cheaply.**  The series `∑_ρ b_ρ F_ρ` is only `ℓ²`,
never absolutely convergent (`∑ √(m_ρ)/|γ_ρ|` diverges), so the pointwise sum must be identified
with the `L²` sum.  **Fatou does it without any subsequence extraction**: for a finite `F`, the
finite orthonormality computation gives exactly

```text
∫ |h|² |∑_{ρ∈F} m_ρ c_ρ/(x-γ_ρ)|² = π ∑_{ρ∈F} m_ρ |c_ρ|²,
```

and applying Fatou to the tail along a countable exhaustion yields
`‖h P_t - h P_t^F‖² ≤ π ∑_{ρ∉F} m_ρ |c_ρ|² → 0`.  Taking `F = ∅` also gives `h P_t ∈ L²`.

**Pieces to build**: (a) RH ⟹ every `xiSpectralPointSupport` is real, and `ρ ↦ γ_ρ` is injective;
(b) `m_ρ = (analyticOrderAt XiC γ_ρ).toNat`, already `xiSpectralMultiplicity_eq_analyticOrderAt_toNat`;
(c) countability of `XiDivisorSupport` (corpus: `XiC_zeroSet_countable`); (d) the finite
orthonormality integral; (e) Fatou on the tail; (f) `∑ m_ρ |c_ρ|² < ∞` (from
`xiSpectralPoint_inv_sq_summable`); (g) assembly against `suzukiFrakSFull`.

**Source defect found**: equation (3.6) has a sign error.  `F_γ^♯(z) = √(m_γ/π)(-i)(1+Θ^♯(z))/(2(z-γ))`,
so `∑_γ √(π m_γ)((e^{-iγt}-1)/γ) F_γ^♯(z) = -𝔖_t(z)`, not `+𝔖_t(z)`.  Harmless downstream: every
use of (3.6) is sesquilinear or through a norm.  The sign in (4.2) (`F_γ(γ) = +1/√(m_γ π)`) is
consistent with (3.5) and with (1.5), so the defect is in (3.6) alone.

## Route for section 4.3 — EXECUTED (4.4, 4.5, 1.2 CLOSED; 4.6 blocked on BoLa99)

**The converse needs no Yoshida Lemma 1.**  The corpus already owns
`riemannHypothesis_of_suzukiSmoothTestFormNonnegative` (Su22 Theorem 1.3):
`(∀ a > 0, ∀ φ : SuzukiSmoothZeroMeanTest a, 0 ≤ (suzukiScrewSmoothForm φ φ).re) → RH`, where
`suzukiScrewSmoothForm φ₁ φ₂ = ∫∫ G_g(t,u) φ₁(u) conj(φ₂(t))` is literally Suzuki's `⟨·,·⟩_{G_g}`
of eq. (2.2) and `SuzukiSmoothZeroMeanTest a` is literally `φ ∈ C_c^∞` supported in `[-a,a]` with
`φ̂(0) = 0`.  So the `⟸` half of Theorem 4.4 is: the assumed identity makes
`(suzukiScrewSmoothForm φ φ).re = ‖𝒫̂_φ‖²/π ≥ 0`, then apply the corpus criterion.  Suzuki's own
contradiction argument (a nonreal zero plus Yoshida test functions) is not needed.

**The `⟹` half** is the isometry already built, applied to the ray coefficients of `𝒫̂_φ`:
`suzukiPHatConj φ z = I(1+Θ^♯(z))/2 · ∑'_q b_q(φ)/(z - γ_q)` with
`b_q(φ) = (∫ (e^{-iγ_q t} - 1) conj(φ(t)) dt)/γ_q` — this is `suzukiPHatConj_eq_tsum`, already
proved.  Structurally identical to `𝔖_t`, so `‖𝒫̂_φ‖² = π ∑'_q ‖b_q(φ)‖²` by
`integral_conj_of_hasSum`.

**The remaining new computation** is `⟨φ,φ⟩_{G_g} = ∑'_q ‖C_q‖²/γ_q²` with
`C_q = ∫ (e^{-iγ_q u} - 1) φ(u) du`, obtained from `suzukiScrewKernel_eq_tsum` by two applications
of `integral_tsum` (inner in `u`, then outer in `t`); the majorant is
`(e^{|t|/2}+1)(e^{|u|/2}+1)/‖γ_q‖²` against the compactly supported `φ`, summable by
`xiSpectralPoint_inv_sq_summable`.  Finally `∑'_q ‖b_q‖² = ∑'_q ‖C_q‖²/γ_q²` by the reflection
`γ ↦ -γ` of the divisor.

Then Theorem 4.5 (`‖ψ‖₀² = ⟨ψ,ψ⟩_W`) follows with `φ = Dψ`, and Corollary 4.6 by specializing to
the Bombieri--Lagarias `g_n` — the latter needs `⟨g_n,g_n⟩_W ≥ 0 ⟹ RH`, which is a separate
external input (BoLa99 §4) not yet in the corpus.

## Route for section 5 — Lemma 5.1 EXECUTED (CLOSED)

Section 5 introduces the **conjugate-linear** involution `K := F^{-1} M_Θ J F` (`J F = F^♯`) and
the spaces `V(t) := L²(t,∞) ∩ K L²(t,∞)`.  Note `K L²(t,∞)` is still a *complex* subspace even
though `K` is only conjugate-linear, since `c · Kψ = K(conj c · ψ)`.

**Lemma 5.1 (`K(Θ) = F(V(0))`) reduces to a Hilbert-space identity already half-built here.**
Writing `H² = F(L²(0,∞))` in Suzuki's convention,

```text
F(V(0)) = H² ∩ Θ · conj(H²) = H² ∩ Θ · (H²)^⊥ = H² ∩ (Θ H²)^⊥ = K(Θ),
```

the last two steps because multiplication by a unimodular `Θ` is unitary — which is exactly
`thetaUnitary` and `suzukiModelSpace_eq_inf_map` in `SuzukiModelSpaceOrthogonal`.

**Convention.**  mathlib's kernel is `e^{-2πixξ}`, so Suzuki's datum ray `L²(0,∞)` corresponds to
`lowerHalfLineL2 = L²(-∞,0)` here, and `hardyL2 = 𝖥(lowerHalfLineL2)` is `H²(ℂ₊)` (this is the
half-plane orientation already fixed once in this card — do not re-derive it from the formula).

**The one genuinely new input** is a `star`/Fourier relation on `L²(ℝ)`:

```text
star (𝖥 (star f)) = 𝖥⁻¹ f,     equivalently     star (𝖥 g) = l2Reflection (𝖥 (star g)),
```

which follows pointwise from `conj (∫ f(x) e^{-2πixξ} dx) = ∫ conj(f x) e^{2πixξ} dx` and extends
by density.  With it, `star hardyL2 = hardyL2ᗮ` (conjugation fixes `lowerHalfLineL2`, reflection
maps it to `halfLineL2`, and `hardyL2ᗮ = 𝖥 halfLineL2` is already proved).

**Mathlib gap found**: `𝓢(ℝ, ℂ)` has no `Star` instance, so the density argument cannot mirror
`L2FourierReflection` verbatim — the conjugate Schwartz map has to be built first (postcomposition
with `Complex.conjLIE` as an `ℝ`-linear isometry), or the identity proved on the integrable class
via `coeFn_fourierTransform_ae_eq_fourierIntegral` instead.  `L2FourierReflection` supplies the
density-induction pattern (`DenseRange.induction_on` + `SchwartzMap.denseRange_toLpCLM`).

After Lemma 5.1 the rest of §5 (Lemmas 5.2–5.4, Theorems 5.5–5.7, Prop 5.8, Theorem 1.1) needs the
de Branges space `H(E)` and the Makarov--Poltoratski restriction isometry (eq. 2.8), neither of
which exists yet in the corpus.

## Route for `H(E)` — EXECUTED (`H(E)` built, Lemma 5.1 second half closed)

Suzuki's definition (just before eq. (2.4)): for `E` Hermite--Biehler,

```text
H(E) = { F entire : F/E ∈ H² and F^♯/E ∈ H² },   ‖F‖_{H(E)} := ‖F/E‖_{L²(ℝ)}.
```

The corpus does **not** have `H(E)`; it has only `suzukiDeBrangesKernel` (the reproducing kernel).
What it *does* have is a full analytic realization of `H²` of a half-plane:

* `HTGeometry.PaleyWienerHalfPlane.isHalfPlaneHardy_eq_laplaceRay` — every Hardy function is the
  half-line Laplace transform of its datum;
* `HTGeometry.HalfPlaneHardy.isHalfPlaneHardy_laplaceRay` — the easy converse;
* `HTGeometry.HardyLineIsometry.isHalfPlaneHardy_integral_norm_sq_vertical_eq` — the Paley--Wiener
  isometry on each vertical line `Re w = σ`.

**The one missing bridge** is between that analytic realization and the boundary realization used
here: `hardyL2 = 𝖥 lowerHalfLineL2` is a subspace of `L²(ℝ)` with no attached analytic
continuation.  Concretely one needs, for `d` supported on the datum ray, that `𝖥 d` is the
`L²(dt)` limit as `σ → 0⁺` of `F(σ + it)` where `F` is the Laplace transform of `d`.  The vertical
isometry above gives the `σ`-family norms; the remaining work is the boundary limit.

Beware the rotation and the ray orientation: the corpus's `laplaceRay` uses the *right* half-plane
and the datum ray `(0,∞)`, while `hardyL2` here is the *upper* half-plane with datum ray `(-∞,0)`
under mathlib's `e^{-2πixξ}` kernel.  The composite is `w = -iz` together with a ray flip; this is
the same orientation trap that was already fixed once for `hardyL2` — check it against
`hardyL2_orthogonal` rather than re-deriving from the integral formula.

With the bridge, `H(E)` follows as a structure on entire functions, and Lemma 5.1's second half
(`H(E) = E · 𝖥(V(0))`) plus the isometry `K(Θ) → H(E)`, `G ↦ E·G`, are then formal consequences of
`map_fourier_suzukiV0`.

## Route for Prop 4.1 completeness / Makarov--Poltoratski — the single remaining §5 target

Since `μ_Θ({γ}) = π m_γ` and `F_γ(γ) = 1/√(m_γ π)`, the MaPo restriction isometry
`‖F‖²_{L²(ℝ)} = ∑_γ π m_γ |F(γ)|²` **is** Parseval for `{F_γ}`.  So one target serves both.

**Reduction worked out.**  Let `G ∈ K(Θ)` with `⟪F_γ, G⟫ = 0` for every `γ ∈ Γ`; show `G = 0`.
Through `memDeBranges_iff_mem_suzukiModelSpace`, write `G = F/E` with `F` entire in `H(E)`.  Then:

1. `⟪F_γ, G⟫ = 0` for all `γ` should give `F(γ) = 0` for all `γ ∈ Γ`.  This is the *reproducing*
   property of the boundary kernel `F_γ` in `K(Θ)`, i.e. `⟪F_γ, G⟫ = c_γ · G(γ)` — the one place
   where the analytic realization of `K(Θ)` is genuinely needed.  The half-plane Cauchy machinery
   already built (`integral_eq_zero_of_upperHalfPlane_farDecay`) is the natural tool.
2. `F` entire vanishing on the whole Xi divisor makes `F/A` entire (`A` has exactly those zeros
   with those multiplicities).
3. Krein's growth argument: `F ∈ H(E)` with `F/A` entire forces `F/A` constant.
4. `A ∉ H(E)` (this is [SiTo15, Theorem 11], the same condition Suzuki quotes for density of
   `D(M)`), so the constant is `0` and `F = 0`.

**Entry point for step 1, computed.**  For `Im w < 0` the Cauchy kernel is the Fourier transform of
an explicit one-sided exponential:

```text
𝖥 (fun t => if t < 0 then (-2πi) · exp (2πi w t) else 0) (ξ) = 1/(ξ - w),
```

since `∫_{-∞}^{0} e^{2πiwt} e^{-2πitξ} dt = 1/(2πi(ξ - w))` (convergent at `-∞` exactly because
`Im w < 0`).  Hence `1/(· - w) ∈ hardyL2` for `Im w < 0`, and `1/(· - w) ∈ hardyL2ᗮ` for
`Im w > 0`.  With that, `∫ G(x)/(x - w) dx = ⟪1/(· - w̄), G⟫` is the reproducing pairing for
`G ∈ hardyL2` when `Im w > 0`, and vanishes when `Im w < 0`.  This is the concrete brick to build
first; everything in step 1 rests on it.

**A dead end, recorded so it is not retried.**  Writing `G = Θ · conj g` with `g ∈ H²` gives
`conj(A/E) · G = (A/E) · conj g`, which is a product of an `H^∞` function with an *anti*-analytic
one — so the orthogonality relations do not become a statement about a single analytic function,
and the naive contour argument does not close.  The completeness really does need Clark theory or
the Krein route.

**What is genuinely missing**: steps 1, 3, 4.  Step 3 is a Phragmén--Lindelöf/Krein argument, step
4 a de Branges-space fact; neither is in the corpus (searched: no Clark theory, no `H(E)`-membership
criteria beyond what this card built).  Step 1 is the most tractable and should be attempted first,
since it is the only one needing new analytic input rather than imported theory.

## Kernel totality in `hardyL2ᗮ` — argument fully worked out, ready to implement

Goal: if `F ∈ L²(ℝ)` satisfies `⟪k_v, F⟫ = 0` for every `v` with `Im v > 0`, then `F ∈ hardyL2`.

1. Split `F = P F + Q F` along the closed subspace `hardyL2`.  Since `k_v ∈ hardyL2ᗮ`
   (`cauchyKernel_mem_hardyL2_orthogonal`), `⟪k_v, F⟫ = ⟪k_v, Q F⟫`, so `Q F ⊥ k_v` for all `v`.
2. `Q F ∈ hardyL2ᗮ = 𝖥 halfLineL2` (`hardyL2_orthogonal`), so `Q F = 𝖥 d` with `d` on `(0,∞)`.
3. **Datum of the kernel.**  For `Im w < 0` write `v = conj w`, so `Im v > 0`.  Then
   `k_v = star (k_w)` (`star_cauchyKernelLp`), `k_w = 𝖥 (cauchyDatum w)`
   (`cauchyKernel_mem_hardyL2`), and `star (𝖥 g) = 𝖥 (l2Reflection (star g))` (from
   `star_fourier_star` and `l2_fourier_reflection`).  Hence `k_v = 𝖥 e` with

   ```text
   e(s) = (2πi) · exp (2πi (conj w) s) · 1_{s>0},
   ```

   whose modulus is `2π exp (-2π Im(conj w) s)` — decaying, since `Im (conj w) > 0`.
   *(Sign check: an earlier pass wrote `exp(-2πi (conj w) s)` here, which grows on `(0,∞)` and
   cannot be an `L²` datum.  The correct exponent is `+2πi (conj w) s`.)*
4. **Plancherel.**  `⟪k_v, F⟫ = ⟪e, d⟫ = (-2πi) ∫_{s>0} d(s) exp(-2πi w s) ds
   = (-2πi) · laplaceRay d (2πi w)`.
5. As `w` runs over `Im w < 0`, `u = 2πi w` runs over `Re u > 0` (`Re (2πi w) = -2π Im w`).  So the
   hypothesis says `laplaceRay d` vanishes on the right half-plane, whence `d = 0` by
   `ae_eq_zero_of_laplaceRay_eq_zero`, so `Q F = 0` and `F = P F ∈ hardyL2`.

Applying this with `F = F_γ` (whose Cauchy transform vanishes below the axis by
`integral_eq_zero_of_upperHalfPlane_farDecay` applied to `F_γ(z)/(z - conj v)`) gives
`F_γ ∈ hardyL2`, and `mem_suzukiModelSpace_iff_conj` then gives `F_γ ∈ K(Θ)`.

## Log
- 2026-08-23 — **Half-line Laplace injectivity CLOSED**
  (`HTGeometry.LaplaceRayInjective.ae_eq_zero_of_laplaceRay_eq_zero`): an `L²` datum on the
  positive ray whose Laplace transform vanishes on the open right half-plane is zero.  Only one
  vertical line is needed — on `Re w = 1` the Laplace transform is `𝖥` of the datum damped by
  `e^{-x}` (`coeFn_fourierTransform_rayDamp`, already in the corpus), so vanishing there kills the
  damped datum by injectivity of the `L²` Fourier transform, and the damping factor never vanishes.

  **This is the missing ingredient for kernel totality**, hence for `F_γ ∈ hardyL2` by a route that
  avoids the rotation/dilation bookkeeping entirely:
  * `⟪k_v, F⟫ = ∫ F(x)/(x - conj v) dx` for the Cauchy kernels, and for `Im v > 0` the point
    `conj v` lies *below* the axis, so this integral vanishes for `F = F_γ` by the half-plane
    Cauchy theorem (`integral_eq_zero_of_upperHalfPlane_farDecay` applied to
    `F_γ(z)/(z - conj v)`, which is holomorphic on the closed half-plane and `O(‖z‖^{-2})`);
  * the kernels `{k_v : Im v > 0}` are total in `hardyL2ᗮ`: a datum orthogonal to all of them has
    vanishing Laplace transform on a half-plane after the substitution `s = -t`, hence is zero;
  * therefore `F_γ ⊥ hardyL2ᗮ`, i.e. `F_γ ∈ (hardyL2ᗮ)ᗮ = hardyL2`.

  The rotation route (`SuzukiDslopeRotated`) remains valid and is kept, but this second route is
  shorter and needs no dilation lemma.

- 2026-08-23 — **`F_γ` is an analytic Hardy function of the half-plane CLOSED**
  (`SuzukiDslopeRotated.isHalfPlaneHardy_suzukiRotatedDslope`): rotating by `w ↦ i w` carries the
  upper half-plane to the right half-plane, and all three clauses of `IsHalfPlaneHardy` hold for
  `suzukiRotatedDslope γ` with bound `C²`.

  Holomorphy transports along the rotation; the two line clauses come from the height-free Cauchy
  profile, transported across `rayLine σ ξ = σ + 2πξ i`.  The `2π` in that parametrisation rescales
  the mass by `(2π)^{-1}` (via `Measure.integral_comp_mul_left`), which is exactly what turns the
  bound `2C²π` into `C²`.

  **Paley--Wiener now applies to `F_γ`.**  With `hardyDatumLp_mem_halfLineL2` its datum is on the
  positive ray, and the two convergence results (`tendsto_dampedDatumLp`, `tendsto_dslope_lineLp`)
  identify the same `L²` limit from the analytic and boundary sides.  Uniqueness of limits then
  gives `l2Reflection (F_γ|_ℝ) ∈ 𝖥 halfLineL2 = hardyL2ᗮ`, and undoing the reflection with
  `l2_fourier_reflection` gives `F_γ|_ℝ ∈ hardyL2`.

- 2026-08-23 — **`F_γ` attains its boundary values in `L²` CLOSED**
  (`SuzukiDslopeBoundaryLimit.tendsto_dslope_lineLp`): along any sequence of heights tending to
  zero, the line restrictions of `F_γ` converge in `L²(ℝ)` to the restriction to the real axis.

  Dominated convergence: pointwise convergence because `F_γ` is holomorphic — hence continuous — at
  every point of the *closed* half-plane, and the uniform Cauchy profile dominates the differences
  (constant `4` absorbing the triangle inequality, via `‖a-b‖² ≤ 2(‖a‖²+‖b‖²)`).

  **Status of `F_γ ∈ hardyL2`.**  Both halves of the identification are now available:
  the *analytic* side (`IsHalfPlaneHardy` hypotheses: holomorphy, `memLp_dslope_line`,
  `integral_norm_sq_dslope_line_le`) and the *boundary* side (`tendsto_dslope_lineLp`, plus the
  Paley--Wiener bridge `lineRestriction_eq_fourier_dampedDatum` + `tendsto_dampedDatumLp`).  What
  joins them is the rotation `G w := F_γ (i w)`, under which `Re w > 0 ↔ Im (i w) > 0` and the
  boundary function is `ξ ↦ F_γ(-ξ)`; the reflection is then undone by `l2_fourier_reflection`
  together with `map_l2Reflection_lowerHalfLineL2`, since
  `l2Reflection (𝖥 halfLineL2) = 𝖥 lowerHalfLineL2 = hardyL2`.

- 2026-08-23 — **The line mass of `F_γ` CLOSED** (`SuzukiDslopeLineMass`): for every horizontal
  line in the closed upper half-plane,
  * `memLp_dslope_line` — `F_γ` is square-integrable along the line;
  * `integral_norm_sq_dslope_line_le` — `∫ ‖dslope (A/E) γ (x+iy)‖² dx ≤ 2C²π`, **independent of
    the height `y`**.

  These are exactly the two analytic hypotheses of `IsHalfPlaneHardy`; holomorphy on the closed
  half-plane was already available.  Supporting lemmas added: `continuous_dslope_line`,
  `integrable_lineMajorant`, `integral_lineMajorant`.

  **What is left for `F_γ ∈ hardyL2`**: only the rotation `w ↦ i w` carrying the corpus's
  right-half-plane predicate to the upper-half-plane setting used here, and then the boundary
  bridge.  After that, `mem_suzukiModelSpace_iff_conj` upgrades it to `F_γ ∈ K(Θ)`, which closes
  the containment half of Prop 4.1 and the `V(0) ≠ 0` half of Rmk 5.2.

- 2026-08-23 — **The uniform line majorant for `F_γ` CLOSED** (`SuzukiDslopeLineMajorant`):

  ```text
  ‖dslope (A/E) γ z‖² ≤ 2C² / (1 + (Re z - Re γ)²)   on the closed upper half-plane, for C ≥ 1.
  ```

  Near `γ` the uniform bound binds, far away the reciprocal-distance bound does, and `C ≥ 1`
  (supplied by `exists_one_le_bound_dslope`) is exactly what makes the two regimes meet.  The
  profile is independent of the height of the line, so integrating it bounds the mass of `F_γ` on
  every horizontal line by `2C²π` at once — whereas `1/‖z-γ‖` alone would give `π/y`, useless at
  the boundary.

  **Remaining for `F_γ ∈ hardyL2`**: integrate the majorant (`integral_inv_one_add_sq` after a
  translation) to get the `MemLp` and mass hypotheses of `IsHalfPlaneHardy` for the rotated `F_γ`,
  then apply the boundary bridge.  The only non-mechanical part left is the rotation `w ↦ i w`
  between the corpus's right-half-plane predicate and the upper-half-plane setting here.

- 2026-08-23 — **`F_γ` is bounded on the closed upper half-plane** (`SuzukiDslopeBounded`):
  `norm_dslope_suzukiHalfInner_le_inv` (`‖dslope (A/E) γ z‖ ≤ 1/‖z-γ‖` off `γ`) and
  `exists_bound_dslope_suzukiHalfInner` (a uniform bound, from that plus continuity on the compact
  part within distance one of `γ`).  Together: `‖F_γ‖ ≤ min (C, 1/‖z-γ‖)`.

  **Why this matters for the `F_γ ∈ K(Θ)` gap.**  That min-bound makes
  `∫ ‖F_γ(x+iy)‖² dx ≤ 2C² + 2` uniformly in `y > 0`, which is exactly the mass hypothesis of
  `IsHalfPlaneHardy`.  With holomorphy on the closed half-plane (already proved) the rotated `F_γ`
  is therefore an analytic Hardy function, and the boundary bridge
  (`lineRestriction_eq_fourier_dampedDatum` + `tendsto_dampedDatumLp`) turns that into
  `F_γ ∈ hardyL2`.  The second half of membership, `Θ · conj F_γ ∈ hardyL2`, then follows from
  `mem_suzukiModelSpace_iff_conj` applied to the same data.

  Remaining for the containment: the rotation bookkeeping `w ↦ i w` between the corpus's
  right-half-plane predicate and the upper-half-plane setting used here, and the `L²`-line estimate
  itself.

- 2026-08-23 — **Remark 5.2's eigenvector reduction CLOSED** (`SuzukiVZeroInvolution`):
  `suzukiKFun_mem_suzukiV0` (`V(0)` is `K`-invariant, immediate from `K ∘ K = id`, since membership
  of `f` in `K L²` exhibits `K f` as the datum it came from) and `exists_suzukiK_eigenvector` (a
  nonzero element of `V(0)` yields an eigenvector of `K` in `V(0)` with eigenvalue `±1`, because
  `f + Kf` and `f - Kf` cannot both vanish).

  **A gap in the Prop 4.1 bookkeeping, now recorded.**  What is proved is that `{F_γ}` is
  orthonormal *in `L²(ℝ)`*; membership `F_γ ∈ K(Θ)` is **not** yet proved, and Suzuki's statement is
  about an orthonormal basis *of `K(Θ)`*.  The other half of Remark 5.2 (`V(0) = {0}` would falsify
  RH, because `A/(z-γ) ∈ H(E)`) is exactly that missing membership, since `E · F_γ` is a constant
  multiple of `A/(z-γ)`.  So `F_γ ∈ K(Θ)` should be proved before completeness is attempted.

- 2026-08-23 — **The Cauchy transform layer CLOSED** (`CauchyTransformHardy`):
  * `star_cauchyKernelLp` — conjugation carries the kernel at `w` to the kernel at `conj w`;
  * `cauchyKernel_mem_hardyL2_orthogonal` — kernels *above* the axis lie in `hardyL2ᗮ`
    (from `map_star_hardyL2` plus the previous item);
  * **`integral_cauchyTransform_eq_zero`** — `∫ G(x)/(x - w) dx = 0` for `G ∈ hardyL2` and
    `Im w < 0`, the boundary form of Cauchy's theorem for `H²`.

  The pairing identity `∫ G(x)/(x - w) dx = ⟪1/(· - conj w), G⟫` is the content: it turns the
  Cauchy transform into a Hilbert-space inner product against a kernel whose side of the axis is
  now known.

  **Step 1 of the completeness route is analytically complete.**  What is left in step 1 is the
  boundary passage `w → γ`: the reproducing pairing at `w ∈ ℂ₊` has to be pushed to the real points
  `γ ∈ Γ`, where `F_γ` is the boundary kernel.  Steps 3 and 4 (Krein growth, `A ∉ H(E)`) are
  unchanged and remain imported theory.

- 2026-08-23 — **`cauchyKernel_mem_hardyL2` CLOSED**: for `Im w < 0`, the kernel `ξ ↦ 1/(ξ - w)`
  is in `hardyL2`.  The `Lp`-level lift went through
  `HTGeometry.L2FourierIntegralBridge.coeFn_fourierTransform_ae_eq_fourierIntegral` (its
  integrability hypothesis is met — the datum is in `L¹ ∩ L²`) composed with
  `Real.Lp.fourierTransform_apply`, plus `memLp_cauchyKernel` (square-integrability of the kernel,
  by comparison with `integrable_inv_one_add_sq` after an affine change).

  Step 1 of the completeness route now has its analytic input.  What remains of step 1 is the
  pairing identity `∫ G(x)/(x - w) dx = ⟪1/(· - w̄), G⟫` and the passage `w → γ` to the boundary,
  which turns orthogonality to every `F_γ` into `F(γ) = 0`.

- 2026-08-23 — **The Cauchy-kernel brick BUILT** (`CauchyKernelHardy`), the entry point recorded
  for step 1 of the completeness route:
  * `cauchyDatum w` — the one-sided exponential `1_{(-∞,0)}(t) · (-2πi) exp(2πi w t)`;
  * `integrable_cauchyDatum`, `memLp_cauchyDatum` — integrable and square-integrable exactly
    because `Im w < 0` makes the exponent decay at `-∞` (rate `cauchyRate w = -2π Im w > 0`);
  * `cauchyDatum_mem_lowerHalfLineL2` — the datum sits on the negative ray, i.e. in the datum
    subspace of `hardyL2`;
  * **`fourierIntegral_cauchyDatum`** — `𝓕 (cauchyDatum w) ξ = 1/(ξ - w)`, via
    `integral_exp_mul_complex_Iic` after collapsing the two exponentials.

  **Remaining plumbing for step 1**: lift the classical identity to the `Lp` level with
  `coeFn_fourierTransform_ae_eq_fourierIntegral` (the datum is in `L¹ ∩ L²`, so the hypothesis is
  met), concluding `1/(· - w) ∈ hardyL2` for `Im w < 0` and `∈ hardyL2ᗮ` for `Im w > 0`.  Then
  `∫ G(x)/(x - w) dx = ⟪1/(· - w̄), G⟫` is the reproducing pairing, which is what carries
  orthogonality to every `F_γ` into `F(γ) = 0`.

- 2026-08-23 — **The Clark measure of `Θ_ξ` identified** (`SuzukiClarkMeasure`), i.e. both
  ingredients of Suzuki eq. (2.8) for the Hedenmalm pair:
  * `suzukiThetaMero_ofReal_eq_neg_one_iff` — `σ(Θ_ξ) = {x ∈ ℝ | A(x) = 0}`, the real Xi divisor,
    multiple zeros included;
  * `clarkWeight_suzukiThetaMero` — `2π/|Θ'(γ)| = π m_γ`, from the derivative law of eq. (4.1).

  **A correction to the earlier `suzukiThetaSymbol`.**  That symbol was normalized to `1` at the
  zeros of `E` to make it unimodular everywhere.  For the multiplication operator that is harmless
  (the zeros are a null set), but it gives the *wrong pointwise value* on `σ(Θ)`: the true
  meromorphic `Θ` has the removable value `-1` at a multiple zero of `A`, not `1`.  Writing
  `Θ = 2(A/E) - 1` (`suzukiThetaMero`) fixes this, since `A/E` already carries the correct
  removable value there.  `suzukiThetaMero_ae_eq_symbol` records that the two agree a.e., so the
  model space is unchanged.

  **A mathematical observation that focuses the remaining work.**  For `Θ_ξ` the Makarov--Poltoratski
  restriction isometry says `‖F‖²_{L²(ℝ)} = ∑_γ π m_γ |F(γ)|²` for `F ∈ K(Θ)`.  Via eq. (4.2)
  (`F_γ(γ) = 1/√(m_γ π)`) that is *exactly* Parseval for the family `{F_γ}` — so MaPo Theorem 2.1
  and the completeness half of Proposition 4.1 are the same statement here.  Everything still open
  in §5 therefore reduces to that single target, which is genuine Clark theory.

- 2026-08-23 — **`H(E)` BUILT and the second half of Lemma 5.1 CLOSED**
  (`SuzukiDeBrangesSpace`).  `MemDeBranges F` is Suzuki's literal condition — `F` entire with `F/E`
  and `F^♯/E` in `H²` — and

  ```text
  memDeBranges_iff_mem_suzukiModelSpace :  F ∈ H(E)  ⟺  F/E ∈ K(Θ).
  ```

  The whole argument is boundary algebra, no analytic continuation: on `ℝ`, `F^♯ = conj F` and
  `E^♯ = conj E`, so `F^♯/E = Θ · conj(F/E)`, and `Θ · conj G ∈ H²` is exactly `G ∈ (Θ H²)^⊥`.
  The supporting Hilbert-space step is `mem_suzukiModelSpace_iff_conj`
  (`G ∈ K(Θ) ↔ G ∈ H² ∧ Θ · conj G ∈ H²`), which rests on `map_star_hardyL2` and
  `thetaMul_star_thetaMul_star`.

  Also proved: `ae_xiHedenmalmDeBrangesE_ofReal_ne_zero` — `E` is a.e. nonzero on the real axis,
  unconditionally, because `E(x) = 0` forces `XiC(x) = 0` and the real Xi zeros are countable.

  **Still needed for §5's remaining statements**: the Makarov--Poltoratski restriction isometry
  (eq. 2.8) `K(Θ) → L²(μ_Θ)`, which requires the Clark measure `μ_Θ`.  That is the next
  construction.

- 2026-08-23 — **The analytic-to-boundary bridge COMPLETE** (`HalfPlaneHardyBoundary`).
  `tendsto_dampedDatumLp`: along any positive null sequence `σ n → 0`, the damped datum converges
  in `L²(ℝ)` to the datum itself.  Combined with `lineRestriction_eq_fourier_dampedDatum`, the
  boundary values of a right-half-plane Hardy function are exactly `𝖥` of its Paley--Wiener datum,
  which lies in `halfLineL2` — i.e. they fill `𝖥 halfLineL2 = hardyL2ᗮ`.

  Dominated convergence, with the bound `|e^{-σx} - 1|² ≤ 1` valid on the support of the datum
  (which vanishes for `x < 0`), so the dominating function is `‖d‖²` itself.  mathlib's
  `tendsto_Lp_finite_of_tendsto_ae` was not usable — it assumes `IsFiniteMeasure` — so the
  argument runs through `norm_sq_lp_eq_integral` (`‖f‖²_{L²} = ∫ ‖f x‖²`, also added here) and the
  ordinary dominated convergence theorem.

  **`H(E)` is now unblocked**: with the boundary realization in hand, `H(E)` can be defined as the
  entire functions `F` with `F/E`, `F^♯/E` in `hardyL2`, and Lemma 5.1's second half
  (`H(E) = E · 𝖥(V(0))`) plus the isometry `K(Θ) → H(E)` follow from `map_fourier_suzukiV0`.

- 2026-08-23 — **The analytic-to-boundary bridge for the half-plane Hardy space, first half**
  (`HalfPlaneHardyBoundary`).  Two theorems:
  * `hardyDatumLp_mem_halfLineL2` — the Paley--Wiener datum of an `IsHalfPlaneHardy` function is a
    genuine `L²(ℝ)` vector lying in `halfLineL2`.  (The corpus only had `MemLp` on the *restricted*
    measure `volume.restrict (Ioi 0)`; globalizing it uses `memLp_indicator_iff_restrict` together
    with `hardyDatum_ae_zero_of_neg`.)
  * `lineRestriction_eq_fourier_dampedDatum` — the restriction of the Hardy function to the line
    `Re w = σ` is `𝖥` of the datum damped by `e^{-σx}`.

  **Remaining half**: `dampedDatumLp F hF hσ → hardyDatumLp F hF` in `L²` as `σ → 0⁺`.  This is
  dominated convergence: `|e^{-σx} - 1|² |d(x)|² ≤ |d(x)|²` since the datum vanishes for `x < 0`,
  and the integrand tends to `0` pointwise.  With it, the boundary values of a right-half-plane
  Hardy function are exactly `𝖥 halfLineL2 = hardyL2ᗮ`, which is what `H(E)` needs.

- 2026-08-23 — **Suzuki Lemma 5.1 CLOSED** (`SuzukiModelSpaceConjugation.map_fourier_suzukiV0`):
  `𝖥(V(0)) = K(Θ)`, together with eq. (5.1)'s involution `K` (`suzukiKₛₗ`,
  `suzukiKFun_suzukiKFun : K ∘ K = id`) and eq. (5.2) at `t = 0` (`suzukiV0`).

  The chain: `map_star_hardyL2` proves `conj(H²) = (H²)^⊥` from `star_fourier_star` plus the fact
  that reflection exchanges the two datum rays (`map_l2Reflection_lowerHalfLineL2`) and
  conjugation fixes each (`map_star_lowerHalfLineL2`); then `Submodule.map_inf` with injectivity of
  `𝖥` and `suzukiModelSpace_eq_inf_map` (eq. 2.7) finish it.  `K S` is a genuine complex subspace
  even though `K` is conjugate-linear, so `suzukiKₛₗ` is built as a `starRingEnd ℂ`-semilinear map
  and `Submodule.map` applies directly.

  Supporting layer added: `lpStar_add`, `lpStar_smul`, `star_star_lp`, `lpStarₛₗ` (conjugation as a
  semilinear map on `L²(ℝ)`), and `l2Reflection_coeFn`.

  **Next in §5**: Lemmas 5.2–5.4 and Theorems 5.5–5.7 need the de Branges space `H(E)` and the
  Makarov--Poltoratski restriction isometry (eq. 2.8).  Neither is in the corpus; both are
  buildable and are the next major construction.

- 2026-08-23 — **The section-5 star/Fourier input CLOSED**
  (`L2FourierConjugation.star_fourier_star`): `star (𝖥 (star f)) = l2Reflection (𝖥 f)` on `L²(ℝ)`,
  proved pointwise on Schwartz functions and extended by density with the
  `L2FourierReflection` pattern.  This is the only genuinely new analytic ingredient the
  Lemma 5.1 reduction needed.

  Two supporting gaps had to be filled first, both recorded in the module docstring:
  * mathlib gives `𝓢(ℝ, ℂ)` no `Star` instance, so `starSchwartz` is built by postcomposing with
    `Complex.conjLIE`; being an isometry it carries every Schwartz seminorm bound across
    unchanged (`LinearIsometry.norm_compContinuousMultilinearMap`);
  * `Lp ℂ 2 volume` has `Star` but no synthesizable `StarAddMonoid`, so `star_sub` and
    `‖star f‖ = ‖f‖` (`norm_lpStar`, `continuous_lpStar`) are proved from `Lp.coeFn_star`.

  **Immediate next step**: `star hardyL2 = hardyL2ᗮ` (conjugation fixes `lowerHalfLineL2`,
  reflection maps it to `halfLineL2`, and `hardyL2ᗮ = 𝖥 halfLineL2` is already proved), then
  define `K` and `V(0)` and conclude Lemma 5.1 from `suzukiModelSpace_eq_inf_map` and
  `thetaUnitary`.

- 2026-08-23 — **Theorem 1.2 (= Theorem 4.5) CLOSED, both directions**
  (`SuzukiWeilFormNormCriterion.riemannHypothesis_iff_normSq_suzukiPHat_deriv`):

  ```text
  RH  ⟺  ‖𝒫̂_{Dψ}‖²_{L²} = π ⟨ψ,ψ⟩_W   for every smooth compactly supported ψ.
  ```

  The corpus already owned Su22 Proposition 3.1 as
  `SuzukiScrewWeilIdentity.suzuki_proposition_three_one`
  (`suzukiScrewSmoothForm ψ₁.toDerivativeZeroMean ψ₂.toDerivativeZeroMean =
  suzukiWeilDistribution (suzukiHermitianConvolution ψ₁ ψ₂)`), so the forward direction is
  Theorem 4.4 composed with it.

  For the converse the only missing piece was surjectivity of `D` onto smooth zero-mean tests.
  The corpus's `suzukiSmoothIntegralPrimitive` (in `SuzukiFriedrichsExtension`) already has
  smoothness, compact support and `deriv = φ`; the one adjustment is raising the aperture from
  `a` to `a + 1`, since that construction wants the support inside an *open* interval while
  `SuzukiSmoothZeroMeanTest` gives a closed one.  `suzukiScrewSmoothForm_congr` then transports
  the form across the aperture change, which is legitimate because the form depends only on the
  underlying function.

  Section 4.3 is therefore closed except Corollary 4.6, which needs Bombieri--Lagarias §4
  (`⟨g_n,g_n⟩_W ≥ 0 for all n ⟹ RH`) — not in the corpus, and not derivable from what is.

- 2026-08-23 — **Theorem 4.4 CLOSED, both directions**
  (`SuzukiPHatIsometry.riemannHypothesis_iff_normSq_suzukiPHat`):

  ```text
  RH  ⟺  ∀ a > 0, ∀ φ : SuzukiSmoothZeroMeanTest a,  ‖𝒫̂_φ‖²_{L²} = π (⟨φ,φ⟩_{G_g}).re
  ```

  Forward: `suzukiPHatConj_eq_tsum` puts `𝒫̂_φ` in the same shape as `𝔖_t`
  (`i · conj(A/E) ·` Cauchy series), so `integral_conj_of_hasSum` gives
  `‖𝒫̂_φ‖² = π ∑'_q ‖b_q(φ)‖²`; `tsum_normSq_suzukiPHatCoefFn` matches that against the ray energy
  of `⟨φ,φ⟩_{G_g}` using the divisor reflection `γ ↦ -γ` (the two ray integrals are conjugate
  because every `γ` is real under RH).

  Converse: the hypothesis makes `(⟨φ,φ⟩_{G_g}).re = ‖𝒫̂_φ‖²/π ≥ 0` on exactly the test class of
  Su22 Theorem 1.3, so `riemannHypothesis_of_suzukiSmoothTestFormNonnegative` closes it.  Suzuki's
  contradiction argument via Yoshida's Lemma 1 is not needed.

  New modules: `SuzukiScrewTestRayEnergy` (the unconditional ray-energy identity for
  `⟨φ,φ⟩_{G_g}`) and `SuzukiPHatIsometry`; plus `hasSum_supportCauchy` in `SuzukiScrewLine` (the
  general divisor-support regrouping) and `integral_conj_of_hasSum` / `memLp_of_hasSum` in
  `SuzukiCauchyIsometry`.  All capstones axiom-clean.

  **Next**: Theorem 4.5 (`‖ψ‖₀² = ⟨ψ,ψ⟩_W`) and Theorem 1.2 follow by taking `φ = Dψ` and using
  Su22 Proposition 3.1 (`⟨Dψ₁,Dψ₂⟩_{G_g} = ⟨ψ₁,ψ₂⟩_W`); check the corpus for that relation before
  building it.  Corollary 4.6 additionally needs Bombieri--Lagarias §4, not in the corpus.

- 2026-08-23 — **Section 4.3 route fixed and its hardest new computation CLOSED.**
  `SuzukiScrewTestRayEnergy.suzukiScrewSmoothForm_eq_tsum` proves, **unconditionally**,

  ```text
  ⟨φ,φ⟩_{G_g} = ∑'_q  (∫ (e^{iγ_q t} - 1) conj(φ(t)) dt) · (∫ (e^{-iγ_q u} - 1) φ(u) du) / γ_q²
  ```

  for every `φ : SuzukiSmoothZeroMeanTest a`, by feeding the exponential zero series for `G_g`
  into the double integral and interchanging twice (`integral_tsum_of_summable_integral_norm`,
  inner in `u` then outer in `t`), with majorant `(e^{|a|/2}+1)‖φ‖₁ · ‖γ_q‖^{-2}`.

  Also added the general form of the isometry, `SuzukiCauchyIsometry.integral_conj_of_hasSum` and
  `memLp_of_hasSum`, so that both `𝔖_t` and `𝒫̂_φ` specialize from one theorem.

  **Remaining for Theorem 4.4**: identify `‖𝒫̂_φ‖²` with `π ∑'_q ‖b_q(φ)‖²` via
  `suzukiPHatConj_eq_tsum` and `integral_conj_of_hasSum` (structurally identical to what was done
  for `𝔖_t`), then match `∑'_q ‖b_q‖²` with the ray energy above using the divisor reflection
  `γ ↦ -γ`.  The `⟸` half is `riemannHypothesis_of_suzukiSmoothTestFormNonnegative`, already in
  the corpus — Yoshida's Lemma 1 is not needed.

- 2026-08-23 — **Theorem 4.2 and Corollary 4.3 CLOSED.**  The route in the section above was
  executed with one change: the tail bound uses an almost-everywhere convergent subsequence of the
  `L²` limit rather than Fatou, which is shorter (`tendstoInMeasure_of_tendsto_Lp` +
  `TendstoInMeasure.exists_seq_tendsto_ae`).

  New modules:
  - `SuzukiCauchyGram`: `xiRealSpectralPointSupport`, `xiSupportMult`, the real spectral point and
    multiplicity at each support element under RH, and `integral_halfInnerEnergy_kernel_pair` — the
    Gram matrix of the boundary Cauchy kernels `1/(x-γ_ρ)` against the energy `|A/E|²`: zero off
    the diagonal, `π/m_ρ` on it.
  - `SuzukiCauchyIsometry`: an enumeration `xiSupportEnum : ℕ ≃ XiDivisorSupport` (countable and
    infinite are both corpus theorems), the `L²` vectors `suzukiEnergyKernel`, their Gram identity,
    the finite orthogonal-sum formula, `cauchySeq_suzukiCauchyPartial`, `coeFn_eq_of_tendsto_ae`
    (the subsequence identification), `exists_lp_of_hasSum`, and `inner_of_tendsto`.
  - `SuzukiScrewLine`: `suzukiPtSupportCoef` and the regrouping of `P_t` over the divisor support,
    square-summability of the coefficients, `integral_conj_suzukiEnergyPt`,
    **`inner_suzukiFrakSFull_eq_pi_mul_screwKernel`** (Theorem 4.2),
    **`norm_sq_suzukiFrakSFull_eq`** (`‖𝔖_t‖² = 2π Ψ(t)`), and
    **`riemannHypothesis_iff_norm_sq_suzukiFrakSFull`** (Corollary 4.3).

  All capstones axiom-clean.

  **One recorded shortfall**: Suzuki's Corollary 4.3 assumes the identity only on `[t₀, ∞)`.  The
  corpus owns Su22 Theorem 1.7 (`riemannHypothesis_iff_suzukiPsiPointwiseNonnegative`) which needs
  the whole half-line, so the `t₀ > 0` refinement is stated with `t₀ = 0`.  Closing the gap needs
  Su22 Theorem 11.1.

- 2026-08-23 — **Proposition 4.1 orthonormality CLOSED, and Su22 eq. (1.9) CLOSED unconditionally.**

  **New reusable analysis (HTGeometry).**
  - `UpperHalfPlaneCauchyVanishing`: `integral_eq_zero_of_upperHalfPlane_decay`,
    `exists_global_decay_bound_of_farDecay`, `integral_eq_zero_of_upperHalfPlane_farDecay`,
    `integrable_ofReal_of_decay`, `integrable_ofReal_of_farDecay`.  A function holomorphic at
    every point of the *closed* upper half-plane and `O(‖z‖^{-2})` in the far field integrates
    to zero over `ℝ`.  Square contour `[-R,R] × [0,R]`; top and both sides are `O(1/R)`.
    This replaced the planned Paley–Wiener rotation entirely — no `H²` theory needed.
  - `DslopeLocalFactor`: `dslope_eventuallyEq_of_localFactor`,
    `differentiableAt_dslope_of_localFactor`,
    `differentiableAt_dslope_of_eventually_differentiableAt`.

  **New RHTower layers.**
  - `SuzukiScrewKernelExponentialSeries`: **Su22 (1.9)** as `suzukiScrewKernel_eq_tsum`,
    `G_g(t,u) = ∑_γ m_γ (e^{iγt}-1)(e^{-iγu}-1)/γ²`, **unconditional**.  The strip bound
    `|Im γ| < 1/2` bounds the exponentials; symmetrizing over `xiZeroCopyReflectEquiv` turns the
    exponential sum into the corpus's cosine series `xiScrewDivisor`.
  - `SuzukiHalfInnerHalfPlane`: `‖A/E‖ ≤ 1` on the closed half-plane under RH;
    `‖A/E‖² = Re(A/E)` on `ℝ` (the analytic form of `|Θ| = 1`); `A/E` holomorphic at every point
    of the closed half-plane.
  - `SuzukiHalfInnerLocalFactor`: the peeled factorization `A/E = (z-γ)·(h/P)` on a whole
    neighbourhood of a zero (both sides of the axis), hence `dslope (A/E) γ` and its iterate are
    holomorphic on the closed half-plane, with the value formulas.
  - `SuzukiFGammaOffDiagonal`: `integral_normSq_suzukiHalfInner_div_pair` — the off-diagonal
    integral `∫ |A/E|²/((x-γ)(x-δ)) = 0`.
  - `SuzukiFGammaDiagonal`: `integral_normSq_suzukiHalfInner_div_sq = π/m`.  The genuine simple
    pole is removed by subtracting `(1/m)/(z-γ+i)`, whose pole sits at `γ-i` below the axis and
    whose value at `γ` matches the residue `(A/E)'(γ) = -i/m`; taking real parts turns it into
    the Cauchy kernel `(1/m)/((x-γ)²+1)`, integral `π/m`.  No indented contour, no p.v.
  - `SuzukiFGammaOrthonormal`: `suzukiFGammaFun`, **eq. (4.2)** (`suzukiFGammaFun_self`,
    `suzukiFGammaFun_eq_zero_of_ne`), `memLp_suzukiFGammaFun`, `suzukiFGammaLp`,
    **`inner_suzukiFGammaLp = 0`** and **`norm_suzukiFGammaLp = 1`**.

  All capstones axiom-clean (`propext, Classical.choice, Quot.sound`).

  **Still open in Prop 4.1**: completeness (that `{F_γ}` *spans* `K(Θ)`), which is the only part
  Theorem 1.1's surjectivity needs.  Theorem 4.2 needs only orthonormality + Su22 (1.9), both now
  in hand, plus the identification of `𝔖_t` with the `F_γ`-series (3.6).
- 2026-08-23 — **Suzuki eq. (4.1) CLOSED** (`hasDerivAt_suzukiHalfInner`), plus the two unconditional steps of Theorem 4.2 (`suzukiFrakSFull_zero`, `summable_norm_sq_suzukiScrewCoeff`).  Remaining for Prop 4.1: orthonormality of `{F_γ}`.  **Route found**: `⟪F_γ,F_δ⟫ = (√(m_γm_δ)/π)∫ W/((x-γ)(x-δ))` with `W = A²/|E|² = (1+Re Θ)/2`, so everything reduces to `∫_ℝ (1+Θ(x))/((x-γ)(x-δ))dx = 0` (off-diagonal) and the residue `Θ'(γ) = -2i/m_γ` (diagonal, now proved).  The vanishing integral is `∫ u` for `u = 2(A/E)/((z-γ)(z-δ))`, holomorphic and `O(1/|z|²)` on `ℂ₊` under RH — so `u|_ℝ ∈ H²`, hence `û` is supported in `[0,∞)`, hence `û(0) = ∫u = 0`.  The corpus's `PaleyWienerHalfPlane` supplies the `H²` step after rotating `z = iw`.
- 2026-08-23 — **`K(Θ)` BUILT** (`SuzukiModelSpace`, `SuzukiModelSpaceOrthogonal`): `H²` of the upper half-plane as a closed subspace of `L²(ℝ)`, the unimodular `Θ_ξ` multiplier as a unitary, the model space `K(Θ_ξ) = H² ⊖ ΘH²` closed, and Suzuki eq. (2.7).  This is the first of the three objects the RH-conditional layer needs; `H(E)` and the Makarov–Poltoratski restriction isometry remain.
- 2026-08-23 — **Lemma 3.2 (definiteness) CLOSED** (`eq_zero_of_suzukiPHat_D_ae_zero`), completing the unconditional §3 content.  Chain: a.e. vanishing → ray series zero on admissible reals → identity theorem off the divisor → corpus fibre-sum theorem → `integral_expSlope_mul_conj_D` → `compactFourier (conj ψ)` vanishes at every Xi zero → `suzuki_lemma_two_one` → `ae_eq_zero_of_compactFourier_vanishing`.  Modules `SuzukiWeilRayVectorBridge`, `SuzukiWeilFiberVanishing`, `SuzukiWeilNormDefiniteness`.
- 2026-08-22 — **Anti-duplication catch.**  `finite_xiSpectralPoint_fiber` and the whole fibre-residue step already exist in `RHTower.XiCauchyTransformCompleteness` / `XiWeilPolarization`.  Step 3b(ii) is a bridge to `xiWeilFiberSum_eq_zero_of_re_xiCauchyTransform_eq_zero_on_ball`, not a construction.  See the route section.
- 2026-08-22 — Lemma 3.2 **step 3b(i) closed** (`suzukiPHatRaySum_eq_zero_off_divisor`).  Only the fiber residue 3b(ii) and the Su22 application (4) remain.
- 2026-08-22 — Lemma 3.2 **step 3a closed** (`differentiableAt_suzukiPHatRaySum`): the ray series is holomorphic off the divisor, with the sharp `|z₀-γ_q|/2` dominant.  Remaining: 3b (identity theorem + fiber residue) and 4 (Su22 Lemma 2.1).
- 2026-08-22 — Lemma 3.2 **step 2 closed** (`integral_expSlope_mul_conj_D`): the `D`-pairing collapses each ray to `F(-γ_q)/(z-γ_q)`.  Only the residue extraction (step 3) and the Su22 application (step 4) remain.
- 2026-08-22 — **eq. (3.7) CLOSED** (`suzukiPHatConj_eq_tsum`): the transform expanded over the Xi divisor, multiplicity-exact and absolutely convergent.  This is step 1 of the Lemma 3.2 route.
- 2026-08-22 — **`suzukiFrakSFull` built** and Proposition 1.3 rebased on it, after discovering that the paper's even extension of `𝔖_t` to negative `t` contradicts (3.6)–(3.8): with it, `𝒫̂_{Dψ} ≡ 0` for every *even* `ψ`, so Lemma 3.2 and eq. (1.9) would be false.  Defect recorded under "Source defects found".
- 2026-08-22 — **Proposition 1.3 CLOSED in Lean, unconditionally** (`memLp_suzukiPHat_of_compactSupport`, stated for merely continuous compactly supported `φ`).  Minkowski's integral inequality is not needed: the Prop 1.2 bound is pointwise with an explicit monotone constant, so `‖∫‖ ≤ ∫‖·‖` closes it.  The one real ingredient is joint measurability of the Prop 1.2 model in `(x,t)`.
- 2026-08-22 — **Proposition 1.2 CLOSED in Lean, unconditionally** (`memLp_suzukiFrakS`), by a route that uses *no* Titchmarsh zero-density or `ζ'/ζ` input: the two elementary quotient bounds `|A/E^♯| ≤ 1`, `|A'/E^♯| ≤ 1` on the real axis kill the poles, and a weighted-AM–GM bound gives the Lerch kernel the decay exponent `3/4` (the naive `1/2` would not be square integrable).  Also generalized the corpus's `suzukiFrakP_eq_reg` to `suzukiFrakP_eq_reg_of_re_pos` (hypothesis `‖z‖ < 1/2` weakened to `0 < Re(1/4 - iz/2)`, which the whole real axis satisfies).  All capstones axiom-clean.
- 2026-08-22 — **eq. (7.2) CLOSED in Lean, unconditionally** (`tendsto_suzukiFrakP_vertical`), completing the whole unconditional appendix Theorem 7.1.  Required a new mathlib/corpus gap module: Gauss's digamma difference series off the poles.  Both new capstones axiom-clean.
- 2026-08-22 — created; source inventoried statement by statement; corpus dictionary established.
- 2026-08-22 — **Proposition 3.1 CLOSED in Lean, unconditionally** (`suzukiFrakP_eq_suzukiPtZeroSum`), by the Laplace-matching route: five-block Laplace transform of eq. (1.6), Laplace transform of the Xi-zero series, the corpus explicit formula as the bridge, Laplace determinacy through the exponential Fourier transform, and continuity in `t`.  All capstones axiom-clean.
- 2026-08-22 — L3 started: the Xi-zero-series Laplace transform is closed; the five-block split of eq. (1.6) and the polar/zeta/digamma Laplace transforms are closed.
- 2026-08-22 — L1 (Lerch block) and eq. (7.1) closed in Lean; two sign typos in the printed proof of
  (7.1) recorded; anti-duplication audit run and one duplicate (`suzukiGXi`) removed.


## Completeness of `{F_γ}` — the route, and the layers already built

Suzuki cites [Su23, Prop 3.2], which rests on the Clark/Makarov--Poltoratski isometry
[MaPo05, Thm 2.1] plus density of `𝔇(M)` in `H(E)`.  Formalising Clark's theorem in general would
demand Herglotz/Poisson boundary theory.  It is not needed: for `Θ_ξ` the whole statement reduces to
one *algebraic* identity plus contour integrals of the kind already in the tree.

**The reduction.**  Let `M := closure span {F_γ}` inside `K(Θ)`.
1. `{F_γ}` is orthonormal in `K(Θ)` (done).
2. The reproducing kernels `k_w`, `w ∈ ℂ₊`, lie in `K(Θ)` and are *total* in it (done, see below).
3. `⟪k_w, F⟫ = F(w)` for every `F ∈ K(Θ)` with a holomorphic decaying representative (done).
   Hence `⟪F_γ, k_w⟫ = conj(F_γ(w))` and `‖k_w‖² = k_w(w)`.
4. Parseval for the single vector `k_w`, i.e. `∑_γ |F_γ(w)|² = k_w(w)`, forces `k_w ∈ M`
   (a projection has `‖Px‖² = ∑|⟪e_i,x⟫|²`, so `‖x - Px‖ = 0`).
5. `k_w ∈ M` for all `w` plus totality of `{k_w}` gives `M = K(Θ)`: the complement is orthogonal to
   every `k_w`, hence zero.

**Step 4 is an algebraic identity.**  With `F_γ(z) = √(m_γ/π) i (A/E)(z)/(z-γ)` and
`k_w(w) = (1-|Θ(w)|²)/(4π Im w)`, and `|1+Θ|² = 4|A/E|²`, step 4 says

```text
  ∑_γ m_γ/|w-γ|²  =  (|E(w)|² - |E♯(w)|²) / (4 |A(w)|² Im w).
```

Now `|E|² = |A|² + |A'|² - 2 Im(A' conj A)` and `|E♯|² = |A|² + |A'|² + 2 Im(A' conj A)`, so the
right side is `-Im(A'(w) conj A(w))/(|A(w)|² Im w) = -Im((A'/A)(w))/Im w`.  And the corpus already
owns the multiplicity-exact partial fraction
`logDeriv XiC z = ∑'_q (γ_q⁻¹ - (γ_q - z)⁻¹)` (`logDeriv_XiC_eq_relativeResolventTrace`), whose
imaginary part at real `γ_q` is exactly `-Im(w) ∑_q 1/|w-γ_q|²`.  So step 4 is the imaginary part of
a partial fraction the corpus has already proved — no Clark theory at all.

### Layers landed for this route

| Module | Content |
|---|---|
| `HTGeometry/UpperHalfPlaneCauchyFormula.lean` | Poisson normalisation `∫ dx/((x-a)²+b²) = π/b`; **Cauchy formula** `∫ u(x)/(x-w) dx = 2πi u(w)` for `u` holomorphic and `O(1/|z|)` on the closed upper half-plane, proved by regularising with the mirrored kernel and recognising the difference as a divided slope |
| `RHTower/CauchyKernelTotality.lean` | The Cauchy kernels below the axis are **total** in `(H²)^⊥`: vanishing Cauchy transform on the whole lower half-plane forces membership in `H²`.  Fourier side: the kernel above the axis is `𝖥` of a one-sided exponential, and the pairing becomes a half-line Laplace transform |
| `RHTower/SuzukiFGammaModelSpace.lean` | `F_γ ∈ H²`; `Θ conj(F_γ) = -F_γ` on the axis; hence `F_γ ∈ K(Θ)` and `F_γ` is a `-1`-eigenvector of the Clark conjugation |
| `RHTower/SuzukiModelKernel.lean` | `k_w` and `Θ conj(k_w) = (-i/2π) dslope Θ w`; both Hardy; `k_w ∈ K(Θ)`; the reproducing identity; `⟪k_w,k_v⟫ = k_v(w)`; **totality** of `{k_w}` in `K(Θ)` |

### Completed

| Module | Content |
|---|---|
| `HTGeometry/BesselSaturation.lean` | A saturated Bessel inequality forces orthogonality to everything the family annihilates — replaces the orthogonal-projection argument |
| `RHTower/SuzukiZeroSumIdentity.lean` | `Σ_ρ m_ρ/|w-γ_ρ|² = -Im(logDeriv A(w))/Im w`; the energy identity `Re(A/E) - |A/E|² = -|A/E|² Im(A'/A)`; `k_w(w) = (Re(A/E) - |A/E|²)/(π Im w)`; and hence `Σ_γ |F_γ(w)|² = k_w(w)` |
| `RHTower/SuzukiFGammaBasis.lean` | `⟪k_w, F_γ⟫ = F_γ(w)`; Bessel saturates at `k_w`; completeness; `suzukiFGammaHilbertBasis`; Parseval in `K(Θ_ξ)` |

Proposition 4.1 is closed.  Everything downstream that needed "orthonormal *basis*" is now unblocked.

## Lemma 5.3 closed

`RHTower/SuzukiSpectralRestriction.lean`: `suzukiRestriction` (values on the spectrum),
`hasSum_suzukiClarkWeight_normSq_restriction` (isometry `‖F‖² = Σ π m_γ |F(γ)|²`),
`suzukiRestriction_inj`, `exists_suzukiRestriction_eq` (surjectivity),
`hasSum_expansion_at_spectrum` (the value at `γ_ρ` really is the basis expansion there),
`hasSum_expansion_upper` (the same expansion above the axis is the Cauchy transform), and
`hasSum_suzukiClarkWeight_normSq_restriction_suzukiV0` (the `V(0)` form).

Convention note: the corpus's Fourier transform is unitary, so the identity reads
`‖ψ‖² = Σ_γ π m_γ |ψ̂(γ)|²`; Suzuki's `2‖ψ‖² = ‖S_ψ‖²_{L²(τ)}` is the same statement in his
`‖ψ̂‖² = 2π‖ψ‖²` normalisation.

## The next gate: `H_W`

Every remaining item (Thm 1.1, Cor 1.5, Lem 5.4, Thm 5.5/5.6/5.7, Prop 5.8, §6) needs the Hilbert
space `H_W` — the completion of `C_c^∞(ℝ)` under the Weil hermitian form.  The corpus owns the form
itself: `suzukiWeilDistribution (suzukiHermitianConvolution ψ φ)`, defined as the sum over the Xi
divisor of `suzukiEntireFourier` at the spectral points, i.e. `Σ_q ψ̂(γ_q) conj(φ̂(γ_q))` when the
zeros are real.  What is missing is the space.

Planned layers.

1. **Aperture-free test space.**  The corpus's `SuzukiSmoothCompactTest a` is indexed by an
   aperture, so it is not a vector space; `C_c^∞(ℝ, ℂ)` (smooth with compact support) with its
   `Module ℂ` structure, plus the bridge to each `SuzukiSmoothCompactTest a`, and translation.
2. **The Weil inner product** on that space, sesquilinear, with `⟪ψ,ψ⟫ = Σ_q |ψ̂(γ_q)|²` under RH.
   Positivity is then immediate (real zeros), and definiteness follows from the corpus's
   `suzuki_exponentialType_uniqueness`: `ψ̂` is entire of exponential type and vanishes at every Xi
   zero, hence vanishes identically, hence `ψ = 0`.
3. **`H_W`** as `UniformSpace.Completion` of that pre-Hilbert space (mathlib's
   `Analysis/InnerProductSpace/Completion.lean` supplies the inner product on the completion).
   RH enters as a hypothesis; carry it as `[Fact RiemannHypothesis]` so instances can be declared.
4. **Lemma 5.4** (`H_W ≅ L²(τ)`).  Isometry is (2); the content is *density* of
   `{(ψ̂(γ))_γ : ψ ∈ C_c^∞}` in `ℓ²(m_γ)`.  Elementary route, no Kreĭn theory:
   let `a` be orthogonal to every `S_ψ` and put `b_γ = m_γ conj(a_γ)`.  Applying the hypothesis to
   the translates `ψ(· - t)` gives `Σ_γ b_γ ψ̂(γ) e^{iγt} = 0` for every `t`, and the coefficients
   are absolutely summable (Cauchy--Schwarz against `Σ m_γ |ψ̂(γ)|² < ∞`, itself from
   `|ψ̂(γ)| = O((1+γ²)^{-1})` and `Σ m_γ (1+γ²)^{-2} < ∞`).  Uniqueness of Bohr coefficients then
   forces `b_γ ψ̂(γ) = 0` for every `γ` and every `ψ`; taking `ψ(x) = e^{-iγx}χ(x)` with `χ` a
   nonnegative bump makes `ψ̂(γ) > 0`, so `b = 0`.
5. **Thm 1.1, Cor 1.5, Thm 5.5/5.6/5.7, Prop 5.8, §6** on top.


## `H_W` built

| Module | Content |
|---|---|
| `RHTower/SuzukiWeilTestSpace.lean` | `suzukiTestSubmodule` / `SuzukiTest` — smooth compactly supported functions as a `ℂ`-module, with the bridge to the aperture-indexed `SuzukiSmoothCompactTest`; `suzukiWeilInner`, its spectral form `Σ_q conj(ψ̂(-γ_q)) φ̂(-γ_q)`, summability, sesquilinearity, positivity, and **definiteness** (`eq_zero_of_suzukiTestFourier_eq_zero`, via `suzuki_lemma_two_one` and injectivity of the compact Fourier transform) |
| `RHTower/SuzukiWeilHilbert.lean` | The `InnerProductSpace.Core`, the normed and inner-product instances (under `[Fact RiemannHypothesis]`), and `SuzukiHW` — the completion |
| `HTGeometry/ExponentialSeriesUniqueness.lean` | `bohrSincKernel` and `coeff_eq_zero_of_tsum_cis_eq_zero`: an absolutely convergent exponential series with distinct real frequencies that vanishes identically has zero coefficients.  Mean value over `[-T,T]`; no almost-periodicity theory |

Remaining for Lemma 5.4: the density argument (translation covariance of the spectral values, the
bump with `ψ̂(-γ) > 0`, and the orthogonality computation), then Thm 1.1, Cor 1.5, Thm 5.5/5.6/5.7,
Prop 5.8, §6.


## Lemma 5.4 and Theorem 1.1 closed

| Module | Content |
|---|---|
| `HTGeometry/LinearIsometryCompletion.lean` | Extension of a linear isometry to the completion; surjective when the original had dense range |
| `RHTower/SuzukiTestSpectralDensity.lean` | Translation covariance of the spectral values, the modulated bump with `ψ̂(-γ) > 0`, and the density theorem `eq_zero_of_orthogonal_suzukiTestSpectral` |
| `RHTower/SuzukiWeilTauIsomorphism.lean` | The spectral map `SuzukiWeilTest →ₗᵢ L²(τ)`, its dense range, and **Lemma 5.4** `suzukiWeilTauEquiv : H_W ≃ₗᵢ L²(τ)` |
| `RHTower/SuzukiModelWeilIsomorphism.lean` | **Theorem 1.1** `suzukiModelWeilEquiv : K(Θ) ≃ₗ H_W`, `norm_sq_suzukiModelWeilEquiv` (`‖F‖² = π‖ψ_F‖²`), and `suzukiWeilTauEquiv_suzukiModelWeilEquiv` (the map matches spectral values, so it is the source's `F ↦ ψ_F`) |

Design note: `H_W` is the completion of a *type synonym* `SuzukiWeilTest` rather than of the
submodule itself.  A submodule of `ℝ → ℂ` already carries the product uniformity, and the completion
must be taken with respect to the Weil norm alone.

Still open: Cor 1.5, Cor 4.6 (Bombieri--Lagarias), Thm 5.5/5.6/5.7, Prop 5.8, §6.


## Cor 1.5, Thm 5.5, and the first half of Thm 5.6

| Module | Content |
|---|---|
| `RHTower/SuzukiV0WeilMass.lean` | **Theorem 5.5**: `‖ψ‖² = π‖ψ_F‖²_{H_W}` on `V(0)`, and the composite `V(0) → K(Θ) → H_W` matches spectral values |
| `RHTower/SuzukiWeilNormZero.lean` | `suzukiTestDeriv`; **Theorem 5.6, first half** `‖·‖₀ = ‖·‖_W` so `H_0 = H_W`; and **Corollary 1.5** as the equivalence `riemannHypothesis_iff_normSq_suzukiPHat_suzukiTest` |

Corollary 1.5 turned out to be Theorem 1.4 read on the aperture-free test space: the `L²` mass of
`𝖥⁻¹𝒫̂_{Dψ}` is `‖𝒫̂_{Dψ}‖²` and its spectral values are those of `ψ`, so the two sides of the
source's equality are exactly the two sides of Theorem 1.4.

Still open: `K_0 = K(Θ)` and `V(0) = closure V°(0)` (Thm 5.6), Thm 5.7, Prop 5.8, §6, and Cor 4.6
(Bombieri--Lagarias).

## Route for the rest of Theorem 5.6 (`K_0 = K(Θ)`, `V(0) = closure V°(0)`)

Everything needed is identified; the build is mechanical but long.

1. **Pointwise expansion.**  For a zero-mean test `φ` and a.e. real `x`,
   `suzukiPHat φ x = conj(suzukiPHatConj φ x)` (`suzukiPHat_ofReal_eq_conj`),
   `suzukiPHatConj φ x = i(1+Θ♯(x))/2 · Σ_q rayTerm_q` (`suzukiPHatConj_eq_tsum`),
   `(1+Θ♯(x))/2 = conj(A/E)(x)` (inside `norm_suzukiPHat_ofReal_eq`), and
   `rayTerm φ x q = coefFn φ γ_q · (x-γ_q)⁻¹` (`suzukiPHatRayTerm_eq`).  Conjugating and using that
   the `γ_q` are real gives

   `suzukiPHat φ x = Σ_ρ (-i) m_ρ conj(coefFn φ γ_ρ) · suzukiEnergyKernelFun ρ x`

   by `hasSum_supportCauchy` applied to `c w = conj(coefFn φ w)`.

2. **`L²` expansion.**  `exists_lp_of_hasSum` turns that into an `Lp` element `S` with
   `S = lim suzukiCauchyPartial` and `S = 𝒫̂_φ` a.e.  Each partial sum is a finite combination of
   `suzukiEnergyKernel ρ`, which is a scalar multiple of `F_ρ ∈ K(Θ)`, and `K(Θ)` is closed, so
   `S ∈ K(Θ)`.  This is `range 𝒫̂_D ⊆ K(Θ)`.

3. **The coefficients are the spectral values.**  Integration by parts turns
   `coefFn (Dψ) γ = (∫ (e^{-iγt} - 1) conj(ψ'(t)) dt)/γ` into `i conj(ψ̂(γ))`, so the coefficient of
   `F_ρ` in `𝒫̂_{Dψ}` is `i √(π m_ρ) ψ̂(γ_ρ)` — the source's equation (3.8).

4. **Density.**  Those coefficients are `√(π)` times the spectral sequence of `ψ`, whose range is
   dense in `L²(τ)` by `denseRange_suzukiSpectralMap`.  Hence `closure (range 𝒫̂_D) = K(Θ)`, i.e.
   `K_0 = K(Θ)`, and applying `𝖥⁻¹` (a unitary carrying `K(Θ)` to `V(0)`) gives
   `V(0) = closure V°(0)`.

The remaining items after that are Thm 5.7 (needs the de Branges axioms (dB1)--(dB3) and the
support of `𝖥⁻¹Θ`, i.e. [QXYYY09]), Prop 5.8 (needs the Weil form at *complex* spectral points and
`Σ m_γ |γ|^{-1-δ} < ∞`), §6 (an unbounded self-adjoint operator diagonal in `{F_γ}` — reachable
directly from the Hilbert basis, without de Branges operator theory), and Cor 4.6 (Bombieri--Lagarias).


## Progress on the rest of Theorem 5.6

| Module | Content |
|---|---|
| `RHTower/SuzukiPHatModelSpace.lean` | The pointwise expansion (3.8) `hasSum_suzukiPHat_energy`; `suzukiEnergyKernel_mem_suzukiModelSpace`; **`exists_suzukiPHat_lp`** — the transform is an `L²` element of `K(Θ)`, i.e. `K_0 ⊆ K(Θ)` |
| `RHTower/SuzukiPHatSpectralCoefficient.lean` | `suzukiPHatCoefFn_toDerivativeZeroMean` and `suzukiPHatCoefFn_ofReal`: one integration by parts identifies the ray coefficient of `𝒫̂_{Dψ}` at `γ` with `i conj(ψ̂(γ))` |

What remains for `K_0 = K(Θ)` is Hilbert-space bookkeeping:

1. `⟪F_ρ, S⟫ = suzukiPHatEnergyCoef φ ρ / (√(m_ρ/π) i)` — the partial sums are eventually constant
   against a fixed `F_ρ`, since `⟪F_ρ, suzukiEnergyKernel σ⟫` vanishes off the diagonal.  Combining
   with the coefficient identification gives `⟪F_ρ, 𝒫̂_{Dψ}⟫ = i √(π m_ρ) ψ̂(γ_ρ)`.
2. Density: a `G ∈ K(Θ)` orthogonal to every `𝒫̂_{Dψ}` gives
   `Σ_ρ m_ρ S_G(ρ) ψ̂(γ_ρ) = 0` for all `ψ`, which is `eq_zero_of_orthogonal_suzukiTestSpectral`
   after replacing `ψ` by `ψ(-·)` (this converts `ψ̂(γ)` into `ψ̂(-γ)`, the convention of
   `suzukiTestSpectral`).  Hence `closure (span (range 𝒫̂_D)) = K(Θ)`.
3. `V(0) = closure V°(0)` then follows by applying the unitary `𝖥⁻¹`, which carries `K(Θ)` to `V(0)`.


## `K_0 = K(Θ)` closed

| Module | Content |
|---|---|
| `RHTower/SuzukiPHatBasisCoefficient.lean` | `suzukiEnergyScale`, the diagonal inner products, coefficient extraction from an energy-kernel limit, and **equation (3.8)** `inner_suzukiFGammaFamily_suzukiPHat` |
| `RHTower/SuzukiKZero.lean` | `suzukiPHatLp` (the transform as an `L²` element), its membership and coefficients, the conjugate and reflected test functions, the density theorem `eq_zero_of_inner_suzukiPHatLp`, and **`suzukiKZero_eq_suzukiModelSpace`** |

The last clause of Theorem 5.6, `V(0) = closure V°(0)`, is the image of this equality under the
unitary `𝖥⁻¹`, which carries `K(Θ)` to `V(0)` (`map_fourier_suzukiV0`).

Remaining in the paper: Thm 5.7 (de Branges axioms (dB1)--(dB3) and the support of `𝖥⁻¹Θ`,
i.e. [QXYYY09]), Prop 5.8 (the Weil form at *complex* spectral points and `Σ m_γ|γ|^{-1-δ} < ∞`),
§6 (an unbounded self-adjoint operator diagonal in `{F_γ}`), Cor 4.6 (Bombieri--Lagarias §4).


## §6 closed in the sequence model

`RHTower/SuzukiHilbertPolya.lean` builds the operator `A_{W,π/2}` directly, as multiplication by the
spectral points on `L²(τ)` — the model of `H_W` supplied by Lemma 5.4.  This replaces the source's
route through de Branges operator theory ([SiTo15, Thm 11], Remling's estimate for `S_θ ∉ H(E)`),
none of which the corpus owns.

* `suzukiTauDiag` — the operator as a `LinearPMap`, with domain the sequences whose multiple is
  still square-summable.
* `inner_suzukiTauDiag_symm` — symmetric, because the spectral points are real.
* `dense_suzukiTauDomain` — the domain is dense (it contains every basis vector).
* `isSelfAdjoint_suzukiTauDiag` — **self-adjoint**.  Testing the fundamental property of the adjoint
  against the basis vector at `γ` shows the adjoint acts by the same coordinatewise multiplication,
  so its domain is already the original domain.
* `suzukiTauDiag_basis` — the basis vector at `γ` is an eigenvector with eigenvalue `γ`.
* `eq_smul_suzukiTauBasis_of_eigen` — **multiplicity one**: the eigenspace at `γ` is spanned by that
  one vector.  The multiplicity of `γ` as a zero of `ξ` sits in the weight of `L²(τ)`, not in the
  dimension of the eigenspace, exactly as the source emphasises.

So `(H_W, A_{W,π/2})` is a Hilbert--Pólya space under RH.

Remaining: Thm 5.7 (de Branges axioms (dB1)--(dB3) plus the support of `𝖥⁻¹Θ`, i.e. [QXYYY09]),
Prop 5.8 (the Weil form at *complex* spectral points and `Σ m_γ|γ|^{-1-δ} < ∞`), Cor 4.6
(Bombieri--Lagarias §4).

## The last three items: exact obstructions

### Theorem 5.7 — one analytic brick, and *not* [QXYYY09]

Suzuki cites [QXYYY09] (Fourier-spectrum characterisation of Hardy spaces) to see that
`J_♯ K f ∈ L²(-∞,-t)` for `f ∈ V(t)`.  That citation is avoidable: `V(t) = L²(t,∞) ∩ K L²(t,∞)`
and `K² = 1`, so `f ∈ V(t)` already gives `K f = g ∈ L²(t,∞)` directly from the definition, whence
`(J_♯ K f)(x) = conj((Kf)(-x))` is supported in `(-∞,-t]`.  Nothing about the distributional support
of `𝖥⁻¹Θ` is needed.

What is genuinely missing is one reusable brick:

> **Gluing.**  If `F₊` is holomorphic on `ℂ₊` and `F₋` on `ℂ₋`, both with `L²` boundary values that
> agree almost everywhere on `ℝ`, then they glue to an entire function.

Proof route: Morera on a rectangle straddling the axis, splitting into the upper and lower halves at
height `±ε` and letting `ε → 0`; the boundary integrals cancel because both sides converge in `L¹loc`
to the same boundary function.  For a Hardy function that convergence is immediate on the Fourier
side — `f(· + iε) = 𝖥(d · e^{2πεs})` for the datum `d`, and `‖d(e^{2πεs} - 1)‖_{L²} → 0` by dominated
convergence.

With that brick, `Φ = E · 𝖥f` is entire, and the three de Branges axioms (dB1)--(dB3) are the
computations Suzuki gives: (dB1) is the two half-plane integral representations, (dB2) is `K f ∈ V(t)`
plus isometry of `K`, and (dB3) is the explicit Volterra perturbation
`f_w(x) = f(x) - i(w - conj w) ∫_0^{x-t} f(x-y) e^{-iwy} dy`.

### Proposition 5.8 — the Weil form at complex spectral points

The obstruction is the *meaning* of `⟨ψ,ψ⟩_W` for `ψ ∈ V(0)` when RH is assumed false.  The corpus's
`suzukiWeilInner` is the spectral sum `Σ_q ψ̂(-γ_q) conj(ψ̂(-conj γ_q))`, and for `ψ ∈ L²(0,∞)` the
entire Fourier integral converges only for `Im z > 0`, i.e. only at the zeros with `Im γ < 0`.  A
faithful statement needs the Weil form extended to `V(0)` at *all* spectral points, which is exactly
the analytic content Suzuki is exploiting.

The tail estimate the proof needs is already owned: `xiSpectralPoint_inv_three_halves_summable`
gives `Σ_q |γ_q|^{-3/2} < ∞`, i.e. `δ = 1/2`.

### Corollary 4.6 — Bombieri--Lagarias

Still the only item blocked on a source the corpus does not own at all: the construction of the
countable family `g_n` from [BoLa99, §4], and the argument that it is rich enough to detect the
equality.

### Theorem 5.7, better route: no gluing either

The entirety of `Φ = E·𝖥f` can be had from the orthonormal basis instead of from a boundary-gluing
argument.  For `F ∈ K(Θ)` write `F = Σ_γ c_γ F_γ` (Proposition 4.1).  Then

`E(z) F_γ(z) = √(m_γ/π) · i · A(z)/(z-γ)`

is **entire**, because `A` vanishes at `γ`.  And the series `Σ_γ c_γ E F_γ` converges locally
uniformly: by Cauchy--Schwarz its tail is bounded by

`|A(z)| · (Σ|c_γ|²)^{1/2} · (Σ_γ m_γ/(π|z-γ|²))^{1/2}`,

and `|A(z)|² Σ_γ m_γ|z-γ|^{-2}` is locally bounded — the zero-sum identity of
`SuzukiZeroSumIdentity` evaluates the sum off the axis, and near a zero `γ₀` the potentially
singular term `m_{γ₀}|A(z)|²/|z-γ₀|²` is bounded because `A` vanishes there to order `m_{γ₀} ≥ 1`.

So `E·K(Θ)` consists of entire functions with no appeal to Morera, to nontangential limits, or to
[QXYYY09].  What then remains of Theorem 5.7 is the three de Branges axioms, of which (dB1) and
(dB2) are immediate from the two half-plane representations and `K`-invariance, and (dB3) is the
explicit Volterra perturbation.

## First step of Theorem 5.7 landed

`RHTower/SuzukiDeBrangesVector.lean`:

* `suzukiDeBrangesVector γ m z = √(m/π) i · dslope A γ z` — the de Branges vector `E F_γ` written
  directly, and **entire**, because the divided slope of an entire function is entire.
* `suzukiDeBrangesVector_eq` — off the zeros of `E` it really is `E(z) F_γ(z)`.
* `memDeBranges_suzukiDeBrangesVector` — **`E F_γ ∈ H(E)`**.  The two Hardy conditions of the de
  Branges space are exactly the two conditions of the model space for `F_γ`: the first quotient is
  `F_γ` a.e., and the second is `Θ conj(F_γ) = -F_γ`.

So `H(E) = E K(Θ)` is realised on the basis, with no boundary gluing, no nontangential limits, and
no [QXYYY09].  What remains of Theorem 5.7 is the locally uniform convergence of the basis expansion
(to get *every* element of `E K(Θ)` entire) and the three de Branges axioms for `E 𝖥(V(t))`.


## `H(E) = E K(Θ)` closed

| Module | Content |
|---|---|
| `RHTower/SuzukiDeBrangesEntire.lean` | `suzukiDslopeSup` and its far-field bound; `summable_deBrangesBound`; **`differentiable_suzukiDeBrangesSeries`** — the de Branges series is entire |
| `RHTower/SuzukiDeBrangesRepresentation.lean` | `summable_deBrangesSeries_at`; `hasSum_smul_suzukiFGammaFamily`; **`suzukiDeBrangesSeries_div_ae`** — the series divided by `E` is the model-space element; **`memDeBranges_suzukiDeBrangesSeries`** — so `E K(Θ) ⊆ H(E)` |

So every element of `K(Θ_ξ)` has an entire `E`-multiple lying in `H(E)`.  This is the analytic core
of Theorem 5.7, obtained from the orthonormal basis rather than from boundary gluing: `E F_γ` is the
divided slope of `A`, and the expansion converges normally on every ball because only finitely many
spectral points lie in a bounded region while beyond it the divided slope is `O(1/|γ|)`.

What remains of Theorem 5.7 is the three de Branges axioms for the subspaces `E 𝖥(V(t))`:
(dB1) continuity of point evaluation, from the two half-plane integral representations;
(dB2) `Φ ↦ Φ^♯` preserves the space, from `K`-invariance of `V(t)` and isometry of `K`;
(dB3) the Volterra perturbation `f_w(x) = f(x) - i(w - conj w) ∫_0^{x-t} f(x-y) e^{-iwy} dy`.


## Theorem 5.3 CLOSED (`E 𝖥(V(t))` is a de Branges subspace)

The whole of the paper's Theorem 5.3 is now Lean-proved, with `V(t)` defined faithfully as
`L²(t,∞) ∩ K L²(t,∞)`.  The route avoids [QXYYY09] entirely.

| Module | Content |
|---|---|
| `HTGeometry/FourierTranslationModulation.lean` | `translateL2`, `modulationSymbol`, `modulationMul`, and **`fourierTransform_translateL2`** — the `L²` translation/modulation exchange law (mathlib gap), proved from the `L¹∩L²` bridge plus Schwartz density |
| `RHTower/SuzukiDeBrangesLift.lean` | `suzukiDeBrangesLift`; **`suzukiDeBrangesLift_apply`** (`(EF)(w) = E(w)⟪k_w,F⟫`); (dB1) bound; `inner_thetaMul_star` (κ is anti-unitary); `conj_suzukiDeBrangesVector_conj`; **`suzukiDeBrangesLift_thetaMul_star`** (dB2) |
| `RHTower/HardyBlaschkeMultiplier.lean` | `blaschkeSymbol`, `blaschkeSymbolInv`, isometry, partial fractions, **`blaschkeMulInv_mem_hardyL2`** (unconditional) and **`blaschkeMul_mem_hardyL2`** (given a vanishing Cauchy transform) |
| `RHTower/HardyModulationRay.lean` | `modulationEntire`, `modulationSlope`, **`integral_modulationMul_cauchy`**, `hardyRay`, and Blaschke stability of the modulated Hardy space |
| `RHTower/SuzukiRaySpaces.lean` | `suzukiRayL2` (= `L²(t,∞)`), **`suzukiV`** (Suzuki (5.2)), `suzukiKappaₛₗ`, `suzukiModelRay`, `map_fourier_suzukiV`, and (dB2)/(dB3) in boundary form |
| `RHTower/SuzukiDeBrangesSubspace.lean` | `suzukiDeBrangesLift_blaschkeMul`, (dB1) below the axis, and the capstone **`suzuki_deBranges_subspace`** |
| `RHTower/SuzukiWeilRaySubspace.lean` | `suzukiWeilRay` (= `H_W(t)`) and the isometry up to `π` — the second half of Theorem 5.3 |

Two corpus lemmas were generalized to allow one exceptional point, which is what the inner Blaschke
factor needs at its own pole: `ae_eq_zero_of_laplaceRay_eq_zero_of_ne` and
`mem_hardyL2_of_cauchyTransform_eq_zero_of_ne`.  The originals are now one-line corollaries.


## Proposition 5.1 CLOSED (the unconditional criterion on `V(0)`)

`RiemannHypothesis ↔ (SuzukiV0MassCondition ∧ SuzukiV0PeakCondition)` is Lean-proved, both
directions, axiom-clean.  The obstruction recorded above — that `⟨ψ,ψ⟩_W` was only defined for
`C_c^∞` test functions and only through an RH-dependent spectral formula — is removed by giving the
point evaluation `ψ̂(γ)` its correct unconditional meaning: the pairing against the reproducing
kernel of the model space.

| Module | Content |
|---|---|
| `RHTower/SuzukiHalfInnerRealAxis.lean` | `XiC_eq_zero_of_xiHedenmalmDeBrangesE_eq_zero_ofReal` (on `ℝ` the Hermite--Biehler function `E` vanishes only at zeros of `A`, since `A` and `A'` are real there); `eventually_differentiableAt_suzukiHalfInner_ofReal`; `continuous_dslope_suzukiHalfInner_ofReal`; **`memLp_dslope_suzukiHalfInner`** — the divided slope of `A/E` at *any* zero of `A` is in `L²(ℝ)`, unconditionally |
| `RHTower/SuzukiModelPointEval.lean` | `suzukiThetaMero_eq_neg_one_of_XiC_zero` (`Θ = -1` at every zero of `A`, multiple zeros included); **`suzukiModelKernel_of_XiC_zero`** — there the reproducing kernel is `(i/π)·dslope(A/E)`; `memLp_suzukiModelKernel_of_XiC_zero`; `suzukiModelKernelLp`; **`suzukiModelEval`**; **`suzukiModelEval_xiSpectralPointSupport`** — under RH the evaluation is the corpus's `suzukiRestriction` |
| `RHTower/SuzukiV0WeilForm.lean` | `summable_sq_of_summable_nonneg`; `finite_xiSpectralPoint_norm_le`; **`summable_xiSpectralPoint_shift_three_halves`**; `hasSum_xiZeroCopy_of_support`; **`riemannHypothesis_iff_forall_XiC_zero_im_eq_zero`**; `exists_xiSpectralPointSupport_eq`; `suzukiV0Eval`, **`suzukiV0WeilForm`**; **`norm_sq_eq_pi_mul_suzukiV0WeilForm`** (Prop 5.1 (1) forward); **`exists_peaked_suzukiV0`** (Prop 5.1 (2) forward) |
| `RHTower/SuzukiPropFiveOne.lean` | `re_peak_term_le`, `peak_term_swap`; `SuzukiV0MassCondition`, `SuzukiV0PeakCondition`; **`riemannHypothesis_of_suzukiV0_conditions`** (the converse); capstone **`suzuki_prop_5_1`** |

### What made it unconditional

`Θ_ξ` written as `2(A/E) - 1` takes the *correct* value `-1` at every zero of `A`, so the
reproducing kernel `k_γ(x) = (i/2π)(1 - conj(Θ(γ))Θ(x))/(x - conj γ)` collapses there to
`(i/π)·dslope(A/E)(conj γ)`.  That divided slope is holomorphic on a neighbourhood of the real axis
with no RH input — at a real point either `E ≠ 0`, or `E = 0` and then `A = A' = 0` because both are
real on the line, and the local factorisation of `SuzukiHalfInnerLocalFactor` applies.  Its `L²`
bound is `|A/E| ≤ 1` on the line plus compactness near the centre.  So `⟪k_γ, 𝖥ψ⟫` is defined for
every zero `γ ∈ Γ`, real or not, and it is the analytic continuation Suzuki writes as `ψ̂(γ)`.

Under RH the kernel at a spectral point is the normalised basis vector `F_γ/√(π m_γ)`, so the
evaluation *is* `suzukiRestriction`, and Makarov--Poltoratski gives (1) while orthonormality of
`{F_γ}` gives (2) in the sharp form (exact zeros at the other spectral points, so any `δ > 0`
works).

### Deviations from the source, stated

* The source leaves `δ > 0` unspecified in (2) and only uses `Σ_γ m_γ|γ|^{-1-δ} < ∞`; the corpus
  fixes `δ = 1/2`, the exponent it owns (`xiSpectralPoint_inv_three_halves_summable`).  The forward
  direction produces the sharp form, so nothing is lost there.
* The unitary Fourier normalisation turns the source's `‖ψ‖² = 2^{-1}⟨ψ,ψ⟩_W` into
  `‖ψ‖² = π⟨ψ,ψ⟩_W`.
* The Weil sum is indexed by the spectral points `γ_q` rather than `-γ_q`.  `Γ` is stable under
  `γ ↦ -γ` with equal multiplicities (`A` is even, `XiC_neg`), so this is the same hermitian form
  written with the opposite sign convention for the Fourier kernel.

Remaining from the paper: **Corollary 4.6** (Bombieri--Lagarias §4).


## Corollary 4.6 — the plan (Bombieri--Lagarias / Li's criterion)

Suzuki contributes nothing to Cor 4.6 beyond the citation: `‖g_n‖₀² ≥ 0` turns (EQ_411) into
`⟨g_n,g_n⟩_W ≥ 0`, and [BoLa99, §4] turns that into RH.  So the whole item is **Li's criterion,
hard direction**, which the corpus does not own (`LiFiniteCriterionFrontier` says so explicitly).

### The arithmetic identity (checked on paper)

`g_n(x) = e^{-x/2} Σ_{j=1}^n C(n,j)(-x)^{j-1}/(j-1)!` on `x > 0` has

`ĝ_n(z) = ∫_0^∞ g_n(x)e^{izx}dx = 1 - (1 - 1/s)^n`,  `s := 1/2 - iz`,

because `∫_0^∞ x^{j-1}e^{-sx}dx = (j-1)!/s^j`.  At `z = -γ`, `s = 1/2 + iγ = ρ`, so
`ĝ_n(-γ) = 1 - (1-1/ρ)^n` — Li's summand.  Since `g_n` is real, `(ĝ_n)^♯(z) = ĝ_n(-z)`, and with
`w_ρ := 1 - 1/ρ` one has `w_{1-ρ} = w_ρ^{-1}`, so

`⟨g_n,g_n⟩_W = Σ_ρ m_ρ (1 - w_ρ^n)(1 - w_ρ^{-n}) = Σ_ρ m_ρ (2 - w_ρ^n - w_ρ^{-n}) = 2 λ_n`

(the last step by the `ρ ↦ 1-ρ` symmetry of the divisor).  **This is the form to formalise**: the
paired sum `Σ_ρ (2 - w^n - w^{-n})` converges *absolutely*, unlike Li's `Σ_ρ (1 - w^n)`.

### The pointwise bound that makes everything absolute

`2 - w^n - w^{-n} = -w^{-n}(w^n - 1)^2`, and `|w^n - 1| ≤ n |w-1| max(1,|w|)^{n-1}`, so with
`M := max(‖w‖, ‖w‖⁻¹) ≥ 1`

> `‖2 - w^n - w^{-n}‖ ≤ n² Mⁿ ‖w - 1‖²`.

Since `w_ρ - 1 = -1/ρ` and `Σ_ρ |ρ|^{-2} < ∞` (`xiSpectralPoint_inv_sq_summable`), every `λ_n` is an
absolutely convergent sum, and the double series `Σ_n Σ_ρ (…) z^n` converges absolutely for
`|z| < 1/M`.

### The contradiction (no Dirichlet/Kronecker needed)

Let `Φ(z) := Σ_ρ [2z/(1-z) - w_ρ z/(1-w_ρ z) - (z/w_ρ)/(1-z/w_ρ)]`, meromorphic with poles exactly at
`w_ρ` and `1/w_ρ`, and let `G(z) := Σ_{n≥1} 2λ_n z^n` with radius `R`.

1. `w_ρ ∈ (0,1)` forces `ρ = 1/(1-w) > 1` and `w_ρ > 1` forces `ρ < 0`: **no pole of `Φ` lies in the
   real interval `(0,1)`**, because `ξ` has no zeros with `Re s ≤ 0` or `Re s ≥ 1`, and none real in
   `(0,1)` (there `s(s-1) < 0`, `Γ(s/2) > 0`, `ζ(s) < 0`).
2. If RH fails there is `ρ₀` with `|w_{ρ₀}| = W > 1`; `Φ` has a genuine pole at `z₀ = 1/w_{ρ₀}`
   (all `ρ` contributing to that pole have residue `1/w_{ρ₀}`, so nothing cancels), hence `R ≤ |z₀| < 1`.
3. `λ_n ≥ 0` makes `G` a power series with nonnegative coefficients, so **Vivanti--Pringsheim**
   (`HTGeometry.VivantiPringsheim.not_continuesAcross_of_nonneg`) says `z = R` is a singular point.
4. But `R ∈ (0,1)` and `Φ` is analytic there and continues `G`.  Contradiction.

### Module plan

| Planned module | Content |
|---|---|
| `RHTower/LiTermBound.lean` | `liTerm w n = 2 - w^n - w⁻ⁿ`; the factorisation `-w⁻ⁿ(wⁿ-1)²`; the bound `n² Mⁿ‖w-1‖²`; summability of `liTerm ∘ w` for a family with `Σ‖w_i-1‖² < ∞` and bounded `M` |
| `RHTower/LiCoefficientXi.lean` | `w_ρ := 1 - 1/ρ`, `w_{1-ρ} = w_ρ⁻¹`, the bounds `inf|ρ| > 0`, `inf|ρ-1| > 0`, `Σ|ρ|⁻² < ∞`; definition of `λ_n` as the paired sum |
| `RHTower/LiGeneratingFunction.lean` | `Φ`, local uniform convergence off the poles, `G = Φ` near `0`, the residue computation |
| `RHTower/LiCriterion.lean` | `(∀ n ≥ 1, 0 ≤ λ_n) ↔ RiemannHypothesis` |
| `RHTower/SuzukiCorFourSix.lean` | `ĝ_n(z) = 1 - (1-1/s)^n`; `⟨g_n,g_n⟩_W = 2λ_n`; Cor 4.6 |


## LI'S CRITERION IS CLOSED (the Bombieri--Lagarias input of Cor 4.6)

`RHTower.riemannHypothesis_iff_forall_re_xiLiPaired_nonneg` :
`RiemannHypothesis ↔ ∀ n, 0 ≤ (xiLiPaired n).re`, unconditional, axiom-clean.

This removes the wall that `LiFiniteCriterionFrontier` recorded ("construct the canonical
multiplicity-sensitive infinite sums ... and establish the Bombieri--Lagarias positivity
equivalence").

| Module | Content |
|---|---|
| `RHTower/LiTermBound.lean` | `liTerm w n = 2 - wⁿ - w⁻ⁿ`; `liTerm_eq_neg_mul_sq` (`= -w⁻ⁿ(wⁿ-1)²`); `liTerm_inv` (invariance under `w ↦ w⁻¹`); `liTerm_of_norm_eq_one` (`= 2 - 2Re(wⁿ)` on the circle); **`norm_liTerm_le`** (`≤ n² Mⁿ ‖w-1‖²`, `M = max(‖w‖,‖w‖⁻¹)`); `summable_liTerm`; `re_tsum_liTerm_nonneg` |
| `RHTower/LiCoefficientXi.lean` | `xiRootW ρ = 1 - 1/ρ`; `norm_xiRootW_eq_one_iff` (unimodular ⟺ on the critical line); `xiRootW_one_sub` (`w_{1-ρ} = w_ρ⁻¹`); `im_eq_zero_of_xiRootW_im_eq_zero`; `finite_xiDivisorSupport_near_half`; **`exists_bound_xiRootW`** (the `w_ρ` live in a fixed annulus); **`xiLiPaired n`** = `2λ_n`; `summable_xiLiPairedTerm`; **`re_xiLiPaired_nonneg_of_rh`** (easy half) |
| `RHTower/LiBracket.lean` | `liBracket w z = z(z+1)(w-1)²/((z-1)(z-w)(wz-1))` and **`hasSum_liTerm_mul_pow`** — the closed form of `Σ_n liTerm(w,n) zⁿ` |
| `RHTower/LiPositivityFails.lean` | **`exists_pos_pow_sub_one_lt`** (simultaneous recurrence on a finite torus, by compactness); `re_ge_half_of_norm_sub_one_lt_one`; `exists_ge_pow_re_gt_half`; `summable_re_liTerm_of_one_le`; `finite_far_set`; **`exists_re_tsum_liTerm_neg`** — the abstract hard half |
| `RHTower/LiCriterion.lean` | `xiRootV` (the modulus-`≥1` representative); **`riemannHypothesis_of_forall_re_xiLiPaired_nonneg`**; capstone **`riemannHypothesis_iff_forall_re_xiLiPaired_nonneg`** |

### The proof, and why it is elementary

The classical route runs through the generating function `Σ λ_n zⁿ`, Vivanti--Pringsheim, and a
meromorphic continuation with a pole at `1/w_ρ`.  The route taken here avoids all of it.

Pair the zeros: `ρ ↦ 1-ρ` sends `w = 1-1/ρ` to `w⁻¹`, and `liTerm w n = 2 - wⁿ - w⁻ⁿ` is invariant,
so `Σ_ρ m_ρ liTerm(w_ρ, n) = 2λ_n` **converges absolutely** — the summand is
`-w⁻ⁿ(wⁿ-1)²`, of size `O(n² Mⁿ ‖w-1‖²)`, and `w_ρ - 1 = -1/ρ` with `Σ m_ρ|ρ|⁻² < ∞`.

If a zero sits off the critical line, normalise every `w` to the representative of modulus `≥ 1`.
Only finitely many can exceed `q := (1+W)/2`, where `W = ‖w_{ρ₀}‖ > 1`, because `‖w-1‖ ≥ ‖w‖-1` and
the weighted squares are summable.  The infinite tail contributes `O(n² qⁿ)`.  A pigeonhole on the
finite product of unit circles (compactness ⟹ two powers are close ⟹ their difference is a power
near `1`) gives arbitrarily large `n` with `Re(w_iⁿ) ≥ ‖w_i‖ⁿ/2 ≥ 0` for *every* `i` in the finite
bad set at once, so the finite part is at least `m_{ρ₀} Wⁿ/2`.  Since `W > q`, the exponential beats
the polynomial and `2λ_n < 0`.

That `w_ρ` real forces `ρ` real — impossible for a Xi zero — is recorded as
`im_eq_zero_of_xiRootW_im_eq_zero`; it is what the classical Pringsheim route uses instead.

### What Corollary 4.6 still needs

`⟨g_n,g_n⟩_W = 2λ_n = xiLiPaired n`, i.e. the identification of Bombieri--Lagarias's test functions.
On paper (checked above) `ĝ_n(z) = 1 - (1-1/s)ⁿ` with `s = 1/2 - iz`, so `ĝ_n(-γ) = 1 - w_ρⁿ` and
`(ĝ_n)^♯(-γ) = ĝ_n(γ) = 1 - w_ρ⁻ⁿ`, whose product is exactly `liTerm(w_ρ, n)`.  The one missing
Lean brick is the **complex-rate half-line Laplace transform of a monomial**

> `∫_{x>0} xʲ e^{-cx} dx = j! / c^{j+1}` for `Re c > 0`,

a mathlib gap: mathlib's `integral_cpow_mul_exp_neg_mul_Ioi` and the corpus's
`integral_pow_mul_exp_neg_mul_Ioi` both take a *real* rate; only `HTGeometry.integral_Ioi_cexp_neg`
(`j = 0`) is complex.  The plan is the explicit antiderivative
`A_{j+1}(x) = -x^{j+1}e^{-cx}/c + ((j+1)/c) A_j(x)`, `A_0(x) = -e^{-cx}/c`, with
`A_j(0) = -j!/c^{j+1}` and `A_j(x) → 0`, fed to `integral_Ioi_of_hasDerivAt_of_tendsto`.
