# Li Reciprocal Chebyshev Kernel

- **ID:** li-reciprocal-chebyshev-kernel
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** `docs/consolidated/gpt/research-topics.md` topic 20; `docs/consolidated/gpt/proof-route.md`
- **Statement:** Under FE folding, each Li coefficient is an exact Chebyshev-kernel transform of the reciprocal seam atoms `y=-(rho-1/2)^(-2)`; in the reciprocal moment chart this is an infinite shifted-moment expansion, not a finite triangular transform.

## Goal

Close a missing atlas edge between the Li chart and the corrected reciprocal-seam square-test chart. The Li coefficients are finite triangular in the ordinary `rho^{-k}` power sums, but after passing to the FE-folded reciprocal coordinate `y`, the chart change is a rational Chebyshev kernel whose Taylor expansion uses all shifted reciprocal moments.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 -> 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 -> 3 formalized: **DONE (2026-08-16)** — `GaloisForLFunctions.liPairKernel_eq_chebyshev`,
  `hasSum_liChebyshevKernel_one`, `tsum_liChebyshevKernel_one` in
  `formal/GaloisForLFunctions/RHTower/LiReciprocalChebyshevKernel.lean`; `lake build` green; axiom
  footprint `[propext, Classical.choice, Quot.sound]`
- [ ] 3 -> 4 publication-ready: standalone note if needed

## Proof

[PROVED HERE]

Let

```text
rho = 1/2 + w,
rho' = 1-rho = 1/2 - w
```

be an FE pair, and set

```text
y = -w^(-2).
```

The pair contribution to Li's coefficient is

```text
L_n(w) =
[1 - (1 - 1/rho)^n] + [1 - (1 - 1/rho')^n].
```

Put

```text
q = 1 - 1/rho = (w-1/2)/(w+1/2).
```

For the FE partner, `1 - 1/rho' = q^(-1)`. Hence

```text
L_n = 2 - (q^n + q^(-n)).
```

A direct calculation gives

```text
(q + q^(-1))/2 = (4-y)/(4+y).
```

Therefore, if `C_n` denotes the Chebyshev polynomial of the first kind,

```text
L_n(y) = 2 - 2 C_n((4-y)/(4+y)).
```

This is an exact FE-folded Li kernel in the reciprocal seam coordinate.

Since `L_n(0)=0`, its Taylor expansion at the reciprocal accumulation point has the form

```text
L_n(y) = sum_{k>=1} c_{n,k} y^k.
```

The Taylor expansion is valid whenever the reciprocal atoms lie in `|y|<4`; for the `xi` divisor this follows from the standard verified zero-free region below the first nontrivial zero height, so `|rho-1/2|>1/2` for every nontrivial zero. Thus

```text
lambda_n = sum_{k>=1} c_{n,k} T_k,
qquad
T_k = sum_rho m_rho y_rho^k,
```

with absolute convergence. In particular, the Li-to-reciprocal chart is not finite triangular in the `T_k`; every `lambda_n` sees an infinite tail of reciprocal moments through a fixed rational kernel.

The first kernel begins

```text
L_1(y) = y - y^2/4 + y^3/16 - y^4/64 + ...
```

and higher `n` have the same singularity at `y=-4`, with coefficients decaying geometrically up to polynomial factors in `k`.

## Computation

Symbolic verification for `n=1..7` and coefficient extraction are archived in:

- `computations/2026-06-21-conway-li-reciprocal-chebyshev-kernel.py`
- `computations/2026-06-21-conway-li-reciprocal-chebyshev-kernel.txt`

## Route Consequence

The Li chart is a smoothed/global kernel chart over the reciprocal seam moments. A finite Li prefix cannot be treated as a finite shifted-Hankel prefix in disguise: it mixes all `T_k`. Conversely, any theorem deriving shifted square-test positivity from Li data must control this infinite Chebyshev kernel and cannot rely only on the known finite triangular `lambda_n <-> P_k` transform.

This makes the atlas edge explicit:

```text
ordinary power sums P_k  <--finite triangular-->  lambda_n,
reciprocal moments T_k   <--infinite Chebyshev kernel-->  lambda_n.
```

## Log

- 2026-06-21 -- Conway: created after workflow NODE "fluid diffusion can create delayed or migrating aftershock patterns that resemble ordinary Omori decay", using method 8 (look for similar objects) on the Li chart.

## Lean formalization — 2026-08-16

**Module:** `formal/GaloisForLFunctions/RHTower/LiReciprocalChebyshevKernel.lean` (wired into
`RHTower.lean`).  **Axioms:** `[propext, Classical.choice, Quot.sound]` on every headline theorem —
no `sorry`, no added axiom, no hypothesis beyond the card's own.

| Paper step (§) | Lean name | Statement |
|-|-|-|
| `L_n(w) = [1-(1-1/ρ)^n] + [1-(1-1/ρ')^n]` | `liPairKernel` | the FE-folded pair contribution in the seam coordinate `ρ = 1/2 + w` |
| `L_n(y) = 2 - 2 C_n((4-y)/(4+y))` | `liChebyshevKernel` | the Chebyshev kernel in the reciprocal coordinate |
| `2 T_n((z+z⁻¹)/2) = z^n + z^{-n}` | `two_mul_chebyshevT_eval_half_add_inv` | via mathlib's Dickson/Chebyshev bridge `dickson_one_one_eval_add_inv` |
| **`1-1/ρ = q`, `1-1/ρ' = q⁻¹`, `(q+q⁻¹)/2 = (4-y)/(4+y)`, hence the kernel identity** | **`liPairKernel_eq_chebyshev`** | the exact FE-folded Li kernel in the reciprocal seam coordinate |
| `L_n(0) = 0` | `liChebyshevKernel_zero` (with `chebyshevT_eval_one`) | the kernel vanishes at the reciprocal accumulation point |
| `L_1(y) = y - y²/4 + y³/16 - …` | `liChebyshevKernel_one`, **`hasSum_liChebyshevKernel_one`** | `L_1(y) = 4y/(4+y)`, with the convergent expansion on `‖y‖ < 4` |
| "not finite triangular" | **`liKernelOne_coeff_ne_zero`** | every Taylor coefficient `(-1)^k/4^k` is nonzero, so the expansion never terminates |
| "the same singularity at `y = -4`" | `analyticOnNhd_liChebyshevKernel` (with `differentiableAt_liChebyshevKernel`) | for every `n` the kernel is analytic exactly away from `y = -4` |
| **`λ_n = Σ_k c_{n,k} T_k` with absolute convergence** | **`tsum_liChebyshevKernel_one`** | if the reciprocal atoms lie in `‖y‖ ≤ r < 4` and the multiplicities are absolutely summable, the Li coefficient is the absolutely convergent Chebyshev transform of *all* reciprocal moments `T_k = Σ_j m_j y_j^k` |

### Faithfulness note on the convergence hypothesis

The card states the expansion is "valid whenever the reciprocal atoms lie in `|y| < 4`", and then
records that for the `ξ` divisor this follows from the standard verified zero-free region below the
first nontrivial zero height (`|ρ - 1/2| > 1/2`).  `tsum_liChebyshevKernel_one` is the theorem in
exactly that conditional form — the disc condition is a hypothesis on the divisor data, as on the
card — and the `ξ`-specific verification remains the card's credited classical import, not a Lean
obligation of this card.

## Log (cont.)

- 2026-08-16 (Leaner) — **→ 3-formalized.**  The exact kernel identity, the vanishing at the
  accumulation point, the explicit `L_1` expansion with all coefficients nonzero (the
  "infinite, not finite triangular" content), the analyticity away from `y = -4`, and the
  absolutely convergent reciprocal-moment transform are all unconditional Lean theorems.
