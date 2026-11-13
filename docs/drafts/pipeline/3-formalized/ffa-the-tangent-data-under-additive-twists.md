# The tangent data of Möbius and Liouville under additive twists

- **ID:** A144
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `FloorFreeArithmetic/TheTangentDataOfMobiusAndLiouvilleUnderAdditiveTwists.lean`
- **Source:** docs/reports/review-1311/obstacles-summary.md §2.1 "Models and laws of world I", A144
- **Statement:** in world I (`Θ∞ < Θ`) the Gaussian window sums of `μ(n) c_q(n)` and `λ(n) c_q(n)`
  (`c_q(n) = Σ_{ζ primitive q-th root} ζ^n`, the sum of the additive twists at modulus `q`) are
  asymptotic after normalization to the sums of residues at the top zeros of `ζ`; the residue
  numerators are those of `μ` multiplied by `R_q(s)`, resp. `R^λ_q(s) ζ(2s)`.

## Lean
| Statement | Declaration (namespace `FloorFreeArithmetic`) |
|---|---|
| multiples of `e` in `1/ζ` and `ζ(2s)/ζ(s)` | `moebius_mul_eq`, `LSeries_dvd_eq`, `LSeries_moebius_dvd`, `LSeries_liouville_dvd` |
| Dirichlet series of the twists | `LSeries_moebius_mul_ramanujanSum`, `LSeries_liouville_mul_ramanujanSum` |
| factors: holomorphy, size | `differentiableAt_ramanujanFactor`, `exists_norm_ramanujanFactor_le`, `differentiable_liouvilleRamanujanFactor`, `norm_liouvilleRamanujanFactor_le` |
| window sums | `signal_eq_tsum_of_LSeries`, `signal_ramanujanKernel_eq_tsum`, `signal_liouvilleRamanujanKernel_eq_tsum` |
| tangent data | `tangentDatum_ramanujanTwist`, `tangentDatum_liouvilleRamanujanTwist` |
| residue numerators | `ramanujanNumerator_div_eq` |

Axioms of the headline theorems: `propext`, `Classical.choice`, `Quot.sound`.

## Proof
*Dirichlet series.* `c_q(n) = Σ_{de=q} μ(d) e 1_{e|n}` (`ramanujanSum_eq_sum_moebius`). For `e ≥ 1`,
`μ(em) = μ(e) 1_e(m) μ(m)` (`1_e` the trivial character mod `e`: multiplicativity on coprime `m`,
`em` not squarefree otherwise), so reindexing `n = em`,
`Σ_{e|n} μ(n) n^{−s} = μ(e) e^{−s} L(1_e·μ, s) = μ(e) e^{−s}/L(s, 1_e)`
(`DirichletCharacter.LSeries.mul_mu_eq_one`), and `L(s, 1_e) = ζ(s) Π_{p|e}(1 − p^{−s})`
(`HalfWeight.LFunction_one_eq`). Summing the finitely many bounded pieces:
`Σ μ(n) c_q(n) n^{−s} = R_q(s)/ζ(s)`, `R_q(s) = Σ_{de=q} μ(d) e μ(e) e^{−s} Π_{p|e}(1 − p^{−s})⁻¹`.
For `λ`, complete multiplicativity gives `Σ_{e|n} λ(n) n^{−s} = λ(e) e^{−s} ζ(2s)/ζ(s)`, so
`Σ λ(n) c_q(n) n^{−s} = R^λ_q(s) ζ(2s)/ζ(s)`, `R^λ_q(s) = Σ_{de=q} μ(d) e λ(e) e^{−s}`.

*Factors.* `1 − p^{−s} ≠ 0` on `Re s > 0`, so `R_q` is holomorphic there; on `Re s ≥ ½`,
`|R_q| ≤ Σ_{de=q} e (1 − 2^{−½})^{−ω(e)}` and `|R^λ_q| ≤ Σ_{de=q} e`.

*Window sums.* For coefficients `|a(n)| ≤ B`, `a(0) = 0`, whose world kernel equals
`e^{(s−c)²} L(a, s)` on `Re s = 2`: expand `L(a, s)`, exchange sum and integral (the Gaussian gives
`O(e^{−t²}/n²)`), and evaluate the complex Gaussian integral (as `signal_mobius_eq_tsum`). With
`A_q = (s − 1)R_q` and `A^λ_q = (s − 1)ζ(2s)R^λ_q`, the kernels `e^{(s−c)²}A/((s−1)ζ)` are
`e^{(s−c)²} R_q/ζ` and `e^{(s−c)²} R^λ_q ζ(2s)/ζ` on `Re s = 2`.

*Tangent data.* `A_q`, `A^λ_q` are holomorphic on `Re s > ½` with linear growth on every
`σ ≤ Re s ≤ 2`, `σ > ½`; `tendsto_normalized_signal_sub_top` applies. With
`(s − 1)ζ(s) = (s − ρ)^m g(s)`, the residue numerator `e^{(s−c)²} A/g` is `R_q` (resp.
`R^λ_q ζ(2s)`) times that of `μ`. ∎

## Reading
The finite top layer of `ζ` reappears in every Ramanujan twist with amplitude `R_q(ρ)`: same top
zeros and same degrees wherever `R_q(ρ) ≠ 0`. The amplitude can vanish: for `q = p` prime,
`R_p(s) = −(p^s − 1 + p)/(p^s − 1)` is zero exactly when `p^s = 1 − p`, i.e. on the points with
`Re s = log(p−1)/log p` and `Im s · log p ≡ π mod 2π`. A single additive twist `e(an/q)` has the
`ζ`-component `R_q/φ(q)` (the principal characters) plus components carried by the nonprincipal
Dirichlet `L`-functions modulo divisors of `q` [C]; world I, a statement about `ζ` alone, does not
control those.

## Log
- 2026-11-13 — proved on paper and formalized.
