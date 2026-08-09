# Sampling detects independence, and what it leaves for the Báez-Duarte sections

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The step

`finite-section-zeta-interpolation-dichotomy.md` ends with a certificate: one nonvanishing bordered
determinant of sampled `ζ` values proves a finite section of the Báez-Duarte problem has positive distance.
The obvious next question is whether such a sample must exist. This card supplies the general tool that
answers it and reduces the answer to a single identity.

## What is proved

`RHTower/SamplingDeterminant.lean` — stated for an arbitrary *separating* family of functionals, with only
`Field K` assumed: no topology, no finite-dimensionality, no structure on the index set:

* **`exists_det_ne_zero_of_linearIndependent_of_separating`** — if functionals `Φ : ι → (V →ₗ[K] K)` kill no
  nonzero vector, a linearly independent `f : Fin n → V` has indices `x` with `det [Φ_{xⱼ}(fᵢ)] ≠ 0`.
  Induction on `n`: expand along the last column, which by **linearity** presents the determinant as
  `Φ_t(∑ᵢ cᵢ fᵢ)` whose last coefficient is the smaller determinant supplied by the induction hypothesis;
  independence makes that combination a nonzero *vector*, and separation finds an index not killing it;
* **`exists_det_ne_zero_of_linearIndependent`** — the point-evaluation case (`Φ = LinearMap.proj`, separating
  because a nonzero function is nonzero somewhere): a linearly independent family of `K`-valued functions has
  sample points with `det [fᵢ(xⱼ)] ≠ 0`;
* `not_linearIndependent_of_forall_det_eq_zero` — the contrapositive, the usable direction;
* `exists_det_inner_ne_zero_of_linearIndependent` — the inner-product case (`Φ = innerSL`, separating by
  `inner_self_eq_zero`): independent vectors have an invertible cross-Gram matrix against some finite sample
  of test vectors.

`RHTower/BorderDeterminantVanishing.lean` — applied to the sampled pairings:

* `StripPoint`, `borderRowFun` — the row functions on the open strip `½ < Re s < 1`, namely
  `Fᵢ(s) = −(θᵢ^s − θᵢ)·ζ(s)/s` for `i < N` and `F_N(s) = 1/s`;
* `matrix_borderRowFun_eq_sampledBorderMatrix` — `sampledBorderMatrix` *is* their evaluation matrix;
* `not_linearIndependent_borderRowFun` — so a determinant vanishing at every sample makes the row functions
  linearly dependent;
* **`exists_relation_of_forall_det_eq_zero`** — unwinding the dependence (clearing the `1/s`):

  > If no sample of `N+1` points certifies a floor, there are coefficients `c`, not all zero, with
  > `(∑ᵢ cᵢ(θᵢ^s − θᵢ))·ζ(s) = c_N` at **every** point of the strip.

All eight declarations are `#print axioms`-clean.

## Why it matters

The escape route has collapsed from "for each sample there are coefficients" to "one fixed coefficient
vector works on the whole strip". That is no longer an interpolation problem but a rigid identity between
`ζ` and an entire function: `ζ(s) = c_N / P(s)` with `P(s) = ∑ᵢ cᵢ(θᵢ^s − θᵢ)` entire.

Such an identity is false, and the contradiction is elementary rather than deep:

1. `P·ζ − c_N` is analytic on the connected set `ℂ \ {1}` and vanishes on the strip, hence identically
   (identity theorem);
2. at a trivial zero, `ζ(−2) = 0`, the identity gives `c_N = 0`;
3. then `P·ζ ≡ 0`, and `ζ(2) = π²/6 ≠ 0` makes `ζ` nonvanishing near `2`, so `P ≡ 0` near `2` and hence
   everywhere;
4. `P(n) = 0` for `n = 0,…,N` gives `∑ᵢ cᵢ(θᵢ − 1)·θᵢⁿ = 0` for `n < N`, a Vandermonde system in the
   distinct `θᵢ`, so every `cᵢ(θᵢ − 1) = 0` and — for `θᵢ ≠ 1` — every `cᵢ = 0`, contradicting `c ≠ 0`.

Steps 1–4 need only mathlib (`riemannZeta_neg_two_mul_nat_add_one`, `riemannZeta_two`,
`Matrix.det_vandermonde_ne_zero_iff`, `Matrix.exists_vecMul_eq_zero_iff` — the last already used in
`FiniteSectionBorderDeterminant`) and are the next increment. Their conclusion is the capstone

> **every finite family of distinct dilations `θᵢ ∈ (0,1)` has positive Báez-Duarte distance,**

which subsumes the special cases already in the corpus (`bdDistDiscrete_pos` via the factorial floor,
`bdDist_single_ge` for one generator) and proves them for arbitrary families by a structural argument rather
than an arithmetic estimate.

## Reuse

`exists_det_ne_zero_of_linearIndependent_of_separating` is the general law: any separating family of
functionals — point evaluations, inner products, moments, jets — detects independence by a finite sample. It
is the converse half of mathlib's `Matrix.linearIndependent_rows_iff_isUnit`, which sees only a fixed matrix,
and it answers every "does a finite sample see the whole space" question uniformly. The proof needs only
linearity of the functionals plus separation, which is why it carries no topological hypotheses.
