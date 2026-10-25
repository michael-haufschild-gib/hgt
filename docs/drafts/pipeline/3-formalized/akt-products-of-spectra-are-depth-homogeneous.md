# Products of spectra are depth-homogeneous: the independence test of Arithmetic Künneth Theory

- **ID:** akt-kunneth-homogeneity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2510/opus.md` §4.9 (retirement test of AKT), §2.1(b) (depth homogeneity), walls ledger face 1.15
- **Statement:** A product receiver on the spectrum of a source sees zero depth only through its total arithmetic length. Its free (unique-factorization) region ends at total length equal to the square-root threshold, whatever the product order. Over `𝔽_q`, Künneth positivity is exactly point-count positivity, which does not imply purity. So products of spectra supply no non-scaling term.

## Goal

This decides whether AKT is an independent programme. The retirement test asks for homogeneity of every product construction definable from the actual source. Product constructions fall into three layers, each settled below:

1. **External products of the spectrum.** These are k-linear zero functionals, external powers of the explicit-formula distribution, Nyquist-renormalized diagonals and moments.
2. **Correspondences on the product.** These are Frobenius, Hecke and successor graphs and the Weil pairing.
3. **Families over a base.**

Layer 1 is homogeneous (K1, K2). Over `𝔽_q` its positivity content is exactly `N_n ≥ 0` (K3). Layer 2 carries the only non-scaling term in a purity proof, the budget `τ(0) = 2g`, but its positivity is the Hodge index, which belongs to ACS and APD (F3). Layer 3 over ζ consists of the abelian twists only; their tensor powers are moments, covered by K2. A Deligne base must be non-abelian and does not come from products (F1).

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2 fully-proven: complete paper proof, no open dependency
- [x] 2 → 3 formalized: Lean theorems below; each file checked with `lake --old env lean`; `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`

## Theorems

Notation: `B_S = {x ∈ ℝ^k : Σ_j |x_j| ≤ S}`. A *product receiver* of total length `S` is a finite measure `μ` on `ℝ^k` supported in `B_S` together with `Φ ∈ L¹(μ)`. Its response to `z ∈ ℂ^k` is `R(z) = ∫ Φ(x) e^{⟨z, x⟩} dμ(x)`.

For the external power `T^{⊠k}` of the explicit-formula distribution `T(x) = Σ_ρ e^{(ρ−½)x}`, the spectral side of the receiver is `Σ_{ρ_1,…,ρ_k} R(ρ_1 − ½, …, ρ_k − ½)`. A zero tuple of depths `d_j = Re ρ_j − ½` enters through `e^{Σ d_j x_j}`.

### K1. Depth–length conservation

Let `δ ≥ 0` and `|Re z_j| ≤ δ` for all `j`.

1. `|R(z)| ≤ e^{δS} ∫ |Φ| dμ`.
2. On the diagonal, `∫ e^{w Σ_j x_j} dμ = ∫ e^{wu} d(σ_*μ)(u)`, where `σ(x) = Σ_j x_j` and `σ_*μ` is supported in `[−S, S]`. In depth, a k-fold receiver on a repeated zero is a degree-one receiver of length `S`.
3. The bound is sharp. If `μ` is carried by `{x ∈ B_S : Σ_j x_j ≥ S − ε}`, then `Re ∫ e^{δ Σ x_j} dμ ≥ e^{δ(S−ε)} μ(ℝ^k)`.

*Proof.*
1. `|e^{⟨z,x⟩}| = e^{Σ Re z_j x_j} ≤ e^{δ Σ |x_j|} ≤ e^{δS}` on `B_S`. Integrate.
2. Change of variables along `σ`; and `|σ(x)| ≤ Σ|x_j| ≤ S` on `B_S`.
3. The integrand `e^{δσ(x)}` is real and at least `e^{δ(S−ε)}` on the carrier. ∎

*Contrast with Deligne.* For a local system with a stalk eigenvalue `α`, `|α| = q^{n(w/2+d)}` at a point of degree `n`, the `2k`-th tensor power has trace weight `q^{2kn(w/2+d)}` at the *same* length `n`. The global sum costs `q^{n(1+kw)}`, whose base part `q^n` does not grow with `k`. So the depth gain is `2knd` against a fixed base loss `n`. In K1 the depth gain `dS` is tied to the length `S`; no term is left over that does not scale.

### K2. The free region of every product order ends at total length equal to the threshold

Take a Dirichlet polynomial `D(ξ) = Σ_{n∈s} c_n e^{2πiξ log n}` with `s ⊆ [1, X]`, and a window `η ∈ C²` supported in `[−r, r]`.

- If `2r X^k ≤ 1`, the windowed `2k`-th moment is exactly its multiplicative diagonal:
  `∫ pairTransform_η(ξ) |D(ξ)|^{2k} dξ = ‖η‖₂² Σ_{N ≤ X^k} |c^{*k}(N)|²`, where `c^{*k}(N) = Σ_{n_1⋯n_k = N} Π_i c_{n_i}`.
- If `2r X^k > 1` and the data are real and nonnegative, every off-diagonal term is nonnegative (`le_integral_normSq_mul_normSq_expSum_of_nonneg` applied to `D^k`). No argument that uses only coefficient sizes beats the mean-value bound there.

*Proof.*
1. `e^{2πiξ log m} e^{2πiξ log n} = e^{2πiξ log mn}`, so `D^k = Σ_{N ≤ X^k} c^{*k}(N) e^{2πiξ log N}` and `|D|^{2k} = |D^k|²`.
2. Apply the windowed Gram identity `integral_pairTransform_mul_normSq_expSum_eq_diag_add` to `D^k`.
3. For distinct `M < N ≤ Y = X^k`, `log(N/M) ≥ log(1 + 1/M) ≥ 1/(M+1) ≥ 1/Y ≥ 2r`. So the window autocorrelation vanishes at every off-diagonal lag (`weilTest_eq_zero_of_two_mul_le`). ∎

*Meaning.* The free product information is unique factorization: Montgomery for `α < 1`, Rudnick–Sarnak for `Σ|ξ_j| < 2`, the second and fourth moments of ζ. It is exhausted at total length `T` for every `k`. Combined with K1, a product receiver inside the free region sees depth no better than a degree-one receiver at the threshold, and those yield only density bounds. Beyond the threshold the input is signed near-coincidence counting of products (F2).

The archimedean family `t ↦ D(σ + it)` is a base with a fixed loss, the length of the `t`-interval, and its tensor powers are exactly these moments. So the tensor-power trick over this base is K2. In particular, its free region ends at `X^k ≍ T`.

### K3. Künneth positivity is point-count positivity

Let `D` be a curve datum with point counts `N_n`. A *Künneth–Adams count* is `N_{m}(n) = Π_{i<k} N_{m_i n}` with all `m_i ≥ 1`. This is the ghost sequence of an external product of Adams twists. Its zeta series is `σ(g) = exp(Σ_{j≥1} g(j) X^j/j)`, the symmetric powers in λ-ring form. The following are equivalent:

1. `N_n ≥ 0` for all `n ≥ 1`;
2. every Künneth–Adams count is `≥ 0`;
3. every `σ`-series of a Künneth–Adams count has real nonnegative coefficients.

The golden datum `1 − 5X + 5X²` over `𝔽₅` satisfies 1–3 and is not pure. Hence no positivity statement about external products, Adams twists or symmetric powers of a curve's counts implies RH for curves. Purity is the Hodge index on the Frobenius span (`hodgeIndexOnSpan_iff_unitary`), a positivity of correspondences.

*Proof.*
- 1 ⇒ 2: products of nonnegative reals.
- 2 ⇒ 3: Newton–Witt gives `(n+1)σ_{n+1} = Σ_{j≤n} σ_j g(n+1−j)` with every index `n+1−j ≥ 1`. Strong induction gives `σ_n` real and `≥ 0`.
- 3 ⇒ 1: `σ_1(g) = g(1)`, and the count with `k = 1`, `m = (n)` has `g(1) = N_n`.
- Golden: `goldenDatum_pointCount_nonneg`, `goldenDatum_not_unitary`. ∎

## Verdict on AKT

- **External products** (layer 1) are depth-homogeneous (K1), and their free region ends at the threshold for every order (K2). Beyond the threshold their content is signed near-coincidence cancellation, which is F2 as TTPC and SquareRootThreshold pose it.
- **Correspondences** (layer 2) carry the non-scaling budget `τ(0)`: Hasse–Weil is `|τ(m)| ≤ τ(0)` (`curve_rh_tfae`). Over ℤ the same law at resolution `η` is square-root precision for primes in intervals `[y, y(1+η)]` with a constant independent of `y`, which is RH. Proving it needs the Hodge index or Riemann–Roch on the scaling surface (F3, ACS/APD). Successor graphs are moved diagonals: their lag `log(1 + h/n)` puts them at the Nyquist scale, so their intersection numbers are twin-prime sums at `X ≍ T` (F2). They supply no effectivity of their own.
- **Bases** (layer 3): the only families definable from ζ are twists, which are abelian, and their tensor powers are moments (K2). The Deligne mechanism needs a non-abelian base, which is not a product construction (F1).

So AKT is not an independent mechanism. Its product layer reduces to F2, its correspondence layer is F3, and its base layer is F1. K1–K3 are its positive survivors and the content of the folder `ArithmeticKunnethTheory/`.

## Lean

Folder `formal/GaloisForLFunctions/ArithmeticKunnethTheory/`, umbrella `ArithmeticKunnethTheory.lean` (imported from `MainTheorems.lean`).

- **K1** (`ProductReceiversSeeDepthOnlyThroughTotalLength`): `norm_productResponse_le`, `integral_cexp_diag_eq_integral_map`, `ae_abs_le_of_map_sum`, `exp_mul_le_re_integral_cexp_diag`.
- **K2** (`ProductMomentsAreDiagonalBelowTheThreshold`): `expSum_pow_eq_powSum`, `integral_pairTransform_mul_normSq_pow_eq_diag`, `integral_normSq_pow_eq_diag_add_offDiag_nonneg`.
- **K3** (`KunnethPositivityIsPointCountPositivity`): `exists_sigmaCoeff_eq_ofReal_nonneg`, `kunneth_positivity_tfae`, `goldenDatum_kunneth_positive_not_pure`.

## No-go closure

- **Exact killing theorem/mechanism:** K1 (depth enters only through the total length), K2 (the free region ends at total length `T` for every product order) and K3 (Künneth positivity equals `N_n ≥ 0`, which the golden datum satisfies).
- **Strongest positive survivor:** K1, K2 and K3 themselves. Each is a sharp boundary: K1 is attained on the diagonal, K2 is exact below the threshold with nonnegative off-diagonal above it, and K3 is an equivalence.
- **New insight:** Products of spectra are where purity statements *land* (Rudnick–Sarnak, function-field correlations via Deligne), not where they come from. The only non-scaling terms are a base loss (F1) and the correspondence budget `τ(0)` (F3).
- **Status:** dependency-closed; K1–K3 formalized (see Lean).

## Log
- 2026-10-25 — created; paper proofs; formalized.
