# Arithmetic Künneth Theory (AKT)

Products of arithmetic spectra: external powers of the explicit-formula distribution, product
Dirichlet polynomials, k-level receivers, Künneth and symmetric powers of curves, correspondences
on the product, and families over a base. Over `𝔽_q` both proofs of purity use products: Weil uses
`C × C`, Deligne uses tensor powers over a base. AKT asks which products of an arithmetic spectrum
carry a term that does **not** scale with the amplification, since only such a term can turn
positivity into a rate. Its first theorems answer this for the spectrum itself. A product of any
order sees depth only through its total length. Its free region ends at the square-root threshold.
Its positivity content over `𝔽_q` is the positivity of point counts.

Namespace `GaloisForLFunctions.ArithmeticKunnethTheory`; umbrella `ArithmeticKunnethTheory.lean`.

---

## 1. Place in the research

**The question AKT owns.** Every exhaustion theorem in the corpus is an instance of *depth
homogeneity*: whatever a mechanism gains on a zero's depth it pays for in arithmetic length (walls
ledger face 1.15). Purity proofs break homogeneity with a term that does not scale:

- **Deligne:** the loss of a one-dimensional base stays fixed while tensor powers raise the local
  weight.
- **Weil:** the budget `τ(0) = 2g` stays fixed while the Frobenius power grows.

Both terms live on products. AKT is the theory that classifies products of arithmetic spectra by
*scaling class*, decides where a non-scaling term can exist, and hands each surviving question to
its owner.

**Three layers.** Every product construction definable from a source falls into one of them.

| Layer | What is multiplied | Scaling class | Owner of the remaining question |
|---|---|---|---|
| 1. Spectrum | zero tuples: external powers `T^{⊠k}`, k-level receivers, moments, Nyquist diagonals, Künneth and symmetric powers | **homogeneous** (pillars 1–3) | beyond-threshold signed near-coincidences: TTPC, SquareRootThreshold (F2) |
| 2. Correspondences | graphs on the product: Frobenius, Hecke, successor; the Weil pairing | **non-scaling budget** `τ(0)` | its positivity is the Hodge index: ACS, APD (F3) |
| 3. Families over a base | fibres over the points of a base, tensor powers of a coefficient system | over ζ alone: abelian twists, whose tensor powers are moments (pillar 2) | a non-abelian base: F1 |

AKT is not a route by itself: layer 1 cannot supply the missing term. It is the programme that
proves this, maps layers 2 and 3 precisely, and tests any new product construction against the
classification.

| Programme | Interface |
|---|---|
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Layer 1 beyond the threshold in degree two: signed close prime pairs. Pillar 1 shows the k-fold version has the same depth per total length |
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Windowed Gram identity, sub-threshold silence, size bound attained for aligned data. Pillar 2 extends them to every product order |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Curve data, λ-ring of the scaling surface (`sigmaSeries`), Hodge index on the Frobenius span, golden datum. Pillar 3 is built on them; layer 2 is ACS |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | `curve_rh_tfae`: RH for curves ⇔ `|τ(m)| ≤ τ(0)`, the layer-2 budget; quantum budget of multiplicative positivity |
| [StripBochnerWeilForcing](../StripBochnerWeilForcing/README.md) | Coupled multi-channel positivity: it couples heights `Σ vγ`, not depths. A layer-1 instance: boundary collar only |
| [MultiplicativePositivityGeometry](../MultiplicativePositivityGeometry/README.md) | Euler-factor-wise products (twists, harmonic coupling): the multiplicative part of layer 1 |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Bézout structure: the additive correspondences of layer 2 and the near-coincidence counts of layer 1 |
| [SignedSuccessorArithmetic](../SignedSuccessorArithmetic/README.md) | Successor correspondences, which are moved diagonals at the Nyquist scale |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md) | The correspondence algebra of the product at finite resolution |

---

## 2. Why

**Products over `𝔽_q`.** For a curve `C`:

- Künneth gives `H^*(C^k) = H^*(C)^{⊗k}`, with point counts `N_n(C^k) = N_n^k`.
- Weil proves `|N_n − q^n − 1| ≤ 2g q^{n/2}` by the Hodge index on `C × C`. The intersection
  numbers of Frobenius graphs with the diagonal are `N_n`, and the genus enters as a fixed budget.
- Deligne bounds a stalk eigenvalue `α` of a self-dual local system on a curve `U`. The `2k`-th
  tensor power has local trace weight `|α|^{2kn}` at a point of degree `n`, while its global sum costs
  `q^{n(1+kw)}`. The base part `q^n` does not grow with `k`, so the `2k`-th root removes it.

**Products over ℤ.** `Spec ℤ × Spec ℤ` is missing as a geometric object, but its trace exists:
- the external power `T^{⊠k}` of the explicit-formula distribution `T(x) = Σ_ρ e^{(ρ−½)x}`;
- product Dirichlet polynomials and their moments;
- k-level correlations of zeros;
- correspondences given by kernels on `ℕ × ℕ`.

The review that founded AKT conjectured that some product carries a term that does not scale.

**The answer for the spectrum.** It does not.
- A k-linear receiver sees a tuple of depths `d_j` through `e^{Σ d_j x_j}`. On total length `S` this
  is at most `e^{δS}`, the gain of one receiver of length `S`, whatever `k` is (pillar 1).
- The `k`-th power of a polynomial of length `X` is a polynomial of length `X^k`. Its windowed mean
  value is exactly diagonal up to `X^k = 1/(2r)` and no further (pillar 2). Montgomery's `α < 1`,
  Rudnick–Sarnak's `Σ|ξ_j| < 2`, and the second and fourth moments of ζ are this one free region.
- Over `𝔽_q`, positivity of all Künneth–Adams counts and of all their zeta series is equivalent to
  `N_n ≥ 0`. The golden fake curve has this and is impure (pillar 3).

Products of the spectrum are where purity statements land. Rudnick–Sarnak and the function-field
prime correlations obtained through Deligne are consequences of purity, not causes of it.

---

## 3. Objects and language

**Product receivers.** A product receiver of order `k` is a measure `μ` on `ℝ^k` with a weight
`Φ ∈ L¹(μ)`. Its response is `R(z) = ∫ Φ(x) e^{⟨z,x⟩} dμ(x)`, read at `z_j = ρ_j − ½`.

| Term | Meaning | Lean |
|---|---|---|
| total length | `Σ_j |x_j|` on the support | `totalLength` |
| response | `∫ Φ e^{⟨z,x⟩} dμ` | `productResponse` |
| diagonal image | image of `μ` under `x ↦ Σ_j x_j`, a degree-one receiver on `[−S, S]` | `Measure.map` in `integral_cexp_diag_eq_integral_map` |
| depth | `d = Re ρ − ½` | — |

**Product polynomials.** `D(ξ) = Σ_{n∈s} c_n e^{2πiξ log n}`.

| Term | Meaning | Lean |
|---|---|---|
| product support | `{n_1 ⋯ n_k : n_i ∈ s}` | `powSupport` |
| product coefficient | `c^{*k}(N) = Σ_{n_1⋯n_k = N} Π c_{n_i}` | `powCoeff`, `powCoeffReal` |
| windowed `2k`-th moment | `∫ pairTransform_η · |D|^{2k}` | — |
| free region | `2rX^k ≤ 1`: the moment is its multiplicative diagonal | — |
| threshold | total length `X^k = 1/(2r)`, i.e. `≍ T` at height `T` | — |

**Künneth data over `𝔽_q`.** A curve datum `D` with point counts `N_n` (`CurveDatum.pointCount`).

| Term | Meaning | Lean |
|---|---|---|
| Adams twist | `ψ^m`: the ghost sequence `n ↦ g(mn)` | — |
| Künneth–Adams count | `n ↦ Π_i N_{m_i n}`, ghost sequence of `ψ^{m_1}C × ⋯ × ψ^{m_k}C` | `kunnethCount` |
| λ-ring exponential | `σ(g) = exp(Σ g(j)X^j/j)`, zeta series and symmetric powers | `sigmaSeries`, `sigmaCoeff` |

**Scaling vocabulary.**
- **Gain:** the factor by which a zero of depth `δ` enlarges a receiver.
- **Cost:** the size of the noise or trivial bound the gain must beat.
- **Homogeneous:** gain and cost have the same exponent in the arithmetic length.
- **Non-scaling term:** a cost that stays fixed while the gain grows: a *base loss* or a
  *budget*.
- **Layer:** spectrum, correspondence or base (§1).
- **Moved diagonal:** a successor graph `n ↦ n + h`. Its logarithmic lag `log(1 + h/n)` tends to
  `0`, so it sits at the Nyquist scale of the diagonal.

---

## 4. Mechanisms

1. **Laplace bound on the support.** `|e^{⟨z,x⟩}| = e^{Σ Re z_j x_j} ≤ e^{δ Σ|x_j|}`. Depth reaches a
   receiver only through its total length, and the order `k` does not appear.
2. **Diagonal pushforward.** On a repeated zero the response is the Laplace transform of the
   diagonal image, so a product receiver *is* a degree-one receiver of the same length. Sharpness:
   a receiver carried near `Σ x_j = S` attains `e^{δ(S−ε)}`.
3. **Multiplicativity of frequencies.** `e^{2πiξ log m}e^{2πiξ log n} = e^{2πiξ log mn}`, so `D^k` is a
   polynomial of length `X^k`. Distinct integers in `[1, Y]` are `1/Y`-separated in logarithm, so
   below the threshold the only coincidences are equalities of products: unique factorization.
4. **Aligned near-coincidence mass.** For nonnegative data and a nonnegative window, every
   off-diagonal term is nonnegative. Beyond the threshold, size information is stuck at the
   mean-value bound for every product order. What remains is the *signed* information carried by
   the height phase.
5. **Newton–Witt recursion.** `(n+1)σ_{n+1} = Σ_{j≤n} σ_j g(n+1−j)` uses only positive ghost
   indices. So λ-ring positivity follows from ghost positivity, and Künneth positivity collapses to
   `N_n ≥ 0`.
6. **The base contrast (Deligne).** A non-scaling base loss requires local data: an eigenvalue
   attached to a point of a base whose own cost is fixed. ζ's zeros are global data of `Spec ℤ`,
   and the only families definable from ζ are twists by characters. These are abelian, and their
   tensor powers are twists again. The archimedean family `t ↦ D(σ + it)` is a base with a fixed
   loss, and its tensor powers are exactly the moments of mechanism 3.
7. **The budget contrast (Weil).** `|τ(m)| ≤ τ(0)` is a two-point Gram inequality for a
   correspondence pairing. Its budget does not scale, and it is the Hodge index on the Frobenius
   span. Over ℤ at resolution `η` it says that primes in `[y, y(1+η)]` are counted with
   square-root error and a constant independent of `y`, which is RH. Products of the spectrum do
   not prove it.

---

## 5. Pillar theorems

1. **Depth–length conservation** (`ProductReceiversSeeDepthOnlyThroughTotalLength`):
   - `norm_productResponse_le`: `|R(z)| ≤ e^{δS} ∫|Φ| dμ` for total length `S` and depths `≤ δ`, for every order `k`;
   - `integral_cexp_diag_eq_integral_map`, `ae_abs_le_of_map_sum`: the diagonal is a degree-one receiver on `[−S, S]`;
   - `exp_mul_le_re_integral_cexp_diag`: sharpness.
2. **The free region ends at the threshold for every product order**
   (`ProductMomentsAreDiagonalBelowTheThreshold`):
   - `expSum_pow_eq_powSum`: `D^k` is the polynomial with coefficients `c^{*k}`;
   - `integral_pairTransform_mul_normSq_pow_eq_diag`: if `2rX^k ≤ 1`, the windowed `2k`-th moment is exactly `‖η‖² Σ_N |c^{*k}(N)|²`;
   - `integral_normSq_pow_eq_diag_add_offDiag_nonneg`: beyond the threshold, for nonnegative data, the moment is the diagonal plus a nonnegative near-coincidence sum.
3. **Künneth positivity is point-count positivity** (`KunnethPositivityIsPointCountPositivity`):
   - `exists_sigmaCoeff_eq_ofReal_nonneg`: Newton–Witt positivity;
   - `kunneth_positivity_tfae`: `N_n ≥ 0` ⇔ all Künneth–Adams counts `≥ 0` ⇔ all their zeta series have nonnegative real coefficients;
   - `goldenDatum_kunneth_positive_not_pure`: the golden fake curve is Künneth-positive, impure, and fails the Hodge index on its Frobenius span.

Used from the corpus: `SquareRootThreshold.integral_pairTransform_mul_normSq_expSum_eq_diag_add`,
`SquareRootThreshold.le_integral_normSq_mul_normSq_expSum_of_nonneg`,
`SquareRootThreshold.weilTest_self_eq_zero_of_le`,
`ArithmeticCastelnuovoSeveri.CurveDatum.hodgeIndexOnSpan_iff_unitary`,
`ArithmeticCastelnuovoSeveri.goldenDatum_not_unitary`,
`ArithmeticCastelnuovoSeveri.goldenDatum_pointCount_nonneg`,
`ArithmeticPositiveDuality.CurveDatum'.curve_rh_tfae`.

---

## 6. Traps

| Trap | Correct statement |
|---|---|
| Tensor powers amplify depth | Only local data over a fixed base. On one spectrum, depth gain is bounded by the total length (pillar 1) |
| k-level correlations are free beyond Rudnick–Sarnak support for large `k` | The free region ends at total length `T` for every `k` (pillar 2) |
| Positivity of point counts of `C^k`, `Sym^k C`, Adams twists forces purity | It is `N_n ≥ 0`; the golden datum has it and is impure (pillar 3) |
| Products of many small primes make near-coincidences cheaper | Same total length, same depth. The order changes constants (the `k!` of the diagonal), not exponents |
| The archimedean family is a Deligne base | It is a base with fixed loss, but abelian; its tensor powers are moments, free only up to `X^k ≍ T` |
| Coupled multi-channel positivity breaks homogeneity | It couples heights; depth enters through `1 − β` only, giving a boundary collar |
| Family averages over `χ mod q` amplify | Primes start at `q + 1` while the zero count grows by `φ(q)`. The family is abelian and homogeneous |
| Successor graphs supply effective classes | They are moved diagonals at the Nyquist scale; their intersection numbers are twin-prime sums (F2) |
| Function-field twin-prime theorems show that products cause purity | They are consequences of Deligne's purity applied to configuration spaces |
| Homogeneity retires the product side | Beyond the threshold the signed near-coincidence content is live: it is F2, owned by TTPC and SquareRootThreshold |
| A k-fold gain by a constant is amplification | Amplification means a gain in the exponent against a fixed cost |
| Products and correspondences are the same | `T^{⊠k}` multiplies spectra (homogeneous); the Weil pairing pulls `T` back along `(x, y) ↦ x − y` (budget, layer 2) |

---

## 7. Questions AKT aims to answer

1. **Classification.** Which product constructions definable from an arithmetic source carry a term
   that does not scale with their amplification? For layer 1 the answer is none (pillars 1–2). The
   open part is the precise class statement for mixed-sign, renormalized and family receivers.
2. **Content of a product.** What does a product of spectra know beyond its total length? Below
   the threshold, unique factorization; beyond it, signed near-coincidences of products. Is the
   k-fold signed problem ever easier than the pair problem at the same total length?
3. **Bases.** What data would a non-abelian base under ζ have to provide? Can such data be defined
   from additive structure, given that multiplicatively definable data admit Beurling
   countermodels?
4. **Correspondences.** Which part of the layer-2 budget `τ(0)` at resolution `η` can product data
   compute (it is archimedean and polar), and which part needs the Hodge index or Riemann–Roch?

---

## 8. Open research topics

1. **Scaling-class theorem for all layer-1 receivers.** Extend pillar 1 to:
   - mixed-sign k-level receivers with distinct-zero inclusion–exclusion;
   - Nyquist-renormalized diagonals as limits of product receivers;
   - receivers averaged over a family of twists.

   The target is one statement: the gain exponent is at most the depth times the total length.
2. **Constants-only law beyond the threshold.** At equal total length, k-fold detection of a depth
   `δ` needs at least the pair detection length up to a factor depending only on `k`. A model
   computation exists; the theorem does not.
3. **Conductor homogeneity.** Make the family-average no-go formal. Averaging over `χ mod q` makes
   the form archimedean up to aperture `½ log(q+1)`, while visibility needs `q^δ ≳ φ(q)`.
4. **Abelian-base no-go.** Euler-factor-wise products of twists `ζ(s + iτ_j)` have unitary local
   parameters, and their zero sets are translates. Formalize this, and that tensor powers over any
   abelian family reduce to pillar 2.
5. **Base axioms (F1 interface).** State the positivity data of a base: a simple pole, no zeros, a
   self-dual system whose even tensor powers have nonnegative log-coefficients, and a computable pole
   part. Prove that data definable from multiplicative structure alone admit over-regular Beurling
   countermodels.
6. **Moved diagonals.** Build the intersection theory of successor graphs with scaling cycles at
   Nyquist resolution. Identify the regularized self-intersection (the genus at resolution `η`) with
   pair correlation at `α = 1`, as an interface with TTPC.
7. **Budget at resolution `η`.** Split `T_η(0)` into its archimedean and polar parts (computable) and
   state the two-point law `|T_η(x)| ≤ T_η(0)` as a correspondence statement, as an interface with
   APD and ACS.
8. **Function-field direction.** Over `𝔽_q[T]`, write prime-pair correlations as point counts of
   configuration varieties whose errors are bounded by purity. This records that layer-1
   correlations are downstream of purity.

---

## 9. Tools

**Built:**
- product receivers on `ℝ^k` with the total-length Laplace bound and the diagonal pushforward;
- product Dirichlet polynomials (`powSupport`, `powCoeff`) with the exact sub-threshold diagonal and the aligned off-diagonal law at every order;
- Newton–Witt positivity and the Künneth–Adams counts on ACS curve data.

**To build:**
- a scaling-class calculus (gain and cost exponents of a construction);
- k-level inclusion–exclusion in product-receiver form;
- family receivers over twists;
- Nyquist renormalization of diagonals as limits of product receivers;
- successor-graph intersection numbers on the scaling surface;
- base axioms with a Beurling test harness.

---

## 10. Success criteria

AKT succeeds in one of two ways:

- **A route.** A product construction definable from an arithmetic source, with a proved term that
  does not scale with its amplification and an unconditional statement about zeros of ζ beyond
  what its total length gives.
- **A complete map.** Homogeneity proved for every layer-1 construction and every abelian layer-3
  construction; layer 2 reduced to a stated Hodge-index or effectivity statement; each surviving
  question stated precisely in the programme that owns it (F1, F2, F3).

A contribution must:

- **State its layer and scaling class:** product order, total length, the gain exponent and the
  cost exponent.
- **Calibrate:** specialize over `𝔽_q` correctly, either as a Künneth, Weil or Deligne statement or
  as a stated failure, and be tested on the golden datum, Beurling systems, shifted pairs
  `ζ(s−a)ζ(s+a)` and the pole-order models.
- **Not count constants as amplification:** a gain is a change of exponent against a fixed cost.
- **Be unconditional and in Lean:** no imported zero location, no assumption binders carrying the
  missing input.
- **Respect ownership:** beyond-threshold signed near-coincidence estimates go to TTPC and
  SquareRootThreshold, Hodge index and effectivity to ACS and APD. AKT owns the classification and
  the product calculus.

---

## 11. Working conventions

- State coordinates: log-scale `x = log n`, depth `d = Re ρ − ½`, total length in the units of the
  receiver.
- Products of spectra (`T^{⊠k}`, `D^k`) and correspondences (kernels on `ℕ × ℕ`, Weil pairing) are
  different layers; say which one a statement is about.
- Over `𝔽_q`, use the ACS curve data (`CurveDatum`, `pointCount`, `sigmaSeries`) and APD's
  `CurveDatum'` for the trace sequence; do not redefine them.
- Lean: products of finite exponential sums via `Finset.prod_univ_sum` and
  `Finset.sum_fiberwise_of_maps_to`; window lemmas from `SquareRootThreshold`
  (`weilTest_self_eq_zero_of_le`, `integral_pairTransform_mul_normSq_expSum_eq_diag_add`); type the
  pushforward map explicitly as `Fin k → ℝ` to `ℝ`.
