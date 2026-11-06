# Arithmetic Künneth Theory (AKT)

Namespace `GaloisForLFunctions.ArithmeticKunnethTheory`; umbrella `ArithmeticKunnethTheory.lean`. All results
unconditional.

## 1. Motivation

Over $\mathbb F_q$ both proofs of purity use products: Weil the Hodge index on $C\times C$ (fixed budget $2g$), Deligne
tensor powers over a base (base loss fixed while local weight is powered). Over $\mathbb Z$ the surface
$\operatorname{Spec}\mathbb Z\times\operatorname{Spec}\mathbb Z$ is missing, but products of the spectrum exist: external
powers of $T(x)=\sum_\rho e^{(\rho-\frac12)x}$, product Dirichlet polynomials, Künneth and Adams counts. AKT asks whether any
product of the spectrum itself carries a term that does not scale with the amplification. Answer: none. Products of the
spectrum are depth-homogeneous; the non-scaling term must come from correspondences or a base.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Product receiver | `productResponse` | $R(z)=\int\Phi(x)e^{\langle z,x\rangle}d\mu$ on $\mathbb R^k$, $z_j=\rho_j-\tfrac12$ |
| Total length | `totalLength` | $\sum_j|x_j|$ |
| Product polynomial | `powSupport`, `powCoeff` | $D^k$ on products $n_1\cdots n_k\le X^k$, coefficients $c^{*k}(N)$ |
| Log frequency | `logFreq` | $\log n$ |
| Künneth–Adams count | `kunnethCount` | $n\mapsto\prod_iN_{m_in}$ for $\psi^{m_1}C\times\cdots\times\psi^{m_k}C$ |
| λ-ring exponential | `sigmaSeries`, `sigmaCoeff` (ACS) | $\exp(\sum_{j\ge1}g(j)X^j/j)$ |

## 3. Language

- **Gain**: factor by which a depth-δ zero enlarges a receiver. **Cost**: arithmetic length to pay. **Homogeneous**: gain
  exponent = depth × total length.
- **Non-scaling term**: a base loss or budget fixed while the gain grows (Deligne base, Weil $\tau(0)$).
- **Free region**: product order and window with $2rX^k\le1$; below it moments see only unique factorization.
- **Layers**: (1) products of the spectrum; (2) correspondences on the product (Frobenius, Hecke, successor graphs);
  (3) families over a base. AKT closes layer 1.

## 4. Mechanisms

1. **Laplace bound on the support**: $|e^{\sum z_jx_j}|\le e^{\delta\cdot\text{totalLength}}$; order $k$ never enters.
2. **Diagonal pushforward**: on a repeated zero $(w,\dots,w)$ the response is the Laplace transform of $\mu$ pushed forward by
   $x\mapsto\sum x_j$, a measure on $[-S,S]$; sharp for positive receivers carried near $\sum x_j=S$.
3. **Multiplicativity of frequencies**: $D^k$ is again an integer-frequency polynomial of length $X^k$; distinct integers in
   $[1,Y]$ are $1/Y$-separated in $\log$ ⇒ off-diagonal Weil test terms vanish when $2rX^k\le1$.
4. **Aligned near-coincidence mass**: beyond threshold, nonnegative data give diagonal + nonnegative off-diagonal; size
   information alone cannot improve.
5. **Newton–Witt recursion** $(n+1)\sigma_{n+1}=\sum_{j\le n}\sigma_jg(n+1-j)$ uses only positive ghost indices ⇒ all
   product positivities collapse to $N_n\ge0$; $\sigma_1=g(1)$ gives the converse.

## 5. Pillar theorems

| Theorem | Lean | Status |
|---|---|---|
| Depth–length conservation: $|R(z)|\le e^{\delta S}\int|\Phi|d\mu$ for every order | `norm_productResponse_le` | proved |
| Diagonal of a product receiver is a degree-one receiver; sharp | `integral_cexp_diag_eq_integral_map`, `exp_mul_le_re_integral_cexp_diag` | proved |
| $D^k$ is the polynomial on products with coefficients $c^{*k}$ | `expSum_pow_eq_powSum` | proved |
| Below $2rX^k\le1$ the windowed $2k$-th moment is exactly $\|\eta\|^2\sum_N|c^{*k}(N)|^2$ | `integral_pairTransform_mul_normSq_pow_eq_diag` | proved |
| Beyond threshold: diagonal + nonnegative near-coincidence part | `integral_normSq_pow_eq_diag_add_offDiag_nonneg` | proved |
| $N_n\ge0$ ⇔ Künneth–Adams counts ≥ 0 ⇔ all Künneth–Adams zeta coefficients ≥ 0 | `kunneth_positivity_tfae` | proved |
| Golden datum: Künneth-positive, impure, fails Hodge index on its Frobenius span | `goldenDatum_kunneth_positive_not_pure` | proved |
| Every even `SL₂` invariant transforms by the determinant character; odd invariants vanish | `invariant_even_det`, `invariant_odd_eq_zero` | proved |
| Nonzero invariant forms exist in every even degree | `exists_nonzero_even_invariant` | proved |
| Degree-`m` trace moment has exponential rate at most `B` iff every eigenvalue satisfies `‖zᵢ‖^m≤B` | `tensor_moment_bound_iff` | proved |
| One rate across all even degrees ⇔ unit disk; for curve data ⇔ purity ⇔ spectrum-window positivity | `fixed_base_tensor_bound_iff`, `curve_tensor_bound_iff_spectrum_window` | proved |
| Golden Frobenius has every invariant weight and positive even-tensor Euler coefficients, but optimal degree-`m` rate is `φ^m` | `golden_weight_and_coefficient_countermodel`, `golden_tensor_rate_iff` | proved |
| Canonical divisor compression has point spectrum exactly `1/2 + i Im(ρ)` unconditionally | `compressed_eigenvalue_iff`, `compressed_eigenvalues_pure` | proved |
| Frobenius preserves the canonical monodromy-invariant subspace iff RH | `invariant_subspace_stable_iff_riemannHypothesis` | proved |

The last seven rows belong to `WeightFamilies/`. They classify the algebraic input and the required
global estimate; they do not construct an arithmetic family or prove a new purity bound for ζ.

## 6. Tools

**Developed**
- `norm_cexp_sum_le_exp_totalLength`: Laplace weight bound by total length.
- `ae_abs_le_of_map_sum`: support of the diagonal pushforward.
- `inv_le_abs_logFreq_sub`: $1/Y$ log separation.
- `mem_powSupport_bounds`, `powCoeffReal`, `powCoeffReal_nonneg`: product-polynomial calculus.
- `exists_sigmaCoeff_eq_ofReal_nonneg`, `sigmaCoeff_one`: Newton–Witt positivity.

**To build**
- Mixed-sign $k$-level receivers (distinct-zero inclusion–exclusion) in product-receiver form.
- Family receivers averaged over twists $\chi\bmod q$ (conductor homogeneity).
- Nyquist renormalisation of moved diagonals (successor graphs) and their intersection numbers.
- Base axioms (simple pole, no zeros, self-dual system with nonnegative even tensor powers) with a Beurling countermodel test.

## 7. Open questions

1. Scaling-class theorem for all layer-1 receivers: is gain ≤ depth × total length for mixed-sign and twist-averaged receivers?
2. Beyond threshold at equal total length: does order $k$ change only constants?
3. Conductor homogeneity: formal no-go for family averages over Dirichlet characters.
4. Euler-factor-wise products of $\zeta(s+i\tau_j)$ (abelian base): reduce to the moment pillar.
5. Can any base definable from $\zeta$ be non-abelian, or do multiplicatively definable data admit over-regular Beurling
   countermodels?
6. Moved diagonals: regularised self-intersection of successor graphs ↔ pair correlation at α = 1.
7. Budget at resolution η: split $T_\eta(0)$ into archimedean and polar parts as a correspondence statement.

## 8. Traps

| Trap | Fact |
|---|---|
| Tensor powers of the spectrum amplify depth | Gain ≤ $e^{\delta S}$ at total length $S$, any order |
| High-order correlations escape the threshold | Free region ends at total length $X^k=1/(2r)$ for every $k$ |
| Positivity of counts of $C^k$, $\operatorname{Sym}^k$, Adams twists forces purity | It is exactly $N_n\ge0$; golden datum is impure |
| A constant $k$-fold gain is amplification | Amplification = exponent gain against a fixed cost |
| Products = correspondences | $T^{\boxtimes k}$ multiplies spectra; Weil pulls $T$ back along a graph |
| The archimedean family is a Deligne base | It is abelian; its tensor powers are moments |
| Homogeneity retires the product side | Beyond threshold the signed near-coincidence content remains (TTPC, SRT) |

## 9. Context

| Uses | Modules |
|---|---|
| SquareRootThreshold | 1 (windowed off-diagonal identity) |
| ArithmeticCastelnuovoSeveri | 2 (λ-ring of the scaling surface, Frobenius-span Hodge index) |

| Used by | Modules |
|---|---|
| ArithmeticCorrelationGeometry | 1 (gauge moments = product moments below threshold) |
| MainTheorems | umbrella |

| Neighbour | Relation |
|---|---|
| SquareRootThreshold | its windowed Gram identity, extended to every product order |
| TransThresholdPairCorrelation | layer 1 beyond threshold in degree two |
| ArithmeticCastelnuovoSeveri, ArithmeticPositiveDuality | layer 2: correspondences, Hodge index, budget $|\tau(m)|\le\tau(0)$ |
| ArithmeticCorrelationGeometry | gauge Jensen turns this homogeneity into a linear loss law |
| SignedSuccessorArithmetic, BiarithmeticGeometry | successor graphs as moved diagonals |

## 10. Big picture

Every exhaustion theorem in the corpus has the same shape: what a mechanism gains on a zero's depth it pays in
arithmetic length. AKT shows this is not a weakness of particular constructions but a property of multiplying the
spectrum with itself: products, moments, Künneth and Adams powers are all homogeneous, and their positivity content over
finite fields is mere point-count positivity, which impure fake curves satisfy.

The lesson for RH is a sharp division of labour. The term that turns positivity into a rate in the function-field
proofs is a fixed budget of a correspondence (Weil) or a fixed base loss (Deligne); neither is a product of the spectrum.
Over $\mathbb Z$ the search has to target correspondences on the missing surface or a genuinely non-abelian base,
not higher moments or tensor powers of $\zeta$.
