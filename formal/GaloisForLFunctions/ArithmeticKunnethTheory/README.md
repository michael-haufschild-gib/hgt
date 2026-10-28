# Arithmetic Künneth Theory (AKT)

Namespace `GaloisForLFunctions.ArithmeticKunnethTheory`; umbrella `ArithmeticKunnethTheory.lean`.

**Question.** Over $\mathbb F_q$ both proofs of purity use products: Weil uses $C\times C$, Deligne tensor powers over a
base. Which products of an arithmetic spectrum carry a term that does **not** scale with the amplification — the only
kind of term that can turn positivity into a rate?

**Answer for the spectrum itself: none.** A product of any order sees depth only through its total length; its free
region ends at the square-root threshold; its positivity content over $\mathbb F_q$ is positivity of point counts.

---

## 1. Place in the research

Every exhaustion theorem in the corpus is an instance of **depth homogeneity**: whatever a mechanism gains on a zero's
depth it pays in arithmetic length. Purity proofs break it with a non-scaling term: Deligne's fixed base loss
(tensor powers raise local weight), Weil's fixed budget $\tau(0)=2g$ (Frobenius power grows). Both live on products.

**Three layers** of product constructions:

| Layer | What is multiplied | Scaling class | Owner of what remains |
|---|---|---|---|
| 1. Spectrum | zero tuples: $T^{\boxtimes k}$, $k$-level receivers, moments, Künneth/symmetric powers | **homogeneous** | beyond-threshold signed near-coincidences: TTPC, SRT |
| 2. Correspondences | graphs on the product: Frobenius, Hecke, successor; Weil pairing | **non-scaling budget** $\tau(0)$ | its positivity is Hodge index: ACS, APD |
| 3. Families over a base | fibres, tensor powers of a coefficient system | over $\zeta$ alone: abelian twists = moments | a non-abelian base |

AKT is not a route: it proves layer 1 cannot supply the missing term, maps layers 2–3, and tests new product constructions.

| Programme | Interface |
|---|---|
| TransThresholdPairCorrelation | Layer 1 beyond threshold in degree two |
| SquareRootThreshold | Windowed Gram identity; extended here to every product order |
| ArithmeticCastelnuovoSeveri | Curve data, λ-ring (`sigmaSeries`), golden datum; layer 2 |
| ArithmeticPositiveDuality | `curve_rh_tfae`: the layer-2 budget $|\tau(m)|\le\tau(0)$ |
| StripBochnerWeilForcing, MultiplicativePositivityGeometry | Height coupling and Euler-factor-wise products: layer-1 instances |
| ArithmeticCorrelationGeometry | Gauge Jensen turns AKT homogeneity into a linear loss law |
| BezoutValuationIncidence, SignedSuccessorArithmetic, BiarithmeticGeometry | Additive correspondences; successor graphs = moved diagonals |

---

## 2. Why

**Over $\mathbb F_q$.** Künneth: $N_n(C^k)=N_n^k$. Weil: Hodge index on $C\times C$, genus as fixed budget. Deligne: the $2k$-th
tensor power has local weight $|\alpha|^{2kn}$ against global cost $q^{n(1+kw)}$; the base part $q^n$ does not grow with $k$, so
the $2k$-th root removes it.

**Over $\mathbb Z$.** $\operatorname{Spec}\mathbb Z\times\operatorname{Spec}\mathbb Z$ is missing, but its trace exists: external powers of $T(x)=\sum_\rho e^{(\rho-1/2)x}$,
product Dirichlet polynomials, $k$-level correlations, kernels on $\mathbb N\times\mathbb N$. For the spectrum:
- a $k$-linear receiver sees depths through $e^{\sum d_jx_j}\le e^{\delta S}$ on total length $S$ — one receiver of length $S$;
- $D^k$ has length $X^k$; its windowed mean value is diagonal exactly up to $X^k=1/(2r)$ (Montgomery $\alpha<1$, Rudnick–Sarnak
  $\sum|\xi_j|<2$, second and fourth moments are this one free region);
- over $\mathbb F_q$, positivity of all Künneth–Adams counts and their zeta series ⇔ $N_n\ge0$; the golden fake curve has it.

Products of the spectrum are where purity *lands*, not where it comes from.

---

## 3. Objects and language

| Term | Meaning | Lean |
|---|---|---|
| Product receiver | measure $\mu$ on $\mathbb R^k$, weight $\Phi$; response $\int\Phi e^{\langle z,x\rangle}d\mu$ at $z_j=\rho_j-\tfrac12$ | `productResponse`, `totalLength` |
| Diagonal image | image under $x\mapsto\sum x_j$ | `integral_cexp_diag_eq_integral_map` |
| Product polynomial | $D^k$, support $\{n_1\cdots n_k\}$, coefficients $c^{*k}$ | `powSupport`, `powCoeff` |
| Free region / threshold | $2rX^k\le1$; total length $\asymp T$ | — |
| Künneth–Adams count | $n\mapsto\prod_iN_{m_in}$ | `kunnethCount` |
| λ-ring exponential | $\sigma(g)=\exp(\sum g(j)X^j/j)$ | `sigmaSeries`, `sigmaCoeff` |

**Scaling vocabulary.** *Gain*: factor by which a depth-$\delta$ zero enlarges a receiver; *cost*: noise or trivial bound
to beat; *homogeneous*: same exponent in arithmetic length; *non-scaling term*: a base loss or budget fixed while the
gain grows; *moved diagonal*: successor graph $n\mapsto n+h$, lag $\log(1+h/n)\to0$ (Nyquist scale of the diagonal).

---

## 4. Mechanisms

1. **Laplace bound on the support**: depth reaches a receiver only through total length; $k$ does not appear.
2. **Diagonal pushforward**: on a repeated zero a product receiver *is* a degree-one receiver of the same length; sharp.
3. **Multiplicativity of frequencies** + $1/Y$-separation of logs ⇒ below threshold the only coincidences are product
   equalities (unique factorization).
4. **Aligned near-coincidence mass**: beyond threshold, size information is stuck at the mean-value bound for every
   order; only signed height-phase information remains.
5. **Newton–Witt recursion** uses only positive ghost indices ⇒ Künneth positivity collapses to $N_n\ge0$.
6. **Base contrast (Deligne)**: a non-scaling base loss needs local data over a fixed base; $\zeta$'s zeros are global, the
   only families definable from $\zeta$ are abelian twists, whose tensor powers are twists again (moments).
7. **Budget contrast (Weil)**: $|\tau(m)|\le\tau(0)$ is a two-point Gram inequality of a correspondence; over $\mathbb Z$ at resolution
   $\eta$ it is RH. Products of the spectrum do not prove it.

---

## 5. Pillar theorems

1. **Depth–length conservation** for every order (`norm_productResponse_le`, `integral_cexp_diag_eq_integral_map`,
   `exp_mul_le_re_integral_cexp_diag`).
2. **The free region ends at the threshold for every product order** (`expSum_pow_eq_powSum`,
   `integral_pairTransform_mul_normSq_pow_eq_diag`, `integral_normSq_pow_eq_diag_add_offDiag_nonneg`).
3. **Künneth positivity is point-count positivity**; golden datum is Künneth-positive and impure
   (`kunneth_positivity_tfae`, `goldenDatum_kunneth_positive_not_pure`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| Tensor powers amplify depth | Only local data over a fixed base; on one spectrum gain ≤ total length |
| $k$-level correlations are free beyond RS support for large $k$ | Free region ends at total length $T$ for every $k$ |
| Positivity of counts of $C^k$, $\operatorname{Sym}^kC$, Adams twists forces purity | It is $N_n\ge0$; golden datum |
| More small primes make near-coincidences cheaper | Same total length, same depth; order changes constants only |
| The archimedean family is a Deligne base | Abelian; its tensor powers are moments |
| Family averages over $\chi\bmod q$ amplify | Abelian and homogeneous |
| Successor graphs supply effective classes | Moved diagonals; their intersection numbers are twin-prime sums |
| Function-field twin-prime theorems show products cause purity | They are consequences of purity |
| Homogeneity retires the product side | Beyond threshold the signed near-coincidence content is live (TTPC, SRT) |
| A constant-factor $k$-fold gain is amplification | Amplification = exponent gain against a fixed cost |
| Products = correspondences | $T^{\boxtimes k}$ multiplies spectra (layer 1); the Weil pairing pulls $T$ back along $x-y$ (layer 2) |

---

## 7. Open problems

1. **Scaling-class theorem for all layer-1 receivers**: mixed-sign $k$-level receivers (distinct-zero
   inclusion–exclusion), Nyquist-renormalized diagonals, receivers averaged over twists — gain exponent ≤ depth × total length.
2. **Constants-only law beyond threshold**: at equal total length, $k$-fold detection needs the pair length up to a
   factor depending only on $k$.
3. **Conductor homogeneity**: formal no-go for family averages over $\chi\bmod q$.
4. **Abelian-base no-go**: Euler-factor-wise products of $\zeta(s+i\tau_j)$ reduce to pillar 2.
5. **Base axioms**: simple pole, no zeros, self-dual system with nonnegative even tensor powers and computable pole
   part; prove multiplicatively definable data admit over-regular Beurling countermodels.
6. **Moved diagonals**: intersection theory of successor graphs at Nyquist resolution; regularized self-intersection
   ↔ pair correlation at $\alpha=1$ (TTPC interface).
7. **Budget at resolution $\eta$**: split $T_\eta(0)$ into archimedean and polar parts; state $|T_\eta(x)|\le T_\eta(0)$ as a
   correspondence statement (APD/ACS interface).

## 8. Tools to build

Scaling-class calculus (gain/cost exponents); $k$-level inclusion–exclusion in product-receiver form; family receivers
over twists; Nyquist renormalization of diagonals; successor-graph intersection numbers; base axioms with a Beurling
test harness.

## 9. Success criteria and conventions

Success is either a product construction with a proved non-scaling term and an unconditional zero statement beyond its
total length, or a complete map (homogeneity for all layer-1 and abelian layer-3 constructions; layer 2 reduced to a
stated Hodge-index statement). A contribution states layer, order, total length, gain and cost exponents; calibrates
over $\mathbb F_q$ and on golden datum, Beurling systems, shifted pairs; does not count constants as amplification.
Coordinates: $x=\log n$, depth $d=\Re\rho-\tfrac12$. Use ACS `CurveDatum`, `sigmaSeries` and APD `CurveDatum'`; window lemmas
from SquareRootThreshold; type pushforward maps explicitly as `Fin k → ℝ` to `ℝ`.
