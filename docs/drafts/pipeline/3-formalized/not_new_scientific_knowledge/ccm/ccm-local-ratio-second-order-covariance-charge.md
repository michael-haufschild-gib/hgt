# The completed local-ratio product carries a cofinal second-order covariance charge

- **ID:** `ccm-local-ratio-second-order-covariance-charge`
- **Stage:** 3 — formalized in Lean 4
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent sources:** the local-ratio multipliers and quantized differential of Connes--Consani,
  elementary finite-product differentiation, and Euler's reciprocal-prime divergence
- **Statement:** The canonical finite completed local-ratio multiplier differs from the sum of its
  one-place increments by a factorization-independent covariance anomaly. The anomaly has vanishing
  constant and linear diagonal jets, while its quadratic central jet is strictly negative and has
  cofinally divergent magnitude. Thus the additive local Weil trace and the multiplicative
  prime--Gamma covariance occupy different grades of one source object. Every successful CCM
  positivity construction must retain the quadratic grade in a relative/Schur carrier rather than
  discard it when taking the linear trace.

## 1. Critical-line local ratios

For a prime `p`, put `r_p=p^(-1/2)`, `L_p=log p`, and restrict the local ratio

```text
rho_p(s)=(1-p^(s-1))/(1-p^(-s))
```

to the critical line:

```text
u_p(t)=rho_p(1/2+it)
      =(1-r_p exp(iL_pt))/(1-r_p exp(-iL_pt)).              (1)
```

Then `|u_p(t)|=1`, `u_p(0)=1`, and direct differentiation gives

```text
u_p'(0)=-i b_p,
b_p=2 log(p)/(sqrt(p)-1)>0.                                 (2)
```

For the archimedean ratio

```text
rho_infinity(s)=gamma_infinity(s)/gamma_infinity(1-s),
gamma_infinity(s)=pi^(-s/2)Gamma(s/2),                       (3)
```

the critical restriction satisfies

```text
u_infinity(0)=1,
u_infinity'(0)=-i b_infinity,
b_infinity=log(pi)-psi(1/4)>0.                              (4)
```

The positivity in `(4)` follows, for example, from the classical value
`psi(1/4)=-gamma-pi/2-3log 2`.

## 2. Canonical covariance anomaly

For a finite prime set `F`, let

```text
u_F(t)=u_infinity(t) product_(p in F)u_p(t).                 (5)
```

Define the completed multiplicative covariance anomaly

```text
C_F(t)
 =u_F(t)-1-(u_infinity(t)-1)-sum_(p in F)(u_p(t)-1).         (6)
```

More generally, if the places are indexed by `V={infinity} union F`, the elementary subset
expansion gives

```text
C_F(t)=sum_(I subset V, |I|>=2) product_(v in I)(u_v(t)-1).  (7)
```

Thus `(6)` is independent of any Gauss splitting or pairing of archimedean components with primes.
It is the complete higher-than-linear part of the canonical local-ratio product.

Every factor in `(7)` vanishes at `t=0`, so

```text
C_F(0)=0,
C_F'(0)=0.                                                   (8)
```

Differentiating `(7)` twice leaves only the two-element subsets. Equations `(2)` and `(4)` give

```text
C_F''(0)
 =2 sum_(v<w)u_v'(0)u_w'(0)
 =-2 sum_(v<w)b_vb_w<0                                     (9)
```

whenever at least two places are present. Therefore the covariance anomaly has exact order two at
the central seam.

The prime-only part

```text
C_F^fin(t)
 =product_(p in F)u_p(t)-1-sum_(p in F)(u_p(t)-1)            (10)
```

has the exact curvature

```text
-(C_F^fin)''(0)
 =8 sum_({p,q} subset F)
    log(p)log(q)/((sqrt(p)-1)(sqrt(q)-1)).                   (11)
```

Every summand is strictly positive.

## 3. Cofinal divergence

For `x>1`, the elementary inequality `log x>=1-1/x` gives

```text
b_p
 =2log(p)/(sqrt(p)-1)
 >=2(p-1)/(p(sqrt(p)-1))
 =2(sqrt(p)+1)/p
 >=2/p.                                                      (12)
```

Hence

```text
-(C_F^fin)''(0)>=8 sum_({p,q} subset F)1/(pq).               (13)
```

Along a cofinal exhaustion of the primes,

```text
sum_(p<q, p,q in F)1/(pq)
 =1/2 ((sum_(p in F)1/p)^2-sum_(p in F)1/p^2)
 ->infinity,                                                 (14)
```

because `sum_p 1/p` diverges while `sum_p 1/p^2` converges. Thus the canonical second-order
covariance charge cannot remain bounded in the cofinal finite-place limit.

## 4. Quantized-differential kernel meaning

For critical-line boundary points `x,y`, set

```text
r_v(x,y)=conj(u_v(x))u_v(y).                                 (15)
```

The off-diagonal kernel multiplier in

```text
U_F^*[F_H,U_F]
```

is proportional to

```text
product_v r_v(x,y)-1.                                       (16)
```

The sum of the one-place quantized differentials has multiplier

```text
sum_v(r_v(x,y)-1).                                          (17)
```

Their exact difference is therefore

```text
kappa_F(x,y)
 =sum_(I subset V, |I|>=2)product_(v in I)(r_v(x,y)-1).      (18)
```

Each factor `r_v(x,y)-1` vanishes on the diagonal. Hence `kappa_F` has at least quadratic diagonal
vanishing. Multiplication by the Cauchy/Hilbert kernel, whose local singularity is first order,
leaves a kernel vanishing on the diagonal. This is the local analytic reason that the covariance
anomaly has zero ordinary diagonal trace while the first-order local terms yield the additive Weil
functional.

No global trace-class claim follows from local diagonal cancellation alone. The behavior at
infinity, prime cutoff, and Hardy/Sonin compression remains load-bearing.

## 5. Positive carrier law

The finite source therefore has an exact two-grade constraint:

```text
degree one:
  sum_v(r_v-1)
  -> additive local Weil trace;

degree at least two:
  kappa_F
  -> multiplicative prime--Gamma covariance with divergent central curvature. (19)
```

The second grade is not an arbitrary correction and cannot be consistently set to zero: `(9)`--
`(14)` fix a nonzero, cofinally growing source charge. Conversely it is trace-invisible at degree
one, so the scalar local trace cannot reconstruct it.

Every successful CCM construction must consequently carry `(19)` in a pointed relative object:

1. a Gauss-paired Hardy representative of the canonical covariance class;
2. a principal-relative or Schur block in which the signed covariance is retained before the final
   positive square;
3. a cofinal smoothing/renormalization controlling its divergent curvature; and
4. an index-faithful map from that pointed lift to the shifted-Xi Pick/Weil carrier.

The exact next theorem is a **Gauss-descent theorem**: prove that the analytically compact
Gauss-paired representatives descend, modulo trace-zero conjugation coboundaries, to the canonical
kernel `(18)`, and that the Sonin relative grade is a positive Schur lift of this class with a bound
uniform in the prime cutoff.

## 6. Scope and scientific classification

- `[SEARCH]` The local ratios, Hardy quantized differential, Gauss-paired quasi-inner
  factorization, and trace interpretation are Connes--Consani.
- `[PROVED]` The factorization-independent anomaly `(6)`--`(7)`, exact central curvature `(9)`--
  `(11)`, harmonic lower bound `(13)`, and cofinal divergence `(14)` follow as above.
- `[PROVED]` The kernel anomaly has quadratic diagonal vanishing and therefore contributes no local
  first-order diagonal trace.
- `[NOT PROVED]` No uniform global trace-ideal estimate, Sonin positivity, determinant convergence,
  or divisor-index transport is established.
- `[NOT PROVED]` This theorem does not prove RH.

The result is a route-specific assembly of elementary product calculus and standard local-ratio
formulas. It is useful because it identifies the exact canonical covariance carrier, but it does
not introduce a scientifically new parent mechanism. It is classified as a bridge rather than new
scientific knowledge.

## 7. Lean status

**Formalized unconditionally, 2026-08-04.**  The previous decision ("formalizing only the commutative product
identity would be a routine wrapper") was wrong about what the card's proved content is.  Sections 2
and 3 are not a product identity: they are a jet computation plus an arithmetic divergence, and both
are now formalized unconditionally.

`formal/GaloisForLFunctions/RHTower/CCM/CCMLocalRatioAnomaly.lean` — the place-independent layer:

- `multiplierDefectSum`, **`covarianceAnomaly`** — the objects of `(6)`.
- **`prod_one_add_sub_one_sub_sum`**, **`covarianceAnomaly_eq_sum_powerset`** — equation `(7)`, the
  factorization independence, by the elementary subset expansion.  The powerset is split by
  cardinality, with the `|I| <= 1` part identified as `insert ∅ (image singleton)`.
- **`covarianceAnomaly_insert`** — the recursion `C_(insert x s) = u_x C_s + (u_x - 1) D_s`.  This is
  the device that carries both jet computations and keeps them free of subset combinatorics.
- **`covarianceAnomaly_zero`**, **`hasDerivAt_covarianceAnomaly`** — equation `(8)`.
- **`tendsto_covarianceAnomaly_div_sq`** — equation `(9)`: the quadratic jet is
  `((sum c_v)^2 - sum c_v^2)/2`, i.e. `sum_(v<w) c_v c_w`, so `C_s''(0) = 2 sum_(v<w) c_v c_w`.

  Worth recording: **only first derivatives are used**, even for the quadratic jet.  The card's
  "differentiating twice leaves only the two-element subsets" is exactly the statement that the
  second-order data of each place cancels between the product and the sum of increments; formalizing
  the jet as the limit of `C_s(t)/t^2` makes that cancellation automatic and avoids any second-derivative
  machinery for finite products.
- **`offDiagCharge_eq_sum_offDiag`**, `sum_offDiag_le_sum_offDiag` — the identity
  `(sum b)^2 - sum b^2 = sum_(v != w) b_v b_w` and its termwise comparison.  The off-diagonal form is
  needed because the `(sum)^2 - sum^2` form admits **no** termwise lower bound: the diagonal correction
  has the wrong sign, and `sum_p b_p^2` in fact diverges.  This is a real subtlety in `(13)`.

`formal/GaloisForLFunctions/RHTower/CCM/CCMLocalRatioPlaces.lean` — the finite places:

- **`primeLocalRatio`**, `primeLocalRatio_den_ne_zero`, `primeLocalRatio_num_ne_zero`,
  `primeLocalRatio_zero` — the multiplier `(1 - r e^(iLt))/(1 - r e^(-iLt))` for `|r| < 1`, and
  `u(0) = 1`.
- `hasDerivAt_linPhase`, `hasDerivAt_expFreq`, `hasDerivAt_expFreq_neg`,
  **`hasDerivAt_primeLocalRatio`** — equation `(2)`: `u'(0) = -i (2 r L/(1 - r))`.
- `primeRadius`, `primeRatioCharge`, `primeRatio`, `primeRatio_zero`, **`hasDerivAt_primeRatio`** —
  the arithmetic instance `r_p = p^(-1/2)`, `L_p = log p`, giving `b_p = 2 log p/(sqrt p - 1)`.  Both
  are extended by the trivial value at `p <= 1`, so the family is defined and equal to one at *every*
  index; that is what lets the generic theorems apply with no side conditions.
- **`primeRatioCharge_pos`**, **`two_div_le_primeRatioCharge`** — positivity and equation `(12)`,
  `b_p >= 2/p`, from `log x >= 1 - 1/x` and `p - 1 = (sqrt p - 1)(sqrt p + 1)`.
- **`tendsto_primeCovarianceAnomaly_div_sq`** — equations `(9)`–`(10)` at the finite places: the
  quadratic jet of the prime-only anomaly is `-((sum b)^2 - sum b^2)/2`, strictly negative once two
  places are present.
- **`primeRatioCharge_mul`**, **`primeQuadraticCharge_eq_sum_offDiag`** — equation `(11)`: the pairwise
  contribution is `4 log p log q/((sqrt p - 1)(sqrt q - 1))`, and the total curvature is the
  off-diagonal sum (which is twice the `p < q` sum, whence the card's factor `8`).
- `summable_inv_sq`, **`tendsto_primeOffDiagCharge_atTop`** — equations `(13)`–`(14)`: the charge
  diverges along the exhaustion of the primes.  The arithmetic input is Euler's divergence, reused from
  `CCMCoherentSquareExclusion.lean` (`tendsto_primeReciprocalSum_atTop`), against the convergence of
  `sum 1/p^2`.

`formal/GaloisForLFunctions/RHTower/DigammaQuarter.lean` — the archimedean constant:

- `quarter_ne_intCast`, `half_ne_negNatCast`, `digamma_quarter_add_three_quarter`,
  `digamma_quarter_sub_three_quarter`, **`digamma_quarter`** — Gauss's value
  `psi(1/4) = -gamma - pi/2 - 3 log 2`.  The two functional equations were already in the corpus:
  `HTGeometry.digamma_duplication` at `s = 1/4` gives `psi(1/4) + psi(3/4) = 2 psi(1/2) - 2 log 2`, and
  `RHTower.digamma_reflection` at `z = 1/4` gives `psi(1/4) - psi(3/4) = -pi` because
  `cos(pi/4) = sin(pi/4)`.  Adding them eliminates `psi(3/4)`; mathlib's `Complex.digamma_one_half`
  supplies the rest.
- `archRatioCharge`, `ofReal_archRatioCharge`, **`archRatioCharge_pos`** — equation `(4)`'s
  positivity.  Every term of the closed value is positive, so **no monotonicity of `psi` is needed**;
  `Real.one_half_lt_eulerMascheroniConstant` finishes it.

`formal/GaloisForLFunctions/RHTower/CCM/CCMLocalRatioArchimedean.lean` — the archimedean place:

- `gammaArch`, **`gammaArch_eq_cpow`** — `gamma_infinity(s) = pi^(-s/2) Gamma(s/2)`, defined through
  `exp` so the differentiation is elementary, with the bridge to the `cpow` form.
- `hasDerivAt_gammaHalf`, `hasDerivAt_expArch`, **`hasDerivAt_gammaArch_half`** — the log-derivative at
  the seam is `(psi(1/4) - log pi)/2 = -b_infinity/2`.  The factor `1/2` is the chain rule from
  `Gamma(s/2)`; the two halves of `b_infinity` come from the two factors of `gamma_infinity`.
- `hasDerivAt_linePlusC`, `hasDerivAt_lineMinusC`, `hasDerivAt_archPlus`, `hasDerivAt_archMinus`,
  `archRatio_zero`, **`hasDerivAt_archRatio`** — equation `(4)`.  Note the route: differentiate
  `gammaArch` **inside `ℂ`** and only then compose with `t ↦ (t : ℂ)` via `HasDerivAt.comp_ofReal`.
  Going straight from `ℝ` to `ℂ` with `HasDerivAt.scomp` produces a `HasDerivAt` whose `ℂ`-module
  instance path does not match the goal's, and `simpa` cannot cross it.

`formal/GaloisForLFunctions/RHTower/CCM/CCMLocalRatioCompleted.lean` — the completed product and the
kernel:

- `placeRatio`, `placeCharge`, `placeRatio_zero`, **`hasDerivAt_placeRatio`**, `placeCharge_pos` — the
  places indexed by `Option ℕ`, with `none` archimedean.  Both kinds of multiplier have value one and
  purely imaginary first jet, so the generic theorems apply to the completed family with no side
  conditions.
- **`tendsto_covarianceAnomaly_div_sq_of_imaginary`**,
  **`tendsto_completedCovarianceAnomaly_div_sq`** — equations `(6)`–`(9)` for `V = {infinity} ∪ F`.
- **`completedCharge_pos`** — the jet is *strictly* negative as soon as two places are present: the
  off-diagonal charge is then a nonempty sum of positive terms.
- `norm_div_conj`, `conj_primeLocalRatio_num`, **`norm_primeLocalRatio`**, `gammaArch_conj`,
  `gammaArch_line_ne_zero`, **`norm_archRatio`**, **`norm_placeRatio`** — `|u_v| = 1` on the critical
  line, at every place.  The reason is structural and the same in both cases: numerator and denominator
  are complex conjugates of each other — at a finite place because `r_p` is real, at the archimedean
  place because `Gamma` commutes with conjugation and `log pi` is real.
- `placePairKernel`, **`placePairKernel_diag`**, **`quantizedDifferentialAnomaly`**,
  **`quantizedDifferentialAnomaly_diag`**, **`norm_kernelAnomaly_le`** — section 4.  Equation `(18)` is
  the *same* algebraic identity as `(7)`, applied to `a_v = r_v(x,y) - 1`; unimodularity gives
  `r_v(x,x) = 1`, hence the diagonal vanishing; and `norm_kernelAnomaly_le` is the quantitative form —
  if every one-place increment is at most `D <= 1` then the anomaly is at most `card · D²`, because
  every surviving product has at least two factors.  With `D = O(|y - x|)` that is the card's "at least
  quadratic diagonal vanishing", and it is exactly what makes the product against a first-order
  singular kernel vanish on the diagonal.

Section 5 is a requirements list, not a theorem: `(19)` records what a successful construction must
carry, and the four items after it (Gauss-paired Hardy representative, principal-relative Schur block,
cofinal renormalization, index-faithful transport) are open research, as the card says.

## Gates

- [x] factorization-independent anomaly `(6)`–`(7)` proved
- [x] exact central curvature `(9)`–`(11)` proved
- [x] harmonic lower bound `(13)` and cofinal divergence `(14)` proved
- [x] quadratic diagonal vanishing of the kernel `(18)` proved
- [x] Lean: place-independent anomaly, factorization independence `(7)`
- [x] Lean: vanishing constant and linear jets `(8)`
- [x] Lean: quadratic jet `(9)`, from first derivatives only
- [x] Lean: finite-place local ratio and its jet `(1)`–`(2)`
- [x] Lean: archimedean local ratio and its jet `(3)`–`(4)`, with Gauss's `psi(1/4)`
- [x] Lean: prime curvature `(10)`–`(11)`
- [x] Lean: harmonic bound `(12)` and cofinal divergence `(13)`–`(14)`
- [x] Lean: unimodularity of every local ratio on the critical line
- [x] Lean: kernel anomaly `(18)`, diagonal vanishing, and its second-order bound
- [ ] Gauss-descent theorem: analytically compact Gauss-paired representatives descend to `(18)`
      modulo trace-zero conjugation coboundaries
- [ ] Sonin relative grade as a positive Schur lift with a bound uniform in the prime cutoff

## 8. Original Lean decision (superseded)



The exact finite-product and second-jet identities are formalizable, but the present Lean tree has
no critical-line local-ratio multiplier or Hardy singular-kernel realization. Formalizing only the
commutative product identity would be a routine wrapper and would not certify the analytic
Gauss-descent or uniform Schur theorem. No Lean file is added for this bridge.
