# The Hedenmalm theta source has an intrinsic compact reciprocal-divisor operator

- **ID:** `hedenmalm-theta-source-compressed-inverse-determinant`
- **Stage:** 2-fully-proven / weighted kernel layer formalized; determinant layer open
- **Type:** THEOREM / SOURCE-DERIVED HILBERT--SCHMIDT EVANS OPERATOR
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Lean core:** `GaloisForLFunctions.HTGeometry.SourceGrushinInverse`
- **Parents:**
  `hedenmalm-supersymmetric-fredholm-range-divisor.md`;
  `../../3-formalized/not_new_scientific_knowledge/hedenmalm-weil-source-to-operator-capstone.md`;
  Hedenmalm, arXiv:2606.17494.

## Exact statement

Let `k` be Hedenmalm's normalized positive even logarithmic theta source. Write

\[
 M=\int_{\mathbb R}k(x)\,dx=\Xi_C(0),\qquad
 \Xi_C(z)=\int_{\mathbb R}k(x)e^{izx}\,dx,
 \tag{1}
\]

and put

\[
 \mathcal H_k=L^2(\mathbb R,k^{-1}dx),\qquad
 A=\overline{-i\partial_x\vert_{C_c^\infty}},\qquad
 K=k^\perp,\qquad P=P_K.
 \tag{2}
\]

The preceding Fredholm theorem proves that `A` is injective, has closed range `K`, and is bounded
below. Consequently `A^{-1}:K\to\mathcal H_k` is bounded. Define, without mentioning a zero of
`XiC`,

\[
 B=A^{-1}P:\mathcal H_k\longrightarrow\mathcal H_k.
 \tag{3}
\]

Then:

1. `B` is Hilbert--Schmidt. If
   \[
   F(x)=\int_{-\infty}^xk(y)\,dy,\qquad p(x)=F(x)/M,
   \]
   its integral kernel relative to `d\mu(x)=k(x)^{-1}dx` is
   \[
   B(x,y)=i k(y)\bigl(\mathbf1_{y\le x}-p(x)\bigr),
   \tag{4}
   \]
   and
   \[
   \lVert B\rVert_{\mathrm{HS}}^2
   =M\int_{\mathbb R}\frac{p(x)(1-p(x))}{k(x)}\,dx<\infty.
   \tag{5}
   \]
2. For every `z\in\mathbb C`,
   \[
   \Xi_C(z)=0
   \quad\Longleftrightarrow\quad
   I+zB\text{ is not invertible}
   \quad\Longleftrightarrow\quad
   -z^{-1}\in\sigma_p(B).
   \tag{6}
   \]
   The zero order of `XiC` at `z` equals the algebraic multiplicity of the eigenvalue `-z^{-1}`.
3. If `R f(x)=f(-x)`, then
   \[
   RBR=-B.
   \tag{7}
   \]
   Hence the nonzero spectrum, including algebraic multiplicity, is paired under
   `\lambda\mapsto-\lambda`.
4. The second regularized Fredholm determinant is the completed Xi function itself:
   \[
   \boxed{\displaystyle
   \det{}_2(I+zB)=\frac{\Xi_C(z)}{\Xi_C(0)}}.
   \tag{8}
   \]
5. The first nontrivial trace invariant is the source variance:
   \[
   \operatorname{tr}(B^2)
   =2\int_{x<y}p(x)(1-p(y))\,dx\,dy
   =\frac1M\int_{\mathbb R}x^2k(x)\,dx.
   \tag{9}
   \]
6. Since critical-line zeros correspond to real centered parameters,
   \[
   \mathrm{RH}
   \quad\Longleftrightarrow\quad
   \sigma(B)\setminus\{0\}\subset\mathbb R.
   \tag{10}
   \]

Unlike the previously formalized reciprocal diagonal operator, `(3)` is source-derived: its Hilbert
space, differential, projection, kernel, and determinant are constructed from `k` before the Xi
divisor is enumerated. Statement `(10)` is a terminal equivalence, not a proof of the required
spectral reality.

## Proof

### 1. Explicit inverse and Hilbert--Schmidt kernel

For `f\in\mathcal H_k`, orthogonal projection onto `K=k^\perp` is

\[
 Pf=f-\frac{\int_{\mathbb R}f(y)\,dy}{M}k.
 \tag{11}
\]

The integral is continuous on `\mathcal H_k` because it is the inner product with `k`.  Since
`Pf\perp k`, the unique two-ended primitive in `\operatorname{dom}A` is

\[
 (Bf)(x)=i\int_{-\infty}^x(Pf)(y)\,dy.
 \tag{12}
\]

Writing each Lebesgue integral in `(12)` against `d\mu(y)=k(y)^{-1}dy` gives `(4)`.  Therefore

\[
\begin{aligned}
 \lVert B\rVert_{\mathrm{HS}}^2
 &=\int_{\mathbb R}\frac{dx}{k(x)}
   \int_{\mathbb R}k(y)
    \bigl(\mathbf1_{y\le x}-p(x)\bigr)^2dy\\
 &=M\int_{\mathbb R}\frac{p(x)(1-p(x))}{k(x)}dx.
\end{aligned}
\tag{13}
\]

At `+\infty`, Hedenmalm's theta asymptotic gives

\[
 1-p(x)\asymp \frac{k(x)}{e^{2x}},
\]

and reflection gives `p(x)\asymp k(x)e^{2x}` at `-\infty`.  Thus the integrand in `(13)` is
integrable at both ends.  This proves `(5)` and compactness.

### 2. Grushin reduction and the exact divisor

Give `\operatorname{dom}A` its graph norm and define the source-augmented pencil

\[
 \mathcal G_z:\operatorname{dom}A\oplus\mathbb C\longrightarrow\mathcal H_k,
 \qquad
 \mathcal G_z(u,c)=(A+z)u+ck.
 \tag{14}
\]

The decomposition `\mathcal H_k=K\oplus\mathbb Ck` shows that `\mathcal G_0` is a bounded
bijection with

\[
 \mathcal G_0^{-1}(v+ck)=(A^{-1}v,c).
\]

Consequently

\[
 \mathcal G_z\mathcal G_0^{-1}=I+zB.
 \tag{15}
\]

The continuous analytic functional

\[
 \ell_z(f)=\int_{\mathbb R}f(x)e^{izx}\,dx
 \tag{16}
\]

annihilates `\operatorname{ran}(A+z)` by integration by parts.  The previous Fredholm theorem says
that this range has codimension one, so it equals `\ker\ell_z`.  Moreover

\[
 \ell_z(k)=\Xi_C(z).
 \tag{17}
\]

It follows that `\mathcal G_z`, hence `I+zB`, is invertible exactly when `\Xi_C(z)\ne0`.  Since
`B` is compact, noninvertibility away from `z=0` is equivalent to the eigenvalue statement in `(6)`.

For multiplicity, fix a zero `z_0` and choose `h\in\mathcal H_k` with
`\ell_{z_0}(h)\ne0`.  This remains nonzero near `z_0`.  Split the codomain analytically as

\[
 \mathcal H_k=\ker\ell_z\oplus\mathbb Ch.
\]

Because `A+z:\operatorname{dom}A\to\ker\ell_z` is a bounded bijection, analytic row and column
operations reduce `(14)` locally to

\[
 \begin{pmatrix}I&0\\0&\Xi_C(z)\end{pmatrix}
\tag{18}
\]

up to multiplication of the scalar corner by a nonvanishing analytic unit.  The analytic Fredholm
multiplicity of `I+zB` at `z_0` is therefore exactly
`\operatorname{ord}_{z_0}\Xi_C`.  This proves the multiplicity clause.

### 3. Reflection and determinant

Evenness of `k` makes `P` commute with reflection and gives `RAR=-A`; hence `(7)`.  The
Hilbert--Carleman product formula for a Hilbert--Schmidt operator, together with the exact
multiplicity statement and the `\pm` pairing, gives

\[
 \det{}_2(I+zB)
 =\prod_{\{\alpha,-\alpha\}}
   \left(1-\frac{z^2}{\alpha^2}\right)^{m_\alpha}.
 \tag{19}
\]

The paired genus-one Hadamard product for the even order-one function `XiC` is

\[
 \frac{\Xi_C(z)}{\Xi_C(0)}
 =\prod_{\{\alpha,-\alpha\}}
   \left(1-\frac{z^2}{\alpha^2}\right)^{m_\alpha}.
 \tag{20}
\]

The products in `(19)` and `(20)` are locally normally convergent because
`\sum_\alpha |\alpha|^{-2}<\infty`.  This proves `(8)`.

### 4. Trace calibration

Since `B` is Hilbert--Schmidt, `B^2` is trace class.  Substitution of `(4)` into the diagonal kernel
of `B^2` gives

\[
 \operatorname{tr}(B^2)
 =2\int_{x<y}p(x)(1-p(y))\,dx\,dy.
 \tag{21}
\]

If `X,Y` are independent with density `k/M`, Tonelli's theorem rewrites the right side as
`\frac12\mathbb E[(X-Y)^2]=\operatorname{Var}(X)`.  Evenness makes the mean zero, proving `(9)`.
It also matches the quadratic Taylor coefficient on both sides of `(8)`.

## What this changes

The existing terminal operator

\[
 (R_\Xi v)(q)=\alpha_q^{-1}v(q)
\]

is Hilbert--Schmidt but target-fed: it starts with the Xi divisor.  Operator `(3)` has the same
nonzero spectral divisor, including multiplicity, and the same normalized regularized determinant,
but starts with only the ordinary theta density and its derivative range.  Thus the missing
source-to-divisor operation in the Hedenmalm lane is no longer hypothetical.  It is the compact
Grushin inverse `(3)`.

The exact remaining RH theorem is narrower and more hostile:

> Prove from the arithmetic theta/Poisson structure, not from the Xi divisor, that the nonzero
> spectrum of `B` is real; equivalently, construct a source-defined conservative positive metric
> `G` with `B^*G=GB` which does not annihilate any root space.

Generic positive even rapidly decreasing sources do not have this property: their Fourier transforms
may have nonreal zeros.  Positivity, evenness, confinement of `A^*A`, compactness, and the determinant
identity therefore cannot prove `(10)` by themselves.

This theorem uses the theta/Poisson/Gamma completion but does not retain literal prime-incidence
labels.  Welding `(3)` to the ordinary-integer Euler--Poisson--Gamma source without replacing it by
its completed Fourier transform remains a separate source-faithfulness obligation.

The child theorem
`hedenmalm-essential-inverse-flow-prime-tomography.md` now proves an aggregate version of that
weld.  In the reciprocal coordinate `mu=-i/w`, the fixed-width window is the essential inverse
flow

\[
 2\mu\left(\sin(a/\mu)-\sin((a-L)/\mu)\right),
\]

and its absolutely convergent punctured Riesz trace is exactly the literal finite
von-Mangoldt--Gamma sequence on the logarithmic integer orbit.  This retains the complete divisor
and multiplicity globally but does not yet attach prime incidence fibrewise to each Riesz mode or
prove spectral reality.

The second child theorem
`hedenmalm-prime-translation-rank-one-anomaly.md` supplies that fibrewise incidence on the
preboundary exponential source core.  Normalized shifts
`T_n=n^(-1/2)S_(-log n)` have a rank-one commutator with the source inverse, every divisor
conormal transforms by the literal character `n^(-s)`, and its jets retain the logarithmic-prime
Jordan package through full multiplicity.

The third child theorem
`hedenmalm-two-prime-theta-interval-normal-frame.md` corrects the raw-anomaly interpretation and
closes conormal nonannihilation.  The commutator range is divisible by `XiC`, but its centered
source-normal quotient is the pair of sinc multipliers attached to the literal intervals
`log 2` and `log 3`; they have no common zero and generate the full Xi normal module.  In compact
reciprocal coordinates they become an essential-singular two-component symbol.  What remains
absent is its closed strict descent to a positive prime-cylinder boundary; ordinary bounded
multiplier descent is explicitly impossible.

## Literature status

The Grushin/Evans reduction, Hilbert--Carleman determinant, and Livsic theory of compact
non-self-adjoint operators are classical parent technology.  Hedenmalm's 2026 preprint gives the
theta differential pencil and asks for a self-adjoint realization, but does not define `(3)`, prove
its Hilbert--Schmidt kernel, or identify its determinant with `XiC`.  Initial searches found related
triangular integration-operator models with rank-one imaginary part, but no source-specific theorem
matching `(3)`--`(8)`.  Novelty remains unverified pending a focused operator-theory audit.


## Lean status

`[PARTIAL]`  Two layers exist.

**Bounded algebraic core.** `GaloisForLFunctions.HTGeometry.SourceGrushinInverse` gives the
Grushin factorization `G_z G_0^(-1) = I + z B`, the reciprocal eigenvalue law
`ker(I+zB) = ker(B + z^(-1))` away from the origin, and compactness transfer.

**Concrete weighted layer.** `formal/GaloisForLFunctions/RHTower/HedenmalmHilbertSchmidtNorm.lean`
(namespace `RHTower.HedenmalmHilbertSchmidt`), built on the quantile normal form of the sibling
card.  All declarations are `#print axioms`-clean.

| # | statement | Lean declaration |
|---|---|---|
| `(4)` | the pinned kernel slice `1_(y<=x) - p(x)`, bounded by one | `pinnedKernelSlice`, `abs_pinnedKernelSlice_le` |
| `(5)` | inner slice energy `t(1-t)` | `integral_pinnedKernelSlice_sq` |
| `(5)` | Hilbert--Schmidt energy `= M integral p(1-p)/k` | `integral_quantileSpeed_sq_slice`, `tailEnergyDensity` |
| `(6)` | a divisor point is an eigenvalue: `B f_z = -z^(-1) f_z` | `sourceInverse_sourceModeF_eq_smul` |
| `(6)` | an eigenvector forces a zero, for any nonzero source coefficient | `xiC_eq_zero_of_solution_const` |
| `(7)` | reflection law `R B R = -B` for an even source | `sourceReflection`, `sourceFunctional_sourceReflection`, `sourceInverse_sourceReflection` |
| `(4)` | the kernel row as an `L^2` vector, energy `q(t)^2 t(1-t)` | `pinnedKernelFun`, `pinnedKernelVec`, `norm_sq_pinnedKernelVec` |
| `(1)` | the kernel field `t |-> K(t,.)` is `L^2`-continuous | `pinnedSliceVec`, `norm_pinnedSliceVec_sub_le`, `continuous_pinnedSliceVec` |
| `(1)` | the assembled field of functionals | `pinnedKernelField`, `pinnedKernelField_apply`, `pinnedKernelL2` |
| `(1)` | **`B` is Hilbert--Schmidt**, and compact | `isHilbertSchmidt_pinnedKernelOperator`, `isCompactOperator_pinnedKernelOperator` |

**Unconditional layer.**  `formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceUnconditional.lean`
and `.../HedenmalmThetaKernelEnergy.lean` (namespace `RHTower.HedenmalmThetaSource`) instantiate the
whole layer at the actual arithmetic source, so the statements below carry **no hypothesis at all**.

| # | statement | Lean declaration |
|---|---|---|
| `(2)` | the theta-cusp state is a positive density source | `thetaCuspFullSource_pos`, `thetaSource` |
| `(1)` | `Xi_C` is its completed transform on `|Im z| < 1` | `xiC_thetaSource`, `hasShiftedTail_thetaSource` |
| `(5)` | **the theta-tail energy converges**: `M integral p(1-p)/k < infinity` | `integrable_tailEnergyDensity_thetaSource`, `hasFiniteKernelEnergy_thetaSource` |
| `(5)` | the doubly exponential squeeze behind it | `thetaEnvelope`, `thetaCuspFullSource_le_envelope`, `thetaCuspFullSource_ge_envelope`, `thetaEnvelope_le_shift`, `integral_Ioi_thetaCuspFullSource_le` |
| `(1)` | **`B` is Hilbert--Schmidt for the Riemann source** | `isHilbertSchmidt_thetaKernelOperator` |
| `(1)` | `B` is compact for the Riemann source | `isCompactOperator_thetaKernelOperator` |
| `(7)` | `R B R = -B` for the Riemann source | `thetaSource_even`, `sourceInverse_sourceReflection_theta` |
| `(6)` | **a source solution with any nonzero coefficient forces `Xi_C(alpha) = 0`**, unconditionally | `XiC_eq_zero_of_solution_const` |
| `(6)` | the source mode at a divisor point is integrable and vanishes at both ends | `integrable_sourceModeU`, `tendsto_sourceModeU_atBot`, `tendsto_sourceModeU_atTop` |
| `(9)` | the first source moment vanishes (evenness) | `integrable_mul_thetaSource`, `integral_mul_thetaSource_eq_zero`, `integral_quantileFun` |
| `(9)` | **the source variance in quantile coordinates**, `integral over (0,1) of Q^2 = M^(-1) integral of x^2 k` | `integral_sq_quantileFun` |
| `(9)` | **`tr(B^2)` is well posed**: the diagonal series converges over every Hilbert basis and its sum is basis independent | `thetaKernelOperator`, `thetaTraceSq`, `summable_thetaTraceSq_diag`, `thetaTraceSq_eq_tsum_basis` |
| `(9)` | `tr(B^2) = <B^dagger, B>_HS`, bounded by the Hilbert--Schmidt energy | `thetaTraceSq_eq_hsInner`, `norm_thetaTraceSq_le` |
| `(1)`,`(9)` | **`B^2` is trace class**, and so is the positive energy `B^dagger B`, whose trace is the Hilbert--Schmidt energy | `isTraceClass_thetaKernelOperator_sq`, `isTraceClass_adjoint_comp_thetaKernelOperator`, `re_opTrace_adjoint_comp_thetaKernelOperator` |

Corpus assets to use for the remaining items, rather than rebuilding them:
`ContinuousLinearMap.IsHilbertSchmidt` (`HTGeometry/HilbertSchmidtOperator.lean`),
`IsHilbertSchmidt.isCompactOperator` (`HTGeometry/HilbertSchmidtCompact.lean`), and
`RHTower.isHilbertSchmidt_kernelOperator` (`RHTower/SoninTimeBandHilbertSchmidt.lean`), which
turns an `L2` field of continuous functionals into an actual Hilbert--Schmidt operator.

Both directions of the point-spectrum half of `(6)` are therefore available in explicit form.

**Corpus audit correction.**  An earlier version of this section stated that no general `det_2`
exists in the corpus or in mathlib.  That is false.  `HTGeometry/FredholmDeterminant.lean` builds
the regularized Hilbert--Carleman determinant `det_2(1 - zK)` for an arbitrary Hilbert--Schmidt
kernel, together with the Plemelj identity `logDeriv det_2(1 - zK) = -resolventTrace K z`
(`fredholmExp`, `fredholmExp_summable`, `fredholmDet`, `logDeriv_fredholmDet`,
`fredholmDet_ne_zero`, `hasDerivAt_fredholmDet`, `fredholmDet_differentiableOn`,
`fredholmDet_weld`), and `HTGeometry/FredholmDeterminantInfinite.lean` supplies the countable
diagonal case.  `HTGeometry/HilbertSchmidtMatrix.lean` supplies the operator/kernel bridge
(`toOperator`, `matrixOf`, `isHS_matrixOf`, `matrixOf_toOperator`, `toOperator_matrixOf`), and
`HTGeometry/HilbertSchmidtTrace.lean` the trace weld `HilbertSchmidt.opTrace_toOperator_comp`.
None of this is to be rebuilt; `(8)` is a *transfer and identification* problem, not a missing-theory
problem.

Still missing: the **multiplicity clause** of
`(6)` (the Grushin reduction to `diag(I, Xi_C)`; this clause is what
`hedenmalm-prime-translation-rank-one-anomaly.md` cites for its Jordan length), the identification
`(8)` of the regularized determinant with `Xi_C(z)/Xi_C(0)`, and the
trace calibration `(9)`.  Both ends of `(9)` are now formalized --- the source variance
`M^(-1) integral of x^2 k` in quantile form, and the well-posedness of `tr(B^2)` on the operator
side --- so what is left of `(9)` is the *equality* between them, i.e. the kernel evaluation of the
diagonal sum.  The corpus trace layer that makes this reachable is
`HTGeometry/HilbertSchmidtTrace.lean` (`opTrace`, `opTrace_comp_eq_hsInner`,
`opTrace_comp_eq_tsum_basis`, `opTrace_comp_comm`, `norm_opTrace_comp_le`, and the kernel weld
`HilbertSchmidt.opTrace_toOperator_comp`) --- it must not be rebuilt.

## Gates

- [x] source-only construction; no Xi-zero index in the definition
- [x] boundedness and explicit inverse kernel
- [x] Hilbert--Schmidt estimate from theta tails
- [x] exact point-spectrum/zero equivalence
- [x] analytic multiplicity preserved
- [x] exact normalized `det_2 = XiC`
- [x] parity and trace calibration
- [x] target-fed collision audit
- [x] no RH or positivity overclaim
- [x] bounded Grushin factorization, reciprocal eigenvalue law, and compactness transfer in Lean
- [ ] focused Livsic/triangular-model novelty audit
- [x] Lean pinned kernel `(4)`, Hilbert--Schmidt energy `(5)`, and reflection law `(7)`
- [ ] formalize the assembled Hilbert--Schmidt operator, the multiplicity clause of `(6)`,
      and the regularized determinant `(8)` in Lean
- [ ] prove source-specific spectral reality
