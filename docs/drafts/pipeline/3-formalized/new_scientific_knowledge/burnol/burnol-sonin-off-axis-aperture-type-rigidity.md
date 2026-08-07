# Burnol--Sonin off-axis aperture-type rigidity

- **ID:** `burnol-sonin-off-axis-aperture-type-rigidity`
- **Stage:** 3-formalized
- **Formalized companion:** `burnol-sonin-off-axis-aperture-type-rigidity-formalized.md`
- **Type:** THEOREM / HOSTILE ROUTE AUDIT
- **Scientific status:** `[CORPUS-NEW SYNTHESIS] [PRELIMINARY EXTERNAL NONCOLLISION] [NOT RH]`
- **Parents:**
  - `../gamma/gamma-copoisson-sonin-independent-quadrant-boundary-transgression.md`;
  - `burnol-copoisson-quotient-bilateral-order-rh-law.md`;
  - Burnol's continuous completed-Mellin evaluation theorem for the extended Sonine spaces.
- **Statement:** Away from the critical line, the completed-Mellin evaluation vector in
  Burnol's extended Sonine space has exactly the aperture exponent
  \(\lvert\operatorname{Re}w-\tfrac12\rvert\) on every co-Poisson annihilator fibre.  Hence the
  independent-quadrant section has the exact exponential face growth already predicted by its
  prime-transfer character.  The proposed subexponential estimate `(GS24)` is not generic Sonine
  regularity and cannot be obtained by sharpening an ambient evaluation estimate.

## Set-up

Let \(L_a\subset L^2(0,\infty;dt)\) be Burnol's extended cosine-Sonine space: \(f\) and its
unitary cosine transform \({\cal F}_+f\) are constant on \((0,a)\).  For \(w\notin\{0,1\}\), let
\[
 {\cal M}f(w)
 =\gamma(w)\int_0^\infty f(t)t^{-w}\,dt,
 \qquad
 \gamma(w)=\pi^{-w/2}\Gamma(w/2),
 \tag{1}
\]
denote the completed right Mellin evaluation, meromorphically interpreted where necessary.
Write \(k_{w,a}\in L_a\) for its Riesz vector.

Fix \(a_0>0\), \(r>1\), and
\[
 a_N=a_0r^{-N},\qquad
 \lambda_r(w)=r^{w-1/2}.
 \tag{2}
\]

## Ambient off-axis upper bound

`[PAPER-PROVED] [EXTENDED_SONIN_EVALUATION_APERTURE_UPPER_BOUND]`

If \(0<\sigma=\operatorname{Re}w<1\) and \(\sigma\ne\tfrac12\), then
\[
 \boxed{\quad
 \|k_{w,a}\|
 \le C(w)\,a^{-|\sigma-1/2|}
 \quad}
 \tag{3}
\]
for every \(a>0\), where one may take
\[
\begin{aligned}
C_+(w)
 &=|\gamma(w)|
   \left({1\over|1-w|}+{1\over\sqrt{2\sigma-1}}\right),
 &&\sigma>\tfrac12,\\
C_-(w)
 &=|\gamma(1-w)|
   \left({1\over|w|}+{1\over\sqrt{1-2\sigma}}\right),
 &&\sigma<\tfrac12.
\end{aligned}
\tag{4}
\]

### Proof

Suppose first that \(\sigma>\tfrac12\).  For \(f\in L_a\), write \(f(t)=c\) on \((0,a)\).
Then
\[
 |c|\sqrt a\le\|f\|_2
 \tag{5}
\]
and
\[
 \left|\int_0^a c\,t^{-w}\,dt\right|
 ={ |c|a^{1-\sigma}\over|1-w|}
 \le {a^{1/2-\sigma}\over|1-w|}\|f\|_2.
 \tag{6}
\]
Cauchy--Schwarz on the tail gives
\[
\begin{aligned}
\left|\int_a^\infty f(t)t^{-w}\,dt\right|
&\le\|f\|_2
 \left(\int_a^\infty t^{-2\sigma}\,dt\right)^{1/2}\\
&={a^{1/2-\sigma}\over\sqrt{2\sigma-1}}\|f\|_2.
\end{aligned}
\tag{7}
\]
Multiplication by \(|\gamma(w)|\) proves `(3)` with \(C_+(w)\).

If \(\sigma<\tfrac12\), Burnol's completed Mellin--cosine functional equation gives
\[
 {\cal M}f(w)={\cal M}({\cal F}_+f)(1-w).
 \tag{8}
\]
The cosine transform is unitary, belongs again to \(L_a\), and
\(\operatorname{Re}(1-w)>\tfrac12\).  Apply the already-proved estimate at \(1-w\).  Its aperture
factor is
\[
 a^{1/2-\operatorname{Re}(1-w)}
 =a^{\sigma-1/2},
 \tag{9}
\]
which proves `(3)` with \(C_-(w)\).  `QED`

No estimate is asserted at \(\sigma=\tfrac12\): the tail weight \(t^{-1/2}\) is exactly outside
\(L^2(a,\infty)\), and continuity there uses the full Sonine condition rather than this elementary
split.

## Sharp aperture type on an annihilator fibre

Let \(\rho\) be a nontrivial zeta zero.  Burnol's orthogonal-complement theorem identifies its
co-Poisson quotient vector with the full evaluator:
\[
 y_{\rho,N}=k_{\rho,a_N}\ne0.
 \tag{10}
\]
The two projected dilation maps in the parent boundary-transgression theorem are contractions and
obey the exact characters \(\overline{\lambda_r(\rho)}\) and
\(\overline{\lambda_r(\rho)^{-1}}\).  Consequently,
\[
 \|k_{\rho,a_N}\|
 \ge
 \max\{|\lambda_r(\rho)|^N,|\lambda_r(\rho)|^{-N}\}
 \|k_{\rho,a_0}\|.
 \tag{11}
\]

`[PAPER-PROVED] [ANNIHILATOR_EVALUATION_EXACT_APERTURE_TYPE]`

If \(\operatorname{Re}\rho\ne\tfrac12\), there are constants
\(0<c_\rho\le C_\rho<\infty\), independent of \(N\), such that
\[
 \boxed{\quad
 c_\rho r^{N|\operatorname{Re}\rho-1/2|}
 \le
 \|k_{\rho,a_N}\|
 \le
 C_\rho r^{N|\operatorname{Re}\rho-1/2|}.
 \quad}
 \tag{12}
\]
In particular,
\[
 \boxed{\quad
 \lim_{N\to\infty}{1\over N\log r}
 \log\|k_{\rho,a_N}\|
 =
 |\operatorname{Re}\rho-\tfrac12|.
 \quad}
 \tag{13}
\]

### Proof

The lower bound is `(11)`.  The upper bound follows from `(3)` and
\[
 a_N^{-|\operatorname{Re}\rho-1/2|}
 =
 a_0^{-|\operatorname{Re}\rho-1/2|}
 r^{N|\operatorname{Re}\rho-1/2|}.
 \tag{14}
\]
Taking logarithms and dividing by \(N\log r\) proves `(13)`.  `QED`

Thus horizontal zero displacement is literally the anomalous aperture dimension of the
Gamma-completed Sonine evaluator.  The local Xi residue, prime-shell Lyapunov exponent, and Sonine
norm exponent are the same charge, up to sign and multiplicity.

## Exact independent-face growth

For the parent quadrant section
\[
 X_{p,q}(\rho)
 =\overline{\lambda_r(\rho)}^{\,q-p}
   k_{\rho,a_{p+q}},
 \tag{15}
\]
equation `(12)` sharpens the earlier lower bound to a two-sided law.

If \(\operatorname{Re}\rho>\tfrac12\), then
\[
 c_\rho|\lambda_r(\rho)|^{2q}
 \le\|X_{p,q}(\rho)\|
 \le C_\rho|\lambda_r(\rho)|^{2q}.
 \tag{16}
\]
If \(\operatorname{Re}\rho<\tfrac12\), then
\[
 c_\rho|\lambda_r(\rho)|^{-2p}
 \le\|X_{p,q}(\rho)\|
 \le C_\rho|\lambda_r(\rho)|^{-2p}.
 \tag{17}
\]
These follow immediately by multiplying `(12)` by
\(|\lambda_r(\rho)|^{q-p}\) and using \(N=p+q\).

## Hostile consequence for `(GS24)`

Every off-line annihilator character violates `(GS24)` with its exact source character rate:

- a right-half zero escapes only through the \(q\)-face, with exponent
  \(2(\operatorname{Re}\rho-\tfrac12)\log r\);
- a left-half zero escapes only through the \(p\)-face, with exponent
  \(2(\tfrac12-\operatorname{Re}\rho)\log r\).

Therefore `(GS24)` is not an ambient Sonine estimate waiting for a finer Cauchy--Schwarz
argument.  The ambient estimate is already sharp on every off-axis annihilator fibre.  Proving
`(GS24)` from the arithmetic source would have to prove a new protection or anomaly-cancellation
law which eliminates the off-axis fibres themselves.

Moreover `(GS24)` may be stronger than RH: the theorem says nothing about subexponential growth
of critical-line evaluation norms.  The logically minimal RH reader is the vanishing of the
off-axis aperture exponent `(13)`, not a raw subexponential bound on every critical evaluator.

This closes the strategy

```text
improve ordinary Sonine evaluation estimates
  -> prove subexponential quadrant growth
  -> RH.
```

The surviving problem is not an estimate internal to one evaluator fibre.  It is construction of
a source comparison which forces Xi conormal fibres to be protected, trace-like, or otherwise
zero-anomaly before their individual characters are read.

## Literature boundary

Burnol proves:

1. \(L_a\) consists of functions, and cosine transforms, constant on \((0,a)\);
2. completed Mellin evaluations are continuous;
3. the co-Poisson orthogonal complement is the closed zeta-evaluator span.

The estimate `(3)` is an elementary consequence of those definitions.  Targeted searches of
Burnol's Sonine papers and searches for small-aperture reproducing-kernel asymptotics found no
statement of the exact annihilator-fibre sandwich `(12)`, exponent identity `(13)`, or quadrant
two-sided laws `(16)`--`(17)`.  This is preliminary noncollision, not a priority claim.

Primary references:

- J.-F. Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta
  function*, J. Théor. Nombres Bordeaux 16 (2004), 65--94,
  <https://arxiv.org/abs/math/0203120>.
- J.-F. Burnol, *On Fourier and Zeta(s)*, Forum Math. 16 (2004), 789--840,
  <https://arxiv.org/abs/math/0112254>.

## Lean decision

The ambient off-axis upper bound `(3)`--`(4)`, which is the analytic content of this card, is now
formalized unconditionally in

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninEvaluationAperture.lean
```

on the literal Hilbert space `L^2((0,infinity),dt)`.  The module defines the completed right Mellin
evaluator

```text
mellinCompletionFactor w = pi^(-w/2) Gamma(w/2),
soninMellinKernel w t     = t^(-w),
soninMellinEvaluation w f = mellinCompletionFactor w * integral_{(0,infinity)} f t * t^(-w) dt,
```

and the constant-aperture-head class `SoninHeadConstant a f`.  It proves

```text
norm_head_mul_sqrt_le                    : ||c|| sqrt A <= ||f||                            (5)
integral_Ioo_soninMellinKernel           : integral_{(0,A)} t^(-w) dt = A^(1-w)/(1-w)       (6)
integral_Ioi_norm_sq_soninMellinKernel   : integral_{(A,infinity)} t^(-2 sigma) dt
                                             = A^(1-2 sigma)/(2 sigma - 1)                  (7)
norm_soninMellinEvaluation_le_aperture   : ||M f w|| <= ||gamma(w)||
                                             (1/||1-w|| + 1/sqrt(2 sigma - 1))
                                             A^(1/2-sigma) ||f||                            (3),(4)
norm_soninMellinEvaluation_le_geometric_sample
                                         : the same bound at a_N = a_0 r^(-N), with the
                                           exact factor r^(N(sigma-1/2))                    (14)
```

for `1/2 < sigma = Re w < 1`.  All `#print axioms` reduce to
`[propext, Classical.choice, Quot.sound]`.  Note that the upper bound at `sigma > 1/2` needs only
the constant head, not the full Sonine condition; the Sonine condition enters the paper proof only
through the functional equation `(8)` used to transfer the estimate to `sigma < 1/2`.

The unitary cosine transform and the extended Sonine space are now built as well, in

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninEvenCosineAperture.lean
```

The half-line model `L^2(0,infinity)` is realized as the even carrier of `L^2(R)`, for which the
formal tree already owns the Fourier unitary and the even projection.  The module proves

```text
integral_Iio_norm_sq_eq_integral_Ioi : an even carrier splits its mass evenly,
norm_soninHalfLine                   : ||f|_(0,infinity)|| = ||f||/sqrt 2,
soninCosineUnitary                   : evenSubspace ~=L2 evenSubspace, the cosine transform F_+,
soninCosineUnitary_involutive        : F_+^2 = 1, since F^2 is the reflection,
soninCosineUnitary_symm_eq           : F_+^(-1) = F_+,
soninHeadConstantSubmodule a         : the constant-aperture-head submodule,
soninExtendedSpace a                 : L_a, both f and F_+ f with constant head a,
soninCosineUnitary_mem_soninExtendedSpace
                                     : L_a is cosine invariant,
norm_soninMellinEvaluation_le_aperture_even
                                     : the ambient bound on an even carrier,
norm_soninMellinEvaluation_cosine_le_aperture
                                     : the same bound applied to F_+ f, with the same norm.
```

The last item is the entire right-hand side of the reflected estimate: once the completed Mellin
functional equation `(8)` is available, the `sigma < 1/2` case of `(3)` is immediate from it, because
`F_+` is norm preserving and `L_a` is cosine invariant.

The functional equation `(8)` is being built in

```text
formal/GaloisForLFunctions/RHTower/ArchimedeanMellinFourier.lean
```

along the Gaussian-resolution route, which reduces `(8)` to two identities about the Gaussian
smoothing family `G f u = integral_R f(t) exp(-pi u t^2) dt`.  Both are now proved unconditionally:

```text
integral_Ioi_gaussianPower
  : 0 < Re w -> 0 < t
    -> integral_{(0,infinity)} u^(w/2-1) exp(-pi u t^2) du
         = pi^(-w/2) Gamma(w/2) t^(-w)                                (Gamma resolution)
gaussianSmoothing_fourier
  : f integrable, 0 < u -> G (Fourier f) u = u^(-1/2) G f (1/u)        (multiplication formula)
gaussianSmoothing_of_even
  : f even and integrable -> G f u = 2 * half-line smoothing
```

The first is the Gamma integral applied to the Gaussian at rate `pi t^2`; the second is mathlib's
self-adjointness of the Fourier integral tested against the self-dual Gaussian, whose transform
supplies exactly the factor `u^(-1/2)` and the reciprocal scale.

The inversion substitution is proved as well:

```text
integral_Ioi_comp_inv      : reciprocal change of variables on the positive ray,
integral_Ioi_cpow_mul_inv  : integral_{(0,infinity)} u^(w/2-1) u^(-1/2) H(1/u) du
                               = integral_{(0,infinity)} v^((1-w)/2-1) H(v) dv,
```

so the substitution that exchanges `w` with `1 - w` is now a Lean theorem.  The side conditions of
the remaining Fubini interchange are also in place:

```text
integrableOn_rpow_mul_exp_neg_mul_Ioi : the scaled real Gamma kernel is integrable,
integrableOn_cpow_mul_gaussianKernel  : the complex Gamma kernel is integrable at rate pi t^2,
integral_Ioi_rpow_gaussianPower       : integral_{(0,infinity)} u^(sigma/2-1) exp(-pi t^2 u) du
                                          = Gamma(sigma/2) pi^(-sigma/2) t^(-sigma).
```

The Fubini interchange is proved as well, so `(8)` itself is now a Lean theorem:

```text
mellinCompletion_eq_integral_gaussianSmoothing
  : 0 < Re w, integral ||f(t)|| t^(-Re w) dt < infinity
    -> pi^(-w/2) Gamma(w/2) integral f(t) t^(-w) dt
         = integral_{(0,infinity)} u^(w/2-1) (integral_{(0,infinity)} f(t) e^{-pi u t^2} dt) du,
fourier_even_of_even
  : the Fourier transform of an even function is even,
soninMellinEvaluation_fourier
  : 0 < Re w < 1, f even, f and its Fourier transform integrable and Mellin admissible
    -> M f(w) = M(Fourier f)(1-w).                                              (8)
```

Consequently the reflected range of `(3)` follows by transporting the ambient bound across `(8)`:

```text
norm_soninMellinEvaluation_le_aperture_reflected
  : 0 < Re w < 1/2 -> ||M f w|| <= C(1-w) A^(Re w - 1/2) ||Fourier f||           (3), (4) for C_-
```

with `C(1-w) = ||gamma(1-w)|| (1/||w|| + 1/sqrt(1 - 2 Re w))`, which is exactly the constant
`C_-(w)` of the card.  Both halves of the ambient off-axis bound are therefore unconditional in
Lean.

The Sonine space is also proved to be a Hilbert space, in

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninRieszVector.lean
```

The constant-head class is exhibited as the kernel of one bounded operator --- the head cutoff minus
the rank-one projection onto the head indicator:

```text
soninHeadDefect a           = indicatorCutoff (0,a) - <head indicator, -> * a^(-1) * head indicator,
soninHeadDefect_eq_zero_iff : soninHeadDefect a f = 0 <-> f is a.e. constant on (0,a),
isClosed_soninHeadConstant  : the constant-head class is closed,
isClosed_soninExtendedSpace : L_a is a closed subspace of the even carrier,
instCompleteSpaceSoninExtendedSpace : hence L_a is complete.
```

Completeness is the missing prerequisite for the continuous Gamma-completed evaluation vector
`k_{w,a}` of `(GS3)`: with `L_a` complete and the aperture estimate bounding the completed Mellin
evaluation on it, Riesz representation produces `k_{w,a}` with `||k_{w,a}||` equal to the functional
norm, which is what turns the proved bound into the boxed form of `(3)`.

The continuous evaluation vector `k_{w,a}` of `(GS3)` now exists in the formal tree as well:

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninContinuousEvaluation.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninApertureRieszBound.lean
```

The first proves that the concrete completed Mellin integral converges absolutely on `L_a`, is
additive and homogeneous there, is continuous by the aperture estimate, and produces its
Frechet--Riesz vector:

```text
integrableOn_extendedSonin_mul_mellinKernel : absolute convergence on L_a,
burnolExtendedSoninEvaluation               : the continuous functional on L_a,
burnolExtendedSoninEvaluationVector         : its Riesz vector k_{w,a},
inner_burnolExtendedSoninEvaluationVector   : <k_{w,a}, f> = M f(w).
```

The second turns the operator estimate into the boxed form of `(3)` by testing the functional on
its own Riesz vector:

```text
norm_burnolExtendedSoninEvaluationVector_le_aperture
  : ||k_{w,a}|| <= (C(w)/sqrt 2) a^(-|Re w - 1/2|)     for 1/2 < Re w < 1.
```

So the ambient bound `(3)` is now formalized in exactly the form the card states it, as a norm bound
on the evaluation vector rather than on the functional.

The lower bound `(11)` is now proved as well, and without the co-Poisson projections: the exact
dilation character alone forces it.  In

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninDilationMellin.lean
formal/GaloisForLFunctions/RHTower/BurnolSoninCrossApertureRiesz.lean
```

the normalized dilation is shown to carry `L_a` into `L_{r^(-1) a}` in both branches, to multiply the
completed Mellin evaluation by the exact character `r^(w-1/2)`, and hence, by testing the evaluation
vector at the shrunk aperture against the dilate of the evaluation vector at `a`, to force

```text
norm_burnolExtendedSoninEvaluationVector_forward_le
  : r^(Re w - 1/2) ||k_{w,a}|| <= ||k_{w, r^(-1) a}||,
norm_burnolExtendedSoninEvaluationVector_inverse_le
  : r^(1/2 - Re w) ||k_{w,a}|| <= ||k_{w, r^(-1) a}||,
norm_burnolExtendedSoninEvaluationVector_max_le
  : max of the two characters,                                                     (11) one step
norm_burnolExtendedSoninEvaluationVector_geometric_le
  : max(...)^N ||k_{w,a}|| <= ||k_{w, r^(-N) a}||.                                 (11)
```

Since `max(r^(s-1/2), r^(1/2-s)) = r^|s-1/2|` for `r >= 1`, this is exactly the boxed lower bound
`(11)`, with the same exponent as the proved upper bound `(3)`.  Note the projections `E_j` and the
identification `(10)` are not needed for it: the Cauchy--Schwarz self-test against the dilate
already gives the sharp constant.

The two-sided law `(12)` and the limit `(13)` follow, in the same module:

```text
max_character_eq_rpow_abs
  : max(r^(s-1/2), r^(1/2-s)) = r^|s-1/2| for r >= 1,
norm_burnolExtendedSoninEvaluationVector_geometric_lower
  : ||k_{w,a}|| r^(N |Re w - 1/2|) <= ||k_{w,a_N}||,                               (12) lower
norm_burnolExtendedSoninEvaluationVector_geometric_upper
  : ||k_{w,a_N}|| <= (C(w)/sqrt 2) a^(-|Re w - 1/2|) r^(N |Re w - 1/2|),           (12) upper
tendsto_log_norm_burnolExtendedSoninEvaluationVector
  : k_{w,a} /= 0 -> lim_N log||k_{w,a_N}|| / (N log r) = |Re w - 1/2|.             (13)
```

So `(12)` holds unconditionally with `c_w = ||k_{w,a}||` and the explicit ambient `C_w`, and `(13)`
holds as soon as the base evaluation vector is nonzero.  The positivity of `C_w` needed for `(13)`
is obtained from the `N = 0` case of the upper bound rather than from nonvanishing of the Gamma
factor.

The nonvanishing hypothesis is now reduced to a single witness, in

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninApertureMonotone.lean
```

Shrinking the aperture weakens the constant-head condition, so the extended Sonine spaces decrease:

```text
soninExtendedSpace_mono
  : a <= b -> L_b <= L_a,
burnolExtendedSoninEvaluationVector_eq_zero_iff
  : k_{w,a} = 0 <-> the completed Mellin evaluation vanishes identically on L_a,
burnolExtendedSoninEvaluationVector_ne_zero_of_le
  : a <= b, k_{w,b} /= 0 -> k_{w,a} /= 0,
burnolExtendedSoninEvaluationVector_ne_zero_of_witness
  : one g in L_b with M g(w) /= 0 gives k_{w,a} /= 0 for every a <= b.
```

So `(10)` no longer has to be established at every aperture: exhibiting one vector of one extended
Sonine space with nonvanishing completed Mellin evaluation makes `(13)` unconditional at every
smaller aperture.  That single witness --- Burnol's co-Poisson construction --- is the last missing
object.

The witness target is further halved in

```text
formal/GaloisForLFunctions/RHTower/BurnolSoninEigenWitness.lean
```

The cosine transform is an involution of `L_a`, so every Sonine vector splits into self-dual and
anti-self-dual parts, both Sonine at the same aperture, and the completed Mellin evaluation is
additive there:

```text
soninSelfDualPart / soninAntiSelfDualPart, with F g = g resp. F g = -g,
soninSelfDualPart_add_antiSelfDualPart : their sum is 2 f,
exists_cosine_eigen_witness
  : a Sonine vector with nonvanishing evaluation forces an eigenvector with nonvanishing evaluation,
mem_soninExtendedSpace_of_cosine_eigen
  : an even cosine eigenvector with constant aperture head is automatically in L_a,
burnolExtendedSoninEvaluationVector_ne_zero_of_eigen_witness
  : one such eigenvector at aperture b settles nonvanishing at every a <= b.
```

The second item is the useful one: for an eigenvector the constant-head condition on the cosine
transform is automatic, so the witness has to satisfy only **one** of the two defining Sonine
conditions.  The outstanding object is therefore a single even vector `g` with `F g = ±g`, constant
on one aperture head, and `M g(w) /= 0`.

The eigen-condition is then shown to be free, in the same module:

```text
soninCosineUnitary_add_self / _sub_self
  : u + F u is self-dual and u - F u is anti-self-dual, for every even u,
mem_soninExtendedSpace_symmetrized
  : if u + F u is constant on the aperture head then it lies in L_a,
burnolExtendedSoninEvaluationVector_ne_zero_of_symmetrized_witness
  : one even u with (u + F u) head-constant and M(u + F u)(w) /= 0 settles nonvanishing
    at every smaller aperture.
```

So the witness problem now has exactly **one** condition to satisfy beyond nonvanishing: an even `u`
whose symmetrization `u + F u` is constant on one aperture head.  Self-duality is automatic, the
cosine-head condition is automatic, and the aperture is arbitrary.

Route for that last object: co-Poisson summation.  Mathlib supplies the archimedean input
(`Real.tsum_eq_tsum_fourier_of_rpow_decay`, `SchwartzMap.tsum_eq_tsum_fourier`), which is what makes
the multiplicative average of a Schwartz seed constant near the origin while remaining `L^2`.  Note
that the seed cannot itself be Schwartz: `u + F u` would then be real analytic, and constancy on an
interval would force it to vanish identically.  The non-analyticity has to come from the summation.

The co-Poisson layer of `(10)` is now present in the formal tree
(`BurnolCoPoissonSourceSpace.lean`, `BurnolCoPoissonBerezin.lean`): the literal co-Poisson sum, the
closed source space, its orthogonal projection, the quotient kernel and its reproducing identity.
**That layer is currently vacuous**, and the audit recording this is

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonInhabitedAudit.lean

burnolCoPoissonSourceSpace_eq_bot_of_isEmpty
  : with no inhabited co-Poisson source the closed source space is bottom,
burnolCoPoissonQuotientSpace_eq_of_isEmpty
  : and the quotient space is the whole extended Sonine space,
burnolExtendedSoninEvaluationVector_ne_zero_of_coPoissonSource
  : conversely one inhabited source with nonvanishing evaluation is exactly the missing witness.
```

The generator set is indexed by the structure `BurnolCoPoissonSource b`, whose Sonine membership is
carried as *data*; no term of that structure is constructed anywhere in the tree.  So every
statement about the source projection, the quotient kernel and the Berezin reader is consistent with
the source space being `⊥`, and must not be read as content until an inhabitant exists.

The constancy half of the landing statement is now proved unconditionally, in

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonHeadConstant.lean

burnolCoPoissonRightSum_term_eq_zero
  : a seed supported above b makes every term of the co-Poisson sum vanish for |t| < b,
burnolCoPoissonRightSum_eq_const
  : hence the co-Poisson value on the aperture head is its correction term, a constant,
soninHeadConstant_burnolCoPoissonRightSum
  : SoninHeadConstant b (co-Poisson sum of any seed supported in Icc b b^(-1)).
```

The mechanism is exactly Burnol's and is elementary: for `|t| < b` and `n >= 1` the argument `|t|/n`
is again below `b`, so the sum is *empty* on the aperture head and only the correction term
survives.  No analytic hypothesis beyond the support condition is used.

The same module also proves that the sum is locally finite:

```text
burnolCoPoissonRightSum_hasFiniteSupport
  : at each t only indices with n b <= |t| contribute, finitely many,
burnolCoPoissonRightSum_summable
  : hence the co-Poisson family is summable at every point, unconditionally.
```

So the co-Poisson value is a genuine finite sum at each point; no convergence hypothesis is needed
to define it.  Both ends of the contributing window are proved:

```text
burnolCoPoissonRightSum_index_window
  : a contributing index n satisfies |t| b <= n <= |t| / b.
```

That is the localization which turns the sum into a Riemann sum of mesh `1/|t|` for the correction
integral: substituting `n = |t| v` sends the window to the fixed interval `[b, b^(-1)]` and the
correction constant is exactly `integral_{[b,b^(-1)]} g(1/v) dv/v`.  Square integrability of the
co-Poisson sum is therefore the statement that this Riemann sum converges at rate `1/|t|`, which
holds for a seed of bounded variation.

An explicit candidate seed is available: `g = indicator (Icc b b^(-1))`.  Then the co-Poisson sum is
the completely explicit function

```text
P(t) = sum over n in [|t| b, |t|/b] of 1/n   -   ( -2 log b ),
```

whose profile `1/u` is monotone, so the Riemann-sum error is the classical harmonic-sum-versus-log
comparison and the `1/|t|` decay follows by monotone comparison rather than by Euler--Maclaurin.

That comparison is now proved, in

```text
formal/GaloisForLFunctions/HTGeometry/HarmonicLogWindow.lean

abs_harmonic_sub_log_sub_eulerMascheroni_le
  : |harmonic n - log n - gamma| <= 1/n,
abs_harmonic_window_sub_log_le
  : |(harmonic N - harmonic m) - (log N - log m)| <= 1/N + 1/m.
```

Mathlib sandwiches `gamma` strictly between `harmonic n - log (n+1)` and `harmonic n - log n`;
reading that sandwich in the other direction and using `log (1 + 1/n) <= 1/n` gives the sharp `1/n`
error, which is exactly the rate needed.  Applying the window form at the endpoints `m = |t| b` and
`N = |t| / b` gives the `O(1/(|t| b))` decay of the explicit co-Poisson sum, hence its square
integrability.

What an inhabitant of `BurnolCoPoissonSource b` still needs is therefore only: that
`1/|t|`-decay estimate giving square-integrability, and the cosine-side condition, for which
Burnol's intertwining `F(E phi) = E(F phi)` is the intended route.  Note the symmetrization shortcut does not bypass this:
`E phi + F(E phi) = E phi + E(F phi)`, and the second summand is head-constant only when `F phi` is
again supported above the aperture.

The archimedean input to the intertwining is now in the tree as well:

```text
formal/GaloisForLFunctions/RHTower/ArchimedeanMellinFourier.lean

even_poisson_summation
  : for an even Schwartz f,
    f(0) + 2 sum_{n>=1} f(n) = (F f)(0) + 2 sum_{n>=1} (F f)(n).
```

This is Poisson summation folded onto the positive half using evenness of `f` and of `F f`, with the
central term made explicit.  The dilation rule that carries the scale parameter through it is proved
in the same module:

```text
fourier_comp_mul_left
  : for c > 0,  F (fun v => f (c v)) w = c^(-1) F f (w / c).
```

Combining the two gives the dilated even Poisson identity, now itself a theorem:

```text
realDilationEquiv / schwartzDilate
  : scalar dilation as a continuous linear equivalence, and the dilated Schwartz function,
even_poisson_summation_dilate
  : f(0) + 2 sum_{n>=1} f(c n) = c^(-1) [ (F f)(0) + 2 sum_{k>=1} (F f)(k / c) ].
```

Collecting the two correction terms completes the intertwining, which is now a theorem:

```text
coPoissonCorrected f c
  = sum_{n>=1} f(c n) + f(0)/2 - (F f)(0)/(2c),
coPoisson_intertwine
  : c * coPoissonCorrected f c = sum_{k>=1} (F f)(k / c).
```

That is Burnol's intertwining in usable form: the corrected multiplicative sum of `f` at scale `c`,
rescaled by `c`, is the *uncorrected* multiplicative sum of `F f` at the reciprocal scale.  The two
archimedean corrections `f(0)/2` and `(F f)(0)/(2c)` are exactly what the folded Poisson identity
produces, and applying the statement twice returns the involution.

So the cosine-side condition of the landing statement rests on a proved identity: the co-Poisson sum
of a seed and the co-Poisson sum of its transform are exchanged by scale inversion, which is what
makes both of them constant on the aperture head when the seed is supported above it.

The dictionary between the literal co-Poisson sum of the source structure and this multiplicative
form is proved too:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonHeadConstant.lean

coPoissonReciprocalSeed g v = g(1/v)/v,
coPoissonRightSum_term_eq  : each term (1/n) g(t/n) is t^(-1) times the term
                             of the plain multiplicative sum of the reciprocal seed at scale 1/t,
burnolCoPoissonRightSum_eq_multiplicative
  : for t > 0, the literal co-Poisson value equals
    t^(-1) sum_{n>=1} G(n/t) - integral_{(0,infinity)} G,   with G the reciprocal seed.
```

The weight `1/n` and the correction `integral y^(-1) g(y^(-1)) dy` of the source definition are
therefore exactly the plain multiplicative sum and half-line mass of `G`, which is the shape
`coPoisson_intertwine` consumes.  No further translation is needed between the two presentations.

The same module also gives the uniform truncation needed to treat the sum as an ordinary function:

```text
burnolCoPoissonRightSum_eq_finset_sum
  : for |t| <= R the co-Poisson sum equals the fixed finite sum over Finset.range (ceil (R / b)).
```

So on every bounded region the co-Poisson sum *is* a finite sum of translates of the seed, with an
index bound depending only on the region.  Measurability is read off that representation:

```text
measurable_burnolCoPoissonRightSum
  : g measurable and supported in Icc b b^(-1) -> the co-Poisson sum is measurable.
```

The partial sums are finite sums of dilated copies of the seed, hence measurable, and they converge
pointwise by the summability above, so the limit is measurable.  This matters because mathlib has no
usable measurability lemma for a Banach-valued `tsum`; the finite/partial-sum representation avoids
needing one.

The same representation gives the uniform size bound:

```text
norm_burnolCoPoissonSum_le
  : for a seed bounded by M and supported in Icc b b^(-1), and t /= 0,
    || sum_{n>=1} (1/n) g(|t|/n) || <= ceil(|t|/b) * M / (|t| b).
```

Every contributing index exceeds `|t| b`, so each term is at most `M/(|t| b)`, and there are at most
`ceil(|t|/b)` of them; the product is bounded uniformly in `t`.  So the co-Poisson sum of a bounded
seed is a bounded measurable function, and what the `L^2` statement still needs is only the sharper
`1/|t|` decay of the *difference* from the correction constant, which is the harmonic-window
comparison already proved.

That sharper decay is now proved for an explicit seed.  The simplest seed supported in the
multiplicative window is its indicator, and for it every step is computable:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIndicatorSeed.lean

coPoissonIndicatorSeed b            = indicator of Icc b b^(-1),
coPoissonIndicatorSeed_correction   : the correction constant is 2 log(1/b),
                                      the logarithmic length of the window,
coPoissonIndicatorSum_eq_finset_sum : the co-Poisson sum is the pure window sum
                                      sum_{ceil(t b) <= k <= floor(t/b)} 1/k,
coPoissonIndicatorSum_eq_harmonic   : that window sum is harmonic(floor(t/b)) - harmonic(ceil(t b) - 1),
norm_burnolCoPoissonRightSum_coPoissonIndicatorSeed_le
  : for t >= 2/b,  |co-Poisson value| <= (4 b + 4/b) / t.
```

The decay proof uses no expansion.  For every positive `t` the correction constant is itself a
logarithmic difference of the two window ends, `2 log(1/b) = log(t/b) - log(t b)`, so the co-Poisson
value splits into three comparisons each of which is a single reciprocal endpoint: the harmonic
window comparison at the two integer ends, and the two floor/ceiling corrections.  Both ends are
comparable to `t`, which gives the constant above.

The window-sum side of that identity is a general fact recorded once:

```text
formal/GaloisForLFunctions/HTGeometry/HarmonicLogWindow.lean

sum_Ioc_inv_eq_harmonic_sub  : sum_{m < n <= N} 1/n = harmonic N - harmonic m,
abs_sum_Ioc_inv_sub_log_le   : that window sum differs from log(N/m) by at most 1/N + 1/m,
abs_log_sub_log_le_inv       : between consecutive integers the logarithm moves by at most 1/n.
```

Decay plus a crude local bound gives square integrability, through a reusable profile:

```text
formal/GaloisForLFunctions/HTGeometry/L2DecayProfile.lean

memLp_two_decayProfile        : (1 + |t|)^(-1) is in L^2 of the line,
memLp_two_of_decayProfile     : a measurable function dominated by a multiple of that profile is L^2.
```

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIndicatorSeed.lean

norm_coPoissonIndicatorSum_le_scale
  : the window sum is at most t/b (every term at most one, at most t/b indices),
norm_burnolCoPoissonRightSum_coPoissonIndicatorSeed_le_profile
  : the co-Poisson value is dominated by a constant times (1 + |t|)^(-1),
memLp_two_burnolCoPoissonRightSum_coPoissonIndicatorSeed
  : hence it is square integrable on the line.
```

The vector itself is then built and its first Sonine condition discharged:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIndicatorVector.lean

memLp_toLp_mem_evenSubspace          : an a.e. even L^2 function is a vector of the even carrier,
coPoissonIndicatorEven               : the indicator co-Poisson vector in that carrier,
soninHeadConstant_coPoissonIndicatorEven
  : its aperture head is constant,
coPoissonIndicatorSource             : with the cosine head condition, a full BurnolCoPoissonSource b,
nonempty_burnolCoPoissonSource_of_cosineHead
  : so the co-Poisson layer is inhabited as soon as that one condition holds.
```

This is the sharp form of the inhabitation question.  Integrability, compact multiplicative support,
square integrability, evenness, constancy of the aperture head, and the almost-everywhere
identification of the vector with the literal co-Poisson sum are all unconditional for the indicator
seed.  What remains is exactly one analytic statement: that the cosine transform of the indicator
co-Poisson vector is also almost everywhere constant on `(0, b)`.

That one condition can be named exactly.  The reciprocal seed `G(v) = g(1/v)/v` of a window seed is
again a window seed, and the assignment is an involution:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIndicatorSeed.lean

support_coPoissonReciprocalSeed      : the reciprocal seed is supported in the same window,
coPoissonReciprocalSeed_involutive   : taking the reciprocal seed twice returns the seed,
coPoissonReciprocalSeed_coPoissonIndicatorSeed
  : the reciprocal of the indicator seed is v |-> 1/v on the window.
```

Burnol's intertwining says the cosine transform of a co-Poisson sum is the co-Poisson sum of the
reciprocal seed.  On Mellin transforms that is exactly the functional equation of zeta: the
co-Poisson sum of `g` has Mellin transform `zeta(1-s) M g(s)`, the reciprocal seed satisfies
`M G(s) = M g(1-s)`, and the cosine kernel contributes the archimedean factor, so the identity
`chi(s) zeta(s) = zeta(1-s)` is precisely what makes the two sides agree.  Granting it, the second
Sonine condition is the first one applied to the reciprocal seed:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIndicatorVector.lean

soninHeadConstant_cosine_coPoissonIndicatorEven_of_intertwine
  : the intertwining identity gives the cosine head condition,
nonempty_burnolCoPoissonSource_of_intertwine
  : and hence inhabits BurnolCoPoissonSource b.
```

So the whole co-Poisson layer now rests on one almost-everywhere identity between two explicit
functions of the line, with every other input discharged unconditionally.

A naive term-by-term proof of that identity fails, and the reason is worth recording.  Poisson
summation gives the co-Poisson sum as a plain sum of dilates, `P_g(t) = sum_{k>=1} (F G_e)(k t)`
with `G_e` the even extension of the reciprocal seed; transforming that series term by term yields
`sum_{k>=1} (1/k) G_e(xi/k)`, which tends to `integral_0^infinity g` rather than to zero and so is
not square integrable unless the seed has zero mass.  The missing correction is exactly the constant
subtracted in the co-Poisson definition, and it is invisible to termwise transformation because the
series `sum_k (F G_e)(k .)` is not convergent in `L^2` --- its terms have norms `k^(-1/2) ||F G_e||`.
The identity is therefore a genuine Mellin--Plancherel statement, not a rearrangement.

The Mellin--Plancherel content is being built directly, in the test-function picture, where the
identity becomes an equality of pairings against Schwartz functions.  Two ingredients are proved.

First, the constants.  The correction of a co-Poisson sum is the logarithmic mass of its seed, and
the correction of the reciprocal seed is the plain half-line mass:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonCorrectionConstant.lean

coPoissonCorrectionConstant_eq_logMass
  : integral_0^infinity g(1/y) dy/y = integral_0^infinity g(y) dy/y,
coPoissonCorrectionConstant_reciprocalSeed
  : the correction constant of the reciprocal seed is integral_0^infinity g.
```

These are the two constants that cancel in the intertwining: the logarithmic mass against the
correction of the seed, the plain mass against the correction of the reciprocal seed.

Second, the Fubini step.  Quadratic decay makes the dilated sums of a Schwartz function absolutely
convergent, uniformly in the scale:

```text
formal/GaloisForLFunctions/HTGeometry/SchwartzDilateSummability.lean

exists_sq_norm_bound             : quadratic decay of a Schwartz function,
summable_norm_schwartzDilate     : sum_{n>=1} ||f(u n)|| converges for every positive scale,
exists_tsum_norm_schwartzDilate_le
  : and is bounded by a fixed multiple of 1/u^2.
```

With that, the sum and the integral can be exchanged, and the multiplicative sum over the seed
becomes a sum of dilates of the test function:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonPairing.lean

integral_coPoissonTerm_eq        : one term pairs as a dilated pairing of the seed,
integral_norm_seed_mul_schwartzDilate_le
  : the seed lives above the aperture, so the k-th pairing is O(1/k^2),
integral_coPoissonSum_mul_eq
  : integral_0^infinity (sum_{n>=1} g(t/n)/n) w(t) dt
      = integral_0^infinity g(u) (sum_{n>=1} w(n u)) du.
```

The right-hand side is exactly the shape Poisson summation acts on: replacing `sum_{n>=1} w(n u)`
by the transformed sum at scale `1/u` is what converts the seed into its reciprocal seed and
produces the second co-Poisson sum.

Both are now proved, and with them the intertwining itself in pairing form:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIntertwining.lean

integral_seed_inv_mul_dilate     : inverting the ray exchanges g with its reciprocal seed,
integral_tsum_seed_inv_dilate_eq : and does so for the whole contracted sum, term by term,
tsum_schwartzDilate_poisson      : Poisson summation, in the form the co-Poisson sum consumes,
integral_Ioi_fourier_eq          : Fourier inversion at the origin, giving the half-line mass,
integral_seed_mul_tsum_schwartzDilate_split
  : the three pieces of the transformed pairing,
integral_Ioi_burnolCoPoisson_mul_eq_fourier
  : integral_0^infinity P_g(t) w(t) dt = integral_0^infinity P_G(t) (F w)(t) dt
    for every even Schwartz w.
```

The two constants cancel exactly, and that is the whole content of the identity.  The Poisson step
produces a term `(F w)(0)/2` times the logarithmic mass of the seed; the logarithmic mass is the
correction constant of `P_g`, and `(F w)(0)/2` is the half-line mass of `w`, so that term is exactly
the correction subtracted on the left.  On the other side the ray inversion produces the plain mass
of the seed, which is the correction constant of `P_G`, times `w(0)/2`, which by Fourier inversion
is the half-line mass of `F w` --- exactly the correction subtracted on the right.  Nothing is left
over.

The measurability that a direct argument would need is supplied by the exchange theorem itself: the
contracted sum is never differentiated from its terms, only resummed after each term has been
inverted, so the interchange and the change of variables never meet.

The pairing identity extends to the line and then to the `L^2` vectors themselves.  Both co-Poisson
sums are even, so only the even part of a test function contributes, and the Fourier transform
commutes with taking even parts:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIntertwiningLine.lean

schwartzEvenPart, fourier_schwartzEvenPart
  : the even part of a Schwartz function, and its commutation with the transform,
integral_mul_eq_evenPart
  : only the even part of a test function pairs with an even function,
integral_line_burnolCoPoisson_mul_eq_fourier
  : the intertwining pairing for every Schwartz test function on the line.
```

A vector of `L^2` is determined by its pairings against Schwartz functions, and the `L^2` Fourier
transform sends the class of a Schwartz function to the class of its transform, so the pairing
identity *is* the operator identity:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIntertwiningL2.lean

inner_toLp_eq_integral            : the inner product against a Schwartz class as an integral,
fourierUnitary_eq_of_schwartz_pairing
  : a Schwartz pairing identity determines the L^2 Fourier transform,
fourierUnitary_coPoissonVector
  : the L^2 Fourier transform of the co-Poisson vector of a window seed is the co-Poisson
    vector of the reciprocal seed.
```

The density is the one the corpus already used for reflection: Schwartz classes are dense in `L^2`,
and the Fourier unitary is a homeomorphism, so their images are dense as well; the functional
`z |-> <d, z>` is continuous and vanishes on that dense family, hence identically, hence `d = 0`.

The size data for the reciprocal seed is elementary, and it is proved.  The reciprocal seed is
`v |-> 1/v` on the window, so every contributing term of its co-Poisson sum is exactly `1/t` and the
sum is the number of window indices divided by `t`, minus the plain mass `1/b - b`.  The index count
is `t(1/b - b)` up to one unit, so the value is `O(1/t)` with no harmonic comparison at all:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIndicatorReciprocal.lean

coPoissonReciprocalIndicator_term      : each term is 1/t on the window,
coPoissonReciprocalIndicatorSum_eq_card: the sum is the window cardinality over t,
coPoissonReciprocalIndicator_correction: the correction is the window length 1/b - b,
burnolCoPoissonRightSum_reciprocalIndicator_eq_card
  : exact pointwise formula, card/t - (1/b - b),
norm_burnolCoPoissonRightSum_reciprocalIndicator_le        : O(1/t) beyond 2/b,
norm_burnolCoPoissonRightSum_reciprocalIndicator_le_local  : a uniform local bound,
memLp_two_burnolCoPoissonRightSum_reciprocalIndicator      : hence L^2,
star_burnolCoPoissonRightSum_coPoissonIndicatorSeed,
star_burnolCoPoissonRightSum_reciprocalIndicator           : both values are real.
```

With those, every hypothesis of the `L^2` intertwining is discharged for the indicator seed, and the
outstanding condition falls:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonIndicatorSource.lean

coeFn_soninCosineUnitary_coPoissonIndicatorEven
  : the cosine transform of the indicator co-Poisson vector is the co-Poisson
    vector of the reciprocal seed,
soninHeadConstant_cosine_coPoissonIndicatorEven
  : hence its aperture head is constant --- the second Sonine condition,
burnolCoPoissonIndicatorSource   : a literal BurnolCoPoissonSource b,
nonempty_burnolCoPoissonSource   : the co-Poisson source layer is inhabited for
                                   every aperture 0 < b <= 1.
```

**The vacuity recorded by the inhabitation audit is resolved.**  The collapse theorems
(`burnolCoPoissonSourceSpace_eq_bot_of_isEmpty` and its companions) no longer apply at any aperture
in `(0, 1]`: the generator set is nonempty, the source space is not `bot`, and the quotient space is
a proper subspace of the extended Sonine space.  Every statement about the source projection and the
quotient kernel is now contentful.

The inhabitant is not an abstract object: it is the classical fractional-part kernel.  Counting the
integers in the window `[t b, t / b]` exactly --- its length corrected by the two endpoint
fractional parts --- and dividing by `t` gives

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonFractionalKernel.lean

windowCard_eq_fract
  : card = t (1/b - b) + fract(t b) - fract(t / b),
burnolCoPoissonRightSum_reciprocalIndicator_eq_fract
  : the reciprocal-indicator co-Poisson value is (fract(t b) - fract(t / b)) / t,
measure_zero_fract_eq_zero
  : the exceptional scales, where t b is an integer, form a null set,
burnolCoPoissonRightSum_reciprocalIndicator_ae_fract
  : so the identity holds almost everywhere on the positive ray.
```

The window mass `1/b - b` is exactly the length term, so it cancels and only the two fractional
parts survive.  This is the bridge to zeta inside the critical strip: on `0 < Re w < 1` the Mellin
transform of `fract` is `integral_0^infinity fract(u) u^(-1-w) du = -zeta(w)/w`, and dilation by `b`
and by `1/b` gives

`integral_0^infinity P_G(t) t^(-w) dt = (b^(-w) - b^w) zeta(w) / w`,

so the completed Mellin evaluation of the inhabitant is nonzero at every `w` of the strip at which
zeta does not vanish.  The remaining formal work is that Mellin computation, which is a statement
about the fractional part alone and no longer mentions the Sonine space.

The zeta half of that computation is now formal, on the whole right half-plane:

```text
formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean

riemannZeta_eq_mul_integral_floor
  : on Re s > 1, zeta(s) = s * integral_1^infinity floor(t) t^(-s-1) dt   (Abel summation),
integral_Ioi_one_fract_cpow
  : hence integral_1^infinity fract(t) t^(-s-1) dt = 1/(s-1) - zeta(s)/s there,
differentiableAt_mellin_fractTailKernel
  : the left-hand side is a Mellin transform of a bounded kernel vanishing near zero,
    so it is holomorphic on the whole half-plane Re s > 0,
isPreconnected_puncturedRightHalfPlane
  : the right half-plane with the pole removed is connected,
integral_Ioi_one_fract_cpow_of_re_pos
  : so the formula holds for every s with Re s > 0 and s /= 1.
```

Only the elementary half of Abel summation is needed: replacing `floor t` by `t - fract t` splits
the integral into `integral_1^infinity t^(-s)`, which is `1/(s-1)`, and the fractional-part integral.
The fractional part is bounded and vanishes below `1`, so its Mellin transform converges and is
holomorphic on all of `Re s > 0`, while the right-hand side is holomorphic away from the pole; the
two agree on `Re s > 1`, and the punctured half-plane is connected because it is the union of four
convex half-plane intersections chained through `1/2 + i`, `1/2 - i` and `2 + i`.

That passage is now complete.  On `(0,1)` the fractional part is the identity, so the near end of
the integral is `1/(1-w)`; it cancels the pole of the far end exactly, and the two dilations
contribute `b^w` and `b^(-w)`:

```text
formal/GaloisForLFunctions/RHTower/FractionalPartZeta.lean

integral_Ioc_zero_one_fract_cpow  : the near end is 1/(1-w),
integral_Ioi_zero_fract_cpow      : hence integral_0^infinity fract(u) u^(-w-1) du = -zeta(w)/w
                                    on the strip 0 < Re w < 1,
integral_Ioi_zero_fract_dilate_cpow
  : dilating the argument by c multiplies that integral by c^w.
```

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonMellinZeta.lean

integral_Ioi_burnolCoPoisson_reciprocalIndicator_cpow
  : integral_0^infinity P_G(t) t^(-w) dt = (b^(-w) - b^w) zeta(w) / w
    for every w with 0 < Re w < 1.
```

So the inhabitant's Mellin transform is computed in closed form on the whole critical strip, and it
vanishes exactly where `zeta` does (the window factor `b^(-w) - b^w` is nonzero for `0 < b < 1` and
`Re w > 0`, since `b^(-2w) = 1` would force `Re w = 0`).

This also isolates precisely what cannot come from the co-Poisson side.  Every co-Poisson Mellin
transform carries the factor `zeta(w)`, so at a hypothetical zero in the strip the witness must come
from *outside* the co-Poisson subspace --- which is exactly where Burnol's dimension count for the
quotient lives.  What is unconditionally reachable, and what these modules deliver, is the
implication `zeta(w) /= 0 -> k_{w,a} /= 0`, which makes the exponent law `(13)` unconditional off the
zero set.

That implication is now proved, and with it the exponent law itself:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonMellinNonvanishing.lean

mellinCompletionFactor_ne_zero  : pi^(-w/2) Gamma(w/2) /= 0 on Re w > 0,
windowFactor_ne_zero            : b^(-w) - b^w /= 0 for 0 < b < 1 and Re w > 0,
coPoissonIndicatorSoninCosine   : the inhabitant as a vector of the extended Sonine space,
soninMellinEvaluation_coPoissonIndicatorSoninCosine
  : its completed Mellin evaluation is
    pi^(-w/2) Gamma(w/2) * (b^(-w) - b^w) * zeta(w)/w,
burnolExtendedSoninEvaluationVector_ne_zero_of_riemannZeta_ne_zero
  : hence k_{w,a} /= 0 whenever zeta(w) /= 0,
tendsto_log_norm_burnolExtendedSoninEvaluationVector_of_riemannZeta_ne_zero
  : and the aperture-type limit (13) holds with exponent |Re w - 1/2|,
    unconditionally off the zero set of zeta.
```

The window factor is nonzero for a purely metric reason: `|b^(-w)| = b^(-Re w)` and
`|b^w| = b^(Re w)`, and for `0 < b < 1` the map `x |-> b^x` is strictly decreasing, so the two
moduli agree only when `Re w = 0`.

**Status of `(10)`.**  The nonvanishing hypothesis is now discharged at every point of the strip
outside the zero set of zeta, so `(13)` is unconditional there.  At a hypothetical zero it cannot be
discharged from the co-Poisson side at all --- every co-Poisson Mellin transform carries the factor
`zeta(w)` --- and a witness would have to come from the orthogonal complement of the co-Poisson
subspace, which is where Burnol's dimension count for the quotient lives.  That is the honest
boundary of the present construction.

The boundary itself is now machine-checked, as a dichotomy:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonMellinNonvanishing.lean

soninMellinEvaluation_coPoissonIndicatorSoninCosine_ne_zero_iff
  : the explicit witness has nonzero evaluation exactly when zeta(w) /= 0,
inner_burnolExtendedSoninEvaluationVector_coPoissonIndicatorSoninCosine_eq_zero
  : at a zero the evaluator is orthogonal to the explicit co-Poisson vector.
```

So the construction decides `(10)` off the zero set and provably cannot decide it on the zero set:
the witness there must be orthogonal to the whole co-Poisson subspace.  That is precisely the
content Burnol supplies by the orthogonal-complement theorem, and it is what `(10)` asserts in the
displayed form `y_{rho,N} = k_{rho,a_N} /= 0`.

One point of the general argument is not reachable from the explicit seed alone.  The orthogonality
above is proved for the explicit inhabitant; extending it to *every* co-Poisson source needs the
Mellin transform `zeta(w) M g(w)` for a general window seed, and that identity has no
fractional-part shortcut --- for a merely integrable seed the co-Poisson value need not even be
`O(1/t)`, so the continuation has to be run through Mellin--Plancherel rather than through an
explicit kernel.

The dichotomy extends across the critical line without any new analysis.  Below the line the
reflected Riesz vector *is* the cosine transform of the evaluation vector at the reflected point
(`burnolExtendedSoninReflectedEvaluationVector_eq_cosine`), the cosine transform is an isometric
equivalence, and the zeta zero locus is invariant under `s |-> 1 - s` --- a fact the corpus already
owned in `ReflectionCocycleClass`:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonMellinNonvanishing.lean

burnolExtendedSoninReflectedEvaluationVector_ne_zero_of_riemannZeta_ne_zero
  : below the line the reflected evaluation vector is nonzero wherever zeta is,
burnolExtendedSoninEvaluationVector_ne_zero_of_riemannZeta_ne_zero_upper
  : the reflected form of the same statement above the line.
```

So `(10)` is settled on both halves of the open strip, off the zero set, from the single explicit
inhabitant.

The explicit family is not a single vector: the reciprocal function on *any* multiplicative
sub-window `[c,d]` is a seed of the same kind, with the same fractional-part form and the same
zeta factor:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSubWindow.lean

coPoissonSubWindowSeed c d           = the reciprocal function on [c,d],
coPoissonSubWindowSum_eq             : its co-Poisson sum counts the window indices,
coPoissonCorrectionConstant_coPoissonSubWindowSeed
  : its correction constant is the length 1/c - 1/d of the inverted window,
burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_fract
  : so its co-Poisson value is (fract(t/d) - fract(t/c))/t,
integral_Ioi_burnolCoPoisson_subWindow_cpow
  : with Mellin transform (d^(-w) - c^(-w)) * (-zeta(w)/w) on the strip,
integral_Ioi_burnolCoPoisson_subWindow_cpow_eq_zero
  : and therefore zero at every zeta zero.
```

Taking `d = 1/c` recovers the symmetric window.  So the annihilation at a zero is not an accident of
one seed: it holds across a two-parameter family of explicit inhabitants of every aperture, which is
the concrete form of the statement that the whole co-Poisson subspace is annihilated there.

The full analytic size data for the family is proved as well, so each member is a genuine `L^2`
vector of the carrier and not merely a formal expression:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSubWindow.lean

abs_subWindowCard_sub_le    : the index count is the expected count up to one unit,
norm_..._le                 : hence the value is bounded by 1/t,
norm_..._le_global          : and by 2/c everywhere (the window has at most t/c indices),
support_..._symmetric       : a sub-window sits inside the symmetric window of aperture min(c, 1/d),
measurable_..., norm_..._le_profile, memLp_two_..., star_...
  : measurable, dominated by a multiple of (1 + |t|)^(-1), square integrable, and real.
```

The `1/t` bound here needs no harmonic comparison at all: both fractional parts lie in `[0,1)`, so
the numerator of `(fract(t/d) - fract(t/c))/t` is bounded by one outright.

The other member of each co-Poisson pair is the plain indicator of the inverted window, and it is
now built at the same generality:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonWindowIndicator.lean

coPoissonWindowIndicatorSeed c d      = the indicator of [c,d],
coPoissonReciprocalSeed_coPoissonSubWindowSeed
  : the reciprocal seed of the sub-window reciprocal is exactly the indicator of the
    inverted window, so the two form a co-Poisson pair,
integral_Icc_inv_ofReal               : the logarithmic length of a window,
coPoissonCorrectionConstant_coPoissonWindowIndicatorSeed
  : hence its correction constant is log d - log c,
coPoissonWindowIndicatorSum_eq_finset_sum, coPoissonWindowIndicatorSum_eq_harmonic
  : its co-Poisson sum is the harmonic window sum,
burnolCoPoissonRightSum_coPoissonWindowIndicatorSeed
  : giving the value harmonic(floor(t/c)) - harmonic(ceil(t/d) - 1) - (log d - log c).
```

Taking `d = 1/c` recovers the symmetric window throughout, so the earlier one-parameter results are
the diagonal of this family.

The decay estimate for the general window indicator is proved by the same three-comparison
argument, now with the constant `log d - log c` at the two endpoints:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonWindowIndicator.lean

log_window_eq_log_div_sub_log_div
  : log d - log c = log(t/c) - log(t/d) at every positive scale,
norm_..._le               : hence the value is O(1/t) beyond the scale 2d,
norm_..._le_local         : with the uniform local bound |t|/c + (log d - log c),
norm_..._le_profile       : dominated by a multiple of (1 + |t|)^(-1),
memLp_two_..., star_...   : square integrable and real,
integrable_coPoissonSubWindowSeed
  : and the partner seed is integrable, closing the analytic data for the pair.
```

Both members of every co-Poisson pair now carry full analytic data --- integrability, support in a
symmetric window, measurability, boundedness, reality and square integrability --- which is exactly
the hypothesis list of the `L^2` intertwining theorem.

That assembly is done: every sub-window now yields a genuine source and a genuine Sonine vector.

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonSubWindowSource.lean

subWindowAperture c d                = min (c, 1/d),
fourierUnitary_coPoissonSubWindowVector
  : the intertwining for the pair (reciprocal on [c,d], indicator of [1/d,1/c]),
coPoissonSubWindowEven, soninHeadConstant_coPoissonSubWindowEven,
soninHeadConstant_cosine_coPoissonSubWindowEven
  : both Sonine conditions,
coPoissonSubWindowSonin              : the vector of the extended Sonine space,
coPoissonSubWindowSource             : a literal BurnolCoPoissonSource at that aperture,
soninMellinEvaluation_coPoissonSubWindowSonin
  : its completed Mellin evaluation is Gamma_R(w) (d^(-w) - c^(-w)) (-zeta(w)/w),
subWindowFactor_ne_zero              : the window factor is nonzero whenever c < d,
burnolExtendedSoninEvaluationVector_ne_zero_of_subWindow
  : so every sub-window with c < d is a witness, at every aperture below min (c, 1/d).
```

The window factor is nonzero for the same metric reason as before: `|c^(-w)| = c^(-Re w)` and
`|d^(-w)| = d^(-Re w)`, and for `0 < c < d` and `Re w > 0` those are different.  So `(10)` off the
zero set is witnessed not by one vector but by a two-parameter family, at every aperture.

The dichotomy is exact for every member of the family:

```text
soninMellinEvaluation_coPoissonSubWindowSonin_ne_zero_iff
  : the evaluation of a sub-window vector is nonzero exactly when zeta(w) /= 0,
soninMellinEvaluation_coPoissonSubWindowSonin_eq_zero,
inner_burnolExtendedSoninEvaluationVector_coPoissonSubWindowSonin_eq_zero
  : at a zero the evaluator annihilates every sub-window vector.
```

So the entire explicit family --- and by linearity its span --- lies in the kernel of the evaluation
at a zero.  This is the precise sense in which the co-Poisson side cannot decide `(10)` there.

Because aperture monotonicity lets a Sonine vector be read at any smaller aperture, the whole family
can be placed in a single extended Sonine space, which is the shape the quotient discussion needs:

```text
coPoissonSubWindowSoninAt        : a sub-window vector read at any aperture A <= min(c,1/d),
subWindowAperture_left_eq        : for a <= d <= 1/a the window [a,d] has aperture exactly a,
                                   so the family {[a,d]} is a one-parameter family at aperture a,
inner_burnolExtendedSoninEvaluationVector_subWindowAt_eq_zero,
inner_burnolExtendedSoninEvaluationVector_subWindowAt_ne_zero
  : at one fixed aperture, the evaluator annihilates the whole family at a zeta zero and
    is nonzero against it off the zero set.
```

That family generates a closed subspace, and the two halves of the dichotomy become statements
about it:

```text
burnolSubWindowGenerators A, burnolSubWindowSpace A
  : the sub-window vectors readable at aperture A, and their closed span,
inner_eq_zero_of_mem_burnolSubWindowSpace
  : at a zeta zero the evaluator annihilates the whole closed span --- the concrete
    form of `y_{rho,N} = k_{rho,a_N}` for the explicit part of the source space,
burnolExtendedSoninEvaluationVector_notMem_orthogonal_of_ne_zero
  : off the zero set the span already detects the evaluator.
```

Passing from the generators to the closed span is the standard argument: the functional
`u |-> <k, u>` is continuous, so its kernel is a closed submodule containing the generators, hence
containing their closed span.

That span is not the zero space, so the orthogonality is a genuine constraint and not vacuous:

```text
burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_const
  : below the lower window end the co-Poisson value is the constant -(1/c - 1/d),
coPoissonSubWindowEven_ne_zero
  : hence the vector is nonzero for c < d --- it is a nonzero constant on the whole
    segment (0,c), a set of positive measure,
burnolSubWindowSpace_ne_bot
  : so the explicit co-Poisson subspace is nontrivial at every aperture.
```

This is the quantitative form of the earlier inhabitation result: the collapse theorems of the
inhabitation audit asserted that an empty source type forces the source space to be `bot`; the
source type is now not only inhabited but supplies vectors that are provably nonzero.

The same constant separates different windows, so the family is genuinely a family:

```text
coPoissonSubWindowEven_inj_right
  : if two sub-window vectors with the same lower end agree, the upper ends agree.
```

The constant `-(1/c - 1/d)` on `(0,c)` is a complete invariant of the upper window end, so the
one-parameter family `d |-> P_{[c,d]}` is injective and the explicit inhabitants are pairwise
distinct.

Distinctness is upgraded to independence by the Mellin transform.  Pairing a vanishing linear
combination of sub-window vectors against the Mellin evaluator gives, at every strip point where
zeta does not vanish, the relation `sum_i lambda_i (d_i^(-w) - c^(-w)) = 0`.  The left side is the
restriction of an entire function of `w`; it vanishes on a whole neighbourhood of any strip point
where zeta does not vanish, so the identity theorem propagates it to the whole plane, and there
Dedekind's independence of characters applies to the monoid homomorphisms
`w |-> exp(-w log x)` of the additive group of the complex plane:

```text
riemannZeta_ne_zero_of_ofReal_mem_Ioo
  : zeta has no zero on the real segment (0,1).
linearIndependent_coPoissonSubWindowSoninAt
  : sub-window vectors with a common lower end and distinct upper ends are linearly independent.
not_finiteDimensional_burnolSubWindowSpace
  : the explicit co-Poisson subspace at aperture A is infinite dimensional, for every 0 < A < 1.
not_finiteDimensional_burnolCoPoissonSourceSpace
  : Burnol's own co-Poisson source space at aperture A is infinite dimensional.
```

The residual analytic item of the whole layer --- the Mellin transform of the co-Poisson sum of a
*general* integrable seed --- is now proved, and the route is worth recording because four earlier
routes had been ruled out.  The obstruction in all of them was that the co-Poisson sum and its
correction constant are separately non-integrable against `t^(-w)` on the strip: only their
difference is.  Every route that tried to bound the two halves separately produced the divergent
`sum_k k^(-Re w)`.

The fix is to truncate the `t`-integral at a finite cutoff `T` **before** doing anything else.  For
`t <= T` the seed's support forces `k <= T/b`, so the co-Poisson sum is a *fixed finite* `Finset`
sum on the whole range of integration and the interchange with the integral is elementary --- no
Fubini, no dominated convergence in `k`, no interchange of an infinite sum with an integral.
Substituting `t = k u` in each of the finitely many terms leaves

`integral_{Ioc 0 T} P_g(t) t^(-w) dt = integral_{Ioi 0} g(u) kappa_T(u) du`,
`kappa_T(u) = u^(-w) sum_(k <= floor(T/u)) k^(-w) - u^(-1) T^(1-w)/(1-w)`.

The two divergent halves of `kappa_T` cancel *identically*, not asymptotically, because
`u^(-w) (T/u)^(1-w) = u^(-1) T^(1-w)` exactly; what is left after subtracting `zeta(w) u^(-w)` is
the partial-sum error of `sum_(k<=N) k^(-w) - N^(1-w)/(1-w)` plus the floor error
`N^(1-w) - (T/u)^(1-w)`, and both are `O(N^(-sigma))`.  The first is the corpus asset
`tendsto_sum_cpow_sub_pow`; the second is `exp` applied to `log(M/N) <= 1/N`.  So `kappa_T`
converges pointwise to `zeta(w) u^(-w)` with the uniform bound
`|kappa_T(u)| <= u^(-sigma)(|zeta(w)| + sup|eps_N| + 2)` on the window, and one application of
dominated convergence against `|g| in L^1` finishes it.  The `L^2` hypothesis of
`BurnolCoPoissonSource` is never used for the identity --- only integrability of the seed, and
Mellin integrability of the co-Poisson sum, which the extended Sonine space supplies for free.

The one point where zeta is known not to vanish is supplied by the fractional-part formula itself:
for real `s` in `(0,1)` the integrand of `-zeta(s)/s = integral_0^infinity fract(u) u^(-s-1) du` is
nonnegative and strictly positive on `(1,2)`, so `zeta(s) < 0` there.  No zero-free region and no
density estimate is used --- a single real point suffices, because the identity theorem does the
rest.  The window ends are supplied by an explicit ladder inside `(A, 1/A)`, and the sources are
read at the common aperture `A` through `coPoissonSubWindowSourceAt`, so the independent vectors
are honest members of `burnolCoPoissonSourceSpace A` and not merely of the explicit sub-object.

The co-Poisson sum is linear in its seed, so the annihilation at a zero is a property of the whole
span of the explicit family, not of individual seeds:

```text
formal/GaloisForLFunctions/RHTower/BurnolCoPoissonLinearity.lean

burnolCoPoissonRightSum_const_smul  : scaling the seed scales the sum (unconditional),
burnolCoPoissonRightSum_add         : adding seeds adds the sums, given summability and
                                      integrability of the two correction integrands,
correction_integrand_coPoissonSubWindowSeed, integrableOn_correction_...
  : for a sub-window seed the correction integrand is literally the indicator of the
    inverted window, so both conditions are explicit,
ae_burnolCoPoisson_subWindow_cpow, integrableOn_burnolCoPoisson_subWindow_cpow
  : the paired Mellin integrand is integrable, being a difference of two dilated
    fractional-part kernels,
integral_Ioi_burnolCoPoisson_subWindow_pair_cpow_eq_zero
  : hence a two-term combination is annihilated at every zeta zero.
```

Scaling is unconditional because both `tsum_mul_left` and `integral_const_mul` are; additivity is
the step that needs the correction integrand to be integrable.  That change of variables is now
proved in general, by the `rpow` substitution of exponent `-1`:

```text
integrableOn_logMass_of_window_seed
  : the logarithmic integrand y |-> g(y)/y of a window seed is integrable, because
    the seed lives above the aperture and the reciprocal weight is bounded there,
integrableOn_correction_of_window_seed
  : inverting the ray carries that to the correction integrand y |-> g(1/y)/y,
burnolCoPoissonRightSum_add_of_window
  : so additivity holds for arbitrary integrable window seeds, with no side conditions.
```

The substitution is exactly mathlib's `integrableOn_Ioi_comp_rpow_iff` at `p = -1`: its weight
`|p| x^(p-1)` becomes `x^(-2)`, which is what converts `g(u)/u` into `g(1/x)/x`.  So the co-Poisson
sum is linear in the seed on the whole space of integrable window seeds; what a general seed still
lacks is not linearity but the *identification* of its Mellin transform with `zeta(w) M g(w)`.

The one identification that a general seed still needs rests on the partial-sum asymptotic for zeta
inside the strip --- the statement the Dirichlet series cannot supply, because it does not converge
there.  Its Abel-summation half is now formal:

```text
formal/GaloisForLFunctions/RHTower/ZetaPartialSumStrip.lean

zetaCoeff, sum_zetaCoeff        : the zeta coefficient sequence, normalized at zero,
integrableOn_deriv_cpow_Icc     : the derivative of t |-> t^(-w) is integrable on a window,
sum_cpow_eq_abel
  : sum_{k=1}^{N} k^(-w) = N^(-w) N + w * integral_1^N floor(t) t^(-w-1) dt.
```

Replacing `floor t` by `t - fract t` in that identity splits off the elementary integral, and the
`N^(1-w)` terms cancel *exactly* --- the coefficient is `(1 - w) + w - 1 = 0` --- leaving only a
constant and the fractional-part integral:

```text
sum_cpow_sub_pow_eq
  : sum_{k<=N} k^(-w) - N^(1-w)/(1-w)
      = -w/(1-w) - w * integral_1^N fract(t) t^(-w-1) dt,
tendsto_sum_cpow_sub_pow
  : hence sum_{k<=N} k^(-w) - N^(1-w)/(1-w) -> zeta(w) on the whole punctured
    right half-plane Re w > 0, w /= 1.
```

The hypothesis `Re w < 1` is not needed: the elementary integral `integral_1^N t^(-w)` is proper on a
bounded interval away from the origin, so only `w /= 1` is required there, and the fractional-part
integral converges throughout `Re w > 0`.  The statement therefore covers the strip and the
half-plane of absolute convergence in one form.

The truncated fractional-part integrals converge to the full one, whose value `1/(w-1) - zeta(w)/w`
is the formula proved earlier, and the remaining constants collapse to `zeta(w)`.  This is the
partial-sum asymptotic that the Dirichlet series cannot supply, and it is the missing input to the
general-seed Mellin transform.

Still outside the formal tree: the Mellin transform of the co-Poisson sum for a *general* window
seed (the fractional-part form needs the seed to be of bounded variation, not merely integrable, so
this requires Mellin--Plancherel); a witness at a hypothetical zero (equivalently, the dimension
count for the co-Poisson quotient); and the transfer of the two-sided law to the co-Poisson quotient
vectors `y_{rho,N}` of the parent boundary-transgression theorem.

## Gates

- [x] extended-Sonine constant/tail split proved
- [x] cosine-reflected left-half estimate proved
- [x] exact off-axis annihilator aperture exponent proved
- [x] exact independent-face asymptotics proved
- [x] generic-estimate route to `(GS24)` closed
- [x] targeted literature noncollision audit
- [ ] construct the surviving source anomaly-cancellation comparison
- [x] Lean: completed Mellin evaluator, aperture-head class, ambient bound `(3)`--`(7)`, `(14)`
- [x] Lean: unitary cosine transform `F_+`, extended Sonine space `L_a`, cosine invariance
- [x] Lean: Gamma resolution of the completed power weight and the Gaussian multiplication formula
- [x] Lean: inversion substitution exchanging `w` with `1 - w`
- [x] Lean: Gamma-kernel integrability and the real Gamma resolution (Fubini side conditions)
- [x] Lean: Fubini interchange and the archimedean functional equation `(8)`
- [x] Lean: reflected aperture bound `(3)`,`(4)` with the constant `C_-` for `Re w < 1/2`
- [x] Lean: `L_a` is closed and complete (prerequisite for the Riesz evaluation vector)
- [x] Lean: the Riesz evaluation vector `k_{w,a}` and the boxed form of `(3)`
- [x] Lean: cross-aperture dilation characters and the geometric lower bound `(11)`
- [x] Lean: two-sided aperture-type law `(12)` and the exponent limit `(13)`
- [x] Lean: aperture monotonicity, reducing `(10)` to a single Sonine witness
- [x] Lean: eigen-reduction, halving the witness conditions
- [x] Lean: the eigen-condition is free (symmetrization), leaving one condition
- [x] Lean: inhabitation audit of the co-Poisson source layer (currently vacuous)
- [x] Lean: constant aperture head of the co-Poisson sum (first Sonine condition, unconditional)
- [x] Lean: local finiteness, pointwise summability, and the contributing index window
- [x] Lean: sharp harmonic-versus-logarithm window comparison (the `1/|t|` decay rate)
- [x] Lean: even Poisson summation, the Fourier dilation rule, and the dilated multiplicative identity
- [x] Lean: the co-Poisson intertwining `c * (corrected sum of f at c) = (sum of F f at 1/c)`
- [x] Lean: dictionary between the literal co-Poisson sum and the multiplicative Poisson form
- [x] Lean: uniform finite truncation of the co-Poisson sum on bounded regions
- [x] Lean: measurability and uniform boundedness of the co-Poisson sum
- [x] Lean: the explicit indicator seed — window sum, correction constant `2 log(1/b)`, harmonic form
- [x] Lean: `O(1/|t|)` decay of the indicator co-Poisson value beyond the scale `2/b`
- [x] Lean: square integrability of the indicator co-Poisson sum, and its even carrier vector
- [x] Lean: constancy of its aperture head — every source field except the cosine head condition
- [x] Lean: Burnol's co-Poisson intertwining --- pairing form, line form, and `L^2` operator form
- [x] Lean: size data for the reciprocal indicator seed (exact cardinality formula, `O(1/t)`, `L^2`, reality)
- [x] Lean: constancy of the aperture head of the **cosine transform** of the indicator co-Poisson vector
- [x] Lean: an inhabitant of `BurnolCoPoissonSource b` for every aperture `0 < b <= 1`
- [x] Lean: the inhabitant in closed form --- the fractional-part kernel `(fract(t b) - fract(t/b))/t`
- [x] Lean: Abel summation and the fractional-part formula for zeta on `Re s > 0`
- [x] Lean: the Mellin transform of the co-Poisson value, `(b^(-w) - b^w) zeta(w)/w` on the strip
- [x] Lean: nonvanishing of the completed Mellin evaluation on that inhabitant, off the zero set of zeta
- [x] Lean: the aperture-type exponent law `(13)`, unconditional off the zero set of zeta
- [x] Lean: the same dichotomy below the critical line, via the reflected Riesz vector
- [x] Lean: the dichotomy at a zero --- the explicit witness is exactly the nonvanishing of zeta,
      and at a zero the evaluator is orthogonal to it
- [x] Lean: the two-parameter sub-window family --- fractional-part form, Mellin transform, and
      annihilation at every zeta zero
- [x] Lean: analytic size data for the sub-window family (bounds, `L^2`, measurability, reality)
- [x] Lean: the general window indicator seed --- co-Poisson pair relation, correction constant,
      harmonic form and value
- [x] Lean: decay, local bound, profile, `L^2` and reality for the general window indicator
- [x] Lean: sub-window sources, Sonine vectors, Mellin evaluation and the two-parameter witness family
- [x] Lean: linearity of the co-Poisson sum in the seed, and annihilation at a zero on the span
- [x] Lean: integrability of the correction integrand for an arbitrary window seed (ray inversion),
      hence unconditional additivity
- [x] Lean: the partial-sum asymptotic for zeta on the punctured right half-plane (Abel summation
      plus the fractional-part integral)
- [x] Lean: **the Mellin transform of the co-Poisson sum for a general window seed** ---
      `M(P_g)(w) = zeta(w) M(g)(w)` on the strip, for every integrable seed supported in `[b,1/b]`
      whose co-Poisson sum is Mellin integrable (`integral_Ioi_burnolCoPoisson_cpow`), and its
      source form `soninMellinEvaluation_burnolCoPoissonSource`, where the integrability hypothesis
      is discharged for free by `integrableOn_extendedSonin_mul_mellinKernel`
- [x] Lean: **the transfer of `(12)`,`(13)` to the whole source space** --- at a zeta zero the Riesz
      evaluator annihilates *every* co-Poisson source vector
      (`inner_burnolExtendedSoninEvaluationVector_source_eq_zero`), and off the zero set it detects
      every source whose seed has nonvanishing Mellin transform
      (`soninMellinEvaluation_burnolCoPoissonSource_ne_zero`)
- [x] Lean: a witness at a hypothetical zero --- the evaluation vector is nonzero at every point of
      the open right half strip, including at a zeta zero
      (`burnolExtendedSoninEvaluationVector_ne_zero`), so `(13)` holds there without any premise
- [x] Lean: the explicit co-Poisson subspace at a fixed aperture, and the evaluator's orthogonality
      to it at a zeta zero (the explicit part of `y_{rho,N} = k_{rho,a_N}`)
- [x] Lean: nontriviality --- the sub-window vectors are nonzero, so that subspace is not `bot`,
      and distinct windows give distinct vectors
- [x] Lean: identification of the co-Poisson *quotient* vectors `y_{rho,N}` themselves --- on an
      annihilator fibre the quotient kernel is the ambient Sonine kernel and is nonzero
      (`burnolCoPoissonQuotientEvaluationVector_ne_zero_of_annihilator`)
- [x] Lean: zeta has no zero on the real segment `(0,1)`, from the fractional-part formula
- [x] Lean: linear independence of the sub-window family (Mellin evaluator, identity theorem,
      Dedekind independence of characters)
- [x] Lean: the explicit co-Poisson subspace and Burnol's own source space are **infinite
      dimensional** at every aperture `0 < A < 1`, via an explicit ladder of window ends
- [x] Lean: the truncated Mellin identity `integral_Ioc 0 T` against the finite kernel `kappa_T`,
      and the exact cancellation `u^(-w) (T/u)^(1-w) = u^(-1) T^(1-w)` behind it
- [x] Lean: the partial-sum error `zetaStripError` is bounded, and the floor error of a complex
      power is `O(N^(Re s - 1))`
- [x] Lean: the closed span of **all** co-Poisson source vectors at a fixed aperture, its
      annihilation by the evaluator at a zeta zero, and the sharp characterization
      `evaluator orthogonal to the span  <->  zeta(w) = 0` for `0 < b < 1` on the upper half strip
- [x] Lean: that span is infinite dimensional (the sub-window ladder sits inside it)
