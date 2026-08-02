# Burnol--Sonin off-axis aperture-type rigidity

- **ID:** `burnol-sonin-off-axis-aperture-type-rigidity`
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / HOSTILE ROUTE AUDIT
- **Scientific status:** `[CORPUS-NEW SYNTHESIS] [PRELIMINARY EXTERNAL NONCOLLISION] [NOT RH]`
- **Parents:**
  - `gamma-copoisson-sonin-independent-quadrant-boundary-transgression.md`;
  - `../not_new_scientific_knowledge/burnol-copoisson-quotient-bilateral-order-rh-law.md`;
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

Combining the two gives the dilated even Poisson identity

```text
f(0) + 2 sum_{n>=1} f(n x) = x^(-1) [ (F f)(0) + 2 sum_{k>=1} (F f)(k / x) ],
```

which is the co-Poisson intertwining `F(E phi) = E(F phi)` after collecting the correction terms.
The remaining cosine-side condition is therefore bookkeeping on top of two proved identities rather
than a fresh analytic theorem.

Still outside the formal tree: an inhabitant of `BurnolCoPoissonSource` --- equivalently the single
symmetrized witness --- and the transfer of the two-sided law to the co-Poisson quotient vectors
`y_{rho,N}` of the parent boundary-transgression theorem.

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
- [x] Lean: even Poisson summation and the Fourier dilation rule (both inputs to the intertwining)
- [ ] Lean: an inhabitant of `BurnolCoPoissonSource`, i.e. one even `u` with `u + F u` constant on an aperture head and nonvanishing evaluation
- [ ] Lean: transfer of `(12)`,`(13)` to the co-Poisson quotient vectors `y_{rho,N}`

