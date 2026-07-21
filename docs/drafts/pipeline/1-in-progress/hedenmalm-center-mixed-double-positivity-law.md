# Hedenmalm center-mixed double-positivity law

- **ID:** `hedenmalm-center-mixed-double-positivity-law`
- **Stage:** 1-in-progress
- **Type:** THEOREM / SOURCE-SIDE HILBERT--POLYA ORIENTATION COORDINATE
- **Scientific status:** `[PROVED ON PAPER] [LEAN PARTIAL] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** `theta-wigner-eisenstein-orientation-current.md`

## Statement

Let `k : R -> R` be even, strictly positive, and rapidly decreasing against every exponential of
rate below `1/2`, and define its Wigner distribution by

```text
W_k(y,b)=integral_R k(y+t)k(y-t)exp(2 i b t)dt.
```

For `0<a<1/2`, define the center-mixed density

```text
M_(k,a)(t)
 =integral_(0,infinity)
    r sinh(a r) k(r/2+t)k(r/2-t)dr.                       (1)
```

Then `M_(k,a)` is strictly positive, even, continuous, and integrable.  Its Fourier transform is
the radial Wigner current:

```text
integral_R M_(k,a)(t) exp(2 i b t)dt
 =integral_(0,infinity) r sinh(a r)W_k(r/2,b)dr.          (2)
```

For Hedenmalm's normalized theta source

```text
k(x)=2 VarTheta_00(i exp(2x)),
X(w)=integral_R k(x)exp(w x)dx=xi(1/2+w),
```

the following are equivalent:

```text
RH;

for every 0<a<1/2 and b in R,
  Fourier(M_(k,a))(2b)>=0;

for every 0<a<1/2,
  M_(k,a) is positive definite on R.                     (3)
```

Thus the source-side orientation carrier is **doubly positive**: `M_(k,a)` is already pointwise
positive unconditionally, while RH is exactly its second positivity, positive definiteness.

## Proof of the transform identity

Absolute convergence follows from the exponential decay of `k` and `a<1/2`.  Fubini gives

```text
integral_R M_(k,a)(t) exp(2 i b t)dt
 =integral_(0,infinity) integral_R
    r sinh(a r) k(r/2+t)k(r/2-t)exp(2 i b t)dt dr.
```

The inner integral is `r sinh(a r)W_k(r/2,b)`, which proves `(2)`.

The two source factors in `(1)` are exchanged by `t -> -t`, so `M_(k,a)` is even.  Every other
factor is positive for `r>0`, and the theta source is strictly positive, so `M_(k,a)(t)>0`.
Continuity follows by dominated convergence.  Integrability follows either by the same exponential
majorant or by Tonelli after integrating the positive kernel in `t`.

For the theta source, the already proved Wigner--Bezoutian identity and Hermitian orientation gate
give the equivalence of RH with the second line of `(3)`.  Since `M_(k,a)` is continuous and
integrable, the classical Bochner theorem identifies nonnegativity of its Fourier transform with
positive definiteness, proving the third equivalence.

## Unconditional order-two positive-definiteness rung

The source-specific score--variance theorem in
`../2-fully-proven/needs-audit/theta-cusp-kernel-log-concavity-score-variance-repair.md` proves
that `log k` is strictly concave on `R`.  Consequently

```text
k(u+t)k(u-t) <= k(u)^2,
0 <= M_(k,a)(t) <= M_(k,a)(0).
```

Hence every two-node Bochner matrix

```text
[[M_(k,a)(0), M_(k,a)(x-y)],
 [M_(k,a)(x-y), M_(k,a)(0)]]
```

is positive semidefinite unconditionally.  This exact rung is formalized by
`thetaCuspCenterMixedTwoNodeMatrix_posSemidef` and its determinant form
`thetaCuspCenterMixedTwoNode_det_nonneg`.  It closes order two only.  The open research wall in
`(3)` is compatibility of all finite node sets, equivalently the nonnegative Fourier transform;
no finite-order extrapolation is valid.

## Unconditional radial and partial order-three rung

The paper-proof and formalization in
`../3-formalized/needs-audit/hedenmalm-center-mixed-radial-three-point-chamber.md` strengthen
the source endpoint without assuming any Fourier sign.  The actual reflected product

```text
t |-> k(u+t)k(u-t)
```

is strictly decreasing for `t>=0`; consequently `M_(k,a)` is nonincreasing on the positive
half-line and is strictly below its center for every positive displacement.

For ordered nodes `0,x,x+y`, put

```text
d=M_(k,a)(0), p=M_(k,a)(x), q=M_(k,a)(y), r=M_(k,a)(x+y).
```

The exact three-node determinant is

```text
D=d^3+2pqr-d(p^2+q^2+r^2).
```

Whenever `p^2+q^2<=d^2`, radial ordering proves `D>=0`, so the actual three-node Bochner matrix
is positive semidefinite.  The successor theorem
`exists_thetaCuspCenterMixedThreePointMatrix_posSemidef_of_large_gap` also closes every
near-center packet with at least one sufficiently large adjacent gap.  Consequently
`exists_thetaCuspCenterMixedThreePointMatrix_compactCore_iff` reduces the complete order-three
problem to a bounded two-gap core at each aperture.  It does not prove that compact core and does
not extrapolate from order three to all finite orders.

## Pure-state tangent interpretation

Put

```text
f_a(x)=exp(a x)k(x),
rho_a=|f_a><f_a|.
```

The full-center form of `(1)` is

```text
M_(k,a)(t)=partial_a R_(f_a)(2t),                         (4)

R_(f_a)(q)=integral_R f_a(x)f_a(x-q)dx.
```

Equivalently, the Fourier transform in `(2)` is the momentum diagonal of the rank-two tangent

```text
partial_a rho_a
 =|x f_a><f_a|+|f_a><x f_a|.                             (5)
```

Unless the source is concentrated at one point, `(5)` is indefinite on the span of `f_a` and
`x f_a`: it has one positive and one negative direction.  Therefore `(3)` does not claim ambient
operator positivity.  It says that the distinguished momentum diagonal of this universal Krein
tangent is nonnegative throughout the critical aperture.

### Exact rank-two tangent inertia `[PAPER-PROVED] [BRIDGE]`

Let `H` be a complex Hilbert space, let `u,v in H`, and put

```text
T_(u,v)=|v><u|+|u><v|,
Delta(u,v)=||u||^2||v||^2-|<u,v>|^2.
```

Write `a=<u,u>`, `b=<v,v>`, `c=<u,v>`, and `c*=<v,u>`.  The Hermitian matrix of `T_(u,v)` on the
ordered pair `(u,v)` is

```text
G_T = [[a(c+c*),       ab+c^2],
       [ab+(c*)^2,     b(c+c*)]].
```

Direct expansion gives the exact value relation

```text
det G_T
 = ab(c+c*)^2-(ab+c^2)(ab+(c*)^2)
 = -(ab-cc*)^2
 = -Delta(u,v)^2.                                      (6)
```

The ordinary two-vector Gram theorem gives `Delta(u,v)>=0`, with strict inequality exactly when
`u,v` are complex-linearly independent.  Under that independence, `(6)` is strictly negative.
The same determinant belongs to `-G_T`, since the matrix has size two.  Hence neither `G_T` nor
`-G_T` is positive semidefinite: the restriction has both a positive and a negative direction.
Because `(6)` is nonzero, its rank is two, so the inertia is exactly `(1,1)`.

For the formal right-line Hedenmalm path take `u=f_a` and `v=-x f_a` in `L^2(R)`.  The theta
source is strictly positive, so these vectors are independent: a relation `alpha u+beta v=0`
lifts through the injective Schwartz-to-`L^2` map; evaluation at `x=1` and `x=2` gives
`alpha-beta=0` and `alpha-2 beta=0`, hence both coefficients vanish.  Thus the actual tangent
`(5)` has exact inertia `(1,1)` for every `|a|<1` (up to the harmless aperture sign convention).

This is not new quantum geometry.  Pure-state projector tangents and their projective Gram/Fisher
energy are standard in the Provost--Vallee and Braunstein--Caves framework.  The contribution here
is the exact reusable determinant interface `(6)` and its source-specific discharge; its scientific
label is `[BRIDGE]`, not new knowledge.

This is the continuous form of the already formalized two-atom Mellin signature.  It also explains
why an ambient Hecke square, a Loewner-monotone density matrix, or a positive Gram factorization on
arbitrary theta coefficients cannot prove orientation.

## Why this survives the previous attacks

1. **Hudson rigidity does not apply.**  Hudson forbids pointwise positivity of every pure-state
   Wigner slice `W_k(y,b)` unless `k` is Gaussian.  The density `(1)` mixes the center variable
   before the Fourier sign is read and is not a pure-state Wigner distribution.
2. **The ambient Krein obstruction is retained.**  Formula `(5)` is indefinite, in agreement with
   the exact negative two-atom determinant.  Only its source-selected momentum diagonal is tested.
3. **No divisor has been inserted.**  The density `(1)` is constructed directly from the theta
   source and the critical aperture parameter `a`.
4. **The remaining theorem is explicit.**  A proof must establish positive definiteness of the
   concrete positive density `(1)`, not positivity of a reconstructed zero measure or an abstract
   Hilbert space.

## Positive carrier obligation

Any successful Hedenmalm--Hilbert--Polya construction in this coordinate must provide one of:

```text
a source factorization of M_(k,a) as a positive mixture of autocorrelations;

a source-preserving operation that places M_(k,a) in the positive-definite cone;

or a direct finite-matrix proof that
  sum_(i,j) c_i conjugate(c_j) M_(k,a)(t_i-t_j)>=0
for every finite packet, uniformly for 0<a<1/2.
```

Pointwise positivity of `M_(k,a)` is only the first half of this obligation.

## Formalization status and open proof obligations

- [x] formalize the actual theta-source center-mixed density and its absolute integrability;
- [x] formalize the center-mixing Fubini identity with the exact Fourier phase normalization;
- [x] formalize strict positivity, evenness, continuity, and integrability of `M_(k,a)`;
- [x] formalize `M_(k,a)(x/2)=partial_a R_(f_a)(x)`, extend integrability and continuity to
      `|a|<1`, and combine strict spatial positivity with the finite differential-frame exclusion;
- [x] formalize the Fourier-sign/RH equivalence in `(3)` without introducing a positivity premise;
- [x] formalize strict source log-concavity and the resulting two-node Bochner positivity rung;
- [x] formalize radial monotonicity, strict center drop, the far-separated order-three chamber,
      and the exact near-center three-point determinant wall;
- [x] formalize the rank-two inertia statement `(5)`;
- [ ] audit the exact center-mixed criterion against ambiguity-function, Wigner, and
      positive-definite-function literature;
- [ ] find or refute a source factorization of `M_(k,a)` inside the positive-definite cone.

The completed unconditional analytic layer is in
`formal/GaloisForLFunctions/RHTower/ThetaWignerCenterMix.lean`.  It includes an explicit
two-variable exponential majorant, so absolute integrability is derived for the actual theta
source rather than exposed as a theorem hypothesis.  This does not formalize, assume, or imply the
positive-definiteness assertion in `(3)`.  The exact module build succeeds, and the Fubini,
strict-positivity, integrability, and continuity theorems print only the standard foundations
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` occurs.

The exact autocorrelation-path identification and full-aperture regularity are in
`formal/GaloisForLFunctions/RHTower/HedenmalmAutocorrelationPath.lean`; their separate formalized
card is `../3-formalized/not_new_scientific_knowledge/hedenmalm-autocorrelation-path-boundary.md`.

The general value-reflection law and its unconditional theta-source discharge are in
`formal/GaloisForLFunctions/HTGeometry/PureStateProjectorTangentInertia.lean` and
`formal/GaloisForLFunctions/RHTower/HedenmalmRankTwoTangentInertia.lean`.  They prove
`det G_T = -Delta(u,v)^2`, identify positive projective Gram energy with pair independence, and
establish that the actual source compression is Hermitian, nonsingular, and neither positive nor
negative semidefinite for every `|a|<1`.  This closes the ambient rank-two inertia obligation but
does not prove the momentum-diagonal positivity equivalent to RH.

The exact source-to-orientation boundary is in
`formal/GaloisForLFunctions/RHTower/HedenmalmCenterMixedOrientationBoundary.lean`.  It proves that
the actual and pointed-moment Bezoutian diagonals equal the theta-orbit Krein current divided by
`2a`, and that nonnegativity of the corresponding center-mixed Fourier current throughout the
critical aperture is equivalent to RH.  It does not prove that current nonnegative.

The formal theorem surface is:

```text
integral_thetaWignerCenterMixedDensity_mul_phase_thetaCusp
thetaCuspCenterMixedDensity_pos
integrable_thetaCuspCenterMixedDensity
continuous_thetaCuspCenterMixedDensity.
thetaXiHankelOrbitNonnegative_iff_riemannHypothesis
thetaCuspCenterMixedFourierNonnegative_iff_riemannHypothesis
```

## Parent-theory boundary

The sign in `(3)` is the source-coordinate form of horizontal monotonicity of the modulus of the
Riemann xi function.  Sondow and Dumitrescu proved that horizontal modulus monotonicity in the
zero-free right half-plane is equivalent to RH.  Consequently the RH equivalence itself is a
`[BRIDGE]`, not new scientific knowledge.  Potential novelty can attach only to the explicit
center-mixed positive-density representation or to a genuinely new source factorization proving
its positive definiteness.  No such factorization has yet been proved.

Primary parent: J. Sondow and C. Dumitrescu, *A monotonicity property of Riemann's xi function and
a reformulation of the Riemann Hypothesis*, Period. Math. Hungar. 60 (2010), 37--40,
doi:10.1007/s10998-010-1037-3.

## Publication boundary

The transform identity and criterion are not yet sufficient for a publication-level RH result.
They become significant only if the center-mixed density admits a new source-side
positive-definiteness mechanism, or if the failure of every natural factorization can be classified
by a theorem stronger than the existing two-point Krein obstruction.

## 2026-07-21 complete-tower producer audit

The all-order distinction is now explicit.

1. The canonical strip-boundary aperture is closed unconditionally.  For every `tau>0`,
   `HedenmalmExteriorGaussianHankel.lean` proves

   ```text
   J_(1/2)(b)>=0 for every real b
   ```

   and hence the complete Gaussian Hankel cone at `a=1/2`.  This uses every polynomial degree;
   it is not a finite-section result.  The same proof covers every exterior aperture
   `1/2<=a<1`.

2. This boundary law does not perturb automatically into a fixed interior aperture.  The current
   has no uniform positive margin at frequency infinity, and the exact aperture--width theorem
   shows that a cofinal inward propagation to `a downarrow 0` is RH itself.

3. `HTGeometry/ReflectionPositiveHankel.lean` is an all-order consumer, not a producer.  It proves
   that an independently constructed Gram orbit with entries `m_(i+j)` makes every polynomial
   square a Hilbert norm square.  The canonical prime--archimedean Gram orbit currently available
   in `PrimeArchCanonicalReflectionPositiveEquivalence.lean` exists exactly when RH holds.
   Importing that orbit into the Hedenmalm current would therefore be circular.

4. The positive spectral measure in `ThetaCuspLikelihoodSpectralMeasure.lean` belongs to the
   nonlinear higher-to-first likelihood coordinate

   ```text
   B(x)=pi*exp(2*x)-3/2.
   ```

   Its strict all-order tilted Hankel hierarchy does not give a translation Gram factorization of
   the center-mixed density `M_(k,a)(t)`.  The two moment problems have different semigroup
   coordinates; identifying them without a new intertwiner would be category substitution.

5. The independent four-unit leakage route would imply every interior Hedenmalm tower by first
   proving RH, but its source-first graph incidence remains open.  Toeplitz contractivity and
   Osterwalder--Schrader reflection positivity alone do not bound the boundary curvature corner;
   the one-layer Cauchy mode gives an arbitrarily large corner while preserving contractivity.

The surviving proof target is consequently not another finite Hankel minor or another abstract
Gram theorem.  It is one of the following equivalent-strength source constructions:

```text
(a) a nonlocal theta-source factorization of M_(k,a) inside the positive-definite cone,
(b) a source-defined reflected Gram orbit for every translation packet of M_(k,a), or
(c) an independently normalized all-prime--Gamma continuation that transports the four-unit
    contact budget to the Xi anti-causal profile without increasing Hilbert energy.
```

No item `(a)`--`(c)` is proved here.  Until one is proved, the only complete unconditional
Gaussian tower is the sharp boundary/exterior family, and the interior all-order sign remains the
RH-bearing theorem.

## 2026-07-21 hostile producer audit: generic shape theory is exhausted

The remaining all-order sign cannot follow from the source properties used by the two- and
three-point arguments alone.  There is an exact counterfamily.

For parameters

```text
0 < beta^2 <= 2,
0 < epsilon*exp(beta^2/4) < 1,
```

put

```text
k_(epsilon,beta)(x)=exp(-x^2)*(1+epsilon*cosh(beta*x)).   (26)
```

Then `k_(epsilon,beta)` is even, strictly positive, Schwartz, and strictly log-concave.  Indeed

```text
(log k)''
 =-2+epsilon*beta^2*(cosh(beta*x)+epsilon)
       /(1+epsilon*cosh(beta*x))^2,
```

and

```text
epsilon*(cosh(beta*x)+epsilon)
  < (1+epsilon*cosh(beta*x))^2.
```

Hence `(log k)''<-2+beta^2<=0` everywhere.  Its bilateral Fourier--Laplace transform is explicit:

```text
X_(epsilon,beta)(w)
 =sqrt(pi)*exp(w^2/4)
    *(1+A*cosh(beta*w/2)),
A=epsilon*exp(beta^2/4) in (0,1).                        (27)
```

Writing `u=arcosh(1/A)>0`, the last factor vanishes at

```text
w=(2/beta)*(+-u+(2m+1)*pi*i),   m in Z.                 (28)
```

Thus the transform has two positive-density off-axis vertical zero lattices.  If

```text
J_a(b)=partial_a |X_(epsilon,beta)(a+i*b)|^2,
```

then at any zero `(a_0,b_0)` from `(28)`, the nonnegative real-analytic function
`a |-> |X(a+i*b_0)|^2` has an isolated zero at `a_0>0`; consequently its derivative is strictly
negative immediately to the left of `a_0`.  The associated center-mixed density is therefore not
positive definite at those apertures.

This proves the positive carrier obligation:

> A proof of the theta-source sign must use a property which distinguishes the exact
> Riemann--Jacobi modular/prime completion from every even positive strictly log-concave Schwartz
> source.  Shape inequalities at any fixed differential order, including strict log-concavity,
> radial decrease, and finitely many reflected Turan signs, cannot be the final producer.

The theorem is an exact symbolic countermodel; it uses no numerical evaluation and no Xi zero
data.  It has not yet been promoted as a novelty claim.

## Critical Poisson--resolvent aperture law `[PAPER ALGEBRA COMPLETE; SIGN OPEN]`

Let

```text
f_a(b)=|X(a+i*b)|^2,
P_r(x)=r/(pi*(x^2+r^2)),
R=2*a+r,
```

with `a,r>0`, and define the renormalized critical-mass response

```text
Rcal_(r,c)(a)
  =(P_r*f_a)(c)-(r/R)*(P_R*f_a)(c).                     (29)
```

Equivalently,

```text
Rcal_(r,c)(a)
 =r/pi*integral_R
    (1/((b-c)^2+r^2)-1/((b-c)^2+R^2))*f_a(b) db.        (30)
```

The kernel in `(30)` is strictly positive, so `Rcal_(r,c)(a)>0` whenever `X` is not identically
zero.  If `J_a=partial_a f_a`, differentiation gives the exact law

```text
partial_a Rcal_(r,c)(a)
 =(P_r-(r/R)*P_R)*J_a(c)
  +4*r*R/pi*integral_R
      f_a(b)/((b-c)^2+R^2)^2 db.                        (31)
```

The last term is strictly positive.  Under the theta-source decay already available in Lean,
Poisson approximation and dominated convergence give

```text
Rcal_(r,c)(a) -> f_a(c),
partial_a Rcal_(r,c)(a) -> J_a(c)       as r downarrow 0. (32)
```

Consequently a cofinal monotonicity theorem

```text
partial_a Rcal_(r,c)(a)>=0 for all sufficiently small r
```

would prove `J_a(c)>=0`; conversely `J_a>=0` makes every term on the right of `(31)` nonnegative.
Thus the critical resolvent supplies an exact positive carrier and a vanishing positive correction,
but positivity of `Rcal` itself does not imply its aperture monotonicity.  The missing assertion is
again the orientation sign, not a resolvent normalization.

This audit retires two tempting but circular moves:

1. positivity of the critical-mass response `(30)` without control of its aperture derivative;
2. a generic heat/Poisson maximum principle which would also apply to the explicit counterfamily
   `(26)`--`(28)`.

The surviving target is source-specific: prove the derivative sign in `(31)` from the modular
Eisenstein boundary/scattering data, or construct a different theta arithmetic norm-square whose
aperture derivative is `(31)` including its boundary channel.

## Two-ended causal resolvent factorization `[PAPER-PROVED; UNCONDITIONAL; NOT RH]`

The critical Poisson response `(29)` has a sharper source factorization.  Fix the Fourier
convention

```text
hat(g)(xi)=integral_R g(x) exp(-i xi x)dx,
||g||_2^2=(1/(2*pi)) integral_R |hat(g)(xi)|^2 dxi.
```

For `s>0` define the causal and anti-causal one-sided resolvents

```text
(T_s g)(u)=integral_u^infinity exp(-s(x-u))g(x)dx,
(S_s g)(u)=integral_(-infinity)^u exp(-s(u-x))g(x)dx,
```

and put

```text
g_(a,c)(x)=exp((a+i*c)x)k(x),
R=2*a+r.
```

Then Plancherel and the exact factorization

```text
exp(-s|x-y|)
 =2*s*integral_(-infinity)^min(x,y)
      exp(-s(x-u))exp(-s(y-u))du
```

give

```text
(P_s*f_a)(c)=2*s*||T_s g_(a,c)||_2^2.                    (33)
```

Consequently the critical response is exactly

```text
Rcal_(r,c)(a)
 =2*r*(||T_r g_(a,c)||_2^2-||T_R g_(a,c)||_2^2).         (34)
```

If `D` denotes the real Fourier multiplier `xi`, then

```text
||T_r g||_2^2-||T_R g||_2^2
 =(1/(2*pi))*integral_R |hat(g)(xi)|^2
   *(R^2-r^2)/((r^2+xi^2)(R^2+xi^2)) dxi,
```

so `(34)` is the positive norm square

```text
Rcal_(r,c)(a)
 =2*r*(R^2-r^2)
   ||(r^2+D^2)^(-1/2)(R^2+D^2)^(-1/2)g_(a,c)||_2^2.     (35)
```

This proves the strict positivity in `(30)` by a source Hilbert norm, rather than by pointwise
inspection of the Lorentz kernel.

Evenness and reality of `k` join the two ends exactly:

```text
T_R g_(a,c)(u)=exp(2*a*u)*conj(S_r g_(a,c)(-u)).          (36)
```

Thus the apparently unrelated resolvent radii `r` and `r+2a` are the same one-sided damping rate
viewed from the two reflected source ends; the gap `2a` is forced by the critical reflection.

There is also an exact boundary-primitive form.  With the existing Hedenmalm primitive

```text
B(w,x)=exp(i*w*x)*integral_(-infinity)^x exp(-i*w*y)k(y)dy
```

and

```text
w_-=c+i(r-a),
w_+=c+i(r+a),
```

one has

```text
T_r g_(a,c)(u)=exp((a+i*c)u)B(w_-,-u),
T_R g_(a,c)(u)=exp((a+i*c)u)B(w_+,-u),
```

and hence

```text
Rcal_(r,c)(a)
 =2*r*integral_R exp(-2*a*x)
    (|B(w_-,x)|^2-|B(w_+,x)|^2)dx.                      (37)
```

Formula `(37)` is a weighted vertical contraction law for the actual one-sided theta boundary
problem.  It is stronger than positivity of either a finite determinant or a finite Hankel
section: it is an exact all-frequency source identity.

### Aperture derivative and the unique orientation term

Write

```text
A_s=(s^2+D^2)^(-1).
```

Since `partial_a g_(a,c)=x*g_(a,c)` and `partial_a R=2`, differentiating `(34)` gives

```text
partial_a Rcal_(r,c)(a)
 =4*r*Re <x*g_(a,c),(A_r-A_R)g_(a,c)>
  +8*r*R*<g_(a,c),A_R^2 g_(a,c)>.                       (38)
```

The second term is a positive resolvent square.  The first term is the sole unresolved
orientation channel.  In Fourier coordinates it is a weighted phase current:

```text
Re <x*g,(A_r-A_R)g>
 =(1/(2*pi))*integral_R
   (1/(r^2+xi^2)-1/(R^2+xi^2))
   *Im(conj(partial_xi hat(g)(xi))*hat(g)(xi)) dxi.       (39)
```

Thus the missing theorem is not positivity of the resolvent gap `(35)`.  It is domination of the
source phase current `(39)` by the positive square in `(38)`, uniformly as `r downarrow 0`.
Together with `(32)`, this yields the exact cofinal statement

```text
J_a(c)>=0
 iff lim_(r downarrow 0) partial_a Rcal_(r,c)(a)>=0,
```

and a sufficient source theorem is

```text
Re <x*g_(a,c),(A_r-A_R)g_(a,c)>
  >= -2*R*<g_(a,c),A_R^2 g_(a,c)>
for every r>0, 0<a<1/2, and c in R.                      (40)
```

The explicit log-concave counterfamily `(26)`--`(28)` proves that `(40)` is not a generic causal
resolvent inequality.  Any proof must use a theta-specific arithmetic or modular phase relation.
The newly formalized theta-tail Haar/Jacobi decompositions do not supply it: their exact cofinal
conservation theorem transfers every decaying top-row current into a surviving translation
current and returns the original raw orientation.  Importing the favorable Jacobi fourth-power
packet while dropping that survivor would therefore be circular.

### Positive carrier law

The two-ended factorization turns the no-go into a precise positive obligation:

> A successful Hedenmalm construction must be a passive two-ended scattering law.  It must retain
> the causal/anti-causal reflection `(36)` and prove the phase-current domination `(40)` at every
> resolution, or at a cofinal sequence of resolutions tending to zero.  A positive resolvent norm,
> a finite Hankel packet, or a favorable interior Jacobi square without its boundary survivor does
> not meet this obligation.

No claim in this section proves `(40)` for the theta source.  The complete interior Gaussian
Hankel tower, equivalently global nonnegativity of `J_a`, remains open.

## Modular seam dominance over the first theta atom `[PAPER-PROVED; LEAN OPEN; NOT RH]`

The positive-half-line domination of the full theta source by its first atom cannot be transported
to the high-frequency orientation current.  In fact the first atom has the wrong eventual sign.

Let

```text
h(x)=thetaCuspSourceTerm(x,1),                 x>=0,
k_1(x)=h(|x|),
X_1(w)=integral_R k_1(x) exp(w*x) dx,
J_(1,a)(b)=partial_a |X_1(a+i*b)|^2.
```

The exact endpoint theorem already proved for the first atom gives

```text
h'(0)=ell_1*h(0)>0,
ell_1=9/2-2*pi+6/(2*pi-3).                    (41)
```

Although `k_1` is even and positive, it has a nonzero cusp slope at the modular seam.  Repeated
integration by parts on the positive half-line gives, for fixed real `a`,

```text
X_1(w)=2*h'(0)/w^2+2*h'''(0)/w^4+2*h^(5)(0)/w^6+o(|w|^(-6)),
X_1'(w)=-4*h'(0)/w^3-8*h'''(0)/w^5-12*h^(5)(0)/w^7
          +o(|w|^(-7)),                       (42)
```

as `w=a+i*b` and `|b|->infinity`.  All even endpoint jets cancel between the two half-line
channels; only odd right jets survive.  Since

```text
Re(1/(w^3*conj(w)^2))=a/(a^2+b^2)^3,
```

the leading current is exact:

```text
lim_(|b|->infinity) ((a^2+b^2)^3/a)*J_(1,a)(b)
  =-16*h'(0)^2 < 0                         for every fixed a>0.   (43)
```

Thus the reflected first theta atom fails every interior complete Gaussian Hankel tower: its
current is strictly negative at all sufficiently large frequencies.

For the completed theta source `k`, by contrast, every exponential tilt `exp(a*x)k(x)`, `|a|<1`,
is Schwartz.  Its bilateral transform and its aperture derivative therefore decay faster than
every inverse power of `|b|`.  If

```text
J_a(b)=partial_a |X(a+i*b)|^2,
J_(corr,a)=J_a-J_(1,a),
```

then `(43)` forces the complementary exact law

```text
lim_(|b|->infinity) ((a^2+b^2)^3/a)*J_(corr,a)(b)
  =+16*h'(0)^2.                                (44)
```

The higher-atom sector is small in positive-half-line mass but is leading-order decisive in the
orientation topology: it cancels and reverses the algebraic cusp current of the dominant first
atom.  After this cancellation the full Xi current is beyond all algebraic endpoint orders.

This converts the failed first-atom comparison into a positive carrier theorem:

> Every successful source proof of the complete Hedenmalm tower must retain the full modular seam
> completion.  A tail estimate in mass, moments, or any fixed boundary-jet norm cannot be the
> producer.  The proof must control the nonperturbative remainder left after the exact all-order
> cancellation between the first atom and the higher theta tail.

The theorem explains why the likelihood spectral measure and the first-atom domination bounds do
not settle `(40)`: those results control a positive amplitude topology, whereas the RH-bearing
current is carried by the modular seam in a strictly stronger oscillatory topology.  Formulae
`(43)`--`(44)` still do not determine the sign of that beyond-all-orders remainder, so they do not
prove RH.

## 2026-07-21 strict positive-matrix mixing connector

**[REDISCOVERED] [BRIDGE] [LEAN-PROVED].**  The order-four center-mixture closure previously
contained a source-specific proof of a general fact: strict positivity of an integrable real
`2 x 2` Hankel field survives integration when the integrated first diagonal mass is positive.
The exact theorem now lives in
`formal/GaloisForLFunctions/HilbertMetric/FourthCurvatureMixture.lean`:

```text
integral_twoByTwo_det_pos
```

For integrable fields `p0,p2,p4`, assume

```text
0 < integral p0,
almost everywhere: 0 < p0 and 0 < p0*p4-p2^2.
```

Put `A=integral p0`, `B=integral p2`, and use the nonzero vector `(-B,A)`.  Pointwise Sylvester
positivity makes

```text
Q = p0*B^2 - 2*p2*A*B + p4*A^2
```

strictly positive almost everywhere.  Its integral is exactly

```text
A * (A*integral(p4)-B^2),
```

so positivity of `A` gives the strict mixed determinant.  No uniform lower determinant gap or
finite-measure normalization is needed.  This is elementary positive-cone/Sylvester theory; broad
matrix-valued positive-definite integration is classical parent theory, so no novelty claim is
made.

`RHTower/HedenmalmCenterMixedFourthJetCuspClosure.lean` now uses this theorem directly.  Its proof
only discharges source facts already present in the corpus:

- integrability of the weighted zeroth, second, and fourth reflection jets;
- positive mixed zeroth mass;
- pointwise strict fourth Hankel positivity from the full theta reflection theorem.

The pointwise determinant factors as the square of `r*sinh(a*r)` times the source determinant.
The prior bespoke quadratic-form integration and explicit positive-measure interval argument were
removed.  The unconditional capstones and RH status are unchanged: this is a theorem-graph
consolidation that exposes the exact general producer consumed by the theta closure.

Focused verification passed:

```text
lake env lean GaloisForLFunctions/HilbertMetric/FourthCurvatureMixture.lean
lake build GaloisForLFunctions.HilbertMetric.FourthCurvatureMixture
  8476/8476
lake env lean GaloisForLFunctions/RHTower/HedenmalmCenterMixedFourthJetCuspClosure.lean
lake build GaloisForLFunctions.RHTower.HedenmalmCenterMixedFourthJetCuspClosure
  8822/8822
```

The generic quadratic lemma, strict mixture theorem, theta fourth-Hankel theorem, and coalesced-cusp
capstone depend on exactly `propext`, `Classical.choice`, and `Quot.sound`.
