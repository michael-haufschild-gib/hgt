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
