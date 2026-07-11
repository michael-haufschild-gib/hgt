# The Hedenmalm theta pair forces a divisor-supported nonlocal metric

- **ID:** `hedenmalm-theta-pair-divisor-supported-metric-law`
- **Stage:** 2-fully-proven / needs full literature audit
- **Type:** THEOREM (paper) / DIRECT HILBERT--POLYA METRIC CLASSIFICATION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED]`
- **Statement:** Every continuous positive source-core form which symmetrizes Hedenmalm's 2026
  theta differential pair pulls back to a positive Fourier measure supported on the real divisor
  of `Xi`.  Thus every nonzero admissible metric is necessarily nonlocal and divisor-supported;
  no scalar weighted `L^2` metric, and no nonzero finite-order local differential metric, can do
  the job.

## 1. The theta pair in logarithmic coordinates

Hedenmalm's eigenvalue problem uses

```text
D^x f(t)=(t/i)f'(t),
L_phi f=D^x f+f D^x phi,
phi(t)=-log VarTheta_00(i t^2),                            (1)
```

and characterizes the real zeros `alpha` of `Xi` by

```text
L_phi D^x u+alpha L_phi u=0,
u(0+)=u(+infinity)=0.                                     (2)
```

Put `t=exp x` and

```text
k(x)=2 VarTheta_00(i exp(2x)),
Phi(x)=-log k(x),
D=-i partial_x,
L=-i(partial_x+Phi'(x))=k D k^(-1).                       (3)
```

The factor `2` corrects the normalization of the displayed theta-Mellin formula in the June 2026
preprint.  It changes `Phi` only by an additive constant and therefore leaves `L` unchanged.  The
theta source is positive and has double-exponential decay in both directions.  In particular,
`k` is a nonzero Schwartz function and

```text
Lk=0.                                                      (4)
```

Riemann's theta-Mellin formula becomes the ordinary Fourier identity

```text
hat k(alpha)=int_R k(x) exp(i alpha x)dx=Xi(alpha).         (5)
```

The sign in the Fourier convention is immaterial because `k` and `Xi` are even.

## 2. Source-core symmetrizing forms

Let `q_2` be a nonnegative sesquilinear form on a function space containing the required images
of `L`.  Its pullback is

```text
q_1(u,v)=q_2(Lu,Lv).                                      (6)
```

Assume that `q_1` extends to a continuous nonnegative sesquilinear form on the Schwartz space and
that Hedenmalm pair symmetry holds on a translation-stable source core:

```text
q_2(LDu,Lv)=q_2(Lu,LDv).                                  (7)
```

Equivalently,

```text
q_1(Du,v)=q_1(u,Dv).                                      (8)
```

The Schwartz-extension hypothesis is the precise source-purity boundary.  A form defined only on
the span of eigenfunctions selected from the target divisor is not being assumed to extend.

## 3. Divisor-supported metric classification `[PROVED HERE]`

### Theorem

Under the hypotheses above, there is a unique positive tempered measure `mu` on `R` such that

```text
q_1(u,v)=int_R hat u(xi) conjugate(hat v(xi)) dmu(xi),     (9)
```

and

```text
supp(mu) subset {gamma in R:Xi(gamma)=0}.                 (10)
```

Consequently there are coefficients `c_gamma>=0`, of at most tempered growth, with

```text
mu=sum_(gamma real:Xi(gamma)=0)c_gamma delta_gamma,

q_1(u,v)=sum_gamma c_gamma
  hat u(gamma) conjugate(hat v(gamma)).                    (11)
```

Conversely, every positive tempered atomic measure of the form `(11)` defines a nonnegative
pullback form satisfying `(8)` and killing the kernel of `L`.  It therefore descends to a
well-defined form on the algebraic range of `L`.

### Proof

Let `T_a u(x)=u(x+a)`.  Since `D` generates translations, differentiate

```text
a |-> q_1(T_a u,T_a v).                                   (12)
```

The two derivative terms cancel by `(8)`.  Continuity gives

```text
q_1(T_a u,T_a v)=q_1(u,v)                                 (13)
```

for every real `a`.  Thus the Schwartz kernel of `q_1` is invariant under simultaneous
translation in its two variables.  It depends only on their difference and is a positive-definite
tempered distribution.  The Bochner--Schwartz theorem gives the unique positive tempered measure
`mu` and representation `(9)`.

By `(4)` and `(6)`,

```text
q_1(k,k)=q_2(0,0)=0.                                      (14)
```

Equations `(5)`, `(9)`, and positivity of `mu` give

```text
0=int_R |Xi(xi)|^2 dmu(xi).                               (15)
```

Hence `mu` is carried by the real zero set of `Xi`, proving `(10)`.  Since `Xi` is a nonzero
entire function, its real zeros form a discrete set with no finite accumulation point.  Every
positive tempered measure carried by that set is an atomic measure of the form `(11)`.

Conversely, `(11)` is positive and translation invariant, hence satisfies `(8)`.  Equation `(5)`
shows that `q_1(k,v)=0` for every `v`.  Since the smooth kernel of `L` is exactly `C k`, the formula

```text
q_2(Lu,Lv):=q_1(u,v)                                      (16)
```

is independent of the chosen preimages and defines a form on `ran L`.  This proves the converse.
QED.

## 4. Every ordinary metric operator is zero `[PROVED HERE]`

Suppose more restrictively that the pullback form is represented in ordinary `L^2(R,dx)` by a
positive self-adjoint metric operator `A`:

```text
q_1(u,v)=<Au,v>_(L^2).                                    (17)
```

If `A` is bounded, `(8)` makes `A` commute with the momentum operator `D`, hence `A=m(D)` for an
essentially bounded nonnegative multiplier `m`.  Equation `(14)` gives

```text
0=<Ak,k>=int_R m(xi)|Xi(xi)|^2dxi.                        (18)
```

The real zero set of `Xi` has Lebesgue measure zero, so `m=0` almost everywhere and `A=0`.

The same conclusion holds for a closed absolutely continuous Fourier-multiplier form: its
nonnegative density must vanish almost everywhere.  Therefore no nondegenerate symmetrizing
metric is an ordinary absolutely continuous `L^2` metric.  The atomic measure in `(11)` is not a
technical option; it is forced.

## 5. No finite-order local metric `[PROVED HERE]`

The nonlocality can also be read directly from differential operators.  Suppose on
`C_c^infinity(R)` that

```text
q_2(f,g)=int_R f(x) conjugate(g(x)) w(x)dx,                (19)
```

where `w` is a positive `C^2` function.  With formal adjoints in unweighted `L^2`, put

```text
A=L^* w L
 =-(partial_x-Phi') w (partial_x+Phi').                   (20)
```

Pair symmetry is

```text
[D,A]=0.                                                   (21)
```

Expanding `(20)` gives

```text
A=-w partial_x^2-w' partial_x
  +w(Phi')^2-w'Phi'-wPhi''.                               (22)
```

Commutation with `partial_x` forces every coefficient in `(22)` to be constant.  In particular,

```text
w is constant,
(Phi')^2-Phi'' is constant.                               (23)
```

But Hedenmalm's theta asymptotic gives

```text
Phi(x)=pi exp(2x)-(9/2)x-log(2pi^2)+O(exp(-2x)),

(Phi'(x))^2-Phi''(x)=4pi^2 exp(4x)+O(exp(2x)),             (24)
```

which is not constant.  Thus `(19)` is impossible.

More generally, let `q_2` be any scalar finite-order local differential form whose pullback is
represented by a finite-order differential operator `A`.  Equation `(21)` forces `A` to have
constant coefficients.  Since `Lk=0`, one also has `Ak=0`.  Fourier transformation gives

```text
a(xi)Xi(xi)=0                                             (25)
```

for the polynomial symbol `a`.  Since `Xi` is nonzero on an open subset of the real axis,
`a=0`.  Hence the only finite-order local symmetrizing pullback is the zero form.

The positive implementation law is:

> A Hilbert metric for the Hedenmalm theta pair must be a genuinely nonlocal rigging whose
> Fourier spectral measure is carried by the real `Xi` divisor.  Local weights and finite-order
> differential metrics cannot be repaired; the missing theorem is conservativity of a
> source-defined divisor-supported incidence form.

## 6. Exact eigenfunction sampling and the simplicity floor `[PROVED HERE]`

Let `u_alpha` be twice Hedenmalm's displayed eigenfunction for any complex zero `alpha` of `Xi`,
written in the logarithmic coordinate.  Eigenfunctions are defined only up to nonzero scalar, and
this normalization matches `(5)`.  The first-order reduction in his proof is

```text
(D+alpha)u_alpha=-i k.                                    (26)
```

With the Fourier convention in `(5)`, the momentum operator has symbol `-xi`.  Hence

```text
hat u_alpha(xi)=-i Xi(xi)/(alpha-xi).                     (27)
```

The apparent singularity at a real zero `xi=alpha` is removable.  Therefore:

1. if `alpha` is nonreal, `hat u_alpha(gamma)=0` at every real zero `gamma` of `Xi`;
2. if `alpha` is real, then

   ```text
   hat u_alpha(gamma)=0                  for gamma!=alpha,
   hat u_alpha(alpha)=i Xi'(alpha).                       (28)
   ```

Insert `(28)` into `(11)`.  For every real zero `alpha`,

```text
q_1(u_alpha,u_alpha)=c_alpha |Xi'(alpha)|^2,               (29)
```

while every nonreal-zero eigenfunction has zero norm.  Distinct real-zero eigenfunctions are
orthogonal.

### Nondegeneracy corollary

The form `(11)` is positive definite on the finite span of all theta eigenfunctions if and only if

```text
every Xi zero is real,
every Xi zero is simple,
c_gamma>0 at every zero.                                  (30)
```

Indeed, an off-line zero is killed by the first clause above, and a multiple real zero has
`Xi'(alpha)=0` and is killed by `(29)`.  Conversely, under `(30)`, a finite linear combination of
distinct eigenfunctions has squared norm

```text
sum_alpha c_alpha |a_alpha|^2 |Xi'(alpha)|^2,              (31)
```

which vanishes only when every coefficient `a_alpha` vanishes.

Thus a nondegenerate source-core metric for the Hedenmalm pair is not merely an RH certificate.  In
this category it certifies

```text
RH + simplicity of every nontrivial zeta zero.             (32)
```

Hedenmalm notes that the boundary-value problem has one eigenfunction at each eigenvalue and that
this gives weak support for simplicity.  Equations `(27)`--`(32)` give the exact metric reason:
multiplicity is invisible to a positive order-zero divisor measure and forces degeneracy.

## 7. Why this does not prove RH

Positive atomic measures supported on the already-real zeros exist.  They give semidefinite forms,
but a complex-zero eigenfunction, if one exists, lies in their radical by pair symmetry.  The
Hedenmalm corollary needs a genuine Hilbert norm on the relevant image space, not merely a positive
semidefinite form.

Thus the remaining assertion is exactly

```text
q_2(Lu_alpha,Lu_alpha)>0
for every nonzero theta eigenfunction u_alpha.             (33)
```

Under pair symmetry, `(33)` excludes every nonreal `alpha`, excludes multiple real zeros, and proves
RH plus simplicity.  Defining `mu` by first listing the real zeros is target-fed and does not prove
`(33)`.  A viable construction must derive the atomic metric and its conservativity from the
completed Euler source.

## 8. Carrier consequence

The finite-Gamma boundary law proves that finite-degree archimedean completion contributes only one
projective valuation direction.  The present theorem says that the missing Hilbert metric is not
another local archimedean weight: it is a nonlocal spectral measure supported on divisor atoms.
Therefore a source-pure implementation must couple

```text
all-prime phase carrier
  + theta/Gamma completion
  + divisor-supported Fourier rigging.                    (34)
```

At cutoff `N`, the arithmetic side must still transport at least `pi(N)` marked prime directions.
The divisor measure in `(11)` is a separate pointed quotient and cannot manufacture those phase
directions.  This is precisely the carrier shape demanded by the completed Euler--divisor
incidence-stack conjecture.

## 9. Attacks and exact boundary

1. **Hedenmalm's theorem is not contradicted.**  His proposed form is defined on a finite span of
   zero eigenfunctions.  The classification applies when the pullback extends to a
   translation-stable source core.  A form refusing every such extension remains possible, but is
   intrinsically target-domain and needs its own density and closure theorem.
2. **The theta source is essential.**  The support law uses the exact Fourier identity
   `hat k=Xi`, not only asymptotic information about `Phi`.
3. **Positivity is essential.**  From `(15)`, a signed distribution can cancel away from the zero
   set.  A Hilbert metric is positive, so such cancellation is unavailable.
4. **Nonlocal does not mean arbitrary.**  Pair symmetry fixes the nonlocal metric completely up to
   positive weights on the real divisor atoms.
5. **Known real zeros are insufficient.**  Choosing weights on them creates a semidefinite
   target-fed form.  Source-derived conservativity `(33)` is the RH-and-simplicity-bearing
   statement.
6. **A domain escape is explicit.**  One may avoid the theorem only by using a form without a
   continuous translation-stable source-core pullback.  Such an architecture must prove that its
   restricted domain is source-defined, complete, and contains every theta eigenfunction before
   invoking self-adjointness.

## 10. Parent and novelty audit

The direct parent is H. Hedenmalm, *Spectral interpretation of Riemann zeta zeros*, arXiv:2606.17494
(June 2026).  That paper proves the theta boundary-value characterization and proposes finding a
Hilbert form which makes the pair `(L D,L)` self-adjoint.  It does not classify such forms, derive
their Fourier support, or exclude local metrics.

The harmonic-analysis inputs used here are classical:

1. the Bochner--Schwartz representation of positive-definite tempered distributions;
2. the Fourier-multiplier description of the commutant of translations;
3. Riemann's theta-Mellin representation of `Xi`.

Searches through 11 July 2026 did not locate the assembled divisor-support classification or its
local-metric corollary for Hedenmalm's pair.  Because the parent preprint is only weeks old, priority
is especially fragile.  The paper proof is complete, but the claim remains
`[NOVELTY UNVERIFIED]` until a specialist literature audit confirms that no contemporaneous note
contains the same pullback-form argument.

## Lean status

`formal/GaloisForLFunctions/RHTower/XiDivisorSupportedMetric.lean` now constructs the complete
atomic metric class occurring after the Bochner--Schwartz support step. A weight is a nonnegative
function on the actual analytic-multiplicity copies of the Xi divisor together with a proof that
it vanishes at every nonreal centered spectral point. Lean proves unconditionally that its
polarization is Hermitian, symmetrizes multiplication by the centered spectral coordinate, and
has `XiC` in both radicals.

For every actual Xi zero `alpha`, the module proves the exact weighted sampling identity

```text
q_c(u_alpha,u_alpha)
  = (sum of c over the multiplicity fiber at alpha) * ||XiC'(alpha)||^2.
```

It follows in Lean that every nonreal-zero eigenfunction is null, and that strict positivity on
every theta eigenfunction implies both RH and `XiC'(alpha) != 0` at every zero. The exact converse
criterion is also formalized: conservativity is equivalent to positive mass on every zero fiber
plus simplicity. No RH, positivity, or source-conservativity assertion is introduced as an
assumption inside these results.

`formal/GaloisForLFunctions/SchwartzTranslation.lean` supplies the first missing upstream layer
that mathlib did not package: additive translation as a continuous linear action on Schwartz
space, with its group and inverse laws, exact commutation with every directional derivative,
strong continuity, and strong differentiability of every translation orbit in the Schwartz
topology.

`formal/GaloisForLFunctions/SchwartzSesquilinear.lean` packages jointly continuous sesquilinear
forms on complex Schwartz space. Lean proves directly that momentum symmetry makes the derivative
of every simultaneous-translation matrix coefficient vanish, and hence forces exact simultaneous
translation invariance. No differentiability assumption on the form is added.

`formal/GaloisForLFunctions/RHTower/XiSchwartzMetricSupport.lean` formalizes the downstream
measure step. The real Xi zero set is closed and countable; if a representing measure has
integrable `|XiC|^2` with zero integral, its support lies in that set and the measure is exactly
the sum of its point masses there. The countability proof is extracted from local finiteness of
the actual global Xi divisor and sigma-compactness of the complex plane.

`formal/GaloisForLFunctions/SchwartzProduct.lean` supplies the jointly continuous pointwise
Schwartz algebra that mathlib did not package. It proves explicit defining-seminorm product bounds,
joint continuity of multiplication, continuous complex conjugation, and joint continuity of
`f * conjugate(g)`.

`formal/GaloisForLFunctions/SchwartzSpectralMeasureForm.lean` formalizes the constructive half of
the Bochner--Schwartz classification. Every positive measure of temperate growth now produces,
without further hypotheses, a jointly continuous nonnegative Hermitian Schwartz form through the
Fourier integral in `(9)`. Lean proves directly that momentum is symmetric for this form and that
the form is invariant under simultaneous translation.

`formal/GaloisForLFunctions/RHTower/XiSchwartzSpectralMeasure.lean` joins that construction to the
Xi support theorem. If an actual Schwartz source has Fourier transform `XiC` on the real axis,
integrability of `|XiC|^2` against every temperate spectral measure follows automatically from
Schwartz decay. Nullity of the source then forces the complete atomic decomposition `(11)`; no
integrability or support premise remains in this adapter.

The remaining formal gap is the central Schwartz-kernel plus Bochner--Schwartz existence theorem
taking an arbitrary positive continuous translation-invariant Schwartz form to its positive
tempered spectral measure, together with the construction of the theta source as an actual
Schwartz object whose formal Fourier transform is `XiC`. Mathlib supplies the component theories
but neither the required Schwartz kernel theorem nor this assembled representation theorem.

## Gates

- [x] latest direct Hilbert--Polya parent identified and read at theorem level
- [x] logarithmic-coordinate operator pair derived
- [x] pair symmetry converted into translation invariance
- [x] positive pullback forms classified by Bochner--Schwartz
- [x] support forced onto the real `Xi` divisor
- [x] bounded/absolutely-continuous metrics excluded
- [x] scalar weighted `L^2` metrics excluded
- [x] every finite-order local differential metric excluded
- [x] exact Fourier samples of every theta eigenfunction computed
- [x] nondegeneracy identified with RH plus simplicity
- [x] source-core boundary separated from target-defined zero spans
- [x] exact RH-bearing conservativity statement isolated
- [ ] independent specialist novelty audit
- [ ] source-derived conservative atomic metric
- [x] Lean positive atomic real-divisor metric class
- [x] Lean exact weighted eigenfunction sampling and conservativity criterion
- [x] Lean conservativity implies RH plus simplicity
- [x] Lean continuous linear Schwartz translations and strong orbit differentiability
- [x] Lean momentum symmetry implies simultaneous-translation invariance
- [x] Lean zero Xi energy forces support on the closed real Xi divisor
- [x] Lean countability and atomic decomposition of the supported measure
- [x] Lean jointly continuous Schwartz multiplication and conjugate multiplication
- [x] Lean every positive temperate measure constructs the required continuous positive form
- [x] Lean the constructed spectral form symmetrizes momentum and is translation invariant
- [x] Lean the Schwartz-Xi null-source adapter discharges integrability and yields atomicity
- [ ] Lean Schwartz translation-invariance to Bochner--Schwartz classification bridge
