# Suzuki finite shifts carry a flat projective resolvent holonomy

- **ID:** `suzuki-finite-shift-flat-projective-resolvent-holonomy`
- **Status:** fully proved on paper; dependency-closed core formalized in Lean
- **Lane:** Suzuki finite-aperture divisor dynamics; nonlinear prime transport
- **Parents:** `suzuki-prime-clock-atom-velocity-transference`,
  `suzuki-donoghue-defect-spectral-measure-law`
- **Source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  [arXiv:2606.09096](https://arxiv.org/abs/2606.09096), especially Theorem 1.5 and
  Sections 6--7
- **RH used:** no
- **Computation used:** no

## Frontier question

The free-boundary tangent is now arithmetic-complete: every prime power has an exact nonzero
velocity in every free Donoghue pole, and half-shifted Bohr demodulation recovers its von Mangoldt
weight.  The live obstruction was whether this first-order signal can be integrated through a
finite Suzuki shift without a perturbation series, a branch choice, or a global labeling of the
infinite pole set.

The tempting stronger claim was:

> At fixed aperture, all Suzuki poles form globally defined noncolliding real-analytic curves over
> the whole admissible shift interval.

This is not justified by simplicity alone.  The analytic implicit-function theorem gives local
curves, but global continuation also needs properness: a labeled pole must not escape to infinity
at a finite shift.  Neither Suzuki's theorem nor the current corpus supplies the required uniform
zero count or phase asymptotic.  The global claim is therefore rejected, not used.

The replacement below integrates the complete carrier without labeling any pole.  It is stronger
at the meromorphic-function level and exposes a single endpoint object for the cofinal limit.

## Setup

Fix an aperture `a>0`.  Let `A=A_a` be Suzuki's Friedrichs operator and let

```text
e(x)=exp(x),
R_r=(A+rI)^(-1),
u_r=R_r e,
F_r(z)=integral_[-a,a] u_r(x) exp(i z x) dx,
```

where `r> -lambda_a`, so `A+rI` is positive.  Write Suzuki's normalized Fourier Livsic carrier as

```text
Theta_r(z)=((z-i) F_r(z))/((z+i) F_r(-z)).                 (1)
```

For two admissible shifts `r,s`, define the two-resolvent source and its transform

```text
v_(s,r)=R_s R_r e,
J_(s,r)(z)=integral_[-a,a] v_(s,r)(x) exp(i z x) dx.       (2)
```

Finally define the reflected determinant

```text
D_(s,r)(z)
  =J_(s,r)(z) F_r(-z)-F_r(z) J_(s,r)(-z).                 (3)
```

All identities below are meromorphic identities; displayed quotients are read away from their
explicit denominators and hence extend wherever both sides do.

## Theorem: exact finite-shift response and flat projective holonomy

For every pair of admissible shifts `r,s`:

1. **Exact two-resolvent update**

   ```text
   u_s-u_r=(r-s)R_s R_r e,
   F_s(z)=F_r(z)+(r-s)J_(s,r)(z).                         (4)
   ```

2. **Branch-free finite carrier response**

   ```text
   Theta_s(z)-Theta_r(z)
    =((z-i)/(z+i))
      *(r-s)D_(s,r)(z)/(F_s(-z)F_r(-z)).                 (5)
   ```

3. Define endpoint projective transport

   ```text
   H_(s<-r)(z)
    =F_s(z)F_r(-z)/(F_s(-z)F_r(z)).                      (6)
   ```

   Then

   ```text
   Theta_s=H_(s<-r) Theta_r,                              (7)

   H_(s<-r)-1
    =(r-s)D_(s,r)/(F_s(-z)F_r(z)).                       (8)
   ```

4. **Flatness / exact path independence.**  For any admissible `r,s,t`,

   ```text
   H_(t<-r)=H_(t<-s) H_(s<-r).                           (9)
   ```

   Thus any finite sequence of intermediate shifts or prime-activation states telescopes to the
   same endpoint transport.  Noncommuting operator dressings become a scalar flat cocycle after
   the reflected projectivization `(6)`.

5. Put

   ```text
   G_r(z)=integral_[-a,a] (R_r^2 e)(x) exp(i z x) dx,
   Xi_r(z)=G_r(-z)/F_r(-z)-G_r(z)/F_r(z).                (10)
   ```

   Then the infinitesimal form of the finite law is

   ```text
   partial_r F_r=-G_r,
   partial_r Theta_r=Theta_r Xi_r,                       (11)

   Xi_r(z)
    =-[G_r(z)F_r(-z)-F_r(z)G_r(-z)]/[F_r(z)F_r(-z)].     (12)
   ```

6. Let `x(r)` be any local simple real pole of the Donoghue function, equivalently
   `Theta_r(x(r))=1`.  If

   ```text
   partial_z Theta_r(x)=i q_r(x),   q_r(x)>0,
   mu_r({x})=2/q_r(x),
   ```

   then its exact nonlinear velocity is

   ```text
   x'(r)=i mu_r({x}) Xi_r(x)/2.                          (13)
   ```

   For real `x`, the source vectors are real, hence
   `F_r(-x)=conj(F_r(x))` and `G_r(-x)=conj(G_r(x))`.  Therefore `Xi_r(x)` is purely imaginary and
   `(13)` is real, as required.

## Proof

The second resolvent identity gives

```text
R_s-R_r=(r-s)R_s R_r.                                   (14)
```

Apply `(14)` to `e` and take the compactly supported Fourier transform to obtain `(4)`.

Subtract the two fractions in `(1)`.  Their cross numerator is

```text
F_s(z)F_r(-z)-F_r(z)F_s(-z).
```

Substitution of `(4)` cancels both `F_r(z)F_r(-z)` terms and leaves exactly
`(r-s)D_(s,r)(z)`.  This proves `(5)`.

Dividing `(1)` at shift `s` by `(1)` at shift `r` cancels the universal Cayley factor and gives
`(6)`--`(7)`.  Subtracting one in `(6)` and using the same cross-numerator calculation gives `(8)`.

For `(9)`, multiply the two cross ratios:

```text
[F_t(z)F_s(-z)/(F_t(-z)F_s(z))]
*[F_s(z)F_r(-z)/(F_s(-z)F_r(z))]
 =F_t(z)F_r(-z)/(F_t(-z)F_r(z)).
```

Every intermediate source value cancels.  This proves flatness and path independence without a
logarithm or an ordering convention.

Differentiate `(A+rI)R_r=I` to get `partial_r R_r=-R_r^2`.  This proves the first identity in
`(11)`.  Logarithmic differentiation of `(1)` then gives

```text
partial_r log Theta_r
 =-G_r(z)/F_r(z)+G_r(-z)/F_r(-z)=Xi_r(z),
```

which is equivalent to the second identity in `(11)`.  A common denominator gives `(12)`.

Differentiate `Theta_r(x(r))=1`.  Using `(11)` and the phase-speed law,

```text
0=Xi_r(x)+i q_r(x)x'(r),
x'(r)=-Xi_r(x)/(i q_r(x))=i mu_r({x})Xi_r(x)/2,
```

proving `(13)`.  The conjugation identities make `(10)` a difference of a complex number and its
conjugate, hence purely imaginary on the real line.

## Exact nonlinear prime dressing

At fixed aperture Suzuki's prime contribution is finite.  Write an admissible activation family

```text
A(t)=A_arch+sum_m t_m B_m,
R_t=(A(t)+rI)^(-1).
```

On every open parameter region where the inverse exists,

```text
partial_(t_m) R_t=-R_t B_m R_t.                          (15)
```

Replacing `R_r^2 e` in `(10)` by `R_t B_m R_t e` gives the exact fully dressed prime generator and
the same pole law `(13)`.  At the free endpoint, the parent theorem evaluates it explicitly as

```text
partial_(t_m) x_(a,k)|_(t=0)
 =Lambda(m)/(a sqrt(m))
   *sin(((k+1/2)pi/a)log(m)).                            (16)
```

Equations `(6)` and `(9)` now integrate all such activations at carrier level: activation order and
partition disappear from the endpoint holonomy.  What remains nonlinear is concentrated in the
single dressed determinant `(3)`, not in an uncontrolled perturbation series.

## Frontier consequence

This closes the previously stated "nonlinear integration" wall at finite aperture in the exact
meromorphic category.  It does **not** prove RH and does not assert global labeled pole curves.
The remaining cofinal problem is narrower:

> Choose an intrinsic admissible endpoint schedule and prove compact-open tightness plus divisor
> control for the endpoint transports `H_(s_a<-r_a)`, equivalently for the normalized dressed
> determinants `(r_a-s_a)D_(s_a,r_a)` in `(5)` or `(8)`.

No accumulation of local Taylor remainders and no path-ordering ambiguity remain.

## Novelty audit

- Suzuki proves the deficiency-index construction, real zeros, and motivates arithmetic control
  of the shift parameter, but does not state `(5)`--`(13)`.
- Classical second-resolvent and implicit-function identities are inputs.  New content is their
  exact reflected projective synthesis for Suzuki's source, especially the endpoint cocycle `(9)`
  and its prime-activation path independence.
- Exact-phrase and concept searches across the repository and arXiv found Clark/rank-one
  perturbation theory and general resolvent identities, but no Suzuki finite-shift cross-ratio
  transport or reflected two-resolvent determinant law.
- Novelty claim is source-specific, not a claim that the second resolvent identity itself is new.

## Formalization target

Lean should formalize the dependency-closed exact core:

```text
suzukiProjectiveSourceTransport
suzukiProjectiveSourceTransport_self
suzukiProjectiveSourceTransport_comp
suzukiProjectiveSourceTransport_path_independent
suzukiFiniteShiftSource
suzukiFiniteShiftSource_cross
suzukiProjectiveSourceTransport_finiteShift_sub_one
suzukiFourierLivsic_eq_transport_mul
suzukiFourierLivsic_finiteShift_sub
suzukiLogarithmicSourceGenerator
suzukiLogarithmicSourceGenerator_eq_neg_reflectionTangent
suzukiImplicitPoleVelocity_eq_clarkTransport
```

The unbounded Suzuki operator, inverse differentiation, and Fourier integral remain paper-level
until the concrete Friedrichs operator is represented in Lean.

## Pipeline checklist

- [x] prior Suzuki corpus and failed routes audited
- [x] global labeled-flow conjecture hostile-tested and rejected
- [x] positive survivor strengthened to finite endpoint transport
- [x] dependency-closed paper proof
- [x] external novelty audit
- [x] Lean module
- [x] exact module build, lint, and axiom audit
- [x] promote to Stage 2/3 and connect to SOTA wall

### Audit — item 6's reality claim is already formal (target list was under-listing)

The Formalization target block omits three declarations that
`RHTower/SuzukiFiniteShiftProjectiveHolonomy.lean` already proves, all discharging item 6's closing
sentence *"therefore `Xi_r(x)` is purely imaginary and `(13)` is real, as required"*:

- `conj_suzukiLogarithmicSourceGenerator_eq_neg` : from `F(-x) = conj F(x)` and `G(-x) = conj G(x)`,
  the generator is anti-self-conjugate.
- `suzukiLogarithmicSourceGenerator_re_eq_zero` : hence `Xi_r(x)` is purely imaginary.
- `suzukiClarkTransport_im_eq_zero` : hence `(13)`'s velocity `i mu Xi / 2` is real.

No new Lean was needed; this entry exists so the target list is not read as a gap. The genuinely
paper-level remainder is unchanged and is operator-dependent: the unbounded Suzuki operator, the
inverse differentiation `(11)`, and the Fourier integral defining `G_r` in `(10)`.
