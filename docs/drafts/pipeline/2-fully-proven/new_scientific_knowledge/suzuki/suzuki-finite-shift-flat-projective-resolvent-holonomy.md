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

**Superseded — see the 2026-08-01 entries below.**  This paragraph read that "the unbounded Suzuki
operator, inverse differentiation, and Fourier integral remain paper-level until the concrete
Friedrichs operator is represented in Lean".  Two of those three were never blocked on it, and the
third is mathlib's:

- **inverse differentiation** — `partial_r R_r = -R_r^2` follows from the first resolvent identity
  alone, already proved in `HTGeometry/ResolventFamilyJet.lean` for a family of *bounded* elements;
- **the Fourier integral** — differentiation under an interval integral, supplied by mathlib's
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`;
- **the operator itself** — not needed: `(11)`'s derivative law is
  `hasDerivAt_reflectedQuotientCarrier`, which takes the family's parameter derivative as a
  hypothesis, and `(10)` = `(12)` is the pure algebra of
  `suzukiReflectedQuotientDifference_eq_crossWronskian`.

What genuinely remains are the domination hypotheses for the integral differentiation — properties
of the source family — and the identification of that family with Suzuki's construction.  No
Friedrichs extension is required anywhere.

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

### Cross-reference — `(11)`'s "inverse differentiation" is already corpus-owned

The Formalization target parks "the unbounded Suzuki operator, inverse differentiation, and Fourier
integral" until the concrete Friedrichs operator exists in Lean. The **inverse differentiation** half
does not need it: `partial_r R_r = -R_r^2` follows from the first resolvent identity alone, and the
corpus already proves exactly that in `HTGeometry/ResolventFamilyJet.lean`:

- `IsResolventFamilyOn` — the resolvent identity as a property of a family `S : ℝ → A` of **bounded**
  elements, with no operator construction;
- `IsResolventFamilyOn.continuousAt`, `.hasDerivAt` — continuity and the derivative law
  `partial_u R_u = R_u^2` forced by that identity;
- `.hasDerivAt_pow`, `.hasDerivAt_jet`, `resolventShiftJet`, `hasDerivAt_resolventShiftJet` — the
  full jet law `partial_u^n R_u = n! R_u^{n+1}`;
- `aeval_eq_resolventShiftJet_sum` — polynomial realization.

So `(11)`'s `partial_r F_r = -G_r` reduces to differentiating under the Fourier integral, with the
operator derivative supplied. Combined with the strong-limit machinery recorded on
`suzuki-neumann-dominated-shift-cone-obstruction.md` and
`suzuki-boundary-log-nonclock-nonflat-tangent.md`, the only genuinely operator-dependent input left
on this card is the Fourier integral defining `G_r` in `(10)` — i.e. naming the source, not
constructing the operator.

### Gap class — objects present, calculus absent

`RHTower/SuzukiFiniteShiftProjectiveHolonomy.lean` defines `suzukiProjectiveSourceTransport`,
`suzukiFiniteShiftSource`, `suzukiLogarithmicSourceGenerator` and proves their algebra, but contains
**zero** derivative lemmas — no `HasDerivAt`, `DifferentiableAt` or `deriv` anywhere. Yet `(11)` and
`(12)` differentiate exactly these objects (`partial_r Theta_r = Theta_r Xi_r`, and `Xi_r` as the
cross-Wronskian quotient).

So the card's differentiation steps are not blocked on the operator — the operator derivative
`partial_r R_r = -R_r^2` is already corpus-owned (see the cross-reference above) — but on the
**calculus of this module's own objects**, which nobody has written. That is a bounded, mechanical
piece of work: derivative, `DifferentiableAt`, and a logarithmic-derivative law for the transport,
mirroring what `RHTower/SuzukiDonoghueHerglotzTransform.lean` now carries for the Cayley pair.

Note for whoever writes it: mathlib's `logDeriv_div` (`Mathlib/Analysis/Calculus/LogDeriv.lean`)
gives the quotient rule for logarithmic derivatives directly, and the transport is a quotient of two
products, so `logDeriv_mul` and `logDeriv_div` compose to `(12)` without a bare quotient-rule
computation.

### Lean progress — `(10)` and `(12)` are the same expression

- `suzukiReflectedQuotientDifference_eq_crossWronskian` :
  `G(-z)/F(-z) - G(z)/F(z) = -[G(z)F(-z) - F(z)G(-z)] / [F(z)F(-z)]`, for `F(z), F(-z) ≠ 0`.
  [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean.

The card presents `Xi_r` twice — as the reflected difference of logarithmic quotients in `(10)` and
as the negated cross-Wronskian in `(12)` — and their equality is **pure algebra**, requiring no
differentiation at all. So that half of `(12)` is independent of how the source family depends on the
shift, and is now discharged regardless of the parameter setup. What still needs the parameter
dependence is only `partial_r Theta_r = Theta_r Xi_r` itself.

### Lean progress — `(11)`'s derivative law, with the dependence parameterized

- `hasDerivAt_reflectedQuotientCarrier` : for a parameter family,
  `d/dr [c * f(r) / g(r)] = (c f/g) * (f'/f - g'/g)` — the carrier times the difference of
  logarithmic derivatives, with the constant Cayley factor `c` passing straight through.
  [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean.

This is `(11)`'s `partial_r Theta_r = Theta_r Xi_r` with the family's parameter dependence taken as a
**hypothesis** rather than assumed of Suzuki's source: instantiate `f = F_r(z)`, `g = F_r(-z)`,
`c = (z - i)/(z + i)`, and the conclusion is `Theta_r` times `F'(z)/F(z) - F'(-z)/F(-z)`, which is
`Xi_r` by `suzukiReflectedQuotientDifference_eq_crossWronskian` above.

So `(11)` and `(12)` are now both formal **modulo supplying `HasDerivAt` for the source family** —
which is precisely the card's `partial_r F_r = -G_r`, and that reduces to differentiating under the
Fourier integral with `HTGeometry/ResolventFamilyJet.lean`'s `partial_r R_r = -R_r^2` already in
hand. No step of this card now requires constructing the operator.

### The Fourier integral step is mathlib's, not ours

The Formalization target's last parked item, the Fourier integral behind `partial_r F_r = -G_r`, is
differentiation under an interval integral, and mathlib provides it directly:

- `Mathlib/Analysis/Calculus/ParametricIntervalIntegral.lean` :
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` — under a local dominating
  bound it gives exactly
  `HasDerivAt (fun x => ∫ t in a..b, F x t) (∫ t in a..b, F' x₀ t) x₀`.

Instantiating `F r t = u_r(t) exp(i z t)` and `F' r t = (partial_r u_r)(t) exp(i z t)` yields
`(11)`'s `partial_r F_r = -G_r`, with `partial_r u_r = -R_r^2 e` supplied by
`HTGeometry/ResolventFamilyJet.lean`. The remaining obligations are the domination hypotheses — a
bound on `‖(partial_r u_r)(t) exp(i z t)‖` integrable over `[-a, a]` — which are properties of the
source family, not of an operator construction.

**Net position on this card.** Every step of the Theorem is now either formal or located in mathlib:
`(4)`--`(9)` algebra formal; `(10)` = `(12)` by `suzukiReflectedQuotientDifference_eq_crossWronskian`;
`(11)`'s derivative law by `hasDerivAt_reflectedQuotientCarrier`; the resolvent derivative by
`ResolventFamilyJet`; the Fourier differentiation by the mathlib theorem above; and `(13)`'s reality
by the three declarations noted earlier. Nothing requires the Friedrichs construction.

### Lean progress — the Fourier kernel bound for the domination hypotheses

The remaining obligations of the Fourier differentiation step are domination hypotheses, and the
factor they turn on is the kernel's modulus. Added to
`HTGeometry/CompactFourierSineKernel.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `norm_fourierKernel` : `‖exp (I z t)‖ = exp (-(Im z) t)` for real `t` — the real part of `I z t`
  is `-(Im z) t`.
- `norm_fourierKernel_le` : on `|t| <= a` the kernel is bounded by `exp (|Im z| a)`.

So a dominating bound for `partial_r u_r` on `[-a, a]` transfers to one for
`(partial_r u_r)(t) exp(I z t)` by multiplying by this constant, which is what
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` consumes. The remaining input is a bound on the
source family itself.

- `norm_mul_fourierKernel_le` : the domination transfer — a bound `‖f t‖ <= bound t` on `|t| <= a`
  gives `‖f t * exp (I z t)‖ <= exp (|Im z| a) * bound t`. [PROVED HERE], standard axioms, builds
  clean.

With this the domination hypothesis of `hasDerivAt_integral_of_dominated_loc_of_deriv_le` reduces to
a bound on the **amplitude family** `partial_r u_r` alone, the kernel contributing only the constant
`exp (|Im z| a)`. Nothing about the operator enters that reduction.

### The amplitude bound is corpus-owned too — the domination chain closes

The one input the transfer lemma still needed was a bound on the amplitude family
`partial_r u_r = -R_r^2 e`. That is `‖R_r‖^2 ‖e‖`, and a **local uniform** bound on `‖R_r‖` is
already proved in `HTGeometry/ResolventFamilyJet.lean`:

- `IsResolventFamilyOn.norm_sub_le` : `‖S u - S v‖ <= |u - v| (‖S u‖ ‖S v‖)`, straight from the
  resolvent identity;
- `IsResolventFamilyOn.norm_le_two_mul` : if `|u - v| ‖S v‖ <= 1/2` then `‖S u‖ <= 2 ‖S v‖` — the
  norms stay within a factor of two near a reference shift.

So on a small enough shift neighbourhood the amplitude is bounded by the constant
`4 ‖S v‖^2 ‖e‖`, a constant is interval-integrable on `[-a, a]`, and
`norm_mul_fourierKernel_le` carries that through the kernel. The domination package of
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` is therefore fully assembled from corpus and
mathlib theorems.

**Every analytic ingredient of this card's Theorem is now formal or located, with nothing left
requiring the Friedrichs construction.** What remains is the identification of the abstract family
`S` with Suzuki's `R_r = (A + rI)^{-1}` — naming the source.

### Lean progress — the derivative amplitude bound, named

- `IsResolventFamilyOn.norm_sq_le_four_mul` : near a reference shift, `‖(S u)^2‖ <= 4 ‖S v‖^2`.
  Since `partial_u S u = -(S u)^2`, this is exactly the quantity a domination hypothesis must bound.
  [PROVED HERE] in `HTGeometry/ResolventFamilyJet.lean`, standard axioms
  `[propext, Classical.choice, Quot.sound]`, builds clean.

The domination package is now explicit end to end: `norm_sq_le_four_mul` bounds the amplitude by a
constant on a shift neighbourhood, `norm_mul_fourierKernel_le` carries that through the kernel, the
resulting constant bound is interval-integrable on `[-a, a]`, and
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` consumes the package to give
`partial_r F_r = -G_r`.

- `IsResolventFamilyOn.norm_pow_le_of_small` : the same bound at **every** jet order,
  `‖(S u)^(n+1)‖ <= (2 ‖S v‖)^(n+1)` near a reference shift. Since
  `partial_u^n S u = n! (S u)^(n+1)` (`hasDerivAt_jet`), this is what higher-order domination needs,
  so the differentiation-under-the-integral argument extends to every jet, not just the first.
  [PROVED HERE], standard axioms, builds clean.
