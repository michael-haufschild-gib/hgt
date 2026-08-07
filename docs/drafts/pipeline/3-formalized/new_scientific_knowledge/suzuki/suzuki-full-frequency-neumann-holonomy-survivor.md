# Suzuki full-frequency Neumann holonomy survivor

- **ID:** `suzuki-full-frequency-neumann-holonomy-survivor`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT SOURCE THEOREM / FAILED-SQUARE POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:** `suzuki-one-sided-coordinate-phase-normalization`,
  `suzuki-jump-kernel-loewner-growth-gap`
- **RH used:** no
- **Computation used:** no

## Claim

The direct Neumann comparison channel cancels from Suzuki's sewn **central residue**, but it does
not cancel from the full-frequency jump quotient.  Its exact survivor is a projective holonomy of
the two finite characteristics.  This invalidates the prime--Gamma-only Bianchi-square producer
in the active Loewner card and supplies the missing correction that every full-frequency proof
must retain.

Fix aperture `a>0`.  Let `nu` be an odd compact source distribution on `[-a,a]`, and use Fourier
convention

```text
W(z)=<nu,e^(iz·)>.
```

Assume `W'(0)!=0`, as for Suzuki's phase-one characteristic.  For the global Neumann kernel

```text
r_0(t)=-|t|/2,
```

let `T_R,T_L` be its right and left compact convolution triangles.  The Xi-real normalized
triangle is `I=-i T_R`.  Then, away from the characteristic divisor,

```text
n_(a,W)(z):=Odd_z[I(z)/W(z)]
 =-W'(0) sin(az)/(2z W(z)).                            (1)
```

The quotient is meromorphic; every displayed occurrence of `sin(az)/z` has its usual removable
value `a` at zero.

For two real shifts `alpha!=beta`, write `W_alpha,W_beta` for their odd characteristics and split
the normalized full shifted-kernel responses as

```text
q_lambda=q_lambda^EG-lambda n_(a,W_lambda).             (2)
```

Affine sewing to target shift zero gives the exact full-frequency decomposition

```text
[beta q_alpha-alpha q_beta]/(beta-alpha)
 =[beta q_alpha^EG-alpha q_beta^EG]/(beta-alpha)
   +N_(alpha,beta),                                     (3)

N_(alpha,beta)(z)
 =alpha beta/(beta-alpha)
    [n_(a,W_beta)(z)-n_(a,W_alpha)(z)]                  (4)

 =alpha beta sin(az)/(2z(beta-alpha))
    [W_alpha'(0)/W_alpha(z)-W_beta'(0)/W_beta(z)].       (5)
```

Equivalently, with projectively normalized characteristics

```text
What_lambda(z)=W_lambda(z)/W_lambda'(0),
```

one has

```text
N_(alpha,beta)(z)
 =alpha beta sin(az)/(2z(beta-alpha))
    [1/What_alpha(z)-1/What_beta(z)].                    (6)
```

Thus the direct channel disappears at all frequencies if and only if the two normalized
characteristics coincide.  Finite shift is projectively non-flat in the actual Suzuki source, so
this is not the generic situation.

## Proof of the one-source triangle law

Write `mu_j=<nu,y^j>`.  Oddness gives `mu_0=0`.  On `[-a,a]`, right minus left Neumann response is

```text
h_R(x)-h_L(x)
 =<nu(y),sgn(x-y)r_0(x-y)>
 =<nu(y),-(x-y)/2>
 =-x mu_0/2+mu_1/2
 =mu_1/2.                                               (7)
```

The apparent sign discontinuity causes no distributional problem because
`sgn(t)r_0(t)=-t/2` is the smooth linear function used in the second line.  Endpoint atoms from
zero extension are therefore included automatically.

Odd-source reflection gives `T_L(z)=-T_R(-z)`.  Hence the reflection-even part of the right
triangle is half the Fourier transform of `(7)`:

```text
Even_z[T_R](z)
 =1/2 Fourier_[−a,a](h_R-h_L)(z)
 =mu_1 sin(az)/(2z).                                    (8)
```

Differentiating the compact Fourier transform at zero gives

```text
W'(0)=i mu_1.                                           (9)
```

Because `W` is odd,

```text
Odd_z[(-i T_R)/W]=Even_z[-i T_R]/W.                     (10)
```

Substitution of `(8)--(9)` into `(10)` proves `(1)`, including the physical-to-Xi-real phase.

## Proof of affine holonomy

Linearity of the triangle in `g-lambda r_0` proves `(2)` even though the source `nu_lambda`
itself depends on `lambda`: formula `(1)` is applied separately to its own characteristic
`W_lambda`.  Substitute `(2)` into the affine source term:

```text
beta(q_alpha^EG-alpha n_alpha)
 -alpha(q_beta^EG-beta n_beta)

 =beta q_alpha^EG-alpha q_beta^EG
   +alpha beta(n_beta-n_alpha).                         (11)
```

Division by `beta-alpha` proves `(3)--(4)`.  Formula `(1)` then gives `(5)`, and division by the
nonzero central jets gives `(6)`.

## Exact finite-resolvent tangent form

Put `d_alpha=W_alpha'(0)`.  Suppose the second resolvent identity is written in characteristic
gauge as

```text
W_beta=W_alpha+(beta-alpha)J,
W_beta'(0)=d_alpha+(beta-alpha)J'(0).                   (12)
```

Then

```text
d_alpha W_beta-W_beta'(0)W_alpha
 =(beta-alpha)[d_alpha J-J'(0)W_alpha].                 (13)
```

Combining `(5)` and `(13)` cancels the shift denominator exactly:

```text
N_(alpha,beta)(z)
 =alpha beta sin(az)/(2z)
   [d_alpha J(z)-J'(0)W_alpha(z)]
   /[W_alpha(z)W_beta(z)].                              (14)
```

The bracket in `(14)` is a centered projective tangent: its value and first jet at zero vanish.
It is the full-frequency datum discarded by the old central-only cancellation argument.

## Why central cancellation remains correct

Every odd characteristic with simple center has

```text
W(z)=W'(0)z+O(z^3).
```

Therefore `(1)` gives

```text
n_(a,W)(z)=-a/(2z)+O(z).                                (15)
```

The pole in `(15)` is universal, independent of the shift and source.  Consequently
`n_beta-n_alpha=O(z)` and `N_(alpha,beta)` has zero central residue.  This recovers the corpus's
central Neumann cancellation exactly while proving that its extension to the whole function was
false.

If

```text
W(z)=d z+e z^3+O(z^5),
kappa(W)=e/d=W'''(0)/(6W'(0)),                           (16)
```

then the first surviving term is

```text
N_(alpha,beta)(z)
 =alpha beta a/[2(beta-alpha)]
    [kappa(W_beta)-kappa(W_alpha)]z+O(z^3).              (17)
```

Thus normalized cubic characteristic curvature, not the central residue, is the first Neumann
observable seen by the full Pick kernel.

## Far-negative dyadic persistence theorem

The holonomy is not merely nonzero at finite shift.  Dyadic extrapolation preserves its first
projective tangent at order one.

Write `lambda=-L`, `epsilon=1/L`, and remove the harmless scalar `1/L` from the resolvent source:

```text
u_epsilon=(I+epsilon A_a)^(-1)e^x
          =e^x-epsilon A_a e^x+o(epsilon)              (P1)
```

in `L2(-a,a)`.  The source-domain theorem in
`suzuki-boundary-log-nonclock-nonflat-tangent.md` proves `(P1)` unconditionally.  Let
`W_epsilon` be the odd phase-one characteristic built from `u_epsilon` and its reflection, and
normalize its central jet:

```text
What_epsilon(z)=W_epsilon(z)/W_epsilon'(0).             (P2)
```

Compact Fourier functionals turn `(P1)` into a locally uniform expansion

```text
What_epsilon=What_0+epsilon dotWhat_0+o(epsilon).       (P3)
```

For the free source `e^x`, direct integration gives

```text
W_0(z)=4 cosh(a) sin(az),
What_0(z)=sin(az)/a.                                    (P4)
```

At the dyadic pair `alpha=-2L`, `beta=-L`, formula `(6)` becomes

```text
N_L(z)=L sin(az)/z
 [1/What_(1/(2L))(z)-1/What_(1/L)(z)].                 (P5)
```

For every compact set away from `z=0` and the free clock divisor, `(P3)` and differentiation of
the reciprocal give

```text
N_L(z) -> N_infty(z)
 :=sin(az)/(2z) * dotWhat_0(z)/What_0(z)^2              (P6)
  =a^2/[2z sin(az)] * dotWhat_0(z).                     (P7)
```

This is locally uniform meromorphic convergence.  In raw characteristic gauge write

```text
W_epsilon=W_0-epsilon K+o(epsilon),
d_0=W_0'(0), k=K'(0).                                   (P8)
```

Then

```text
dotWhat_0=-(d_0 K-kW_0)/d_0^2,
N_infty(z)
 =-sin(az)/(2z) [d_0K(z)-kW_0(z)]/W_0(z)^2.            (P9)
```

### Nonvanishing

The centered phase-one tangent in `(P9)` is not identically zero.  Suppose otherwise.  Then
`K=(k/d_0)W_0`.  Put

```text
f=A_a e^x-(k/d_0)e^x.
```

Vanishing of its phase-one characteristic says, after inverse Fourier transformation of the
first-order bracket,

```text
f_odd=(f_even)'.                                        (P10)
```

The exact endpoint theorem for `A_a e^x` gives, near `a-`,

```text
f(x)=-(1/2)e^x log(a^2-x^2)+R(x),                       (P11)
```

where `R` is `C1` near the endpoint.  Consequently

```text
f_odd(x)=-(1/2)sinh(x)log(a^2-x^2)+O(1),

(f_even)'(x)
 =-(1/2)sinh(x)log(a^2-x^2)
   +x cosh(x)/(a^2-x^2)+O(1).                          (P12)
```

The rational term in the second line diverges like `1/[2(a-x)]` and cannot be canceled by the
first line, contradicting `(P10)`.  Therefore

```text
dotWhat_0 is not identically zero,
N_infty is not identically zero.                        (P13)
```

Far-negative dyadic sewing therefore does not wash out the comparison channel.  It converts
infinitesimal projective shift motion into a finite meromorphic response.  That response is built
from `A_a e^x`, whose endpoint finite-part term and finite von-Mangoldt packet are already
source-explicit in the corpus.

## Consequence for the RH frontier

Let

```text
m_jump=-M_0+[beta q_alpha-alpha q_beta]/(beta-alpha),
m_EG  =-M_0+[beta q_alpha^EG-alpha q_beta^EG]/(beta-alpha).
```

Equations `(3)--(5)` give

```text
m_jump=m_EG+N_(alpha,beta),
K_jump=K_(m_EG)+K_(N_(alpha,beta)).                     (18)
```

The old proposed factorization omitted the second kernel in `(18)`.  Correct stronger
conjecture is the holonomy-compensated square

```text
K_(m_EG)+K_(N_(alpha,beta))=B_(alpha,beta)^*B_(alpha,beta). (19)
```

This is not a cosmetic correction.  `K_(N)` can have nonzero linear and higher Pick data even
when its central residue vanishes.  The finite resolvent identity supplies `(14)`, while
`(P6)--(P13)` prove its large-negative dyadic limit exists and is genuinely nonzero.  The term is
source-before-divisor and is eligible to be part of a genuine square producer.

## Hostile tests

- Physical triangle must be multiplied by `-i`; omitting it reverses `(1)`.
- Source dependence on `lambda` is retained through `W_lambda`; it cannot be pulled outside
  affine sewing.
- Central cancellation tests only the universal principal part `(15)`, not the function.
- Common source rescaling cancels from `W'(0)/W(z)`.
- A proof setting `N_(alpha,beta)=0` must prove normalized-characteristic equality, contradicting
  the corpus's non-flat finite-shift mechanism unless the source degenerates.
- No sign is asserted for `K_(N)` alone.  Positivity target is compensated sum `(19)`.
- Functional-equation--Schwarz orbit insertion still changes `M_0` without changing abstract
  finite characteristics; it must break the completed identity `(19)` in the Euler--Gamma term.

## Novelty audit

Suzuki 2023 supplies the one-sided screw transform.  Suzuki 2026 supplies the shifted positive
forms, deficiency characteristics, and finite Neumann kernel.  Neither paper defines the
two-shift Carleman sheet jump, performs affine triangle sewing, or states `(1)--(18)`.  Corpus had
the central moment cancellation and finite projective shift holonomy separately, but incorrectly
extrapolated central cancellation to the proposed full-frequency square.  Claimed new content is
their exact synthesis into the Neumann holonomy survivor.  Priority remains unverified.

## Formal status

`formal/GaloisForLFunctions/RHTower/SuzukiFullFrequencyNeumannHolonomy.lean` proves the exact
algebraic layer `(3)--(6)`, `(12)--(14)`, the centered-pole cancellation identity, dyadic
specialization, Pick-kernel split `(18)`, projective-cancellation rigidity, and the exact dyadic
reciprocal-secant derivative limit used in `(P6)--(P8)`.  It also proves the pointwise smoothing identity
`sgn(t)(-|t|/2)=-t/2` behind `(7)`.

The passage `(7)--(10)`, and `(1)` itself, are **now also formal** for a signed-measure source; see
the 2026-08-01 log entries below.  `(7)` is `momentFunctional_neumannResponseDifference`, `(8)` is
`half_integral_neumannResponseDifference_eq_sineKernel` over
`HTGeometry/CompactFourierSineKernel.lean`, `(9)` is `deriv_signedCharFun_zero` in
`HTGeometry/SignedCharFunCentralJet.lean`, `(10)` is `oddPart_div_of_odd`, and their assembly into
`(1)` is `oddPart_normalizedResponse_eq`.  Only linearity, a vanishing zeroth moment and a first
moment are used — no distribution of order above a measure — which is why no distribution triangle
was needed.  What is still not represented in Lean is a source of higher distributional order,
which this card's argument never invokes.

## Log

- 2026-07-22 — hostile full-frequency audit found central-only cancellation had been extrapolated
  beyond its proof; exact Neumann holonomy survivor derived and paper proof closed.
- 2026-07-22 — axiom-free Lean algebraic/Pick connector passed direct checking; analytic compact
  distribution triangle-to-response bridge remains the exact formalization boundary.
- 2026-07-22 — formalized dyadic reciprocal-secant limit with exact factor `1/2`, closing the
  analytic amplification engine from first characteristic motion to order-one holonomy.

### Lean progress — the Nonvanishing step's engine `(P12)` FORMALIZED

The Formal status section correctly records that the compact-distributional Fourier passage
`(7)--(10)` awaits a Lean representation of Suzuki's distribution triangle. The **Nonvanishing**
argument `(P10)--(P13)` does not depend on that interface: once `(P11)` is granted, the
contradiction is pure real analysis at the endpoint — a logarithmic singularity cannot cancel a
simple pole. That engine is now formal, in
`RHTower/SuzukiFiniteShiftNonClock.lean` (the module that already owns the endpoint log layer used
by `(P11)`), [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `tendsto_sub_mul_suzukiBoundaryLog` : `(a - x) * log (a^2 - x^2) -> 0` as `x -> a⁻`, i.e. the
  endpoint logarithm is `o(1/(a-x))`. Proof: factor `a^2 - x^2 = (a-x)(a+x)` and use mathlib's
  `Real.continuous_mul_log` (continuity of `u * log u` at `0`) on the first factor.
- `tendsto_sub_mul_suzukiBoundaryPole` : `(a - x) * (x cosh x/(a^2 - x^2)) -> cosh a / 2 ≠ 0` — the
  pole reaches the rate the logarithm misses.
- `suzukiBoundaryPole_ne_log_add_bounded` : **`(P12)` itself.** There is no eventual identity
  `x cosh x/(a^2 - x^2) = c(x) log(a^2 - x^2) + R(x)` near `a⁻` with `c` and `R` having finite
  endpoint limits. The coefficient `c` is allowed to vary — which is what the card needs, since its
  log coefficient is `-(1/2) sinh x`, not a constant.

So `(P13)` now rests only on `(P11)` and the distributional passage, not on any unformalized
estimate: the "rational term diverges like `1/[2(a-x)]` and cannot be canceled" sentence is a
theorem.

### Lean progress — `(8)` and `(10)` do not need the distribution interface

The Formal status section treats `(7)--(10)` as one block awaiting Suzuki's distribution triangle
in Lean. Re-reading them separately, only `(7)` and `(9)` pair a distribution against a test
function. `(8)` and `(10)` are elementary once `(7)` is granted:

- `(8)` is the Fourier transform of a **constant** `mu_1/2` over `[-a,a]` — an interval integral of
  an exponential, no distribution anywhere;
- `(10)` is the parity algebra of a quotient whose denominator is odd.

Both are now formal, as reusable analysis in `HTGeometry/CompactFourierSineKernel.lean`
[PROVED HERE], wired into the `HTGeometry` umbrella, standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `integral_const_mul_exp_mul_I_symm` : `∫ y in -a..a, c * exp (I z y) = c * (2 sin (a z) / z)` for
  `z ≠ 0`. Composing with `(7)`'s value `mu_1/2` and the leading `1/2` gives exactly `(8)`'s
  `mu_1 sin(az)/(2z)`. Proof: `integral_exp_mul_complex` plus `Complex.two_sinh` through
  `Complex.sinh_mul_I`.
- `tendsto_sineKernel_nhdsNE_zero` : the sine kernel is regular at the origin with value `2a`,
  which is what makes the `(8)`-`(9)` central-jet division legitimate.
- `oddPart_div_of_odd` : **`(10)` itself** — for `W(-z) = -W(z)`, the odd part of `F/W` equals the
  even part of `F` divided by `W`.
- `evenPart_div_of_odd` : the companion identity.

The formalization boundary of this card is therefore narrower than recorded: it is `(7)` and `(9)`
alone — the two genuine distribution pairings — not the whole `(7)--(10)` passage.

### Lean progress — `(7)` FORMALIZED on the corpus moment functional

`(7)` does not need a general distribution theory either. Its whole content is: linearity of the
pairing, applied to the **smooth** kernel `sgn(t) r_0(t) = -t/2` (the smoothing identity is already
formal), plus `mu_0 = 0` from oddness. The corpus already owns the right vehicle —
`HTGeometry/MomentFunctionalPositivity.lean`'s `momentFunctional s p = ∑ₖ aₖ sₖ`, with additivity,
`smul`, and `momentFunctional_X_pow` — so no new source theory was needed.

Added to `RHTower/SuzukiFullFrequencyNeumannHolonomy.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `IsOddSourceMoments` : an odd source is one with all even moments vanishing; `.zeroth` extracts
  `mu_0 = 0`.
- `momentFunctional_C` : the moment functional of a constant is that constant times `mu_0`.
- `momentFunctional_neumannResponseDifference` : **`(7)` itself** —
  `⟨nu, (y - x)/2⟩ = mu_1 / 2` for an odd source, for every `x`.
- `momentFunctional_neumannResponseDifference_const` : the response is independent of `x`. This
  constancy is the property `(8)` consumes, stated separately because it is what makes the Fourier
  transform in `(8)` the transform of a *constant*.
- `half_integral_neumannResponseDifference_eq_sineKernel` : `(7)` composed with `(8)` —
  half the compact Fourier transform of that constant over `[-a,a]` is
  `mu_1 sin(a z)/(2 z)`, exactly the card's `(8)`.

**Revised formalization boundary.**  Of the `(7)--(10)` passage, `(7)`, `(8)` and `(10)` are now
formal. The only remaining item is `(9)` — `W'(0) = i mu_1` — which differentiates the compact
Fourier transform of the source itself under the pairing, and is the one step that genuinely needs
Suzuki's distribution triangle in Lean.

### Lean progress — `(9)` FORMALIZED for a signed measure source; `(7)--(10)` closed

`(9)` was the last item of the passage. It is a theorem about differentiating a characteristic
function at the origin, and mathlib already carries that: `iteratedDeriv_charFun_zero` gives
`iteratedDeriv n (charFun mu) 0 = I^n * ∫ x^n dmu`. The only thing missing was the **signed** case —
`charFun` is defined for nonnegative measures, while an odd source is necessarily signed.

New reusable module `HTGeometry/SignedCharFunCentralJet.lean` [PROVED HERE], wired into the
`HTGeometry` umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `signedCharFun mp mn = charFun mp - charFun mn` : the characteristic of a signed source presented
  as a difference of two finite measures (every finite signed measure is such a difference).
- `contDiff_signedCharFun` : it is `C^1` when both parts have a first moment.
- `deriv_signedCharFun_zero` : **`(9)` itself** — `W'(0) = I * (∫x dmp - ∫x dmn) = I mu_1`.
- `signedCharFun_reflected_odd` : if the negative part is the reflection of the positive part — i.e.
  the source is **odd** — then `W(-t) = -W(t)`. This is exactly the hypothesis `(10)` consumes, so
  `(9)` and `(10)` now compose without an extra assumption.

**Passage `(7)--(10)` is now formal in full** for a signed-measure source: `(7)` on the moment
functional, `(8)` as the compact Fourier transform of the resulting constant, `(9)` as the central
jet above, `(10)` as the parity identity. The card's Formal status paragraph, which recorded the
whole passage as awaiting a Lean distribution triangle, is superseded: what is still not represented
is a source of distributional order above a measure, which the card's own argument never uses —
`(7)` needs only linearity and a vanishing zeroth moment, and `(9)` needs only a first moment.

### Lean progress — `(1)` assembled from `(8)`--`(10)`

With `(8)`, `(9)` and `(10)` formal, the card's own sentence *"substitution of `(8)--(9)` into
`(10)` proves `(1)`"* is now a Lean theorem. Added to
`HTGeometry/CompactFourierSineKernel.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `oddPart_normalizedResponse_eq` : for an odd denominator `W` with `W z ≠ 0`, a numerator whose
  even part is the sine kernel carrying `mu_1`, and a central jet `d = I mu_1`,

  `Odd_z[(-i T)/W](z) = -d sin(a z) / (2 z W(z))`,

  which is exactly `(1)` — the formula in this module's own header docstring. The mechanism is
  `-i * mu_1 = -d` after substituting the jet identity; no analysis is used beyond the two inputs,
  which is the point: `(1)` is an algebraic consequence of the even-part computation and the
  central-jet identification, both of which are now proved rather than assumed.

It is stated generically (in `T`, `W`, `a`, `mu_1`, `d`) so that instantiating it needs only the
card's own objects. Kept in the light `CompactFourierSineKernel` module deliberately: the Suzuki
module's import cone costs ~3.5 minutes per typecheck, so generic algebra iterates there instead.
