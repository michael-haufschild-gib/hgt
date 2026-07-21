# Suzuki arithmetic tangent and inverse-moment holography

- **ID:** `suzuki-arithmetic-tangent-inverse-moment-holography`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / RESTRICTED-WEIL SOURCE RESPONSE / SPECTRAL RECONSTRUCTION
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED]`
  `[GENERIC PERTURBATION AND MOMENT DETERMINACY CLASSICAL] [NOT AN RH PROOF]`
- **Primary source:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), Theorem 1.5 and Sections 6--8.

## 1. Exact setup

Fix `a>0` and an admissible shift `lambda<lambda_a`.  Let `nu` be the spectral probability of the
normalized positive deficiency vector for Suzuki's canonical even extension, as identified in
`suzuki-donoghue-defect-spectral-measure-law.md`.  Its Donoghue function is

```text
R_nu(z) = integral_R 1/(t-z) dnu(t),
m_nu(z) = z + (z^2+1) R_nu(z).                            (1)
```

The measure is even, pure atomic, and has no atom at zero.  At fixed aperture its support is closed
and discrete, hence is separated from zero.  Define its inverse even moments

```text
q_n(nu) = integral_R t^(-2n) dnu(t),       q_0=1.          (2)
```

All moments in `(2)` are finite because the support has a positive gap about zero.

For the far-negative shift chart, write `lambda=-r`, `epsilon=1/r`, and

```text
f_+(x)=e^x,
u_epsilon=(I+epsilon A_a)^(-1)f_+,
F_epsilon(z)=integral_(-a)^a u_epsilon(x)e^(izx) dx.       (3)
```

The scalar factor `epsilon` in `(A_a+rI)^(-1)=epsilon(I+epsilon A_a)^(-1)` cancels from Suzuki's
projective quotient.  Put

```text
F_0(z)=integral_(-a)^a e^x e^(izx) dx,
H_a(z)=integral_(-a)^a (A_a e^x)(x)e^(izx) dx,
h_a(z)=H_a(z)/F_0(z),
Delta_a(z)=h_a(-z)-h_a(z).                                (4)
```

Thus `Delta_a` is the anti-reflected normalized restricted-Weil matrix coefficient.  It vanishes
for a scalar operator and therefore removes exactly the projectively invisible common scale.

## 2. Theorem A: complete inverse-moment holography

For every `n>=0`,

```text
m_nu^(2n+1)(0)/(2n+1)! = q_n(nu)+q_(n+1)(nu).             (5)
```

Consequently the complete odd Taylor jet of `m_nu` at zero recovers all inverse moments by

```text
q_0=1,
q_(n+1)=m_nu^(2n+1)(0)/(2n+1)!-q_n.                       (6)
```

This moment sequence determines the entire even measure `nu`, not merely a finite spectral prefix.
Indeed, push `nu` forward by `t |-> t^(-2)`.  The resulting probability `rho_nu` is supported on the
compact interval `[0,delta^(-2)]`, where `delta=dist(0,supp nu)>0`, and

```text
integral y^n drho_nu(y)=q_n(nu).                           (7)
```

Compact moment determinacy gives `rho_nu` uniquely.  Evenness then recovers `nu`: each positive
radius receives half its mass at each sign.

The scale-free sequence

```text
kappa_n(nu)=q_n(nu)/q_1(nu)^n                              (8)
```

is invariant under every spectral dilation `t |-> c t`, `c>0`, because
`q_n |-> c^(-2n)q_n`.  Conversely, the complete sequence `(kappa_n)` determines the even zero-free
probability up to dilation.  It is the moment sequence of the canonical normalized observable

```text
Y_nu(t)=1/(q_1(nu)t^2),        integral Y_nu dnu=1.        (9)
```

Thus `(8)` is a complete projective spectral coordinate, not another finite Schur prefix.

The first two recovered quantities are

```text
q_1=m_nu'(0)-1,
q_2=m_nu'''(0)/6-q_1.                                    (10)
```

For Suzuki's source presentation `m=-i W_1/W_(-1)` with Fourier transform `F`, direct
differentiation at zero gives the especially small source observable

```text
q_1=-i F'(0)/F(0).                                        (11)
```

For the exact free clock `m_a^free(z)=coth(a)tan(az)`,

```text
q_1^free=a coth(a)-1,
q_2^free=(a^3/3)coth(a)-a coth(a)+1.                      (12)
```

Equality with a dilation of the free clock is therefore equivalent to equality of every
`kappa_n`; one unequal `kappa_n` is an exact non-clock certificate.

## 3. Proof of Theorem A

At a regular point, differentiation under the Cauchy transform gives

```text
R_nu^(j)(0)=j! integral_R t^(-j-1) dnu(t).                (13)
```

Set `r=2n+1`.  For `n>=1`, Leibniz's rule applied to `(1+z^2)R_nu(z)` leaves only the zeroth and
second derivatives of `1+z^2` at zero:

```text
m_nu^(r)(0)
 =R_nu^(r)(0)+r(r-1)R_nu^(r-2)(0)
 =r!q_(n+1)+r(r-1)(r-2)!q_n
 =r!(q_n+q_(n+1)).                                        (14)
```

For `n=0`, the derivative of the leading `z` supplies `q_0=1`, giving the same formula.  This proves
`(5)--(6)`.  Equations `(7)--(9)` follow from compact moment determinacy and change of variables.
Equations `(10)--(12)` are direct substitutions into `(5)`.

## 4. Theorem B: first arithmetic tangent away from the free clock

For `|epsilon|<||A_a||^(-1)`, the bounded resolvent has the operator-norm expansion

```text
(I+epsilon A_a)^(-1)=I-epsilon A_a+O(epsilon^2).
```

Consequently, locally uniformly in `z`,

```text
F_epsilon(z)=F_0(z)-epsilon H_a(z)+O(epsilon^2).           (15)
```

Let

```text
Theta_epsilon(z)
 =(z-i)F_epsilon(z)/((z+i)F_epsilon(-z)),
m_epsilon(z)=i(1+Theta_epsilon(z))/(1-Theta_epsilon(z)).   (16)
```

Away from the displayed denominators and the free clock poles, the exact first variations are

```text
dot Theta_a(z)=Theta_a^free(z) Delta_a(z),                (17)

dot m_a(z)
 =2i Theta_a^free(z) Delta_a(z)/(1-Theta_a^free(z))^2.    (18)
```

In particular the first inverse-moment response is

```text
dot q_1(a)=dot m_a'(0)=i h_a'(0).                         (19)
```

Writing

```text
U_0=integral e^x dx,        M_1=integral x e^x dx,
U_A=integral A_a(e^x) dx,  M_(1,A)=integral x A_a(e^x) dx,
```

and using `q_1^free=M_1/U_0=a coth(a)-1`, equation `(19)` becomes the source-only law

```text
dot q_1(a)
 =-(M_(1,A)U_0-U_A M_1)/U_0^2
 =-(M_(1,A)-q_1^free U_A)/U_0.                            (20)
```

This is the centered restricted-Weil matrix coefficient which first bends the universal clock.
No arbitrary normalization remains.

There is also an exact atom-level response.  The free clock poles and phase speed are

```text
x_(a,k)=(k+1/2)pi/a,
phi_0'(x_(a,k))=2a tanh(a),
mu_(a,k)^free=coth(a)/a.                                  (21)
```

If `x_(a,k)(epsilon)` is the continued pole, implicit differentiation of
`Theta_epsilon(x_(a,k)(epsilon))=1` gives

```text
dot x_(a,k)=-Delta_a(x_(a,k))/(2ia tanh(a)).              (22)
```

The free phase speed is stationary in `x` at each clock pole.  Differentiating
`mu=2/phi'` therefore yields

```text
dot mu_(a,k)=i Delta_a'(x_(a,k))/(2a^2 tanh(a)^2).         (23)
```

For the Donoghue probability atom `p=mu/(1+x^2)`,

```text
dot p_(a,k)
 =dot mu_(a,k)/(1+x_(a,k)^2)
  -2x_(a,k)mu_(a,k)^free dot x_(a,k)/(1+x_(a,k)^2)^2.     (24)
```

Equations `(22)--(24)` identify, pole by pole, how the restricted-Weil source deforms clock
locations and weights before any cofinal limit is taken.

## 5. Proof of Theorem B

Equation `(15)` is the derivative of inversion at the identity, followed by the bounded Fourier
functional on `[-a,a]`.  Logarithmic differentiation of the quotient in `(16)` gives

```text
dot Theta/Theta
 =-H_a(z)/F_0(z)+H_a(-z)/F_0(-z)=Delta_a(z),              (25)
```

which is `(17)`.  The derivative of `i(1+w)/(1-w)` is `2i/(1-w)^2`, proving `(18)`.
Since `Delta_a(0)=0`, differentiating `(18)` at zero, where `Theta_a^free(0)=-1`, gives
`dot m_a'(0)=i h_a'(0)`.  Expanding `h_a'= (H_a'F_0-H_aF_0')/F_0^2` proves `(20)`.

At a free pole, `Theta_a^free=1` and `(Theta_a^free)'=2ia tanh(a)`.  This proves `(22)`.
Writing the boundary logarithmic derivative as `phi'=-i Theta'/Theta`, inserting `(17)`, and
using `(phi_0')'(x_(a,k))=0` gives `dot phi'=-i Delta_a'`; differentiating `2/phi'` proves
`(23)`, and the quotient rule proves `(24)`.

## 6. Scientific consequence

The far-negative boundary is no longer only a universal no-go.  It has a canonical arithmetic
outgoing direction:

```text
A_a
 -> H_a/F_0
 -> anti-reflected tangent Delta_a
 -> pole velocities and weight velocities
 -> complete projective inverse-moment response.          (26)
```

This is the first exact source producer for non-clock deformation in the Suzuki route.  It converts
the restricted-Weil operator directly into observable motion of the Donoghue spectrum.  The full
odd germ at zero is faithful to the entire even defect measure, so no finite-support or finite-jet
ambiguity remains after all orders are retained.

The live frontier is now precise: prove that the tangent field `Delta_a` has a source-derived
nonzero component which survives on an intrinsic cofinal intermediate shift schedule, then identify
the resulting atom motion with the Xi divisor.  Equations `(17)--(24)` provide the exact quantity
that such a theorem must propagate; generic Clark theory does not.

## 7. Hostile audit

1. **Classical parent theory.** Resolvent differentiation, quotient perturbation, Clark residues,
   and compact moment determinacy are classical.  Candidate novelty is their exact synthesis for
   Suzuki's restricted-Weil source, especially `(17)`, `(20)`, and the clock response `(22)--(24)`.
2. **No nonzero tangent is assumed.** A scalar `A_a` makes `Delta_a=0`; the theorem correctly
   records projective invisibility.  Proving source nonvanishing and cofinal survival remains open.
3. **No RH-bearing shift.** The expansion is taken at `lambda=-infinity` through
   `epsilon=(-lambda)^(-1)`.  It never inserts `lambda=0`.
4. **No finite-jet overclaim.** A finite prefix does not determine the measure.  Faithfulness uses
   every odd derivative plus compact determinacy of the reciprocal-square pushforward.
5. **No hidden zero atom.** The even extension divisor excludes zero; otherwise `(2)` would be
   undefined and the theorem would not apply.
6. **No cofinal conclusion.** A nonzero fixed-aperture tangent does not by itself prevent later
   homogenization.  The exact open core is persistence of `(26)` on one intrinsic schedule.

## 8. Literature and priority audit

- Suzuki's 2026 paper constructs the shifted finite-aperture characteristic family and states the
  cofinal spectral limit as a conjectural direction, but does not derive `(5)--(24)`.
- Livšic--Donoghue and Clark theory classically relate characteristic functions, Herglotz functions,
  spectral measures, residues, and phase derivatives.
- Search through 2026-07-21 found no Suzuki follow-up deriving a restricted-Weil free-boundary
  tangent, inverse-moment reconstruction, or clock atom-response law.
- Specialist priority review remains required.

## 9. Formalization target

Formalize the dependency-closed analytic core in
`formal/GaloisForLFunctions/RHTower/SuzukiArithmeticTangentHolography.lean`:

```text
iteratedDeriv_suzukiDonoghueTransform_odd_zero
suzukiInverseMomentReconstruction_eq
suzukiProjectiveMomentShape_geometricScale
hasDerivAt_suzukiFourierLivsic_freeBoundary
hasDerivAt_suzukiUpperCayleyInv_parameter
hasDerivAt_suzukiHerglotz_freeBoundary
```

The concrete operator expansion `(15)` and measure pushforward determinacy stay paper-level until
the restricted-Weil operator is represented in Lean.  They must not be replaced by an axiom or an
abstract wrapper claiming source construction.

## 10. Gates

- [x] exact odd-jet/inverse-moment law proved
- [x] complete projective determinacy proved
- [x] free first two inverse moments derived
- [x] restricted-Weil tangent derived
- [x] pole and atom response derived
- [x] RH circularity and projective-scalar attacks closed
- [x] current primary-source and literature search completed
- [x] scratch Lean proof of analytic connectors completed
- [ ] source nonvanishing/persistence theorem
- [ ] intrinsic cofinal intermediate shift
- [ ] Xi divisor weld
- [ ] specialist novelty review
- [ ] RH
