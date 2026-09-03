# Restricted-unitary cubic relative index

- **ID:** ULF-RUCRI-001
- **Stage:** 2-fully-proven
- **Type:** unconditional operator theorem + exact arithmetic source identity
- **Purpose:** construct one pre-divisor, prime-mixed, integral--nuclear homotopy defect and
  identify why cubic source laws are forced at critical Hardy regularity.

## Provenance boundary

The generic implication

```text
P-Q in S_(2m+1)  ==>  Tr(P-Q)^(2m+1)=relative index(P,Q)
```

is classical (Avron--Seiler--Simon, *The Index of a Pair of Projections*, 1994).  The new claim
here is not that abstract theorem.  It is the corpus-native identification of `m=1` as the first
available degree at the proved `S_2` Hardy boundary, the realization of that cubic character as
one pre-divisor prime-mixed integral kernel, and its exact fusion with the Gaussian Euler,
continuum-anomaly, Route-P, and Burnol source clocks.

## 1. Object

`ULF-FACHD-001` supplies the preferred arithmetic representative: replace the bare reference
projection `P` by the zero-free Gaussian Euler--continuum polarization `R_(D,x)`.  The resulting
relative defect `(R_(D,0)-R_(D,x))^3` has the same integral trace but is literally the homotopy
defect from source formation to singular completion.  The one-endpoint form below is the generic
normal form used to prove it.

Let `H` be a separable complex Hilbert space, `P` an orthogonal projection, and `U` a unitary with

```text
[P,U] in S_2.
```

Put

```text
R_U = U* P U,
Delta_U = R_U - P,
T(U) = Delta_U^3.                                      (RUCRI.1)
```

For a circle phase `u` acting by multiplication, `P` is the Hardy projection.  If `u` is formed
by exponentiating the full Euler--Gamma boundary current before compression, `T(M_u)` is
pre-divisor and prime-mixed: it is not a direct sum of one-prime defects.

## 2. Cubic relative-index theorem

**Theorem RUCRI-A.** Under `(RUCRI.1)`:

1. `Delta_U` is self-adjoint and Hilbert--Schmidt.
2. `T(U)` is self-adjoint and trace class.
3. One has the exact positive-channel decomposition

   ```text
   Delta_U^3
     = R_U (1-P) R_U - P (1-R_U) P.                    (RUCRI.2)
   ```

4. Its trace is the integer relative index

   ```text
   Tr T(U)
     = dim(R_U H intersect (1-P)H)
       - dim(PH intersect (1-R_U)H)
     = -index(P U P : PH -> PH).                       (RUCRI.3)
   ```

5. If `U=M_u` for a piecewise `C1` unitary circle phase, then

   ```text
   Tr T(M_u)
     = ||Q M_(conj u) P||_HS^2 - ||Q M_u P||_HS^2
     = wind(u).                                         (RUCRI.4)
   ```

6. If `U_t` is continuous in operator norm and `[P,U_t]` is continuous in `S_2`, then
   `T(U_t)` is continuous in `S_1` and `Tr T(U_t)` is constant.

**Proof.** Since

```text
Delta_U = U* [P,U],
```

it is Hilbert--Schmidt; it is self-adjoint because `P` and `R_U` are projections.  Two
Hilbert--Schmidt factors have trace-class product, so `Delta_U^3` is trace class.  Expanding with
`P^2=P` and `R_U^2=R_U` gives

```text
(R_U-P)^3 = R_U-P-R_U P R_U+P R_U P,
```

which is `(RUCRI.2)`.

For completeness, use the canonical two-projection decomposition.  Apart from the four
intersection spaces, the generic part is `K directSum K`, on which

```text
P   = [[1,0],[0,0]],
R_U = [[C^2,CS],[CS,S^2]],
```

for commuting positive contractions `C,S` with `C^2+S^2=1`.  On this generic part the nonzero
eigenvalues of `R_U-P` occur in pairs `+S,-S`; hence every trace-class odd power has zero generic
trace.  The `+1` eigenspace is `R_U H intersect (1-P)H`, and the `-1` eigenspace is
`PH intersect (1-R_U)H`.  Hilbert--Schmidt displacement makes both endpoint spaces
finite-dimensional.  This proves the first equality in `(RUCRI.3)`.  Conjugating the Fredholm
pair by `U` identifies its relative index with the negative Fredholm index of `PUP`, proving the
second.

Let `Q=1-P`.  Cyclicity of the trace and unitary invariance give

```text
Tr(R_U Q R_U) = ||Q U* P||_HS^2,
Tr(P (1-R_U) P) = ||Q U P||_HS^2.
```

For `U=M_u` these are the two Hankel seams.  Their Fourier traces are respectively
`sum_(n>=1) n |uHat(n)|^2` and `sum_(n>=1) n |uHat(-n)|^2`; their difference is the Fourier degree
formula, proving `(RUCRI.4)`.

Finally, multiplication and ideal Holder inequalities make `Delta -> Delta^3` continuous from
`S_2` to `S_1` on bounded sets.  The trace is therefore continuous along the stated homotopy, but
`(RUCRI.3)` makes it integer-valued, so it is constant.  QED.

## 3. Integral-kernel form and genuine prime mixing

On `L2(S1)`, write the Szego kernel of `P` as `K_P(z,w)`.  The displacement has the `L2` kernel

```text
d_u(z,w) = (conj(u(z))*u(w)-1) K_P(z,w).               (RUCRI.5)
```

The cancellation in the numerator is exactly the `H^(1/2)` condition.  Consequently `T(M_u)` is
the nuclear integral operator with kernel

```text
t_u(z,w) = integral integral
  d_u(z,z1) d_u(z1,z2) d_u(z2,w) dz1 dz2.              (RUCRI.6)
```

For the zero-free Gaussian Euler--continuum formation `Phi_x` of `ULF-GECRF-001`, the normalized
boundary phase has exponent

```text
Im(log h_infinity + A_x
   + sum_(n>=2) (Lambda(n)/log n) exp(-pi*x*n^2) n^(-s)).
```

Thus the factor `conj(u_x(z))*u_x(w)-1` in `(RUCRI.5)` is the exponential of one sum over all
prime powers.  Its power-series expansion contains mixed monomials with distinct prime labels
before any Hardy compression.  Equations `(RUCRI.5)`--`(RUCRI.6)` therefore give a literal
prime-mixed integral kernel, not a sum of local indices.

Every finite `x>0` phase is zero-winding, hence `Tr T(M_(u_x))=0`.  A nonzero completed trace can
arise only if the formation path fails to be proper in the restricted metric; it is precisely the
integral charge lost at the completion corona.

## 4. Minimality of cubic grade

**Theorem RUCRI-B.** In the critical topology `Delta in S_2`, cubic degree is the first polynomial
grade that is simultaneously:

```text
defined by an ordinary nuclear trace,
odd under orientation reversal Delta -> -Delta,
capable of retaining relative index.
```

**Proof.** A linear trace is unavailable because an arbitrary `S_2` displacement need not be
trace class.  The square is trace class but even, so reflection cannot orient it.  The cube is
trace class, odd, and has integer trace by RUCRI-A.  No smaller degree satisfies all three
requirements.  QED.

This explains a corpus-wide pattern: quadratic positivity sees unsigned pair-production energy,
linear logarithmic currents retain orientation but are non-nuclear, and cubic Green/Cauchy laws
are the first place where orientation and nuclearity can coexist.

## 5. Exact safe-Euler Gamma-clock identity

Let

```text
J(t) = sum_(n>=2) Lambda(n) n^(-(1+t))
     = -zeta'(1+t)/zeta(1+t),        t>0.
```

Let `B_base` be the complete Route-P primitive base Cauchy-cubic budget.  Corpus identities reduce
its natural-number atom exactly to

```text
routePPrimeGammaBaseCubicWeight(n)
  = Lambda(n)/(4*n*log(n)^3).                          (RUCRI.7)
```

**Theorem RUCRI-C.** One has

```text
B_base
  = (1/8) integral_0^infinity t^2 J(t) dt
  = (1/4) sum_(n>=2) Lambda(n)/(n*log(n)^3)
  < 1.                                                  (RUCRI.8)
```

**Proof.** For `n>=2`, the Gamma integral gives

```text
integral_0^infinity t^2 n^(-t) dt = 2/log(n)^3.
```

Every integrand is nonnegative, so Tonelli permits exchange of sum and integral.  This gives the
first two equalities.  Equation `(RUCRI.7)` follows from the exact corpus constants
`(216/115)*(115/864)=1/4`; summing and using
`tsum_routePPrimeGammaBaseCubicWeight_eq_budget` identifies the result with `B_base`.
`routePPrimitiveBaseCauchyCubicTraceBudget_lt_one` supplies the strict inequality.  QED.

Equivalently, if `G` is the prime-log generator, then

```text
G^(-3) = (1/2) integral_0^infinity t^2 exp(-tG) dt.
```

The source budget is therefore the third inverse moment of the same safe contraction semigroup
that the Burnol aperture colligation diagonalizes.  The corpus additionally proves that this
colligation preserves every complex matrix coefficient and splits lost energy into explicit
boundary and cocycle channels.  Cubic target index and cubic source capacity are consequently at
the same summability and homotopy grade.

## 6. Gaussian--aperture subordination

The preceding safe current is not external to the Gaussian formation.  Put

```text
Theta_Lambda(x) = J_x(1)
  = sum_(n>=2) Lambda(n) exp(-pi*x*n^2)/n,

Theta_0(x) = M_x(1)
  = integral_1^infinity exp(-pi*x*u^2)/u du.
```

**Theorem RUCRI-D.** For every `t>0`,

```text
J(t)
  = pi^(t/2)/Gamma(t/2)
      * integral_0^infinity x^(t/2-1) Theta_Lambda(x) dx,       (RUCRI.9)

1/t
  = pi^(t/2)/Gamma(t/2)
      * integral_0^infinity x^(t/2-1) Theta_0(x) dx,            (RUCRI.10)

J(t)-1/t
  = pi^(t/2)/Gamma(t/2)
      * integral_0^infinity x^(t/2-1)
          (Theta_Lambda(x)-Theta_0(x)) dx.                       (RUCRI.11)
```

Consequently

```text
B_base = integral_0^infinity K_3(x) Theta_Lambda(x) dx,         (RUCRI.12)

K_3(x) = (1/8) integral_0^infinity
  t^2 pi^(t/2)/Gamma(t/2) x^(t/2-1) dt >= 0.
```

**Proof.** The elementary Gaussian Mellin integral is

```text
integral_0^infinity x^(t/2-1) exp(-pi*n^2*x) dx
  = Gamma(t/2) pi^(-t/2) n^(-t).
```

All terms in `Theta_Lambda` are nonnegative, so Tonelli gives `(RUCRI.9)`.  Applying the same
identity under the positive `u` integral and using
`integral_1^infinity u^(-(1+t))du=1/t` gives `(RUCRI.10)`; subtraction gives `(RUCRI.11)`.
Insert `(RUCRI.9)` into `(RUCRI.8)` and apply Tonelli again to obtain `(RUCRI.12)`.  QED.

This is the exact source-level fusion previously missing.  The additive theta clock `x`, the
multiplicative aperture clock `t`, the unsquared von-Mangoldt current, and the continuum anomaly
are four transforms of one formation law.  The continuum begins at log-frequency zero and yields
the non-trace-class pole `1/t`; literal integers begin at `n=2`, hence have the positive log gap
`log 2`.  The cubic source capacity is a positive functional of the same Gaussian current that
appears in `logDeriv Phi_x`, not an independently imported Route-P scalar.

## 7. Source action as total colligation flux

Let `C_B` be the positive trace-class label Gram operator of the complete primitive Burnol
synthesis, so `Tr C_B=B_base`.  Let `D_c` be the diagonal Burnol semigroup on primitive labels.
Its full eigenvalue at log-frequency/ordinate `(log n,kappa)` is
`exp(-c*(log n + i*kappa))`, and its energy multiplier is `n^(-2c)`.  Matrix-complete Burnol
colligation gives a positive defect covariance

```text
C_def(c) = C_B - D_c* C_B D_c >= 0.                    (RUCRI.13)
```

**Theorem RUCRI-E.** For `c>=0`,

```text
Tr C_def(c)
  = sum_(n>=2) (1-n^(-2c)) Lambda(n)/(4*n*log(n)^3),   (RUCRI.14)

d/dc Tr C_def(c)
  = F(c)
  = sum_(n>=2) Lambda(n)n^(-(1+2c))/(2*log(n)^2),      (RUCRI.15)

B_base = integral_0^infinity F(c) dc.                  (RUCRI.16)
```

Moreover `(RUCRI.13)` is an operator identity before taking trace: its two positive summands are
the deleted-boundary and distributed-cocycle Gram channels of the Burnol colligation, so mixed
prime matrix coefficients remain present.

**Proof.** The corpus identifies each diagonal of `C_B` with
`Lambda(n)/(4*n*log(n)^3)` and proves full matrix colligation.  Multiplication by `D_c` changes its
diagonal by `n^(-2c)`, proving `(RUCRI.14)`.  Termwise differentiation is justified by the
summable quadratic Green flux already proved in
`RoutePPrimitiveBurnolApertureDefectFirstFlux`; it gives `(RUCRI.15)`.  Positivity permits Tonelli,
and

```text
integral_0^infinity n^(-2c)/(2*log(n)^2) dc
  = 1/(4*log(n)^3),
```

which proves `(RUCRI.16)`.  QED.

The source budget is therefore not merely a static number.  It is the total positive action
dissipated by a matrix-complete one-sided homotopy.  The target `Tr T_D` is the integral boundary
charge of another one-sided homotopy.  The remaining theorem is a source-forced bulk-to-boundary
action inequality between these two homotopies.

## 8. Exact remaining RH edge

For a strict-right rational rectangle `D`, let `u_D` be the pre-divisor completed boundary phase
obtained as the formation limit, and set

```text
T_D = (M_(u_D)* P M_(u_D) - P)^3.                       (RUCRI.17)
```

The corpus source-current contour law and RUCRI-A give

```text
Tr T_D = enclosed strict-right Xi multiplicity.         (RUCRI.18)
```

Thus RH follows from the single source-side cyclic domination

```text
0 <= Tr T_D <= B_base < 1.                              (RUCRI.19)
```

`(RUCRI.19)` is not proved here.  It is substantially narrower than an unspecified
source-to-resolvent landing: both sides now have forced cubic provenance.  The required map is a
degree-three cyclic transgression from the matrix-complete Burnol source colligation to the
restricted Hardy projection pair.  It need not, and by the corpus no-go cannot, be a bounded
one-particle landing.  Any proof must be constructed before divisor specialization from the
Gaussian Euler--continuum formation.

## 9. Lean status

Paper proof dependency-closed.  Lean formalization intentionally deferred during current
corpus-audit phase.
