# Formation-anchored cubic homotopy defect

- **ID:** ULF-FACHD-001
- **Stage:** 2-fully-proven
- **Type:** unconditional operator theorem + corpus-native arithmetic specialization
- **Parents:** `ULF-GECRF-001`, `ULF-RUCRI-001`
- **Purpose:** construct one pre-divisor, prime-mixed, integral--nuclear defect whose two
  endpoints are literal Euler--theta formation and completed prime--Gamma formation.  The bare
  Hardy observer is no longer mistaken for the source endpoint.

## 1. The object

Fix an admissible positively oriented rectangle `D` compactly contained in
`1/2 < Re(s) < 1`, with a piecewise `C1` boundary parametrization `gamma_D : S1 -> boundary D`.
Let `P` be the Hardy projection on `L2(S1)`.

For `x>0`, let `Phi_x` be the zero-free Gaussian Euler--continuum formation from
`ULF-GECRF-001`:

```text
Phi_x(s)=h_infinity(s) exp(L_x(s)+A_x(s)),
L_x(s)=sum_(n>=2) Lambda(n)/log(n) exp(-pi*x*n^2)n^(-s),
A_x'(s)=integral_1^infinity exp(-pi*x*u^2)u^(-s)du.
```

Normalize its boundary phase at one basepoint:

```text
u_(D,x)(t)
  = Phi_x(gamma_D(t))/|Phi_x(gamma_D(t))|
    * |Phi_x(gamma_D(0))|/Phi_x(gamma_D(0)).             (FACHD.1)
```

Let `u_(D,0)` be the analogously normalized phase of the completed prime--Gamma carrier `xi`,
equivalently the parallel transport of `continuedPrimeArchSourceRelativeTrace` around `D`.
No zero, divisor list, inner factor, or zero ordinate enters either definition.

Write

```text
U_(D,x)=M_(u_(D,x)),
R_(D,x)=U_(D,x)* P U_(D,x).
```

The **formation-anchored cubic homotopy defect** is

```text
mathsf T_D
  = (R_(D,0)-R_(D,1))^3.                              (FACHD.2)
```

The value `x=1` only chooses one normalized Gaussian representative.  The nuclear homotopy class
and trace are independent of every positive anchor `x`; see Theorem FACHD-B.

This is one operator, not a direct sum of prime defects.  Euler coefficients are summed in
`L_x`, exponentiated into one phase, and only then Hardy-compressed.  Its integral kernel therefore
contains mixed monomials from distinct primes before the cubic composition.

## 2. Relative cubic theorem

For two unitary boundary phases `u,v`, put

```text
R_u=M_u* P M_u,
Delta_(u,v)=R_u-R_v,
T(u,v)=Delta_(u,v)^3.                                 (FACHD.3)
```

**Theorem FACHD-A.** If `[P,M_u]` and `[P,M_v]` are Hilbert--Schmidt, then:

1. `Delta_(u,v)` is self-adjoint and Hilbert--Schmidt;
2. `T(u,v)` is self-adjoint and trace class;
3. the exact two-channel identity holds:

   ```text
   T(u,v)
     = R_u(1-R_v)R_u - R_v(1-R_u)R_v;                 (FACHD.4)
   ```

4. its trace is the relative Fredholm index

   ```text
   Tr T(u,v)=index(R_u,R_v);                           (FACHD.5)
   ```

5. for piecewise `C1` circle phases,

   ```text
   Tr T(u,v)=wind(u)-wind(v)=wind(u*conj(v)) in Int.   (FACHD.6)
   ```

6. for any third admitted phase `w`, the trace is an exact homotopy cocycle:

   ```text
   Tr T(u,w)=Tr T(u,v)+Tr T(v,w).                      (FACHD.7)
   ```

**Proof.** Each `R` is a projection and

```text
R_u-R_v
  = M_u* [P,M_(u*conj(v))] M_v,
```

up to multiplication by unitaries; hence it is Hilbert--Schmidt.  It is self-adjoint because it
is a difference of projections.  Its square is trace class, so its cube is trace class and
self-adjoint.  Expanding the cube and using `R_u^2=R_u`, `R_v^2=R_v` gives `(FACHD.4)`.

The canonical two-projection decomposition pairs every generic eigenvalue `lambda` of
`R_u-R_v` with `-lambda`.  Only the finite-dimensional `+1` and `-1` endpoint spaces contribute
to an odd trace.  Their dimension difference is the relative Fredholm index, proving
`(FACHD.5)`.

Conjugate the pair by `M_v`.  The resulting pair is

```text
(M_(v*conj(u)) P M_(u*conj(v)), P),
```

which is the restricted-unitary displacement associated with the relative phase
`u*conj(v)`.  The Toeplitz index/Fourier degree identity from `ULF-RUCRI-001` gives
`(FACHD.6)`.  Relative Fredholm index is additive through an intermediate projection, proving
`(FACHD.7)`.  QED.

The operator itself is not falsely declared additive.  Its exact nuclear associator is

```text
Omega(u,v,w)=T(u,w)-T(u,v)-T(v,w) in S_1,              (FACHD.8)
Tr Omega(u,v,w)=0.
```

Thus `T` is a genuine operator-valued homotopy defect, while its trace is the integral abelianized
charge.  The traceless associator retains noncommutative matrix data discarded by the integer.

## 3. Integral-kernel form

Let `K_P(z,w)` denote the Szego kernel.  The Hilbert--Schmidt relative displacement has kernel

```text
d_(u,v)(z,w)
  = (conj(u(z))*u(w)-conj(v(z))*v(w)) K_P(z,w).         (FACHD.9)
```

Consequently `T(u,v)` is the nuclear integral operator with threefold cyclic kernel

```text
t_(u,v)(z,w)=integral integral
  d_(u,v)(z,z1)d_(u,v)(z1,z2)d_(u,v)(z2,w) dz1 dz2.   (FACHD.10)
```

For `u_(D,1)`, the numerator contains the exponential of the complete Gaussian-damped
von-Mangoldt sum.  Products in `(FACHD.10)` therefore contain cross-prime terms before trace.
The object is prime-mixed in its kernel, not merely in a scalar total.

## 4. Formation specialization

**Theorem FACHD-B.** The operator `mathsf T_D` in `(FACHD.2)` is pre-divisor, self-adjoint,
nuclear, prime-mixed, and has integral trace

```text
Tr mathsf T_D
  = wind(u_(D,0))-wind(u_(D,1))
  = wind(u_(D,0))
  = (1/(2*pi*i)) integral_(boundary D)
      continuedPrimeArchSourceRelativeTrace(s) ds
  = enclosed Xi multiplicity in D.                    (FACHD.11)
```

For every `x>0`, the alternative representative

```text
mathsf T_(D,x)=(R_(D,0)-R_(D,x))^3                    (FACHD.12)
```

is connected to `mathsf T_D` by a continuous trace-class homotopy and has the same trace.  For
all `x,y>0`,

```text
Tr(R_(D,x)-R_(D,y))^3=0.                              (FACHD.13)
```

**Proof.** `Phi_x` is holomorphic and zero-free on `Re(s)>0`; hence every `u_(D,x)` is piecewise
`C1`, belongs to the restricted unitary group, and has winding zero.  The completed carrier is
nonzero on the admissible boundary, so `u_(D,0)` has the same regularity.  FACHD-A gives
nuclearity, self-adjointness, and the first two equalities in `(FACHD.11)`.  The continued-source
identity and argument principle give its last two equalities.

On every compact positive `x` interval, Gaussian normal convergence holds together with all
boundary derivatives.  Thus `x -> u_(D,x)` is continuous in `C1`, hence in the restricted
`H^(1/2)` metric.  Projection differences vary continuously in `S_2`, and cubing varies
continuously from `S_2` to `S_1`; this proves anchor independence and `(FACHD.13)`.  QED.

## 5. What changed

The earlier representative `(R_(D,0)-P)^3` is correct but conceptually incomplete: `P` is the
additive observer, not literal arithmetic formation.  FACHD replaces the empty reference by the
zero-free Euler--continuum endpoint.  Exact cocycle conservation gives

```text
Tr(R_(D,0)-P)^3
  = Tr mathsf T_(D,x) + Tr(R_(D,x)-P)^3
  = Tr mathsf T_(D,x),                                 (FACHD.14)
```

because every finite Gaussian formation phase has zero winding.

Therefore a strict-right zero is precisely a component jump between two source-defined
polarizations:

```text
literal zero-free Euler--theta formation
  -- singular completion --> completed prime--Gamma formation,
component jump = Tr mathsf T_D.
```

This is the requested homotopy defect.  It is not yet the selection theorem.

## 6. Exact remaining RH edge

The direct sub-unit theorem is now an inequality on the same relative object:

```text
0 <= Tr mathsf T_D <= B_base < 1.                      (FACHD.15)
```

The left equality in `(FACHD.11)` makes `Tr mathsf T_D` an integer.  Thus `(FACHD.15)` forces it
to vanish for every strict-right rectangle and closes RH by functional-equation reflection.

No known theorem proves `(FACHD.15)`.  The missing construction remains a matrix-complete
degree-three transgression from Burnol/Gaussian source action to the two positive channels in
`(FACHD.4)`.  This card removes one false ambiguity: source and completion no longer live on
unrelated objects or unrelated boundaries.  Both endpoints are Hardy polarizations of phases on
the same `boundary D`; only the action domination is open.

## 7. Hostile audit

1. **Not a new abstract index theorem.** Odd traces of projection differences are classical.
   New content is the corpus-native Euler--theta/completed-prime--Gamma endpoint pair.
2. **Not RH.** Integrality and source ownership do not imply the sub-unit inequality.
3. **Not divisor-defined.** `u_(D,0)` uses the continued prime--Gamma current; the divisor appears
   only when its contour integral is evaluated.
4. **Not prime-diagonal.** Exponentiation precedes Hardy compression and cubic composition.
5. **Not a bounded landing.** No finite source vector is mapped to a completed zero projector.
   The defect compares two polarizations after singular completion.
6. **Not anchor-dependent.** All `x>0` anchors are trace-class homotopic and have zero mutual
   charge.
7. **Not positive as an operator.** `T` is signed.  Its positive/negative channels are exactly
   `(FACHD.4)`; positivity may be used only after the continuum anomaly is reduced.
8. **Sharp falsifier for closure.** If no coefficient-native cyclic map bounds the first channel
   of `(FACHD.4)` by the Burnol action, the object remains a complete receiver rather than an RH
   selector.

## Status

Paper proof dependency-closed.  Lean formalization deferred by current read-only research phase.
