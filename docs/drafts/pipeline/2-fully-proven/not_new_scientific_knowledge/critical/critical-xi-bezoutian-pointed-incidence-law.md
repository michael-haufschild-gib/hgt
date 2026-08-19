# The critical Xi Bezoutian is the pointed global incidence kernel for the Connes route

- **ID:** `critical-xi-bezoutian-pointed-incidence-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the critical log-derivative Pick kernel, the polarized Weil form, and the
  theta-source realization of Xi
- **Statement:** Clearing the completed logarithmic derivative by the actual Xi trace produces an
  entire two-variable Bezoutian. Its positivity on the Euler half-plane is equivalent to RH, it is
  exactly the completed two-channel Weil resolvent Gram, and it is determined by the pointed
  theta/Euler/trace-moment source rather than by a local regular germ.

## Entire Bezoutian

Put

```text
X(w)=xi(1/2+w).                                            (1)
```

Then `X` is even, entire, real under conjugation, and `X(0)!=0`. Define

```text
B_X(w,v)
 =(X'(w)conjugate(X(v))+X(w)conjugate(X'(v)))
   /(w+conjugate(v)).                                      (2)
```

Although `(2)` is written as a quotient, it extends holomorphically in `w` and
antiholomorphically in `v` across `w+conjugate(v)=0`.

### Proof of removability

Write `y=conjugate(v)`. The numerator is

```text
N(w,y)=X'(w)X(y)+X(w)X'(y).                               (3)
```

On `y=-w`, evenness of `X` and oddness of `X'` give

```text
N(w,-w)=X'(w)X(w)-X(w)X'(w)=0.                            (4)
```

The entire function `N(w,y)` therefore vanishes on the irreducible hyperplane `w+y=0`, so it is
divisible by `w+y` in the ring of entire functions. The quotient is the entire extension of
`B_X`.

Equivalently,

```text
B_X(w,v)
 =X(w)conjugate(X(v))
   *(L(w)+conjugate(L(v)))/(w+conjugate(v)),               (5)

L=X'/X,                                                    (6)
```

wherever the displayed logarithmic derivatives are regular.

## RH equivalence on the Euler half-plane

The following are equivalent:

```text
(i)  RH;

(ii) B_X is a positive kernel on Re w>1/2;

(iii) for every finite node system w_j in Re w>1/2,
      (B_X(w_j,w_k))_(j,k)>=0.                             (7)
```

### Proof

The half-plane `Re w>1/2` corresponds to `Re(1/2+w)>1`, so `X` has no zeros there. Multiplication of
a finite Gram matrix by the invertible diagonal matrix

```text
diag(X(w_1),...,X(w_N))                                    (8)
```

is a congruence. Equation `(5)` therefore identifies positivity of the Bezoutian matrices with
positivity of the critical logarithmic-derivative matrices. The complete-detector theorem in
`critical-logderivative-two-channel-weil-resolvent-law.md` identifies the latter with RH. This
proves `(7)`.

## Completed two-channel Weil identity

For `Re w>1/2`, let

```text
A_w(alpha)=w/(w^2+alpha^2),
B_w(alpha)=alpha/(w^2+alpha^2).                            (9)
```

The two-channel theorem and `(5)` give

```text
B_X(w,v)
 =q_W(X(w)A_w,X(v)A_v)
  +q_W(X(w)B_w,X(v)B_v),                                  (10)
```

where scalar factors act in the node parameter and `q_W` is the polarized Weil source form. More
explicitly, using the centered divisor modulo sign,

```text
B_X(w,v)
 =sum_(alpha mod +-)
   2m_alpha X(w)conjugate(X(v))
   *(w conjugate(v)+alpha^2)
   /((w^2+alpha^2)(conjugate(v)^2+alpha^2)).               (11)
```

The apparent poles at `w=+-i alpha` are removable because `X` vanishes there. Under RH every
`alpha` is real, and `(11)` is the positive Gram sum of the two entire feature channels

```text
E_(alpha,0)(w)
 =sqrt(2m_alpha) X(w)w/(w^2+alpha^2),

E_(alpha,1)(w)
 =sqrt(2m_alpha) X(w)alpha/(w^2+alpha^2).                  (12)
```

Away from RH, `(10)` remains the unconditional polarized Weil identity, but the divisor pairing is
indefinite.

## Pointed source presentation

The kernel `(2)` has two simultaneous source presentations.

### Theta/trace presentation

Riemann's theta formula gives `X` as the completed Fourier--Mellin trace of the fixed positive theta
source. Differentiation gives `X'`. Hence `(2)` is determined by

```text
completed theta source
  + distinguished trace X
  + its full even-moment/odd-log-trace germ.                (13)
```

The exact odd-trace/even-moment inverse in `CriticalTraceMomentGerm.lean` makes the last clause an
invertible pointed coordinate, not a finite jet heuristic.

### Euler--Gamma presentation

On `Re w>1/2`,

```text
X'(w)/X(w)
 =b(1/2+w)
  -sum_(n>=2)Lambda(n)n^(-1/2-w),                          (14)
```

so `(5)` is determined by

```text
weighted all-prime coefficient tail
  + finite-degree archimedean completion
  + the same distinguished completed trace X.             (15)
```

Equations `(13)`--`(15)` are the pointed global incidence structure forced by the critical-disc
Euler-orbit quotient theorems. Compact-open regular-germ convergence alone forgets precisely the
data retained in `(13)`--`(15)`.

## Positive factorization target

The direct source theorem is now unambiguous:

```text
construct a Hilbert space H_src and source-defined vectors R_w in H_src
such that

B_X(w,v)=<R_v,R_w>_(H_src)
for Re w,Re v>1/2.                                        (16)
```

Compatibility under enlargement of finite node sets is part of `(16)`. By `(7)`, such a
factorization proves RH. Constructing `H_src` as the abstract RKHS of an already-assumed positive
`B_X`, or constructing `(12)` after listing real zeros, is target-fed and does not count.

The Hedenmalm metric classification sharpens the form of a valid construction. Any continuous
positive source-core form symmetrizing the theta differential pair is necessarily nonlocal and has
Fourier measure supported on the real Xi divisor; ordinary weighted `L2` and finite-order local
differential metrics are zero. Therefore a successful factorization `(16)` must be a genuinely
nonlocal all-prime rigging whose divisor support emerges from the source identity, not a local
Gamma metric.

## Signed-Gamma rank boundary

The neutral signed-Gamma theorem proves

```text
K_G
 ->C[z,e^(beta z),e^(-beta z)]
 ->C[e^(beta z),e^(-beta z)]                               (17)
```

and the recurrent bound

```text
rank_Q Gamma_B(f)<=delta_beta+2m(n+1).                     (18)
```

Consequently `(16)` must carry the complementary prime-character module of rank at least

```text
pi(N)-delta_beta-2m(n+1)                                  (19)
```

through cutoff `N`, unless its differential-state complexity grows accordingly. The theta trace
in `(13)` supplies completion and moments; it does not license the Gamma field to impersonate the
independent prime phases in `(15)`.

## Relation to CCM

The chain is now exact:

```text
source factorization of the entire Bezoutian B_X
  -> positive critical Euler resolvent matrices
  -> exponentially convergent even/odd aperture channels
  -> no negative compact screw mode at any aperture
  -> conserved zero Morse charge
  -> RH.                                                    (20)
```

This is the positive Connes--CCM architecture after all finite-determinant and fixed-source
shortcuts are removed.

## Scientific status

The Bezoutian identity, diagonal congruence, and zero-side feature expansion are standard
consequences of the logarithmic derivative and Weil polarization. Their assembly gives the correct
pointed source object but is classified as bridge infrastructure, not new scientific knowledge.

## References

- `critical-logderivative-two-channel-weil-resolvent-law.md`.
- `critical-euler-weighted-shift-accretivity-law.md`.
- `hedenmalm-pair-weil-polarization-law.md`.
- `hedenmalm-theta-pair-divisor-supported-metric-law.md`.
- `signed-archimedean-gamma-orbit-charge-phase-law.md`.

## Lean decision

The formal tree contains the actual Xi trace/moment germs but not the analytic two-variable
Bezoutian, Weil distribution, or Pick extension theorem. A formal algebraic quotient alone would
not certify `(7)`, `(10)`, or the source presentations, so no Lean file is added.

## Gates

- [x] entire Xi Bezoutian constructed
- [x] removability proved
- [x] Euler-half-plane positivity proved equivalent to RH
- [x] completed two-channel Weil identity proved
- [x] theta/trace and Euler--Gamma source presentations identified
- [x] local-metric obstruction incorporated positively
- [x] signed-Gamma complementary rank bound incorporated
- [ ] construct the non-target-fed source Gram factorization `(16)`
- [ ] deduce RH

