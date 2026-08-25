# The Xi Bezoutian is the double Laplace transform of a positive theta tail-density

- **ID:** `theta-tail-first-moment-bezoutian-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** bilateral Laplace transforms, integration by parts, and the critical Xi
  Bezoutian
- **Statement:** For every positive even rapidly decreasing source `k`, the logarithmic-derivative
  Bezoutian of its bilateral Laplace transform is the double Laplace transform of an explicit
  pointwise nonnegative tail first-moment kernel. For the Riemann theta source, RH is exactly
  positive definiteness of this source kernel on a cofinal exponential family.

## General source theorem

Let `k:R->(0,infinity)` be even and smooth, with enough superexponential decay that every integral
and integration by parts below is absolutely justified. Put

```text
X(w)=integral_R k(x)e^(wx)dx.                              (1)
```

Then `X` is even and entire. Define its Bezoutian

```text
B_X(w,v)
 =(X'(w)conjugate(X(v))+X(w)conjugate(X'(v)))
   /(w+conjugate(v)),                                      (2)
```

with the removable extension at `w+conjugate(v)=0`.

For real `x,t`, put

```text
H_k(x,t)
 =1/2 integral_(x+t)^infinity
      u k((u+x-t)/2) k((u-x+t)/2)du.                       (3)
```

`[PROVED]` One has

```text
B_X(w,v)
 =integral_R integral_R
    H_k(x,t)e^(wx+conjugate(v)t)dxdt.                      (4)
```

Moreover,

```text
H_k(x,t)=H_k(t,x)>=0                                      (5)
```

for every `x,t`.

## Proof of the transform identity

Use

```text
r=x+t,
q=x-t.                                                     (6)
```

The integrand

```text
f_q(u)=k((u+q)/2)k((u-q)/2)                               (7)
```

depends on `x,t` only through `q`, while the lower endpoint in `(3)` is `r`. Since

```text
partial_x+partial_t=2 partial_r,                           (8)
```

differentiation of the lower endpoint gives

```text
(partial_x+partial_t)H_k(x,t)
 =-(x+t)k(x)k(t).                                         (9)
```

On the other hand,

```text
(partial_x+partial_t)e^(wx+conjugate(v)t)
 =(w+conjugate(v))e^(wx+conjugate(v)t).                   (10)
```

Multiply `(10)` by `H_k`, integrate over `R^2`, and integrate by parts using `(9)`. All boundary
terms vanish by the assumed decay. The result is

```text
(w+conjugate(v)) integral integral H_k e^(wx+conjugate(v)t)

 =integral integral (x+t)k(x)k(t)e^(wx+conjugate(v)t)

 =X'(w)conjugate(X(v))+X(w)conjugate(X'(v)).              (11)
```

Division proves `(4)` off the removable hyperplane, and analyticity proves it everywhere.

## Proof of pointwise positivity

Evenness of `k` makes `f_q` in `(7)` even. Hence

```text
integral_R u f_q(u)du=0.                                  (12)
```

If `r=x+t>=0`, the integral in `(3)` is over positive `u` and is nonnegative. If `r<0`, use `(12)`:

```text
integral_r^infinity u f_q(u)du
 =-integral_(-infinity)^r u f_q(u)du>=0,                  (13)
```

because `u<0` on the last interval. This proves positivity. Symmetry follows from replacing
`q` by `-q` and using evenness of `k`.

An equivalent shift-tail formula is

```text
H_k(x,t)
 =integral_0^infinity
    (x+t+2s)k(x+s)k(t+s)ds.                               (14)
```

Unlike `(3)`, the integrand in `(14)` is not pointwise positive when `x+t<0`; the cancellation in
`(13)` is essential.

## Operator positivity is the remaining content

For nodes `w_1,...,w_N` and coefficients `c_j`, put

```text
Phi_c(x)=sum_j c_j e^(w_j x).                              (15)
```

Equation `(4)` gives

```text
sum_(j,l) c_j conjugate(c_l) B_X(w_j,w_l)

 =integral_R integral_R
    H_k(x,t)Phi_c(x)conjugate(Phi_c(t))dxdt.               (16)
```

Thus pointwise positivity `(5)` is not the desired theorem. The source kernel must be
positive-definite as a bilinear integral operator on the relevant exponential span:

```text
integral integral H_k(x,t)Phi(x)conjugate(Phi(t))dxdt>=0.  (17)
```

A nonnegative entrywise kernel need not satisfy `(17)`; this is precisely where collective phase
correlation survives every scalar or one-node positivity test.

## Riemann theta specialization

Take Hedenmalm's logarithmic Riemann theta source

```text
k(x)=2 VarTheta_00(i exp(2x)),                             (18)
```

with the normalization for which its bilateral transform is

```text
X(w)=xi(1/2+w).                                            (19)
```

The source is positive, even, and double-exponentially decreasing, so the general theorem applies.
Combining `(16)` with `critical-xi-bezoutian-pointed-incidence-law.md` gives

```text
RH
 <-> H_k is positive on
     span{e^(wx):Re w>1/2}.                                (20)
```

The span in `(20)` is cofinal, not compact: remote off-line divisor data may require nodes escaping
compactness or combinations approaching the radical.

## Positive factorization target

The tail formula has an exact Krein factorization. Fix any `c>0` and define, initially on the
finite exponential span,

```text
(V_(+,c)Phi)(s)
 =integral_R (x+s+c)k(x+s)Phi(x)dx,

(V_(-,c)Phi)(s)
 =integral_R (x+s-c)k(x+s)Phi(x)dx,

s>=0.                                                       (21)
```

Then

```text
H_k(x,t)
 =1/(2c) integral_0^infinity
    ((x+s+c)k(x+s)(t+s+c)k(t+s)
     -(x+s-c)k(x+s)(t+s-c)k(t+s))ds.                      (22)
```

Indeed

```text
(a+c)(b+c)-(a-c)(b-c)=2c(a+b),                            (23)
```

and `(22)` follows from `(14)` with `a=x+s`, `b=t+s`. Therefore

```text
integral integral H_k(x,t)Phi(x)conjugate(Phi(t))dxdt

 =1/(2c)(||V_(+,c)Phi||_2^2-||V_(-,c)Phi||_2^2).          (24)
```

For the Riemann theta source, `(20)` and `(24)` prove the exact contraction criterion

```text
RH
 <-> ||V_(-,c)Phi||_2<=||V_(+,c)Phi||_2
     for every Phi in span{e^(wx):Re w>1/2}.               (25)
```

The choice of `c>0` is immaterial: the difference in `(24)` is always `2c` times the same source
form.

Equivalently, write

```text
(W Phi)(s)=integral_R k(x+s)Phi(x)dx,
(M Phi)(s)=integral_R (x+s)k(x+s)Phi(x)dx.                 (26)
```

Then `V_(+,c)=M+cW`, `V_(-,c)=M-cW`, and `(25)` is

```text
Re <M Phi,W Phi>_(L2(R_+))>=0.                             (27)
```

This is a concrete source-only operator inequality. By the Douglas factorization lemma, `(25)` is
equivalent, on the relevant closures, to the existence of a contraction `C_c` satisfying

```text
C_c V_(+,c)Phi=V_(-,c)Phi.                                (28)
```

Thus the positive theta-side CCM theorem is to construct the contraction `(28)` directly from the
theta/Euler incidence. A proof of `(28)` yields a genuine Hilbert factorization of `H_k` through the
defect operator `(I-C_c^*C_c)^(1/2)`, and therefore proves the Xi Bezoutian positivity, the
two-channel Weil criterion, conservation of the aperture Morse charge, and RH.

Constructing `(28)` from an already-assumed positive Bezoutian or from the real Xi divisor is
target-fed. The factor must be derived from the theta/Euler incidence.

## Relation to existing corpus constraints

- The critical-disc Euler-orbit theorem says `(21)` cannot be a compact-open invariant of the
  regular germ; it must retain the pointed trace/divisor incidence.
- The Hedenmalm metric classification says a successful positive metric is nonlocal and
  divisor-supported; no scalar weighted `L2` or finite-order differential metric supplies `(21)`.
- The signed-Gamma boundary theorem says the factor must separately transport the complementary
  prime-character module; Gamma jets and Stokes corrections have finite terminal phase rank.
- The compact-detector theorem explains why pointwise positivity `(5)` and any compact strict
  margin are insufficient: the needed positivity is the all-correlation statement `(17)`.

## Scientific status

The tail-kernel identity is elementary integration by parts and its positivity uses only evenness.
It gives a useful source coordinate but does not clear the novelty gate.

## References

- `critical-xi-bezoutian-pointed-incidence-law.md`.
- `hedenmalm-theta-pair-divisor-supported-metric-law.md`.
- Riemann's theta integral for Xi.

## Lean formalization

Formalized unconditionally in:

- `formal/GaloisForLFunctions/RHTower/ThetaTailFirstMomentKernel.lean`;
- `formal/GaloisForLFunctions/RHTower/ThetaTailFirstMomentKreinTransform.lean`;
- `formal/GaloisForLFunctions/RHTower/ThetaTailFirstMomentDoubleLaplace.lean`.

The first module constructs literal kernel `(3)` for actual positive even theta-cusp source and
proves absolute integrability, symmetry, simultaneous reflection invariance, pointwise
nonnegativity, shift-tail formula `(14)`, and pointwise Krein factorization `(22)`. Its negative
half-line proof uses exact odd first-moment cancellation, not false pointwise positivity of shifted
integrand.

The second module constructs literal bilateral source transform and first-moment derivative,
identifies transform with `XiC` after exact `w -> I*w` coordinate rotation, evaluates both
translated source-integral Krein channels, and proves their integrated difference equals actual
theta-transform Bezoutian throughout right Fubini domain.

The third module proves absolute integrability of sheared three-variable channels, exact Fubini
interchange, literal product and iterated double-Laplace identities, every two-variable exponential
moment, simultaneous reflection transfer to negative chamber, and dominated convergence across
zero-real-sum hyperplane. It identifies transform with existing entire `xiCentBezoutian`, including
removable hyperplane, and proves exact equivalences:

```text
RH <-> every finite cofinal-half-plane matrix of literal double-Laplace integrals is PSD,
RH <-> every finite cofinal-half-plane two-Volterra Krein-difference matrix is PSD.
```

All modules are wired into `GaloisForLFunctions.RHTower`. Direct Lean checks and targeted leaf
builds pass. New capstones have `#print axioms` output containing only `propext`,
`Classical.choice`, and `Quot.sound`. No theorem introduces an axiom, hypothesis proxy, or
conditional replacement for card claims.

## Gates

- [x] explicit theta tail first-moment kernel constructed
- [x] double Laplace identity proved
- [x] pointwise nonnegativity proved
- [x] operator-positivity gap isolated
- [x] RH equivalence on the cofinal exponential span proved
- [x] exact two-Volterra Krein factorization proved
- [x] RH reduced to a source-only contraction law
- [ ] construct the non-target-fed contraction `(28)`
- [ ] deduce RH
