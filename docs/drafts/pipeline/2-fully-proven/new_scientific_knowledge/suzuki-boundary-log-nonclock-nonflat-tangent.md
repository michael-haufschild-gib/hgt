# Suzuki boundary-log non-clock and non-flat tangent theorem

- **ID:** `suzuki-boundary-log-nonclock-nonflat-tangent`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SUZUKI SOURCE OPERATOR / EXACT NON-CLOCK RIGIDITY
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED AFTER TARGETED SEARCH]`
  `[NOT AN RH PROOF]`
- **Primary source input:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), equations (2.2), (2.9)--(2.11), and Theorem 1.1.
- **New conclusion:** source does not state endpoint action on `e^x`, finite-shift non-clock
  rigidity, or nonvanishing of far-negative projective tangent proved below.

## 1. Setup

Fix `a>0`. Let `A_a` be Suzuki's lower-bounded self-adjoint operator on `L^2(-a,a)`, and let

```text
e_a(x)=e^x,                         -a<x<a,
k=-g''
```

with functions extended by zero outside the interval when convolved. Suzuki's distributional
kernel decomposition is

```text
k(t)=-(1/2) Pf(1/|t|) -(2A+1) delta_0
     -sum_(n>=2) Lambda(n)/sqrt(n) [delta_(log n)+delta_(-log n)] -r''(t).   (1)
```

Only finitely many prime-power shifts occur after restriction to `(-a,a)`.

For `r>0` with `-r<lambda_a`, put

```text
u_r=(A_a+rI)^(-1)e_a,
U_r(z)=integral_(-a)^a u_r(x)e^(izx) dx,
Theta_r(z)=(z-i)U_r(z)/((z+i)U_r(-z)).                    (2)
```

The far-negative free source is

```text
F_a(z)=integral_(-a)^a e^x e^(izx) dx,
Theta_a^free(z)=(z-i)F_a(z)/((z+i)F_a(-z)).               (3)
```

## 2. Theorem A: exact endpoint action and source non-eigenvector

The vector `e_a` belongs to `Dom(A_a)`. There is a function `R_a` with finite one-sided limits at
both endpoints such that, almost everywhere on `(-a,a)`,

```text
(A_a e_a)(x)=-(1/2)e^x log(a^2-x^2)+R_a(x).              (4)
```

Consequently

```text
(A_a e_a)(x) -> +infinity as x -> a-,                    (5)
```

and similarly at `-a+`. In particular,

```text
A_a e_a is not a scalar multiple of e_a.                 (6)
```

Equation (4), rather than only the negative statement (6), is the positive survivor: endpoint
logarithmic coefficient `-e^x/2` is an exact source invariant. Finite prime shifts and the smooth
archimedean remainder cannot alter it.

### Proof

For a smooth `v` on the closed interval, the finite-part term has the exact pointwise form

```text
Pf integral_(-a)^a v(y)/|x-y| dy
 = integral_(-a)^a (v(y)-v(x))/|x-y| dy
   +v(x)log(a^2-x^2).                                    (7)
```

Apply (7) to `v=e_a`. The divided-difference integral

```text
J_a(x)=integral_(-a)^a (e^y-e^x)/|x-y| dy                (8)
```

has finite one-sided endpoint limits by dominated convergence: the mean-value theorem bounds its
integrand uniformly on the compact square. Every shift in (1) is bounded and has a finite one-sided
endpoint limit because the sum is finite. Since `r''` is continuous, its convolution with `e_a` is
continuous. Substitution into (1) gives (4). Its logarithmic term is in `L^2(-a,a)`, hence the whole
right side is in `L^2`.

For completeness, domain membership does not assume a pointwise formula for a general form-domain
element. The Fourier transform of `e_a` is

```text
F_a(z)=2 sinh(a(1+iz))/(1+iz).                            (9)
```

At every zero `gamma` of `xi(1/2-iz)`, `|Im gamma|<1/2`, so (9) is `O_a((1+|gamma|)^(-1))`.
The Riemann--von Mangoldt zero-counting bound makes Suzuki's defining zero sum for the form
absolutely convergent on `e_a`; thus `e_a` is in the closed form domain. Pairing (1) with the form
core gives the `L^2` vector in (4). The representation theorem for closed lower-bounded forms then
places `e_a` in `Dom(A_a)` and identifies its image with (4). Finally, the logarithm tends to
`-infinity`, while `R_a` has a finite limit, proving (5)--(6).

No RH is used: the only zero-location input is the classical critical-strip bound.

## 3. Theorem B: far-negative source tangent is genuinely nonzero

Set `epsilon=1/r`. Projective cancellation of the scalar `epsilon` reduces (2) to the source

```text
v_epsilon=(I+epsilon A_a)^(-1)e_a.                        (10)
```

Because Theorem A proves `e_a in Dom(A_a)`, the correct strong resolvent expansion is

```text
v_epsilon=e_a-epsilon A_a e_a+o(epsilon) in L^2,          (11)
```

as `epsilon -> 0+`. This is a vector expansion; no false operator-norm expansion of the unbounded
operator is used. Boundedness of the Fourier functionals uniformly on compact `z`-sets gives

```text
U_epsilon(z)=F_a(z)-epsilon H_a(z)+o(epsilon),
H_a(z)=integral_(-a)^a (A_a e_a)(x)e^(izx) dx             (12)
```

locally uniformly. Define the entire cross-tangent numerator

```text
N_a(z)=H_a(z)F_a(-z)-F_a(z)H_a(-z).                       (13)
```

Then

```text
N_a is not identically zero.                              (14)
```

Equivalently, away from zeros of `F_a(z)F_a(-z)`, the meromorphic field

```text
Delta_a(z)=H_a(-z)/F_a(-z)-H_a(z)/F_a(z)                 (15)
```

is nonzero and

```text
d/d epsilon Theta_epsilon(z)|_(0+)=Theta_a^free(z)Delta_a(z).  (16)
```

### Proof

Identity (11) follows exactly from

```text
[(I+epsilon A_a)^(-1)e_a-e_a]/epsilon
 =-(I+epsilon A_a)^(-1)A_a e_a -> -A_a e_a.              (17)
```

Suppose (13) vanished identically. For every nonzero integer `n`, set

```text
z_n=pi n/a+i.                                             (18)
```

Equation (9) gives `F_a(z_n)=0` and `F_a(-z_n) != 0`; hence (13) gives `H_a(z_n)=0`. But

```text
H_a(z_n)=integral_(-a)^a [(A_a e_a)(x)e^(-x)] e^(i pi n x/a) dx.  (19)
```

Thus every nonzero Fourier coefficient of `(A_a e_a)e^(-x)` vanishes. Completeness of the
two-sided Fourier basis forces `(A_a e_a)e^(-x)` to be constant almost everywhere, contradicting
(6). This proves (14); quotient differentiation gives (16).

## 4. Theorem C: no finite admissible shift is the free clock

For every finite admissible `r`,

```text
Theta_r != Theta_a^free                                    (20)
```

as meromorphic functions, hence also as Schur functions on the upper half-plane.

### Proof

Assume equality. The points (18) lie in the upper half-plane and are non-anchor zeros of the free
carrier. The Hermite--Biehler denominator of `Theta_r` is nonzero there, so equality forces
`U_r(z_n)=0` for every `n!=0`. Therefore every nonzero Fourier coefficient of `u_r e^(-x)` vanishes,
and Fourier completeness yields

```text
u_r=c e_a.                                                 (21)
```

The resolvent is injective and `e_a` is nonzero, so `c!=0`. Applying `A_a+rI` to (21) gives

```text
A_a e_a=(c^(-1)-r)e_a,                                    (22)
```

contradicting Theorem A.

## 5. Scientific consequence and remaining frontier

This closes two fixed-aperture gaps left open in prior Suzuki work:

```text
finite admissible shift cannot be exactly universal clock;
far-negative source path has a provably nonzero first projective tangent.  (23)
```

The arithmetic deformation is therefore not an artifact that appears only after a cofinal limit.
Every finite shift already leaves the clock boundary, and departure has an exact first-order
source producer `N_a`.

This does **not** prove a cofinal lower bound for `N_a`, select an RH-bearing schedule, or identify a
limit divisor with Xi. The remaining frontier is now narrower: propagate this proven nonzero
finite-aperture tangent through a cofinal intermediate-shift regime without its scale collapsing.

## 6. Formalization map

Lean module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiFiniteShiftNonClock.lean
```

Formalized, unconditionally:

1. exact free-clock sample zeros `z_n=pi n/a+i`;
2. endpoint logarithmic blow-up modulo every residual with a finite endpoint limit;
3. Hilbert-basis completeness: zero nonconstant modes imply a pure zero mode;
4. vanishing reflected cross-tangent implies source proportionality;
5. nonzero-mode source forces a nonzero cross-tangent somewhere;
6. equality with Suzuki's explicit free carrier at all clock samples forces pure zero mode.

Concrete construction of Suzuki's unbounded `A_a`, form domain, and distribution kernel remains
outside current Lean source layer; analytic Theorem A is paper-proved here and its exact reusable
boundary and sampling mechanisms are formalized without axioms.

## 7. Hostile audit

1. **Unbounded-operator error removed.** No operator-norm Neumann expansion is asserted. Only the
   strong vector derivative (17), valid because Theorem A proves source-domain membership, is used.
2. **No assumed nonzero tangent.** Nonvanishing follows from Fourier completeness plus exact
   endpoint singularity.
3. **No RH.** Critical-strip location and standard zero counting are unconditional.
4. **No finite-dimensional surrogate.** All integer Fourier modes are used.
5. **No cofinal overclaim.** Fixed-`a` nonvanishing may still decay after `a` varies; that remains
   open.
