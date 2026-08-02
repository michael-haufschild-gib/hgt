# Route J semilocal prolate odd-harmonic activation law

**Status:** `[ACTIVE HARD FRONTIER]`
`[CONJECTURE J-OHA]`

## Source-exact setup

For `ell,m >= 0`, put

```text
p_ell(m)=sum_(k=0)^ell 2^(3k) binom(m,k) binom(ell,k)/binom(2k,k),
d_ell=2ell+1,
C_ell=(-1)^ell 2^(3/2-2ell) binom(2ell,ell).
```

The Connes--Consani--Moscovici rank-one Lambert decomposition gives diagonal trace atom

```text
C_ell (-1)^m c_m p_ell(m)^2 q^(d_ell)/(1-q^(d_ell)),
c_m=4^(-m)binom(2m,m).
```

Let `a_n(q)` be positive semilocal Jacobi radius and let

```text
R_k(q)
 =a_(2k)(q)a_(2k+1)(q)-a_(2k+1)(q)^2
  -a_(2k+2)(q)^2+a_(2k+2)(q)a_(2k+3)(q).
```

## Conjectured theorem

The first activation of harmonic `ell` is the unique top-weight contribution to
`[q^(d_ell)]a_n(q)`. Since

```text
lead(p_ell)=L_ell=2^(3ell)ell!/(2ell)!,
```

its exact radius contribution is

```text
F_(ell,n)
 =(r_n C_ell/2)
   [(-1)^(n+1)c_(n+1)p_ell(n+1)^2
    -(-1)^n c_n p_ell(n)^2],
r_n=sqrt((n+1/2)(n+1)).
```

Writing `d=2ell+1`,

```text
(-1)^n F_(ell,n)/n^(d-1/2)
 -> A_ell=-C_ell L_ell^2/sqrt(pi),
```

and every other contribution to `[q^d]a_n(q)` has source weight at most `d-1`.
Consequently

```text
[q^d]R_(n+1)/((2n+3)^(d-1/2))
 -> K_ell,

K_ell=(8ell+2) C_ell L_ell^2/sqrt(pi)
     =(-1)^ell (8ell+2)2^(4ell+1)sqrt(2)/((2ell)!sqrt(pi)).
```

The `d`th Euler correction therefore becomes order one at

```text
q^d n^(d-1/2) asymp 1,
n asymp p^(2d/(2d-1)).
```

For `ell=1`, this specializes to the proved third-Euler constant
`-160sqrt(2/pi)` and scale `p^(6/5)`.

## New filtration mechanism

Use the finite formal identity

```text
log det(I+A)=sum_(k>=1)(-1)^(k+1)Tr(A^k)/k.
```

A `k`-fold source monomial with harmonics `ell_1,...,ell_k` has minimal Euler degree

```text
E=sum_i(2ell_i+1)
```

and its cyclic trace is a product of `k` parity Gram sums. Each Gram sum for the pair
`(ell_i,ell_(i+1))` has size `n^(ell_i+ell_(i+1)+1/2)`. The two-step boundary difference in
the Jacobi determinant quotient lowers total degree by one. After multiplication by `r_n`, its
radius weight is therefore

```text
2sum_i ell_i+k/2 = E-k/2.
```

Lambert repetitions spend Euler degree without increasing this weight. At Euler degree `d`,
the only monomial with weight `d-1/2` is `k=1`, `E=d`, hence the newly activated
`ell=(d-1)/2` atom. Every `k>=2` interaction has weight at most `d-1`; a `k=1` proper odd
divisor has still smaller weight. Products created by the square root also have weight at most
`d-1`.

## Hard proof obligations

1. Prove cyclic rank-one trace factorization and coefficientwise finite log-determinant identity.
2. Prove parity Gram-sum polynomial/central-binomial asymptotics with a two-step remainder bound,
   not only pointwise `O`.
3. Include all Lambert repetitions and proper odd divisors of `d`.
4. Prove square-root/exponential coefficient filtration and uniqueness of top weight.
5. Prove lower-weight terms remain `o(n^(d-1/2))` after the four-radius stencil.
6. Prove exact two-step regular variation of `F_(ell,n)` and the constant `K_ell`.
7. Formalize the dependency-closed theorem unconditionally in Lean.

Route J remains open until these obligations and all later finite-prime/global survivors close.

## 2026-08-02 frontier advance: Meixner--Poisson resummation

`[SOURCE IDENTIFICATION PROVED]`
`[ODD TOP AMPLITUDE LEAN-PROVED]`
`[UNIFORM DARBOUX TRANSFER OPEN]`

The source polynomial is not an isolated ad hoc family. Direct term comparison gives

```text
p_ell(n)={}_2F_1(-ell,-n;1/2;2)=M_ell(n;1/2,-1),       (A1)
```

the Meixner polynomial at the analytically continued parameter `c=-1`. Its standard bilinear
Poisson kernel, specialized with `z=-s^2`, gives for natural `i,j`

```text
P_(i,j)(s)
 :=sum_(ell>=0)(-1)^ell c_ell p_ell(i)p_ell(j)s^(2ell)

 =((1-s^2)^(i+j)/(1+s^2)^(i+j+1/2))
   {}_2F_1(
     -i,-j;1/2;-4s^2/(1-s^2)^2
   ),                                                   (A2)

c_ell=4^(-ell)binom(2ell,ell).
```

This formula is classical as a Meixner Poisson kernel; it is not claimed as new. New Route-J
content is the source specialization and its Lambert reconstruction. The published matrix entry
therefore admits the exact resummation

```text
gamma_(i,j)(q)
 =(-1)^j 2sqrt(2)sqrt(c_i c_j)
   sum_(r>=1) q^r P_(i,j)(q^r).                         (A3)
```

Equation `(A3)` sums every harmonic and every Lambert repetition before taking Jacobi
determinants. It is the missing non-fixed-order infrastructure.

On the diagonal, Euler transformation of `(A2)` gives

```text
P_(n,n)(s)
 =(1+s^2)^(-1/2)
   {}_2F_1(
     -n,n+1/2;1/2;
     4s^2/(1+s^2)^2
   )

 =(1+s^2)^(-1/2)
   n!/(1/2)_n
   P_n^(-1/2,0)(cos(4 arctan s)).                       (A4)
```

Thus Route J's source tower is controlled by one explicit Jacobi-polynomial oscillatory kernel,
not by unrelated fixed Euler coefficients.

Quadratic Jacobi parity and `(1/2)_n/n!=c_n` sharpen `(A4)` to

```text
P_(n,n)(s)
 =(-1)^n/[c_n sqrt(1+s^2)]
   P_(2n)(2s/(1+s^2)),                                  (A4')
```

where `P_(2n)` is the ordinary Legendre polynomial. Hence all central-binomial factors cancel in
the literal diagonal source entry:

```text
gamma_(n,n)(q)
 =2sqrt(2) sum_(r>=1)
   q^r/sqrt(1+q^(2r))
   P_(2n)(2q^r/(1+q^(2r))).                             (A4'')
```

This identity is stronger than a coefficient asymptotic: it resums every odd harmonic and every
Lambert repetition into classical Legendre waves before determinants are formed. The trace-linear
positive-radius contribution is therefore exactly

```text
W_n(q)
 =sqrt(2) r_n sum_(r>=1) q^r/sqrt(1+q^(2r))
   [P_(2n+2)(x_r)-P_(2n)(x_r)],
x_r=2q^r/(1+q^(2r)).                                   (A4''')
```

Uniform bulk Darboux asymptotics at
`theta_r=acos(x_r)=pi/2-2 arctan(q^r)` predict

```text
W_n(q)
 ~(-1)^(n+1) 2sqrt(2/pi) q sqrt(n)
   cos((4n+3)arctan q)
```

whenever `q->0`, `nq->infinity`, and `nq^2->0`; `r>=2` is lower order. A two-step difference in
the Route-J stencil then produces the `q^2 n^(3/2)` envelope in `(A6)`. Proving this with a
uniform remainder, and proving every `k>=2` determinant-log trace is smaller, is the exact next
scientific gate.

The associated-graded odd critical constants have exact generating function. If

```text
K_ell=(8ell+2)C_ell L_ell^2/sqrt(pi)
```

then elementary factorial cancellation gives

```text
K_ell
 =(-1)^ell(16ell+4)sqrt(2/pi)16^ell/(2ell)!,

sum_(ell>=0) K_ell y^(2ell)
 =4sqrt(2/pi)[cos(4y)-8y sin(4y)].                      (A5)
```

This exposes a decisive nonuniformity: the isolated `ell=1` scale `p^(6/5)` is cancelled in the
resummed associated graded. For `q=1/p`, the oscillatory derivative envelope in `(A5)` becomes
order one at

```text
q^2 n^(3/2) asymp 1,
n asymp p^(4/3),                                       (A6)
```

provided the exact kernel transfer is uniform. Therefore neither the old `p^2` guess nor the
fixed-third-order `p^(6/5)` law is the full semilocal boundary.

The hard open theorem is now precise and RH-relevant:

1. prove a uniform Hilb/Darboux asymptotic for `(A4)` in the joint regime
   `s->0`, `ns->infinity`, `ns^2->0`;
2. propagate `(A3)` through the determinant logarithm and four-radius critical stencil;
3. prove higher trace powers are lower at the resulting `n asymp p^(4/3)` boundary, or compute
   their nonzero limiting kernel;
4. decide the limit-point/limit-circle sign and source-selected extension from that kernel;
5. transport or eliminate it through finite-prime orthogonalization, Sonin corner, and the
   infinite-label singular carrier.

The formal module

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateOddHarmonicActivation.lean
```

already proves the exact falling-factorial source polynomial, degree `ell`, leading coefficient
`L_ell`, literal signed radius atom, sharp amplitude `-C_ell L_ell^2/sqrt(pi)`, agreement with
Euler orders one and three, and the unique-top-weight interaction gap. Uniform resummation
`(A2)`--`(A6)` remains the active hard core; it is not yet claimed as a completed theorem.

## Associated-graded all-trace hierarchy

`[PAPER-PROVED SOURCE SYMBOL]`
`[FULL UNIFORM LIFT OPEN]`

The new source structure extends beyond `k=1`. For one parity block define the Gram sum

```text
G_n(a,b)=sum_(0<=j<=n, j=n mod 2)c_j p_a(j)p_b(j).
```

Wallis plus the polynomial top coefficient gives

```text
G_n(a,b)
 ~ L_aL_b/[sqrt(pi)(2a+2b+1)]
    n^(a+b+1/2).                                       (A7)
```

A cyclic `k`-fold rank-one trace with indices `ell_1,...,ell_k` is the product of the `k`
successive Gram sums. Put `S=sum ell_i`. Its exponent is

```text
alpha=2S+k/2.
```

After multiplying by the first Lambert activations and summing all harmonic indices, the complete
associated-graded `k`-trace has the cycle-kernel form

```text
(q sqrt(n))^k Phi_k(qn),                               (A8)

Phi_k(u)
 =(2sqrt(2/pi))^k
   integral_[0,1]^k product_(i mod k)
     cos(4u t_(i-1)t_i) dt_1...dt_k.                  (A9)
```

Proof: use

```text
C_ell L_ell^2
 =(-1)^ell 2sqrt(2)16^ell/(2ell)!,

1/(2a+2b+1)=integral_0^1 t^(2a+2b)dt.
```

Every `ell_i` then occurs only through
`sum_ell (-1)^ell(4u t_(i-1)t_i)^(2ell)/(2ell)!`, which is the displayed cosine.
Absolute convergence justifies all finite products and interchanges. In particular

```text
|Phi_k(u)| <= (2sqrt(2/pi))^k.                         (A10)
```

Parity produces a second new rigidity. A `k`-trace on block `n` carries sign `(-1)^(nk)`.
The Jacobi log quotient applies

```text
B_(n+1)+B_(n-2)-B_n-B_(n-1).                          (A11)
```

For odd `k`, `(A11)` is a first two-step difference and lowers `n^alpha` by one. For even `k`,
the parity sign is absent, both constant and first moments cancel, and `(A11)` is a second
difference, lowering by two. Square-root products contain at least two such log factors and lose
another power.

At the conjectural resummed boundary `n asymp q^(-4/3)`,

```text
q sqrt(n) asymp q^(1/3),
u=qn asymp q^(-1/3).
```

The critical stencil differentiates an oscillatory cycle kernel at most once for odd `k`.
Using `(A10)` and `|Phi_k'(u)|<=4k(2sqrt(2/pi))^k` gives

```text
k=1:  order (q sqrt(n))u = q^2 n^(3/2) asymp 1,
odd k>=3: O((q sqrt(n))^k(1+u))
          =O(q^((k-1)/3)) ->0,
even k:  one additional n^(-1) suppression,
sqrt products: at least one additional n^(-1) suppression. (A12)
```

Thus the associated graded is class-complete: only the resummed single-trace Legendre wave can
survive at `p^(4/3)`. Higher determinant traces cannot repair its oscillating sign at symbol
level. Remaining hard step is a uniform lift from associated graded to exact `(A3)` and exact
finite-section determinant quotients; without that lift `(A12)` is not yet a no-go for J-SF5.
