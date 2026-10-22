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

## 2026-08-02 frontier advance: exact uniform one-trace lift

`[PAPER-PROVED EXACT K=1 LIFT]`
`[SOURCE-SPECIFIC CANDIDATE NEW]`
`[CLASSICAL DARBOUX INPUT]`
`[HIGHER EXACT TRACES OPEN]`

The associated-graded `k=1` prediction admits a full uniform lift.  Put

```text
rho_n=sqrt((n+1/2)(n+1)),
alpha(s)=atan(s),
x(s)=2s/(1+s^2),
D_n(s)=P_(2n+2)(x(s))-P_(2n)(x(s)).
```

The classical Laplace--Darboux formula for Legendre polynomials is uniform when the angular
variable stays in a compact subinterval of `(0,pi)`.  Since

```text
acos(x(s))=pi/2-2alpha(s),
```

it gives, uniformly for `0<=s<=s_0<1`,

```text
D_n(s)
 =(-1)^(n+1) 2sqrt(cos(2alpha(s)))/(sqrt(pi n))
    cos((4n+3)alpha(s))
  +O(n^(-3/2)).                                        (A13)
```

This is a classical asymptotic input, not a novelty claim.  The phase and amplitude in `(A13)`
come from applying the standard formula separately to degrees `2n` and `2n+2`:

```text
P_(2n)(x(s))
 =(-1)^n cos((4n+1)alpha(s))
    /sqrt(pi n cos(2alpha(s)))+O(n^(-3/2)),

P_(2n+2)(x(s))
 =(-1)^(n+1) cos((4n+5)alpha(s))
    /sqrt(pi (n+1) cos(2alpha(s)))+O(n^(-3/2)).
```

Replacing `(n+1)^(-1/2)` by `n^(-1/2)` costs only `O(n^(-3/2))`; the cosine sum then supplies
the factor `2cos(2alpha)`.  A standard source is Szego, *Orthogonal Polynomials*,
Theorem 8.21.2; the corresponding uniform-asymptotic reference is
<https://dlmf.nist.gov/14.15>.

Define

```text
A=2sqrt(2/pi),
a(s)=s sqrt(1-s^2)/(1+s^2),
lambda_n=rho_n/sqrt(n).
```

Substitution of `(A13)` into the exact Lambert--Legendre identity `(A4''')` yields

```text
(-1)^n W_n(q)
 =-A lambda_n sum_(r>=1)
    a(q^r) cos((4n+3)alpha(q^r))
  +O(q/sqrt(n)),                                       (A14)
```

uniformly for `0<q<=q_0<1`.  The error is genuinely uniform over the complete Lambert tower:

```text
rho_n n^(-3/2) sum_(r>=1) q^r/sqrt(1+q^(2r))
 =O(q/sqrt(n)).
```

No fixed-Euler truncation or formal interchange remains in `(A14)`.

For a sequence `h_n`, use the literal alternating four-radius linear stencil

```text
S_m(h)
 =rho_(m+1)h_m-rho_m h_(m+1)+2rho_(m+1)h_(m+1)
  -2rho_(m+2)h_(m+2)+rho_(m+3)h_(m+2)-rho_(m+2)h_(m+3).
                                                               (A15)
```

For fixed `j in {0,1,2,3}`,

```text
rho_(m+j)=m+O(1),          lambda_(m+j)=sqrt(m)+O(m^(-1/2)).
```

Consequently the four coefficients after inserting `(A14)`, divided by `m^(3/2)`, are

```text
1+O(1/m), 1+O(1/m), -1+O(1/m), -1+O(1/m).             (A16)
```

The exact trigonometric cancellation is

```text
 cos(phi)+cos(phi+4alpha)-cos(phi+8alpha)-cos(phi+12alpha)
 =4cos(2alpha)sin(4alpha)sin(phi+6alpha).              (A17)
```

Since

```text
a(s)cos(2alpha(s))sin(4alpha(s))
 =4s^2(1-s^2)^(5/2)/(1+s^2)^4,                        (A18)
```

equations `(A14)`--`(A18)` prove the exact uniform stencil theorem:

```text
S_m(((-1)^n W_n(q))_n)/(q^2 m^(3/2))
 =-32sqrt(2/pi) sin((4m+9)atan(q))+o(1)                (A19)
```

whenever

```text
q->0,      m->infinity,      mq->infinity.             (A20)
```

The formerly imposed condition `mq^2->0` is unnecessary.  Indeed:

1. coefficient and Darboux errors in `(A15)` are `O(q sqrt(m))`, which becomes
   `O((mq)^(-1))` after normalization in `(A19)`;
2. the `r=1` factor in `(A18)`, divided by `q^2`, tends to `4`;
3. all Lambert repetitions `r>=2` contribute

```text
O(m^(3/2) sum_(r>=2) q^(2r))
 =O(q^4 m^(3/2)),
```

which is `O(q^2)` after the same normalization.

Thus `(A19)` is a uniform lift of the complete resummed `k=1` source, not merely its associated
graded.

### Exact prime-by-prime sign obstruction

Let `q=1/p` with `p` prime and let `p->infinity`.  For each such `q`, choose even integers
`m_+(q),m_-(q)` within `O(q^(-1))` of `q^(-4/3)` so that

```text
sin((4m_+(q)+9)atan(q))->1,
sin((4m_-(q)+9)atan(q))->-1.                           (A21)
```

This is possible because consecutive even indices change the phase by `8atan(q)->0`, while an
interval of `O(q^(-1))` indices covers a full turn.  The adjustment is negligible relative to
`q^(-4/3)`:

```text
m_+(q)/q^(-4/3)->1,       m_-(q)/q^(-4/3)->1.
```

Hence both sequences satisfy `(A20)` and

```text
q^2 m_+(q)^(3/2)->1,      q^2 m_-(q)^(3/2)->1.
```

Equation `(A19)` therefore gives opposite nonzero limits:

```text
S_(m_+(q)) -> -32sqrt(2/pi),
S_(m_-(q)) ->  32sqrt(2/pi).                           (A22)
```

The exact resummed trace-linear semilocal current is not eventually sign-definite at its genuine
critical scale.  This is a source-specific, prime-by-prime, uniform no-go for the `k=1` survivor.
It does not use a numerical experiment, fixed-order Euler truncation, or target-selected phase.

### Anti-theatre boundary

What is now closed:

1. every odd harmonic and every Lambert repetition in the trace-linear radius are included;
2. the passage through the literal four-radius stencil is uniform;
3. the true `p^(4/3)` scale and coefficient `32sqrt(2/pi)` are exact;
4. both signs occur on nearby even source indices for every sufficiently large prime.

What remains genuinely open:

1. uniform exact bounds for `Tr(A_n(q)^k)`, `k>=2`, after the finite-section determinant
   logarithm and stencil;
2. proof that determinant-log and square-root remainders are `o(1)` on the indices in `(A21)`,
   or computation of their nonzero limiting kernel;
3. only after that exact lift, limit-point/limit-circle extension selection, finite-prime
   orthogonalization, Sonin transport, and global singular-carrier descent.

Route J remains open.  The surviving hard core has narrowed from the entire Lambert--harmonic
tower to exact higher finite-section determinant traces.

## 2026-08-02 frontier advance: one hyperbolic translation behind the complete source

`[PAPER-PROVED EXACT SOURCE FACTORIZATION]`
`[PAPER-PROVED RAW NONLINEAR TRACE BOUND]`
`[CLASSICAL SU(1,1) BRIDGE]`
`[SOURCE-SPECIFIC NOVELTY UNVERIFIED]`
`[AMPLIFIED FINITE-SECTION STENCIL OPEN]`

The exact Meixner kernel has more structure than `(A2)` exposes.  Its whole two-variable
generating function is rational under a square root.  For

```text
c_n=(1/2)_n/n!=4^(-n)binom(2n,n)
```

the elementary Meixner generating identity

```text
sum_(n>=0)c_n p_ell(n)x^n=(1+x)^ell/(1-x)^(ell+1/2)
```

and `sum c_ell z^ell=(1-z)^(-1/2)` give

```text
sum_(i,j>=0)c_i c_j P_(i,j)(s)x^i y^j
 =1/sqrt((1-x)(1-y)+s^2(1+x)(1+y)).                  (A23)
```

This is a formal-power-series proof, so no boundary interchange is hidden in `(A23)`.  Put

```text
a(s)=(1-s^2)/(1+s^2),
phi_a(x)=(a-x)/(1-a x),
psi_a(x)=(x-a)/(1-a x)=-phi_a(x).
```

Factoring the denominator in `(A23)` and extracting the coefficient of `y^j` gives

```text
sum_(i>=0)c_i P_(i,j)(s)x^i
 =(1+s^2)^(-1/2)(1-a(s)x)^(-1/2)phi_(a(s))(x)^j.     (A24)
```

Let `H_(1/2)` be the reproducing-kernel Hilbert space on the disk with kernel
`(1-z conjugate(w))^(-1/2)` and orthonormal basis `e_n(z)=sqrt(c_n)z^n`.  Define the full,
not-yet-parity-projected matrix

```text
K_s(i,j)=(-1)^j sqrt(c_i c_j)P_(i,j)(s).
```

Equation `(A24)` says exactly

```text
(K_s f)(z)
 =(1+s^2)^(-1/2)(1-a(s)z)^(-1/2)f(psi_(a(s))(z)).    (A25)
```

The classical weighted-composition representation

```text
(U_a f)(z)
 =(1-a^2)^(1/4)(1-a z)^(-1/2)f(psi_a(z))             (A26)
```

is unitary on `H_(1/2)`.  Indeed

```text
1-psi_a(z)conjugate(psi_a(w))
 =(1-a^2)(1-z conjugate(w))/((1-a z)(1-a conjugate(w))),
```

so `(A26)` preserves every reproducing-kernel inner product and hence their dense span.  Since

```text
(1-a(s)^2)^(1/4)=sqrt(2s)/sqrt(1+s^2),
```

`(A25)` becomes the exact operator identity

```text
K_s=(2s)^(-1/2)U_(a(s)).                              (A27)
```

No positivity or parity has been discarded.  The source matrix is zero across opposite
parities, while on equal parities its entry is `K_s(i,j)=K_s(j,i)`.  Therefore its literal
same-parity kernel is

```text
B_s=(K_s+K_s^*)/2
    =(2s)^(-1/2)(U_(a(s))+U_(-a(s)))/2.               (A28)
```

Here `U_a^*=U_(-a)`.  Direct substitution in `(A26)` proves the group law

```text
U_a U_b=U_((a+b)/(1+ab)),
a(st)=(a(s)+a(t))/(1+a(s)a(t)).                       (A29)
```

Fix `0<q<1`, put `t=sqrt(q)` and `T=U_(a(q))`.  Expanding every Lambert denominator in the
published CCM entry `(A3)`, then using `(A28)` and `(A29)`, gives the complete infinite source
operator

```text
A(q)=2sqrt(2)sum_(r>=1)q^r B_(q^r)
    =sum_(r>=1)t^r(T^r+T^(-r)).                       (A30)
```

Thus all odd harmonics, all Lambert repetitions, both parity blocks, and all determinant trace
powers are generated by one hyperbolic translation.  The geometric series give the exact
Poisson/resolvent factorization

```text
I+A(q)
 =(1-q)(I-tT)^(-1)(I-tT^*)^(-1).                     (A31)
```

In particular `I+A(q)` is strictly positive.  Every source finite section is its principal
compression, hence is strictly positive too.  The determinant logarithm used in Route J is
therefore the canonical real logarithm; no formal branch choice or small-`q` positivity
assumption remains.

### Uniform finite-section Hilbert--Schmidt theorem

The infinite norm in `(A27)` is singular as `s->0`, but the low-degree finite section is not.
Let `Q_N` project onto `e_0,...,e_N`.  There is an absolute constant `C` such that, uniformly for
`0<s<=1`,

```text
||Q_N K_s Q_N||_HS^2
 <=C(N+1)(1+log(N+2))^2.                              (A32)
```

Here is a dependency-closed proof.  Write

```text
F_s(x,y)=sum a_(i,j)x^i y^j,
a_(i,j)=c_i c_j P_(i,j)(s).
```

Choose `r=1-1/(N+2)`.  Then `r^(-4N)` is bounded absolutely.  Parseval applied to `(A23)` gives

```text
sum_(i,j>=0)|a_(i,j)|^2 r^(2i+2j)
 =average_(|zeta|=|eta|=1)|F_s(rzeta,reta)|^2.        (A33)
```

For `0<=R<1`, elementary splitting at angular distance `1-R` gives

```text
average_(|zeta|=1) 1/|1-Rzeta|
 <=C(1+log(1/(1-R))).                                 (A34)
```

For completeness, square the denominator as
`(1-R)^2+4R sin^2(theta/2)`.  The range `R<=1/2` is bounded.  For `R>1/2`, use
`sin(theta/2)>=theta/pi` on `0<=theta<=pi` and integrate
`((1-R)^2+c theta^2)^(-1/2)`.

Factor `(A23)` as

```text
F_s(x,y)
 =(1+s^2)^(-1/2)(1-a(s)x)^(-1/2)
   (1-phi_(a(s))(x)y)^(-1/2).                         (A35)
```

Because `phi_a` maps the disk to itself, integrate first in `eta`, then in `zeta`, and apply
`(A34)` twice.  The right side of `(A33)` is at most
`C(1+log(N+2))^2`.  Finally Wallis gives

```text
1/(c_i c_j)<=C(N+1),  0<=i,j<=N,
```

and

```text
|K_s(i,j)|^2=c_i c_j|P_(i,j)(s)|^2
             =|a_(i,j)|^2/(c_i c_j).
```

Removing the Abel weights costs only the bounded factor `r^(-4N)`, proving `(A32)`.
Symmetrization cannot increase the bound by more than an absolute factor, so `(A28)`--`(A32)`
and the triangle inequality yield

```text
||Q_N A(q)Q_N||_HS
 <=C q/(1-q) sqrt(N+1)(1+log(N+2)).                   (A36)
```

For a finite self-adjoint matrix `H`,

```text
|Tr(H^k)|<=||H||_op^(k-2)||H||_HS^2,  k>=2.           (A37)
```

Consequently, whenever the right side of `(A36)` tends to zero,

```text
|log det(I+Q_N A(q)Q_N)-Tr(Q_N A(q)Q_N)|
 <=C||Q_N A(q)Q_N||_HS^2
 <=C q^2(N+1)(1+log(N+2))^2.                          (A38)
```

At the genuine Route-J scale `N asymp q^(-4/3)`, `(A36)` is
`O(q^(1/3)log(1/q))` and `(A38)` is `O(q^(2/3)log^2(1/q))`.  This proves a uniform exact lift of
the complete nonlinear determinant logarithm *before* Jacobi amplification.  It also proves
that no hidden large trace power invalidates the log series at the critical scale.

### Exact surviving obstruction

Estimate `(A38)` alone does not close Route J.  The determinant quotient for the Jacobi radius
and the later four-radius current apply discrete boundary operators with coefficients growing
like `N` and `N^2`; an unstructured `o(1)` determinant error can therefore be amplified.  The
next theorem must control boundary increments, not raw determinants.

If

```text
L_N(q)=log det(I+Q_N^(parity N) A(q)Q_N^(parity N)),
delta_N=L_N-L_(N-2),
```

then the exact CCM determinant quotient is

```text
log(a_N(q)^2/a_N(0)^2)=delta_(N+1)-delta_N.            (A39)
```

Moreover, positivity from `(A31)` gives the exact Schur-complement boundary formula

```text
delta_N
 =log(1+A_(N,N)-v_N^*(I+A_(N-2))^(-1)v_N),            (A40)
```

where `v_N` is the same-parity boundary row against indices at most `N-2`.  Equations
`(A39)`--`(A40)` locate the survivor sharply: prove uniform first and second discrete regularity
of the source-defined Schur energy in `(A40)` through the literal four-radius stencil.  In the
unitary form this is the finite-section overlap problem

```text
Tr(Q_N T^(epsilon_1 r_1)Q_N ...
   Q_N T^(epsilon_k r_k)Q_N),                          (A41)
```

with `epsilon_i in {+1,-1}`, `r_i>=1`, and `T=U_(a(q))`, under `Nq^2->0`.  Raw higher traces are
now closed; their amplified boundary regularity is not.  This survivor belongs to Route J
because `(A39)` is the literal source Jacobi quotient, not an auxiliary route.

The classical ingredients in `(A23)`--`(A29)` are Meixner generating functions and the
`SU(1,1)` weighted-composition representation.  The CCM paper proves the rank-one Lambert
decomposition and coefficient integrality, but does not state `(A30)`--`(A41)` or a joint
`N,q` finite-section estimate.  A targeted primary-literature search found classical
Meixner/`su(1,1)` representation theory, but no treatment of this exact CCM specialization and
its four-radius finite-section determinant.  Novelty therefore remains explicitly unverified
until a broader literature audit; no novelty label stronger than the one above is claimed.

## 2026-08-02 frontier advance: exact Jacobi bispectrality and boundary Wronskians

`[PAPER-PROVED SOURCE BISPECTRAL RECURRENCE]`
`[PAPER-PROVED FULL-OVERLAP CHRISTOFFEL--DARBOUX REDUCTION]`
`[CLASSICAL CHRISTOFFEL--DARBOUX BRIDGE]`
`[PARITY-CONFLUENT DOUBLE-SCALING OPEN]`

The weighted-composition identification also supplies the missing finite-section difference
equation.  Fix `0<s<=1`, abbreviate `a=a(s)`, and put

```text
g_(i,j)(s)=sqrt(c_i c_j)P_(i,j)(s),
rho_i=sqrt((i+1/2)(i+1)),
rho_(-1)=0.
```

For fixed `j`, equation `(A24)` is the ordinary generating function

```text
H_j(x)=sum_(i>=0)c_iP_(i,j)(s)x^i
 =(1+s^2)^(-1/2)(1-a x)^(-1/2)((a-x)/(1-a x))^j.
```

Logarithmic differentiation, with `D(x)=(a-x)(1-a x)`, gives the exact polynomial differential
identity

```text
D(x)H_j'(x)
 =[j(a^2-1)+a^2/2-(a/2)x]H_j(x).                     (A42)
```

Coefficient extraction and `c_(i+1)/c_i=(i+1/2)/(i+1)` prove

```text
a rho_i g_(i+1,j)+a rho_(i-1)g_(i-1,j)
 =[(1+a^2)i+(a^2-1)j+a^2/2]g_(i,j).                 (A43)
```

The `i=0` equation uses `rho_(-1)g_(-1,j)=0`.  Thus columns of exact source kernel diagonalize
the explicit Jacobi operator

```text
(J_a f)_i
 =a rho_i f_(i+1)+a rho_(i-1)f_(i-1)
  -[(1+a^2)i+a^2/2]f_i,                              (A44)
```

with eigenvalue `(a^2-1)j`.  Symmetry in `i,j` gives the dual equation.  Subtracting two forms
yields exact bispectral conservation law

```text
a[rho_i g_(i+1,j)+rho_(i-1)g_(i-1,j)
  -rho_j g_(i,j+1)-rho_(j-1)g_(i,j-1)]
 =2(i-j)g_(i,j).                                      (A45)
```

Normalize to self-adjoint unitary reflection matrix from `(A27)`:

```text
v_(i,j)(s)=sqrt(2s)g_(i,j)(s).
```

Weighted-composition proof gives both `v_(i,j)=v_(j,i)` and
`sum_j v_(i,j)v_(k,j)=delta_(i,k)`.  Let

```text
lambda_i=(a^2-1)i,       beta_N=a rho_N.
```

For `i!=k`, multiply `(A44)` for spectral labels `i,k` by opposite solution and subtract.
Summing from `0` through `N` telescopes every interior term.  This proves exact finite-overlap
Christoffel--Darboux identity

```text
(lambda_i-lambda_k) sum_(r=0)^N v_(i,r)v_(k,r)
 =beta_N[
    v_(N+1,i)v_(N,k)-v_(N,i)v_(N+1,k)
  ].                                                   (A46)
```

Equation `(A46)` reduces finite-section translation overlap from an `N`-term bulk sum to one
boundary Wronskian.  It applies before asymptotic approximation and uniformly in Lambert scale.
By polarization, every nonconfluent quadratic finite-section overlap in expansion `(A41)` is
controlled by boundary matrix coefficients.

Exact survivor is now smaller but not closed:

1. trace square needs confluent limit `i=k` of `(A46)`, hence spectral derivative of boundary
   Wronskian;
2. CCM block keeps only indices of one parity, requiring even/odd (equivalently `2x2`
   block-Jacobi) Christoffel--Darboux formula instead of full projection in `(A46)`;
3. all `k>=3` cycles require iterated boundary overlaps after intermediate finite projections;
4. these Wronskians need estimates in joint regime
   `s->0`, `N s->infinity`, `N s^2->0`, then passage through `(A39)` and literal four-radius
   stencil.

Recurrence shows why fixed-degree Meixner asymptotics are insufficient.  In Route-J regime local
characteristic roots of `(A43)` coalesce while accumulated phase is large:

```text
phase increment ~2s sqrt(j/i),
total phase ~4s sqrt(i j),
N s^2->0 but N s->infinity.                           (A47)
```

Required new theorem is a parity-confluent discrete WKB estimate for `(A43)` with enough
spectral-derivative control to bound `(A46)` and its iterates.  This is exact source-defined
prolate concentration problem left by Route J, not reassignment to another route.

Formal status: scalar hyperbolic parameter algebra, exact source-denominator factorization,
resolved Poisson positivity/strict positivity, compression stability, and four-index boundary
identity are now unconditional in

```text
formal/GaloisForLFunctions/RHTower/
  SemilocalProlateHyperbolicPoissonSource.lean
```

Analytic Wronskian estimates `(A42)`--`(A47)` are not yet Lean-formalized.

## 2026-08-02 frontier advance: exact generator and oscillatory spectral multiplier

`[PAPER-PROVED ONE-GENERATOR REDUCTION]`
`[CLASSICAL MEIXNER--POLLACZEK BRIDGE]`
`[DOUBLE-SCALING SZEGŐ LAW OPEN]`

There is a second exact form of the same source.  Write

```text
s=exp(-u),       u>=0.
```

Then

```text
a(s)=(1-exp(-2u))/(1+exp(-2u))=tanh(u).               (A48)
```

Differentiate weighted composition `(A26)` at `a=0`.  On analytic polynomials its infinitesimal
generator is

```text
(Xf)(z)=(z/2)f(z)+(z^2-1)f'(z).                       (A49)
```

Since `c_(n+1)/c_n=(n+1/2)/(n+1)`, the orthonormal basis action is exactly

```text
X e_n=rho_n e_(n+1)-rho_(n-1)e_(n-1).                 (A50)
```

Thus `X` is skew-symmetric on finite sequences; closure of classical discrete-series
representation is skew-adjoint.  Group law `(A29)` and differentiation at zero give

```text
U_(a(exp(-u)))=U_(tanh u)=exp(uX).                    (A51)
```

After diagonal phase conjugation, `iX` is real Jacobi operator with off-diagonal coefficients
`rho_n`; its generalized eigenfunctions are Meixner--Pollaczek polynomials with lowest weight
`1/4` (up to conventional spectral scaling).  This representation-theoretic identification is
classical.  What is source-specific is the locked relation between group time `u`, Poisson radius
`exp(-u/2)`, and CCM finite K-type cutoff.

Let `H=iX`, so `exp(uX)=exp(-iuH)`.  Spectral theorem turns exact resolvent factorization `(A31)`
into scalar multiplier

```text
m_u(xi)
 =(1-exp(-u))/|1-exp(-u/2)exp(-iu xi)|^2
 =sinh(u/2)/(cosh(u/2)-cos(u xi)).                    (A52)
```

Equivalently,

```text
m_u(xi)-1
 =sum_(r>=1)exp(-ru/2)
    [exp(-iru xi)+exp(iru xi)].                        (A53)
```

Therefore every CCM parity determinant is a finite K-type compression of the single positive
oscillatory multiplier `m_u(H)`.  This supplies three exact conclusions:

1. positivity in `(A31)` is spectral, not coefficientwise accidental;
2. Lambert repetition `r` is literally Fourier mode `r` of one multiplier;
3. all higher determinant traces are finite-section Szegő cumulants for the same Jacobi spectral
   projection.

Existing Meixner and Meixner--Pollaczek Plancherel--Rotach results treat fixed admissible
orthogonality parameters or standard bulk/edge limits.  Existing Christoffel--Darboux results for
periodically modulated unbounded Jacobi matrices likewise keep spectral compacta fixed.  They do
not give the coupled regime here:

```text
u->infinity,
N exp(-u)->infinity,
N exp(-2u)->0,
N asymp exp(4u/3),                                    (A54)
```

nor spectral derivatives and parity-residue kernels uniform enough for determinant cumulants.
Required frontier theorem can now be stated invariantly:

> Prove a parity-resolved strong Szegő/cumulant estimate for K-type compressions of `(A52)` in
> regime `(A54)`, with enough discrete cutoff derivatives to pass through both the source
> determinant quotient and literal four-radius map.  Odd cumulants of order at least three, all
> even cumulants, and square-root products must vanish after that complete amplified map, while
> first cumulant has exact signed limit `(A22)`.

This formulation is equivalent to parity-confluent WKB problem `(A42)`--`(A47)`, but exposes its
classical Jacobi spectral measure and prevents treating higher traces as unrelated combinatorics.

## 2026-08-02 frontier advance: uniform damped-cosine theorem

`[PAPER-PROVED UNIFORM TWO-INDEX KERNEL LIFT]`
`[SOURCE-SPECIFIC NOVELTY UNVERIFIED]`
`[DISCRETE-DERIVATIVE LIFT OPEN]`

The feared two-index WKB estimate has an elementary exact reduction.  Euler transformation in
`(A2)` writes, for `i,j>=1`,

```text
P_(i,j)(s)
 =a(s)^(i+j)/sqrt(1+s^2) F_(i,j)(U),
U=4s sqrt(i j)/(1-s^2),                                (A55)
```

where

```text
F_(i,j)(U)
 =sum_(k=0)^min(i,j) (-1)^k r_k U^(2k)/(2k)!,
r_k=(i falling k)/i^k * (j falling k)/j^k.             (A56)
```

This follows directly from

```text
(1/2)_k k!=(2k)!/4^k.
```

Unlike an absolute-value estimate of hypergeometric series, `(A56)` retains every oscillatory
cancellation.  Extend `r_k` by zero past `min(i,j)`.  Its exact ratio is

```text
r_(k+1)=r_k(1-k/i)(1-k/j),                             (A57)
```

including terminal index because one factor then vanishes.  With Euler operator
`Theta=(U/2)d/dU`, coefficient comparison gives exact differential equation

```text
F''+F=(1/i+1/j)Theta F-(1/(i j))Theta^2 F.             (A58)
```

Equivalently,

```text
(1+U^2/(4ij))F''
 -[U(1/i+1/j)/2-U/(4ij)]F'+F=0,                       (A59)
F(0)=1,   F'(0)=0.
```

This is the crucial stability form.  Put

```text
b(U)=[U(1/i+1/j)/2-U/(4ij)]/[1+U^2/(4ij)],
c(U)=[U^2/(4ij)]/[1+U^2/(4ij)].
```

Then `(A59)` is

```text
F''+F=b(U)F'+c(U)F.                                    (A60)
```

For `0<s<=1/2` and `0<=u<=U`, elementary integration gives

```text
integral_0^U (|b(u)|+|c(u)|)du
 <=C[s^2(i+j)+s^3 sqrt(i j)]
 <=C s^2(i+j).                                        (A61)
```

Indeed `U<=C s sqrt(ij)`, so the two integrals are bounded by constant multiples of
`U^2(1/i+1/j)` and `U^3/(ij)`.  View `(A60)` as first-order system with unperturbed rotation
matrix.  Variation of constants and Gronwall prove

```text
sup_(0<=u<=U)(|F_(i,j)(u)|+|F_(i,j)'(u)|)
 <=C exp(C s^2(i+j)),                                  (A62)

|F_(i,j)(U)-cos(U)|+|F_(i,j)'(U)+sin(U)|
 <=C s^2(i+j) exp(C s^2(i+j)).                         (A63)
```

No unproved interchange occurs: `F` is finite polynomial and `(A58)` is coefficientwise.

It remains to return from `U` to physical phase `4s sqrt(ij)`.  For `s<=1/2`,

```text
|U-4s sqrt(ij)|<=C s^3 sqrt(ij),
|1-a(s)^(i+j)|<=C s^2(i+j),
|1-(1+s^2)^(-1/2)|<=C s^2.                            (A64)
```

The first bound is algebraic, the second uses
`1-x^m<=(m)(1-x)` for `0<=x<=1`, and cosine is one-Lipschitz.  Equations `(A55)`--`(A64)` prove
the uniform theorem

```text
|P_(i,j)(s)-cos(4s sqrt(i j))|
 <=C s^2(i+j+1) exp(C s^2(i+j))                       (A65)
```

for all natural `i,j`, with `i=0` or `j=0` handled directly from `(A24)`.  In particular,

```text
max_(0<=i,j<=N)
 |P_(i,j)(s)-cos(4s sqrt(i j))| ->0                   (A66)
```

whenever `s->0` and `Ns^2->0`.  This is precisely the formerly missing two-index uniform lift;
standard Meixner results at fixed orthogonality parameter do not supply `(A65)`.

### Complete Lambert operator lift in Hilbert--Schmidt norm

Define literal same-parity cosine model

```text
C_(i,j)(q)
 =(-1)^j 2sqrt(2)sqrt(c_i c_j)
   sum_(r>=1)q^r cos(4q^r sqrt(i j))
```

when `i-j` is even, and zero otherwise.  Equations `(A3)` and `(A65)`, summed over every Lambert
repetition, give for `0<=i,j<=N` and `Nq^2<=1`

```text
|gamma_(i,j)(q)-C_(i,j)(q)|
 <=C q^3(i+j+1)sqrt(c_i c_j).                         (A67)
```

Using Wallis sums

```text
sum_(i<=N)c_i=O(sqrt(N+1)),
sum_(i<=N)i c_i=O((N+1)^(3/2)),
sum_(i<=N)i^2 c_i=O((N+1)^(5/2)),
```

one obtains exact finite-section bound

```text
||Q_N(A(q)-C(q))Q_N||_HS
 <=C q^3(N+1)^(3/2).                                  (A68)
```

At critical scale `N asymp q^(-4/3)`, error in `(A68)` is `O(q)`, versus leading operator size
`O(q^(1/3))`.  Telescoping `A^k-C^k` and applying Hilbert--Schmidt Cauchy--Schwarz therefore
uniformly lift every fixed raw trace power `k>=2` from associated cosine cycle kernel; `k=1` is
already covered more sharply by exact Legendre theorem `(A19)`.

Anti-theatre boundary: `(A65)`--`(A68)` still do not finish higher determinant terms.  Literal
Jacobi/current map differentiates cutoff `N`; a Hilbert--Schmidt approximation without controlled
first and second discrete `N`-differences can still be amplified.  Remaining theorem is the
discrete-derivative version of damped-cosine stability: differentiate recurrence `(A57)` with
respect to integer parameters (equivalently compare adjacent coefficient ratios), propagate it
through `(A60)`, and prove boundary-row/cycle errors remain lower after `(A39)` and four-radius
stencil.

## 2026-08-02 frontier advance: nonlinear determinant closure and parity endpoint anomaly

`[PAPER-PROVED COMPLETE HIGHER-CUMULANT STENCIL BOUND]`
`[PAPER-PROVED PARITY ENDPOINT CLASSIFICATION]`
`[SOURCE-SPECIFIC NOVELTY UNVERIFIED]`
`[SEMILOCAL DETERMINANT SURVIVOR CLOSED]`

The discrete derivative required after `(A68)` can be proved without a new steepest-descent
argument.  Comparing equations `(A60)` for `(i,j)` and `(i+1,j+1)` gives an inhomogeneous
rotation system with zero initial data.  Differences of its coefficients satisfy, for `i,j>=1`,

```text
integral_0^U |b_(i+1,j+1)-b_(i,j)|
 <=C s^2(j/i+i/j+1),

integral_0^U |c_(i+1,j+1)-c_(i,j)|
 <=C s^3(sqrt(j/i)+sqrt(i/j)+1).                      (A69)
```

Endpoint change in `U` is at most
`Cs(sqrt(j/i)+sqrt(i/j)+1)`.  Apply variation of constants exactly as in `(A62)`--`(A63)` and
use the derivative error already present in `(A63)`.  For residual

```text
E_(i,j)(s)=P_(i,j)(s)-cos(4s sqrt(i j))
```

this gives

```text
|E_(i+1,j+1)(s)-E_(i,j)(s)|
 <=C exp(Cs^2(i+j))[
      s^2(1+j/i+i/j)
      +s^3(i+j+1)(1+sqrt(j/i)+sqrt(i/j))
    ].                                                 (A70)
```

If one index is zero, `(A24)` gives the same weighted summation bounds directly.  Equations
`(A69)`--`(A70)` are ordinary ODE stability: subtract two copies of `(A60)`, bound forcing by
displayed coefficient differences, and apply Gronwall.  Thus no differentiability in a discrete
index is assumed.

For the cycle estimates, set

```text
I_N={j:0<=j<=N and j=N mod 2},
S_N=sum_(j in I_N)c_j.
```

Exact central-binomial ratio and Wallis give

```text
c_(j+1)=c_j(1-1/(2j+2)),
S_N<=C sqrt(N+1),
sum_(j<=N)c_j/sqrt(j+1)<=C(1+log(N+2)),
sum_(j<=N)sqrt(j+1)c_j<=C(N+1).                       (A71)
```

Let `C_N(q)` be same-parity cosine matrix in `(A67)`, with cutoff `I_N`, after removing constant
block sign `(-1)^N`.  Put

```text
B_(N,k)=Tr(C_N(q)^k),
d_(N,k)=B_(N,k)-B_(N-2,k).
```

Expanding a trace as a cycle, every monomial in `d_(N,k)` contains boundary index `N`.  Fix one
occurrence and use `|C_(i,j)|<=Cq sqrt(c_i c_j)`.  The product around cycle is
`(Cq)^k product c_(i_r)`, hence

```text
|d_(N,k)|
 <=C_k q^k c_N S_N^(k-1)
 <=C_k q^k(N+1)^((k-2)/2).                            (A72)
```

This includes repeated boundary occurrences because choosing first occurrence only overcounts by
factor `k`.

The aligned even/odd comparison uses bijection `2r -> 2r+1`.  From `(A71)`, total weight-shift
cost is a boundary stratum smaller by `N^(-1/2)`.  For phase, elementary identity

```text
|sqrt((i+1)(j+1))-sqrt(i j)|
 <=C(1+sqrt((i+1)/(j+1))+sqrt((j+1)/(i+1)))
```

and `|cos x-cos y|<=|x-y|` give one factor `q`; the ratio sums are controlled by last two sums in
`(A71)`.  Telescoping one factor around cycle proves

```text
aligned variation of d_(N,k)
 <=C_k q^k(N+1)^((k-2)/2)
      [q(1+log(N+2))+1/sqrt(N+1)].                    (A73)
```

The exact-kernel error `(A67)` has one extra factor `q^2N`.  Using `(A70)` on changed factor and
`(A71)` on remaining cycle variables yields

```text
boundary-cycle error
 <=C_k q^(k+2)(N+1)^(k/2),                            (A74)

aligned variation of boundary-cycle error
 <=C_k q^(k+2)(N+1)^(k/2)
      [q(1+log(N+2))+1/sqrt(N+1)].                    (A75)
```

These estimates are uniform over Lambert repetitions because differentiated repetition `r`
contains `q^(2r)` and `sum q^(2r)<=Cq^2`.

### The previously hidden `k=2` endpoint

Bound `(A73)` is sufficient for `k>=3`, but at `k=2` its `N^(-1/2)` term is potentially critical
after naive `N^2` amplification.  It cannot be discarded.  Exact square-cycle boundary is

```text
d_(N,2)
 =2 sum_(j in I_(N-2)) C_(N,j)(q)^2+C_(N,N)(q)^2.    (A76)
```

Pair `N=2m` with `N=2m+1` and write uniquely

```text
d_(2m,2)=M_m+E_m,
d_(2m+1,2)=M_m-E_m.                                  (A77)
```

Termwise shift in `(A76)`, using exact first identity in `(A71)`, separates two effects:

```text
|M_(m+1)-M_m|
 <=C[q^3(1+log(N+2))+q^2/(N+1)],

|E_m|
 <=C[q^2/sqrt(N+1)+q^3(1+log(N+2))],

|E_(m+1)-E_m|
 <=C[q^2/(N+1)^(3/2)
      +q^3(1+log(N+2))/sqrt(N+1)
      +q^4(1+log(N+2))^2].                            (A78)
```

For clarity, first line is common bulk/upper-endpoint motion.  Second is lower parity endpoint
plus phase motion.  Third follows by applying same shift once more.  All sums are the three
elementary sums in `(A71)`; no Euler--Maclaurin remainder is being assumed.

The `q^2/sqrt(N)` term is real and has an exact leading parity constant.  Generating functions

```text
sum_(m>=0)c_(2m)z^m
 =[(1-sqrt(z))^(-1/2)+(1+sqrt(z))^(-1/2)]/2,

sum_(m>=0)c_(2m+1)z^m
 =[(1-sqrt(z))^(-1/2)-(1+sqrt(z))^(-1/2)]/(2sqrt(z))
```

show regular constants `+1/(2sqrt(2))` and `-1/(2sqrt(2))` at `z=1`.  Since cosine-square kernel
equals one at lower endpoint, their difference is `-1/sqrt(2)`.  For first Lambert mode this
gives

```text
d_(N+1,2)-d_(N,2)
 =(-1)^(N+1)8sqrt(2/pi) q^2/sqrt(N)+
   common smooth terms+o(q^2/sqrt(N)).                 (A79)
```

So associated-graded assertion that every even trace simply loses two ordinary powers was too
coarse: there is a half-power parity endpoint anomaly.  It still cannot cancel `(A22)`.  In log
determinant, `k=2` coefficient is `-1/2`, and positive radius takes another factor `1/2`.
Equation `(A79)` therefore creates an alternating radius perturbation of size `O(q^2 sqrt(N))`.
After its sign is removed, last two lines of `(A78)` show literal four-radius stencil is

```text
O(q^3 N^(3/2)(1+log N)+q^2 sqrt(N)),                  (A80)
```

which tends to zero for `N asymp q^(-4/3)`.  Endpoint anomaly is classified and closed, not
ignored.

### All cumulants and square root

For odd `k`, block sign is `(-1)^N`; determinant quotient uses sum of two adjacent boundary
increments, and final alternating four-radius stencil differentiates their sign-removed amplitude.
For even `k`, determinant quotient uses their difference; `(A73)` supplies required gain.  At
`N asymp q^(-4/3)`:

```text
k=2: O(q^(1/3)(1+log(1/q)))+O(q^(4/3)),
k=3: O(q^(1/3)(1+log(1/q))),
k=4: O(q^(2/3)(1+log(1/q))),                          (A81)
```

after complete determinant-quotient and four-radius map.  For `k>=5`, `(A72)` alone gives

```text
O(q^k N^(k/2+1))=O(q^(k/3-4/3));                     (A82)
```

sum over all `k>=5` is geometric because `q sqrt(N)=O(q^(1/3))`.  Error terms `(A74)`--`(A75)`
are smaller.  Hence complete `k>=2` log-determinant contribution is `o(1)`.

Finally exact one-trace log-radius satisfies `O(q/sqrt(N))` by `(A14)`.  Quadratic exponential
term in positive radius is therefore `O(q^2)` after multiplying by `rho_N`; its four-radius image
is `O(Nq^2)=O(q^(2/3))`.  Products involving higher-log part are smaller.  Thus square-root
nonlinearity is also `o(1)`.

Combining `(A19)`, `(A22)`, and `(A69)`--`(A82)` proves exact full semilocal determinant current,
not only trace-linear part, has opposite limits

```text
-32sqrt(2/pi),       +32sqrt(2/pi)                    (A83)
```

along nearby even source indices at every sufficiently large prime.  No higher determinant
trace, parity endpoint, or positive-radius square root can restore sign-definiteness.  Semilocal
determinant survivor is closed on paper.

Route J remains open: next survivor is whether finite-prime orthogonalization, Sonin transport,
or global singular-carrier descent changes this local signed obstruction before it reaches fixed
target-free Meyer source `(A22)`.

## 2026-08-02 hostile correction: determinant closure not yet dependency-closed

`[RETRACT PREMATURE SEMILOCAL DETERMINANT SURVIVOR CLOSED TAG]`
`[A73 AND A78 OPEN]`

A hostile reread does not accept the preceding all-cumulant section as a paper proof.  The cycle
boundary estimate `(A72)` is dependency-closed, but `(A73)` compresses the aligned parity
comparison into “total weight-shift cost” without an explicit telescoping identity, and `(A78)`
asserts first and second parity endpoint differences without displaying the exact decomposition or
summable majorants term by term.  Later bounds `(A80)`--`(A83)` depend on those two estimates.

Therefore `(A83)` remains a conjectural full-determinant lift.  Exact trace-linear sign obstruction
`(A19)`--`(A22)`, hyperbolic factorization, damped-cosine kernel theorem, and raw cycle bound remain
proved.  Route J has two live source-level obligations rather than a closed semilocal branch:

1. prove `(A73)` and `(A78)` with literal parity/cutoff formulas; and
2. construct the depth-nonlocal Gamma/co-Poisson common reporter surviving the width--capacity
   obstruction in `route-j-replica-common-hardy-width-capacity-obstruction.md`.
