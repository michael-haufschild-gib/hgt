# The signed Möbius coisometry is an exact Schur transfer on the Euler side

- **ID:** `mobius-signed-coisometry-schur-transfer-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** the squarefree Euler product, the Laplace shift representation, and Hardy
  multiplier theory
- **Statement:** The signed channel projection of the coupled floor--Möbius source is multiplication
  by an explicit Schur function on the Euler half-plane. Its complete causal Laplace transform is
  an exact quotient of two shifted zeta functions. Hence the arithmetic synthesis is already
  contractive before continuation; the remaining RH-bearing operation is the orbit-sensitive
  contour transfer across the poles created by off-line zeros.

## 1. Signed shift average

Fix `omega>0` and put

```text
sigma=1+2omega,
Z_omega=sum_(d>=1)mu(d)^2d^(-sigma)
       =zeta(sigma)/zeta(2sigma),                         (1)

P_omega(d)=mu(d)^2d^(-sigma)/Z_omega.                    (2)
```

Let `H=L2(R_(>=0),dt)` and let `V_h` be the unilateral right shift

```text
(V_h f)(t)=1_(t>=h)f(t-h).                               (3)
```

Define the signed average

```text
T_omega
 =sum_(d>=1)mu(d)P_omega(d)V_(log d).                    (4)
```

The series converges in operator norm because

```text
sum_d |mu(d)|P_omega(d)=1,
||V_(log d)||=1.                                         (5)
```

Thus `||T_omega||<=1`. This is the one-particle realization of the signed coisometry projection in
`mobius-signed-channel-coisometry-incidence-law.md`.

## 2. Exact Schur multiplier

For `Re z>0`, use the Laplace transform

```text
(L f)(z)=integral_0^infinity f(t)e^(-zt)dt.              (6)
```

Since

```text
L(V_(log d)f)(z)=d^(-z)Lf(z),                            (7)
```

equation `(4)` becomes

```text
L(T_omega f)(z)=tau_omega(z)Lf(z),                       (8)
```

where

```text
tau_omega(z)
 =sum_d mu(d)P_omega(d)d^(-z)
 =1/(Z_omega zeta(sigma+z))
 =zeta(2sigma)/(zeta(sigma)zeta(sigma+z)).               (9)
```

The Euler product is

```text
tau_omega(z)
 =product_p (1-p^(-(sigma+z)))/(1+p^(-sigma)).           (10)
```

For `Re z>=0`, every local factor satisfies

```text
|1-p^(-(sigma+z))|
 <=1+p^(-(sigma+Re z))
 <=1+p^(-sigma).                                         (11)
```

Absolute convergence for `sigma>1` therefore gives

```text
|tau_omega(z)|<=1,        Re z>=0.                       (12)
```

Thus `tau_omega` is a Schur multiplier of the right-half-plane Hardy space. The source contraction
is local-prime exact: it is the product of the Bernoulli sign contractions in `(10)`, not an
estimate imposed after summation.

At the constant character,

```text
tau_omega(0)
 =zeta(2sigma)/zeta(sigma)^2.                            (13)
```

This small coherent coefficient is the angle of the signed squarefree direction to the constant
divisor channel.

## 3. The power-sum boundary vector

Let

```text
a_omega(t)
 =e^(-(1+omega)t)sum_(m<=e^t)m^omega,
c_omega=1/(1+omega).                                     (14)
```

If `k_omega` is the normalized floor remainder from the signed-channel theorem, then

```text
k_omega=a_omega-c_omega.                                 (15)
```

For every divisor channel,

```text
B_(omega,d)
 =V_(log d)k_omega-c_omega(I-P_d)1
 =V_(log d)a_omega-c_omega 1.                            (16)
```

The last expression is a difference of two non-`L2` terms, but their difference belongs to `L2`;
equation `(16)` is first interpreted pointwise and then in that `L2` difference.

For `Re z>0`, Tonelli's theorem gives the exact Laplace transform

```text
L a_omega(z)
 =sum_(m>=1)m^omega
    integral_(log m)^infinity e^(-(1+omega+z)t)dt
 =zeta(1+z)/(1+omega+z).                                 (17)
```

Consequently

```text
L B_(omega,d)(z)
 =d^(-z) zeta(1+z)/(1+omega+z)
  -c_omega/z.                                            (18)
```

## 4. Exact causal transfer function

Put

```text
F_omega(t)=e^(-(1+omega)t)E_omega(e^t),                  (19)
```

where `E_omega` is the coupled arithmetic error. The signed-channel projection identity says

```text
F_omega
 =sum_d mu(d)d^(-sigma)B_(omega,d)
 =Z_omega E_(P_omega)[mu(d)B_(omega,d)].                 (20)
```

Combining `(9)`, `(13)`, `(17)`, and `(20)` yields

```text
L F_omega(z)
 =zeta(1+z)
    /((1+omega+z)zeta(1+2omega+z))
  -1/((1+omega)z zeta(1+2omega)),
Re z>0.                                                   (21)
```

This is the complete signed projection, including the complementary floor counterterm. The first
term is the Schur-transferred power-sum boundary vector; the second is the exact constant-channel
subtraction.

At fixed `Re z>0`, letting `omega` decrease to zero gives

```text
L F_omega(z)->1/(1+z).                                   (22)
```

Differentiating the meromorphic expression `(21)` at `omega=0+` gives

```text
partial_omega L F_omega(z)|_(0+)
 =-1/(1+z)^2
  -2/(1+z) zeta'(1+z)/zeta(1+z)
  -2/z.                                                   (23)
```

This agrees with the critical derivative source obtained from
`partial_omega E_omega(X)|_(0+)=2(psi(X)-X)`, including the derivative of the exterior exponential
normalization and the pole counterterm.

## 4a. Exact centered Hardy decomposition

Define the `H2` floor-remainder transform

```text
K_omega(z)
 =zeta(1+z)/(1+omega+z)-c_omega/z
 =L k_omega(z).                                           (23a)
```

Since `Z_omega tau_omega(z)=1/zeta(sigma+z)` and
`Z_omega tau_omega(0)=1/zeta(sigma)`, equation `(21)` is equivalently

```text
L F_omega(z)/Z_omega
 =tau_omega(z)K_omega(z)
  +c_omega (tau_omega(z)-tau_omega(0))/z.                 (23b)
```

The first term is the contractive image of the genuine `L2` floor remainder. The second term is
one centered boundary difference quotient of the explicit Schur function.

Its inverse Laplace vector is also explicit. Since

```text
(d^(-z)-1)/z=-integral_0^(log d)e^(-zt)dt,               (23c)
```

put

```text
g_omega(t)
 =-E_(P_omega)[mu(d)1_(0<=t<log d)].                     (23d)
```

Then

```text
L g_omega(z)
 =(tau_omega(z)-tau_omega(0))/z.                         (23e)
```

Moreover Cauchy--Schwarz in the probability space gives

```text
|g_omega(t)|^2
 <=P_omega{log d>t},                                     (23f)

||g_omega||_2^2
 <=E_(P_omega)[log d]
 =-zeta'/zeta(sigma)+2zeta'/zeta(2sigma).                (23g)
```

Thus the infinite signed-channel projection has been reduced exactly to two `L2` vectors:

```text
F_omega/Z_omega
 =T_omega k_omega+c_omega g_omega.                       (23h)
```

This reduction is strict: no non-`L2` constant remains.

The universal separate-term estimate is nevertheless insufficient. From `(23g)`,

```text
E_(P_omega)[log d]~1/(2omega),
Z_omega~1/(2omega zeta(2)).                               (23i)
```

Therefore contractivity of `T_omega` plus the triangle inequality yields only the divergent upper
bound `O(Z_omega/sqrt(omega))` for the boundary term. Any finite critical estimate
must use the signed covariance between `T_omega k_omega` and `c_omega g_omega`, or a sharper
source-specific norm law for the centered difference quotient. The positive minimal source object
is the paired vector in `(23h)`, not either component separately.

## 5. Where contractivity stops

Equation `(12)` proves all contractivity available on the Euler side `Re z>=0`. The anti-causal
profile does not live there. It is obtained by moving the inverse-transform contour to the Hardy
boundary used by Suzuki's inner-function criterion. Under meromorphic continuation, `(21)` has
possible poles at

```text
1+2omega+z=rho,
z=rho-1-2omega,                                          (24)
```

for zeta zeros `rho`. Moving the contour crosses exactly the zero modes recorded by the
anti-causal contour-jump profile.

Therefore the Schur estimate `(12)` cannot by itself prove the four-unit boundary inequality. A
channel-independent bounded operator commuting with `T_omega` preserves the Euler-side
contraction, but contour translation is not such a bounded operator on vectors with crossed poles.
Its graph domain must include the residue coordinates in `(24)`.

The positive continuation law forced on a successful construction is

```text
Euler-side Schur transfer tau_omega
  + an orbit-sensitive meromorphic graph domain carrying every crossed residue
  + nonexpansive renormalization of the distinguished pole vector
  -> ||ell_E||_2<=2.                                      (25)
```

This identifies the concrete meaning of the missing archimedean operator in the signed-channel
coisometry theorem: it is not ordinary bounded functional calculus of `T_omega`; it is the
cross-line continuation operator together with its residue seam.

## 6. Rational-orbit attack

Multiplying the completed carrier by a symmetric orbit polynomial changes the logarithmic source
by a rational term and inserts new poles of the continued transfer at the locations `(24)`, while
leaving the Euler-side squarefree multiplier `(9)` unchanged. Hence every proposed proof that
factors only through `tau_omega`, its `H-infinity` norm, or the diagonal squarefree distribution is
divisor-blind.

The continuation in `(25)` must satisfy the pointed gauge covariance

```text
G(source_Xi-2Dlog A)-G(source_Xi)=J_A,                   (26)
```

where `J_A` is the residue vector of the inserted orbit. This is precisely the source--divisor
marking formalized by the rational-quartet countermodel.

The horizontal-charge norm law sharpens this requirement. On a fixed Euler line, symmetric orbit
source corrections remain uniformly bounded as their horizontal displacement `a` tends to zero,
but `||J_A||_2^2` grows at least as `4m^2/a`. Therefore no universal bounded or uniformly
Lipschitz map in the ordinary Hardy norm can satisfy `(26)`. A successful version of `(25)` must
instead be a closed graph whose domain norm contains the Cauchy residue Gram form, or a genuinely
Xi-pointed nonuniform construction. The generic bounded-continuation candidate is closed; the
source-specific charged-graph estimate remains open.

## 7. Route verdict

- `[PROVED]` The signed channel average is an exact contraction.
- `[PROVED]` Its transfer function is the Schur product `(9)`--`(12)`.
- `[PROVED]` The complete coupled causal transform is `(21)`.
- `[PROVED]` The critical tangent transform is `(23)`.
- `[PROVED]` The non-`L2` boundary mode cancels into the two-vector Hardy decomposition `(23h)`.
- `[PROVED]` Ordinary bounded channel-independent functional calculus cannot perform the required
  cross-line continuation when poles are crossed.
- `[OPEN CORE]` Construct the orbit-sensitive continuation graph and prove its renormalized pole
  vector is nonexpansive.
- `[NOT PROVED]` The four-unit energy inequality and RH remain open.

The theorem is a direct Euler-product/Laplace-transform bridge. It identifies the exact boundary
where the signed-coisometry contraction ceases to be automatic, but it is not new scientific
knowledge.

## 8. Lean decision

The unconditional finite-aperture layer is formalized in
`formal/GaloisForLFunctions/RHTower/FiniteSignedChannelCoisometry.lean` and
`formal/GaloisForLFunctions/RHTower/MobiusFiniteSchurTransfer.lean`.  Lean proves the exact
squarefree probability normalization, the signed coisometry and idempotent channel projection,
the squarefree Euler expansion, and the local and finite-product Schur bounds on `Re z>=0`.

The formal certificate is recorded in
`docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/mobius-finite-schur-coisometry-core.md`.
The cofinal squarefree normalization is now formalized independently in
`formal/GaloisForLFunctions/RHTower/SquarefreeMoebiusNormalization.lean`, including the arithmetic,
L-series, and Euler-product faces of `sum mu(n)^2 n^(-s)=zeta(s)/zeta(2s)`.

`formal/GaloisForLFunctions/RHTower/InfiniteMobiusSignedChannel.lean` now consumes that
normalization to construct the actual all-prime signed amplitude as a unit vector in `ell^2(N)`.
It proves the infinite synthesis is a surjective coisometry, its adjoint is the analysis map, and
`R^*R` is a contractive idempotent projection onto the distinguished Möbius source line. The same
module constructs the absolutely summable average of the actual logarithmic `L^2(R)` translation
unitaries and proves it contractive. Thus the arithmetic cofinal projection and ambient shift
average are fully formalized. Causal-subspace preservation, the exact Laplace multiplier identity,
and the meromorphic continuation graph remain unformalized; the last is the RH-bearing layer.

## Gates

- [x] signed shift average constructed
- [x] exact Schur transfer function proved
- [x] local-prime contractivity proved
- [x] power-sum boundary transform proved
- [x] complete coupled causal transform proved
- [x] critical tangent transform proved
- [x] exact centered Hardy decomposition and boundary difference quotient proved
- [x] continuation-pole seam identified
- [x] rational-orbit marking obligation attached
- [x] universal bounded orbit-covariant continuation excluded
- [x] inverse-horizontal residue charge forced into the graph norm
- [x] finite squarefree probability, coisometry, Euler expansion, and Schur contraction formalized
- [x] cofinal squarefree Möbius--zeta normalization formalized
- [x] all-prime signed Möbius unit vector, coisometry, and contractive projection formalized
- [x] infinite logarithmic `L^2` signed shift average and contraction formalized
- [ ] causal Hardy restriction and exact multiplier identity formalized
- [ ] construct the Xi-pointed charged continuation graph
- [ ] prove nonexpansive pole-to-divisor renormalization in that graph
- [ ] four-unit boundary norm
- [ ] RH

## Lean formalization (this sweep, complete and unconditional)

`formal/GaloisForLFunctions/RHTower/MobiusSignedSchurComplexMultiplier.lean` (equations
`(9)`--`(13)`), `.../MobiusPowerSumBoundaryLaplace.lean` (equations `(14)`, `(17)` and the reusable
causal shift law) and `.../MobiusSignedSchurTransferPaper.lean` (equations `(18)`, `(21)`,
`(23a)`, `(23b)`, `(23d)`--`(23g)`) certify the card's proved payload.
