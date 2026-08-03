# One real Euler ray carries the complete shifted-Xi negative index

- **ID:** `ccm-real-euler-ray-loewner-index-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** locality of negative squares, the shifted-Xi generalized Schur kernel, and
  `euler-pick-inertia-offline-zero-count.md`

## Statement

Fix a nonexceptional `omega>0` and define, for

```text
y>1/2+omega,
```

the positive real Euler quotient

```text
f_omega(y)
 =xi(y+1/2-omega)/xi(y+1/2+omega).                       (1)
```

Both arguments in `(1)` lie in `Re s>1`, so `f_omega(y)` is positive and has an absolutely
convergent Euler-product formula. Define the real Hermitian kernel

```text
L_omega(x,y)
 =(1-f_omega(x)f_omega(y))/(x+y),
x,y>1/2+omega.                                           (2)
```

Then

```text
ind_-(L_omega)
 =sum_(xi(rho)=0, Re rho>1/2+omega)multiplicity(rho),    (3)
```

including the value `+infinity`.

Choose any dense sequence of rational numbers

```text
y_n in Q,       y_n>1/2+omega.                           (4)
```

For the nested real symmetric matrices

```text
L_(omega,N)
 =((1-f_omega(y_j)f_omega(y_k))/(y_j+y_k))_(j,k<=N),    (5)
```

one has

```text
lim_(N->infinity)nu_-(L_(omega,N))
 =sum_(Re rho>1/2+omega)multiplicity(rho).                (6)
```

Therefore

```text
no zero in Re rho>1/2+omega
 iff L_omega is positive semidefinite
 iff every matrix in (5) is positive semidefinite.       (7)
```

## Proof

The shifted-Xi quotient and its generalized Schur kernel are

```text
Theta_omega(z)
 =xi(1/2-omega-i z)/xi(1/2+omega-i z),                   (8)

S_omega(z,w)
 =i(1-Theta_omega(z)conjugate(Theta_omega(w)))
   /(z-conjugate(w)).                                    (9)
```

On the Euler uniqueness region

```text
U_omega={z:Im z>1/2+omega},                              (10)
```

the generalized Schur index theorem gives

```text
ind_-(S_omega|U_omega)
 =sum_(Re rho>1/2+omega)multiplicity(rho).                (11)
```

Restrict `(9)` to the vertical ray

```text
z=i y,       y>1/2+omega.                                (12)
```

Then `-iz=y`, so `(8)` becomes `(1)`. For `z=iy` and `w=ix`,

```text
i/(z-conjugate(w))=1/(x+y),                              (13)
```

and hence `(9)` becomes `(2)`.

The ray `(12)` is a uniqueness set inside the connected domain `U_omega`: a holomorphic function
vanishing on it has zeros accumulating at each interior ray point and therefore vanishes
identically. Consequently the kernel sections with nodes on `(12)` have dense span in the
reproducing-kernel Pontryagin space of `S_omega`. Locality of negative squares therefore gives

```text
ind_-(S_omega|ray)=ind_-(S_omega|U_omega).               (14)
```

Equations `(11)`--`(14)` prove `(3)`.

The rational dense sequence `(4)` remains a uniqueness set. Principal-matrix interlacing makes
`nu_-(L_(omega,N))` nondecreasing, and density of the corresponding kernel sections makes its
supremum equal the kernel index. This proves `(6)`--`(7)`. `QED`

## Explicit positive Euler formula

For `s>1`,

```text
xi(s)
 =1/2 s(s-1)pi^(-s/2)Gamma(s/2)
   product_p(1-p^(-s))^(-1).                             (15)
```

Thus `(1)` is

```text
f_omega(y)
 =pi^omega
  *s_-(s_--1)/(s_+(s_+-1))
  *Gamma(s_-/2)/Gamma(s_+/2)
  *product_p (1-p^(-s_+))/(1-p^(-s_-)),                 (16)

s_-=y+1/2-omega,
s_+=y+1/2+omega.
```

Every factor is real and positive. Hence every entry in `(5)` is obtained from positive
archimedean factors and absolutely convergent positive Euler products; no critical-strip
evaluation, zero ordinate, or complex sampling node is used.

## Positive CCM obligation

The shifted CCM problem is reduced to a one-variable real kernel theorem:

```text
positive Euler quotient f_omega on (1/2+omega,infinity)
  -> Cauchy--Loewner kernel
     (1-f_omega(x)f_omega(y))/(x+y)
  -> prove complete positivity
  -> eliminate every zero beyond 1/2+omega.              (17)
```

Cofinally, RH is equivalent to `(7)` along any nonexceptional sequence `omega_j downarrow 0`.

`[PROVED INFINITESIMAL CLOSURE]` Dividing `(2)` by `2omega` and letting `omega` decrease to zero
gives the single fixed kernel

```text
J(x,y)
 =[Q(x)+Q(y)]/(x+y),
Q(x)=xi'(1/2+x)/xi(1/2+x).
```

Its negative index is already the total right-half off-line multiplicity. Hence the entire
cofinal shift family may be replaced by complete positivity of one real Euler-region
log-derivative kernel. See `ccm-infinitesimal-real-euler-ray-logderivative-index-law.md`.

Pointwise bounds `0<f_omega(y)<1` are not sufficient: for unequal values `r_1,r_2`, the matrix

```text
(1-r_i r_j)_(i,j<=2)
```

has determinant `-(r_1-r_2)^2`. The required information is the complete Cauchy--Loewner geometry
of the source function, not scalar monotonicity or positivity of its Euler factors.

The theorem nevertheless removes all unnecessary complex geometry from the prime-side target. A
successful CCM proof may work entirely with the real function `(16)` and prove that it is a
contractive multiplier of the Cauchy space with kernel `1/(x+y)`.

## Relation to the aperture charge

Combining `(3)` with `ccm-aperture-morse-hardymodel-index-exhaustion-law.md` gives

```text
sup_(a>0)kappa(a)
 =sup_(omega>0)ind_-(L_omega)
 =sum_(Re rho>1/2)multiplicity(rho).                     (18)
```

Thus a negative real Euler-ray matrix is transported cofinally into an actual negative
restricted-Weil aperture direction.

## Scope and classification

The proof is locality of negative squares restricted to an analytic uniqueness ray. It sharpens
the route interface but is a direct consequence of classical generalized Schur theory, so it is
not new scientific knowledge.

The formal tree contains finite abstract Pick/inertia facts but not Xi's analytic quotient,
Euler-product evaluation, or Pontryagin-space locality. A finite matrix wrapper would not certify
`(3)`, so no Lean file is added.

## Gates

- [x] complex Euler uniqueness region reduced to one vertical ray
- [x] ray kernel computed as a real Cauchy--Loewner kernel
- [x] complete shifted off-line multiplicity recovered on the ray
- [x] dense rational matrices proved index-exhausting
- [x] every matrix entry written using positive convergent Euler factors
- [x] scalar positivity separated from complete kernel positivity
- [x] cofinal shift family reduced to one infinitesimal log-derivative kernel
- [ ] prove `L_omega>=0` cofinally as `omega downarrow 0`
- [ ] RH
