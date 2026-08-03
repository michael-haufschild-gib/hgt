# The causal Möbius quotient is the Euler-region restriction of the shifted-Xi Pick carrier

- **ID:** `ccm-causal-pick-affine-conjugacy-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / EXACT CCM COORDINATE IDENTIFICATION / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** the completed-zeta identity, the signed Möbius causal transform,
  `shifted-xi-kernel-transverse-index-filtration.md`, and
  `euler-pick-inertia-offline-zero-count.md`
- **Statement:** The nonconstant term of the coupled signed-Möbius causal transform is, after an
  explicit archimedean-polar scalar factor, exactly the shifted completed quotient whose
  generalized Pick kernel counts off-line zeros. The affine change of variables maps the causal
  right half-plane onto the Euler-convergent uniqueness region of that kernel. Consequently the
  missing CCM operation is not a comparison between two unrelated carriers: it is the promotion
  of scalar Hardy contractivity of one distinguished vector to complete Pick positivity of the
  same meromorphic quotient, cofinally in the horizontal shift.

## 1. The two coordinates

Fix `omega>0`. Put

```text
Phi_omega(z)=xi(1+z)/xi(1+2omega+z),                       (1)
```

initially for `Re z>0`. The signed Möbius theorem gives the causal transform

```text
L F_omega(z)
 =zeta(1+z)/((1+omega+z)zeta(1+2omega+z))
  -1/((1+omega)z zeta(1+2omega)).                         (2)
```

Define the explicit meromorphic scalar

```text
A_omega(z)
 =pi^(-omega)
  Gamma((1+2omega+z)/2)/Gamma((1+z)/2)
  *(1+2omega+z)(2omega+z)
   /((1+z)z(1+omega+z)),                                 (3)
```

and the polar counterterm

```text
c_omega(z)=1/((1+omega)z zeta(1+2omega)).                 (4)
```

Then

```text
L F_omega(z)+c_omega(z)=A_omega(z)Phi_omega(z).            (5)
```

### Proof

From

```text
xi(s)=1/2*s*(s-1)*pi^(-s/2)*Gamma(s/2)*zeta(s)             (6)
```

with `s=1+2omega+z`, one obtains

```text
Phi_omega(z)
 =pi^omega
  *(1+z)z/((1+2omega+z)(2omega+z))
  *Gamma((1+z)/2)/Gamma((1+2omega+z)/2)
  *zeta(1+z)/zeta(1+2omega+z).                            (7)
```

Multiplying `(7)` by `(3)` leaves exactly the first term of `(2)`. This proves `(5)`. `QED`

The factor `A_omega` is explicit and has no zero or pole in the open half-plane `Re z>0`.
Its apparent pole at `z=0` lies on the boundary and is precisely paired with the counterterm in
`(2)`. Thus `(5)` is an invertible meromorphic scalar coordinate change throughout the causal
Euler half-plane.

## 2. Exact affine identification with the shifted-Xi quotient

Let

```text
Theta_omega(w)
 =xi(1/2-omega-iw)/xi(1/2+omega-iw).                      (8)
```

The affine embedding

```text
j_omega(z)=i(1/2+omega+z)                                 (9)
```

maps `Re z>0` biholomorphically onto

```text
U_omega={w:Im w>1/2+omega}.                               (10)
```

Direct substitution gives

```text
Theta_omega(j_omega(z))=Phi_omega(z).                     (11)
```

Indeed `-i j_omega(z)=1/2+omega+z`, so the numerator and denominator arguments in `(8)` become
`1+z` and `1+2omega+z`. In particular, both lie in `Re s>1` on `(10)`, exactly the ordinary
Euler-convergence region.

## 3. The causal Pick kernel

Pull the generalized shifted-Xi kernel back by `(9)`. Since

```text
i/(j_omega(z)-conjugate(j_omega(v)))
 =1/(1+2omega+z+conjugate(v)),                            (12)
```

the resulting Hermitian kernel on `Re z>0` is

```text
K_omega(z,v)
 =(1-Phi_omega(z)conjugate(Phi_omega(v)))
  /(1+2omega+z+conjugate(v)).                             (13)
```

For every nonexceptional `omega>0`, locality of negative squares and the shifted-Xi index theorem
give

```text
ind_-(K_omega)
 =sum_(xi(rho)=0, Re rho>1/2+omega) multiplicity(rho),     (14)
```

with the value infinity allowed. At exceptional shifts the common numerator-denominator divisor
is first cancelled, exactly as in the parent theorem.

Combining `(5)` and `(13)` expresses every finite Pick matrix entirely through the causal vector:

```text
Phi_omega(z)
 =A_omega(z)^(-1)(L F_omega(z)+c_omega(z)).               (15)
```

Thus the full transverse divisor filtration is already present in the meromorphic continuation
of the coupled signed-Möbius source. No additional comparison transform between a Möbius carrier
and a shifted-Xi carrier is required.

## 4. Scalar contractivity versus complete Pick positivity

The signed squarefree multiplier

```text
tau_omega(z)
 =zeta(2+4omega)
  /(zeta(1+2omega)zeta(1+2omega+z))                       (16)
```

is a Schur multiplier on `Re z>=0`, and `(2)` gives one distinguished causal Hardy vector. Neither
statement is the matrix inequality

```text
(K_omega(z_j,z_k))_(j,k=1)^N >= 0
for every N and every z_1,...,z_N with Re z_j>0.           (17)
```

By `(14)`, `(17)` is equivalent to the zero-free half-plane

```text
xi(rho)=0 -> Re rho<=1/2+omega.                            (18)
```

Hence the positive operator resource a successful CCM construction must carry is **complete
Pick positivity of the scalar-conjugated causal quotient**, not merely contraction of
`tau_omega`, boundedness of `F_omega`, or a norm bound on one selected vector. Cofinality in
`omega downarrow 0` turns `(17)` into RH.

This identifies the exact missing synthesis:

```text
signed Möbius source and its polar counterterm
  --explicit scalar conjugacy (5)-->
completed shifted quotient Phi_omega
  --complete Pick positivity, cofinally in omega-->
RH.                                                        (19)
```

The first arrow is now proved. The second remains the RH-bearing estimate.

## 5. Critical degeneration and the half-unit seam

At `omega=0`, meromorphic identities give

```text
Phi_0=1,
A_0(z)=1/(1+z),
c_0=0,
L F_0(z)=1/(1+z),
K_0=0.                                                     (20)
```

Therefore the strong causal limit by itself collapses the complete Pick carrier to the zero
kernel. The transverse information is not the endpoint `omega=0`; it is the full right-hand
filtration `omega>0` together with its residue-index jumps. This is the kernel form of the
half-unit weighted-domain obligation: a successful limit must retain the cofinal incidence data,
not only the limiting Hardy vector.

## 6. Relation to intrinsic HT dimension

The periodic-pencil and scalar-principalization theorems apply only after an exact full
Stanley--Reisner differential matroid has been proved. No such matroid is supplied by `(1)`--`(15)`.
Accordingly, they do not prove that the present CCM carrier has analytic dimension two.

They do, however, exclude a misidentification. For each fixed `omega`, `(5)` is an invertible scalar
meromorphic coordinate change in one analytic variable. If one additionally imposed a full exact
prime-translation Stanley--Reisner matroid on this scalar slice, its structural ideal would be pure
and principal. Any genuinely nonpure prime compatibility would then have to live in a second
analytic coordinate, a non-DA-flat internal cocycle, or an infinite-dimensional action.

The actual CCM route already exhibits a different positive carrier: the cofinal parameter
`omega`, the complete family of Pick sections in `z`, and the residue-index filtration `(14)`.
This is a pointed incidence family, not yet a periodic-pencil realization. The two HT geometry
theorems therefore sharpen the branch distinction without supplying the missing positivity.

## 7. Scientific classification and Lean decision

Equations `(5)`, `(11)`, and `(13)` are exact but elementary consequences of the completed-zeta
formula and affine substitution. Equation `(14)` is the existing generalized-Schur bridge.
Therefore the result is scientifically non-new. Its route value is eliminative: it removes an
unnecessary comparison-map problem and isolates complete Pick positivity as the remaining
operator upgrade.

The Lean tree does not contain the completed-zeta quotient, Hardy kernels, or generalized negative
squares. Formalizing only the scalar algebra in `(5)` would be wrapper work and would not certify
the RH-bearing implication `(17)`. No Lean file is added.

## Gates

- [x] causal quotient factored through the completed shifted quotient
- [x] exact affine identification with the Euler-region shifted-Xi carrier
- [x] pulled-back Pick kernel computed
- [x] negative index attached to the off-line divisor filtration
- [x] critical endpoint degeneration identified
- [x] scalar principalization scope stated without assuming a relation matroid
- [ ] prove complete Pick positivity from the pointed source construction
- [ ] retain that positivity cofinally as `omega downarrow 0`
- [ ] RH
