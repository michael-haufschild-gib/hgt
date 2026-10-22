# The infinitesimal CCM half-unit seam is an indefinite Cauchy Schur ratio

- **ID:** `ccm-infinitesimal-half-unit-cauchy-seam-law`
- **Stage:** 2-fully-proven / not-new
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** positive-real kernels, the classical zero strip, and
  `ccm-infinitesimal-real-euler-ray-logderivative-index-law.md`

## Statement

Put

```text
Q(z)=xi'(1/2+z)/xi(1/2+z).                               (1)
```

The classical zero strip implies

```text
Re Q(z)>0,       Re z>1/2.                               (2)
```

Therefore the positive-real kernel

```text
J_safe(x,y)=[Q(x)+Q(y)]/(x+y-1),
x,y>1/2,                                                (3)
```

is positive semidefinite unconditionally. The RH kernel is

```text
J_RH(x,y)=[Q(x)+Q(y)]/(x+y).                             (4)
```

They satisfy the exact Schur-product identity

```text
J_RH=J_safe circ H,
H(x,y)=(x+y-1)/(x+y).                                    (5)
```

The scalar seam kernel `H` is not positive on any set containing two distinct points. Indeed,

```text
det [[H(x,x),H(x,y)],[H(y,x),H(y,y)]]
 =-(x-y)^2(2x+2y-1)/(4xy(x+y)^2)<0                      (6)
```

for distinct `x,y>1/2`.

Consequently no universal scalar Schur multiplier transports the unconditional safe kernel `(3)`
to the RH kernel `(4)`. A successful CCM construction must use the special Euler--Gamma covariance
inside `J_safe`, or an equivalent non-diagonal operator carrier, to cross the half-unit seam.

## Proof

Let `X(z)=xi(1/2+z)`. The centered Hadamard logarithmic derivative is

```text
Q(z)=sum_(lambda mod +/-)
      [1/(z-lambda)+1/(z+lambda)].                       (7)
```

Every centered zero satisfies `|Re lambda|<1/2`. Hence each reciprocal in `(7)` has positive real
part when `Re z>1/2`, proving `(2)`.

Set

```text
F(u)=Q(u+1/2),       Re u>0.                             (8)
```

Then `F` is a scalar positive-real function on the right half-plane. Its standard de
Branges--Rovnyak/impedance kernel

```text
[F(u)+conjugate(F(v))]/(u+conjugate(v))                  (9)
```

is positive semidefinite. Restricting `(9)` to positive real `u=x-1/2`, `v=y-1/2` gives `(3)`.

Equation `(5)` is algebraic. For two points, direct simplification gives `(6)`. Its numerator is
strictly negative for distinct `x,y>1/2`, while both diagonal entries of `H` are positive, so the
two-point matrix has one positive and one negative eigenvalue. `QED`

## Positive carrier law

The finite-shift missing width

```text
(1/2+omega)-omega=1/2
```

from `ccm-completed-quotient-weighted-schur-seam-law.md` survives infinitesimally as the denominator
change

```text
x+y-1 -> x+y.                                            (10)
```

The theorem identifies exactly what must cross it:

```text
unconditional positive-real Euler--Gamma kernel J_safe
  + source-specific covariance beyond scalar Schur multiplication
  -> J_RH>=0
  -> zero aperture Morse charge
  -> RH.                                                  (11)
```

Pointwise positivity of `Q`, complete positivity of `J_safe`, and any scalar factor depending only
on the two denominators are insufficient. The required additional datum must mix source channels
non-diagonally. The canonical closed causal/anti-causal graph and the square boundary Evans line are
the two existing carriers with enough structure to do so.

`[PROVED DIAGONAL FOCK CARRIER]` The source-specific covariance is the positive kernel

```text
D(x,y)=J_safe(x,y)/(x+y),
J_RH=J_safe-D.
```

If `k_x` is the safe RKHS feature and `c_x(t)=exp(-xt)`, then `D` is the Gram kernel of
`k_x tensor c_x`. RH is exactly contractivity of the diagonal lift
`k_x -> k_x tensor c_x`. This is proved in `ccm-safe-kernel-diagonal-fock-lift-rh-law.md`.

## Scope and classification

The positive-real kernel theorem and the two-by-two determinant calculation are classical. This is
the infinitesimal normal form of the already known half-unit seam, so it is a bridge rather than new
scientific knowledge.

The determinant identity `(6)` is elementary and Lean-formalizable, but formalizing it alone would
not represent `Q`, `(2)`, or the source transport in `(11)`. No wrapper is added.

**Superseded, 2026-08-15.**  A wrapper *is* added, and it represents more than `(6)`: the
termwise proof of `(2)`, the Schur factorization `(5)`, the indefiniteness of every two-point seam
minor, the exclusion of universal scalar Schur transport, and the diagonal Fock covariance with its
Cauchy Gram factor.  See the Lean status section below.

## Lean status

**Formalized, 2026-08-15.**  Module
`formal/GaloisForLFunctions/RHTower/CCM/CCMHalfUnitCauchySeam.lean` (wired, axiom-clean, 8
declarations).

- **`re_hadamardPair_pos`** — the proof of `(2)` at the level of `(7)`: for `Re z > 1/2` and a
  centred zero with `|Re lambda| < 1/2`, the Hadamard pair `1/(z-lambda) + 1/(z+lambda)` has
  strictly positive real part, because each summand has positive-real-part denominator.  The
  Hadamard representation `(7)` itself is the imported classical input.
- `safeKernel`, `rhKernel`, `seamKernel`, `fockKernel` — equations `(3)`, `(4)`, `(5)` and the
  diagonal Fock covariance `D = J_safe/(x+y)`.
- **`rhKernel_eq_safe_mul_seam`** — equation `(5)`: `J_RH = J_safe * H` exactly.
- **`rhKernel_eq_safe_sub_fock`** — `J_RH = J_safe - D` exactly, the form in which RH becomes
  contractivity of the diagonal Fock lift.
- **`integral_exp_ray`** — the Cauchy factor is a genuine Gram matrix:
  `int_0^infinity e^{-xt} e^{-yt} dt = 1/(x+y)`, so `D` is the Schur product of `J_safe` with a
  positive kernel.
- **`det_seam_two_point`** — equation `(6)` exactly:
  `H(x,x)H(y,y) - H(x,y)H(y,x) = -(x-y)^2 (2x+2y-1)/(4 x y (x+y)^2)`.
- **`det_seam_two_point_neg`** — its strict negativity for distinct `x, y > 1/2`.
- **`not_posSemidef_seamMatrix`** — hence the two-point seam matrix is *not* positive semidefinite,
  so no universal scalar Schur multiplier transports `J_safe` to `J_RH`.

`#print axioms` on all eight declarations returns exactly `[propext, Classical.choice, Quot.sound]`.

Imported, not reproved: the Hadamard product representation `(7)` of `xi'/xi`, and the de
Branges--Rovnyak positive-real kernel theorem giving positive semidefiniteness of `(9)`, hence of
`J_safe`.  Both are classical and are the card's declared parents.

## Gates

- [x] unconditional safe log-derivative kernel constructed
- [x] RH kernel separated by one exact denominator shift
- [x] scalar seam kernel computed
- [x] every distinct two-point seam minor proved indefinite
- [x] universal scalar Schur transport excluded
- [x] source-specific non-diagonal covariance identified as the required carrier
- [x] construct the canonical diagonal Fock covariance at the critical half-unit
- [ ] prove its source realization is contractive
- [ ] prove `J_RH>=0`
- [ ] RH
